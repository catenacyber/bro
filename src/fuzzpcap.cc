// See the file "COPYING" in the main distribution directory for copyright.

#include "bro-config.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <string.h>
#include <stdbool.h>
#include <list>
#ifdef HAVE_GETOPT_H
#include <getopt.h>
#endif

#ifdef USE_IDMEF
extern "C" {
#include <libidmef/idmefxml.h>
}
#endif

#include <openssl/ssl.h>
#include <openssl/err.h>

#include "bsd-getopt-long.h"
#include "input.h"
#include "DNS_Mgr.h"
#include "Frame.h"
#include "Scope.h"
#include "Event.h"
#include "File.h"
#include "Reporter.h"
#include "Net.h"
#include "NetVar.h"
#include "Var.h"
#include "Timer.h"
#include "Stmt.h"
#include "Debug.h"
#include "DFA.h"
#include "RuleMatcher.h"
#include "Anon.h"
#include "Serializer.h"
#include "RemoteSerializer.h"
#include "PersistenceSerializer.h"
#include "EventRegistry.h"
#include "Stats.h"
#include "Brofiler.h"

#include "threading/Manager.h"
#include "input/Manager.h"
#include "logging/Manager.h"
#include "logging/writers/ascii/Ascii.h"
#include "input/readers/raw/Raw.h"
#include "analyzer/Manager.h"
#include "analyzer/Tag.h"
#include "plugin/Manager.h"
#include "file_analysis/Manager.h"
#include "broxygen/Manager.h"
#include "iosource/Manager.h"

#include "binpac_bro.h"

#include "3rdparty/sqlite3.h"

#ifdef ENABLE_BROKER
#include "broker/Manager.h"
#endif

Brofiler brofiler;

static bool initialized = false;
int fd;

#ifndef HAVE_STRSEP
extern "C" {
char* strsep(char**, const char*);
};
#endif

extern "C" {
#include "setsignal.h"
};


DNS_Mgr* dns_mgr;
TimerMgr* timer_mgr;
PortManager* port_mgr = 0;
logging::Manager* log_mgr = 0;
threading::Manager* thread_mgr = 0;
input::Manager* input_mgr = 0;
plugin::Manager* plugin_mgr = 0;
analyzer::Manager* analyzer_mgr = 0;
file_analysis::Manager* file_mgr = 0;
broxygen::Manager* broxygen_mgr = 0;
iosource::Manager* iosource_mgr = 0;
#ifdef ENABLE_BROKER
bro_broker::Manager* broker_mgr = 0;
#endif

name_list prefixes;
Stmt* stmts;
EventHandlerPtr net_done = 0;
RuleMatcher* rule_matcher = 0;
PersistenceSerializer* persistence_serializer = 0;
FileSerializer* event_serializer = 0;
FileSerializer* state_serializer = 0;
RemoteSerializer* remote_serializer = 0;
EventPlayer* event_player = 0;
EventRegistry* event_registry = 0;
ProfileLogger* profiling_logger = 0;
ProfileLogger* segment_logger = 0;
SampleLogger* sample_logger = 0;
int signal_val = 0;
extern char version[];
char* command_line_policy = 0;
vector<string> params;
set<string> requested_plugins;
char* proc_status_file = 0;

OpaqueType* md5_type = 0;
OpaqueType* sha1_type = 0;
OpaqueType* sha256_type = 0;
OpaqueType* entropy_type = 0;
OpaqueType* cardinality_type = 0;
OpaqueType* topk_type = 0;
OpaqueType* bloomfilter_type = 0;
OpaqueType* x509_opaque_type = 0;
OpaqueType* ocsp_resp_opaque_type = 0;

// Keep copy of command line
int bro_argc;
char** bro_argv;


const char* bro_version()
{
#ifdef DEBUG
    static char* debug_version = 0;
    
    if ( ! debug_version )
    {
        int n = strlen(version) + sizeof("-debug") + 1;
        debug_version = new char[n];
        snprintf(debug_version, n, "%s%s", version, "-debug");
    }
    
    return debug_version;
#else
    return version;
#endif
}

const char* bro_dns_fake()
	{
	if ( ! getenv("BRO_DNS_FAKE") )
		return "off";
	else
		return "on";
	}

void termination_signal()
{
    exit(1);
}

RETSIGTYPE sig_handler(int signo)
	{
	set_processing_status("TERMINATING", "sig_handler");
	signal_val = signo;

	return RETSIGVAL;
	}

static void bro_new_handler()
	{
	out_of_memory("new");
	}

int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size)
	{
	name_list interfaces;
	name_list rule_files;


        if (! initialized) {
            string broxygen_config;
            char* seed_load_file = getenv("BRO_SEED_FILE");
            char* seed_save_file = 0;
            enum DNS_MgrMode dns_type = DNS_DEFAULT;

#ifdef USE_IDMEF
            string libidmef_dtd_path = "idmef-message.dtd";
#endif
            
            std::set_new_handler(bro_new_handler);
            
            brofiler.ReadStats();
            
            bro_argc = 1;
            bro_argv = new char* [bro_argc];
            
            for ( int i = 0; i < bro_argc; i++ )
                bro_argv[i] = copy_string("brofuzz");

            prefixes.append(strdup(""));    // "" = "no prefix"
            dns_type = getenv("BRO_DNS_FAKE") ? DNS_FAKE : DNS_DEFAULT;

            set_processing_status("INITIALIZING", "main");
            
            bro_start_time = current_time(true);

            port_mgr = new PortManager();
            reporter = new Reporter();
            thread_mgr = new threading::Manager();
            plugin_mgr = new plugin::Manager();

            init_random_seed((seed_load_file && *seed_load_file ? seed_load_file : 0) , seed_save_file);
            // DEBUG_MSG("HMAC key: %s\n", md5_digest_print(shared_hmac_md5_key));
            init_hash_function();
            
            ERR_load_crypto_strings();
            OPENSSL_add_all_algorithms_conf();
            SSL_library_init();
            SSL_load_error_strings();
            
            int r = sqlite3_initialize();
            
            if ( r != SQLITE_OK )
                reporter->Error("Failed to initialize sqlite3: %s", sqlite3_errstr(r));

#ifdef USE_IDMEF
            char* libidmef_dtd_path_cstr = new char[libidmef_dtd_path.length() + 1];
            safe_strncpy(libidmef_dtd_path_cstr, libidmef_dtd_path.c_str(),
                         libidmef_dtd_path.length());
            globalsInit(libidmef_dtd_path_cstr);    // Init LIBIDMEF globals
            createCurrentDoc("1.0");        // Set a global XML document
#endif
            
            timer_mgr = new PQ_TimerMgr("<GLOBAL>");
            // timer_mgr = new CQ_TimerMgr();
            
            broxygen_mgr = new broxygen::Manager(broxygen_config, bro_argv[0]);

            add_input_file("base/init-bare.bro");
            add_input_file("base/init-default.bro");
            
            plugin_mgr->SearchDynamicPlugins(bro_plugin_path());
            
            push_scope(0);
            
            dns_mgr = new DNS_Mgr(dns_type);

            dns_mgr->SetDir(".state");
            
            iosource_mgr = new iosource::Manager();
            persistence_serializer = new PersistenceSerializer();
            remote_serializer = new RemoteSerializer();
            event_registry = new EventRegistry();
            analyzer_mgr = new analyzer::Manager();
            log_mgr = new logging::Manager();
            input_mgr = new input::Manager();
            file_mgr = new file_analysis::Manager();
            
#ifdef ENABLE_BROKER
            broker_mgr = new bro_broker::Manager();
#endif
            
            plugin_mgr->InitPreScript();
            analyzer_mgr->InitPreScript();
            file_mgr->InitPreScript();
            broxygen_mgr->InitPreScript();

            bool missing_plugin = false;
            
            for ( set<string>::const_iterator i = requested_plugins.begin();
                 i != requested_plugins.end(); i++ )
            {
                if ( ! plugin_mgr->ActivateDynamicPlugin(*i) )
                    missing_plugin = true;
            }
            
            if ( missing_plugin )
                reporter->FatalError("Failed to activate requested dynamic plugin(s).");
            
            plugin_mgr->ActivateDynamicPlugins(true);
            
            // Must come after plugin activation (and also after hash
            // initialization).
            binpac::init();
            
            init_event_handlers();

            md5_type = new OpaqueType("md5");
            sha1_type = new OpaqueType("sha1");
            sha256_type = new OpaqueType("sha256");
            entropy_type = new OpaqueType("entropy");
            cardinality_type = new OpaqueType("cardinality");
            topk_type = new OpaqueType("topk");
            bloomfilter_type = new OpaqueType("bloomfilter");
            x509_opaque_type = new OpaqueType("x509");
            ocsp_resp_opaque_type = new OpaqueType("ocsp_resp");
            
            yyparse();
            
            init_general_global_var();
            init_net_var();
            init_builtin_funcs_subdirs();
            
            plugin_mgr->InitBifs();
            
            if ( reporter->Errors() > 0 )
                return 0;

            plugin_mgr->InitPostScript();
            broxygen_mgr->InitPostScript();
            
            analyzer_mgr->InitPostScript();
            file_mgr->InitPostScript();
            dns_mgr->InitPostScript();
            
            if ( reporter->Errors() > 0 )
                return 0;

            reporter->InitOptions();
            broxygen_mgr->GenerateDocs();
            
            // Parse rule files defined on the script level.
            char* script_rule_files =
            copy_string(internal_val("signature_files")->AsString()->CheckString());
            
            char* tmp = script_rule_files;
            char* s;
            while ( (s = strsep(&tmp, " \t")) )
                if ( *s )
                    rule_files.append(s);

            // Append signature files defined in @load-sigs
            for ( size_t i = 0; i < sig_files.size(); ++i )
                rule_files.append(copy_string(sig_files[i].c_str()));

            if ( rule_files.length() > 0 )
            {
                rule_matcher = new RuleMatcher(4);
                if ( ! rule_matcher->ReadFiles(rule_files) )
                    return 0;

                file_mgr->InitMagic();
            }

            delete [] script_rule_files;

            BroFile::SetDefaultRotation(log_rotate_interval, log_max_size);
            
            EventHandlerPtr bro_init = internal_handler("bro_init");
            if ( bro_init )    //### this should be a function
                mgr.QueueEvent(bro_init, new val_list);

            // Queue events reporting loaded scripts.
            for ( std::list<ScannedFile>::iterator i = files_scanned.begin(); i != files_scanned.end(); i++ )
            {
                if ( i->skipped )
                    continue;
                
                val_list* vl = new val_list;
                vl->append(new StringVal(i->name.c_str()));
                vl->append(new Val(i->include_level, TYPE_COUNT));
                mgr.QueueEvent(bro_script_loaded, vl);
            }
            
            reporter->ReportViaEvents(true);
            
            // Drain the event queue here to support the protocols framework configuring DPM
            mgr.Drain();
            
            analyzer_mgr->DumpDebug();

            iosource_mgr->Register(thread_mgr, true);
            reading_live = pseudo_realtime > 0.0;
            reading_traces = 1;

            init_ip_addr_anonymizers();
            sessions = new NetSessions();


            //deletes previous tmp dir and (re)create it as a ramfs
            system("umount /tmp/ramfuzz");
            system("rm -Rf /tmp/ramfuzz");
            mkdir("/tmp/ramfuzz", 0600);
            system("mount -t tmpfs -o size=64M tmpfs /tmp/ramfuzz");
            fd = open("/tmp/ramfuzz/fuzz.pcap", O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
            if (fd == -1) {
                return 0;
            }

            initialized = true;
        }

        if (ftruncate(fd, Size) == -1) {
            return 0;
        }
        if (lseek (fd, 0, SEEK_SET) < 0) {
            return 0;
        }
        if (write (fd, Data, Size) != Size) {
            return 0;
        }

    //TODO compile with oss-fuzz
    //TODO run with oss-fuzz
        iosource::PktSrc* ps = iosource_mgr->OpenPktSrc("/tmp/ramfuzz/fuzz.pcap", false);
        assert(ps);
        
        if ( ! ps->IsOpen() )
            reporter->FatalError("problem with trace file %s (%s)",
                                 "/tmp/ramfuzz/fuzz.pcap",
                                 ps->ErrorMsg());

    net_run();

	return 0;
	}
