/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#ifdef _MSC_VER
//#   include <win/zlib.h>
#else
//#   include <zlib.h>
#   include <sys/resource.h>
#endif


#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

using namespace Minisat; 




void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("c restarts              : %-12ld\n", solver.starts);
    printf("c conflicts             : %-12ld   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("c decisions             : %-12ld   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("c propagations          : %-12ld   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("c conflict literals     : %-12ld   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("c Memory used           : %.2f MB\n", mem_used);
    printf("c CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("c *** INTERRUPTED ***\n");
    if (solver->verbosity > 0){ 
        printStats(*solver);
        printf("\n"); printf("c *** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", false);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
		
        
		parseOptions(argc, argv, true);

		 

		//vec<uint32_t> icParentsVec; 
		//vec<uint32_t> remParentsVec; 
		//vec<uint32_t> allParentsVec; 
		////Resol r = Resol(icParentsVec, remParentsVec, allParentsVec, true);
		//for (int i = 32; i < 64; ++i) {
		//	if (i == 34)
		//		remParentsVec.push(i);
		//	else
		//		icParentsVec.push(i);
		//	allParentsVec.push(i);
		//}
		//icParentsVec.push(10);  icParentsVec.push(7); icParentsVec.push(6); icParentsVec.push(2); icParentsVec.push(1);
		//remParentsVec.push(5); remParentsVec.push(4); remParentsVec.push(15);  remParentsVec.push(8);
		//allParentsVec.push(5); allParentsVec.push(10);  allParentsVec.push(4); allParentsVec.push(7); allParentsVec.push(6); allParentsVec.push(15); allParentsVec.push(2); allParentsVec.push(1); allParentsVec.push(8);

		// for (int i = 64; i < 96; ++i) {
		//	 if (i == 65 || i == 95)
		//		 icParentsVec.push(i);
		//	 else
		//		 remParentsVec.push(i);
		//	 allParentsVec.push(i);
		// }


		//vec<uint32_t> dummyVec;
  //     
		//for (int i = 0; i < allParentsVec.size(); ++i) {
		//	S.resolGraph.AddNewResolution(allParentsVec[i], CRef_Undef, dummyVec, dummyVec, dummyVec);
		//}

		//S.resolGraph.AddNewResolution(0, CRef_Undef, icParentsVec, remParentsVec, allParentsVec);
		//CRef resolRef = S.resolGraph.GetResolRef(0);
		//Resol& resol = S.resolGraph.GetResol(resolRef);


		//int remSize = resol.remParentsSize();
		//int icSize = resol.ParentsSize();
		//int size = remSize + icSize;
		//int flagsSize = (size / 32) + (int)((size % 32) > 0);


		//for (int i = 0; i < 1 + resol.ParentsSize() + ((remSize == 0) ? 0 : (1 + remSize + flagsSize)); ++i)
		//	printf("resol.m_Parents[%d] =  %u\n",i, resol.m_Parents[i]);

		//uint32_t j, k;
		//uint32_t flags;
		//uint32_t flagBit;
		//uint32_t icOffset = 1;
		//uint32_t remOffset = icOffset + 1 + icSize;
		//uint32_t flagOffset = remOffset + remSize;
		//uint32_t lastFlagWordLoc = size / 32;
		//uint32_t icIdx, remIdx; icIdx = remIdx = 0;


		//
		//for (uint32_t i = 0; i < size; ++i) {
		//	k = i % 32;
		//	if (k == 0) {
		//		j = i / 32;
		//		flags = resol.m_Parents[flagOffset + j].guideFlags;
		//	}
		//	flagBit = ((flags << k) & 0x80000000) >> 31; //extract the MSB after shifting k steps to the left (i.e. after multiplying by 2^k)
		//	//printf("flagsIdx[%d]=%u, flagBit[%d] = %d, \n", j, flags, k, flagBit);
		//	if (flagBit)
		//		printf("ic uid: %d\n", resol.m_Parents[icOffset + icIdx++]);
		//	else
		//		printf("rem uid: %d\n", resol.m_Parents[remOffset + remIdx++]);
		//}



		//printf("flags size: %d\n", flagsSize);

		//exit(-5);






		SimpSolver  S;


        double      initial_time = cpuTime();

        if (!pre) S.eliminate(true);

        S.verbosity = verb;
        
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
#ifndef _MSC_VER
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
#endif
		
		if (argc == 1) {
			printf("c please provide an input (cnf) file name ... Use '--help' for help.\n");
			exit(1);
		}

        //gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
		FILE* in = fopen(argv[1], "rb");
		printf("input: %s\n", argv[1]);
        if (in == NULL)
            printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        if (S.verbosity > 0){
            printf("c ============================[ Problem Statistics ]=============================\n");
            printf("c |                                                                             |\n"); }
        
        CMinimalCore coreManager(S);
        parse_DIMACS(in, coreManager);
        //gzclose(in);
		fclose(in);

        if (S.verbosity > 0){
            printf("c |  Number of variables:  %12d                                         |\n", S.nVars());
            printf("c |  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("c |  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt); 
#ifndef _MSC_VER
        signal(SIGXCPU,SIGINT_interrupt);
#endif


		// !!test
		//coreManager.testsat();
		
		
		lbool ret = coreManager.Solve(pre);
		printf("### decisions %d\n", solver->decisions);
		printf("### pf_time %g\n", solver->time_for_pf);
        if (S.verbosity > 0){
            printStats(S);
            printf("\n"); }
        printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s UNKNOWN\n");
//		getchar();
		freopen("CON", "w", stdout);
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("c ===============================================================================\n");
        printf("s UNKNOWN\n");
		freopen("CON", "w", stdout);
        exit(0);
    }
}
