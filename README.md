* Description

Yogar-CBMC-Parallel is a parallel version of Yogar-CBMC, which employs multiple engines to refine the abstraction in parallel.

It contains two parts, the master procedure and the single Yogar-CBMC.

The master procedure manages the shared resources and starts multiple processes of yogar-cbmc to perform the refinement.

The single Yogar-CBMC performs its own refinement and exchanges refinement constraints at its end of each iteration.

* Compiling

To compile the master procedure, enter the master directory and use the following command to obtain the procedure yogar-cbmc-parallel

g++ yogar-cbmc-parallel.cpp -o yogar-cbmc-parallel

To compile the single Yogar-CBMC, enter the yogar-cbmc/src directory and use the following command to obtain the procedure yogar-cbmc

make

Then copy the two procedures yogar-cbmc-parallel and yogar-cbmc into the same directory, when we run yogar-cbmc-parallel, it will start multiple yogar-cbmc processes.

* Usage (SV-COMP 2019) *

To run Yogar-CBMC-Parallel, use the following command-line from this directory:

>./yogar-cbmc-parallel [--thread-num N] <inputfile>

where  <inputfile>  is the filename to be verified. 

The counterexample will also be written in counterexample.witness.

To run Yogar-CBMC-Parallel for SV-COMP benchmark, use the following command-line from this directory:

>PYTHONPATH=. benchexec -r "sv-comp19" -t Concurrency --no-container yogar-cbmc-parallel.xml

We assume that benchexec has been installed already.

* Environement

This binary of Yogar-CBMC-Parallel runs on Ubuntu of 64bit.

* Contributors

Liangze Yin, Wei Dong, Wanwei Liu, Ji Wang, Haining Feng
