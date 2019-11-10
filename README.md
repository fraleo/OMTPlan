# OMTPlan: Optimal Planning Modulo Theories

OMTPlan provides a Python framework for planning in numeric domains.


## Obtaining OMTPlan

Clone the OMTPlan repository in your favourite folder.
	
	git clone https://github.com/fraleo/OMTPlan.git


## Dependencies

To run OMTPlan, make sure you have the following on your machine

* Python 2.7
* [Z3](https://github.com/Z3Prover/z3) (4.8.6) and its Python API (make sure you add z3 Python bindings to your Python search path)
* [NetworkX](https://networkx.github.io/) (as simple as `pip install networkx`)



Already provided within this repo are the following external modules

* A modified version of the [Temporal Fast Downward](http://gki.informatik.uni-freiburg.de/tools/tfd/) Python parser 
* Binaries of [VAL](https://github.com/KCL-Planning/VAL), the plan validator devoleped and mainted by King's College 


## About OMTPlan


##### Getting help

To see the list of input arguments, type

	./omtplan -h


##### Running OMTPlan

To run OMTPlan on a problem, type, e.g.,

	./omtplan -omt -parallel -domain domain.pddl problem.pddl

or

	./omtplan -omt -parallel problem.pddl

if PDDL files describing domain and problem are in the same folder.


##### Translating to SMT-LIB
 
To produce an SMT-LIB encoding of the bounded planning problem, type, e.g.,

	./omtplan.py -smt -parallel -translate bound problem.pddl 
 

##### Some PDDL examples

You can find some planning problems written in PDDL in [pddl_examples](/pddl_examples).


## Documentation

Further documentation is available [here](https://fraleo.github.io/OMTPlan/).


## Author

[Francesco Leofante](https://fraleo.github.io)

Do not hesitate to contact me if you have problems using OMTPlan, or if you find bugs :)


## Citing OMTPlan

If you ever decide to use OMTPlan for your experiments, please cite

"Optimal Planning Modulo Theories", Some authors, Some Conf, Sometime






