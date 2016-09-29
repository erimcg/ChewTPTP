# ChewTPTP

ChewTPTP is a refutationally complete and sound automated theorem prover for first order theorems. It accepts problems in TPTP CNF format.  ChewTPTP proves rigid first order theorems by encoding them as propositional satisfiability problems. The prover encodes the existence of a first order connection tableau and the satisfiability of unification constraints in propositional logic. The rigid first order theorem is rigidly unsatisfiable if and only if the encoding is propositionally satisfiable. This method is extended to general first order problems by continually adding more instances of each clause.

## Publications

1. T. Deshane, W. Hu, P. Jablonski, H. Lin, C. Lynch, R.E. McGregor, Encoding First Order Proofs In SAT, Conference on Automated Deduction (CADE), Bremen, Germany, 2007

2. J. Bongio, C. Katrak, H. Lin, C. Lynch, R.E. McGregor, Encoding First Order Proofs In SMT, Electronic Notes in Theoretical Computer Science, April 2008

Updated: June 27, 2016 by Eric McGregor

