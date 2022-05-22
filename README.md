# fmcad22_saturation

# Supplementary Material for submission "On Cutoff and Saturation of Unbounded Distributed Protocols"

This repository contains the results that we presented in our FMCAD'22 case study titled as "On Cutoff and Saturation of Unbounded Distributed Protocols".

The structure of the repository is as follows:

* `R_equivalence_checks/`: contains all SMT queries that prove the quivalence of the two derived R-representations (intersection of over-approximations vs. union of under-approximations).

* `espresso_inputs/`: Contains the output of the first step of the workflow presented in the paper. For each protocol it provides the following files:
  1. `[protocolname]_[R-cutoff-size]_R.pla`: The .pla file generated from the reachable states for the `R-cutoff-size` of domains.
  2. `[protocolname]_[conf-cutoff-size]_conf[conf-ID].pla`: The .pla generated from the states that are belonging to the configuration identified with `conf-ID` (while considering `conf-cutoff-size` domain sizes).

* `R_formulas/`: Contains for each analyzed protocol the following details:
  1. `[protocolname]_R_formulas.txt`: Closed FOL formulas describing R. The file contains the closed formulas of each configurations of the protocol (whose disjunction together describes R), and the set of invariants whose conjunction also describes R.
  2. `[protocolname]_[size]_minR_clauses.txt`: The output of espresso on the complete set of reachable states at the cutoff size of the protocol.

