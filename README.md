# fmcad22_saturation

# Supplementary Material for submission "On Cutoff and Saturation of Unbounded Distributed Protocols"

This repository contains the results that we presented in our FMCAD'22 case study titled as "On Cutoff and Saturation of Unbounded Distributed Protocols".

The structure of the repository is as follows:

* `R_equivalence_checks/`: contains all SMT queries that prove the quivalence of the two derived R-representations (intersection of over-approximations vs. union of under-approximations).

* `espresso_inputs/`: Contains the output of the first step of the workflow presented in the paper. For each protocol it provides the following files:
  1. `[protocolname]_[R-cutoff-size]_R.pla`: The .pla file generated from the reachable states for the `R-cutoff-size` of domains.
  2. `[protocolname]_[conf-cutoff-size]_conf[conf-ID].pla`: The .pla generated from the states that are belonging to the configuration identified with `conf-ID` (while considering `conf-cutoff-size` domain sizes).

* `espresso_outputs/`: Contains the output of the second step of the workflow presented in the paper. For each protocol it provides the following files:
  1. `[protocolname]_[R-cutoff-size]_minR_CNF.txt`: Contains the minimized R representation in a clausal form. It is based on the output of espresso, where the minimal solution is mapped back to the original state variables of the protocol.
  2. `[protocolname]_[conf-cutoff-size]_conf[conf-ID]_minCNF.txt`: Contains the minimized configuration representation in a clausal form. It is based on the output of espresso, where the minimal solution is mapped back to the original state variables of the protocol.
  - In both output types each clause starts with a numerical ID that is referenced by the derived closed formulas (see `R_formulas/`).

* `R_formulas/`: Contains for each analyzed protocol the following details:
  1. `[protocolname]_R_formulas.txt`: All the derived closed FOL formulas describing R. 
    - It starts with the set of invariants derived from the complete set of reachable states of the protocol.
    - Then, for each configuration of the protocol, it contains a set of invariants derived from the set of reachable states belonging to that configuration.
    - Each formula set starts with an identifier (e.g. R, of config1), the domain size where the saturated formula was encountered and a refernce to the clausal representation of the minimization result that was the base of the quantifier inference.
    - Each quantified FOL formula starts with a set of numbers indicating the clauses of the minimization result that are encoded by that formula (see the referenced files in `espresso_outputs/`.
    - Reminder: The disjunction of these configuration-conjunctions is equivalent with the conjunction of the R-invariants.

  3. `[protocolname].ivy`: The specification of the distributed protocol in the ivy language.

