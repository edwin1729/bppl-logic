# Lilac: Probabilistic Separation Logic
[Lilac](https://dl.acm.org/doi/10.1145/3591226) is a probabilistic separation logic for reasoning about first order probabilistic programs supporting continuous distributions.
This is a mechanisation of Core [Lilac](https://dl.acm.org/doi/10.1145/3591226), i.e. we don't yet support the
conditioning connective.
The mechanisation in Lean includes full soundness proofs of the system as well as an embedding into [iris-lean](https://github.com/leanprover-community/iris-lean/).
for tactical proof support

The following outlines the structure of the repository:

- [`Bppl/Lilac/Appl.lean`](Bppl/Lilac/Appl.lean) — APPL probabilistic programming language syntax and semantics; the language Lilac reasons about.
- [`Bppl/Lilac/MeasureOnSpace.lean`](Bppl/Lilac/MeasureOnSpace.lean) — Independent product of probability measures; common foundation shared with [Bluebell](https://github.com/Verified-zkEVM/iris-lean).
- [`Bppl/Lilac/KRM.lean`](Bppl/Lilac/KRM.lean) — Kripke Resource Monoids, instantiated to probability spaces and to probability spaces with finite footprint (`PSp`).
- [`Bppl/Lilac/BI.lean`](Bppl/Lilac/BI.lean) — Generating an instance of BI (logic of Bunched Implications) from a KRM, with a proof that the resulting logic is affine.
- [`Bppl/Lilac/Assertion.lean`](Bppl/Lilac/Assertion.lean) — Probability-specific connectives of Lilac: ownership, distribution `∼`, almost-sure equality `≗`, expectation `𝔼[·]=`, and weakest precondition `wp`.
- [`Bppl/Lilac/ProofRules/WP.lean`](Bppl/Lilac/ProofRules/WP.lean) — Main WP proof rules (consequence, frame, return, bind, unif) corresponding to Appendix B.20 of the Lilac paper.
- [`Bppl/Lilac/ProofRules/WPMeas.lean`](Bppl/Lilac/ProofRules/WPMeas.lean) — Generalised WP rule `wp_meas` for introducing random variables that are primitive measures; specialised to `wp_unif` and `wp_flip`.
<!-- - [`Bppl/Lilac/ProofRules/WPUnifHelpers.lean`](Bppl/Lilac/ProofRules/WPUnifHelpers.lean) — Helper lemmas for `WPMeas` (pending consolidation into `WPMeas.lean`). -->
- [`Bppl/Lilac/ProofRules/MeasureProduct.lean`](Bppl/Lilac/ProofRules/MeasureProduct.lean) — Helper lemmas for the measure product condition used in `wp_meas`.
- [`Bppl/Lilac/Examples.lean`](Bppl/Lilac/Examples.lean) — Worked examples (`unif1`, `unif2`, `half`) using the Iris proof mode instantiated to Lilac.
- [`Bppl/Lilac/HilbertCube.lean`](Bppl/Lilac/HilbertCube.lean) — Fundamental transformations on Hilbert cubes.
