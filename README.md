# Interchange graphs of (0,1)-matrices are maximally Hamiltonian — Lean 4 companion

The machine-checked companion to the paper *Interchange graphs of (0,1)-matrices are maximally
Hamiltonian*, by Jeffrey S. Baggett and Huiya Yan.

For integer vectors `R, S`, the interchange graph `G(R,S)` has as vertices the (0,1)-matrices with row
sum vector `R` and column sum vector `S`, two being adjacent when they differ by a single 2x2
interchange. Brualdi conjectured that `G(R,S)` is always Hamiltonian. The paper proves the stronger
statement that `G(R,S)` is **maximally Hamiltonian**: Hamilton-laceable when bipartite,
Hamilton-connected when not.

**This repository is the proof, checked by machine.** The composed statement is proved from Lean's
foundations together with seven cited results of the literature, and nothing else. No assumption of
ours remains.

## Verify it yourself

```sh
cd brualdi_lean
lake exe cache get                                    # fetch the mathlib build cache
lake build                                            # gate 1: the development compiles
test -f .lake/build/lib/lean/BrualdiLean/Sec5.olean   #         ... and Section 5 really was built
lake env lean CheckAxioms.lean                        # gate 2: print the axiom trace
```

The last command prints the complete trust boundary of the main theorem: Lean's own three axioms
(`propext`, `Classical.choice`, `Quot.sound`) together with the cited external results, and nothing
else. Anything not on that list is *proved here*.

`.github/workflows/verify.yml` runs all of this on GitHub's runners on every push, and adds an
independent kernel re-check of every compiled file (`leanchecker`).

## What to read

- **`brualdi_lean/TRUST_SURFACE.md`** — start here. It states the final theorem, explains the
  definitions it factors through, identifies every cited axiom on the kernel trace, and quotes the
  corresponding statement from the literature, so that a reader can decide whether *the Lean theorem is
  the paper's theorem*. Part I is a guided tour; Part II is a definition-by-definition and
  axiom-by-axiom reference.
- **`brualdi_lean/PROOFS.md`** — the map from the paper's numbered results to their formal counterparts.

The kernel certifies the deduction. It cannot certify that the formal statement means what the English
statement means, nor that the cited theorems say what we claim they say. Those two things are what the
trust surface is for, and they are where a skeptical reader should spend their attention.

## What is here, and what is not

`brualdi_lean/` is the Lean development for the paper: the 20 modules on which the main theorem
`Brualdi.Ledger.brualdi_MH` depends, including machine-checked proofs of the disjoint-path-cover
results the paper imports, and independent alternate proofs of several lemmas. It is the complete
dependency closure of the theorem, and nothing beyond it: work on adjacent problems lives elsewhere and
is not part of this artifact.

- Toolchain: `lean-toolchain` (`leanprover/lean4:v4.31.0`); mathlib pinned in `lakefile.toml`.
- The paper's arXiv version cites this repository at an immutable tag. Use that tag to reproduce
  exactly what the paper claims; `main` may move ahead of it.

## License

Apache 2.0 (see `LICENSE`). The paper itself is distributed separately under CC BY 4.0.
