/-
  Family 1 of the Brualdi path-3 program: for m <= 2, the interchange graph G(r,s) is
  isomorphic to a JOHNSON graph J(f,k), hence MH by Alspach's theorem.

  Here we (i) define the Johnson graph and (ii) state Alspach's theorem (the cited fact,
  axiom A10 in `Ledger.lean` as `johnson_isMH`). A historical `native_decide` demo of the
  smallest case J(4,2) was removed in the 2026-07-08 hard-pass cleanup (superseded by the
  pure-kernel certificates of `Sec6`); the repository is now `native_decide`-free.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic

namespace Brualdi.Johnson

/-- Vertices of the Johnson graph J(n,k): the `k`-element subsets of `Fin n`. -/
abbrev JV (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- Two `k`-subsets are Johnson-adjacent iff they share `k-1` elements (differ by one swap). -/
def Jadj {n k : ℕ} (s t : JV n k) : Prop := (s.1 ∩ t.1).card = k - 1

/-- The Johnson graph J(n,k) (symmetrized and loop-free via `fromRel`). -/
def Jgraph (n k : ℕ) : SimpleGraph (JV n k) :=
  SimpleGraph.fromRel (fun s t => (s.1 ∩ t.1).card = k - 1)

/- HISTORICAL NOTE: an early version declared `axiom johnson_isHamiltonian` here (Alspach's
  theorem in its weak Hamiltonicity form). It was never used by the mainline — the trace axiom is
  `johnson_isMH` (Ledger.lean), Alspach's Hamilton-connectedness weakened to `IsMH` — and it was
  removed in the 2026-07-08 hard pass so that the repository's `axiom` declarations match the
  seven-axiom trace exactly. -/

end Brualdi.Johnson
