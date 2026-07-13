/-
  Brualdi interchange-graph Hamiltonicity -- definitions + conjecture (learning scaffold).

  This file *type-checks* even though the hard proofs are `sorry`. That is the point:
  Lean forces every definition to be precise, and a `sorry` is a clearly-marked hole.
  Read top to bottom; each block has a plain-English comment.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Brualdi

variable {m n : ℕ}

/-- A 0/1 matrix is just a grid of Booleans: `m` rows, `n` columns. -/
abbrev ZeroOneMat (m n : ℕ) := Fin m → Fin n → Bool

/-- The number of 1s in row `i` (a Bool counts as 1 if `true`, else 0). -/
def rowSum (M : ZeroOneMat m n) (i : Fin m) : ℕ := ∑ j, (if M i j then 1 else 0)

/-- The number of 1s in column `j`. -/
def colSum (M : ZeroOneMat m n) (j : Fin n) : ℕ := ∑ i, (if M i j then 1 else 0)

/-- `M` has the prescribed row-sum vector `r` and column-sum vector `s`. -/
def HasMargins (r : Fin m → ℕ) (s : Fin n → ℕ) (M : ZeroOneMat m n) : Prop :=
  (∀ i, rowSum M i = r i) ∧ (∀ j, colSum M j = s j)

/-- The vertex set of the flip graph: all 0/1 matrices with margins `r`, `s`. -/
abbrev MarginClass (r : Fin m → ℕ) (s : Fin n → ℕ) : Type :=
  {M : ZeroOneMat m n // HasMargins r s M}

/--
  One oriented 2x2 interchange sends `M` to `M'`: in some two rows `i ≠ i'` and two
  columns `j ≠ j'`, the block `[[1,0],[0,1]]` becomes `[[0,1],[1,0]]`, and `M'` agrees
  with `M` everywhere outside those four cells.
-/
def Interchange (M M' : ZeroOneMat m n) : Prop :=
  ∃ (i i' : Fin m) (j j' : Fin n), i ≠ i' ∧ j ≠ j' ∧
    M i j = true ∧ M i' j' = true ∧ M i j' = false ∧ M i' j = false ∧
    M' i j = false ∧ M' i' j' = false ∧ M' i j' = true ∧ M' i' j = true ∧
    (∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → M' a b = M a b)

/--
  **The Brualdi flip graph.** Vertices are 0/1 matrices with margins `r, s`; two are
  adjacent iff one is obtained from the other by a single 2x2 interchange.

  We use `SimpleGraph.fromRel`, which takes any relation and automatically makes it
  symmetric and loop-free: `Adj M M' ↔ M ≠ M' ∧ (Interchange M M' ∨ Interchange M' M)`.
-/
def flipGraph (r : Fin m → ℕ) (s : Fin n → ℕ) : SimpleGraph (MarginClass r s) :=
  SimpleGraph.fromRel (fun M M' => Interchange M.val M'.val)

/-
  **Brualdi's conjecture (strengthened) is proved elsewhere in this development.** That every
  `flipGraph r s` is maximally Hamiltonian -- hence Hamiltonian -- is `Brualdi.Ledger.brualdi_MH`
  in `BrualdiLean/Ledger.lean`, established modulo an explicit list of cited-theorem axioms (see
  `README.md`). We deliberately do NOT restate it here as a `sorry`: this file is definitions only.
-/

end Brualdi
