/-
  Boolean Hamiltonicity checkers and the small adjacency tables (`coreA`, `coreB`, `ct3`)
  consumed by `Sec6`'s PURE-KERNEL certificates. HISTORICAL NOTE: this file once carried
  `native_decide` certificates for these graphs (Tier 1); they were superseded by `Sec6`'s
  foundations-only route and deleted in the 2026-07-08 hard-pass cleanup, so the repository
  is now `native_decide`-free.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Tactic

namespace Brualdi.FiniteCerts

/-! ### Generic Boolean Hamiltonicity checkers on `Fin n` (kernel-evaluable). -/

/-- Symmetric Boolean adjacency on `Fin n` built from an undirected edge list. -/
def mkAdj {n : ℕ} (edges : List (Fin n × Fin n)) : Fin n → Fin n → Bool :=
  fun a b => edges.any (fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a))

/-- Consecutive vertices of the list are adjacent. -/
def pathOK {n : ℕ} (adj : Fin n → Fin n → Bool) : List (Fin n) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => adj a b && pathOK adj (b :: t)

/-- There is a Hamilton path from `u` to `v`: some permutation of all `n` vertices starts at
    `u`, ends at `v`, and is a walk. (Permutations of `finRange n` are automatically the
    length-`n` vertex-distinct lists.) -/
def hasHamPath {n : ℕ} (adj : Fin n → Fin n → Bool) (u v : Fin n) : Bool :=
  ((List.finRange n).permutations).any
    (fun p => (p.head? == some u) && (p.getLast? == some v) && pathOK adj p)

/-- Hamilton-connected: a Hamilton path between every ordered pair of distinct vertices. -/
def hamConnected {n : ℕ} (adj : Fin n → Fin n → Bool) : Bool :=
  (List.finRange n).all
    (fun u => (List.finRange n).all (fun v => (u == v) || hasHamPath adj u v))

/-- Hamilton-laceable: a Hamilton path between every opposite-colour pair. -/
def hamLaceable {n : ℕ} (adj : Fin n → Fin n → Bool) (col : Fin n → Bool) : Bool :=
  (List.finRange n).all
    (fun u => (List.finRange n).all (fun v => (col u == col v) || hasHamPath adj u v))

/-! ### The two |V|=6-or-less non-Johnson base cores (manuscript §6 census). -/

/-- The interchange graph `G((2,1,1),(2,1,1))` — 5 vertices, non-bipartite (4 triangles).
    Edges computed from the actual class enumeration. -/
def coreA : Fin 5 → Fin 5 → Bool :=
  mkAdj [(0,1),(0,2),(0,4),(1,3),(1,4),(2,3),(2,4),(3,4)]

/-- The interchange graph `G((2,2,1),(2,2,1))` (the 3×3 complement of `coreA`) — 5 vertices,
    non-bipartite (4 triangles). -/
def coreB : Fin 5 → Fin 5 → Bool :=
  mkAdj [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,4),(3,4)]



/-! ### CT₃ = K₃,₃ = G((1,1,1),(1,1,1)) : the smallest CORE base, Hamilton-laceable. -/

/-- `K₃,₃` on `Fin 6` with sides `{0,1,2}` and `{3,4,5}`. -/
def ct3 : Fin 6 → Fin 6 → Bool :=
  fun a b => (decide (a.val < 3)) != (decide (b.val < 3))

/-- The bipartition colouring of `K₃,₃`. -/
def ct3col : Fin 6 → Bool := fun v => decide (v.val < 3)


end Brualdi.FiniteCerts
