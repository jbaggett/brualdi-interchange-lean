/-
  Brualdi-MH -- core definitions layer (Lean 4, mathlib v4.31.0).

  SPLIT OUT of Coleman.lean on 2026-07-06 (the A2/A3 flip): this file owns every ledger
  DEFINITION and every axiom-free lemma about them, so that the from-scratch proof files
  (DPC.lean, DPC2.lean) can sit between the definitions and the cited-axiom layer
  (Coleman.lean, which now imports them and derives the former axioms A2 and A3 as theorems).
  Nothing in this file declares or uses a project axiom.
-/
import BrualdiLean.Basic
import BrualdiLean.Johnson
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic


set_option autoImplicit false

namespace Brualdi.Ledger
open Brualdi

variable {V : Type*} [DecidableEq V]

/-- D3a: a Hamilton path between `u` and `v`. -/
def HasHamPath (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, p.IsHamiltonian

/-- D3b: Hamilton-connected. -/
def IsHamConnected (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → HasHamPath G u v

/-- D3c: Hamilton-laceable wrt a 2-colouring `col`. -/
def IsHamLaceable (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ u v : V, col u ≠ col v → HasHamPath G u v

/-- D3: Maximal Hamiltonicity. The laceable disjunct requires `col` to be a *proper* 2-colouring
    (`∀ u v, G.Adj u v → col u ≠ col v`) that is *surjective* (both colour classes nonempty). Both guards
    are needed for faithfulness: without proper, a constant colour makes `IsHamLaceable` vacuous; without
    surjectivity, an edgeless graph still satisfies it vacuously (two isolated vertices are not MH). -/
def IsMH (G : SimpleGraph V) : Prop :=
  IsHamConnected G ∨ ∃ col : V → Bool,
    (∀ u v, G.Adj u v → col u ≠ col v) ∧ Function.Surjective col ∧ IsHamLaceable G col

/-- D8: spanning-2-DPC for opposite-colour demands wrt `col`. -/
def IsSpanning2DPCOpposite (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : V,
    col a₁ ≠ col b₁ → col a₂ ≠ col b₂ →
    a₁ ≠ a₂ → a₁ ≠ b₂ → b₁ ≠ a₂ → b₁ ≠ b₂ → a₁ ≠ b₁ → a₂ ≠ b₂ →
    ∃ (p : G.Walk a₁ b₁) (q : G.Walk a₂ b₂),
      p.IsPath ∧ q.IsPath ∧
      (∀ x, x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ x, ¬ (x ∈ p.support ∧ x ∈ q.support))

/-- D2': `G` IS an interchange graph — it is (isomorphic to) `flipGraph r s` for some margins.
    A genuine predicate (not every graph satisfies it): this is what keeps the axioms below sound. -/
def IsInterchangeGraph (G : SimpleGraph V) : Prop :=
  ∃ (m n : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ) (φ : V ≃ MarginClass r s),
    ∀ a b, G.Adj a b ↔ (flipGraph r s).Adj (φ a) (φ b)

/-- D7': `col` is a proper 2-colouring of `G` (a bipartiteness witness). NOTE: despite the name, this
    predicate asserts **only** properness (`G` is bipartite) — there is NO equal-class-size condition
    here. "Balanced" names the *semantic class* (balanced-bipartite interchange graphs), where balance
    is automatic (Prop 2.2 / `weak_ct_product`); the explicit equal-parts condition, where CORE needs
    it, is the separate `IsEquitableBipartite`. -/
def IsProper2Coloring (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ u v, G.Adj u v → col u ≠ col v

/-- `G` is an interchange graph in the base class: it is (isomorphic to) a Johnson graph J(n,k) —
    the ≤2-active-line case — or has at most 6 vertices (the small directly-checked cases). -/
def IsBaseClass {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsInterchangeGraph G ∧
    ((∃ (n k : ℕ), 0 < k ∧ k < n ∧ Nonempty (G ≃g Brualdi.Johnson.Jgraph n k)) ∨
      Fintype.card V ≤ 6)

/-- `G` is **decomposable**: isomorphic to a nontrivial Cartesian (box) product of two smaller
    **interchange** graphs. Uses Mathlib's `SimpleGraph.boxProd` (`□`) — the established encoding of §4's
    products. The factors are required to be interchange graphs (as the §2.2 invariant-position
    decomposition guarantees): this is exactly what lets the §4 induction hypothesis apply to each factor.
    The `DecidableEq`/`Fintype` instances on the factor vertex types are bundled so the IH (which needs
    them) can be invoked. -/
def IsDecomposable {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (W₁ W₂ : Type) (_ : DecidableEq W₁) (_ : DecidableEq W₂) (_ : Fintype W₁) (_ : Fintype W₂)
      (A : SimpleGraph W₁) (B : SimpleGraph W₂),
    Nontrivial W₁ ∧ Nontrivial W₂ ∧ IsInterchangeGraph A ∧ IsInterchangeGraph B ∧
      Nonempty (G ≃g A □ B)

/-- `G` is indecomposable-non-base = the residual trichotomy case: non-bipartite, not a base class, and
    not decomposable. Defined as the "else" branch, which makes the trichotomy a classical tautology;
    the mathematical content lives in the branch axioms + the (deferred) base/decomposable definitions. -/
def IsIndecomposableNonBase {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬(∃ col, IsProper2Coloring G col) ∧ ¬IsBaseClass G ∧ ¬IsDecomposable G

variable {V : Type*} [DecidableEq V]

def IsPairedDPC (G : SimpleGraph V) (k : Nat) (s t : Fin k → V) : Prop :=
  ∃ p : ∀ i : Fin k, G.Walk (s i) (t i),
    (∀ i : Fin k, (p i).IsPath) ∧
    (∀ x : V, ∃ i : Fin k, x ∈ (p i).support) ∧
    (∀ i j : Fin k, i ≠ j → ∀ x : V,
      ¬ (x ∈ (p i).support ∧ x ∈ (p j).support))

/-- A paired demand `s, t : Fin k → V` whose `k` source/target pairs are **opposite-coloured** and all
    `2k` endpoints distinct. FAITHFULNESS NOTE: the disjoint-path-cover sources (Jo–Park–Chwa, Coleman)
    phrase paired-`k`-DPC over sets `S ⊆ V₁`, `T ⊆ V₂` (each side inside one colour class). This
    pairwise-opposite `(s i, t i)` encoding is *equivalent* to that "S in one part, T in the other" form
    for an equitable bipartite graph, via a trivial within-pair relabelling (swap `s i ↔ t i` where
    needed so all sources land in `V₁`) together with walk reversal — a pair's two endpoints are
    oppositely coloured, so exactly one lies in each part. We use the pairwise form throughout; the
    relabelling is left implicit as it does not affect any conclusion. -/
def OppositeDemand (col : V → Bool) {k : Nat} (s t : Fin k → V) : Prop :=
  (∀ i : Fin k, col (s i) ≠ col (t i)) ∧
  Function.Injective s ∧
  Function.Injective t ∧
  (∀ i j : Fin k, s i ≠ t j)

def IsPairedKDPCForOpposite (G : SimpleGraph V) (col : V → Bool) (k : Nat) : Prop :=
  ∀ s t : Fin k → V, OppositeDemand col s t → IsPairedDPC G k s t

def pairMap (x0 x1 : V) (i : Fin 2) : V :=
  if i = 0 then x0 else x1

omit [DecidableEq V] in
@[simp] theorem pairMap_zero (x0 x1 : V) : pairMap x0 x1 (0 : Fin 2) = x0 := by
  simp [pairMap]

omit [DecidableEq V] in
@[simp] theorem pairMap_one (x0 x1 : V) : pairMap x0 x1 (1 : Fin 2) = x1 := by
  simp [pairMap]

omit [DecidableEq V] in
theorem spanning2_of_paired_two_opposite {G : SimpleGraph V} {col : V → Bool}
    (h : IsPairedKDPCForOpposite G col 2) :
    IsSpanning2DPCOpposite G col := by
  intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁a₂ ha₁b₂ hb₁a₂ hb₁b₂ ha₁b₁ ha₂b₂
  let s : Fin 2 → V := pairMap a₁ a₂
  let t : Fin 2 → V := pairMap b₁ b₂
  have hd : OppositeDemand col s t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [s, t, hc₁, hc₂]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [s] at hij ⊢
      · exact (ha₁a₂ hij).elim
      · exact (ha₁a₂ hij.symm).elim
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [t] at hij ⊢
      · exact (hb₁b₂ hij).elim
      · exact (hb₁b₂ hij.symm).elim
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [s, t]
      · exact ha₁b₁
      · exact ha₁b₂
      · exact fun h => hb₁a₂ h.symm
      · exact ha₂b₂
  rcases h s t hd with ⟨p, hpPath, hcover, hdisj⟩
  let p₀ : G.Walk a₁ b₁ :=
    (p (0 : Fin 2)).copy (by simp [s]) (by simp [t])
  let p₁ : G.Walk a₂ b₂ :=
    (p (1 : Fin 2)).copy (by simp [s]) (by simp [t])
  refine ⟨p₀, p₁, ?_, ?_, ?_, ?_⟩
  · simpa [p₀, SimpleGraph.Walk.isPath_copy] using hpPath (0 : Fin 2)
  · simpa [p₁, SimpleGraph.Walk.isPath_copy] using hpPath (1 : Fin 2)
  · intro x
    rcases hcover x with ⟨i, hi⟩
    fin_cases i
    · left
      simpa [p₀, SimpleGraph.Walk.support_copy] using hi
    · right
      simpa [p₁, SimpleGraph.Walk.support_copy] using hi
  · intro x hx
    exact (hdisj (0 : Fin 2) (1 : Fin 2) (by decide) x) (by
      simpa [p₀, p₁, SimpleGraph.Walk.support_copy] using hx)

omit [DecidableEq V] in
theorem paired_two_of_spanning2 {G : SimpleGraph V} {col : V → Bool}
    (h : IsSpanning2DPCOpposite G col) :
    IsPairedKDPCForOpposite G col 2 := by
  intro s t hd
  rcases hd with ⟨hcol, hs, ht, hst⟩
  have hs01 : s (0 : Fin 2) ≠ s (1 : Fin 2) := by
    intro hEq
    exact (by decide : (0 : Fin 2) ≠ 1) (hs hEq)
  have ht01 : t (0 : Fin 2) ≠ t (1 : Fin 2) := by
    intro hEq
    exact (by decide : (0 : Fin 2) ≠ 1) (ht hEq)
  rcases h (s (0 : Fin 2)) (t (0 : Fin 2)) (s (1 : Fin 2)) (t (1 : Fin 2))
      (hcol (0 : Fin 2)) (hcol (1 : Fin 2)) hs01 (hst (0 : Fin 2) (1 : Fin 2))
      (fun hEq => hst (1 : Fin 2) (0 : Fin 2) hEq.symm) ht01
      (hst (0 : Fin 2) (0 : Fin 2)) (hst (1 : Fin 2) (1 : Fin 2)) with
    ⟨p₀, p₁, hp₀, hp₁, hcover, hdisj⟩
  let p : ∀ i : Fin 2, G.Walk (s i) (t i) := fun i =>
    if h0 : i = (0 : Fin 2) then
      p₀.copy (by rw [h0]) (by rw [h0])
    else
      have h1 : i = (1 : Fin 2) := by
        apply Fin.ext
        have hne : i.1 ≠ 0 := by
          intro hval
          exact h0 (Fin.ext hval)
        omega
      p₁.copy (by rw [h1]) (by rw [h1])
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [p, SimpleGraph.Walk.isPath_copy] using hp₀
    · simpa [p, SimpleGraph.Walk.isPath_copy] using hp₁
  · intro x
    rcases hcover x with hx | hx
    · exact ⟨(0 : Fin 2), by simpa [p, SimpleGraph.Walk.support_copy] using hx⟩
    · exact ⟨(1 : Fin 2), by simpa [p, SimpleGraph.Walk.support_copy] using hx⟩
  · intro i j hij x hx
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdisj x (by simpa [p, SimpleGraph.Walk.support_copy] using hx)
    · exact hdisj x (by
        constructor
        · simpa [p] using hx.2
        · simpa [p, SimpleGraph.Walk.support_copy] using hx.1)
    · exact (hij rfl).elim

def IsEquitableBipartite [Fintype V] (G : SimpleGraph V) (col : V → Bool) : Prop :=
  IsProper2Coloring G col ∧
    Fintype.card {v : V // col v = false} = Fintype.card {v : V // col v = true}

theorem paired_one_opposite_iff_hamLaceable [Fintype V] {G : SimpleGraph V} {col : V → Bool} :
    IsPairedKDPCForOpposite G col 1 ↔ IsHamLaceable G col := by
  constructor
  · intro h u v huv
    let s : Fin 1 → V := fun _ => u
    let t : Fin 1 → V := fun _ => v
    have huv_ne : u ≠ v := fun hEq => huv (congrArg col hEq)
    have hd : OppositeDemand col s t := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        simpa [s, t] using huv
      · intro i j _
        exact Subsingleton.elim i j
      · intro i j _
        exact Subsingleton.elim i j
      · intro i j
        fin_cases i
        fin_cases j
        simpa [s, t] using huv_ne
    rcases h s t hd with ⟨p, hpPath, hcover, _hdisj⟩
    let p₀ : G.Walk u v :=
      (p (0 : Fin 1)).copy (by simp [s]) (by simp [t])
    refine ⟨p₀, ?_⟩
    have hp₀Path : p₀.IsPath := by
      simpa [p₀, SimpleGraph.Walk.isPath_copy] using hpPath (0 : Fin 1)
    exact hp₀Path.isHamiltonian_iff.mpr (fun x => by
      rcases hcover x with ⟨i, hi⟩
      fin_cases i
      simpa [p₀, SimpleGraph.Walk.support_copy] using hi)
  · intro hHL s t hd
    rcases hd with ⟨hcol, _hs, _ht, _hst⟩
    rcases hHL (s (0 : Fin 1)) (t (0 : Fin 1)) (hcol (0 : Fin 1)) with ⟨p₀, hp₀⟩
    let pFam : ∀ i : Fin 1, G.Walk (s i) (t i) := fun i =>
      p₀.copy (congrArg s (Subsingleton.elim (0 : Fin 1) i))
        (congrArg t (Subsingleton.elim (0 : Fin 1) i))
    refine ⟨pFam, ?_, ?_, ?_⟩
    · intro i
      simpa [pFam, SimpleGraph.Walk.isPath_copy] using hp₀.isPath
    · intro x
      refine ⟨(0 : Fin 1), ?_⟩
      simpa [pFam, SimpleGraph.Walk.support_copy] using hp₀.mem_support x
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim

def CompleteTranspositionGraph (a : Nat) : SimpleGraph (Equiv.Perm (Fin a)) :=
  SimpleGraph.fromRel fun σ τ => Equiv.Perm.IsSwap (σ⁻¹ * τ)

def CompleteTranspositionColor (a : Nat) (σ : Equiv.Perm (Fin a)) : Bool :=
  if Equiv.Perm.sign σ = 1 then false else true

def CTProductVertex : List Nat → Type
  | [] => PUnit
  | [a] => Equiv.Perm (Fin a)
  | a :: b :: ranks => Equiv.Perm (Fin a) × CTProductVertex (b :: ranks)

instance instDecidableEqCTProductVertex (ranks : List Nat) : DecidableEq (CTProductVertex ranks) := by
  induction ranks with
  | nil =>
      simp [CTProductVertex]
      infer_instance
  | cons a ranks ih =>
      cases ranks with
      | nil =>
          simp [CTProductVertex]
          infer_instance
      | cons b ranks =>
          letI := ih
          simp [CTProductVertex]
          infer_instance

instance instFintypeCTProductVertex (ranks : List Nat) : Fintype (CTProductVertex ranks) := by
  induction ranks with
  | nil =>
      simp [CTProductVertex]
      infer_instance
  | cons a ranks ih =>
      cases ranks with
      | nil =>
          simp [CTProductVertex]
          infer_instance
      | cons b ranks =>
          letI := ih
          simp [CTProductVertex]
          infer_instance

def CTProductGraph : (ranks : List Nat) → SimpleGraph (CTProductVertex ranks)
  | [] => ⊥
  | [a] => CompleteTranspositionGraph a
  | a :: b :: ranks => CompleteTranspositionGraph a □ CTProductGraph (b :: ranks)

def CTProductColor : (ranks : List Nat) → CTProductVertex ranks → Bool
  | [], _ => false
  | [a], σ => CompleteTranspositionColor a σ
  | a :: b :: ranks, x => Bool.xor (CompleteTranspositionColor a x.1) (CTProductColor (b :: ranks) x.2)

/-- The **weld** of equal-order copies `Gs i` on a vertex type `W`, glued by an arbitrary perfect matching
    `M i j : W ≃ W` between every pair of copies (`(i,u)` matched to `(j, M i j u)` for `i ≠ j`). This is
    exactly Coleman's "disjoint copies + a perfect matching between every pair of copies"; it lives on
    `Fin ell × W` (`fromRel` symmetrises, so a consistent family `M j i = (M i j).symm` gives a clean
    matching). General `M` (not just coherent relabellings) is what `CT_a`'s coset matchings need. -/
def weldGraph {W : Type*} (ell : ℕ) (Gs : Fin ell → SimpleGraph W) (M : Fin ell → Fin ell → (W ≃ W)) :
    SimpleGraph (Fin ell × W) :=
  SimpleGraph.fromRel (fun p q =>
    (p.1 = q.1 ∧ (Gs p.1).Adj p.2 q.2) ∨ (p.1 ≠ q.1 ∧ q.2 = M p.1 q.1 p.2))

/-- **Coleman welding tree** (Def 1.2/1.3 + the Thm 1.5 leaf condition, over ONE tree): rank 1 = a
    Hamilton-connected graph, or a Hamilton-laceable graph with respect to a *proper surjective*
    2-colouring (Def 1.3's "Hamiltonian-connected or Hamiltonian-laceable" — the properness and
    surjectivity make laceability non-vacuous), which moreover is a single vertex or of even order
    (Thm 1.5's leaf condition); rank `r ≥ 2` = a weld of `ell ≥ r` rank-`(r-1)` trees of equal order.
    RE-AUDITED VERBATIM 2026-07-04: this REPLACES the former pair of separate inductives
    (`IsTranspositionLike` + `ColemanLeavesSingleOrEven`), which was UNSOUND on two counts caught by
    the Coleman re-read: (i) the old rank-1 base `∃ col, IsHamLaceable G col` was vacuous for a
    constant colouring, admitting every graph as a leaf (concrete counterexample: the weld of two
    2-vertex edgeless graphs is `2K₂`, disconnected, yet satisfied every hypothesis of the axiom at
    `n = 2`); (ii) the two conditions were witnessable by *different* welding trees, whereas Coleman
    states both over the single tree "during the welding process to form G". -/
inductive IsColemanTree : {V : Type} → SimpleGraph V → ℕ → Prop where
  | base {V : Type} [DecidableEq V] {G : SimpleGraph V}
      (hham : IsHamConnected G ∨
        ∃ col : V → Bool, IsProper2Coloring G col ∧ Function.Surjective col ∧
          IsHamLaceable G col)
      (hcard : Nat.card V = 1 ∨ Even (Nat.card V)) :
      IsColemanTree G 1
  | weld {V W : Type} {G : SimpleGraph V} {ell r : ℕ} {Gs : Fin ell → SimpleGraph W}
      {M : Fin ell → Fin ell → (W ≃ W)}
      (hr : 2 ≤ r) (hEll : r ≤ ell) (htl : ∀ i, IsColemanTree (Gs i) (r - 1))
      (hM : ∀ i j, M j i = (M i j).symm)
      (e : G ≃g weldGraph ell Gs M) :
      IsColemanTree G r

/-- An equitable proper 2-colouring of a nonempty graph is surjective (both classes nonempty). -/
theorem surjective_of_equitable_nonempty {V : Type} [Fintype V] {G : SimpleGraph V}
    {col : V → Bool} (hEq : IsEquitableBipartite G col) (hne : Nonempty V) :
    Function.Surjective col := by
  classical
  have hcard := hEq.2
  have htot : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hne
  have hsplit : Fintype.card {v : V // col v = false} + Fintype.card {v : V // col v = true}
      = Fintype.card V := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : col v
      · exact iff_of_true (Or.inl rfl) trivial
      · exact iff_of_true (Or.inr rfl) trivial
    · rw [Finset.disjoint_filter]
      intro v _ hf ht
      rw [hf] at ht
      cases ht
  have hpos : 0 < Fintype.card {v : V // col v = false} := by omega
  intro b
  cases b
  · obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨v, hv⟩
  · have hpos' : 0 < Fintype.card {v : V // col v = true} := by omega
    obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.mp hpos'
    exact ⟨v, hv⟩

/-- An equitable 2-colouring forces even order (`card = |false class| + |true class| = 2·|false|`). -/
theorem equitable_even_card {V : Type} [Fintype V] {G : SimpleGraph V} {col : V → Bool}
    (hEq : IsEquitableBipartite G col) : Even (Fintype.card V) := by
  classical
  have hsplit : Fintype.card {v : V // col v = false} + Fintype.card {v : V // col v = true}
      = Fintype.card V := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : col v
      · exact iff_of_true (Or.inl rfl) trivial
      · exact iff_of_true (Or.inr rfl) trivial
    · rw [Finset.disjoint_filter]
      intro v _ hf ht
      rw [hf] at ht
      cases ht
  have h2 := hEq.2
  exact ⟨Fintype.card {v : V // col v = false}, by omega⟩

/-- A 2-vertex graph with an edge is Hamilton-laceable for ANY colouring: the sole Hamilton path is
    the edge itself. (The degenerate-order case that the `prop11c` demand guard excludes.) -/
theorem laceable_card_two {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    (col : V → Bool) (hcard : Fintype.card V = 2) (hedge : ∃ u v, G.Adj u v) :
    IsHamLaceable G col := by
  obtain ⟨u, v, huv⟩ := hedge
  intro x y hxy
  have hxyne : x ≠ y := fun h => hxy (by rw [h])
  have huniv : ({x, y} : Finset V) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hxyne]), Finset.card_singleton, hcard]
  have hall : ∀ z : V, z = x ∨ z = y := by
    intro z
    have hz : z ∈ ({x, y} : Finset V) := huniv.symm ▸ Finset.mem_univ z
    simpa using hz
  have hadj : G.Adj x y := by
    rcases hall u with rfl | rfl <;> rcases hall v with rfl | rfl
    · exact absurd rfl (G.ne_of_adj huv)
    · exact huv
    · exact huv.symm
    · exact absurd rfl (G.ne_of_adj huv)
  refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
  intro z
  rcases hall z with rfl | rfl <;>
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.count_cons,
      hxyne, hxyne.symm]

/-- The CT-colour is `false` exactly on the even permutations. -/
theorem ctColor_false_iff (a : Nat) (σ : Equiv.Perm (Fin a)) :
    CompleteTranspositionColor a σ = false ↔ Equiv.Perm.sign σ = 1 := by
  unfold CompleteTranspositionColor
  split <;> simp_all

/-- The CT-colour is `true` exactly on the odd permutations. -/
theorem ctColor_true_iff (a : Nat) (σ : Equiv.Perm (Fin a)) :
    CompleteTranspositionColor a σ = true ↔ Equiv.Perm.sign σ = -1 := by
  constructor
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [(ctColor_false_iff a σ).mpr hs] at h; exact absurd h (by decide)
    · exact hs
  · intro h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs] at h; exact absurd h (by decide)
    · have hne : CompleteTranspositionColor a σ ≠ false := by
        intro hc
        have h1 := (ctColor_false_iff a σ).mp hc
        rw [h1] at hs; exact absurd hs (by decide)
      cases hcol : CompleteTranspositionColor a σ
      · exact absurd hcol hne
      · rfl

/-- CT_a is properly 2-coloured by permutation parity (the bipartiteness witness). -/
theorem completeTransposition_balanced (a : Nat) :
    IsProper2Coloring (CompleteTranspositionGraph a) (CompleteTranspositionColor a) := by
  intro u v huv
  have hsw : (u⁻¹ * v).IsSwap ∨ (v⁻¹ * u).IsSwap := by
    have h := huv
    simp only [CompleteTranspositionGraph, SimpleGraph.fromRel_adj] at h
    exact h.2
  have hne : Equiv.Perm.sign u ≠ Equiv.Perm.sign v := by
    intro heq
    have key : Equiv.Perm.sign (u⁻¹ * v) = -1 ∨ Equiv.Perm.sign (v⁻¹ * u) = -1 :=
      hsw.imp Equiv.Perm.IsSwap.sign_eq Equiv.Perm.IsSwap.sign_eq
    have sq : Equiv.Perm.sign v * Equiv.Perm.sign v = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign v) with h | h <;> simp [h]
    rcases key with h | h
    · rw [map_mul, Equiv.Perm.sign_inv, heq, sq] at h; exact absurd h (by decide)
    · rw [map_mul, Equiv.Perm.sign_inv, heq, sq] at h; exact absurd h (by decide)
  rcases Int.units_eq_one_or (Equiv.Perm.sign u) with su | su <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign v) with sv | sv
  · exact absurd (su.trans sv.symm) hne
  · rw [(ctColor_false_iff a u).mpr su, (ctColor_true_iff a v).mpr sv]; decide
  · rw [(ctColor_true_iff a u).mpr su, (ctColor_false_iff a v).mpr sv]; decide
  · exact absurd (su.trans sv.symm) hne

/-- **(Formerly an axiom; now proved.)** CT_a is equitable bipartite for `a ≥ 3`: the parity
    2-colouring is proper and the even/odd classes have equal size (bijection `σ ↦ (swap)·σ`). -/
theorem completeTransposition_equitable (a : Nat) (ha : 2 ≤ a) :
    IsEquitableBipartite (CompleteTranspositionGraph a) (CompleteTranspositionColor a) := by
  classical
  refine ⟨completeTransposition_balanced a, ?_⟩
  set i : Fin a := ⟨0, by omega⟩ with hi_def
  set j : Fin a := ⟨1, by omega⟩ with hj_def
  have hij : i ≠ j := by simp [hi_def, hj_def, Fin.ext_iff]
  set c : Equiv.Perm (Fin a) := Equiv.swap i j with hc_def
  have hc : Equiv.Perm.sign c = -1 := Equiv.Perm.sign_swap hij
  have hcc : c * c = 1 := Equiv.swap_mul_self i j
  apply Fintype.card_congr
  refine ⟨fun x => ⟨c * x.1, ?_⟩, fun y => ⟨c * y.1, ?_⟩, ?_, ?_⟩
  · have hx := (ctColor_false_iff a x.1).mp x.2
    rw [ctColor_true_iff, map_mul, hc, hx]; decide
  · have hy := (ctColor_true_iff a y.1).mp y.2
    rw [ctColor_false_iff, map_mul, hc, hy]; decide
  · intro x; apply Subtype.ext; change c * (c * x.1) = x.1
    rw [← mul_assoc, hcc, one_mul]
  · intro y; apply Subtype.ext; change c * (c * y.1) = y.1
    rw [← mul_assoc, hcc, one_mul]

/-! ### `CT_a` is a weld of `CT_{a-1}` — discharging the former `ct_weld_iso` axiom. -/
section CTWeldProof
open Equiv Equiv.Perm
variable {n : ℕ}

/-- **Within-coset relation.** Right-multiplying `σ` by a transposition of two `succ`-elements preserves
    the coset (`(decomposeFin _).1`) and right-multiplies the rest (`(decomposeFin _).2`) by the
    corresponding transposition of `Fin n`. This realises the within-copy `CT_{a-1}` edges of the weld. -/
theorem decomposeFin_rest_swapSucc (σ : Perm (Fin (n + 1))) (x0 y0 : Fin n) :
    decomposeFin (σ * swap x0.succ y0.succ)
      = ((decomposeFin σ).1, (decomposeFin σ).2 * swap x0 y0) := by
  have hσ0 : σ 0 = (decomposeFin σ).1 := by
    conv_lhs => rw [← Equiv.symm_apply_apply decomposeFin σ]
    rw [decomposeFin_symm_apply_zero]
  apply decomposeFin.symm.injective
  rw [Equiv.symm_apply_apply]
  ext z
  refine Fin.cases ?_ (fun w => ?_) z
  · rw [decomposeFin_symm_apply_zero, Perm.mul_apply,
        swap_apply_of_ne_of_ne (Fin.succ_ne_zero x0).symm (Fin.succ_ne_zero y0).symm, hσ0]
  · rw [decomposeFin_symm_apply_succ, Perm.mul_apply, Perm.mul_apply,
        ← (Fin.succ_injective n).map_swap x0 y0 w]
    conv_lhs => rw [← Equiv.symm_apply_apply decomposeFin σ]
    rw [decomposeFin_symm_apply_succ]

/-- The coset of `σ` (its `decomposeFin` first coordinate) is `σ 0`. -/
theorem decomposeFin_fst (σ : Perm (Fin (n + 1))) : (decomposeFin σ).1 = σ 0 := by
  conv_rhs => rw [← Equiv.symm_apply_apply decomposeFin σ]
  rw [decomposeFin_symm_apply_zero]

/-- Right-multiplying `σ` by the transposition `swap 0 (σ⁻¹ j)` sends `0` to `j` (lands in coset `j`). -/
theorem mul_swap_zero_apply_zero (σ : Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (σ * Equiv.swap 0 (σ⁻¹ j)) 0 = j := by
  simp [Perm.mul_apply, Equiv.swap_apply_left]

/-- The transposition that the cross-coset partner uses to return: `(σ·swap 0 (σ⁻¹ j))⁻¹ i = σ⁻¹ j`
    when `σ 0 = i`. -/
theorem mul_swap_zero_inv_apply (σ : Perm (Fin (n + 1))) (i j : Fin (n + 1)) (hσ : σ 0 = i) :
    (σ * Equiv.swap 0 (σ⁻¹ j))⁻¹ i = σ⁻¹ j := by
  have hinv : σ⁻¹ i = 0 := by rw [← hσ]; simp
  rw [mul_inv_rev, Equiv.swap_inv, Perm.mul_apply, hinv, Equiv.swap_apply_left]

/-- The cross-coset matching map `coset i → coset j` in rest-coordinates: send `σ` (coset `i`, rest `u`)
    to the rest of `σ · swap 0 (σ⁻¹ j)` (its unique 0-moving-transposition partner in coset `j`). -/
def crossFun (i j : Fin (n + 1)) (u : Perm (Fin n)) : Perm (Fin n) :=
  (decomposeFin (decomposeFin.symm (i, u) * Equiv.swap 0 ((decomposeFin.symm (i, u))⁻¹ j))).2

/-- `crossFun j i` inverts `crossFun i j` (swap² = 1 and the partner returns to `σ`). -/
theorem crossFun_left_inv (i j : Fin (n + 1)) (u : Perm (Fin n)) :
    crossFun j i (crossFun i j u) = u := by
  simp only [crossFun]
  have hσ0 : (decomposeFin.symm (i, u)) 0 = i := decomposeFin_symm_apply_zero i u
  set σ := decomposeFin.symm (i, u) with hσ
  have hdσ : decomposeFin σ = (i, u) := Equiv.apply_symm_apply decomposeFin (i, u)
  set τ := σ * Equiv.swap 0 (σ⁻¹ j) with hτ
  have hτ0 : τ 0 = j := mul_swap_zero_apply_zero σ j
  have hdτ1 : (decomposeFin τ).1 = j := by rw [decomposeFin_fst, hτ0]
  have hsymm : decomposeFin.symm (j, (decomposeFin τ).2) = τ := by
    conv_rhs => rw [← Equiv.symm_apply_apply decomposeFin τ]
    exact congrArg decomposeFin.symm (Prod.ext hdτ1.symm rfl)
  have hτinv : τ⁻¹ i = σ⁻¹ j := mul_swap_zero_inv_apply σ i j hσ0
  rw [hsymm, hτinv,
      show τ * Equiv.swap 0 (σ⁻¹ j) = σ from by rw [hτ, mul_assoc, Equiv.swap_mul_self, mul_one], hdσ]

/-- The cross-coset matching as an equivalence `Perm (Fin n) ≃ Perm (Fin n)` (the weld matching `M i j`). -/
def ctCrossMatch (i j : Fin (n + 1)) : Perm (Fin n) ≃ Perm (Fin n) where
  toFun := crossFun i j
  invFun := crossFun j i
  left_inv := crossFun_left_inv i j
  right_inv := crossFun_left_inv j i

/-! ### Step 3-4: the adjacency match + the iso (Codex-drafted). -/

private theorem isSwap_apply_apply {α : Type*} [DecidableEq α] {g : Perm α}
    (hg : g.IsSwap) (x : α) : g (g x) = x := by
  rcases hg with ⟨a, b, _hab, rfl⟩
  simp

private theorem sameCoset_lift_isSwap {n : ℕ} {σ τ : Perm (Fin (n + 1))}
    (hfst : (decomposeFin σ).1 = (decomposeFin τ).1)
    (hrest : ((decomposeFin σ).2⁻¹ * (decomposeFin τ).2).IsSwap) :
    (σ⁻¹ * τ).IsSwap := by
  rcases hrest with ⟨x, y, hxy, hswap⟩
  have hrest_eq : (decomposeFin τ).2 = (decomposeFin σ).2 * swap x y := by
    calc
      (decomposeFin τ).2 = (decomposeFin σ).2 * ((decomposeFin σ).2⁻¹ * (decomposeFin τ).2) := by
        simp
      _ = (decomposeFin σ).2 * swap x y := by rw [hswap]
  have hτ : τ = σ * swap x.succ y.succ := by
    apply decomposeFin.injective
    rw [decomposeFin_rest_swapSucc]
    exact Prod.ext hfst.symm hrest_eq
  refine ⟨x.succ, y.succ, ?_, ?_⟩
  · intro h
    exact hxy ((Fin.succ_injective n) h)
  · rw [hτ]
    simp

private theorem cross_lift_isSwap {n : ℕ} {σ τ : Perm (Fin (n + 1))}
    (hneq : (decomposeFin σ).1 ≠ (decomposeFin τ).1)
    (hcross : (decomposeFin τ).2 =
      (ctCrossMatch (n := n) (decomposeFin σ).1 (decomposeFin τ).1) (decomposeFin σ).2) :
    (σ⁻¹ * τ).IsSwap := by
  have hcross' : (decomposeFin τ).2 =
      crossFun (decomposeFin σ).1 (decomposeFin τ).1 (decomposeFin σ).2 := by
    simpa [ctCrossMatch] using hcross
  set ρ : Perm (Fin (n + 1)) := σ * swap 0 (σ⁻¹ (decomposeFin τ).1) with hρ
  have hρfst : (decomposeFin ρ).1 = (decomposeFin τ).1 := by
    rw [decomposeFin_fst, hρ, mul_swap_zero_apply_zero]
  have hσsymm : decomposeFin.symm ((decomposeFin σ).1, (decomposeFin σ).2) = σ := by
    simp
  have hρrest : (decomposeFin τ).2 = (decomposeFin ρ).2 := by
    simpa [crossFun, hσsymm, hρ] using hcross'
  have hτ : τ = ρ := by
    apply decomposeFin.injective
    exact Prod.ext hρfst.symm hρrest
  have hne0 : (0 : Fin (n + 1)) ≠ σ⁻¹ (decomposeFin τ).1 := by
    intro h0
    apply hneq
    have hj : σ 0 = (decomposeFin τ).1 := by
      calc
        σ 0 = σ (σ⁻¹ (decomposeFin τ).1) := by rw [h0]
        _ = (decomposeFin τ).1 := by simp
    rw [decomposeFin_fst, hj]
  refine ⟨0, σ⁻¹ (decomposeFin τ).1, hne0, ?_⟩
  calc
    σ⁻¹ * τ = σ⁻¹ * ρ := by rw [hτ]
    _ = swap 0 (σ⁻¹ (decomposeFin τ).1) := by rw [hρ]; simp

private theorem sameCoset_descend_isSwap {n : ℕ} {σ τ : Perm (Fin (n + 1))}
    (hfst : (decomposeFin σ).1 = (decomposeFin τ).1)
    (hs : (σ⁻¹ * τ).IsSwap) :
    ((decomposeFin σ).2⁻¹ * (decomposeFin τ).2).IsSwap := by
  rcases hs with ⟨a, b, hab, hswap⟩
  have hfix0 : (σ⁻¹ * τ) 0 = 0 := by
    have hτ0 : τ 0 = σ 0 := by
      rw [← decomposeFin_fst τ, ← decomposeFin_fst σ, hfst]
    rw [Perm.mul_apply, hτ0]
    simp
  have ha0 : a ≠ 0 := by
    intro ha
    have hb0 : b = 0 := by
      have := hfix0
      rw [hswap, ha, Equiv.swap_apply_left] at this
      exact this
    exact hab (by rw [ha, hb0])
  have hb0 : b ≠ 0 := by
    intro hb
    have ha_eq0 : a = 0 := by
      have := hfix0
      rw [hswap, hb, Equiv.swap_apply_right] at this
      exact this
    exact hab (by rw [ha_eq0, hb])
  obtain ⟨x, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha0
  obtain ⟨y, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hb0
  have hxy : x ≠ y := by
    intro hxy
    exact hab (by rw [hxy])
  have hτ : τ = σ * swap x.succ y.succ := by
    calc
      τ = σ * (σ⁻¹ * τ) := by simp
      _ = σ * swap x.succ y.succ := by rw [hswap]
  have hrest_eq : (decomposeFin τ).2 = (decomposeFin σ).2 * swap x y := by
    rw [hτ, decomposeFin_rest_swapSucc]
  refine ⟨x, y, hxy, ?_⟩
  calc
    (decomposeFin σ).2⁻¹ * (decomposeFin τ).2 =
        (decomposeFin σ).2⁻¹ * ((decomposeFin σ).2 * swap x y) := by rw [hrest_eq]
    _ = swap x y := by simp

private theorem cross_descend {n : ℕ} {σ τ : Perm (Fin (n + 1))}
    (hneq : (decomposeFin σ).1 ≠ (decomposeFin τ).1)
    (hs : (σ⁻¹ * τ).IsSwap) :
    (decomposeFin τ).2 =
      (ctCrossMatch (n := n) (decomposeFin σ).1 (decomposeFin τ).1) (decomposeFin σ).2 := by
  have hmove : (σ⁻¹ * τ) 0 ≠ 0 := by
    intro h0
    apply hneq
    rw [decomposeFin_fst σ, decomposeFin_fst τ]
    have hpre : σ⁻¹ (τ 0) = 0 := by
      simpa [Perm.mul_apply] using h0
    have hτ0σ : τ 0 = σ 0 := by
      calc
        τ 0 = σ (σ⁻¹ (τ 0)) := by simp
        _ = σ 0 := by rw [hpre]
    exact hτ0σ.symm
  have hg : σ⁻¹ * τ = swap 0 ((σ⁻¹ * τ) 0) :=
    hs.isCycle.eq_swap_of_apply_apply_eq_self hmove (isSwap_apply_apply hs 0)
  have hg' : σ⁻¹ * τ = swap 0 (σ⁻¹ (decomposeFin τ).1) := by
    rw [hg]
    congr 1
    rw [Perm.mul_apply, decomposeFin_fst τ]
  have hτ : τ = σ * swap 0 (σ⁻¹ (decomposeFin τ).1) := by
    calc
      τ = σ * (σ⁻¹ * τ) := by simp
      _ = σ * swap 0 (σ⁻¹ (decomposeFin τ).1) := by rw [hg']
  have hσsymm : decomposeFin.symm ((decomposeFin σ).1, (decomposeFin σ).2) = σ := by
    simp
  have hfirst : (decomposeFin τ).2 = (decomposeFin (σ * swap 0 (σ⁻¹ (decomposeFin τ).1))).2 :=
    congrArg Prod.snd (congrArg decomposeFin hτ)
  calc
    (decomposeFin τ).2 = (decomposeFin (σ * swap 0 (σ⁻¹ (decomposeFin τ).1))).2 := hfirst
    _ = (ctCrossMatch (n := n) (decomposeFin σ).1 (decomposeFin τ).1) (decomposeFin σ).2 := by
      simp [ctCrossMatch, crossFun, hσsymm]

theorem ct_weld_adj (n : ℕ) (σ τ : Equiv.Perm (Fin (n + 1))) :
    (weldGraph (n + 1) (fun _ => CompleteTranspositionGraph n)
      (fun i j => ctCrossMatch (n := n) i j)).Adj
        (decomposeFin σ) (decomposeFin τ) ↔
    (CompleteTranspositionGraph (n + 1)).Adj σ τ := by
  classical
  simp only [weldGraph, CompleteTranspositionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · have hneστ : σ ≠ τ := fun h => hne (by rw [h])
      refine ⟨hneστ, ?_⟩
      rcases hrel with hsame | hcross
      · rcases hsame with ⟨hfst, _hrest_ne, hsw | hsw⟩
        · exact Or.inl (sameCoset_lift_isSwap hfst hsw)
        · exact Or.inr (sameCoset_lift_isSwap hfst.symm hsw)
      · rcases hcross with ⟨hneq, hmatch⟩
        exact Or.inl (cross_lift_isSwap hneq hmatch)
    · have hneστ : σ ≠ τ := fun h => hne (by rw [h])
      refine ⟨hneστ, ?_⟩
      rcases hrel with hsame | hcross
      · rcases hsame with ⟨hfst, _hrest_ne, hsw | hsw⟩
        · exact Or.inr (sameCoset_lift_isSwap hfst hsw)
        · exact Or.inl (sameCoset_lift_isSwap hfst.symm hsw)
      · rcases hcross with ⟨hneq, hmatch⟩
        exact Or.inr (cross_lift_isSwap hneq hmatch)
  · rintro ⟨hne, hs | hs⟩
    · have hned : decomposeFin σ ≠ decomposeFin τ := fun h => hne (decomposeFin.injective h)
      refine ⟨hned, ?_⟩
      by_cases hfst : (decomposeFin σ).1 = (decomposeFin τ).1
      · left
        left
        refine ⟨hfst, ?_, Or.inl (sameCoset_descend_isSwap hfst hs)⟩
        intro hrest
        apply hne
        apply decomposeFin.injective
        exact Prod.ext hfst hrest
      · left
        right
        exact ⟨hfst, cross_descend hfst hs⟩
    · have hned : decomposeFin σ ≠ decomposeFin τ := fun h => hne (decomposeFin.injective h)
      refine ⟨hned, ?_⟩
      by_cases hfst : (decomposeFin σ).1 = (decomposeFin τ).1
      · left
        left
        refine ⟨hfst, ?_, Or.inr (sameCoset_descend_isSwap hfst.symm hs)⟩
        intro hrest
        apply hne
        apply decomposeFin.injective
        exact Prod.ext hfst hrest
      · right
        right
        exact ⟨fun h => hfst h.symm, cross_descend (fun h => hfst h.symm) hs⟩

def ct_weld_isoN (n : ℕ) :
    CompleteTranspositionGraph (n + 1) ≃g
    weldGraph (n + 1) (fun _ => CompleteTranspositionGraph n)
      (fun i j => ctCrossMatch (n := n) i j) :=
  { toEquiv := decomposeFin,
    map_rel_iff' := by
      intro σ τ
      exact ct_weld_adj n σ τ }

/-- **`ct_weld_iso` discharged:** `CT_a` is a weld of `a` copies of `CT_{a-1}`. -/
theorem ct_weld_iso_proof (a : ℕ) (ha : 2 ≤ a) :
    ∃ M : Fin a → Fin a → (Equiv.Perm (Fin (a - 1)) ≃ Equiv.Perm (Fin (a - 1))),
    (∀ i j, M j i = (M i j).symm) ∧
    Nonempty (CompleteTranspositionGraph a ≃g
      weldGraph a (fun _ => CompleteTranspositionGraph (a - 1)) M) := by
  cases a with
  | zero => omega
  | succ n =>
      refine ⟨fun i j => by simpa using (ctCrossMatch (n := n) i j), ?_, ?_⟩
      · intro i j
        exact Equiv.ext (fun u => rfl)
      · refine ⟨?_⟩
        simpa using (ct_weld_isoN n)

end CTWeldProof

theorem ct_weld_iso (a : Nat) (ha : 2 ≤ a) :
    ∃ M : Fin a → Fin a → (Equiv.Perm (Fin (a - 1)) ≃ Equiv.Perm (Fin (a - 1))),
      (∀ i j, M j i = (M i j).symm) ∧
      Nonempty (CompleteTranspositionGraph a ≃g
        weldGraph a (fun _ => CompleteTranspositionGraph (a - 1)) M) :=
  ct_weld_iso_proof a ha

/-- `CT_1` is a single vertex, hence (vacuously) Hamilton-connected. -/
private theorem ct1_hamConnected : IsHamConnected (CompleteTranspositionGraph 1) :=
  fun u v huv => absurd (Subsingleton.elim u v) huv

/-- `CT_a` carries a Coleman welding tree of rank `a` — PROVED by induction on `a` from
    `ct_weld_iso` and the single-vertex rank-1 base. -/
theorem ct_tree : ∀ a : Nat, 1 ≤ a →
    IsColemanTree (CompleteTranspositionGraph a) a
  | 0, h => absurd h (by omega)
  | 1, _ => IsColemanTree.base (Or.inl ct1_hamConnected)
      (Or.inl (by simp [Nat.card_eq_fintype_card, Fintype.card_perm]))
  | (n + 2), _ => by
      obtain ⟨M, hM, ⟨e⟩⟩ := ct_weld_iso (n + 2) (by omega)
      exact IsColemanTree.weld (by omega) (le_refl _)
        (fun _ => ct_tree (n + 1) (by omega)) hM e

theorem completeTransposition_tree (a : Nat) (ha : 3 ≤ a) :
    IsColemanTree (CompleteTranspositionGraph a) a :=
  ct_tree a (by omega)

inductive CanonicalCTRanks : List Nat → Prop where
  | allTwos {ranks : List Nat} (hne : ranks ≠ []) (hall : ∀ a : Nat, a ∈ ranks → a = 2) :
      CanonicalCTRanks ranks
  | singleLarge (a : Nat) (ha : 3 ≤ a) : CanonicalCTRanks [a]
  | consLarge (a : Nat) {ranks : List Nat} (ha : 3 ≤ a) (htail : CanonicalCTRanks ranks) :
      CanonicalCTRanks (a :: ranks)

private theorem xor_ne_left (p q r : Bool) (h : p ≠ q) : Bool.xor p r ≠ Bool.xor q r := by
  revert h; cases p <;> cases q <;> cases r <;> decide
private theorem xor_ne_right (p q r : Bool) (h : q ≠ r) : Bool.xor p q ≠ Bool.xor p r := by
  revert h; cases p <;> cases q <;> cases r <;> decide
private theorem xor_not_left (p q : Bool) : Bool.xor (!p) q = !(Bool.xor p q) := by
  cases p <;> cases q <;> decide

/-- Multiplying by an odd permutation flips the parity colour. -/
theorem ctColor_neg (a : Nat) {c g : Equiv.Perm (Fin a)} (hc : Equiv.Perm.sign c = -1) :
    CompleteTranspositionColor a (c * g) = !(CompleteTranspositionColor a g) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
  · have h2 : Equiv.Perm.sign (c * g) = -1 := by rw [map_mul, hc, hg]; decide
    simp [(ctColor_true_iff a (c * g)).mpr h2, (ctColor_false_iff a g).mpr hg]
  · have h2 : Equiv.Perm.sign (c * g) = 1 := by rw [map_mul, hc, hg]; decide
    simp [(ctColor_false_iff a (c * g)).mpr h2, (ctColor_true_iff a g).mpr hg]

/-- Every CT-product over a nonempty rank list with all ranks ≥ 2 is equitable bipartite.
    (Each edge flips one factor's parity → proper; a head-swap flips the XOR → equal classes.) -/
theorem ctProduct_equitable_aux : ∀ (ranks : List Nat), ranks ≠ [] →
    (∀ x ∈ ranks, 2 ≤ x) →
    IsEquitableBipartite (CTProductGraph ranks) (CTProductColor ranks) := by
  intro ranks
  induction ranks with
  | nil => intro h _; exact absurd rfl h
  | cons a tail ih =>
    cases tail with
    | nil =>
      intro _ hge
      exact completeTransposition_equitable a (hge a (by simp))
    | cons b rest =>
      intro _ hge
      have ha2 : 2 ≤ a := hge a (by simp)
      have htail : IsEquitableBipartite (CTProductGraph (b :: rest)) (CTProductColor (b :: rest)) :=
        ih (by simp) (fun x hx => hge x (List.mem_cons_of_mem a hx))
      refine ⟨?_, ?_⟩
      · intro u v huv
        obtain ⟨u1, u2⟩ := u
        obtain ⟨v1, v2⟩ := v
        have huv' :
            (CompleteTranspositionGraph a □ CTProductGraph (b :: rest)).Adj (u1, u2) (v1, v2) := huv
        rw [SimpleGraph.boxProd_adj] at huv'
        change Bool.xor (CompleteTranspositionColor a u1) (CTProductColor (b :: rest) u2)
             ≠ Bool.xor (CompleteTranspositionColor a v1) (CTProductColor (b :: rest) v2)
        rcases huv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h2' : u2 = v2 := h2
          rw [h2']; exact xor_ne_left _ _ _ (completeTransposition_balanced a u1 v1 h1)
        · have h1' : u1 = v1 := h2
          rw [h1']; exact xor_ne_right _ _ _ (htail.1 u2 v2 h1)
      · set i : Fin a := ⟨0, by omega⟩ with hi
        set j : Fin a := ⟨1, by omega⟩ with hj
        have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
        set c : Equiv.Perm (Fin a) := Equiv.swap i j with hcd
        have hc : Equiv.Perm.sign c = -1 := Equiv.Perm.sign_swap hij
        have hcc : c * c = 1 := Equiv.swap_mul_self i j
        apply Fintype.card_congr
        refine ⟨fun x => ⟨(c * x.1.1, x.1.2), ?_⟩, fun y => ⟨(c * y.1.1, y.1.2), ?_⟩, ?_, ?_⟩
        · have hflip : CTProductColor (a :: b :: rest) (c * x.1.1, x.1.2)
                     = !(CTProductColor (a :: b :: rest) x.1) := by
            show Bool.xor (CompleteTranspositionColor a (c * x.1.1)) (CTProductColor (b :: rest) x.1.2)
               = !(Bool.xor (CompleteTranspositionColor a x.1.1) (CTProductColor (b :: rest) x.1.2))
            rw [ctColor_neg a hc, xor_not_left]
          rw [hflip]; simp [x.2]
        · have hflip : CTProductColor (a :: b :: rest) (c * y.1.1, y.1.2)
                     = !(CTProductColor (a :: b :: rest) y.1) := by
            show Bool.xor (CompleteTranspositionColor a (c * y.1.1)) (CTProductColor (b :: rest) y.1.2)
               = !(Bool.xor (CompleteTranspositionColor a y.1.1) (CTProductColor (b :: rest) y.1.2))
            rw [ctColor_neg a hc, xor_not_left]
          rw [hflip]; simp [y.2]
        · intro x; apply Subtype.ext
          refine Prod.ext ?_ rfl
          show c * (c * x.1.1) = x.1.1
          rw [← mul_assoc, hcc, one_mul]
        · intro y; apply Subtype.ext
          refine Prod.ext ?_ rfl
          show c * (c * y.1.1) = y.1.1
          rw [← mul_assoc, hcc, one_mul]

theorem canonical_ne_nil {ranks : List Nat} (h : CanonicalCTRanks ranks) : ranks ≠ [] := by
  cases h with
  | allTwos hne _ => exact hne
  | singleLarge a ha => simp
  | consLarge a ha htail => simp

theorem canonical_all_ge2 {ranks : List Nat} (h : CanonicalCTRanks ranks) :
    ∀ x ∈ ranks, 2 ≤ x := by
  induction h with
  | allTwos hne hall => intro x hx; have := hall x hx; omega
  | singleLarge a ha => intro x hx; simp only [List.mem_singleton] at hx; omega
  | consLarge a ha htail ih =>
      intro x hx
      rcases List.mem_cons.mp hx with h' | h'
      · omega
      · exact ih x h'

/-- **(Formerly an axiom; now proved.)** Every canonical CT-product is equitable bipartite. -/
theorem ctProduct_equitable {ranks : List Nat} (hcanon : CanonicalCTRanks ranks) :
    IsEquitableBipartite (CTProductGraph ranks) (CTProductColor ranks) :=
  ctProduct_equitable_aux ranks (canonical_ne_nil hcanon) (canonical_all_ge2 hcanon)

/-- A weld distributes over `□`: `(weld Gs M) □ B ≃g` the weld of the graphs `Gs i □ B`, with each
    matching extended by the identity on `B`. (Vertex map: the reassociation `(Fin ell × W) × X ≃
    Fin ell × (W × X)`.) This lets the CT-product instances reduce to `ct_weld_iso` like the single-CT ones. -/
def weldBoxProd {W X : Type*} (ell : ℕ) (Gs : Fin ell → SimpleGraph W)
    (M : Fin ell → Fin ell → (W ≃ W)) (B : SimpleGraph X) :
    (weldGraph ell Gs M □ B) ≃g
      weldGraph ell (fun i => Gs i □ B) (fun i j => (M i j).prodCongr (Equiv.refl X)) := by
  refine ⟨Equiv.prodAssoc (Fin ell) W X, ?_⟩
  rintro ⟨⟨i, w⟩, x⟩ ⟨⟨j, w'⟩, x'⟩
  simp only [weldGraph, SimpleGraph.boxProd_adj, SimpleGraph.fromRel_adj, Equiv.prodAssoc_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, ne_eq, Prod.ext_iff]
  aesop (add safe apply SimpleGraph.Adj.symm)

/-- Box-product is functorial in the left factor: `G ≃g G' ⇒ G □ B ≃g G' □ B`. -/
def boxProdCongrRight {V V' X : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G')
    (B : SimpleGraph X) : (G □ B) ≃g (G' □ B) where
  toEquiv := e.toEquiv.prodCongr (Equiv.refl X)
  map_rel_iff' := by
    rintro ⟨v, x⟩ ⟨v', x'⟩
    simp only [SimpleGraph.boxProd_adj, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      RelIso.coe_fn_toEquiv, RelIso.map_rel_iff, EmbeddingLike.apply_eq_iff_eq]

/-- Hamilton paths transport across a graph isomorphism. -/
theorem hasHamPath_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {u v : V}
    (h : HasHamPath H (e u) (e v)) : HasHamPath G u v := by
  obtain ⟨pH, hpH⟩ := h
  have hbij : Function.Bijective (e.symm.toHom : W → V) := e.symm.bijective
  refine ⟨(pH.map e.symm.toHom).copy (by simp [RelIso.symm_apply_apply])
          (by simp [RelIso.symm_apply_apply]), fun a => ?_⟩
  rw [SimpleGraph.Walk.support_copy]
  exact (hpH.map e.symm.toHom hbij) a

/-- Hamilton-laceability transports across a graph isomorphism. -/
theorem hamLaceable_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {colH : W → Bool}
    (h : IsHamLaceable H colH) : IsHamLaceable G (fun v => colH (e v)) :=
  fun u v huv => hasHamPath_iso e (h (e u) (e v) huv)

/-- `CT_1 □ B ≃g B` — the rank-1 leaf (a single vertex times `B` is `B`). -/
def ct1BoxProd {X : Type} (B : SimpleGraph X) :
    (CompleteTranspositionGraph 1 □ B) ≃g B where
  toEquiv := Equiv.uniqueProd X (Equiv.Perm (Fin 1))
  map_rel_iff' := by
    rintro ⟨p, x⟩ ⟨p', x'⟩
    have hpp : p = p' := Subsingleton.elim p p'
    subst hpp
    simp [SimpleGraph.boxProd_adj, CompleteTranspositionGraph, SimpleGraph.fromRel_adj]

/-- `CT_a □ B` carries a Coleman welding tree of rank `a`, given `B` Hamilton-laceable with respect
    to a proper surjective colouring and of even order (induction on `a`, rank-1 base
    `CT_1 □ B ≃g B`, step `ct_weld_iso` + `weldBoxProd`). -/
theorem ctBox_tree {X : Type} [DecidableEq X] [Fintype X] (B : SimpleGraph X) (colB : X → Bool)
    (hBprop : IsProper2Coloring B colB) (hBsurj : Function.Surjective colB)
    (hB : IsHamLaceable B colB) (hBeven : Nat.card X = 1 ∨ Even (Nat.card X)) :
    ∀ a : Nat, 1 ≤ a → IsColemanTree (CompleteTranspositionGraph a □ B) a
  | 0, h => absurd h (by omega)
  | 1, _ => by
      refine IsColemanTree.base (Or.inr ⟨fun v => colB ((ct1BoxProd B) v), ?_, ?_,
        hamLaceable_iso (ct1BoxProd B) hB⟩) ?_
      · intro u v huv
        exact hBprop _ _ ((ct1BoxProd B).map_rel_iff.mpr huv)
      · intro b
        obtain ⟨x, hx⟩ := hBsurj b
        exact ⟨(ct1BoxProd B).symm x, by simp [hx]⟩
      · have hc : Nat.card ((Equiv.Perm (Fin 1)) × X) = Nat.card X := by
          rw [Nat.card_prod]
          simp [Nat.card_eq_fintype_card, Fintype.card_perm]
        rw [hc]
        exact hBeven
  | (n + 2), _ => by
      obtain ⟨M, hM, ⟨e⟩⟩ := ct_weld_iso (n + 2) (by omega)
      exact IsColemanTree.weld (by omega) (le_refl _)
        (fun _ => ctBox_tree B colB hBprop hBsurj hB hBeven (n + 1) (by omega))
        (fun i j => by rw [hM i j]; exact Equiv.ext (fun u => rfl))
        ((boxProdCongrRight e B).trans
          (weldBoxProd (n + 2) (fun _ => CompleteTranspositionGraph ((n + 2) - 1)) M B))

/-- A nonempty CT-product whose head rank is `≥ 2` has even order (the head factor `Perm (Fin hd)` has
    even card `hd!`). -/
theorem ctProductVertex_card_even {hd : Nat} {tl : List Nat} (hhd : 2 ≤ hd) :
    Even (Nat.card (CTProductVertex (hd :: tl))) := by
  have hfact : Even (Nat.card (Equiv.Perm (Fin hd))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    exact (even_iff_two_dvd).mpr (Nat.dvd_factorial (by norm_num) hhd)
  cases tl with
  | nil => exact hfact
  | cons he rest =>
      rw [show CTProductVertex (hd :: he :: rest)
            = ((Equiv.Perm (Fin hd)) × CTProductVertex (he :: rest)) from rfl, Nat.card_prod]
      exact hfact.mul_right _

theorem ctProductVertex_nonempty : ∀ (ranks : List Nat), ranks ≠ [] →
    Nonempty (CTProductVertex ranks)
  | [a], _ => ⟨(1 : Equiv.Perm (Fin a))⟩
  | (a :: b :: rest), _ => by
      obtain ⟨x⟩ := ctProductVertex_nonempty (b :: rest) (by simp)
      exact ⟨((1 : Equiv.Perm (Fin a)), x)⟩

/-- `CT_a □ (CT-product tail)` carries a Coleman welding tree of rank `a`, given the tail
    Hamilton-laceable (the tail's colouring is proper by equitability and surjective by
    equitability + nonemptiness; its order is even from the head factor's factorial). -/
theorem ctBoxProduct_tree (a : Nat) {ranks : List Nat}
    (ha : 3 ≤ a) (htail : CanonicalCTRanks ranks)
    (hHL : IsHamLaceable (CTProductGraph ranks) (CTProductColor ranks)) :
    IsColemanTree (CTProductGraph (a :: ranks)) a := by
  obtain ⟨hd, tl, rfl, hhd⟩ : ∃ hd tl, ranks = hd :: tl ∧ 2 ≤ hd := by
    cases htail with
    | allTwos hne hall =>
        obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨hd, tl, rfl, by have := hall hd (List.mem_cons_self ..); omega⟩
    | singleLarge b hb => exact ⟨b, [], rfl, by omega⟩
    | consLarge b _ hb => exact ⟨b, _, rfl, by omega⟩
  have hEq := ctProduct_equitable htail
  have hne : Nonempty (CTProductVertex (hd :: tl)) := ctProductVertex_nonempty (hd :: tl) (by simp)
  exact ctBox_tree (CTProductGraph (hd :: tl)) (CTProductColor (hd :: tl))
    hEq.1 (surjective_of_equitable_nonempty hEq hne) hHL
    (Or.inr (ctProductVertex_card_even hhd)) a (by omega)


/-! ### Theorem 7.1 for arbitrary factor orders (2026-07-05).

The paper states Theorem 7.1 for every Cartesian product of complete transposition graphs
and silently reorders factors in its proof ("write G = CT_a □ B"); the canonical-order
induction above is the mechanized core. The bridge below makes the reordering formal:
color-respecting isomorphisms for factor swaps, congruence, and insertion sort, plus
"sorted-descending rank lists are canonical", give the printed statement. -/

/-- A color-respecting isomorphism between CT-products over two rank lists. -/
def CTColorIso (l l' : List Nat) : Prop :=
  ∃ e : CTProductGraph l ≃g CTProductGraph l',
    ∀ v, CTProductColor l' (e v) = CTProductColor l v

theorem CTColorIso.refl (l : List Nat) : CTColorIso l l :=
  ⟨RelIso.refl _, fun _ => rfl⟩

theorem CTColorIso.trans {l₁ l₂ l₃ : List Nat}
    (h₁ : CTColorIso l₁ l₂) (h₂ : CTColorIso l₂ l₃) : CTColorIso l₁ l₃ := by
  obtain ⟨e₁, hc₁⟩ := h₁
  obtain ⟨e₂, hc₂⟩ := h₂
  exact ⟨e₁.trans e₂, fun v => (hc₂ (e₁ v)).trans (hc₁ v)⟩

/-- Congruence in the right factor of a box product. -/
private def boxProdCongrLeft {V X X' : Type*} (A : SimpleGraph V) {G : SimpleGraph X}
    {G' : SimpleGraph X'} (e : G ≃g G') : (A □ G) ≃g (A □ G') where
  toEquiv := (Equiv.refl V).prodCongr e.toEquiv
  map_rel_iff' := by
    rintro ⟨v, x⟩ ⟨v', x'⟩
    simp only [SimpleGraph.boxProd_adj, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
      id_eq, RelIso.coe_fn_toEquiv, RelIso.map_rel_iff, EmbeddingLike.apply_eq_iff_eq]

/-- The three-factor left commutation `A □ (B □ C) ≃g B □ (A □ C)`, by the explicit shuffle. -/
private def boxProdLeftComm {VA VB VC : Type*} (A : SimpleGraph VA) (B : SimpleGraph VB)
    (C : SimpleGraph VC) : (A □ (B □ C)) ≃g (B □ (A □ C)) where
  toEquiv :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun p => (p.2.1, (p.1, p.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩
    simp only [SimpleGraph.boxProd_adj, Equiv.coe_fn_mk, Prod.mk.injEq]
    tauto

/-- Swapping the two leading factors is a color-respecting isomorphism. -/
theorem ctColorIso_swap (a b : Nat) (t : List Nat) :
    CTColorIso (a :: b :: t) (b :: a :: t) := by
  cases t with
  | nil =>
      refine ⟨SimpleGraph.boxProdComm _ _, ?_⟩
      rintro ⟨x, y⟩
      show Bool.xor (CompleteTranspositionColor b y) (CompleteTranspositionColor a x) =
        Bool.xor (CompleteTranspositionColor a x) (CompleteTranspositionColor b y)
      exact Bool.xor_comm _ _
  | cons c t' =>
      refine ⟨boxProdLeftComm _ _ _, ?_⟩
      rintro ⟨x, y, z⟩
      show Bool.xor (CompleteTranspositionColor b y)
          (Bool.xor (CompleteTranspositionColor a x) (CTProductColor (c :: t') z)) =
        Bool.xor (CompleteTranspositionColor a x)
          (Bool.xor (CompleteTranspositionColor b y) (CTProductColor (c :: t') z))
      cases CompleteTranspositionColor a x <;> cases CompleteTranspositionColor b y <;>
        cases CTProductColor (c :: t') z <;> rfl

/-- Consing a factor onto color-isomorphic nonempty products stays color-isomorphic. -/
theorem ctColorIso_cons (a : Nat) {l l' : List Nat} (hl : l ≠ []) (hl' : l' ≠ [])
    (h : CTColorIso l l') : CTColorIso (a :: l) (a :: l') := by
  obtain ⟨e, hc⟩ := h
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨b', t', rfl⟩ := List.exists_cons_of_ne_nil hl'
  refine ⟨boxProdCongrLeft (CompleteTranspositionGraph a) e, ?_⟩
  rintro ⟨x, y⟩
  show Bool.xor (CompleteTranspositionColor a x) (CTProductColor (b' :: t') (e y)) =
    Bool.xor (CompleteTranspositionColor a x) (CTProductColor (b :: t) y)
  rw [hc y]

/-- `orderedInsert` preserves the product up to color-respecting isomorphism. -/
theorem ctColorIso_orderedInsert (a : Nat) (l : List Nat) :
    CTColorIso (a :: l) (l.orderedInsert (· ≥ ·) a) := by
  induction l with
  | nil => exact CTColorIso.refl [a]
  | cons b t ih =>
      by_cases hab : a ≥ b
      · simpa [List.orderedInsert, hab] using CTColorIso.refl (a :: b :: t)
      · have hne : (t.orderedInsert (· ≥ ·) a) ≠ [] := by
          intro h
          have hlen := congrArg List.length h
          rw [List.orderedInsert_length] at hlen
          simp at hlen
        have hstep : CTColorIso (b :: a :: t) (b :: t.orderedInsert (· ≥ ·) a) :=
          ctColorIso_cons b (List.cons_ne_nil a t) hne ih
        have hswap : CTColorIso (a :: b :: t) (b :: a :: t) := ctColorIso_swap a b t
        simpa [List.orderedInsert, hab] using hswap.trans hstep

/-- Insertion sort preserves the product up to color-respecting isomorphism. -/
theorem ctColorIso_insertionSort (l : List Nat) :
    CTColorIso l (l.insertionSort (· ≥ ·)) := by
  induction l with
  | nil => exact CTColorIso.refl []
  | cons a t ih =>
      by_cases ht : t = []
      · subst ht
        exact CTColorIso.refl [a]
      · have hsne : (t.insertionSort (· ≥ ·)) ≠ [] := by
          intro h
          apply ht
          have hlen := congrArg List.length h
          rw [List.length_insertionSort] at hlen
          exact List.length_eq_zero_iff.mp hlen
        have h1 : CTColorIso (a :: t) (a :: t.insertionSort (· ≥ ·)) :=
          ctColorIso_cons a ht hsne ih
        have h2 : CTColorIso (a :: t.insertionSort (· ≥ ·))
            ((t.insertionSort (· ≥ ·)).orderedInsert (· ≥ ·) a) :=
          ctColorIso_orderedInsert a (t.insertionSort (· ≥ ·))
        simpa [List.insertionSort_cons] using h1.trans h2

/-- A nonempty, weakly decreasing rank list with all entries `≥ 2` is canonical. -/
theorem canonical_of_pairwiseGE : ∀ {l : List Nat}, l ≠ [] → (∀ a ∈ l, 2 ≤ a) →
    l.Pairwise (· ≥ ·) → CanonicalCTRanks l
  | [], hne, _, _ => absurd rfl hne
  | [a], _, hall, _ => by
      by_cases ha : 3 ≤ a
      · exact CanonicalCTRanks.singleLarge a ha
      · have h2 : a = 2 := by
          have := hall a (List.mem_singleton_self a)
          omega
        exact CanonicalCTRanks.allTwos (by simp) (by
          intro x hx
          rw [List.mem_singleton.mp hx, h2])
  | a :: b :: t, _, hall, hpw => by
      have hpw' := List.pairwise_cons.mp hpw
      by_cases ha : 3 ≤ a
      · exact CanonicalCTRanks.consLarge a ha
          (canonical_of_pairwiseGE (List.cons_ne_nil b t)
            (fun x hx => hall x (List.mem_cons_of_mem a hx)) hpw'.2)
      · have h2 : a = 2 := by
          have := hall a (List.mem_cons_self ..)
          omega
        exact CanonicalCTRanks.allTwos (List.cons_ne_nil a (b :: t)) (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact h2
          · have hle : x ≤ a := hpw'.1 x hx'
            have hge := hall x (List.mem_cons_of_mem a hx')
            omega)

/-! ## Interchange ↔ CT-product bridge (moved from Ledger so Sec5 need not import Ledger) -/

theorem equitableBipartite_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {colG : V → Bool} {colH : W → Bool}
    (e : G ≃g H) (hcol : ∀ v : V, colH (e v) = colG v)
    (hH : IsEquitableBipartite H colH) :
    IsEquitableBipartite G colG := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    have hAdjH : H.Adj (e u) (e v) := e.map_rel_iff.mpr huv
    simpa [hcol u, hcol v] using hH.1 (e u) (e v) hAdjH
  · let colorEquiv : ∀ b : Bool, {v : V // colG v = b} ≃ {w : W // colH w = b} := fun b =>
      { toFun := fun x => ⟨e x.1, by simpa [hcol x.1] using x.2⟩
        invFun := fun y => ⟨e.symm y.1, by
          have hy : colH (e (e.symm y.1)) = b := by
            rw [RelIso.apply_symm_apply]
            exact y.2
          rw [hcol (e.symm y.1)] at hy
          exact hy⟩
        left_inv := by
          intro x
          apply Subtype.ext
          simp [RelIso.symm_apply_apply]
        right_inv := by
          intro y
          apply Subtype.ext
          simp [RelIso.apply_symm_apply] }
    calc
      Fintype.card {v : V // colG v = false}
          = Fintype.card {w : W // colH w = false} :=
            Fintype.card_congr (colorEquiv false)
      _ = Fintype.card {w : W // colH w = true} := hH.2
      _ = Fintype.card {v : V // colG v = true} :=
            (Fintype.card_congr (colorEquiv true)).symm

/-- On a connected graph, a proper 2-coloring is unique up to the global color swap. -/
theorem proper2Coloring_eq_or_flip {V : Type} {G : SimpleGraph V} (hconn : G.Connected)
    {c1 c2 : V → Bool} (h1 : IsProper2Coloring G c1) (h2 : IsProper2Coloring G c2) :
    (∀ v, c1 v = c2 v) ∨ (∀ v, c1 v = !(c2 v)) := by
  classical
  have step : ∀ u v, G.Adj u v → ((c1 u = c2 u) ↔ (c1 v = c2 v)) := by
    intro u v huv
    have e1 := h1 u v huv
    have e2 := h2 u v huv
    cases hc1u : c1 u <;> cases hc1v : c1 v <;> cases hc2u : c2 u <;> cases hc2v : c2 v <;>
      simp_all
  have key : ∀ u v : V, G.Reachable u v → ((c1 u = c2 u) ↔ (c1 v = c2 v)) := by
    intro u v hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact Iff.rfl
    | cons h p ih => exact (step _ _ h).trans ih
  obtain ⟨v0⟩ := hconn.nonempty
  by_cases h0 : c1 v0 = c2 v0
  · left
    intro v
    exact (key v0 v (hconn.preconnected v0 v)).mp h0
  · right
    intro v
    have hv : ¬(c1 v = c2 v) := fun h => h0 ((key v0 v (hconn.preconnected v0 v)).mpr h)
    cases hc2 : c2 v <;> cases hc1 : c1 v <;> simp_all


end Brualdi.Ledger
