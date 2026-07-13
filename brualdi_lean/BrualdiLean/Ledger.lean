/-
  Brualdi-MH -- Tier-2 ledger assembly (Lean 4, mathlib v4.31.0).

  This file assembles the main theorem from:
    * `weak_ct_product`: the Brualdi 2006 CT-product representation for balanced-bipartite
      interchange graphs;
    * `CORE'`: the decomposed Coleman CORE-prime theorem in `Coleman.lean`;
    * `reduction`: the remaining §§4-7 reduction, now conditional on global CORE.
-/
import BrualdiLean.Coleman
import BrualdiLean.Johnson
import BrualdiLean.Ryser
import BrualdiLean.Sec5
import BrualdiLean.Sec4
import BrualdiLean.Sec4Walk
import BrualdiLean.Sec6
import Mathlib.Tactic

set_option autoImplicit false

namespace Brualdi.Ledger

open Brualdi
open scoped BigOperators

/-! ## Tier-2 assembly layer. -/

theorem spanning2_iso_invariant {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {colG : V → Bool} {colH : W → Bool}
    (hcol : ∀ v : V, colH (e v) = colG v)
    (hH : IsSpanning2DPCOpposite H colH) :
    IsSpanning2DPCOpposite G colG := by
  intro a₁ b₁ a₂ b₂ hc₁ hc₂ ha₁a₂ ha₁b₂ hb₁a₂ hb₁b₂ ha₁b₁ ha₂b₂
  have hc₁H : colH (e a₁) ≠ colH (e b₁) := by
    rw [hcol a₁, hcol b₁]
    exact hc₁
  have hc₂H : colH (e a₂) ≠ colH (e b₂) := by
    rw [hcol a₂, hcol b₂]
    exact hc₂
  have ha₁a₂H : e a₁ ≠ e a₂ := e.injective.ne ha₁a₂
  have ha₁b₂H : e a₁ ≠ e b₂ := e.injective.ne ha₁b₂
  have hb₁a₂H : e b₁ ≠ e a₂ := e.injective.ne hb₁a₂
  have hb₁b₂H : e b₁ ≠ e b₂ := e.injective.ne hb₁b₂
  have ha₁b₁H : e a₁ ≠ e b₁ := e.injective.ne ha₁b₁
  have ha₂b₂H : e a₂ ≠ e b₂ := e.injective.ne ha₂b₂
  rcases hH (e a₁) (e b₁) (e a₂) (e b₂)
      hc₁H hc₂H ha₁a₂H ha₁b₂H hb₁a₂H hb₁b₂H ha₁b₁H ha₂b₂H with
    ⟨pH, qH, hpH, hqH, hcoverH, hdisjH⟩
  let p : G.Walk a₁ b₁ :=
    (pH.map e.symm.toHom).copy (by simp [RelIso.symm_apply_apply])
      (by simp [RelIso.symm_apply_apply])
  let q : G.Walk a₂ b₂ :=
    (qH.map e.symm.toHom).copy (by simp [RelIso.symm_apply_apply])
      (by simp [RelIso.symm_apply_apply])
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · have hpMap : (pH.map e.symm.toHom).IsPath :=
      SimpleGraph.Walk.map_isPath_of_injective e.symm.injective hpH
    simpa [p, SimpleGraph.Walk.isPath_copy] using hpMap
  · have hqMap : (qH.map e.symm.toHom).IsPath :=
      SimpleGraph.Walk.map_isPath_of_injective e.symm.injective hqH
    simpa [q, SimpleGraph.Walk.isPath_copy] using hqMap
  · intro x
    have hxH := hcoverH (e x)
    cases hxH with
    | inl hxP =>
        left
        have hxMap : x ∈ (pH.map e.symm.toHom).support := by
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨e x, hxP, by simp [RelIso.symm_apply_apply]⟩
        simpa [p, SimpleGraph.Walk.support_copy] using hxMap
    | inr hxQ =>
        right
        have hxMap : x ∈ (qH.map e.symm.toHom).support := by
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨e x, hxQ, by simp [RelIso.symm_apply_apply]⟩
        simpa [q, SimpleGraph.Walk.support_copy] using hxMap
  · intro x hx
    have hxPMap : x ∈ (pH.map e.symm.toHom).support := by
      simpa [p, SimpleGraph.Walk.support_copy] using hx.1
    have hxQMap : x ∈ (qH.map e.symm.toHom).support := by
      simpa [q, SimpleGraph.Walk.support_copy] using hx.2
    have hxPH : e x ∈ pH.support := by
      rw [SimpleGraph.Walk.support_map] at hxPMap
      rcases List.mem_map.mp hxPMap with ⟨y, hy, hyx⟩
      have hy_eq : y = e x := by
        calc
          y = e (e.symm y) := (RelIso.apply_symm_apply e y).symm
          _ = e x := congrArg (fun z : V => e z) hyx
      simpa [hy_eq] using hy
    have hxQH : e x ∈ qH.support := by
      rw [SimpleGraph.Walk.support_map] at hxQMap
      rcases List.mem_map.mp hxQMap with ⟨y, hy, hyx⟩
      have hy_eq : y = e x := by
        calc
          y = e (e.symm y) := (RelIso.apply_symm_apply e y).symm
          _ = e x := congrArg (fun z : V => e z) hyx
      simpa [hy_eq] using hy
    exact hdisjH (e x) ⟨hxPH, hxQH⟩


/-- Global CORE statement consumed by the reduction: every finite balanced-bipartite interchange
    graph is spanning-2-laceable. The vertex universe is intentionally `Type`. -/
def CORE_global : Prop :=
  ∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V) (col : V → Bool),
    IsInterchangeGraph G → IsProper2Coloring G col → IsSpanning2DPCOpposite G col

/-- CORE-global follows from the Brualdi CT-product representation and Coleman's decomposed
    CORE-prime theorem. Below 4 vertices the statement is vacuous (a 2-demand needs 4 distinct
    endpoints), which is what discharges the `2 ≤ card` guard of `weak_ct_product`. -/
theorem core_global : CORE_global := by
  intro V _ _ G col hIG hBB
  by_cases hcard : 4 ≤ Fintype.card V
  · rcases weak_ct_product G col hIG hBB (by omega) with ⟨ranks, hcanon, e, hcol⟩
    exact spanning2_iso_invariant e hcol (CORE' hcanon)
  · intro a₁ b₁ a₂ b₂ _ _ h12 h1b2 hb1a2 hb1b2 hab1 hab2
    exfalso
    apply hcard
    have hinj : Function.Injective (![a₁, b₁, a₂, b₂]) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hle := Fintype.card_le_of_injective _ hinj
    simpa using hle


/-- **Theorem 7.1, as stated (arbitrary factor order)**: every Cartesian product of complete
    transposition graphs `CT_a`, `a ≥ 2`, is paired 2-disjoint-path-coverable for opposite
    demands. The canonical-order induction (`canonicalCTProduct_paired_two`) is the core;
    the factor reordering is the sort isomorphism. -/
theorem ctProduct_paired_two_of_ranks (ranks : List Nat) (hne : ranks ≠ [])
    (hall : ∀ a ∈ ranks, 2 ≤ a) :
    IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2 := by
  classical
  have hiso := ctColorIso_insertionSort ranks
  have hsne : (ranks.insertionSort (· ≥ ·)) ≠ [] := by
    intro h
    apply hne
    have hlen := congrArg List.length h
    rw [List.length_insertionSort] at hlen
    exact List.length_eq_zero_iff.mp hlen
  have hsall : ∀ a ∈ (ranks.insertionSort (· ≥ ·)), 2 ≤ a := fun a ha =>
    hall a ((List.mem_insertionSort _).mp ha)
  have hcanon : CanonicalCTRanks (ranks.insertionSort (· ≥ ·)) :=
    canonical_of_pairwiseGE hsne hsall (List.pairwise_insertionSort _ ranks)
  obtain ⟨e, hc⟩ := hiso
  have h2 := canonicalCTProduct_paired_two hcanon
  exact paired_two_of_spanning2 (spanning2_iso_invariant e hc
    (spanning2_of_paired_two_opposite h2))

/-- CORE Lemma (ledger C0-C5): a balanced-bipartite interchange graph is spanning-2-laceable. -/
theorem CORE {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col) :
    IsSpanning2DPCOpposite G col :=
  core_global V G col hIG hBB

/-! ## Reduction, decomposed into the trichotomy (finer trust surface; replaces the opaque `reduction`).
    The §§3-6 reduction is `induction on |V|` + a four-way case split (bipartite / decomposable /
    indecomposable-non-base / base). We expose each branch explicitly. The BIPARTITE branch is *proved*
    from CORE; the others are (for now) named axioms matching the manuscript + the C7 capstone routing,
    to be discharged. -/

/-- Coleman/Prop-11c bridge: a balanced-bipartite spanning-2-laceable INTERCHANGE graph on ≥ 2
    vertices is Hamilton-laceable. The interchange hypothesis supplies equitability
    (`interchange_bipartite_equitable`) and — in the degenerate 2-vertex case, where the `prop11c`
    demand guard bars the paired-cover route — the edge (`Ryser.interchange_has_edge`) that makes
    the graph `K₂`, laceable directly. (The former unguarded `∀ G` version was FALSE at `E₂`;
    2026-07-04 unsoundness certificate #2.) -/
theorem paired2dpc_to_laceable {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) (hS : IsSpanning2DPCOpposite G col) :
    IsHamLaceable G col := by
  have hEq : IsEquitableBipartite G col := interchange_bipartite_equitable hIG hBB hcard
  by_cases h4 : 4 ≤ Fintype.card V
  · exact paired_two_opposite_to_hamLaceable hEq (paired_two_of_spanning2 hS) h4
  · have heven := equitable_even_card hEq
    have hcard2 : Fintype.card V = 2 := by
      rcases heven with ⟨t, ht⟩
      omega
    exact laceable_card_two col hcard2 (Brualdi.Ryser.interchange_has_edge G hIG hcard)

/-! Trichotomy branch — **BIPARTITE** (proved from the global CORE theorem; see `reduction_bipartite`). -/
/-- A nontrivial interchange graph has an edge (Ryser's 2-switch existence). Supplies the
    surjective-colouring witness the faithful `IsMH` requires — makes the connectivity dependency
    EXPLICIT (it was previously hidden behind the edgeless `IsMH` vacuity). **Now PROVED** (Tier-2
    discharged): `Brualdi.Ryser.interchange_has_edge` reduces it, across the interchange isomorphism,
    to the switchable-block lemma `Brualdi.Ryser.switchable_block`, both depending only on Lean
    foundations. -/
theorem interchange_has_edge {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hcard : 2 ≤ Fintype.card V) : ∃ u v, G.Adj u v :=
  Brualdi.Ryser.interchange_has_edge G hIG hcard

theorem reduction_bipartite {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col) (hCORE : CORE_global) :
    IsMH G := by
  by_cases hcard : 2 ≤ Fintype.card V
  · obtain ⟨u, v, huv⟩ := interchange_has_edge G hIG hcard
    have hne : col u ≠ col v := hBB u v huv
    refine Or.inr ⟨col, hBB, ?_,
      paired2dpc_to_laceable G col hIG hBB hcard (hCORE V G col hIG hBB)⟩
    intro b
    by_cases hbu : b = col u
    · exact ⟨u, hbu.symm⟩
    · refine ⟨v, ?_⟩
      rcases Bool.eq_false_or_eq_true b with rfl | rfl <;>
        rcases Bool.eq_false_or_eq_true (col u) with hcu | hcu <;>
        rcases Bool.eq_false_or_eq_true (col v) with hcv | hcv <;>
        simp_all
  · have hle : Fintype.card V ≤ 1 := by omega
    have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hle
    exact Or.inl (fun u v huv => absurd (Subsingleton.elim u v) huv)

/-- Maximal Hamiltonicity is invariant under graph isomorphism (transport Hamilton paths along `e`).
    Reusable infrastructure for the base/Johnson branch (`G ≃g Johnson ⇒ MH`). -/
theorem isMH_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hH : IsMH H) : IsMH G := by
  have transport : ∀ {u v : V}, HasHamPath H (e u) (e v) → HasHamPath G u v := by
    intro u v h
    obtain ⟨pH, hpH⟩ := h
    have hbij : Function.Bijective (e.symm.toHom : W → V) := e.symm.bijective
    refine ⟨(pH.map e.symm.toHom).copy (by simp [RelIso.symm_apply_apply])
            (by simp [RelIso.symm_apply_apply]), fun a => ?_⟩
    rw [SimpleGraph.Walk.support_copy]
    exact (hpH.map e.symm.toHom hbij) a
  rcases hH with hHC | ⟨colH, hBB_H, hsurj_H, hlace⟩
  · exact Or.inl fun u v huv => transport (hHC (e u) (e v) (e.injective.ne huv))
  · refine Or.inr ⟨fun v => colH (e v),
      fun u v huv => hBB_H (e u) (e v) (e.map_rel_iff.mpr huv), ?_,
      fun u v hc => transport (hlace (e u) (e v) hc)⟩
    intro b
    obtain ⟨w, hw⟩ := hsurj_H b
    obtain ⟨a, ha⟩ := e.surjective w
    exact ⟨a, by show colH (e a) = b; rw [ha]; exact hw⟩

/-! ### Reduction glue: the trichotomy + strong induction on `Fintype.card V`.
    The remaining (non-bipartite) trichotomy predicates are opaque for now (their definitions from the
    matrix structure are the deferred modeling); the BRANCH claims and the trichotomy are axioms, but the
    INDUCTION that glues them — the structural heart of §§3-6 — is machine-checked below. -/

private theorem isBaseClass_iso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    IsBaseClass H → IsBaseClass G := by
  classical
  rintro ⟨hIH, hbase⟩
  refine ⟨isInterchangeGraph_of_iso e hIH, ?_⟩
  rcases hbase with ⟨n, k, hk, hkn, ⟨eJ⟩⟩ | hsmall
  · exact Or.inl ⟨n, k, hk, hkn, ⟨e.trans eJ⟩⟩
  · right
    calc
      Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
      _ ≤ 6 := hsmall

/-- Trichotomy — now a **classical tautology** (PROVED), since `IsIndecomposableNonBase` is the residual
    "else" case: every interchange graph is bipartite, a base class, decomposable, or indecomposable-
    non-base. -/
theorem trichotomy {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) :
    (∃ col, IsProper2Coloring G col) ∨ IsBaseClass G ∨ IsDecomposable G ∨ IsIndecomposableNonBase G := by
  classical
  by_cases hb : ∃ col, IsProper2Coloring G col
  · exact Or.inl hb
  · by_cases hba : IsBaseClass G
    · exact Or.inr (Or.inl hba)
    · by_cases hd : IsDecomposable G
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inr (Or.inr ⟨hb, hba, hd⟩))

/-- Alspach (cited): a Johnson graph J(n,k), n>k≥1, is maximally Hamiltonian (Hamilton-connected). -/
axiom johnson_isMH (n k : ℕ) (hk : 0 < k) (hkn : k < n) : IsMH (Brualdi.Johnson.Jgraph n k)

/-- **CITED — verbatim source found 2026-07-06** [Brualdi 2006, *Combinatorial Matrix Classes*,
    §9.13 pp. 491–493, after Brualdi–Hartfiel–Hwang, Linear Multilin. Alg. 19 (1986) 203–219]:
    Theorem 9.13.11 ("Ω_{R,S} ≠ ∅ iff A(R,S) ≠ ∅. In fact, Ω_{R,S} is the convex hull of the
    matrices in A(R,S)", where Ω_{R,S} is the (R,S)-assignment polytope (9.57): 0 ≤ x_ij ≤ 1 with
    margins R,S) together with the in-text dimension statement and its footnote 26 on p. 492–493:
    "Assuming that A(R,S) has no invariant 1's, the dimension of the polytope Ω_{R,S} equals
    (m−1)(n−1), and hence Ω_{R,S} has at least (m−1)(n−1)+1 extreme points." — "So
    |A(R,S)| ≥ (m−1)(n−1)+1 if R and S are positive integral vectors such that the class A(R,S)
    is nonempty and has no invariant 1's." Hypothesis alignment (all conservative): `hact` gives
    positive vectors (active is stronger), `hne` gives nonemptiness (hence equal sums), and `hIF`
    (EVERY cell varies — full invariant-freeness) implies "no invariant 1's". History: this was
    the second half of the formerly-bundled A7, split 2026-07-06 (the first half is exactly axiom
    A6 `active_prime_cell_varies`); the former "standard theory, no displayed source" flag was
    RETIRED the same day when the printed statement was located in the book. Sanity: the `(2,1,1)`/`(2,2,1)` cores have `|𝔄| = 5 = (2)(2)+1`
    (tight); a `3×4` active class gives `≥ (2)(3)+1 = 7 > 6` (correctly excluded by the §6 census).
    The `hact`/`hne` guards carry the sources' standing assumptions: `IsActive` does not imply
    feasibility, and the empty active class r=(2,2,2), s=(1,1,1) falsified the unguarded bundled form
    (kernel-checked `False`, 2026-07-04 unsoundness certificate #4); `hIF` is stated for the same
    class, so an empty class satisfies it vacuously and `hne` remains load-bearing. -/
axiom invariantFree_card_ge {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hIF : ∀ i j, CellVaries r s i j)
    (hne : Nonempty (MarginClass r s)) :
    (m - 1) * (n - 1) + 1 ≤ Fintype.card (MarginClass r s)

/-- The formerly-bundled A7, now a **theorem**: primeness converts to invariant-freeness by axiom
    A6 (`active_prime_cell_varies`, Brualdi–Manber 1983 Thm 9 / Brualdi 2006 Thm 6.3.5), and the
    dimension count is axiom `invariantFree_card_ge`. Signature unchanged, so every downstream use
    (`small_interchange_MH`, the §6 census) is untouched; the axiom trace swaps
    `prime_class_card_ge` for `invariantFree_card_ge`. -/
theorem prime_class_card_ge {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hprime : ¬ IsDecomposable (flipGraph r s))
    (hne : Nonempty (MarginClass r s)) :
    (m - 1) * (n - 1) + 1 ≤ Fintype.card (MarginClass r s) :=
  invariantFree_card_ge r s hact (active_prime_cell_varies r s hact hprime hne) hne

private instance instDecidableHasMargins {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (M : ZeroOneMat m n) : Decidable (HasMargins r s M) := by
  unfold HasMargins
  infer_instance

private instance instDecidableInterchange {m n : ℕ} (M N : ZeroOneMat m n) :
    Decidable (Interchange M N) := by
  unfold Interchange
  infer_instance

private instance instDecidableFlipGraphAdj {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    DecidableRel (flipGraph r s).Adj := by
  unfold flipGraph
  infer_instance

private theorem flipGraph_isInterchange_local {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    IsInterchangeGraph (flipGraph r s) :=
  ⟨m, n, r, s, Equiv.refl _, fun _ _ => Iff.rfl⟩

private theorem isDecomposable_congr {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    IsDecomposable G → IsDecomposable H := by
  rintro ⟨W₁, W₂, dW₁, dW₂, fW₁, fW₂, A, B, hnt₁, hnt₂, hIA, hIB, ⟨eprod⟩⟩
  exact ⟨W₁, W₂, dW₁, dW₂, fW₁, fW₂, A, B, hnt₁, hnt₂, hIA, hIB,
    ⟨e.symm.trans eprod⟩⟩

private theorem sum_row_eq_sum_col {m n : ℕ} (M : ZeroOneMat m n) :
    (∑ i : Fin m, rowSum M i) = ∑ j : Fin n, colSum M j := by
  change (∑ i : Fin m, ∑ j : Fin n, (if M i j then 1 else 0 : ℕ)) =
    ∑ j : Fin n, ∑ i : Fin m, (if M i j then 1 else 0 : ℕ)
  exact Finset.sum_comm

private theorem margin_sum_eq {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) :
    (∑ i : Fin m, r i) = ∑ j : Fin n, s j := by
  calc
    (∑ i : Fin m, r i) = ∑ i : Fin m, rowSum M.val i := by
      exact Finset.sum_congr rfl (fun i _ => (M.property.1 i).symm)
    _ = ∑ j : Fin n, colSum M.val j := sum_row_eq_sum_col M.val
    _ = ∑ j : Fin n, s j := by
      exact Finset.sum_congr rfl (fun j _ => M.property.2 j)

private theorem subsingleton_marginClass_of_active_left_le_one {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (hact : IsActive r s) (hm : m ≤ 1) :
    Subsingleton (MarginClass r s) := by
  refine ⟨fun M N => ?_⟩
  apply Subtype.ext
  funext i j
  have hs := hact.2 j
  omega

private theorem subsingleton_marginClass_of_active_right_le_one {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} (hact : IsActive r s) (hn : n ≤ 1) :
    Subsingleton (MarginClass r s) := by
  refine ⟨fun M N => ?_⟩
  apply Subtype.ext
  funext i j
  have hr := hact.1 i
  omega

private def permuteMat {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (M : ZeroOneMat m n) : ZeroOneMat m n :=
  fun i j => M (σ i) (τ j)

private theorem permute_hasMargins {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (M : MarginClass r s) :
    HasMargins (fun i => r (σ i)) (fun j => s (τ j)) (permuteMat σ τ M.val) := by
  constructor
  · intro i
    calc
      rowSum (permuteMat σ τ M.val) i
          = ∑ j : Fin n, (if M.val (σ i) j then 1 else 0 : ℕ) := by
              exact Fintype.sum_equiv τ
                (fun j => (if M.val (σ i) (τ j) then 1 else 0 : ℕ))
                (fun j => (if M.val (σ i) j then 1 else 0 : ℕ))
                (fun _ => rfl)
      _ = r (σ i) := M.property.1 (σ i)
  · intro j
    calc
      colSum (permuteMat σ τ M.val) j
          = ∑ i : Fin m, (if M.val i (τ j) then 1 else 0 : ℕ) := by
              exact Fintype.sum_equiv σ
                (fun i => (if M.val (σ i) (τ j) then 1 else 0 : ℕ))
                (fun i => (if M.val i (τ j) then 1 else 0 : ℕ))
                (fun _ => rfl)
      _ = s (τ j) := M.property.2 (τ j)

private def permuteEquiv {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    MarginClass r s ≃ MarginClass (fun i => r (σ i)) (fun j => s (τ j)) where
  toFun M := ⟨permuteMat σ τ M.val, permute_hasMargins σ τ M⟩
  invFun M :=
    ⟨permuteMat σ.symm τ.symm M.val, by
      convert permute_hasMargins σ.symm τ.symm M using 2
      · simp
      · simp⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    simp [permuteMat]
  right_inv M := by
    apply Subtype.ext
    funext i j
    simp [permuteMat]

private theorem interchange_permute_iff {m n : ℕ} {M N : ZeroOneMat m n}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Interchange (permuteMat σ τ M) (permuteMat σ τ N) ↔ Interchange M N := by
  constructor
  · rintro ⟨i₁, i₂, j₁, j₂, hi, hj, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨σ i₁, σ i₂, τ j₁, τ j₂, ?_, ?_, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
      hN₁₁, hN₂₂, hN₁₂, hN₂₁, ?_⟩
    · exact σ.injective.ne hi
    · exact τ.injective.ne hj
    · intro a b hnot
      have hnot' :
          ¬ (((σ.symm a = i₁) ∨ (σ.symm a = i₂)) ∧
              ((τ.symm b = j₁) ∨ (τ.symm b = j₂))) := by
        intro hblock
        apply hnot
        constructor
        · rcases hblock.1 with h | h
          · left
            exact ((Equiv.apply_eq_iff_eq_symm_apply σ).2 h.symm).symm
          · right
            exact ((Equiv.apply_eq_iff_eq_symm_apply σ).2 h.symm).symm
        · rcases hblock.2 with h | h
          · left
            exact ((Equiv.apply_eq_iff_eq_symm_apply τ).2 h.symm).symm
          · right
            exact ((Equiv.apply_eq_iff_eq_symm_apply τ).2 h.symm).symm
      have hout' := hout (σ.symm a) (τ.symm b) hnot'
      simpa [permuteMat] using hout'
  · rintro ⟨i₁, i₂, j₁, j₂, hi, hj, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨σ.symm i₁, σ.symm i₂, τ.symm j₁, τ.symm j₂, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact σ.symm.injective.ne hi
    · exact τ.symm.injective.ne hj
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · simpa [permuteMat]
    · intro a b hnot
      have hnot' :
          ¬ (((σ a = i₁) ∨ (σ a = i₂)) ∧ ((τ b = j₁) ∨ (τ b = j₂))) := by
        intro hblock
        apply hnot
        constructor
        · rcases hblock.1 with h | h
          · left
            simpa using congrArg σ.symm h
          · right
            simpa using congrArg σ.symm h
        · rcases hblock.2 with h | h
          · left
            simpa using congrArg τ.symm h
          · right
            simpa using congrArg τ.symm h
      exact hout (σ a) (τ b) hnot'

private theorem permuteEquiv_interchange_iff {m n : ℕ} {r : Fin m → ℕ}
    {s : Fin n → ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (M N : MarginClass r s) :
    Interchange ((permuteEquiv r s σ τ M).val) ((permuteEquiv r s σ τ N).val) ↔
      Interchange M.val N.val := by
  exact interchange_permute_iff σ τ

private theorem flipGraph_perm_iso {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Nonempty (flipGraph r s ≃g flipGraph (fun i => r (σ i)) (fun j => s (τ j))) := by
  let e := permuteEquiv r s σ τ
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [flipGraph, flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using (permuteEquiv_interchange_iff σ τ M N).mp hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using (permuteEquiv_interchange_iff σ τ N M).mp hrel
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using (permuteEquiv_interchange_iff σ τ M N).mpr hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using (permuteEquiv_interchange_iff σ τ N M).mpr hrel

private theorem active_two_row_johnson_iso {n : ℕ} (r : Fin 2 → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hne : Nonempty (MarginClass r s)) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nonempty (flipGraph r s ≃g Brualdi.Johnson.Jgraph n k) := by
  classical
  rcases hne with ⟨M⟩
  have hs_eq : s = fun _ : Fin n => 1 := by
    funext j
    have hj := hact.2 j
    omega
  have hsum := margin_sum_eq M
  rw [Fin.sum_univ_two] at hsum
  have hsum_s : (∑ j : Fin n, s j) = n := by
    simp [hs_eq]
  have hr_sum : r (0 : Fin 2) + r (1 : Fin 2) = n := by
    omega
  have hr_eq : r = (![r (0 : Fin 2), n - r (0 : Fin 2)] : Fin 2 → ℕ) := by
    funext i
    fin_cases i
    · simp
    · simp
      omega
  have hk : 0 < r (0 : Fin 2) := (hact.1 (0 : Fin 2)).1
  have hkn : r (0 : Fin 2) < n := (hact.1 (0 : Fin 2)).2
  refine ⟨r (0 : Fin 2), hk, hkn, ?_⟩
  rw [hr_eq, hs_eq]
  exact flipGraph_two_row_iso_johnson (r (0 : Fin 2)) hk hkn

theorem active_two_row_baseClass {n : ℕ} (r : Fin 2 → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) :
    IsBaseClass (flipGraph r s) := by
  classical
  refine ⟨flipGraph_isInterchange_local r s, ?_⟩
  by_cases hne : Nonempty (MarginClass r s)
  · rcases active_two_row_johnson_iso r s hact hne with ⟨k, hk, hkn, hiso⟩
    exact Or.inl ⟨n, k, hk, hkn, hiso⟩
  · right
    by_contra hcard
    have hpos : 0 < Fintype.card (MarginClass r s) := by omega
    exact hne (Fintype.card_pos_iff.mp hpos)

theorem active_two_col_baseClass {m : ℕ} (r : Fin m → ℕ) (s : Fin 2 → ℕ)
    (hact : IsActive r s) :
    IsBaseClass (flipGraph r s) := by
  refine ⟨flipGraph_isInterchange_local r s, ?_⟩
  obtain ⟨eT⟩ := flipGraph_transpose r s
  exact (isBaseClass_iso eT (active_two_row_baseClass s r ⟨hact.2, hact.1⟩)).2

private theorem active_two_row_isMH {n : ℕ} (r : Fin 2 → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hne : Nonempty (MarginClass r s)) :
    IsMH (flipGraph r s) := by
  rcases active_two_row_johnson_iso r s hact hne with ⟨k, hk, hkn, ⟨eJ⟩⟩
  exact isMH_iso eJ (johnson_isMH n k hk hkn)

private theorem active_two_col_isMH {m : ℕ} (r : Fin m → ℕ) (s : Fin 2 → ℕ)
    (hact : IsActive r s) (hne : Nonempty (MarginClass r s)) :
    IsMH (flipGraph r s) := by
  obtain ⟨eT⟩ := flipGraph_transpose r s
  have hactT : IsActive s r := ⟨hact.2, hact.1⟩
  have hneT : Nonempty (MarginClass s r) := by
    rcases hne with ⟨M⟩
    exact ⟨eT M⟩
  exact isMH_iso eT (active_two_row_isMH s r hactT hneT)

private def core111Color
    (M : MarginClass (![1, 1, 1] : Fin 3 → ℕ) (![1, 1, 1] : Fin 3 → ℕ)) : Bool :=
  (M.val 0 0 && M.val 1 1) || (M.val 0 1 && M.val 1 2) || (M.val 0 2 && M.val 1 0)

private def core222Color
    (M : MarginClass (![2, 2, 2] : Fin 3 → ℕ) (![2, 2, 2] : Fin 3 → ℕ)) : Bool :=
  ((!M.val 0 0) && (!M.val 1 1)) ||
    ((!M.val 0 1) && (!M.val 1 2)) || ((!M.val 0 2) && (!M.val 1 0))

private theorem flipGraph_111_bipartite :
    ∃ col, IsProper2Coloring
      (flipGraph (![1, 1, 1] : Fin 3 → ℕ) (![1, 1, 1] : Fin 3 → ℕ)) col := by
  refine ⟨core111Color, ?_⟩
  unfold IsProper2Coloring
  decide

private theorem flipGraph_222_bipartite :
    ∃ col, IsProper2Coloring
      (flipGraph (![2, 2, 2] : Fin 3 → ℕ) (![2, 2, 2] : Fin 3 → ℕ)) col := by
  refine ⟨core222Color, ?_⟩
  unfold IsProper2Coloring
  decide

private theorem core111_isMH :
    IsMH (flipGraph (![1, 1, 1] : Fin 3 → ℕ) (![1, 1, 1] : Fin 3 → ℕ)) := by
  obtain ⟨col, hcol⟩ := flipGraph_111_bipartite
  exact reduction_bipartite _ col (flipGraph_isInterchange_local _ _) hcol core_global

private theorem core222_isMH :
    IsMH (flipGraph (![2, 2, 2] : Fin 3 → ℕ) (![2, 2, 2] : Fin 3 → ℕ)) := by
  obtain ⟨col, hcol⟩ := flipGraph_222_bipartite
  exact reduction_bipartite _ col (flipGraph_isInterchange_local _ _) hcol core_global

private theorem isMH_of_perm_to_211 {r s : Fin 3 → ℕ}
    (σ τ : Equiv.Perm (Fin 3))
    (hr : (fun i => r (σ i)) = (![2, 1, 1] : Fin 3 → ℕ))
    (hs : (fun j => s (τ j)) = (![2, 1, 1] : Fin 3 → ℕ)) :
    IsMH (flipGraph r s) := by
  obtain ⟨eperm⟩ := flipGraph_perm_iso r s σ τ
  refine isMH_iso eperm ?_
  rw [hr, hs]
  obtain ⟨ecore⟩ := flipGraph_211_iso_coreA
  exact Or.inl (isHamConnected_iso ecore coreA_isHamConnected)

private theorem isMH_of_perm_to_221 {r s : Fin 3 → ℕ}
    (σ τ : Equiv.Perm (Fin 3))
    (hr : (fun i => r (σ i)) = (![2, 2, 1] : Fin 3 → ℕ))
    (hs : (fun j => s (τ j)) = (![2, 2, 1] : Fin 3 → ℕ)) :
    IsMH (flipGraph r s) := by
  obtain ⟨eperm⟩ := flipGraph_perm_iso r s σ τ
  refine isMH_iso eperm ?_
  rw [hr, hs]
  obtain ⟨ecore⟩ := flipGraph_221_iso_coreB
  exact Or.inl (isHamConnected_iso ecore coreB_isHamConnected)

private def bitCount3 (b : Fin 3 → Bool) : ℕ :=
  (if b 0 then 1 else 0) + (if b 1 then 1 else 0) + (if b 2 then 1 else 0)

private def marginBits3 (b : Fin 3 → Bool) : Fin 3 → ℕ :=
  fun i => if b i then 2 else 1

private def permOne3 (b : Fin 3 → Bool) : Equiv.Perm (Fin 3) :=
  if b 0 then Equiv.refl _
  else if b 1 then Equiv.swap (0 : Fin 3) (1 : Fin 3)
  else Equiv.swap (0 : Fin 3) (2 : Fin 3)

private def permTwo3 (b : Fin 3 → Bool) : Equiv.Perm (Fin 3) :=
  if b 2 then
    if b 1 then Equiv.swap (0 : Fin 3) (2 : Fin 3)
    else Equiv.swap (1 : Fin 3) (2 : Fin 3)
  else Equiv.refl _

private theorem bitCount3_le_three (b : Fin 3 → Bool) : bitCount3 b ≤ 3 := by
  unfold bitCount3
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    simp [h0, h1, h2]

private theorem marginBits3_sum (b : Fin 3 → Bool) :
    marginBits3 b 0 + marginBits3 b 1 + marginBits3 b 2 = 3 + bitCount3 b := by
  unfold marginBits3 bitCount3
  by_cases h0 : b 0 <;> by_cases h1 : b 1 <;> by_cases h2 : b 2 <;>
    simp [h0, h1, h2]

private theorem marginBits3_eq_111 (b : Fin 3 → Bool) (h : bitCount3 b = 0) :
    marginBits3 b = (![1, 1, 1] : Fin 3 → ℕ) := by
  revert b
  decide

private theorem marginBits3_eq_222 (b : Fin 3 → Bool) (h : bitCount3 b = 3) :
    marginBits3 b = (![2, 2, 2] : Fin 3 → ℕ) := by
  revert b
  decide

private theorem marginBits3_perm_one (b : Fin 3 → Bool) (h : bitCount3 b = 1) :
    (fun i => marginBits3 b (permOne3 b i)) = (![2, 1, 1] : Fin 3 → ℕ) := by
  revert b
  decide

private theorem marginBits3_perm_two (b : Fin 3 → Bool) (h : bitCount3 b = 2) :
    (fun i => marginBits3 b (permTwo3 b i)) = (![2, 2, 1] : Fin 3 → ℕ) := by
  revert b
  decide

private theorem active_three_margin_eq (r : Fin 3 → ℕ)
    (h : ∀ i, 0 < r i ∧ r i < 3) :
    r = marginBits3 (fun i => r i = 2) := by
  funext i
  have hi := h i
  by_cases h2 : r i = 2
  · simp [marginBits3, h2]
  · have h1 : r i = 1 := by omega
    simp [marginBits3, h1]

private theorem active_three_by_three_isMH (r s : Fin 3 → ℕ)
    (hact : IsActive r s) (hne : Nonempty (MarginClass r s)) :
    IsMH (flipGraph r s) := by
  classical
  let rb : Fin 3 → Bool := fun i => r i = 2
  let sb : Fin 3 → Bool := fun i => s i = 2
  have hr_eq : r = marginBits3 rb := active_three_margin_eq r hact.1
  have hs_eq : s = marginBits3 sb := active_three_margin_eq s hact.2
  rcases hne with ⟨M⟩
  have hsum := margin_sum_eq M
  have hsum3 :
      r (0 : Fin 3) + r (1 : Fin 3) + r (2 : Fin 3) =
        s (0 : Fin 3) + s (1 : Fin 3) + s (2 : Fin 3) := by
    simpa [Fin.sum_univ_three, Nat.add_assoc] using hsum
  rw [hr_eq, hs_eq, marginBits3_sum rb, marginBits3_sum sb] at hsum3
  have hcnt : bitCount3 rb = bitCount3 sb := by omega
  have hle : bitCount3 rb ≤ 3 := bitCount3_le_three rb
  interval_cases hcntRb : bitCount3 rb
  · have hr111 : r = (![1, 1, 1] : Fin 3 → ℕ) := by
      rw [hr_eq]
      exact marginBits3_eq_111 rb hcntRb
    have hs111 : s = (![1, 1, 1] : Fin 3 → ℕ) := by
      rw [hs_eq]
      exact marginBits3_eq_111 sb (by omega)
    rw [hr111, hs111]
    exact core111_isMH
  · exact isMH_of_perm_to_211 (permOne3 rb) (permOne3 sb)
      (by rw [hr_eq]; exact marginBits3_perm_one rb hcntRb)
      (by rw [hs_eq]; exact marginBits3_perm_one sb (by omega))
  · exact isMH_of_perm_to_221 (permTwo3 rb) (permTwo3 sb)
      (by rw [hr_eq]; exact marginBits3_perm_two rb hcntRb)
      (by rw [hs_eq]; exact marginBits3_perm_two sb (by omega))
  · have hr222 : r = (![2, 2, 2] : Fin 3 → ℕ) := by
      rw [hr_eq]
      exact marginBits3_eq_222 rb hcntRb
    have hs222 : s = (![2, 2, 2] : Fin 3 → ℕ) := by
      rw [hs_eq]
      exact marginBits3_eq_222 sb (by omega)
    rw [hr222, hs222]
    exact core222_isMH

/-- Base case (manuscript §6, the small cases checked directly): an **indecomposable** interchange graph
    on ≤6 vertices is MH. The `¬ IsDecomposable` hypothesis is the key structural simplification (mirroring
    the manuscript: the reduction splits off the invariant-position Cartesian product FIRST, via §4, so the
    ≤6 base case only ever faces prime / invariant-free classes). By Brualdi–Manber this means the active
    normal form is invariant-free, so `|A| ≥ (m-1)(n-1)+1`, forcing `m=n=3` (the two cores) once ≤2 active
    lines (Johnson) are excluded — the finite census. Threaded in by the reordered `reduction_glue`
    (decomposable handled before base). -/
theorem small_interchange_MH {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hsmall : Fintype.card V ≤ 6)
    (hindec : ¬ IsDecomposable G) : IsMH G := by
  classical
  by_cases hbip : ∃ col, IsProper2Coloring G col
  · obtain ⟨col, hcol⟩ := hbip
    exact reduction_bipartite G col hIG hcol core_global
  obtain ⟨m, n, r, s, φ, hadj⟩ := hIG
  let eG : G ≃g flipGraph r s := by
    refine { toEquiv := φ, map_rel_iff' := ?_ }
    intro a b
    exact (hadj a b).symm
  by_cases hle1 : Fintype.card V ≤ 1
  · haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hle1
    exact Or.inl (fun u v huv => absurd (Subsingleton.elim u v) huv)
  have hcard_ge2V : 2 ≤ Fintype.card V := by omega
  have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v0 : V := Classical.choice hVne
  have hne : Nonempty (MarginClass r s) := ⟨φ v0⟩
  obtain ⟨m', n', r', s', hact, ⟨eact⟩⟩ := exists_active_iso r s hne
  let eGA : G ≃g flipGraph r' s' := eG.trans eact
  refine isMH_iso eGA ?_
  have hneA : Nonempty (MarginClass r' s') := ⟨eact (φ v0)⟩
  have hcard_eq : Fintype.card V = Fintype.card (MarginClass r' s') :=
    Fintype.card_congr eGA.toEquiv
  have hcard_le6 : Fintype.card (MarginClass r' s') ≤ 6 := by
    rw [← hcard_eq]
    exact hsmall
  have hcard_ge2 : 2 ≤ Fintype.card (MarginClass r' s') := by
    rw [← hcard_eq]
    exact hcard_ge2V
  have hindecA : ¬ IsDecomposable (flipGraph r' s') := by
    intro hd
    exact hindec (isDecomposable_congr eGA.symm hd)
  have hmge2 : 2 ≤ m' := by
    by_contra hm
    have hmle : m' ≤ 1 := by omega
    have hsub : Subsingleton (MarginClass r' s') :=
      subsingleton_marginClass_of_active_left_le_one hact hmle
    have hcardle : Fintype.card (MarginClass r' s') ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hnge2 : 2 ≤ n' := by
    by_contra hn
    have hnle : n' ≤ 1 := by omega
    have hsub : Subsingleton (MarginClass r' s') :=
      subsingleton_marginClass_of_active_right_le_one hact hnle
    have hcardle : Fintype.card (MarginClass r' s') ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  by_cases hm2 : m' = 2
  · subst m'
    exact active_two_row_isMH r' s' hact hneA
  by_cases hn2 : n' = 2
  · subst n'
    exact active_two_col_isMH r' s' hact hneA
  have hmge3 : 3 ≤ m' := by omega
  have hnge3 : 3 ≤ n' := by omega
  have hprime := prime_class_card_ge r' s' hact hindecA hneA
  have hprodle : (m' - 1) * (n' - 1) ≤ 5 := by
    omega
  have hm1 : 2 ≤ m' - 1 := by omega
  have hn1 : 2 ≤ n' - 1 := by omega
  have hn_mul : 2 * (n' - 1) ≤ (m' - 1) * (n' - 1) := by
    exact Nat.mul_le_mul_right (n' - 1) hm1
  have hm_mul : 2 * (m' - 1) ≤ (n' - 1) * (m' - 1) := by
    exact Nat.mul_le_mul_right (m' - 1) hn1
  have hnsub : n' - 1 ≤ 2 := by nlinarith
  have hmsub : m' - 1 ≤ 2 := by nlinarith [Nat.mul_comm (n' - 1) (m' - 1)]
  have hm3 : m' = 3 := by omega
  have hn3 : n' = 3 := by omega
  subst m'
  subst n'
  exact active_three_by_three_isMH r' s' hact hneA

/-- Base branch [§6] — **PROVED** from Alspach (Johnson) + small-case axiom + `isMH_iso`. Carries the
    `¬ IsDecomposable` hypothesis (from the reordered glue) into the ≤6 small case. -/
theorem reduction_base {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hbase : IsBaseClass G) (hindec : ¬ IsDecomposable G) : IsMH G := by
  rcases hbase.2 with ⟨n, k, hk, hkn, ⟨e⟩⟩ | hsmall
  · exact isMH_iso e (johnson_isMH n k hk hkn)
  · exact small_interchange_MH G hIG hsmall hindec

/-- Each factor of a §4 decomposition is `FactorReady` (the input `boxProd_hamConnected` needs):
    a non-bipartite factor is Hamilton-connected (from its MH-ness, since bipartite is the only other
    `IsMH` disjunct); a bipartite factor carries the full paired-cover witness — proper colour
    (surjective, since `interchange_has_edge` gives an edge on ≥2 vertices), Hamilton-laceable and
    spanning-2-laceable (both from CORE via `paired2dpc_to_laceable`). -/
theorem factorReady_of {W : Type} [DecidableEq W] [Fintype W] {A : SimpleGraph W}
    (hIA : IsInterchangeGraph A) (hnt : 2 ≤ Fintype.card W) (hMHA : IsMH A) (hCORE : CORE_global) :
    FactorReady A := by
  by_cases hbip : ∃ col, IsProper2Coloring A col
  · obtain ⟨col, hcol⟩ := hbip
    have hspan : IsSpanning2DPCOpposite A col := hCORE W A col hIA hcol
    have hlace : IsHamLaceable A col :=
      paired2dpc_to_laceable A col hIA hcol hnt hspan
    have hsurj : Function.Surjective col := by
      obtain ⟨u, v, huv⟩ := interchange_has_edge A hIA hnt
      have hne : col u ≠ col v := hcol u v huv
      intro b
      by_cases hb : b = col u
      · exact ⟨u, hb.symm⟩
      · exact ⟨v, by cases hbu : col u <;> cases hbv : col v <;> cases hbb : b <;> simp_all⟩
    exact Or.inr ⟨col, hcol, hsurj, hlace, hspan⟩
  · rcases hMHA with hconn | ⟨col, hproper, _, _⟩
    · exact Or.inl ⟨hbip, hconn⟩
    · exact absurd ⟨col, hproper⟩ hbip

/-- Decomposable branch [§4 product-lifting] — now **PROVED** from `boxProd_hamConnected` (all of §4's
    Cartesian-product Hamilton-connectivity, foundations-only) + the factor-readiness derivation. A
    bipartite `G` uses the CORE branch directly; a non-bipartite `G ≃g A □ B` has non-bipartite product,
    so both factors are MH (by the IH) and `FactorReady`, and `boxProd_hamConnected` gives it
    Hamilton-connected, transported back to `G`. -/
theorem reduction_decompose {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hdec : IsDecomposable G) (hCORE : CORE_global)
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
            Fintype.card W < Fintype.card V → IsInterchangeGraph H → IsMH H) : IsMH G := by
  by_cases hbipG : ∃ col, IsProper2Coloring G col
  · obtain ⟨col, hcol⟩ := hbipG
    exact reduction_bipartite G col hIG hcol hCORE
  · obtain ⟨W₁, W₂, dW₁, dW₂, fW₁, fW₂, A, B, hnt1, hnt2, hIA, hIB, ⟨e⟩⟩ := hdec
    haveI := dW₁; haveI := dW₂; haveI := fW₁; haveI := fW₂; haveI := hnt1; haveI := hnt2
    obtain ⟨hcardA, hcardB⟩ := boxProd_card_lt e
    have hFA : FactorReady A :=
      factorReady_of hIA Fintype.one_lt_card (IH A hcardA hIA) hCORE
    have hFB : FactorReady B :=
      factorReady_of hIB Fintype.one_lt_card (IH B hcardB hIB) hCORE
    have hnbAB : ¬ ∃ col, IsProper2Coloring (A □ B) col := by
      rintro ⟨col, hcol⟩
      exact hbipG ⟨fun v => col (e v),
        fun u v huv => hcol (e u) (e v) (e.map_rel_iff.mpr huv)⟩
    -- §4 as printed (Sec4Walk); the absorber route `boxProd_hamConnected` is the alternate
    exact isMH_iso e (Or.inl (boxProd_hamConnected_paper hFA hFB hnbAB))

/-- `G` has an active representative in the manuscript §5 pivot regime: at least three active rows and
    at least three active columns. -/
def HasWideActiveCore {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (m n : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ),
    3 ≤ m ∧ 3 ≤ n ∧ IsActive r s ∧ Nonempty (G ≃g Brualdi.flipGraph r s)

theorem wideActiveCore_of_not_base {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hcard : 2 ≤ Fintype.card V) (hnb : ¬ IsBaseClass G) :
    HasWideActiveCore G := by
  classical
  obtain ⟨m, n, r, s, φ, hadj⟩ := hIG
  let eG : G ≃g flipGraph r s := by
    refine { toEquiv := φ, map_rel_iff' := ?_ }
    intro a b
    exact (hadj a b).symm
  have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v0 : V := Classical.choice hVne
  have hne : Nonempty (MarginClass r s) := ⟨φ v0⟩
  obtain ⟨m', n', r', s', hact, ⟨eact⟩⟩ := exists_active_iso r s hne
  let eGA : G ≃g flipGraph r' s' := eG.trans eact
  have hcard_eq : Fintype.card V = Fintype.card (MarginClass r' s') :=
    Fintype.card_congr eGA.toEquiv
  have hcard_ge2 : 2 ≤ Fintype.card (MarginClass r' s') := by
    rw [← hcard_eq]
    exact hcard
  have hmge2 : 2 ≤ m' := by
    by_contra hm
    have hmle : m' ≤ 1 := by omega
    have hsub : Subsingleton (MarginClass r' s') :=
      subsingleton_marginClass_of_active_left_le_one hact hmle
    have hcardle : Fintype.card (MarginClass r' s') ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hnge2 : 2 ≤ n' := by
    by_contra hn
    have hnle : n' ≤ 1 := by omega
    have hsub : Subsingleton (MarginClass r' s') :=
      subsingleton_marginClass_of_active_right_le_one hact hnle
    have hcardle : Fintype.card (MarginClass r' s') ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  by_cases hmle2 : m' ≤ 2
  · have hm2 : m' = 2 := by omega
    subst m'
    have hbaseA : IsBaseClass (flipGraph r' s') := active_two_row_baseClass r' s' hact
    exact (hnb (isBaseClass_iso eGA hbaseA)).elim
  by_cases hnle2 : n' ≤ 2
  · have hn2 : n' = 2 := by omega
    subst n'
    have hbaseA : IsBaseClass (flipGraph r' s') := active_two_col_baseClass r' s' hact
    exact (hnb (isBaseClass_iso eGA hbaseA)).elim
  exact ⟨m', n', r', s', by omega, by omega, hact, ⟨eGA⟩⟩

/-- Indecomposable-non-base branch [§5 pivot construction]: MH, given MH for all strictly smaller
    interchange graphs (its fibres). The `hwide` hypothesis records the §5 active-core regime
    (at least three active rows and columns); in `reduction_glue` it is derived from `¬ IsBaseClass G`
    using the mechanized "≤2 active lines ⇒ Johnson/base" bridge, not assumed independently.
    **Now PROVED** (Tier-2 §5 discharged): transported across the wide-active-core isomorphism to the
    concrete `flip_hamConnected_of_row_buffer` — the mechanized §5 pivot construction (buffer line 5.11,
    non-bipartite quotient 5.12, interface stepping 5.6/5.7 with the two-sided avoid 5.8/5.9, and the
    Block-4 single-pass threading 5.13–5.15; paper numbers per the 2026-07-04 renumbering), with the
    column case by the concrete transpose. -/
theorem reduction_pivot {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hind : IsIndecomposableNonBase G)
    (hwide : HasWideActiveCore G) (hCORE : CORE_global)
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
            Fintype.card W < Fintype.card V → IsInterchangeGraph H → IsMH H) : IsMH G := by
  classical
  obtain ⟨m, n, r, s, hm, hn, hact, ⟨e⟩⟩ := hwide
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hnb : ¬ ∃ col : MarginClass r s → Bool,
      IsProper2Coloring (flipGraph r s) col := by
    rintro ⟨col, hcol⟩
    refine hind.1 ⟨fun v => col (e v), ?_⟩
    intro u v huv
    exact hcol _ _ (e.map_rel_iff.mpr huv)
  have hprime : ¬ IsDecomposable (flipGraph r s) := by
    intro hdec
    exact hind.2.2 (isDecomposable_congr e.symm hdec)
  have hcard : Fintype.card (MarginClass r s) = Fintype.card V :=
    (Fintype.card_congr e.toEquiv).symm
  have IH' : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card (MarginClass r s) →
        IsInterchangeGraph H → IsMH H := by
    intro W _ _ H hlt hIG'
    rw [hcard] at hlt
    exact IH H hlt hIG'
  have hconn : IsHamConnected (flipGraph r s) :=
    flip_hamConnected_of_row_buffer r s hact hm hn hprime hnb IH'
  exact isMH_iso e (Or.inl hconn)

/-- **Reduction glue — PROVED.** Every interchange graph is MH, by strong induction on the number of
    vertices, dispatching the trichotomy. This replaces the single opaque `reduction` axiom by the four
    explicit trichotomy branches (bipartite proved; base/decompose/pivot axioms) + the trichotomy, with
    the inductive composition itself machine-checked. -/
theorem reduction_glue (hCORE : CORE_global) :
    ∀ (n : ℕ) {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → IsInterchangeGraph G → IsMH G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G hcard hIG
    have IH' : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
        Fintype.card W < Fintype.card V → IsInterchangeGraph H → IsMH H := by
      intro W _ _ H hlt hIGH
      exact IH (Fintype.card W) (hcard ▸ hlt) H rfl hIGH
    -- Reordered dispatch (matching the manuscript): split off the Cartesian product (§4) BEFORE the
    -- ≤6 base, so `small_interchange_MH` only ever faces INDECOMPOSABLE (invariant-free) ≤6 classes.
    by_cases hbip : ∃ col, IsProper2Coloring G col
    · obtain ⟨col, hcol⟩ := hbip
      exact reduction_bipartite G col hIG hcol hCORE
    · by_cases hdec : IsDecomposable G
      · exact reduction_decompose G hIG hdec hCORE IH'
      · by_cases hbase : IsBaseClass G
        · exact reduction_base G hIG hbase hdec
        · have hcard_ge2 : 2 ≤ Fintype.card V := by
            have hnotSmall : ¬ Fintype.card V ≤ 6 := by
              intro hsmall
              exact hbase ⟨hIG, Or.inr hsmall⟩
            omega
          have hwide := wideActiveCore_of_not_base G hIG hcard_ge2 hbase
          exact reduction_pivot G hIG ⟨hbip, hbase, hdec⟩ hwide hCORE IH'

/-- §§3-6 reduction — now **PROVED** from the trichotomy + the machine-checked induction glue (no longer
    a single opaque axiom): conditional on the global CORE theorem, every finite interchange graph is MH.
    The trust surface is now the trichotomy + the three non-bipartite branch axioms, with the bipartite
    branch and the inductive composition machine-checked. -/
theorem reduction {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (hIG : IsInterchangeGraph G) (hCORE : CORE_global) : IsMH G :=
  reduction_glue hCORE (Fintype.card V) G rfl hIG

/-! ## Part IV -- the Main Theorem (ledger T1), for the actual interchange graphs. -/

/-- Every `flipGraph` is, tautologically, an interchange graph (witness: identity equiv). -/
theorem flipGraph_isInterchange {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    IsInterchangeGraph (flipGraph r s) :=
  ⟨m, n, r, s, Equiv.refl _, fun _ _ => Iff.rfl⟩

/-- **Main Theorem (Brualdi's conjecture, strengthened).** Every interchange graph `G(R,S)` is maximally
    Hamiltonian. The reduction is now applied to the machine-checked global CORE bridge, so the axiom
    surface exposes the Coleman decomposition instead of a single opaque CORE axiom. -/
theorem brualdi_MH {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    IsMH (flipGraph r s) := by
  classical
  exact reduction (flipGraph r s) (flipGraph_isInterchange r s) core_global

/-- **The paper-facing corollary** (Theorem 1.1 as displayed in the manuscript): under the paper's
    standing realizability hypothesis `𝔄(R,S) ≠ ∅`, the interchange graph is maximally Hamiltonian.
    The Lean main theorem is deliberately stronger (no realizability hypothesis — the empty class is
    vacuously covered); this corollary isolates the exact paper statement. Trust-eval 2026-07-06 #13. -/
theorem brualdi_MH_paper {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (_hne : Nonempty (MarginClass r s)) : IsMH (flipGraph r s) :=
  brualdi_MH r s

#check @brualdi_MH
#check @CORE
#print axioms brualdi_MH

end Brualdi.Ledger
