/-
  Brualdi-MH -- Coleman decomposition layer (Lean 4, mathlib v4.31.0).

  This file owns the CITED-AXIOM layer and the decomposed Coleman CORE-prime proof. The
  definitions live in ColemanDefs.lean (split 2026-07-06); the from-scratch proof files
  DPC.lean/DPC2.lean are imported BELOW the definitions and ABOVE this file, so the former
  axioms A2 (`prop11c`) and A3 (`hypercube_ctProduct_paired_two_ge2`) are now DERIVED here
  from `prop11c_proved` and `hypercube_paired_two_proved` (decoupled adversarial audit:
  SAFE-TO-FLIP, results/trust_evaluation4_response_2026-07-06.md).
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

import BrualdiLean.Thm15

set_option autoImplicit false

namespace Brualdi.Ledger
open Brualdi

variable {V : Type*} [DecidableEq V]

/-- **PROVED (A2 FLIPPED 2026-07-06)** — formerly the CITED axiom [Coleman et al. 2025,
    Prop 1.1(c)]; now DERIVED from the from-scratch, foundations-only `prop11c_proved`
    (DPC.lean, Tier 1 of the discharge program). Statement identity with the former axiom was
    verified by a decoupled adversarial audit before the flip (SAFE-TO-FLIP). The original
    citation record and guard history follow. — equitable down-closure of paired DPCs.
    The `hcard : 2 * k ≤ card V` guard makes the level-`k` hypothesis NON-VACUOUS (with equitability
    it says exactly that `k`-subsets of each part exist, the source's implicit standing assumption —
    their proof extends an `ell`-demand upward to a `k`-demand, impossible without room). Without the
    guard the axiom was FALSE: on `E₂` (two isolated vertices, equitable) the `k = 2` hypothesis is
    vacuous while the `l = 1` conclusion asserts Hamilton-laceability of a disconnected graph
    (kernel-checked `False`, 2026-07-04 unsoundness certificate #2). -/
theorem prop11c {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool) {k l : Nat}
    (hEq : IsEquitableBipartite G col)
    (hDPC : IsPairedKDPCForOpposite G col k)
    (hl : 1 ≤ l) (hle : l ≤ k)
    (hcard : 2 * k ≤ Fintype.card V) :
    IsPairedKDPCForOpposite G col l :=
  prop11c_proved G col hEq hDPC hl hle hcard

theorem paired_two_opposite_to_hamLaceable [Fintype V] {G : SimpleGraph V} {col : V → Bool}
    (hEq : IsEquitableBipartite G col)
    (h2 : IsPairedKDPCForOpposite G col 2)
    (hcard : 4 ≤ Fintype.card V) :
    IsHamLaceable G col := by
  have h1 : IsPairedKDPCForOpposite G col 1 :=
    prop11c G col hEq h2 (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) (by omega)
  exact paired_one_opposite_iff_hamLaceable.mp h1

/-- **DISCHARGED 2026-07-07** (was axiom A1, [Coleman et al. 2025, Thm 1.5]): now a THEOREM,
    proved from foundations by the rank induction in `Thm15.lean` — base ranks 2 and 3 from
    the paper's parts (a)/(b), rank 4 through the part-(c) engine (`small_prop16_c`, which
    needs no piece-order floor), and ranks ≥ 5 through the machine-checked Proposition 1.6
    (`coleman_prop16`). The original verbatim statement (re-audited 2026-07-04 from the DAM
    PDF): "Let n ≥ 2, and let G be a bipartite transposition-like graph of rank n with
    partite sets V₁ and V₂. Assume that during the welding process to form G, every rank 1
    transposition-like graph that G is built up from is either a single vertex or has an
    even number of vertices. Then for every choice of (n−1)-subsets S ⊆ V₁ and T ⊆ V₂,
    G admits an (n−1)-PDPC." -/
theorem coleman_thm15 {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool) (n : Nat)
    (hn : 2 ≤ n)
    (hT : IsColemanTree G n)
    (hBB : IsProper2Coloring G col) :
    IsPairedKDPCForOpposite G col (n - 1) :=
  coleman_thm15_proved n hn G col hT hBB

/-- The `prop11c` demand guard for `CT_a`, `a ≥ 3`: `2(a-1) ≤ a·(a-1) ≤ a!`. -/
private theorem two_mul_pred_le_card_perm {a : Nat} (ha : 3 ≤ a) :
    2 * (a - 1) ≤ Fintype.card (Equiv.Perm (Fin a)) := by
  rw [Fintype.card_perm, Fintype.card_fin]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb : 2 ≤ b := by omega
  have h1 : 2 * (b + 1 - 1) ≤ (b + 1) * b :=
    (by omega : 2 * (b + 1 - 1) = 2 * b) ▸ Nat.mul_le_mul_right b (by omega)
  have h2 : b ≤ b.factorial := Nat.self_le_factorial b
  calc 2 * (b + 1 - 1) ≤ (b + 1) * b := h1
    _ ≤ (b + 1) * b.factorial := Nat.mul_le_mul_left _ h2
    _ = (b + 1).factorial := (Nat.factorial_succ b).symm

/-- **PROVED (A3 FLIPPED 2026-07-06)** — formerly the CITED axiom [Jo–Park–Chwa 2013,
    Lemma 1]; now DERIVED from the from-scratch, foundations-only `hypercube_paired_two_proved`
    (DPC2.lean, Tier 2 of the discharge program; adapter: `2 ≤ length ⟹ ≠ []`). Statement
    identity verified by a decoupled adversarial audit before the flip (SAFE-TO-FLIP). The
    original citation record follows.  `CT₂ = K₂` is Hamilton-laceable directly (its two permutations are swap-adjacent). -/
private theorem ct2_hamLaceable :
    IsHamLaceable (CompleteTranspositionGraph 2) (CompleteTranspositionColor 2) := by
  apply laceable_card_two
  · rw [Fintype.card_perm, Fintype.card_fin]
    rfl
  · refine ⟨1, Equiv.swap 0 1, ?_⟩
    show (SimpleGraph.fromRel _).Adj _ _
    rw [SimpleGraph.fromRel_adj]
    refine ⟨by decide, Or.inl ?_⟩
    simp only [inv_one, one_mul]
    exact ⟨0, 1, by decide, rfl⟩

theorem completeTransposition_paired_two (a : Nat) (ha : 3 ≤ a) :
    IsPairedKDPCForOpposite (CompleteTranspositionGraph a) (CompleteTranspositionColor a) 2 := by
  have hEq := completeTransposition_equitable a (by omega)
  have hBig : IsPairedKDPCForOpposite (CompleteTranspositionGraph a) (CompleteTranspositionColor a) (a - 1) :=
    coleman_thm15 (CompleteTranspositionGraph a) (CompleteTranspositionColor a) a (by omega)
      (completeTransposition_tree a ha) hEq.1
  exact prop11c (CompleteTranspositionGraph a) (CompleteTranspositionColor a) hEq hBig
    (by decide : 1 ≤ 2) (by omega) (two_mul_pred_le_card_perm ha)

theorem hypercube_ctProduct_paired_two_ge2 (ranks : List Nat)
    (hlen : 2 ≤ ranks.length) (hall : ∀ a : Nat, a ∈ ranks → a = 2) :
    IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2 :=
  hypercube_paired_two_proved ranks (fun h => by simp [h] at hlen) hall

/-- The former axiom statement, now a **theorem** (narrowed 2026-07-06, external trust
    evaluation round 2): the source (Jo–Park–Chwa Lemma 1) is stated for hypercubes of
    dimension `m ≥ 2`, so the axiom above now carries exactly that range, and the
    one-factor case `[2]` (the graph `K₂`) is *proved* vacuous here — a paired 2-demand
    requires four distinct vertices, and `K₂` has two. Downstream uses are unchanged. -/
theorem hypercube_ctProduct_paired_two (ranks : List Nat)
    (hne : ranks ≠ []) (hall : ∀ a : Nat, a ∈ ranks → a = 2) :
    IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2 := by
  match ranks, hne with
  | [a], _ =>
      have ha : a = 2 := hall a (List.mem_singleton_self a)
      subst ha
      intro s t hd
      exfalso
      have hcard : Fintype.card (CTProductVertex [2]) = 2 := by
        show Fintype.card (Equiv.Perm (Fin 2)) = 2
        rw [Fintype.card_perm, Fintype.card_fin]
        rfl
      set f : Fin 4 → CTProductVertex [2] := ![s 0, s 1, t 0, t 1] with hf
      have hinj : Function.Injective f := by
        intro a b hab
        fin_cases a <;> fin_cases b <;>
          first
            | rfl
            | (exfalso
               simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one] at hab
               first
                 | exact absurd (hd.2.1 hab) (by decide)
                 | exact absurd (hd.2.2.1 hab) (by decide)
                 | exact hd.2.2.2 _ _ hab
                 | exact hd.2.2.2 _ _ hab.symm)
      have hle := Fintype.card_le_of_injective f hinj
      rw [hcard] at hle
      simp at hle
  | a :: b :: tl, _ =>
      exact hypercube_ctProduct_paired_two_ge2 _ (by simp) hall

/-- Every canonical CT-product other than the bare `[2]` (= `K₂`) has at least 4 vertices. -/
private theorem canonical_card_ge_four_or_eq_two {ranks : List Nat} (hcanon : CanonicalCTRanks ranks)
    (h4 : ¬ 4 ≤ Fintype.card (CTProductVertex ranks)) : ranks = [2] := by
  cases hcanon with
  | allTwos hne hall =>
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hhd : hd = 2 := hall hd (List.mem_cons_self ..)
      subst hhd
      cases tl with
      | nil => rfl
      | cons he rest =>
          exfalso
          apply h4
          have he2 : he = 2 := hall he (by simp)
          have e : CTProductVertex (2 :: he :: rest)
              ≃ (Equiv.Perm (Fin 2) × CTProductVertex (he :: rest)) := Equiv.refl _
          rw [Fintype.card_congr e, Fintype.card_prod]
          have heven : Even (Nat.card (CTProductVertex (he :: rest))) :=
            ctProductVertex_card_even (by omega)
          rw [Nat.card_eq_fintype_card] at heven
          have hpos : 0 < Fintype.card (CTProductVertex (he :: rest)) :=
            Fintype.card_pos_iff.mpr (ctProductVertex_nonempty _ (by simp))
          have hcp : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
            rw [Fintype.card_perm, Fintype.card_fin]
            rfl
          rcases heven with ⟨t, ht⟩
          rw [hcp]
          omega
  | singleLarge b hb =>
      exfalso
      apply h4
      have e : CTProductVertex [b] ≃ Equiv.Perm (Fin b) := Equiv.refl _
      rw [Fintype.card_congr e]
      have := two_mul_pred_le_card_perm hb
      omega
  | consLarge b hb htail' =>
      exfalso
      apply h4
      obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil (canonical_ne_nil htail')
      have e : CTProductVertex (b :: hd :: tl)
          ≃ (Equiv.Perm (Fin b) × CTProductVertex (hd :: tl)) := Equiv.refl _
      rw [Fintype.card_congr e, Fintype.card_prod]
      have h1 := two_mul_pred_le_card_perm hb
      have h2 : 0 < Fintype.card (CTProductVertex (hd :: tl)) :=
        Fintype.card_pos_iff.mpr (ctProductVertex_nonempty _ (by simp))
      have h3 : Fintype.card (Equiv.Perm (Fin b)) ≤
          Fintype.card (Equiv.Perm (Fin b)) * Fintype.card (CTProductVertex (hd :: tl)) :=
        Nat.le_mul_of_pos_right _ h2
      omega

/-- A canonical CT-product with a paired 2-DPC is Hamilton-laceable: via `prop11c` when the demand
    guard `4 ≤ card` holds, and directly for the sole small canonical product `[2]` (= `K₂`). -/
private theorem canonical_paired_two_hamLaceable {ranks : List Nat} (hcanon : CanonicalCTRanks ranks)
    (h2 : IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2) :
    IsHamLaceable (CTProductGraph ranks) (CTProductColor ranks) := by
  by_cases h4 : 4 ≤ Fintype.card (CTProductVertex ranks)
  · exact paired_two_opposite_to_hamLaceable (ctProduct_equitable hcanon) h2 h4
  · have hr2 : ranks = [2] := canonical_card_ge_four_or_eq_two hcanon h4
    subst hr2
    exact ct2_hamLaceable

theorem ctProduct_consLarge_paired_two (a : Nat) {ranks : List Nat}
    (ha : 3 ≤ a) (htail : CanonicalCTRanks ranks)
    (hTail2 : IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2) :
    IsPairedKDPCForOpposite (CTProductGraph (a :: ranks)) (CTProductColor (a :: ranks)) 2 := by
  have hHLTail : IsHamLaceable (CTProductGraph ranks) (CTProductColor ranks) :=
    canonical_paired_two_hamLaceable htail hTail2
  have hCanonHead : CanonicalCTRanks (a :: ranks) :=
    CanonicalCTRanks.consLarge a ha htail
  have hEqHead := ctProduct_equitable hCanonHead
  have hBig : IsPairedKDPCForOpposite (CTProductGraph (a :: ranks)) (CTProductColor (a :: ranks)) (a - 1) :=
    coleman_thm15 (CTProductGraph (a :: ranks)) (CTProductColor (a :: ranks)) a (by omega)
      (ctBoxProduct_tree a ha htail hHLTail) hEqHead.1
  have hguard : 2 * (a - 1) ≤ Fintype.card (CTProductVertex (a :: ranks)) := by
    obtain ⟨hd, tl, hranks⟩ := List.exists_cons_of_ne_nil (canonical_ne_nil htail)
    subst hranks
    have e : CTProductVertex (a :: hd :: tl)
        ≃ (Equiv.Perm (Fin a) × CTProductVertex (hd :: tl)) := Equiv.refl _
    rw [Fintype.card_congr e, Fintype.card_prod]
    have h1 := two_mul_pred_le_card_perm ha
    have h2 : 0 < Fintype.card (CTProductVertex (hd :: tl)) :=
      Fintype.card_pos_iff.mpr (ctProductVertex_nonempty _ (by simp))
    have h3 : Fintype.card (Equiv.Perm (Fin a)) ≤
        Fintype.card (Equiv.Perm (Fin a)) * Fintype.card (CTProductVertex (hd :: tl)) :=
      Nat.le_mul_of_pos_right _ h2
    omega
  exact prop11c (CTProductGraph (a :: ranks)) (CTProductColor (a :: ranks)) hEqHead hBig
    (by decide : 1 ≤ 2) (by omega) hguard

theorem canonicalCTProduct_paired_two :
    ∀ {ranks : List Nat}, CanonicalCTRanks ranks →
      IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2
  | _, CanonicalCTRanks.allTwos hne hall => hypercube_ctProduct_paired_two _ hne hall
  | _, CanonicalCTRanks.singleLarge a ha => by
      change IsPairedKDPCForOpposite (CompleteTranspositionGraph a) (CompleteTranspositionColor a) 2
      exact completeTransposition_paired_two a ha
  | _, CanonicalCTRanks.consLarge a ha htail => by
      exact ctProduct_consLarge_paired_two a ha htail (canonicalCTProduct_paired_two htail)

theorem CORE' {ranks : List Nat} (hcanon : CanonicalCTRanks ranks) :
    IsSpanning2DPCOpposite (CTProductGraph ranks) (CTProductColor ranks) :=
  spanning2_of_paired_two_opposite (canonicalCTProduct_paired_two hcanon)

/-- CITED — Ryser 1957 ("Combinatorial properties of matrices of zeros and ones", Canad. J. Math.
    9:371-377, Theorem 3.1, read verbatim from the original 2026-07-06; also stated verbatim in
    Brualdi–Manber 1983 p.158): any two matrices in a nonempty class A(R,S) are joined by a finite
    sequence of interchanges, so G(R,S) is connected. AUDITED 2026-07-03. (Relocated here from
    Sec5.lean 2026-07-06 so the derived `weak_ct_product` below can transport connectivity.) -/
axiom flipGraph_connected {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hne : Nonempty (MarginClass r s)) : (Brualdi.flipGraph r s).Connected

/-- A nonempty interchange graph is connected (A8 transported through the defining isomorphism). -/
theorem isInterchangeGraph_connected {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} (hIG : IsInterchangeGraph G) (hne : Nonempty V) :
    G.Connected := by
  obtain ⟨m, n, r, s, φ, hadj⟩ := hIG
  have hMC : Nonempty (MarginClass r s) := ⟨φ (Classical.choice hne)⟩
  have hiso : G ≃g Brualdi.flipGraph r s := ⟨φ, fun {a b} => (hadj a b).symm⟩
  exact (SimpleGraph.Iso.connected_iff hiso).mpr (flipGraph_connected r s hMC)

-- (`proper2Coloring_eq_or_flip` was relocated to ColemanDefs.lean on 2026-07-07 for the
-- A1 discharge; statement unchanged.)

/-- Left multiplication by a fixed transposition is a **color-flipping automorphism** of `CT_a`. -/
private theorem ct_flip (a : Nat) (ha : 2 ≤ a) :
    ∃ φ : CompleteTranspositionGraph a ≃g CompleteTranspositionGraph a,
      ∀ σ, CompleteTranspositionColor a (φ σ) = !(CompleteTranspositionColor a σ) := by
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin a, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simp [Fin.mk.injEq] at h⟩
  refine ⟨⟨Equiv.mulLeft (Equiv.swap i0 i1), @fun σ σ' => ?_⟩, ?_⟩
  · show (CompleteTranspositionGraph a).Adj
        (Equiv.swap i0 i1 * σ) (Equiv.swap i0 i1 * σ') ↔ _
    unfold CompleteTranspositionGraph
    rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    have hL : ∀ x y : Equiv.Perm (Fin a),
        (Equiv.swap i0 i1 * x)⁻¹ * (Equiv.swap i0 i1 * y) = x⁻¹ * y := by
      intro x y
      rw [mul_inv_rev]
      simp [mul_assoc]
    rw [hL, hL]
    constructor
    · rintro ⟨hne, h⟩
      exact ⟨fun he => hne (by rw [he]), h⟩
    · rintro ⟨hne, h⟩
      exact ⟨fun he => hne (mul_left_cancel he), h⟩
  · intro σ
    show CompleteTranspositionColor a (Equiv.swap i0 i1 * σ) = _
    unfold CompleteTranspositionColor
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-- A CT-product with a nontrivial factor has a **parity-flipping automorphism**: flip the first
    factor by `ct_flip`, leave the rest alone. -/
private theorem ctProduct_flip : ∀ (ranks : List Nat), ranks ≠ [] → (∀ b ∈ ranks, 2 ≤ b) →
    ∃ φ : CTProductGraph ranks ≃g CTProductGraph ranks,
      ∀ x, CTProductColor ranks (φ x) = !(CTProductColor ranks x)
  | [], h, _ => absurd rfl h
  | [a], _, hall => ct_flip a (hall a (List.mem_singleton_self a))
  | a :: b :: tl, _, hall => by
    obtain ⟨φ₀, hφ₀⟩ := ct_flip a (hall a (List.mem_cons_self ..))
    refine ⟨⟨Equiv.prodCongr φ₀.toEquiv (Equiv.refl _), @fun x y => ?_⟩, ?_⟩
    · show (CompleteTranspositionGraph a □ CTProductGraph (b :: tl)).Adj
          (φ₀ x.1, x.2) (φ₀ y.1, y.2) ↔
        (CompleteTranspositionGraph a □ CTProductGraph (b :: tl)).Adj x y
      rw [SimpleGraph.boxProd_adj, SimpleGraph.boxProd_adj]
      constructor
      · rintro (⟨hadj, heq⟩ | ⟨hadj, heq⟩)
        · exact Or.inl ⟨φ₀.map_rel_iff.mp hadj, heq⟩
        · exact Or.inr ⟨hadj, φ₀.toEquiv.injective heq⟩
      · rintro (⟨hadj, heq⟩ | ⟨hadj, heq⟩)
        · exact Or.inl ⟨φ₀.map_rel_iff.mpr hadj, heq⟩
        · exact Or.inr ⟨hadj, by rw [heq]⟩
    · intro x
      show Bool.xor (CompleteTranspositionColor a (φ₀ x.1)) (CTProductColor (b :: tl) x.2) =
        !(Bool.xor (CompleteTranspositionColor a x.1) (CTProductColor (b :: tl) x.2))
      rw [hφ₀ x.1]
      cases CompleteTranspositionColor a x.1 <;> cases CTProductColor (b :: tl) x.2 <;> rfl

/-- X2/X3/R3 [CITE: Brualdi 2006, Theorem 6.3.4 and section 6.3] — **RAW FORM** (A4 narrowed in
    two stages 2026-07-06, external evaluation round 4): every bipartite interchange graph on at
    least two vertices is isomorphic to SOME nonempty Cartesian product of complete-transposition
    graphs with factors of order ≥ 2 — the source's content and nothing else. NOT assumed here:
    (stage 1) the color-matching clause — derived in `weak_ct_product` from connectivity (A8),
    uniqueness of proper 2-colorings up to the global swap, and the parity-flipping automorphism;
    (stage 2) the canonical rank ordering — derived in `weak_ct_product_uncolored` by the
    machine-checked sort isomorphism. The `hcard : 2 ≤ card V` guard as before: it excludes the
    degenerate classes the book's product representation handles as the EMPTY product (a single
    vertex); without it the axiom was FALSE at any one-vertex class (kernel-checked `False`,
    2026-07-04 unsoundness certificate #1). -/
axiom weak_ct_product_raw {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ ranks : List Nat, ranks ≠ [] ∧ (∀ a ∈ ranks, 2 ≤ a) ∧
      Nonempty (G ≃g CTProductGraph ranks)

/-- The canonical-form classification — the former uncolored axiom — is now a **THEOREM**
    (A4 stage 2, 2026-07-06): the raw factor list is normalized by the machine-checked sort
    isomorphism (`ctColorIso_insertionSort` + `canonical_of_pairwiseGE`), so the canonical-rank
    packaging is Lean's, not the source's. -/
theorem weak_ct_product_uncolored {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ ranks : List Nat, CanonicalCTRanks ranks ∧ Nonempty (G ≃g CTProductGraph ranks) := by
  classical
  obtain ⟨ranks, hne, hall, ⟨e⟩⟩ := weak_ct_product_raw G col hIG hBB hcard
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
  obtain ⟨e', -⟩ := ctColorIso_insertionSort ranks
  exact ⟨ranks.insertionSort (· ≥ ·), hcanon, ⟨e.trans e'⟩⟩

/-- The former A4 statement, now a **THEOREM**: the color-respecting isomorphism is derived from
    the uncolored classification. If the pulled-back parity coloring disagrees with `col`, the two
    proper colorings of the connected graph are global swaps of each other, and composing with the
    CT-product's parity-flipping automorphism repairs the match. -/
theorem weak_ct_product {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ ranks : List Nat,
      CanonicalCTRanks ranks ∧
        ∃ e : G ≃g CTProductGraph ranks,
          ∀ v : V, CTProductColor ranks (e v) = col v := by
  classical
  obtain ⟨ranks, hcanon, ⟨e⟩⟩ := weak_ct_product_uncolored G col hIG hBB hcard
  have hprod : IsProper2Coloring (CTProductGraph ranks) (CTProductColor ranks) :=
    (ctProduct_equitable hcanon).1
  have hcol' : IsProper2Coloring G (fun v => CTProductColor ranks (e v)) := by
    intro u v huv
    exact hprod _ _ (e.map_rel_iff.mpr huv)
  have hVne : Nonempty V := by
    have h : 0 < Fintype.card V := by omega
    exact Fintype.card_pos_iff.mp h
  have hconn := isInterchangeGraph_connected hIG hVne
  rcases proper2Coloring_eq_or_flip hconn hcol' hBB with hsame | hflip
  · exact ⟨ranks, hcanon, e, hsame⟩
  · obtain ⟨φ, hφ⟩ := ctProduct_flip ranks (canonical_ne_nil hcanon) (canonical_all_ge2 hcanon)
    refine ⟨ranks, hcanon, e.trans φ, ?_⟩
    intro v
    have h1 : CTProductColor ranks (e v) = !(col v) := hflip v
    show CTProductColor ranks (φ (e v)) = col v
    rw [hφ (e v), h1]
    cases col v <;> rfl

theorem interchange_bipartite_equitable {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {col : V → Bool}
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) :
    IsEquitableBipartite G col := by
  rcases weak_ct_product G col hIG hBB hcard with ⟨ranks, hcanon, e, hcol⟩
  exact equitableBipartite_iso e hcol (ctProduct_equitable hcanon)

end Brualdi.Ledger
