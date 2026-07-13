/-
  FIDELITY SENTINELS — definition sanity / vacuity checks.

  A green build only certifies "the proof is valid GIVEN the definitions and axioms". These sentinels guard
  the DEFINITIONS themselves (the layer where the vacuous-`IsMH` bug lived). The method: prove instances a
  definition SHOULD satisfy, and exhibit (or track) ones it should NOT. See results/lean_fidelity_audit.md.
-/
import BrualdiLean.Coleman
import BrualdiLean.Basic
import BrualdiLean.Sec6
import BrualdiLean.Sec5

namespace Brualdi.Ledger
open Brualdi

/-- SATISFIABILITY of `brualdi_MH`'s hypothesis: a flip graph IS an interchange graph, so
    `IsInterchangeGraph` is not vacuously false (else `brualdi_MH` would be vacuously true). -/
theorem isInterchangeGraph_flipGraph {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    IsInterchangeGraph (flipGraph r s) :=
  ⟨m, n, r, s, Equiv.refl _, fun _ _ => Iff.rfl⟩

/-- GAP CLOSED (was `isMH_edgeless_GAP`). `IsMH` now REJECTS edgeless graphs on ≥2 vertices — two
    isolated vertices are not maximally Hamiltonian. The surjective-colouring requirement kills the
    former vacuity: any surjective colouring of `Fin 2` separates `0,1`, so laceability would demand a
    (nonexistent) Hamilton path between them. -/
theorem isMH_edgeless_rejected : ¬ IsMH (⊥ : SimpleGraph (Fin 2)) := by
  have no_walk : ∀ {x y : Fin 2}, x ≠ y → ¬ HasHamPath (⊥ : SimpleGraph (Fin 2)) x y := by
    rintro x y hxy ⟨p, _⟩
    cases p with
    | nil => exact hxy rfl
    | cons h _ => simp at h
  rintro (hHC | ⟨col, _hproper, hsurj, hlace⟩)
  · exact no_walk (by decide) (hHC 0 1 (by decide))
  · have h01 : col 0 ≠ col 1 := by
      intro h
      obtain ⟨a, ha⟩ := hsurj (!(col 0))
      fin_cases a <;> simp_all
    exact no_walk (by decide) (hlace 0 1 h01)

/-- SANITY: for a graph WITH an edge, the constant-colour witness no longer works (the original vacuity
    is genuinely blocked there) — the proper-colouring conjunct fails on the edge. -/
theorem isMH_const_blocked_on_edge :
    ¬ (∀ u v, (⊤ : SimpleGraph (Fin 2)).Adj u v → (fun _ => true) u ≠ (fun _ => true) v) := by
  intro h
  exact (h 0 1 (by decide)) rfl

/-! ### Degenerate-instance sentinels (2026-07-04).
    Four cited axioms gained nonemptiness/cardinality guards that day (`active_prime_cell_varies`,
    `prime_class_card_ge`, `weak_ct_product`, `prop11c`); each fact below exhibits the degenerate
    instance that FALSIFIED the unguarded form (kernel-checked `False` pre-fix; certificates archived
    in `results/unsoundness_certs_2026-07-04.lean.txt`). If a refactor ever drops a guard, the
    corresponding fact re-derives the contradiction. -/

/-- An ACTIVE margin pair with an EMPTY class (row total 6 ≠ column total 3): `IsActive` does NOT
    imply feasibility, so the `Nonempty` guards of `active_prime_cell_varies` /
    `prime_class_card_ge` are load-bearing. -/
theorem active_empty_class_exists :
    IsActive (fun _ : Fin 3 => 2) (fun _ : Fin 3 => 1) ∧
      IsEmpty (MarginClass (fun _ : Fin 3 => 2) (fun _ : Fin 3 => 1)) := by
  constructor
  · exact ⟨fun i => ⟨by norm_num, by norm_num⟩, fun j => ⟨by norm_num, by norm_num⟩⟩
  · constructor
    rintro ⟨M, hr, hc⟩
    have h3 : ∑ i, rowSum M i = ∑ j, colSum M j := by
      unfold rowSum colSum
      exact Finset.sum_comm
    have h1 : ∑ i, rowSum M i = 6 := by
      rw [Finset.sum_congr rfl (fun i _ => hr i)]
      simp
    have h2 : ∑ j, colSum M j = 3 := by
      rw [Finset.sum_congr rfl (fun j _ => hc j)]
      simp
    omega

/-- The ONE-VERTEX class (1×1, r=s=(1)): an interchange graph, vacuously balanced-bipartite, but
    NOT equitable — the `2 ≤ card` guard of `weak_ct_product` is load-bearing. -/
theorem one_vertex_class_not_equitable :
    IsInterchangeGraph (flipGraph (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) ∧
      IsProper2Coloring (flipGraph (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) (fun _ => false) ∧
      ¬ IsEquitableBipartite (flipGraph (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1))
          (fun _ => false) := by
  refine ⟨⟨1, 1, _, _, Equiv.refl _, fun _ _ => Iff.rfl⟩, ?_, ?_⟩
  · intro u v huv
    exfalso
    simp only [flipGraph, SimpleGraph.fromRel_adj] at huv
    obtain ⟨-, h | h⟩ := huv <;>
      · obtain ⟨i, i', j, j', hii', -⟩ := h
        exact hii' (Subsingleton.elim i i')
  · rintro ⟨-, hcard⟩
    have hM : HasMargins (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) (fun _ _ => true) := by
      constructor <;> intro x <;> simp [rowSum, colSum]
    have hpos : 0 < Fintype.card (MarginClass (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) :=
      Fintype.card_pos_iff.mpr ⟨⟨fun _ _ => true, hM⟩⟩
    have hfalse : Fintype.card {v : MarginClass (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) //
        (fun _ => false) v = false}
          = Fintype.card (MarginClass (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => rfl))
    have htrue : Fintype.card {v : MarginClass (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) //
        (fun _ => false) v = true} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun ⟨v, hv⟩ => by simp at hv⟩
    rw [hfalse, htrue] at hcard
    omega

/-- `E₂` (two isolated vertices) is equitable and VACUOUSLY spanning-2-laceable, yet NOT
    Hamilton-laceable — the `2k ≤ card` demand guard of `prop11c` is load-bearing. -/
theorem E2_spanning2_but_not_laceable :
    IsEquitableBipartite (⊥ : SimpleGraph (Fin 2)) (fun v => if v = 1 then true else false) ∧
      IsSpanning2DPCOpposite (⊥ : SimpleGraph (Fin 2)) (fun v => if v = 1 then true else false) ∧
      ¬ IsHamLaceable (⊥ : SimpleGraph (Fin 2)) (fun v => if v = 1 then true else false) := by
  refine ⟨⟨fun u v huv => by simp at huv, by decide⟩, ?_, ?_⟩
  · intro a₁ b₁ a₂ b₂ _ _ h3 h4 h5 h6 h7 h8
    exfalso
    fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;> simp_all
  · intro hL
    obtain ⟨p, -⟩ := hL 0 1 (by decide)
    cases p with
    | cons h _ => simp at h

/-- SENTINEL (trust-eval 2026-07-06 #11): `HasHamPath` really demands a *path* visiting *every*
    vertex. Mathlib's `Walk.IsHamiltonian p` is `∀ a, p.support.count a = 1`; this makes the two
    consequences (path-ness and full coverage) machine-checked rather than a prose gloss. -/
theorem hamPath_isPath {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (h : HasHamPath G u v) : ∃ p : G.Walk u v, p.IsPath ∧ ∀ x : V, x ∈ p.support := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.isPath, fun x => hp.mem_support x⟩

/-- SENTINEL (trust-eval 2026-07-06 #12): `IsColemanTree` forces the vertex type to be FINITE,
    even though its `base` constructor carries no `[Fintype]` hypothesis — a Hamilton path has
    finite support and must cover every vertex, and the demanded endpoint pair always exists
    (any two distinct vertices, or one from each color class of the surjective coloring). So
    `Nat.card` in the leaf condition is always the ordinary finite cardinality, never the junk
    value `0` of an infinite type: no infinite leaf can satisfy the predicate vacuously. -/
theorem colemanTree_finite {V : Type} {G : SimpleGraph V} {n : ℕ}
    (h : IsColemanTree G n) : Finite V := by
  induction h with
  | @base V' _instD G' hham hcard =>
      by_contra hinf
      rw [not_finite_iff_infinite] at hinf
      haveI := hinf
      obtain ⟨u, v, huv⟩ := exists_pair_ne V'
      rcases hham with hconn | ⟨col, hbal, hsurj, hlace⟩
      · obtain ⟨p, hp⟩ := hconn u v huv
        haveI := hp.fintype
        exact not_finite V'
      · obtain ⟨a, ha⟩ := hsurj false
        obtain ⟨b, hb⟩ := hsurj true
        obtain ⟨p, hp⟩ := hlace a b (by rw [ha, hb]; simp)
        haveI := hp.fintype
        exact not_finite V'
  | @weld V' W' G' ell' r' Gs' M' hr hEll htl hM e ih =>
      haveI := ih ⟨0, by omega⟩
      exact Finite.of_equiv _ e.toEquiv.symm

/-- SENTINEL (trust-eval 2026-07-06 #14): `IsInterchangeGraph` is not too broad — the edgeless
    graph on two vertices is NOT an interchange graph. (This sentinel consumes the cited Ryser
    connectivity, axiom A8 `flipGraph_connected`; it is a meaning check relative to the cited
    literature, and it is NOT on `brualdi_MH`'s axiom trace.) Since 2026-07-12, D11 bundles this
    guard directly into `IsBaseClass`; the former use-site audit is therefore subsumed. -/
theorem edgeless_two_not_interchangeGraph :
    ¬ IsInterchangeGraph (⊥ : SimpleGraph (Fin 2)) := by
  rintro ⟨m, n, r, s, φ, hadj⟩
  have hne : Nonempty (MarginClass r s) := ⟨φ 0⟩
  have hiso : (⊥ : SimpleGraph (Fin 2)) ≃g Brualdi.flipGraph r s :=
    { toEquiv := φ, map_rel_iff' := fun {a b} => (hadj a b).symm }
  have hconn : (⊥ : SimpleGraph (Fin 2)).Connected :=
    (SimpleGraph.Iso.connected_iff hiso).mpr (flipGraph_connected r s hne)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨p⟩ := hconn.preconnected 0 1
  cases p with
  | cons h _ => simp at h

/-- SENTINEL (Jeff's checklist read, 2026-07-12): the D11 guard is bundled definitionally, so the
    edgeless two-vertex graph cannot enter `IsBaseClass`, despite satisfying the small-cardinality
    disjunct of the former unbundled definition. -/
theorem edgeless_two_not_baseClass :
    ¬ IsBaseClass (⊥ : SimpleGraph (Fin 2)) := by
  intro hbase
  exact edgeless_two_not_interchangeGraph hbase.1

/-- SENTINEL (trust-eval-2 2026-07-06, A9 bridge): a `BaseFamily` is exactly the classical
    basis-family presentation of a matroid — the one-sided exchange axiom (B2) already forces
    all bases to be equicardinal, so "matroid basis" results (Naddef–Pulleyblank via
    Hausmann–Korte) apply to every `BaseFamily` verbatim, not merely to those set up to look
    like matroids. Proof: strong induction on `(A \\ C).card`. -/
theorem baseFamily_card_eq {α : Type u} [Fintype α] [DecidableEq α] (Bf : BaseFamily α)
    {A C : Finset α} (hA : Bf.Base A) (hC : Bf.Base C) : A.card = C.card := by
  classical
  suffices H : ∀ (n : ℕ) (A : Finset α), Bf.Base A → (A \ C).card = n → A.card = C.card from
    H _ A hA rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hn
    by_cases hAC : A \ C = ∅
    · have hsub : A ⊆ C := by rwa [Finset.sdiff_eq_empty_iff_subset] at hAC
      by_cases hCA : C \ A = ∅
      · have hsub' : C ⊆ A := by rwa [Finset.sdiff_eq_empty_iff_subset] at hCA
        rw [Finset.Subset.antisymm hsub hsub']
      · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hCA
        rw [Finset.mem_sdiff] at he
        obtain ⟨f, hfA, hfC, -⟩ := Bf.exchange hC hA he.1 he.2
        exact absurd (hsub hfA) hfC
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hAC
      rw [Finset.mem_sdiff] at he
      obtain ⟨f, hfC, hfA, hbase⟩ := Bf.exchange hA hC he.1 he.2
      have hfAe : f ∉ A.erase e := fun h => hfA (Finset.mem_of_mem_erase h)
      have hcard' : (insert f (A.erase e)).card = A.card := by
        rw [Finset.card_insert_of_notMem hfAe, Finset.card_erase_of_mem he.1]
        have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨e, he.1⟩
        omega
      have hsdiff : (insert f (A.erase e)) \ C = (A \ C).erase e := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hx | ⟨hxe, hxA⟩, hxC⟩
          · exact absurd (hx ▸ hfC) hxC
          · exact ⟨hxe, hxA, hxC⟩
        · rintro ⟨hxe, hxA, hxC⟩
          exact ⟨Or.inr ⟨hxe, hxA⟩, hxC⟩
      have hlt : ((insert f (A.erase e)) \ C).card < n := by
        rw [hsdiff, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr he)]
        have h1 : 1 ≤ n := by
          rw [← hn]
          exact Finset.card_pos.mpr ⟨e, Finset.mem_sdiff.mpr he⟩
        omega
      have hres := ih _ hlt (insert f (A.erase e)) hbase rfl
      omega

end Brualdi.Ledger
