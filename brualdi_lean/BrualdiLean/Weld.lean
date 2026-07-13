/-
Weld.lean — Tier 3 of the §7 discharge program: toward a from-scratch proof of Coleman
et al.'s Theorem 1.5 (axiom A1). 2026-07-06.

This file mechanizes **Lemma 2.1 of Coleman et al. 2025** (`weld_lemma21`): if a family of
disjoint paths in a weld covers exactly the copies indexed by `J` (with prescribed endpoints),
it extends to a paired DPC of the WHOLE weld — the first path absorbs each missing copy through
a first-edge detour: replace the edge `s₀—w` by `s₀ — (entry into the copy) — Hamilton path of
the copy — (exit) — w`. The detour endpoints are opposite-colored (both cross edges and the
`s₀—w` edge are proper), so laceability of the copy supplies the Hamilton path.

This is the assembly device for all five cases of their Proposition 1.6 (the weld induction
step), which is the remaining Tier 3 work. Nothing here is wired into the mainline.
-/
import BrualdiLean.DPC2

namespace Brualdi.Ledger

universe u

variable {W : Type u} [DecidableEq W] [Fintype W]

/-! ## Copies inside a weld -/

/-- The `j`-th copy embeds in the weld. -/
def weldLift {ell : ℕ} (Gs : Fin ell → SimpleGraph W) (M : Fin ell → Fin ell → (W ≃ W)) (j : Fin ell) :
    Gs j →g weldGraph ell Gs M where
  toFun := fun w => (j, w)
  map_rel' := by
    intro a b hab
    refine ⟨?_, Or.inl (Or.inl ⟨rfl, hab⟩)⟩
    intro h
    exact (Gs j).ne_of_adj hab (congrArg Prod.snd h)

theorem weldLift_inj {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    (j : Fin ell) : Function.Injective (weldLift Gs M j) := by
  intro a b hab
  exact congrArg Prod.snd hab

theorem weldLift_mem_support {ell : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {j : Fin ell} {u v : W} {q : (Gs j).Walk u v}
    {x : Fin ell × W} :
    x ∈ (q.map (weldLift Gs M j)).support ↔ x.1 = j ∧ x.2 ∈ q.support := by
  rw [SimpleGraph.Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨rfl, hw⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.2, h2, Prod.ext h1.symm rfl⟩

/-- The matching edge from copy `i` to copy `j`. -/
theorem weld_cross_adj {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {i j : Fin ell} (hij : i ≠ j) (u : W) :
    (weldGraph ell Gs M).Adj (i, u) (j, M i j u) := by
  refine ⟨?_, Or.inl (Or.inr ⟨hij, rfl⟩)⟩
  intro h
  exact hij (congrArg Prod.fst h)

/-! ## The single-copy extension (the Lemma 2.1 surgery) -/

set_option maxHeartbeats 1600000 in
/-- Absorb one missing copy `j` into the first path of a `J`-confined disjoint family, by a
    first-edge detour through a Hamilton path of the copy. -/
theorem weld_extend_one {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool}
    (hproper : ∀ x y, (weldGraph ell Gs M).Adj x y → col x ≠ col y)
    (hlace : ∀ j : Fin ell, IsHamLaceable (Gs j) (fun w => col (j, w)))
    {k : ℕ} {s t : Fin (k + 1) → Fin ell × W}
    {J : Finset (Fin ell)} {j : Fin ell} (hjJ : j ∉ J)
    (hst : s 0 ≠ t 0)
    (p : ∀ i, (weldGraph ell Gs M).Walk (s i) (t i))
    (hpath : ∀ i, (p i).IsPath)
    (hin : ∀ i, ∀ x, x ∈ (p i).support → x.1 ∈ J)
    (hdisj : ∀ a b, a ≠ b → ∀ x, ¬ (x ∈ (p a).support ∧ x ∈ (p b).support)) :
    ∃ p' : ∀ i, (weldGraph ell Gs M).Walk (s i) (t i),
      (∀ i, (p' i).IsPath) ∧
      (∀ i, ∀ x, x ∈ (p' i).support → x.1 ∈ insert j J) ∧
      (∀ x : Fin ell × W, ((∃ i, x ∈ (p i).support) ∨ x.1 = j) → ∃ i, x ∈ (p' i).support) ∧
      (∀ a b, a ≠ b → ∀ x, ¬ (x ∈ (p' a).support ∧ x ∈ (p' b).support)) := by
  classical
  obtain ⟨w, hadj, rest, hp0⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hst (p 0)
  have hrest : rest.IsPath ∧ s 0 ∉ rest.support := by
    have h := hpath 0
    rw [hp0] at h
    exact (SimpleGraph.Walk.cons_isPath_iff hadj rest).mp h
  have hp0supp : (p 0).support = s 0 :: rest.support := by
    rw [hp0]
    exact SimpleGraph.Walk.support_cons _ _
  have hs0J : (s 0).1 ∈ J := hin 0 (s 0) ((p 0).start_mem_support)
  have hrestJ : ∀ x, x ∈ rest.support → x.1 ∈ J := by
    intro x hx
    exact hin 0 x (by rw [hp0supp]; exact List.mem_cons_of_mem _ hx)
  have hwJ : w.1 ∈ J := hrestJ w rest.start_mem_support
  have hjs0 : (s 0).1 ≠ j := fun h => hjJ (h ▸ hs0J)
  have hjw : w.1 ≠ j := fun h => hjJ (h ▸ hwJ)
  -- entry and exit vertices of the detour
  set y : W := M (s 0).1 j (s 0).2 with hy
  set z : W := (M j w.1).symm w.2 with hz
  have hadj_in : (weldGraph ell Gs M).Adj (s 0) (j, y) := weld_cross_adj hjs0 (s 0).2
  have hadj_out : (weldGraph ell Gs M).Adj (j, z) w := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (i := j) (j := w.1)
      (fun hh => hjw hh.symm) z
    have he : ((w.1, M j w.1 z) : Fin ell × W) = w := by
      rw [hz, Equiv.apply_symm_apply]
    rwa [he] at h
  have hcol_sy : col (s 0) ≠ col (j, y) := hproper _ _ hadj_in
  have hcol_zw : col (j, z) ≠ col w := hproper _ _ hadj_out
  have hcol_sw : col (s 0) ≠ col w := hproper _ _ hadj
  have hcol_yz : col (j, y) ≠ col (j, z) := by
    cases c1 : col (s 0) <;> cases c2 : col w <;> cases c3 : col (j, y) <;>
      cases c4 : col (j, z) <;> simp_all
  obtain ⟨q, hq⟩ := hlace j y z hcol_yz
  -- the new first path
  set R₁ : (weldGraph ell Gs M).Walk (j, y) (j, z) := q.map (weldLift Gs M j) with hR₁
  set R₂ : (weldGraph ell Gs M).Walk (j, z) (t 0) := SimpleGraph.Walk.cons hadj_out rest
    with hR₂
  set P₀ : (weldGraph ell Gs M).Walk (s 0) (t 0) :=
    SimpleGraph.Walk.cons hadj_in (R₁.append R₂) with hP₀
  have hR₁supp : ∀ x : Fin ell × W, x ∈ R₁.support ↔ x.1 = j ∧ x.2 ∈ q.support := by
    intro x
    rw [hR₁]
    exact weldLift_mem_support
  have hR₁all : ∀ u : W, (j, u) ∈ R₁.support := by
    intro u
    rw [hR₁supp]
    exact ⟨rfl, hq.mem_support u⟩
  have hR₂tail : R₂.support.tail = rest.support := by
    rw [hR₂, SimpleGraph.Walk.support_cons, List.tail_cons]
  have hP₀supp : P₀.support = s 0 :: (R₁.support ++ rest.support) := by
    rw [hP₀, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_append, hR₂tail]
  have hP₀path : P₀.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hP₀supp]
    rw [List.nodup_cons]
    constructor
    · rw [List.mem_append]
      rintro (h | h)
      · rw [hR₁supp] at h
        exact hjs0 h.1
      · exact hrest.2 h
    · rw [List.nodup_append]
      refine ⟨?_, hrest.1.support_nodup, ?_⟩
      · rw [hR₁]
        exact (SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj j)
          hq.isPath).support_nodup
      · intro x hx w' hw' heq
        subst heq
        rw [hR₁supp] at hx
        exact hjJ (hx.1 ▸ hrestJ x hw')
  refine ⟨fun i => if h : i = 0 then
      P₀.copy (congrArg s h.symm) (congrArg t h.symm)
    else p i, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0
    · rw [dif_pos h, SimpleGraph.Walk.isPath_copy]
      exact hP₀path
    · rw [dif_neg h]
      exact hpath i
  · intro i x hx
    dsimp only at hx
    by_cases h : i = 0
    · rw [dif_pos h, SimpleGraph.Walk.support_copy, hP₀supp] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Finset.mem_insert_of_mem hs0J
      · rcases List.mem_append.mp hx with hx | hx
        · rw [hR₁supp] at hx
          rw [hx.1]
          exact Finset.mem_insert_self j J
        · exact Finset.mem_insert_of_mem (hrestJ x hx)
    · rw [dif_neg h] at hx
      exact Finset.mem_insert_of_mem (hin i x hx)
  · intro x hx
    rcases hx with ⟨i, hi⟩ | hj'
    · by_cases h : i = 0
      · refine ⟨0, ?_⟩
        dsimp only
        rw [dif_pos rfl, SimpleGraph.Walk.support_copy, hP₀supp]
        subst h
        rw [hp0supp] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hi))
      · refine ⟨i, ?_⟩
        dsimp only
        rw [dif_neg h]
        exact hi
    · refine ⟨0, ?_⟩
      dsimp only
      rw [dif_pos rfl, SimpleGraph.Walk.support_copy, hP₀supp]
      apply List.mem_cons_of_mem
      apply List.mem_append.mpr
      left
      have hxeta : x = (j, x.2) := by
        rw [← hj']
      rw [hxeta]
      exact hR₁all x.2
  · intro a b hab x hx
    dsimp only at hx
    have hmem : ∀ (c : Fin (k+1)), x ∈ (if h : c = 0 then
        P₀.copy (congrArg s h.symm) (congrArg t h.symm) else p c).support →
        (c = 0 ∧ (x ∈ (p 0).support ∨ x.1 = j)) ∨ (c ≠ 0 ∧ x ∈ (p c).support) := by
      intro c hc
      by_cases h : c = 0
      · rw [dif_pos h, SimpleGraph.Walk.support_copy, hP₀supp] at hc
        refine Or.inl ⟨h, ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl ((p 0).start_mem_support)
        · rcases List.mem_append.mp hc with hc | hc
          · rw [hR₁supp] at hc
            exact Or.inr hc.1
          · refine Or.inl ?_
            rw [hp0supp]
            exact List.mem_cons_of_mem _ hc
      · rw [dif_neg h] at hc
        exact Or.inr ⟨h, hc⟩
    rcases hmem a hx.1 with ⟨ha0, hcase_a⟩ | ⟨ha0, ha1⟩ <;>
      rcases hmem b hx.2 with ⟨hb0, hcase_b⟩ | ⟨hb0, hb1⟩
    · exact hab (ha0.trans hb0.symm)
    · rcases hcase_a with ha1 | ha1
      · exact hdisj 0 b (fun h => hb0 h.symm) x ⟨ha1, hb1⟩
      · exact hjJ (ha1 ▸ hin b x hb1)
    · rcases hcase_b with hb1 | hb1
      · exact hdisj a 0 ha0 x ⟨ha1, hb1⟩
      · exact hjJ (hb1 ▸ hin a x ha1)
    · exact hdisj a b hab x ⟨ha1, hb1⟩

/-! ## Lemma 2.1: extend a sub-weld cover to the whole weld -/

private theorem weld_extend_aux {ell : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : ∀ x y, (weldGraph ell Gs M).Adj x y → col x ≠ col y)
    (hlace : ∀ j : Fin ell, IsHamLaceable (Gs j) (fun w => col (j, w)))
    {k : ℕ} {s t : Fin (k + 1) → Fin ell × W} (hst : s 0 ≠ t 0) :
    ∀ (n : ℕ) (J : Finset (Fin ell)), (Finset.univ \ J).card = n →
    ∀ (p : ∀ i, (weldGraph ell Gs M).Walk (s i) (t i)),
      (∀ i, (p i).IsPath) →
      (∀ i, ∀ x, x ∈ (p i).support → x.1 ∈ J) →
      (∀ x : Fin ell × W, x.1 ∈ J → ∃ i, x ∈ (p i).support) →
      (∀ a b, a ≠ b → ∀ x, ¬ (x ∈ (p a).support ∧ x ∈ (p b).support)) →
      IsPairedDPC (weldGraph ell Gs M) (k + 1) s t
  | 0, J, hn, p, hpath, _, hcovJ, hdisj => by
      have hJ : Finset.univ ⊆ J := by
        intro x _
        by_contra hx
        have hmem : x ∈ Finset.univ \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        rw [Finset.card_eq_zero.mp hn] at hmem
        exact absurd hmem (Finset.notMem_empty x)
      exact ⟨p, hpath, fun x => hcovJ x (hJ (Finset.mem_univ x.1)), hdisj⟩
  | n + 1, J, hn, p, hpath, hin, hcovJ, hdisj => by
      have hne : (Finset.univ \ J).Nonempty := by
        rw [← Finset.card_pos, hn]
        omega
      obtain ⟨j, hj⟩ := hne
      have hjJ : j ∉ J := (Finset.mem_sdiff.mp hj).2
      obtain ⟨p', h1, h2, h3, h4⟩ :=
        weld_extend_one hproper hlace hjJ hst p hpath hin hdisj
      refine weld_extend_aux hproper hlace hst n (insert j J) ?_ p' h1 h2 ?_ h4
      · have e1 : (Finset.univ \ J).card = Fintype.card (Fin ell) - J.card := by
          rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
        have e2 : (Finset.univ \ insert j J).card =
            Fintype.card (Fin ell) - (insert j J).card := by
          rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
        have e3 : (insert j J).card = J.card + 1 := Finset.card_insert_of_notMem hjJ
        have e4 : J.card ≤ Fintype.card (Fin ell) := by
          rw [← Finset.card_univ]
          exact Finset.card_le_card (Finset.subset_univ J)
        omega
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact h3 x (Or.inr hx)
        · obtain ⟨i, hi⟩ := hcovJ x hx
          exact h3 x (Or.inl ⟨i, hi⟩)

/-- **Coleman et al. 2025, Lemma 2.1** (weld extension): a disjoint path family with the
    demanded endpoints that covers exactly the copies indexed by `J` extends to a paired
    DPC of the whole weld. -/
theorem weld_lemma21 {ell : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : ∀ x y, (weldGraph ell Gs M).Adj x y → col x ≠ col y)
    (hlace : ∀ j : Fin ell, IsHamLaceable (Gs j) (fun w => col (j, w)))
    {k : ℕ} {s t : Fin (k + 1) → Fin ell × W} (hst : s 0 ≠ t 0)
    (J : Finset (Fin ell))
    (p : ∀ i, (weldGraph ell Gs M).Walk (s i) (t i))
    (hpath : ∀ i, (p i).IsPath)
    (hin : ∀ i, ∀ x, x ∈ (p i).support → x.1 ∈ J)
    (hcovJ : ∀ x : Fin ell × W, x.1 ∈ J → ∃ i, x ∈ (p i).support)
    (hdisj : ∀ a b, a ≠ b → ∀ x, ¬ (x ∈ (p a).support ∧ x ∈ (p b).support)) :
    IsPairedDPC (weldGraph ell Gs M) (k + 1) s t :=
  weld_extend_aux hproper hlace hst (Finset.univ \ J).card J rfl p hpath hin hcovJ hdisj

#print axioms weld_lemma21

/-! ## The Proposition 1.6 target (statement only; the five-case proof is the remaining
Tier 3 work — see results/dpc_program_design_2026-07-06.md for the case plan) -/

/-- The hypotheses of Coleman et al.'s Proposition 1.6, over our pairwise demand encoding:
    a weld of `ell ≥ n+1` copies, each equitable of order `≥ 4n−2` (order is `Fintype.card W`,
    shared), each admitting `(n−1)`-PDPCs for all legal demands, with the weld coloring
    proper and restricting to a proper equitable coloring on every copy. -/
structure ColemanProp16Setting {W : Type u} [DecidableEq W] [Fintype W] (ell n : ℕ)
    (Gs : Fin ell → SimpleGraph W) (M : Fin ell → Fin ell → (W ≃ W))
    (col : Fin ell × W → Bool) : Prop where
  hn : 3 ≤ n
  hEll : n + 1 ≤ ell
  horder : 4 * n - 2 ≤ Fintype.card W
  hM : ∀ i j, M j i = (M i j).symm
  hproper : ∀ x y, (weldGraph ell Gs M).Adj x y → col x ≠ col y
  hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w))
  hcopy_pdpc : ∀ j : Fin ell,
    IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) (n - 1)

/-- **The Tier 3 target** (Coleman et al. 2025, Proposition 1.6): under the setting, the weld
    admits `n`-PDPCs. Once proved, the `IsColemanTree` rank induction discharges axiom A1. -/
def ColemanProp16Statement {W : Type u} [DecidableEq W] [Fintype W] (ell n : ℕ)
    (Gs : Fin ell → SimpleGraph W) (M : Fin ell → Fin ell → (W ≃ W))
    (col : Fin ell × W → Bool) : Prop :=
  ColemanProp16Setting ell n Gs M col →
    IsPairedKDPCForOpposite (weldGraph ell Gs M) col n

/-- Copy laceability follows inside the setting (Tier 1 at `l = 1`), as Coleman's cases use it. -/
theorem ColemanProp16Setting.copy_lace {W : Type u} [DecidableEq W] [Fintype W]
    {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) :
    IsHamLaceable (Gs j) (fun w => col (j, w)) := by
  apply paired_one_opposite_iff_hamLaceable.mp
  apply prop11c_proved _ _ (S.hcopy_eq j) (S.hcopy_pdpc j) (le_refl 1) ?_ ?_
  · have := S.hn
    omega
  · have h1 := S.horder
    have h2 := S.hn
    omega

#print axioms ColemanProp16Setting.copy_lace

end Brualdi.Ledger
