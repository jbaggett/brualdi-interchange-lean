/-
DPC2.lean — Tier 2 of the §7 discharge program: the hypercube paired 2-DPC theorem
(the content of axiom A3), by induction on the rank list. 2026-07-06, "finish them".

Structure: reindex/reverse invariance of covers; the half/lift machinery for CT₂ □ H;
the four case constructions (both-pairs-within-same-half, within-different-halves,
one-within-one-split, both-split); the Q₃ special case (where the free-vertex count
fails and K₂,₂-completeness of Q₂ powers explicit covers); the main induction.

Everything foundations-only; nothing wired into the mainline.
-/
import BrualdiLean.DPC

namespace Brualdi.Ledger

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-! ## Cover invariances -/

/-- Reindexing the demand pairs by a permutation preserves coverability. -/
theorem dpc_reindex {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V}
    (σ : Equiv.Perm (Fin k))
    (h : IsPairedDPC G k (s ∘ σ) (t ∘ σ)) : IsPairedDPC G k s t := by
  obtain ⟨p, hpath, hcover, hdisj⟩ := h
  refine ⟨fun i => (p (σ.symm i)).copy (by simp) (by simp), ?_, ?_, ?_⟩
  · intro i
    rw [SimpleGraph.Walk.isPath_copy]
    exact hpath (σ.symm i)
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨σ i, ?_⟩
    rw [SimpleGraph.Walk.support_copy]
    have hσ : σ.symm (σ i) = i := σ.symm_apply_apply i
    rw [hσ]
    exact hi
  · intro a b hab x hx
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hx
    exact hdisj (σ.symm a) (σ.symm b) (fun h => hab (σ.symm.injective h)) x hx

/-- Reversing one demand pair preserves coverability. -/
theorem dpc_reverse_pair {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V} (i₀ : Fin k)
    (h : IsPairedDPC G k (Function.update s i₀ (t i₀)) (Function.update t i₀ (s i₀))) :
    IsPairedDPC G k s t := by
  classical
  obtain ⟨p, hpath, hcover, hdisj⟩ := h
  refine ⟨fun i => if hi : i = i₀ then
      ((p i).reverse.copy (by rw [hi]; simp) (by rw [hi]; simp)).copy
        (congrArg s hi.symm) (congrArg t hi.symm)
    else
      (p i).copy (Function.update_of_ne hi _ _) (Function.update_of_ne hi _ _), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hi : i = i₀
    · rw [dif_pos hi]
      simp only [SimpleGraph.Walk.isPath_copy]
      exact (hpath i).reverse
    · rw [dif_neg hi, SimpleGraph.Walk.isPath_copy]
      exact hpath i
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨i, ?_⟩
    dsimp only
    by_cases h' : i = i₀
    · rw [dif_pos h']
      simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse]
      rw [List.mem_reverse]
      exact hi
    · rw [dif_neg h', SimpleGraph.Walk.support_copy]
      exact hi
  · intro a b hab x hx
    dsimp only at hx
    have hget : ∀ (j : Fin k), x ∈ (if hj : j = i₀ then
        (((p j).reverse.copy (by rw [hj]; simp) (by rw [hj]; simp)).copy
          (congrArg s hj.symm) (congrArg t hj.symm)) else
        ((p j).copy (Function.update_of_ne hj _ _) (Function.update_of_ne hj _ _))).support →
        x ∈ (p j).support := by
      intro j hj
      by_cases h' : j = i₀
      · rw [dif_pos h'] at hj
        simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
          List.mem_reverse] at hj
        exact hj
      · rw [dif_neg h', SimpleGraph.Walk.support_copy] at hj
        exact hj
    exact hdisj a b hab x ⟨hget a hx.1, hget b hx.2⟩

/-! ## The half/lift machinery for `A □ H` with a complete first factor -/

section HalfLift

variable {E W : Type u} [DecidableEq E] [Fintype E] [DecidableEq W] [Fintype W]
variable {A : SimpleGraph E} {H : SimpleGraph W}

/-- The embedding of `H` as the `ε`-layer of `A □ H`. -/
def dpcLift (A : SimpleGraph E) (H : SimpleGraph W) (ε : E) : H →g (A □ H) where
  toFun := fun v => (ε, v)
  map_rel' := by
    intro a b hab
    exact SimpleGraph.boxProd_adj.mpr (Or.inr ⟨hab, rfl⟩)

theorem dpcLift_inj (ε : E) : Function.Injective (dpcLift A H ε) := by
  intro a b hab
  exact congrArg Prod.snd hab

theorem dpcLift_support {ε : E} {u v : W} (p : H.Walk u v) :
    ((p.map (dpcLift A H ε)).support) = p.support.map (fun w => (ε, w)) :=
  SimpleGraph.Walk.support_map _ _

theorem dpcLift_mem_support {ε : E} {u v : W} {p : H.Walk u v} {x : E × W} :
    x ∈ (p.map (dpcLift A H ε)).support ↔ x.1 = ε ∧ x.2 ∈ p.support := by
  rw [dpcLift_support, List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨rfl, hw⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.2, h2, by rw [← h1]⟩

theorem dpc_vertical_adj {ε ε' : E} (hA : A.Adj ε ε') (v : W) :
    (A □ H).Adj (ε, v) (ε', v) :=
  SimpleGraph.boxProd_adj.mpr (Or.inl ⟨hA, rfl⟩)

end HalfLift

/-! ## Small facts about `CT₂` and all-twos products -/

private theorem ct2_adj_of_ne : ∀ ε ε' : Equiv.Perm (Fin 2), ε ≠ ε' →
    (CompleteTranspositionGraph 2).Adj ε ε' := by decide

/-- The other vertex of `CT₂`. -/
private def dpcOpp (ε : Equiv.Perm (Fin 2)) : Equiv.Perm (Fin 2) :=
  ε * Equiv.swap 0 1

private theorem dpcOpp_ne : ∀ ε, dpcOpp ε ≠ ε := by decide

private theorem dpcOpp_opp : ∀ ε, dpcOpp (dpcOpp ε) = ε := by decide

private theorem ct2_eq_or_opp : ∀ ε ε' : Equiv.Perm (Fin 2), ε' = ε ∨ ε' = dpcOpp ε := by
  decide

private theorem ct2_color_opp : ∀ ε, CompleteTranspositionColor 2 (dpcOpp ε) =
    !(CompleteTranspositionColor 2 ε) := by decide

/-- Vertex counts of all-twos products: `2 ^ length`. -/
private theorem dpc_vt_card : ∀ (tail : List Nat), tail ≠ [] → (∀ a ∈ tail, a = 2) →
    Fintype.card (CTProductVertex tail) = 2 ^ tail.length
  | [], hne, _ => absurd rfl hne
  | [a], _, hall => by
      have ha : a = 2 := hall a (List.mem_cons_self ..)
      subst ha
      show Fintype.card (Equiv.Perm (Fin 2)) = 2 ^ 1
      rw [Fintype.card_perm, Fintype.card_fin]
      rfl
  | a :: b :: t, _, hall => by
      have ha : a = 2 := hall a (List.mem_cons_self ..)
      subst ha
      have hrec := dpc_vt_card (b :: t) (by simp)
        (fun x hx => hall x (List.mem_cons_of_mem 2 hx))
      show Fintype.card (Equiv.Perm (Fin 2) × CTProductVertex (b :: t)) = 2 ^ (b :: t).length.succ
      rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, hrec]
      ring_nf
      rfl


/-- The non-zero element of `Fin 2`. -/
private theorem dpc2_fin2 : ∀ (i : Fin 2), i ≠ 0 → i = 1 := by decide

/-! ## Cross-half splicing and spare selection -/

section HalfLift

variable {E W : Type u} [DecidableEq E] [Fintype E] [DecidableEq W] [Fintype W]
variable {A : SimpleGraph E} {H : SimpleGraph W}

/-- Splice a path in the `ε`-layer to a path in the `ε'`-layer across the vertical edge at
    their shared `W`-coordinate. -/
theorem dpc_cross_splice {ε ε' : E} (hA : A.Adj ε ε') {a x b : W}
    (q : H.Walk a x) (r : H.Walk x b) (hq : q.IsPath) (hr : r.IsPath) :
    ∃ R : (A □ H).Walk (ε, a) (ε', b), R.IsPath ∧
      R.support = q.support.map (fun w => (ε, w)) ++ r.support.map (fun w => (ε', w)) := by
  have hεε' : ε ≠ ε' := A.ne_of_adj hA
  obtain ⟨R, hRp, hRs⟩ := dpc_splice (q.map (dpcLift A H ε)) (r.map (dpcLift A H ε'))
    (SimpleGraph.Walk.map_isPath_of_injective (dpcLift_inj ε) hq)
    (SimpleGraph.Walk.map_isPath_of_injective (dpcLift_inj ε') hr)
    (dpc_vertical_adj hA x)
    (by
      intro v hv
      rw [dpcLift_mem_support, dpcLift_mem_support] at hv
      exact hεε' (hv.1.1.symm.trans hv.2.1))
  rw [dpcLift_support, dpcLift_support] at hRs
  exact ⟨R, hRp, hRs⟩

/-- A color class larger than its trace on an avoid set has a member outside it. -/
theorem dpc_spare_avoid {colH : W → Bool} (c : Bool) (avoid : Finset W)
    (h : (avoid.filter (fun w => colH w = c)).card <
      (Finset.univ.filter (fun w => colH w = c)).card) :
    ∃ y, colH y = c ∧ y ∉ avoid := by
  classical
  have hpos : 0 < ((Finset.univ.filter (fun w => colH w = c)) \
      (avoid.filter (fun w => colH w = c))).card := by
    have hsub := Finset.card_le_card_sdiff_add_card
      (s := Finset.univ.filter (fun w => colH w = c))
      (t := avoid.filter (fun w => colH w = c))
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hy
  refine ⟨y, hy.1.2, ?_⟩
  intro hmem
  exact hy.2 ⟨hmem, hy.1.2⟩

end HalfLift

/-! ## The four case constructions, over an abstract two-layer product

Standing data: a two-element complete first factor (`ε` and `dpcOpp`-style partner given
abstractly by `ε'` with `hE2 : ∀ e, e = ε ∨ e = ε'`), a bipartite second factor `H` with
coloring `colH`, and the xor product coloring. The main induction instantiates
`E := Equiv.Perm (Fin 2)`, `A := CT₂`, `H := CTProduct tail`. -/

section Cases

variable {E W : Type u} [DecidableEq E] [Fintype E] [DecidableEq W] [Fintype W]
variable {A : SimpleGraph E} {H : SimpleGraph W} {colA : E → Bool} {colH : W → Bool}

/-- The product coloring. -/
def dpcColP (colA : E → Bool) (colH : W → Bool) : E × W → Bool :=
  fun x => xor (colA x.1) (colH x.2)

/-- Case A′: both pairs internal, in different layers — two lifted Hamilton paths. -/
theorem dpc_caseA' {ε ε' : E} (hεε' : ε ≠ ε')
    (hE2 : ∀ e : E, e = ε ∨ e = ε')
    (hlace : IsHamLaceable H colH)
    {s t : Fin 2 → E × W}
    (hd : OppositeDemand (dpcColP colA colH) s t)
    (h0s : (s 0).1 = ε) (h0t : (t 0).1 = ε) (h1s : (s 1).1 = ε') (h1t : (t 1).1 = ε') :
    IsPairedDPC (A □ H) 2 s t := by
  classical
  have hcol : ∀ i, colH (s i).2 ≠ colH (t i).2 := by
    intro i
    have h := hd.1 i
    unfold dpcColP at h
    intro hc
    apply h
    by_cases hi : i = 0
    · subst hi
      rw [h0s, h0t, hc]
    · rw [dpc2_fin2 i hi] at h hc ⊢
      rw [h1s, h1t, hc]
  obtain ⟨p0, hp0⟩ := hlace (s 0).2 (t 0).2 (hcol 0)
  obtain ⟨p1, hp1⟩ := hlace (s 1).2 (t 1).2 (hcol 1)
  refine ⟨fun i => if h : i = 0 then
      ((p0.map (dpcLift A H ε)).copy
        (by rw [h]; exact Prod.ext h0s.symm rfl) (by rw [h]; exact Prod.ext h0t.symm rfl))
    else
      ((p1.map (dpcLift A H ε')).copy
        (by rw [dpc2_fin2 i h]; exact Prod.ext h1s.symm rfl)
        (by rw [dpc2_fin2 i h]; exact Prod.ext h1t.symm rfl)), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0 <;>
      [rw [dif_pos h]; rw [dif_neg h]] <;>
      rw [SimpleGraph.Walk.isPath_copy] <;>
      exact SimpleGraph.Walk.map_isPath_of_injective (dpcLift_inj _) (by
        first | exact hp0.isPath | exact hp1.isPath)
  · intro x
    rcases hE2 x.1 with hx | hx
    · refine ⟨0, ?_⟩
      dsimp only
      rw [dif_pos rfl, SimpleGraph.Walk.support_copy, dpcLift_mem_support]
      exact ⟨hx, hp0.mem_support x.2⟩
    · refine ⟨1, ?_⟩
      dsimp only
      rw [dif_neg (by decide : (1 : Fin 2) ≠ 0), SimpleGraph.Walk.support_copy,
        dpcLift_mem_support]
      exact ⟨hx, hp1.mem_support x.2⟩
  · intro a b hab x hx
    dsimp only at hx
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · exact hab (ha.trans hb.symm)
    · rw [dif_pos ha, SimpleGraph.Walk.support_copy, dpcLift_mem_support] at hx
      rw [dif_neg hb, SimpleGraph.Walk.support_copy, dpcLift_mem_support] at hx
      exact hεε' (hx.1.1.symm.trans hx.2.1)
    · rw [dif_pos hb, SimpleGraph.Walk.support_copy, dpcLift_mem_support] at hx
      rw [dif_neg ha, SimpleGraph.Walk.support_copy, dpcLift_mem_support] at hx
      exact hεε' (hx.2.1.symm.trans hx.1.1)
    · exact hab ((dpc2_fin2 a ha).trans (dpc2_fin2 b hb).symm)

end Cases

/-! ## Boolean xor toolkit -/

private theorem dpc_xor_ne_of_ne : ∀ x x' p q : Bool, x ≠ x' →
    ((xor x p ≠ xor x' q) ↔ p = q) := by decide

private theorem dpc_xor_ne_of_eq : ∀ x p q : Bool,
    ((xor x p ≠ xor x q) ↔ p ≠ q) := by decide

section Cases2

variable {E W : Type u} [DecidableEq E] [Fintype E] [DecidableEq W] [Fintype W]
variable {A : SimpleGraph E} {H : SimpleGraph W} {colA : E → Bool} {colH : W → Bool}

/-- Distinct product vertices in the same layer have distinct `W`-coordinates. -/
private theorem dpc_snd_ne {x y : E × W} (hxy : x ≠ y) (h : x.1 = y.1) : x.2 ≠ y.2 := by
  intro h2
  exact hxy (Prod.ext h h2)

/-- Case B: both pairs split, both sources in the `ε`-layer. -/
theorem dpc_caseB {ε ε' : E} (hA : A.Adj ε ε') (hE2 : ∀ e : E, e = ε ∨ e = ε')
    (h2dpc : IsPairedKDPCForOpposite H colH 2)
    (hclass3 : ∀ c, 3 ≤ (Finset.univ.filter (fun w => colH w = c)).card)
    (hcolA : colA ε ≠ colA ε')
    {s t : Fin 2 → E × W} (hd : OppositeDemand (dpcColP colA colH) s t)
    (h0s : (s 0).1 = ε) (h1s : (s 1).1 = ε) (h0t : (t 0).1 = ε') (h1t : (t 1).1 = ε') :
    IsPairedDPC (A □ H) 2 s t := by
  classical
  set va := (s 0).2 with hva
  set vb := (t 0).2 with hvb
  set vc := (s 1).2 with hvc
  set vd := (t 1).2 with hvd
  -- split pairs have equal H-colors
  have hcol0 : colH va = colH vb := by
    have h := hd.1 0
    unfold dpcColP at h
    rw [h0s, h0t] at h
    exact (dpc_xor_ne_of_ne _ _ _ _ hcolA).mp h
  have hcol1 : colH vc = colH vd := by
    have h := hd.1 1
    unfold dpcColP at h
    rw [h1s, h1t] at h
    exact (dpc_xor_ne_of_ne _ _ _ _ hcolA).mp h
  have hvavc : va ≠ vc := dpc_snd_ne (fun h => by have := hd.2.1 h; simp at this)
    (h0s.trans h1s.symm)
  have hvbvd : vb ≠ vd := dpc_snd_ne (fun h => by have := hd.2.2.1 h; simp at this)
    (h0t.trans h1t.symm)
  -- the free crossing vertices
  have htrace_x : ((({va, vb, vc, vd} : Finset W)).filter
      (fun w => colH w = !(colH va))).card < 3 := by
    have hsub : (({va, vb, vc, vd} : Finset W)).filter (fun w => colH w = !(colH va)) ⊆
        {vc, vd} := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hw1, hw2⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
      rcases hw1 with rfl | rfl | rfl | rfl
      · exact absurd hw2 (by simp)
      · rw [← hcol0] at hw2
        exact absurd hw2 (by simp)
      · exact Or.inl rfl
      · exact Or.inr rfl
    calc _ ≤ ({vc, vd} : Finset W).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      _ < 3 := by omega
  obtain ⟨fx, hfxc, hfxa⟩ := dpc_spare_avoid (colH := colH) (!(colH va)) {va, vb, vc, vd}
    (lt_of_lt_of_le htrace_x (hclass3 _))
  have hfx4 : fx ≠ va ∧ fx ≠ vb ∧ fx ≠ vc ∧ fx ≠ vd := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hfxa (by rw [h]; simp)
  have htrace_w : ((insert fx ({va, vb, vc, vd} : Finset W)).filter
      (fun w => colH w = !(colH vc))).card < 3 := by
    by_cases hvv : colH va = colH vc
    · have hsub : ((insert fx ({va, vb, vc, vd} : Finset W)).filter
          (fun w => colH w = !(colH vc))) ⊆ {fx} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
        rcases hw1 with rfl | rfl | rfl | rfl | rfl
        · rfl
        · rw [hvv] at hw2
          exact absurd hw2 (by simp)
        · rw [← hcol0, hvv] at hw2
          exact absurd hw2 (by simp)
        · exact absurd hw2 (by simp)
        · rw [← hcol1] at hw2
          exact absurd hw2 (by simp)
      calc _ ≤ ({fx} : Finset W).card := Finset.card_le_card hsub
        _ < 3 := by simp
    · have hvv' : colH va = !(colH vc) := by
        cases h1 : colH va <;> cases h2 : colH vc <;> simp_all
      have hsub : ((insert fx ({va, vb, vc, vd} : Finset W)).filter
          (fun w => colH w = !(colH vc))) ⊆ {va, vb} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
        rcases hw1 with rfl | rfl | rfl | rfl | rfl
        · rw [hfxc, hvv'] at hw2
          exact absurd hw2 (by simp)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hw2 (by simp)
        · rw [← hcol1] at hw2
          exact absurd hw2 (by simp)
      calc _ ≤ ({va, vb} : Finset W).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
        _ < 3 := by omega
  obtain ⟨gw, hgwc, hgwa⟩ := dpc_spare_avoid (colH := colH) (!(colH vc))
    (insert fx {va, vb, vc, vd}) (lt_of_lt_of_le htrace_w (hclass3 _))
  have hgw5 : gw ≠ fx ∧ gw ≠ va ∧ gw ≠ vb ∧ gw ≠ vc ∧ gw ≠ vd := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hgwa (by rw [h]; simp)
  -- the two H-demands
  have hbne : ∀ b : Bool, b ≠ !b := by decide
  have hd0 : OppositeDemand colH ![va, vc] ![fx, gw] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · show colH va ≠ colH fx
        rw [hfxc]
        exact hbne _
      · show colH vc ≠ colH gw
        rw [hgwc]
        exact hbne _
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : va = vc) hvavc
      · exact absurd (hab : vc = va) (Ne.symm hvavc)
      · rfl
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : fx = gw) (Ne.symm hgw5.1)
      · exact absurd (hab : gw = fx) hgw5.1
      · rfl
    · intro a b
      fin_cases a <;> fin_cases b
      · exact fun h => hfx4.1 h.symm
      · exact fun h => hgw5.2.1 h.symm
      · exact fun h => hfx4.2.2.1 h.symm
      · exact fun h => hgw5.2.2.2.1 h.symm
  have hd1 : OppositeDemand colH ![fx, gw] ![vb, vd] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · show colH fx ≠ colH vb
        rw [hfxc, hcol0]
        exact Ne.symm (hbne _)
      · show colH gw ≠ colH vd
        rw [hgwc, hcol1]
        exact Ne.symm (hbne _)
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : fx = gw) (Ne.symm hgw5.1)
      · exact absurd (hab : gw = fx) hgw5.1
      · rfl
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : vb = vd) hvbvd
      · exact absurd (hab : vd = vb) (Ne.symm hvbvd)
      · rfl
    · intro a b
      fin_cases a <;> fin_cases b
      · exact hfx4.2.1
      · exact hfx4.2.2.2
      · exact hgw5.2.2.1
      · exact hgw5.2.2.2.2
  obtain ⟨p, hpP, hpC, hpD⟩ := h2dpc ![va, vc] ![fx, gw] hd0
  obtain ⟨q, hqP, hqC, hqD⟩ := h2dpc ![fx, gw] ![vb, vd] hd1
  obtain ⟨R0, hR0p, hR0s⟩ := dpc_cross_splice hA (p 0) (q 0) (hpP 0) (hqP 0)
  obtain ⟨R1, hR1p, hR1s⟩ := dpc_cross_splice hA (p 1) (q 1) (hpP 1) (hqP 1)
  have hεε' : ε ≠ ε' := A.ne_of_adj hA
  refine ⟨fun i => if h : i = 0 then
      (R0.copy (Prod.ext h0s.symm hva.symm) (Prod.ext h0t.symm hvb.symm)).copy
        (congrArg s h.symm) (congrArg t h.symm)
    else
      (R1.copy (Prod.ext h1s.symm hvc.symm) (Prod.ext h1t.symm hvd.symm)).copy
        (congrArg s (dpc2_fin2 i h).symm) (congrArg t (dpc2_fin2 i h).symm), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0 <;> [rw [dif_pos h]; rw [dif_neg h]] <;>
      simp only [SimpleGraph.Walk.isPath_copy]
    · exact hR0p
    · exact hR1p
  · intro x
    rcases hE2 x.1 with hx | hx
    · obtain ⟨i, hi⟩ := hpC x.2
      refine ⟨i, ?_⟩
      dsimp only
      by_cases h : i = 0
      · rw [dif_pos h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hR0s, List.mem_append]
        left
        rw [List.mem_map]
        subst h
        exact ⟨x.2, hi, by rw [← hx]⟩
      · rw [dif_neg h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hR1s, List.mem_append]
        left
        rw [List.mem_map]
        rw [dpc2_fin2 i h] at hi
        exact ⟨x.2, hi, by rw [← hx]⟩
    · obtain ⟨i, hi⟩ := hqC x.2
      refine ⟨i, ?_⟩
      dsimp only
      by_cases h : i = 0
      · rw [dif_pos h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hR0s, List.mem_append]
        right
        rw [List.mem_map]
        subst h
        exact ⟨x.2, hi, by rw [← hx]⟩
      · rw [dif_neg h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hR1s, List.mem_append]
        right
        rw [List.mem_map]
        rw [dpc2_fin2 i h] at hi
        exact ⟨x.2, hi, by rw [← hx]⟩
  · intro a b hab x hx
    dsimp only at hx
    have hmem : ∀ (j : Fin 2), x ∈ (if h : j = 0 then
        (R0.copy (Prod.ext h0s.symm hva.symm) (Prod.ext h0t.symm hvb.symm)).copy
          (congrArg s h.symm) (congrArg t h.symm)
      else
        (R1.copy (Prod.ext h1s.symm hvc.symm) (Prod.ext h1t.symm hvd.symm)).copy
          (congrArg s (dpc2_fin2 j h).symm) (congrArg t (dpc2_fin2 j h).symm)).support →
        (x.1 = ε ∧ x.2 ∈ (p j).support) ∨ (x.1 = ε' ∧ x.2 ∈ (q j).support) := by
      intro j hj
      by_cases h : j = 0
      · rw [dif_pos h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hR0s, List.mem_append] at hj
        subst h
        rcases hj with hj | hj <;> rw [List.mem_map] at hj <;>
          obtain ⟨w, hw, rfl⟩ := hj
        · exact Or.inl ⟨rfl, hw⟩
        · exact Or.inr ⟨rfl, hw⟩
      · rw [dif_neg h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hR1s, List.mem_append] at hj
        rw [dpc2_fin2 j h]
        rcases hj with hj | hj <;> rw [List.mem_map] at hj <;>
          obtain ⟨w, hw, rfl⟩ := hj
        · exact Or.inl ⟨rfl, hw⟩
        · exact Or.inr ⟨rfl, hw⟩
    rcases hmem a hx.1 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases hmem b hx.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact hpD a b hab x.2 ⟨ha2, hb2⟩
    · exact hεε' (ha1.symm.trans hb1)
    · exact hεε' (hb1.symm.trans ha1)
    · exact hqD a b hab x.2 ⟨ha2, hb2⟩

/-- Case C: pair 0 internal to the `ε`-layer, pair 1 split with source in `ε`. -/
theorem dpc_caseC {ε ε' : E} (hA : A.Adj ε ε') (hE2 : ∀ e : E, e = ε ∨ e = ε')
    (hlace : IsHamLaceable H colH)
    (h2dpc : IsPairedKDPCForOpposite H colH 2)
    (hclass2 : ∀ c, 2 ≤ (Finset.univ.filter (fun w => colH w = c)).card)
    (hcolA : colA ε ≠ colA ε')
    {s t : Fin 2 → E × W} (hd : OppositeDemand (dpcColP colA colH) s t)
    (h0s : (s 0).1 = ε) (h0t : (t 0).1 = ε) (h1s : (s 1).1 = ε) (h1t : (t 1).1 = ε') :
    IsPairedDPC (A □ H) 2 s t := by
  classical
  set va := (s 0).2 with hva
  set vb := (t 0).2 with hvb
  set vc := (s 1).2 with hvc
  set vd := (t 1).2 with hvd
  have hbne : ∀ b : Bool, b ≠ !b := by decide
  have hcol0 : colH va ≠ colH vb := by
    have h := hd.1 0
    unfold dpcColP at h
    rw [h0s, h0t] at h
    exact (dpc_xor_ne_of_eq _ _ _).mp h
  have hcol1 : colH vc = colH vd := by
    have h := hd.1 1
    unfold dpcColP at h
    rw [h1s, h1t] at h
    exact (dpc_xor_ne_of_ne _ _ _ _ hcolA).mp h
  have hvavb : va ≠ vb := fun h => hcol0 (congrArg colH h)
  have hvavc : va ≠ vc := dpc_snd_ne (fun h => by have := hd.2.1 h; simp at this)
    (h0s.trans h1s.symm)
  have hvbvc : vb ≠ vc := dpc_snd_ne (fun h => (hd.2.2.2 1 0) h.symm)
    (h0t.trans h1s.symm)
  -- the free exit vertex
  have htrace : ((({va, vb, vc} : Finset W)).filter
      (fun w => colH w = !(colH vc))).card < 2 := by
    by_cases hcase : colH va = !(colH vc)
    · have hsub : (({va, vb, vc} : Finset W)).filter (fun w => colH w = !(colH vc)) ⊆
          {va} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
        rcases hw1 with rfl | rfl | rfl
        · rfl
        · exfalso
          apply hcol0
          rw [hcase, hw2]
        · exact absurd hw2 (hbne _)
      calc _ ≤ ({va} : Finset W).card := Finset.card_le_card hsub
        _ < 2 := by simp
    · have hsub : (({va, vb, vc} : Finset W)).filter (fun w => colH w = !(colH vc)) ⊆
          {vb} := by
        intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 ⊢
        rcases hw1 with rfl | rfl | rfl
        · exact absurd hw2 hcase
        · rfl
        · exact absurd hw2 (hbne _)
      calc _ ≤ ({vb} : Finset W).card := Finset.card_le_card hsub
        _ < 2 := by simp
  obtain ⟨y, hyc, hya⟩ := dpc_spare_avoid (colH := colH) (!(colH vc)) {va, vb, vc}
    (lt_of_lt_of_le htrace (hclass2 _))
  have hy3 : y ≠ va ∧ y ≠ vb ∧ y ≠ vc := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact hya (by rw [h]; simp)
  -- the ε-layer cover
  have hd0 : OppositeDemand colH ![va, vc] ![vb, y] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hcol0
      · show colH vc ≠ colH y
        rw [hyc]
        exact hbne _
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : va = vc) hvavc
      · exact absurd (hab : vc = va) (Ne.symm hvavc)
      · rfl
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : vb = y) (Ne.symm hy3.2.1)
      · exact absurd (hab : y = vb) hy3.2.1
      · rfl
    · intro a b
      fin_cases a <;> fin_cases b
      · exact hvavb
      · exact fun h => hy3.1 h.symm
      · exact Ne.symm hvbvc
      · exact fun h => hy3.2.2 h.symm
  obtain ⟨p, hpP, hpC, hpD⟩ := h2dpc ![va, vc] ![vb, y] hd0
  -- the ε'-layer Hamilton path
  have hyvd : colH y ≠ colH vd := by
    rw [hyc, ← hcol1]
    exact Ne.symm (hbne _)
  obtain ⟨ham, hham⟩ := hlace y vd hyvd
  obtain ⟨R1, hR1p, hR1s⟩ := dpc_cross_splice hA (p 1) ham (hpP 1) hham.isPath
  have hεε' : ε ≠ ε' := A.ne_of_adj hA
  refine ⟨fun i => if h : i = 0 then
      (((p 0).map (dpcLift A H ε)).copy (Prod.ext h0s.symm hva.symm)
        (Prod.ext h0t.symm hvb.symm)).copy (congrArg s h.symm) (congrArg t h.symm)
    else
      (R1.copy (Prod.ext h1s.symm hvc.symm) (Prod.ext h1t.symm hvd.symm)).copy
        (congrArg s (dpc2_fin2 i h).symm) (congrArg t (dpc2_fin2 i h).symm), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0 <;> [rw [dif_pos h]; rw [dif_neg h]] <;>
      simp only [SimpleGraph.Walk.isPath_copy]
    · exact SimpleGraph.Walk.map_isPath_of_injective (dpcLift_inj ε) (hpP 0)
    · exact hR1p
  · intro x
    rcases hE2 x.1 with hx | hx
    · obtain ⟨i, hi⟩ := hpC x.2
      refine ⟨i, ?_⟩
      dsimp only
      by_cases h : i = 0
      · rw [dif_pos h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [dpcLift_mem_support]
        subst h
        exact ⟨hx, hi⟩
      · rw [dif_neg h]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hR1s, List.mem_append]
        left
        rw [List.mem_map]
        rw [dpc2_fin2 i h] at hi
        exact ⟨x.2, hi, by rw [← hx]⟩
    · refine ⟨1, ?_⟩
      dsimp only
      rw [dif_neg (by decide : (1 : Fin 2) ≠ 0)]
      simp only [SimpleGraph.Walk.support_copy]
      rw [hR1s, List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨x.2, hham.mem_support x.2, by rw [← hx]⟩
  · intro a b hab x hx
    dsimp only at hx
    have hmem : ∀ (j : Fin 2), x ∈ (if h : j = 0 then
        (((p 0).map (dpcLift A H ε)).copy (Prod.ext h0s.symm hva.symm)
          (Prod.ext h0t.symm hvb.symm)).copy (congrArg s h.symm) (congrArg t h.symm)
      else
        (R1.copy (Prod.ext h1s.symm hvc.symm) (Prod.ext h1t.symm hvd.symm)).copy
          (congrArg s (dpc2_fin2 j h).symm) (congrArg t (dpc2_fin2 j h).symm)).support →
        (j = 0 ∧ x.1 = ε ∧ x.2 ∈ (p 0).support) ∨
        (j = 1 ∧ ((x.1 = ε ∧ x.2 ∈ (p 1).support) ∨ (x.1 = ε' ∧ x.2 ∈ ham.support))) := by
      intro j hj
      by_cases h : j = 0
      · rw [dif_pos h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [dpcLift_mem_support] at hj
        exact Or.inl ⟨h, hj⟩
      · rw [dif_neg h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hR1s, List.mem_append] at hj
        refine Or.inr ⟨dpc2_fin2 j h, ?_⟩
        rcases hj with hj | hj <;> rw [List.mem_map] at hj <;>
          obtain ⟨w, hw, rfl⟩ := hj
        · exact Or.inl ⟨rfl, hw⟩
        · exact Or.inr ⟨rfl, hw⟩
    rcases hmem a hx.1 with ⟨ha0, ha1, ha2⟩ | ⟨ha0, hcase_a⟩ <;>
      rcases hmem b hx.2 with ⟨hb0, hb1, hb2⟩ | ⟨hb0, hcase_b⟩
    · exact hab (ha0.trans hb0.symm)
    · rcases hcase_b with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · exact hpD 0 1 (by decide) x.2 ⟨ha2, hb2⟩
      · exact hεε' (ha1.symm.trans hb1)
    · rcases hcase_a with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
      · exact hpD 1 0 (by decide) x.2 ⟨ha2, hb2⟩
      · exact hεε' (hb1.symm.trans ha1)
    · exact hab (ha0.trans hb0.symm)

/-- Case A: both pairs internal to the same `ε`-layer — cover the layer, detour the first
    edge of the first path through the other layer's Hamilton path. -/
theorem dpc_caseA {ε ε' : E} (hA : A.Adj ε ε') (hE2 : ∀ e : E, e = ε ∨ e = ε')
    (hHbip : ∀ u v, H.Adj u v → colH u ≠ colH v)
    (hlace : IsHamLaceable H colH)
    (h2dpc : IsPairedKDPCForOpposite H colH 2)
    {s t : Fin 2 → E × W} (hd : OppositeDemand (dpcColP colA colH) s t)
    (h0s : (s 0).1 = ε) (h0t : (t 0).1 = ε) (h1s : (s 1).1 = ε) (h1t : (t 1).1 = ε) :
    IsPairedDPC (A □ H) 2 s t := by
  classical
  set va := (s 0).2 with hva
  set vb := (t 0).2 with hvb
  set vc := (s 1).2 with hvc
  set vd := (t 1).2 with hvd
  have hcol0 : colH va ≠ colH vb := by
    have h := hd.1 0
    unfold dpcColP at h
    rw [h0s, h0t] at h
    exact (dpc_xor_ne_of_eq _ _ _).mp h
  have hcol1 : colH vc ≠ colH vd := by
    have h := hd.1 1
    unfold dpcColP at h
    rw [h1s, h1t] at h
    exact (dpc_xor_ne_of_eq _ _ _).mp h
  have hvavb : va ≠ vb := fun h => hcol0 (congrArg colH h)
  have hvcvd : vc ≠ vd := fun h => hcol1 (congrArg colH h)
  have hvavc : va ≠ vc := dpc_snd_ne (fun h => by have := hd.2.1 h; simp at this)
    (h0s.trans h1s.symm)
  have hvbvd : vb ≠ vd := dpc_snd_ne (fun h => by have := hd.2.2.1 h; simp at this)
    (h0t.trans h1t.symm)
  have hvavd : va ≠ vd := dpc_snd_ne (fun h => (hd.2.2.2 0 1) h) (h0s.trans h1t.symm)
  have hvcvb : vc ≠ vb := dpc_snd_ne (fun h => (hd.2.2.2 1 0) h) (h1s.trans h0t.symm)
  have hd0 : OppositeDemand colH ![va, vc] ![vb, vd] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hcol0
      · exact hcol1
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : va = vc) hvavc
      · exact absurd (hab : vc = va) (Ne.symm hvavc)
      · rfl
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (hab : vb = vd) hvbvd
      · exact absurd (hab : vd = vb) (Ne.symm hvbvd)
      · rfl
    · intro a b
      fin_cases a <;> fin_cases b
      · exact hvavb
      · exact hvavd
      · exact hvcvb
      · exact hvcvd
  obtain ⟨p, hpP, hpC, hpD⟩ := h2dpc ![va, vc] ![vb, vd] hd0
  -- detour the first edge of the first path
  obtain ⟨u, hadj_u, rest, hp0eq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hvavb (p 0)
  have hrest : rest.IsPath ∧ va ∉ rest.support := by
    have h := hpP 0
    rw [hp0eq] at h
    exact (SimpleGraph.Walk.cons_isPath_iff hadj_u rest).mp h
  have hp0supp : (p 0).support = va :: rest.support := by
    rw [hp0eq]
    exact SimpleGraph.Walk.support_cons _ _
  obtain ⟨ham, hham⟩ := hlace va u (hHbip va u hadj_u)
  obtain ⟨R, hRp, hRs⟩ := dpc_cross_splice hA.symm ham rest hham.isPath hrest.1
  have hεε' : ε ≠ ε' := A.ne_of_adj hA
  have hheadR : (ε, va) ∉ R.support := by
    rw [hRs, List.mem_append]
    rintro (h | h) <;> rw [List.mem_map] at h <;> obtain ⟨w, hw, hweq⟩ := h
    · exact hεε' (congrArg Prod.fst hweq).symm
    · have hwva : w = va := congrArg Prod.snd hweq
      exact hrest.2 (hwva ▸ hw)
  set P0 : (A □ H).Walk (ε, va) (ε, vb) :=
    SimpleGraph.Walk.cons (dpc_vertical_adj hA va) R with hP0
  have hP0p : P0.IsPath := by
    rw [hP0, SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hRp, hheadR⟩
  have hP0s : P0.support = (ε, va) :: R.support := by
    rw [hP0, SimpleGraph.Walk.support_cons]
  refine ⟨fun i => if h : i = 0 then
      (P0.copy (Prod.ext h0s.symm hva.symm) (Prod.ext h0t.symm hvb.symm)).copy
        (congrArg s h.symm) (congrArg t h.symm)
    else
      (((p 1).map (dpcLift A H ε)).copy (Prod.ext h1s.symm hvc.symm)
        (Prod.ext h1t.symm hvd.symm)).copy
        (congrArg s (dpc2_fin2 i h).symm) (congrArg t (dpc2_fin2 i h).symm), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0 <;> [rw [dif_pos h]; rw [dif_neg h]] <;>
      simp only [SimpleGraph.Walk.isPath_copy]
    · exact hP0p
    · exact SimpleGraph.Walk.map_isPath_of_injective (dpcLift_inj ε) (hpP 1)
  · intro x
    rcases hE2 x.1 with hx | hx
    · obtain ⟨i, hi⟩ := hpC x.2
      by_cases h : i = 0
      · subst h
        rw [hp0supp, List.mem_cons] at hi
        refine ⟨0, ?_⟩
        dsimp only
        rw [dif_pos rfl]
        simp only [SimpleGraph.Walk.support_copy]
        rw [hP0s, List.mem_cons]
        rcases hi with hi | hi
        · left
          exact Prod.ext hx (by rw [hi])
        · right
          rw [hRs, List.mem_append]
          right
          rw [List.mem_map]
          exact ⟨x.2, hi, by rw [← hx]⟩
      · refine ⟨1, ?_⟩
        dsimp only
        rw [dif_neg (by decide : (1 : Fin 2) ≠ 0)]
        simp only [SimpleGraph.Walk.support_copy]
        rw [dpcLift_mem_support]
        rw [dpc2_fin2 i h] at hi
        exact ⟨hx, hi⟩
    · refine ⟨0, ?_⟩
      dsimp only
      rw [dif_pos rfl]
      simp only [SimpleGraph.Walk.support_copy]
      rw [hP0s, List.mem_cons]
      right
      rw [hRs, List.mem_append]
      left
      rw [List.mem_map]
      exact ⟨x.2, hham.mem_support x.2, by rw [← hx]⟩
  · intro a b hab x hx
    dsimp only at hx
    have hmem : ∀ (j : Fin 2), x ∈ (if h : j = 0 then
        (P0.copy (Prod.ext h0s.symm hva.symm) (Prod.ext h0t.symm hvb.symm)).copy
          (congrArg s h.symm) (congrArg t h.symm)
      else
        (((p 1).map (dpcLift A H ε)).copy (Prod.ext h1s.symm hvc.symm)
          (Prod.ext h1t.symm hvd.symm)).copy
          (congrArg s (dpc2_fin2 j h).symm) (congrArg t (dpc2_fin2 j h).symm)).support →
        (j = 0 ∧ ((x.1 = ε ∧ x.2 ∈ (p 0).support) ∨ (x.1 = ε' ∧ x.2 ∈ ham.support))) ∨
        (j = 1 ∧ x.1 = ε ∧ x.2 ∈ (p 1).support) := by
      intro j hj
      by_cases h : j = 0
      · rw [dif_pos h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hP0s, List.mem_cons] at hj
        refine Or.inl ⟨h, ?_⟩
        rcases hj with hj | hj
        · left
          refine ⟨(congrArg Prod.fst hj : x.1 = ε), ?_⟩
          rw [hp0supp, List.mem_cons]
          left
          have h2 : x.2 = (ε, va).2 := congrArg Prod.snd hj
          exact h2
        · rw [hRs, List.mem_append] at hj
          rcases hj with hj | hj <;> rw [List.mem_map] at hj <;>
            obtain ⟨w, hw, rfl⟩ := hj
          · exact Or.inr ⟨rfl, hw⟩
          · refine Or.inl ⟨rfl, ?_⟩
            rw [hp0supp, List.mem_cons]
            right
            exact hw
      · rw [dif_neg h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [dpcLift_mem_support] at hj
        exact Or.inr ⟨dpc2_fin2 j h, hj⟩
    rcases hmem a hx.1 with ⟨ha0, hcase_a⟩ | ⟨ha0, ha1, ha2⟩ <;>
      rcases hmem b hx.2 with ⟨hb0, hcase_b⟩ | ⟨hb0, hb1, hb2⟩
    · exact hab (ha0.trans hb0.symm)
    · rcases hcase_a with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
      · exact hpD 0 1 (by decide) x.2 ⟨ha2, hb2⟩
      · exact hεε' (hb1.symm.trans ha1)
    · rcases hcase_b with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · exact hpD 1 0 (by decide) x.2 ⟨ha2, hb2⟩
      · exact hεε' (ha1.symm.trans hb1)
    · exact hab (ha0.trans hb0.symm)

end Cases2

/-! ## Demand transforms -/

section Transforms

variable {V' : Type u} [DecidableEq V'] [Fintype V']

/-- Reindexing a legal demand stays legal. -/
theorem oppositeDemand_reindex {colP : V' → Bool} {k : ℕ} {s t : Fin k → V'}
    (σ : Equiv.Perm (Fin k)) (hd : OppositeDemand colP s t) :
    OppositeDemand colP (s ∘ σ) (t ∘ σ) := by
  refine ⟨fun i => hd.1 (σ i), ?_, ?_, fun i j => hd.2.2.2 (σ i) (σ j)⟩
  · intro a b hab
    exact σ.injective (hd.2.1 hab)
  · intro a b hab
    exact σ.injective (hd.2.2.1 hab)

/-- Reversing one pair of a legal demand stays legal. -/
theorem oppositeDemand_reverse_pair {colP : V' → Bool} {k : ℕ} {s t : Fin k → V'}
    (i₀ : Fin k) (hd : OppositeDemand colP s t) :
    OppositeDemand colP (Function.update s i₀ (t i₀)) (Function.update t i₀ (s i₀)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = i₀
    · rw [h, Function.update_self, Function.update_self]
      exact (hd.1 i₀).symm
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact hd.1 i
  · intro a b hab
    by_cases ha : a = i₀ <;> by_cases hb : b = i₀
    · rw [ha, hb]
    · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab.symm (hd.2.2.2 b i₀)
    · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab (hd.2.2.2 a i₀)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact hd.2.1 hab
  · intro a b hab
    by_cases ha : a = i₀ <;> by_cases hb : b = i₀
    · rw [ha, hb]
    · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab (hd.2.2.2 i₀ b)
    · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab.symm (hd.2.2.2 i₀ a)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact hd.2.2.1 hab
  · intro a b
    by_cases ha : a = i₀ <;> by_cases hb : b = i₀
    · rw [ha, hb, Function.update_self, Function.update_self]
      exact fun h => (hd.2.2.2 i₀ i₀) h.symm
    · rw [ha, Function.update_self, Function.update_of_ne hb]
      intro h
      exact hb (hd.2.2.1 h).symm
    · rw [hb, Function.update_self, Function.update_of_ne ha]
      intro h
      exact ha (hd.2.1 h)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb]
      exact hd.2.2.2 a b

end Transforms

/-! ## The Q₃ special case: both pairs split over `CT₂ □ Q₂`

Here the generic case B fails (color classes of `Q₂` have only two members), but `Q₂ = K₂,₂`
is complete bipartite, so explicit covers exist in every configuration. -/

section Q3

private abbrev VQ2 := CTProductVertex [2, 2]
private abbrev Q2 := CTProductGraph [2, 2]
private abbrev colQ2 := CTProductColor [2, 2]

/-- Class exhaustion on the four vertices of `Q₂`. -/
private theorem q2_exhaust : ∀ v m c₁ c₂ : VQ2, colQ2 v ≠ colQ2 c₁ → colQ2 m = colQ2 v →
    colQ2 c₂ = colQ2 c₁ → v ≠ m → c₁ ≠ c₂ → ∀ z : VQ2, z = v ∨ z = m ∨ z = c₁ ∨ z = c₂ := by
  decide

/-- Same-class pairs exhaust their class. -/
private theorem q2_class_pair : ∀ v w z : VQ2, colQ2 v = colQ2 w → v ≠ w →
    colQ2 z = colQ2 v → z = v ∨ z = w := by decide

/-- Every vertex has a same-class partner. -/
private theorem q2_partner : ∀ v : VQ2, ∃ w, colQ2 w = colQ2 v ∧ w ≠ v := by decide

/-- Every vertex has an opposite-class vertex. -/
private theorem q2_opp_exists : ∀ v : VQ2, ∃ c, colQ2 c ≠ colQ2 v := by decide

/-- Walks from explicit four-vertex alternating lists. -/
private theorem q3_walk4 {E : Type u} [DecidableEq E] [Fintype E]
    {A : SimpleGraph E} {x₁ x₂ x₃ x₄ : E × VQ2}
    (h₁ : (A □ Q2).Adj x₁ x₂) (h₂ : (A □ Q2).Adj x₂ x₃) (h₃ : (A □ Q2).Adj x₃ x₄)
    (hne : x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄) :
    ∃ P : (A □ Q2).Walk x₁ x₄, P.IsPath ∧ P.support = [x₁, x₂, x₃, x₄] := by
  refine ⟨SimpleGraph.Walk.cons h₁ (SimpleGraph.Walk.cons h₂
    (SimpleGraph.Walk.cons h₃ SimpleGraph.Walk.nil)), ?_, by simp⟩
  apply SimpleGraph.Walk.IsPath.mk'
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rintro (h | h | h)
    · exact hne.1 h
    · exact hne.2.1 h
    · exact hne.2.2.1 h
  · rintro (h | h)
    · exact hne.2.2.2.1 h
    · exact hne.2.2.2.2.1 h
  · exact ⟨hne.2.2.2.2.2, not_false⟩

/-- Walks from explicit six-vertex lists. -/
private theorem q3_walk6 {E : Type u} [DecidableEq E] [Fintype E]
    {A : SimpleGraph E} {x₁ x₂ x₃ x₄ x₅ x₆ : E × VQ2}
    (h₁ : (A □ Q2).Adj x₁ x₂) (h₂ : (A □ Q2).Adj x₂ x₃) (h₃ : (A □ Q2).Adj x₃ x₄)
    (h₄ : (A □ Q2).Adj x₄ x₅) (h₅ : (A □ Q2).Adj x₅ x₆)
    (hnodup : ([x₁, x₂, x₃, x₄, x₅, x₆] : List (E × VQ2)).Nodup) :
    ∃ P : (A □ Q2).Walk x₁ x₆, P.IsPath ∧ P.support = [x₁, x₂, x₃, x₄, x₅, x₆] := by
  refine ⟨SimpleGraph.Walk.cons h₁ (SimpleGraph.Walk.cons h₂ (SimpleGraph.Walk.cons h₃
    (SimpleGraph.Walk.cons h₄ (SimpleGraph.Walk.cons h₅ SimpleGraph.Walk.nil)))), ?_, by simp⟩
  apply SimpleGraph.Walk.IsPath.mk'
  simpa using hnodup

/-- The two-vertex walk (a single edge). -/
private theorem q3_walk2 {E : Type u} [DecidableEq E] [Fintype E]
    {A : SimpleGraph E} {x₁ x₂ : E × VQ2} (h : (A □ Q2).Adj x₁ x₂) :
    ∃ P : (A □ Q2).Walk x₁ x₂, P.IsPath ∧ P.support = [x₁, x₂] := by
  exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil, dpc_edge_path h, by simp⟩

end Q3

section Q3B

/-- The finishing combinator for the Q₃ constructions. -/
private theorem q3_finish {ε ε' : Equiv.Perm (Fin 2)}
    {s t : Fin 2 → Equiv.Perm (Fin 2) × VQ2}
    (h0s : (s 0).1 = ε) (h1s : (s 1).1 = ε) (h0t : (t 0).1 = ε') (h1t : (t 1).1 = ε')
    {va vb vc vd : VQ2} (hva : va = (s 0).2) (hvb : vb = (t 0).2)
    (hvc : vc = (s 1).2) (hvd : vd = (t 1).2)
    {L₀ L₁ : List (Equiv.Perm (Fin 2) × VQ2)}
    (P₀ : (CompleteTranspositionGraph 2 □ Q2).Walk (ε, va) (ε', vb))
    (P₁ : (CompleteTranspositionGraph 2 □ Q2).Walk (ε, vc) (ε', vd))
    (hP₀ : P₀.IsPath) (hP₁ : P₁.IsPath) (hs₀ : P₀.support = L₀) (hs₁ : P₁.support = L₁)
    (hcov : ∀ x, x ∈ L₀ ∨ x ∈ L₁) (hdis : ∀ x, ¬ (x ∈ L₀ ∧ x ∈ L₁)) :
    IsPairedDPC (CompleteTranspositionGraph 2 □ Q2) 2 s t := by
  classical
  refine ⟨fun i => if h : i = 0 then
      (P₀.copy (Prod.ext h0s.symm hva) (Prod.ext h0t.symm hvb)).copy
        (congrArg s h.symm) (congrArg t h.symm)
    else
      (P₁.copy (Prod.ext h1s.symm hvc) (Prod.ext h1t.symm hvd)).copy
        (congrArg s (dpc2_fin2 i h).symm) (congrArg t (dpc2_fin2 i h).symm), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0 <;> [rw [dif_pos h]; rw [dif_neg h]] <;>
      simp only [SimpleGraph.Walk.isPath_copy]
    · exact hP₀
    · exact hP₁
  · intro x
    rcases hcov x with hx | hx
    · refine ⟨0, ?_⟩
      dsimp only
      rw [dif_pos rfl]
      simp only [SimpleGraph.Walk.support_copy]
      rw [hs₀]
      exact hx
    · refine ⟨1, ?_⟩
      dsimp only
      rw [dif_neg (by decide : (1 : Fin 2) ≠ 0)]
      simp only [SimpleGraph.Walk.support_copy]
      rw [hs₁]
      exact hx
  · intro a b hab x hx
    dsimp only at hx
    have hget : ∀ (j : Fin 2), x ∈ (if h : j = 0 then
        (P₀.copy (Prod.ext h0s.symm hva) (Prod.ext h0t.symm hvb)).copy
          (congrArg s h.symm) (congrArg t h.symm)
      else
        (P₁.copy (Prod.ext h1s.symm hvc) (Prod.ext h1t.symm hvd)).copy
          (congrArg s (dpc2_fin2 j h).symm) (congrArg t (dpc2_fin2 j h).symm)).support →
        (j = 0 ∧ x ∈ L₀) ∨ (j = 1 ∧ x ∈ L₁) := by
      intro j hj
      by_cases h : j = 0
      · rw [dif_pos h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hs₀] at hj
        exact Or.inl ⟨h, hj⟩
      · rw [dif_neg h] at hj
        simp only [SimpleGraph.Walk.support_copy] at hj
        rw [hs₁] at hj
        exact Or.inr ⟨dpc2_fin2 j h, hj⟩
    rcases hget a hx.1 with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩ <;>
      rcases hget b hx.2 with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · exact hab (ha0.trans hb0.symm)
    · exact hdis x ⟨ha1, hb1⟩
    · exact hdis x ⟨hb1, ha1⟩
    · exact hab (ha0.trans hb0.symm)

set_option maxHeartbeats 3200000 in
/-- The Q₃ both-pairs-split case: explicit covers, powered by the complete-bipartite
    structure of `Q₂`. -/
theorem dpc_q3_caseB {ε ε' : Equiv.Perm (Fin 2)}
    (hA : (CompleteTranspositionGraph 2).Adj ε ε') (hE2 : ∀ e, e = ε ∨ e = ε')
    (hcolA : CompleteTranspositionColor 2 ε ≠ CompleteTranspositionColor 2 ε')
    {s t : Fin 2 → Equiv.Perm (Fin 2) × VQ2}
    (hd : OppositeDemand (dpcColP (CompleteTranspositionColor 2) colQ2) s t)
    (h0s : (s 0).1 = ε) (h1s : (s 1).1 = ε) (h0t : (t 0).1 = ε') (h1t : (t 1).1 = ε') :
    IsPairedDPC (CompleteTranspositionGraph 2 □ Q2) 2 s t := by
  classical
  set va := (s 0).2 with hva
  set vb := (t 0).2 with hvb
  set vc := (s 1).2 with hvc
  set vd := (t 1).2 with hvd
  have hεε' : ε ≠ ε' := (CompleteTranspositionGraph 2).ne_of_adj hA
  have hbne : ∀ b : Bool, b ≠ !b := by decide
  have hcol0 : colQ2 va = colQ2 vb := by
    have h := hd.1 0
    unfold dpcColP at h
    rw [h0s, h0t] at h
    exact (dpc_xor_ne_of_ne _ _ _ _ hcolA).mp h
  have hcol1 : colQ2 vc = colQ2 vd := by
    have h := hd.1 1
    unfold dpcColP at h
    rw [h1s, h1t] at h
    exact (dpc_xor_ne_of_ne _ _ _ _ hcolA).mp h
  have hvavc : va ≠ vc := dpc_snd_ne (fun h => by have := hd.2.1 h; simp at this)
    (h0s.trans h1s.symm)
  have hvbvd : vb ≠ vd := dpc_snd_ne (fun h => by have := hd.2.2.1 h; simp at this)
    (h0t.trans h1t.symm)
  -- adjacency inside a layer, and vertical adjacencies
  have hin : ∀ (e : Equiv.Perm (Fin 2)) (w w' : VQ2), colQ2 w ≠ colQ2 w' →
      (CompleteTranspositionGraph 2 □ Q2).Adj (e, w) (e, w') := by
    intro e w w' hne
    exact SimpleGraph.boxProd_adj.mpr (Or.inr ⟨q2_opposite_adj w w' hne, rfl⟩)
  have hver : ∀ w, (CompleteTranspositionGraph 2 □ Q2).Adj (ε, w) (ε', w) :=
    fun w => dpc_vertical_adj hA w
  have hver' : ∀ w, (CompleteTranspositionGraph 2 □ Q2).Adj (ε', w) (ε, w) :=
    fun w => dpc_vertical_adj hA.symm w
  have hfstne : ∀ (w w' : VQ2), ((ε, w) : _ × VQ2) ≠ (ε', w') :=
    fun w w' h => hεε' (congrArg Prod.fst h)
  have hsndne : ∀ (e : Equiv.Perm (Fin 2)) {w w' : VQ2}, w ≠ w' →
      ((e, w) : _ × VQ2) ≠ (e, w') := by
    intro e w w' h hh
    exact h (congrArg Prod.snd hh)
  by_cases hby : colQ2 va = colQ2 vc
  · -- (II): all four projections lie in one class, which is exactly {va, vc}
    obtain ⟨n₁, hn₁⟩ := q2_opp_exists va
    obtain ⟨n₂, hn₂c, hn₂n⟩ := q2_partner n₁
    have hvb_mem : vb = va ∨ vb = vc := q2_class_pair va vc vb hby hvavc hcol0.symm
    have hvd_mem : vd = va ∨ vd = vc := q2_class_pair va vc vd hby hvavc
      (hcol1.symm.trans hby.symm)
    have hpair : (vb = va ∧ vd = vc) ∨ (vb = vc ∧ vd = va) := by
      rcases hvb_mem with h1 | h1 <;> rcases hvd_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) hvbvd
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hvbvd
    have hvan₁ : va ≠ n₁ := fun h => hn₁ (congrArg colQ2 h).symm
    have hvan₂ : va ≠ n₂ := fun h => hn₁ (hn₂c.symm.trans (congrArg colQ2 h).symm)
    have hvcn₁ : vc ≠ n₁ := fun h => hn₁ ((congrArg colQ2 h).symm.trans hby.symm)
    have hvcn₂ : vc ≠ n₂ := fun h =>
      hn₁ (hn₂c.symm.trans ((congrArg colQ2 h).symm.trans hby.symm))
    have hvbn₁ : vb ≠ n₁ := fun h => hn₁ ((congrArg colQ2 h.symm).trans hcol0.symm)
    have hvbn₂ : vb ≠ n₂ := fun h =>
      hn₁ (hn₂c.symm.trans ((congrArg colQ2 h.symm).trans hcol0.symm))
    have hvdn₁ : vd ≠ n₁ := fun h =>
      hn₁ ((congrArg colQ2 h.symm).trans (hcol1.symm.trans hby.symm))
    have hvdn₂ : vd ≠ n₂ := fun h =>
      hn₁ (hn₂c.symm.trans ((congrArg colQ2 h.symm).trans (hcol1.symm.trans hby.symm)))
    obtain ⟨P₀, hP₀p, hP₀s⟩ := q3_walk4 (A := CompleteTranspositionGraph 2)
      (x₁ := (ε, va)) (x₂ := (ε, n₁)) (x₃ := (ε', n₁)) (x₄ := (ε', vb))
      (hin ε va n₁ (fun h => hn₁ h.symm)) (hver n₁)
      (hin ε' n₁ vb (fun h => hn₁ (h.trans hcol0.symm)))
      ⟨hsndne ε hvan₁, hfstne va n₁, hfstne va vb,
        hfstne n₁ n₁, hfstne n₁ vb, hsndne ε' (Ne.symm hvbn₁)⟩
    obtain ⟨P₁, hP₁p, hP₁s⟩ := q3_walk4 (A := CompleteTranspositionGraph 2)
      (x₁ := (ε, vc)) (x₂ := (ε, n₂)) (x₃ := (ε', n₂)) (x₄ := (ε', vd))
      (hin ε vc n₂ (fun h => hn₁ (hn₂c.symm.trans (h.symm.trans hby.symm))))
      (hver n₂)
      (hin ε' n₂ vd (fun h => hn₁ (hn₂c.symm.trans (h.trans (hcol1.symm.trans hby.symm)))))
      ⟨hsndne ε hvcn₂, hfstne vc n₂, hfstne vc vd,
        hfstne n₂ n₂, hfstne n₂ vd, hsndne ε' (Ne.symm hvdn₂)⟩
    refine q3_finish h0s h1s h0t h1t hva hvb hvc hvd P₀ P₁ hP₀p hP₁p hP₀s hP₁s ?_ ?_
    · intro x
      obtain ⟨e, w⟩ := x
      rcases hpair with ⟨hb', hd'⟩ | ⟨hb', hd'⟩ <;>
        rcases hE2 e with rfl | rfl <;>
          rcases q2_exhaust va vc n₁ n₂ (Ne.symm hn₁) hby.symm hn₂c hvavc
            (Ne.symm hn₂n) w with rfl | rfl | rfl | rfl <;>
        simp [hb', hd']
    · intro x hx
      obtain ⟨h₀, h₁⟩ := hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀ h₁
      rcases h₀ with rfl | rfl | rfl | rfl <;> rcases h₁ with h₁ | h₁ | h₁ | h₁ <;>
        rw [Prod.mk.injEq] at h₁ <;>
        first
          | exact hεε' h₁.1
          | exact hεε' h₁.1.symm
          | exact hvavc h₁.2
          | exact hvan₂ h₁.2
          | exact hvcn₁ h₁.2.symm
          | exact hn₂n h₁.2.symm
          | exact hvdn₁ h₁.2.symm
          | exact hvbn₂ h₁.2
          | exact hvbvd h₁.2
  · -- (I): the two pairs project to different classes
    have hvbcol : colQ2 vb = colQ2 va := hcol0.symm
    have hvdcol : colQ2 vd = colQ2 vc := hcol1.symm
    have hvavd : va ≠ vd := fun h => hby ((congrArg colQ2 h).trans hvdcol)
    have hvcvb : vc ≠ vb := fun h => hby (hvbcol.symm.trans (congrArg colQ2 h).symm)
    by_cases hab : va = vb
    · by_cases hcd : vc = vd
      · -- (Ia1): pair 1 vertical, six-vertex snake for pair 0
        obtain ⟨m, hmc, hmne⟩ := q2_partner va
        obtain ⟨c₂, hc₂c, hc₂ne⟩ := q2_partner vc
        have hmvc : m ≠ vc := fun h => hby (hmc.symm.trans (congrArg colQ2 h))
        have hmc₂ : m ≠ c₂ := fun h => hby
          (hmc.symm.trans ((congrArg colQ2 h).trans hc₂c))
        have hvac₂ : va ≠ c₂ := fun h => hby ((congrArg colQ2 h).trans hc₂c)
        obtain ⟨P₀, hP₀p, hP₀s⟩ := q3_walk6 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, va)) (x₂ := (ε, c₂)) (x₃ := (ε, m))
          (x₄ := (ε', m)) (x₅ := (ε', c₂)) (x₆ := (ε', vb))
          (hin ε va c₂ (fun h => hby (h.trans hc₂c)))
          (hin ε c₂ m (fun h => hby (hmc.symm.trans (h.symm.trans hc₂c))))
          (hver m) (hin ε' m c₂ (fun h => hby (hmc.symm.trans (h.trans hc₂c))))
          (hin ε' c₂ vb (fun h => hby (hvbcol.symm.trans (h.symm.trans hc₂c))))
          (by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
              List.nodup_nil, and_true]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hvac₂ h2
              · exact hmne h2.symm
              · exact hεε' h1
              · exact hεε' h1
              · exact hεε' h1
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hmc₂ h2.symm
              · exact hεε' h1
              · exact hεε' h1
              · exact hεε' h1
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hεε' h1
              · exact hεε' h1
              · exact hεε' h1
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hmc₂ h2
              · exact hmne (h2.trans hab.symm)
            · refine ⟨?_, not_false⟩
              intro h
              simp only [Prod.mk.injEq] at h
              exact hvac₂ (h.2.trans hab.symm).symm
          )
        obtain ⟨P₁, hP₁p, hP₁s⟩ := q3_walk2 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, vc)) (x₂ := (ε', vd))
          (by rw [← hcd]; exact hver vc)
        refine q3_finish h0s h1s h0t h1t hva hvb hvc hvd P₀ P₁ hP₀p hP₁p hP₀s hP₁s ?_ ?_
        · intro x
          obtain ⟨e, w⟩ := x
          rcases hE2 e with rfl | rfl <;>
            rcases q2_exhaust va m vc c₂ hby hmc hc₂c (Ne.symm hmne) (Ne.symm hc₂ne) w with
              rfl | rfl | rfl | rfl <;>
            simp [← hab, ← hcd]
        · intro x hx
          obtain ⟨h₀, h₁⟩ := hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀ h₁
          rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h₁ with h₁ | h₁ <;>
            rw [Prod.mk.injEq] at h₁ <;>
            first
              | exact hεε' h₁.1
              | exact hεε' h₁.1.symm
              | exact hvavc h₁.2
              | exact hvavd h₁.2
              | exact hvbvd h₁.2
              | exact hmvc h₁.2
              | exact (fun hh : m = vd => hmvc (hh.trans hcd.symm)) h₁.2
              | exact hc₂ne h₁.2
              | exact hc₂ne h₁.2.symm
              | exact (fun hh : c₂ = vd => hc₂ne (hh.trans hcd.symm)) h₁.2
              | exact (fun hh : vb = vc => hvavc (hab.trans hh)) h₁.2
              | exact (fun hh : vb = vd => hvavd (hab.trans hh)) h₁.2
      · -- (Ia2): pair 0 vertical, three-crossing snake for pair 1
        obtain ⟨m, hmc, hmne⟩ := q2_partner va
        have hmvc : m ≠ vc := fun h => hby (hmc.symm.trans (congrArg colQ2 h))
        have hmvd : m ≠ vd := fun h =>
          hby (hmc.symm.trans ((congrArg colQ2 h).trans hvdcol))
        obtain ⟨P₀, hP₀p, hP₀s⟩ := q3_walk2 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, va)) (x₂ := (ε', vb))
          (by rw [← hab]; exact hver va)
        obtain ⟨P₁, hP₁p, hP₁s⟩ := q3_walk6 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, vc)) (x₂ := (ε', vc)) (x₃ := (ε', m))
          (x₄ := (ε, m)) (x₅ := (ε, vd)) (x₆ := (ε', vd))
          (hver vc) (hin ε' vc m (fun h => hby (hmc.symm.trans h.symm)))
          (hver' m) (hin ε m vd (fun h => hby (hmc.symm.trans (h.trans hvdcol))))
          (hver vd)
          (by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
              List.nodup_nil, and_true]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hεε' h1
              · exact hεε' h1
              · exact hmvc h2.symm
              · exact hcd h2
              · exact hεε' h1
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hmvc h2.symm
              · exact hεε' h1.symm
              · exact hεε' h1.symm
              · exact hcd h2
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hεε' h1.symm
              · exact hεε' h1.symm
              · exact hmvd h2
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hmvd h2
              · exact hεε' h1
            · refine ⟨?_, not_false⟩
              intro h
              simp only [Prod.mk.injEq] at h
              exact hεε' h.1
          )
        refine q3_finish h0s h1s h0t h1t hva hvb hvc hvd P₀ P₁ hP₀p hP₁p hP₀s hP₁s ?_ ?_
        · intro x
          obtain ⟨e, w⟩ := x
          rcases hE2 e with rfl | rfl <;>
            rcases q2_exhaust va m vc vd hby hmc hvdcol (Ne.symm hmne) hcd w with
              rfl | rfl | rfl | rfl <;>
            simp [← hab]
        · intro x hx
          obtain ⟨h₀, h₁⟩ := hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀ h₁
          rcases h₀ with rfl | rfl <;> rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
            rw [Prod.mk.injEq] at h₁ <;>
            first
              | exact hεε' h₁.1
              | exact hεε' h₁.1.symm
              | exact hvavc h₁.2
              | exact hmne h₁.2.symm
              | exact hvavd h₁.2
              | exact (fun hh : vb = vc => hvavc (hab.trans hh)) h₁.2
              | exact (fun hh : vb = m => hmne (hab.trans hh).symm) h₁.2
              | exact hvbvd h₁.2
    · by_cases hcd : vc = vd
      · -- (Ib2): pair 1 vertical, six-vertex snake for pair 0
        obtain ⟨c₂, hc₂c, hc₂ne⟩ := q2_partner vc
        have hvac₂ : va ≠ c₂ := fun h => hby ((congrArg colQ2 h).trans hc₂c)
        have hvbc₂ : vb ≠ c₂ := fun h => hby
          (hvbcol.symm.trans ((congrArg colQ2 h).trans hc₂c))
        obtain ⟨P₀, hP₀p, hP₀s⟩ := q3_walk6 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, va)) (x₂ := (ε', va)) (x₃ := (ε', c₂))
          (x₄ := (ε, c₂)) (x₅ := (ε, vb)) (x₆ := (ε', vb))
          (hver va) (hin ε' va c₂ (fun h => hby (h.trans hc₂c)))
          (hver' c₂)
          (hin ε c₂ vb (fun h => hby (hvbcol.symm.trans (h.symm.trans hc₂c))))
          (hver vb)
          (by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
              List.nodup_nil, and_true]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hεε' h1
              · exact hεε' h1
              · exact hvac₂ h2
              · exact hab h2
              · exact hεε' h1
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hvac₂ h2
              · exact hεε' h1.symm
              · exact hεε' h1.symm
              · exact hab h2
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hεε' h1.symm
              · exact hεε' h1.symm
              · exact hvbc₂ h2.symm
            · intro h
              simp only [Prod.mk.injEq] at h
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact hvbc₂ h2.symm
              · exact hεε' h1
            · refine ⟨?_, not_false⟩
              intro h
              simp only [Prod.mk.injEq] at h
              exact hεε' h.1
          )
        obtain ⟨P₁, hP₁p, hP₁s⟩ := q3_walk2 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, vc)) (x₂ := (ε', vd))
          (by rw [← hcd]; exact hver vc)
        refine q3_finish h0s h1s h0t h1t hva hvb hvc hvd P₀ P₁ hP₀p hP₁p hP₀s hP₁s ?_ ?_
        · intro x
          obtain ⟨e, w⟩ := x
          rcases hE2 e with rfl | rfl <;>
            rcases q2_exhaust va vb vc c₂ hby hvbcol hc₂c hab (Ne.symm hc₂ne) w with
              rfl | rfl | rfl | rfl <;>
            simp [← hcd]
        · intro x hx
          obtain ⟨h₀, h₁⟩ := hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀ h₁
          rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h₁ with h₁ | h₁ <;>
            rw [Prod.mk.injEq] at h₁ <;>
            first
              | exact hεε' h₁.1
              | exact hεε' h₁.1.symm
              | exact hvavc h₁.2
              | exact hvavd h₁.2
              | exact hvbvd h₁.2
              | exact hc₂ne h₁.2
              | exact hc₂ne h₁.2.symm
              | exact (fun hh : c₂ = vd => hc₂ne (hh.trans hcd.symm)) h₁.2
              | exact hvcvb h₁.2.symm
              | exact (fun hh : vb = vd => hvcvb (hh.trans hcd.symm).symm) h₁.2
      · -- (Ib1): two four-vertex covers
        obtain ⟨P₀, hP₀p, hP₀s⟩ := q3_walk4 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, va)) (x₂ := (ε', va)) (x₃ := (ε', vc)) (x₄ := (ε', vb))
          (hver va) (hin ε' va vc hby)
          (hin ε' vc vb (fun h => hby (h.trans hvbcol).symm))
          ⟨hfstne va va, hfstne va vc, hfstne va vb,
            hsndne ε' hvavc, hsndne ε' hab, hsndne ε' hvcvb⟩
        obtain ⟨P₁, hP₁p, hP₁s⟩ := q3_walk4 (A := CompleteTranspositionGraph 2)
          (x₁ := (ε, vc)) (x₂ := (ε, vb)) (x₃ := (ε, vd)) (x₄ := (ε', vd))
          (hin ε vc vb (fun h => hby (h.trans hvbcol).symm))
          (hin ε vb vd (fun h => hby (hvbcol.symm.trans (h.trans hvdcol))))
          (hver vd)
          ⟨hsndne ε hvcvb, hsndne ε hcd, hfstne vc vd,
            hsndne ε hvbvd, hfstne vb vd, hfstne vd vd⟩
        refine q3_finish h0s h1s h0t h1t hva hvb hvc hvd P₀ P₁ hP₀p hP₁p hP₀s hP₁s ?_ ?_
        · intro x
          obtain ⟨e, w⟩ := x
          rcases hE2 e with rfl | rfl <;>
            rcases q2_exhaust va vb vc vd hby hvbcol hvdcol hab hcd w with
              rfl | rfl | rfl | rfl <;>
            simp
        · intro x hx
          obtain ⟨h₀, h₁⟩ := hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h₀ h₁
          rcases h₀ with rfl | rfl | rfl | rfl <;> rcases h₁ with h₁ | h₁ | h₁ | h₁ <;>
            rw [Prod.mk.injEq] at h₁ <;>
            first
              | exact hεε' h₁.1
              | exact hεε' h₁.1.symm
              | exact hvavc h₁.2
              | exact hab h₁.2
              | exact hvavd h₁.2
              | exact hcd h₁.2
              | exact hvbvd h₁.2
              | exact hvcvb h₁.2.symm

end Q3B

/-! ## Tier 2 complete: the hypercube paired-2 theorem (axiom A3's statement, proved) -/

private theorem dpc_all2_pairwise : ∀ (l : List Nat), (∀ x ∈ l, x = 2) → l.Pairwise (· ≥ ·)
  | [], _ => List.Pairwise.nil
  | a :: r, hall => by
      refine List.Pairwise.cons ?_ (dpc_all2_pairwise r ?_)
      · intro b hb
        have ha : a = 2 := hall a (List.mem_cons_self ..)
        have hbv : b = 2 := hall b (List.mem_cons_of_mem a hb)
        omega
      · exact fun x hx => hall x (List.mem_cons_of_mem a hx)

set_option maxHeartbeats 3200000 in
/-- **Tier 2 of the §7 discharge program, COMPLETE.** Every all-twos CT-product (i.e. every
    hypercube `Q_n`, `n ≥ 1`) admits paired 2-disjoint-path covers. The statement is identical
    to the axiom `hypercube_ctProduct_paired_two`; nothing is wired in. -/
theorem hypercube_paired_two_proved : ∀ (ranks : List Nat), ranks ≠ [] →
    (∀ a : Nat, a ∈ ranks → a = 2) →
    IsPairedKDPCForOpposite (CTProductGraph ranks) (CTProductColor ranks) 2
  | [], hne, _ => absurd rfl hne
  | [a], _, hall => by
      obtain rfl : a = 2 := hall a (List.mem_cons_self ..)
      exact hypercube_paired_two_base1
  | [a, b], _, hall => by
      obtain rfl : a = 2 := hall a (by simp)
      obtain rfl : b = 2 := hall b (by simp)
      exact hypercube_paired_two_base2
  | a :: b :: c :: tl, _, hall => by
      classical
      obtain rfl : a = 2 := hall a (by simp)
      obtain rfl : b = 2 := hall b (by simp)
      obtain rfl : c = 2 := hall c (by simp)
      have htail_all : ∀ x ∈ 2 :: 2 :: tl, x = 2 :=
        fun x hx => hall x (List.mem_cons_of_mem 2 hx)
      have htail_ne : (2 :: 2 :: tl : List Nat) ≠ [] := by simp
      have h2dpc := hypercube_paired_two_proved (2 :: 2 :: tl) htail_ne htail_all
      have hcanon : CanonicalCTRanks (2 :: 2 :: tl) := canonical_of_pairwiseGE htail_ne
        (fun x hx => by rw [htail_all x hx]) (dpc_all2_pairwise _ htail_all)
      have hEq := ctProduct_equitable hcanon
      have hHbip : ∀ u v, (CTProductGraph (2 :: 2 :: tl)).Adj u v →
          CTProductColor (2 :: 2 :: tl) u ≠ CTProductColor (2 :: 2 :: tl) v := hEq.1
      have hcardW : Fintype.card (CTProductVertex (2 :: 2 :: tl)) =
          2 ^ (2 :: 2 :: tl : List Nat).length :=
        dpc_vt_card _ htail_ne htail_all
      have hclass : ∀ cc : Bool, 2 ^ ((2 :: 2 :: tl : List Nat).length - 1) =
          (Finset.univ.filter
            (fun w => CTProductColor (2 :: 2 :: tl) w = cc)).card := by
        intro cc
        have h := dpc_class_card hEq cc
        rw [hcardW] at h
        have hlen1 : ((2 :: 2 :: tl : List Nat)).length - 1 + 1 =
            ((2 :: 2 :: tl : List Nat)).length := by
          simp
        have h2 : (2:ℕ) ^ (2 :: 2 :: tl : List Nat).length =
            2 * 2 ^ ((2 :: 2 :: tl : List Nat).length - 1) := by
          conv_lhs => rw [← hlen1]
          rw [pow_succ']
        omega
      have hclass2' : ∀ cc : Bool, 2 ≤ (Finset.univ.filter
          (fun w => CTProductColor (2 :: 2 :: tl) w = cc)).card := by
        intro cc
        rw [← hclass cc]
        calc (2:ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ ((2 :: 2 :: tl : List Nat).length - 1) :=
            Nat.pow_le_pow_right (by omega) (by simp)
      have hlace : IsHamLaceable (CTProductGraph (2 :: 2 :: tl))
          (CTProductColor (2 :: 2 :: tl)) := by
        apply paired_one_opposite_iff_hamLaceable.mp
        apply prop11c_proved _ _ hEq h2dpc (le_refl 1) (by omega)
        rw [hcardW]
        calc (4:ℕ) = 2 ^ 2 := rfl
          _ ≤ 2 ^ (2 :: 2 :: tl : List Nat).length :=
            Nat.pow_le_pow_right (by omega) (by simp)
      intro s t hd
      set ε := (s 0).1 with hεdef
      have hA : (CompleteTranspositionGraph 2).Adj ε (dpcOpp ε) :=
        ct2_adj_of_ne ε (dpcOpp ε) (Ne.symm (dpcOpp_ne ε))
      have hE2 : ∀ e, e = ε ∨ e = dpcOpp ε := fun e => ct2_eq_or_opp ε e
      have hbne2 : ∀ x : Bool, x ≠ !x := by decide
      have hcolA : CompleteTranspositionColor 2 ε ≠
          CompleteTranspositionColor 2 (dpcOpp ε) := by
        rw [ct2_color_opp]
        exact hbne2 _
      have h0s : (s 0).1 = ε := hεdef.symm
      have hne01 : (0 : Fin 2) ≠ 1 := by decide
      rcases hE2 ((t 0).1) with h0t | h0t <;>
        rcases hE2 ((s 1).1) with h1s | h1s <;>
        rcases hE2 ((t 1).1) with h1t | h1t
      · -- (ε, ε, ε): case A
        exact dpc_caseA hA hE2 hHbip hlace h2dpc hd h0s h0t h1s h1t
      · -- (ε, ε, ε'): pair 1 split with source in ε — case C after swapping pairs? no: pair0 within, pair1 split source ε: C direct
        exact dpc_caseC hA hE2 hlace h2dpc hclass2' hcolA hd h0s h0t h1s h1t
      · -- (ε, ε', ε): pair 1 split source ε' — reverse pair 1, then C
        apply dpc_reverse_pair 1
        exact dpc_caseC hA hE2 hlace h2dpc hclass2' hcolA
          (oppositeDemand_reverse_pair 1 hd)
          (by rw [Function.update_of_ne hne01])
          (by rw [Function.update_of_ne hne01]; exact h0t)
          (by rw [Function.update_self]; exact h1t)
          (by rw [Function.update_self]; exact h1s)
      · -- (ε, ε', ε'): pair 1 within ε' — case A′
        exact dpc_caseA' ((CompleteTranspositionGraph 2).ne_of_adj hA) hE2 hlace hd
          h0s h0t h1s h1t
      · -- (ε', ε, ε): pair 0 split, pair 1 within ε — swap pairs, then C
        apply dpc_reindex (Equiv.swap 0 1)
        exact dpc_caseC hA hE2 hlace h2dpc hclass2' hcolA
          (oppositeDemand_reindex (Equiv.swap 0 1) hd)
          (by show (s (Equiv.swap 0 1 0)).1 = ε; rw [Equiv.swap_apply_left]; exact h1s)
          (by show (t (Equiv.swap 0 1 0)).1 = ε; rw [Equiv.swap_apply_left]; exact h1t)
          (by show (s (Equiv.swap 0 1 1)).1 = ε; rw [Equiv.swap_apply_right])
          (by show (t (Equiv.swap 0 1 1)).1 = dpcOpp ε; rw [Equiv.swap_apply_right]; exact h0t)
      · -- (ε', ε, ε'): both pairs split, both sources in ε — case B (generic or Q₃)
        cases tl with
        | nil =>
            exact dpc_q3_caseB hA hE2 hcolA hd h0s h1s h0t h1t
        | cons d tl' =>
            have hclass3 : ∀ cc : Bool, 3 ≤ (Finset.univ.filter
                (fun w => CTProductColor (2 :: 2 :: d :: tl') w = cc)).card := by
              intro cc
              rw [← hclass cc]
              calc (3:ℕ) ≤ 2 ^ 2 := by omega
                _ ≤ 2 ^ ((2 :: 2 :: d :: tl' : List Nat).length - 1) :=
                  Nat.pow_le_pow_right (by omega) (by simp)
            exact dpc_caseB hA hE2 h2dpc hclass3 hcolA hd h0s h1s h0t h1t
      · -- (ε', ε', ε): pair 1 split source ε' — reverse pair 1, then B (generic or Q₃)
        apply dpc_reverse_pair 1
        have hd' := oppositeDemand_reverse_pair 1 hd
        have g0s : ((Function.update s 1 (t 1)) 0).1 = ε := by
          rw [Function.update_of_ne hne01]
        have g1s : ((Function.update s 1 (t 1)) 1).1 = ε := by
          rw [Function.update_self]; exact h1t
        have g0t : ((Function.update t 1 (s 1)) 0).1 = dpcOpp ε := by
          rw [Function.update_of_ne hne01]; exact h0t
        have g1t : ((Function.update t 1 (s 1)) 1).1 = dpcOpp ε := by
          rw [Function.update_self]; exact h1s
        cases tl with
        | nil =>
            exact dpc_q3_caseB hA hE2 hcolA hd' g0s g1s g0t g1t
        | cons d tl' =>
            have hclass3 : ∀ cc : Bool, 3 ≤ (Finset.univ.filter
                (fun w => CTProductColor (2 :: 2 :: d :: tl') w = cc)).card := by
              intro cc
              rw [← hclass cc]
              calc (3:ℕ) ≤ 2 ^ 2 := by omega
                _ ≤ 2 ^ ((2 :: 2 :: d :: tl' : List Nat).length - 1) :=
                  Nat.pow_le_pow_right (by omega) (by simp)
            exact dpc_caseB hA hE2 h2dpc hclass3 hcolA hd' g0s g1s g0t g1t
      · -- (ε', ε', ε'): pair 1 within ε' — swap pairs and reverse, then C at swapped layers
        apply dpc_reindex (Equiv.swap 0 1)
        apply dpc_reverse_pair 1
        have hA' : (CompleteTranspositionGraph 2).Adj (dpcOpp ε) ε := hA.symm
        have hE2' : ∀ e, e = dpcOpp ε ∨ e = ε := fun e => (hE2 e).symm
        exact dpc_caseC hA' hE2' hlace h2dpc hclass2' (Ne.symm hcolA)
          (oppositeDemand_reverse_pair 1 (oppositeDemand_reindex (Equiv.swap 0 1) hd))
          (by
            rw [Function.update_of_ne hne01]
            show (s (Equiv.swap 0 1 0)).1 = dpcOpp ε
            rw [Equiv.swap_apply_left]; exact h1s)
          (by
            rw [Function.update_of_ne hne01]
            show (t (Equiv.swap 0 1 0)).1 = dpcOpp ε
            rw [Equiv.swap_apply_left]; exact h1t)
          (by
            rw [Function.update_self]
            show (t (Equiv.swap 0 1 1)).1 = dpcOpp ε
            rw [Equiv.swap_apply_right]; exact h0t)
          (by
            rw [Function.update_self]
            show (s (Equiv.swap 0 1 1)).1 = ε
            rw [Equiv.swap_apply_right])

termination_by ranks _ _ => ranks.length
decreasing_by simp

#print axioms hypercube_paired_two_proved

/-- Composition corollary: every hypercube is Hamilton laceable (Tier 1 + Tier 2). -/
theorem hypercube_laceable_proved (ranks : List Nat) (hne : ranks ≠ [])
    (hall : ∀ a : Nat, a ∈ ranks → a = 2)
    (hcard : 4 ≤ Fintype.card (CTProductVertex ranks)) :
    IsHamLaceable (CTProductGraph ranks) (CTProductColor ranks) := by
  have hcanon : CanonicalCTRanks ranks := canonical_of_pairwiseGE hne
    (fun x hx => by rw [hall x hx]) (dpc_all2_pairwise _ hall)
  have hEq := ctProduct_equitable hcanon
  apply paired_one_opposite_iff_hamLaceable.mp
  exact prop11c_proved _ _ hEq (hypercube_paired_two_proved ranks hne hall)
    (le_refl 1) (by omega) hcard

/-- Composition corollary: `CT₃ = K₃,₃` is Hamilton laceable (Tier 1 + the Tier 3 base). -/
theorem completeTransposition3_laceable :
    IsHamLaceable (CompleteTranspositionGraph 3) (CompleteTranspositionColor 3) := by
  have hcanon : CanonicalCTRanks [3] := CanonicalCTRanks.singleLarge 3 (le_refl 3)
  have hEq : IsEquitableBipartite (CompleteTranspositionGraph 3)
      (CompleteTranspositionColor 3) := ctProduct_equitable hcanon
  apply paired_one_opposite_iff_hamLaceable.mp
  have hc : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    rfl
  apply prop11c_proved _ _ hEq completeTransposition3_paired_two (le_refl 1) (by omega)
  rw [hc]
  omega

#print axioms hypercube_laceable_proved
#print axioms completeTransposition3_laceable

end Brualdi.Ledger
