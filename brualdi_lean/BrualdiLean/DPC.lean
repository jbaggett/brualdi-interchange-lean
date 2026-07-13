/-
DPC.lean — side branch toward discharging the §7 axioms (2026-07-06, Jeff's call).

Tier 1: `prop11c_proved` — Coleman et al. 2025, Proposition 1.1(c) (the equitable
downgrade), proved from scratch by their own argument: a probe cover discovers a fresh
adjacent opposite-colored pair, the larger cover runs on an augmented demand placing that
pair between two demands, and the two extra paths merge across the discovered edge.

Statements match the axioms in `Coleman.lean` EXACTLY. Nothing is wired into the mainline;
the axioms stay until the flip is decided.
-/
import BrualdiLean.Sec4

namespace Brualdi.Ledger

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

theorem dpc_head?_eq {α : Type*} {l : List α} (h : l ≠ []) :
    l.head? = some (l.head h) := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

/-! ## Path splicing over support lists -/

/-- Splice two vertex-disjoint paths across an edge between their facing endpoints. -/
theorem dpc_splice {G : SimpleGraph V} {a x y b : V}
    (P : G.Walk a x) (Q : G.Walk y b) (hP : P.IsPath) (hQ : Q.IsPath)
    (hxy : G.Adj x y)
    (hdisj : ∀ v, ¬ (v ∈ P.support ∧ v ∈ Q.support)) :
    ∃ R : G.Walk a b, R.IsPath ∧ R.support = P.support ++ Q.support := by
  classical
  have hPne : P.support ≠ [] := P.support_ne_nil
  have hQne : Q.support ≠ [] := Q.support_ne_nil
  have hne : P.support ++ Q.support ≠ [] := by simp [hPne]
  have hchain : (P.support ++ Q.support).IsChain G.Adj := by
    refine P.isChain_adj_support.append Q.isChain_adj_support ?_
    intro u hu v hv
    rw [walk_support_getLast? P] at hu
    rw [walk_support_head? Q] at hv
    simp at hu hv
    subst u
    subst v
    exact hxy
  have hWsupp := SimpleGraph.Walk.support_ofSupport hne hchain
  have hhead : (P.support ++ Q.support).head hne = a := by
    have h1 : (P.support ++ Q.support).head? = P.support.head? := by
      cases hp : P.support with
      | nil => exact absurd hp hPne
      | cons c r => simp
    have h2 := (dpc_head?_eq hne).symm.trans (h1.trans (walk_support_head? P))
    exact Option.some.inj h2
  have hlast : (P.support ++ Q.support).getLast hne = b := by
    have h1 : (P.support ++ Q.support).getLast? = Q.support.getLast? :=
      List.getLast?_append_of_ne_nil (l₁ := P.support) hQne
    have h2 : (P.support ++ Q.support).getLast? =
        some ((P.support ++ Q.support).getLast hne) :=
      List.getLast?_eq_some_getLast hne
    have h3 := h2.symm.trans (h1.trans (walk_support_getLast? Q))
    exact Option.some.inj h3
  refine ⟨(SimpleGraph.Walk.ofSupport _ hne hchain).copy hhead hlast, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [SimpleGraph.Walk.support_copy, hWsupp, List.nodup_append]
    refine ⟨hP.support_nodup, hQ.support_nodup, ?_⟩
    intro v hvP w hwQ
    intro heq
    subst heq
    exact hdisj v ⟨hvP, hwQ⟩
  · rw [SimpleGraph.Walk.support_copy, hWsupp]

/-! ## Spare-vertex counting -/

/-- A legal demand uses exactly one endpoint of each color per pair, so a color class with
    more than `j` vertices has a spare outside all endpoints. -/
theorem dpc_spare {col : V → Bool} {j : ℕ}
    {s t : Fin j → V} (hd : OppositeDemand col s t) (c : Bool)
    (hclass : j < (Finset.univ.filter (fun v => col v = c)).card) :
    ∃ u, col u = c ∧ (∀ i, u ≠ s i) ∧ (∀ i, u ≠ t i) := by
  classical
  set picks : Finset V := Finset.univ.image
    (fun i : Fin j => if col (s i) = c then s i else t i) with hpicks
  have hcard : picks.card ≤ j := le_trans Finset.card_image_le (by simp)
  have hcover : ∀ v, col v = c → (∃ i, v = s i ∨ v = t i) → v ∈ picks := by
    rintro v hvc ⟨i, hvi⟩
    rw [hpicks]
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases hvi with rfl | rfl
    · rw [if_pos hvc]
    · rw [if_neg ?_]
      intro hsc
      exact (hd.1 i) (hsc.trans hvc.symm)
  have hpos : 0 < ((Finset.univ.filter (fun v => col v = c)) \ picks).card := by
    have h := Finset.card_le_card_sdiff_add_card
      (s := Finset.univ.filter (fun v => col v = c)) (t := picks)
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have huc : col u = c := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
  have hunp : u ∉ picks := (Finset.mem_sdiff.mp hu).2
  exact ⟨u, huc,
    fun i h => hunp (hcover u huc ⟨i, Or.inl h⟩),
    fun i h => hunp (hcover u huc ⟨i, Or.inr h⟩)⟩

/-- In an equitable graph each color class holds half the vertices. -/
theorem dpc_class_card {G : SimpleGraph V} {col : V → Bool}
    (hEq : IsEquitableBipartite G col) (c : Bool) :
    2 * (Finset.univ.filter (fun v => col v = c)).card = Fintype.card V := by
  classical
  have hsplit : (Finset.univ.filter (fun v : V => col v = false)).card +
      (Finset.univ.filter (fun v : V => col v = true)).card = Fintype.card V := by
    rw [← Finset.card_univ]
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset V)) (p := fun v => col v = false)
    have hneg : (Finset.univ.filter (fun v : V => ¬ col v = false)) =
        (Finset.univ.filter (fun v : V => col v = true)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases hv : col v <;> simp
    rw [hneg] at h
    exact h
  have heqc : (Finset.univ.filter (fun v : V => col v = false)).card =
      (Finset.univ.filter (fun v : V => col v = true)).card := by
    have e1 := Fintype.card_subtype (fun v : V => col v = false)
    have e2 := Fintype.card_subtype (fun v : V => col v = true)
    rw [← e1, ← e2]
    exact hEq.2
  cases c <;> omega

/-! ## The one-step downgrade -/

set_option maxHeartbeats 1600000 in
private theorem dpc_one_step {G : SimpleGraph V} {col : V → Bool} {j : ℕ}
    (hEq : IsEquitableBipartite G col)
    (hDPC : IsPairedKDPCForOpposite G col (j + 1))
    (hj : 1 ≤ j)
    (hcard : 2 * (j + 1) ≤ Fintype.card V) :
    IsPairedKDPCForOpposite G col j := by
  classical
  intro s t hd
  have hclass : ∀ c : Bool, j < (Finset.univ.filter (fun v => col v = c)).card := by
    intro c
    have := dpc_class_card hEq c
    omega
  obtain ⟨u, huc, hus, hut⟩ := dpc_spare hd false (hclass false)
  obtain ⟨w, hwc, hws, hwt⟩ := dpc_spare hd true (hclass true)
  have huw : u ≠ w := by
    intro h
    rw [h, hwc] at huc
    exact Bool.false_ne_true huc.symm
  -- probe demand
  have hd₁ : OppositeDemand col (Fin.snoc s u) (Fin.snoc t w) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hd.1 i'
      · simp only [Fin.snoc_last]
        rw [huc, hwc]
        exact Bool.false_ne_true
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hab
        rw [hd.2.1 hab]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab.symm (hus a')
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab (hus b')
      · rfl
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hab
        rw [hd.2.2.1 hab]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab.symm (hwt a')
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab (hwt b')
      · rfl
    · intro a b
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hd.2.2.2 a' b'
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        intro h
        exact (hws a') h.symm
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hut b'
      · simp only [Fin.snoc_last]
        exact huw
  obtain ⟨P, hPpath, hPcover, hPdisj⟩ := hDPC (Fin.snoc s u) (Fin.snoc t w) hd₁
  -- harvest the final edge of the probe's last path
  have hPl_nn : ¬ (P (Fin.last j)).Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    simp only [Fin.snoc_last]
    exact huw
  set z : V := (P (Fin.last j)).penultimate with hz
  have hz_adj_w : G.Adj z w := by
    have h := SimpleGraph.Walk.adj_penultimate hPl_nn
    simpa only [Fin.snoc_last] using h
  have hz_mem : z ∈ (P (Fin.last j)).support :=
    List.dropLast_subset _ (SimpleGraph.Walk.penultimate_mem_dropLast_support hPl_nn)
  have hz_col : col z = false := by
    have h := hEq.1 z w hz_adj_w
    rw [hwc] at h
    cases hc : col z
    · rfl
    · exact absurd hc h
  have hz_fresh_s : ∀ i, z ≠ s i := by
    intro i h
    have hzi : z ∈ (P i.castSucc).support := by
      rw [h]
      have hh := (P i.castSucc).start_mem_support
      simpa only [Fin.snoc_castSucc] using hh
    exact hPdisj i.castSucc (Fin.last j) (Fin.castSucc_lt_last i).ne z ⟨hzi, hz_mem⟩
  have hz_fresh_t : ∀ i, z ≠ t i := by
    intro i h
    have hzi : z ∈ (P i.castSucc).support := by
      rw [h]
      have hh := (P i.castSucc).end_mem_support
      simpa only [Fin.snoc_castSucc] using hh
    exact hPdisj i.castSucc (Fin.last j) (Fin.castSucc_lt_last i).ne z ⟨hzi, hz_mem⟩
  -- orient the fresh pair against the pair to merge
  set jm : Fin j := ⟨j - 1, by omega⟩ with hjm
  set x : V := if col (t jm) = true then w else z with hx
  set y : V := if col (t jm) = true then z else w with hy
  have hx_col : col x = col (t jm) := by
    by_cases h : col (t jm) = true
    · rw [hx, if_pos h, hwc, h]
    · rw [hx, if_neg h, hz_col]
      cases hc : col (t jm)
      · rfl
      · exact absurd hc h
  have hxy_adj : G.Adj x y := by
    by_cases h : col (t jm) = true
    · rw [hx, if_pos h, hy, if_pos h]
      exact hz_adj_w.symm
    · rw [hx, if_neg h, hy, if_neg h]
      exact hz_adj_w
  have hxy_ne : x ≠ y := G.ne_of_adj hxy_adj
  have hyx_col : col y ≠ col x := by
    intro h
    exact (hEq.1 x y hxy_adj) h.symm
  have hx_fresh_s : ∀ i, x ≠ s i := by
    intro i
    by_cases h : col (t jm) = true
    · rw [hx, if_pos h]; exact hws i
    · rw [hx, if_neg h]; exact hz_fresh_s i
  have hx_fresh_t : ∀ i, x ≠ t i := by
    intro i
    by_cases h : col (t jm) = true
    · rw [hx, if_pos h]; exact hwt i
    · rw [hx, if_neg h]; exact hz_fresh_t i
  have hy_fresh_s : ∀ i, y ≠ s i := by
    intro i
    by_cases h : col (t jm) = true
    · rw [hy, if_pos h]; exact hz_fresh_s i
    · rw [hy, if_neg h]; exact hws i
  have hy_fresh_t : ∀ i, y ≠ t i := by
    intro i
    by_cases h : col (t jm) = true
    · rw [hy, if_pos h]; exact hz_fresh_t i
    · rw [hy, if_neg h]; exact hwt i
  -- the main demand: pair jm's target becomes x, the last pair is (y, t jm)
  set t' : Fin j → V := Function.update t jm x with ht'
  have ht'_jm : t' jm = x := by
    rw [ht']
    simp
  have ht'_ne : ∀ i, i ≠ jm → t' i = t i := by
    intro i h
    rw [ht']
    exact Function.update_of_ne h x t
  have hd₂ : OppositeDemand col (Fin.snoc s y) (Fin.snoc t' (t jm)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        by_cases h : i' = jm
        · subst h
          rw [ht'_jm, hx_col]
          exact hd.1 jm
        · rw [ht'_ne i' h]
          exact hd.1 i'
      · simp only [Fin.snoc_last]
        rw [← hx_col]
        exact hyx_col
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hab
        rw [hd.2.1 hab]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab.symm (hy_fresh_s a')
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        exact absurd hab (hy_fresh_s b')
      · rfl
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hab
        by_cases ha : a' = jm <;> by_cases hb : b' = jm
        · rw [ha, hb]
        · rw [ha, ht'_jm] at hab
          rw [ht'_ne b' hb] at hab
          exact absurd hab (hx_fresh_t b')
        · rw [hb, ht'_jm] at hab
          rw [ht'_ne a' ha] at hab
          exact absurd hab.symm (hx_fresh_t a')
        · rw [ht'_ne a' ha, ht'_ne b' hb] at hab
          rw [hd.2.2.1 hab]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        by_cases ha : a' = jm
        · rw [ha, ht'_jm] at hab
          exact absurd hab (hx_fresh_t jm)
        · rw [ht'_ne a' ha] at hab
          exact absurd (hd.2.2.1 hab) ha
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hab
        by_cases hb : b' = jm
        · rw [hb, ht'_jm] at hab
          exact absurd hab.symm (hx_fresh_t jm)
        · rw [ht'_ne b' hb] at hab
          exact absurd (hd.2.2.1 hab.symm) hb
      · rfl
    · intro a b
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        by_cases hb : b' = jm
        · rw [hb, ht'_jm]
          intro h
          exact (hx_fresh_s a') h.symm
        · rw [ht'_ne b' hb]
          exact hd.2.2.2 a' b'
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hd.2.2.2 a' jm
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        by_cases hb : b' = jm
        · rw [hb, ht'_jm]
          intro h
          exact hxy_ne h.symm
        · rw [ht'_ne b' hb]
          exact hy_fresh_t b'
      · simp only [Fin.snoc_last]
        exact hy_fresh_t jm
  obtain ⟨Q, hQpath, hQcover, hQdisj⟩ := hDPC (Fin.snoc s y) (Fin.snoc t' (t jm)) hd₂
  -- the two paths to merge
  have hs1 : (Fin.snoc s y : Fin (j+1) → V) jm.castSucc = s jm := by
    simp only [Fin.snoc_castSucc]
  have ht1 : (Fin.snoc t' (t jm) : Fin (j+1) → V) jm.castSucc = x := by
    simp only [Fin.snoc_castSucc]
    exact ht'_jm
  have hs2 : (Fin.snoc s y : Fin (j+1) → V) (Fin.last j) = y := by
    simp only [Fin.snoc_last]
  have ht2 : (Fin.snoc t' (t jm) : Fin (j+1) → V) (Fin.last j) = t jm := by
    simp only [Fin.snoc_last]
  have hP1p : ((Q jm.castSucc).copy hs1 ht1).IsPath := by
    rw [SimpleGraph.Walk.isPath_copy]
    exact hQpath jm.castSucc
  have hP2p : ((Q (Fin.last j)).copy hs2 ht2).IsPath := by
    rw [SimpleGraph.Walk.isPath_copy]
    exact hQpath (Fin.last j)
  have hdisj12 : ∀ v, ¬ (v ∈ ((Q jm.castSucc).copy hs1 ht1).support ∧
      v ∈ ((Q (Fin.last j)).copy hs2 ht2).support) := by
    intro v hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hv
    exact hQdisj jm.castSucc (Fin.last j) (Fin.castSucc_lt_last jm).ne v hv
  obtain ⟨R, hRp, hRs⟩ := dpc_splice ((Q jm.castSucc).copy hs1 ht1)
    ((Q (Fin.last j)).copy hs2 ht2) hP1p hP2p hxy_adj hdisj12
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hRs
  -- assemble the final family
  refine ⟨fun i => if h : i = jm then
      R.copy (congrArg s h.symm) (congrArg t h.symm)
    else
      (Q i.castSucc).copy (by simp only [Fin.snoc_castSucc])
        (by simp only [Fin.snoc_castSucc]; exact ht'_ne i h), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = jm
    · rw [dif_pos h, SimpleGraph.Walk.isPath_copy]
      exact hRp
    · rw [dif_neg h, SimpleGraph.Walk.isPath_copy]
      exact hQpath i.castSucc
  · intro v
    obtain ⟨m, hm⟩ := hQcover v
    rcases Fin.eq_castSucc_or_eq_last m with ⟨m', rfl⟩ | rfl
    · by_cases h : m' = jm
      · refine ⟨jm, ?_⟩
        dsimp only
        rw [dif_pos rfl, SimpleGraph.Walk.support_copy, hRs, List.mem_append]
        subst h
        exact Or.inl hm
      · refine ⟨m', ?_⟩
        dsimp only
        rw [dif_neg h, SimpleGraph.Walk.support_copy]
        exact hm
    · refine ⟨jm, ?_⟩
      dsimp only
      rw [dif_pos rfl, SimpleGraph.Walk.support_copy, hRs, List.mem_append]
      exact Or.inr hm
  · intro a b hab v hv
    dsimp only at hv
    by_cases ha : a = jm <;> by_cases hb : b = jm
    · exact hab (ha.trans hb.symm)
    · rw [dif_pos ha, SimpleGraph.Walk.support_copy, hRs] at hv
      rw [dif_neg hb, SimpleGraph.Walk.support_copy] at hv
      rcases List.mem_append.mp hv.1 with h1 | h1
      · exact hQdisj jm.castSucc b.castSucc
          (fun h => hb (Fin.castSucc_injective _ h).symm) v ⟨h1, hv.2⟩
      · exact hQdisj (Fin.last j) b.castSucc (Fin.castSucc_lt_last b).ne' v ⟨h1, hv.2⟩
    · rw [dif_pos hb, SimpleGraph.Walk.support_copy, hRs] at hv
      rw [dif_neg ha, SimpleGraph.Walk.support_copy] at hv
      rcases List.mem_append.mp hv.2 with h2 | h2
      · exact hQdisj a.castSucc jm.castSucc
          (fun h => ha (Fin.castSucc_injective _ h)) v ⟨hv.1, h2⟩
      · exact hQdisj a.castSucc (Fin.last j) (Fin.castSucc_lt_last a).ne v ⟨hv.1, h2⟩
    · rw [dif_neg ha, dif_neg hb, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_copy] at hv
      exact hQdisj a.castSucc b.castSucc
        (fun h => hab (Fin.castSucc_injective _ h)) v hv

/-! ## The downgrade chain -/

private theorem dpc_down {G : SimpleGraph V} {col : V → Bool} {l : ℕ}
    (hEq : IsEquitableBipartite G col) (hl : 1 ≤ l) :
    ∀ d, IsPairedKDPCForOpposite G col (l + d) → 2 * (l + d) ≤ Fintype.card V →
      IsPairedKDPCForOpposite G col l
  | 0, h, _ => by simpa using h
  | d + 1, h, hc => by
      have hstep : IsPairedKDPCForOpposite G col (l + d) := by
        have h' : IsPairedKDPCForOpposite G col ((l + d) + 1) := by
          have harith : l + (d + 1) = (l + d) + 1 := by omega
          rwa [harith] at h
        exact dpc_one_step hEq h' (by omega) (by omega)
      exact dpc_down hEq hl d hstep (by omega)

set_option linter.unusedVariables false in
/-- **Coleman et al. 2025, Proposition 1.1(c) — PROVED from scratch** (Tier 1 of the §7
    discharge program). Statement identical to the axiom `prop11c`; not yet wired in. -/
theorem prop11c_proved {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool) {k l : Nat}
    (hEq : IsEquitableBipartite G col)
    (hDPC : IsPairedKDPCForOpposite G col k)
    (hl : 1 ≤ l) (hle : l ≤ k)
    (hcard : 2 * k ≤ Fintype.card V) :
    IsPairedKDPCForOpposite G col l := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, k = l + d := ⟨k - l, by omega⟩
  exact dpc_down hEq hl d hDPC hcard

#print axioms prop11c_proved

/-! ## Tier 2 bases: the smallest hypercubes -/

/-- `Q₁ = K₂`: paired 2-covers hold vacuously (no four distinct vertices). -/
theorem hypercube_paired_two_base1 :
    IsPairedKDPCForOpposite (CTProductGraph [2]) (CTProductColor [2]) 2 := by
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

/-! Decidability plumbing for the tiny kernel certificates. -/

private instance dpc_isSwap_dec {n : ℕ} (f : Equiv.Perm (Fin n)) : Decidable f.IsSwap := by
  unfold Equiv.Perm.IsSwap
  infer_instance

private instance dpc_ct_adj_dec {n : ℕ} :
    DecidableRel (CompleteTranspositionGraph n).Adj := fun σ τ =>
  decidable_of_iff (σ ≠ τ ∧ (Equiv.Perm.IsSwap (σ⁻¹ * τ) ∨ Equiv.Perm.IsSwap (τ⁻¹ * σ)))
    (by rw [CompleteTranspositionGraph, SimpleGraph.fromRel_adj])

private instance dpc_q1_adj_dec : DecidableRel (CTProductGraph [2]).Adj := fun σ τ =>
  inferInstanceAs (Decidable ((CompleteTranspositionGraph 2).Adj σ τ))

private instance dpc_q2_adj_dec : DecidableRel (CTProductGraph [2, 2]).Adj := fun x y =>
  decidable_of_iff
    ((CompleteTranspositionGraph 2).Adj x.1 y.1 ∧ x.2 = y.2 ∨
      (CTProductGraph [2]).Adj x.2 y.2 ∧ x.1 = y.1)
    (by rw [show (CTProductGraph [2, 2]) =
          (CompleteTranspositionGraph 2 □ CTProductGraph [2]) from rfl,
        SimpleGraph.boxProd_adj])

/-- Adjacency facts and counts on tiny CT-products, kernel-decided. -/
theorem q2_opposite_adj : ∀ p q : CTProductVertex [2, 2],
    CTProductColor [2, 2] p ≠ CTProductColor [2, 2] q →
    (CTProductGraph [2, 2]).Adj p q := by decide

private theorem q2_card : Fintype.card (CTProductVertex [2, 2]) = 4 := by
  show Fintype.card (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) = 4
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- A single edge is a path. -/
theorem dpc_edge_path {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  simp [G.ne_of_adj h]

/-- `Q₂ = K₂ □ K₂ = C₄`: every opposite-colored pair is adjacent, and four distinct
    terminals exhaust the four vertices, so the two demand edges are the cover. -/
theorem hypercube_paired_two_base2 :
    IsPairedKDPCForOpposite (CTProductGraph [2, 2]) (CTProductColor [2, 2]) 2 := by
  classical
  intro s t hd
  have hadj : ∀ i, (CTProductGraph [2, 2]).Adj (s i) (t i) :=
    fun i => q2_opposite_adj _ _ (hd.1 i)
  refine ⟨fun i => SimpleGraph.Walk.cons (hadj i) SimpleGraph.Walk.nil, ?_, ?_, ?_⟩
  · intro i
    exact dpc_edge_path (hadj i)
  · -- four distinct terminals in a four-element type exhaust it
    intro v
    set f : Fin 4 → CTProductVertex [2, 2] := ![s 0, s 1, t 0, t 1] with hf
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
    have hsurj : Function.Surjective f := by
      have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp [q2_card]⟩
      exact hbij.2
    obtain ⟨a, ha⟩ := hsurj v
    fin_cases a <;> simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one] at ha
    · exact ⟨0, by simp [← ha]⟩
    · exact ⟨1, by simp [← ha]⟩
    · exact ⟨0, by simp [← ha]⟩
    · exact ⟨1, by simp [← ha]⟩
  · intro a b hab v hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨h1, h2⟩ := hv
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
    · exact hab (hd.2.1 h2)
    · exact hd.2.2.2 a b h2
    · exact hd.2.2.2 b a h2.symm
    · exact hab (hd.2.2.1 h2)

/-! ## Tier 3 base: `CT₃ = K₃,₃` from scratch -/

/-- In `S₃` every odd permutation is a transposition, so opposite parity means adjacent. -/
private theorem ct3_opposite_adj : ∀ σ τ : Equiv.Perm (Fin 3),
    CompleteTranspositionColor 3 σ ≠ CompleteTranspositionColor 3 τ →
    (CompleteTranspositionGraph 3).Adj σ τ := by decide

private theorem ct3_class_card : ∀ c : Bool,
    (Finset.univ.filter (fun v : Equiv.Perm (Fin 3) =>
      CompleteTranspositionColor 3 v = c)).card = 3 := by decide

private theorem ct3_card : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rfl

set_option maxHeartbeats 800000 in
/-- **`CT₃` is paired 2-disjoint-path coverable — from scratch** (the Tier 3 base):
    cover one demand by its edge, the other by the 4-path through the two non-terminal
    vertices, one of each parity class. -/
theorem completeTransposition3_paired_two :
    IsPairedKDPCForOpposite (CompleteTranspositionGraph 3)
      (CompleteTranspositionColor 3) 2 := by
  classical
  intro s t hd
  -- the two spare vertices, one per class
  have hclass : ∀ c : Bool, (2 : ℕ) <
      (Finset.univ.filter (fun v : Equiv.Perm (Fin 3) =>
        CompleteTranspositionColor 3 v = c)).card := by
    intro c
    rw [ct3_class_card c]
    omega
  obtain ⟨x, hxc, hxs, hxt⟩ := dpc_spare hd (!(CompleteTranspositionColor 3 (s 1))) (hclass _)
  obtain ⟨y, hyc, hys, hyt⟩ := dpc_spare hd (CompleteTranspositionColor 3 (s 1)) (hclass _)
  have hxy : x ≠ y := by
    intro h
    rw [h, hyc] at hxc
    cases hc : CompleteTranspositionColor 3 (s 1) <;> rw [hc] at hxc <;>
      exact absurd hxc (by simp)
  -- adjacencies for the 4-path s₁ – x – y – t₁
  have h1 : (CompleteTranspositionGraph 3).Adj (s 1) x := by
    apply ct3_opposite_adj
    rw [hxc]
    cases CompleteTranspositionColor 3 (s 1) <;> simp
  have h2 : (CompleteTranspositionGraph 3).Adj x y := by
    apply ct3_opposite_adj
    rw [hxc, hyc]
    cases CompleteTranspositionColor 3 (s 1) <;> simp
  have h3 : (CompleteTranspositionGraph 3).Adj y (t 1) := by
    apply ct3_opposite_adj
    rw [hyc]
    intro h
    exact (hd.1 1) h
  have h0 : (CompleteTranspositionGraph 3).Adj (s 0) (t 0) :=
    ct3_opposite_adj _ _ (hd.1 0)
  -- the two paths
  set P0 : (CompleteTranspositionGraph 3).Walk (s 0) (t 0) :=
    SimpleGraph.Walk.cons h0 SimpleGraph.Walk.nil with hP0
  set P1 : (CompleteTranspositionGraph 3).Walk (s 1) (t 1) :=
    SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil)) with hP1
  have hP0s : P0.support = [s 0, t 0] := by simp [hP0]
  have hP1s : P1.support = [s 1, x, y, t 1] := by simp [hP1]
  have hs1t1 : s 1 ≠ t 1 := by
    intro h
    exact (hd.1 1) (congrArg (CompleteTranspositionColor 3) h)
  have hP1path : P1.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hP1s]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rintro (h | h | h)
      · exact (hxs 1) h.symm
      · exact (hys 1) h.symm
      · exact hs1t1 h
    · rintro (h | h)
      · exact hxy h
      · exact (hxt 1) h
    · exact ⟨hyt 1, not_false⟩
  -- cover: the two non-terminals are exactly {x, y}
  have hcover : ∀ v : Equiv.Perm (Fin 3),
      v ∈ P0.support ∨ v ∈ P1.support := by
    intro v
    by_cases hv0 : v = s 0
    · left; rw [hP0s, hv0]; simp
    by_cases hv1 : v = t 0
    · left; rw [hP0s, hv1]; simp
    by_cases hv2 : v = s 1
    · right; rw [hP1s, hv2]; simp
    by_cases hv3 : v = t 1
    · right; rw [hP1s, hv3]; simp
    -- v is a non-terminal; the non-terminals form a 2-set containing x and y
    right
    rw [hP1s]
    have hterm : ({s 0, s 1, t 0, t 1} : Finset (Equiv.Perm (Fin 3))).card ≤ 4 := by
      apply le_trans (Finset.card_insert_le _ _)
      apply Nat.succ_le_succ
      apply le_trans (Finset.card_insert_le _ _)
      apply Nat.succ_le_succ
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have hvmem : v ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))) \ {s 0, s 1, t 0, t 1} := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      push_neg
      exact ⟨hv0, hv2, hv1, hv3⟩
    have hxmem : x ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))) \ {s 0, s 1, t 0, t 1} := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      push_neg
      exact ⟨hxs 0, hxs 1, hxt 0, hxt 1⟩
    have hymem : y ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))) \ {s 0, s 1, t 0, t 1} := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      push_neg
      exact ⟨hys 0, hys 1, hyt 0, hyt 1⟩
    have hsd_card : ((Finset.univ : Finset (Equiv.Perm (Fin 3))) \
        {s 0, s 1, t 0, t 1}).card ≤ 2 := by
      have hT : ({s 0, s 1, t 0, t 1} : Finset (Equiv.Perm (Fin 3))).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]
          intro h
          exact absurd (hd.2.2.1 h) (by decide)
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hd.2.2.2 1 0, hd.2.2.2 1 1⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          refine ⟨?_, hd.2.2.2 0 0, hd.2.2.2 0 1⟩
          intro h
          have := hd.2.1 h
          simp at this
      have hsd : ((Finset.univ : Finset (Equiv.Perm (Fin 3))) \
          {s 0, s 1, t 0, t 1}).card =
          Fintype.card (Equiv.Perm (Fin 3)) - 4 := by
        rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, hT]
      rw [hsd, ct3_card]
    have hxy_sub : ({x, y} : Finset (Equiv.Perm (Fin 3))) ⊆
        (Finset.univ : Finset (Equiv.Perm (Fin 3))) \ {s 0, s 1, t 0, t 1} := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxmem
      · rw [Finset.mem_singleton.mp hz]
        exact hymem
    have hxy_card : ({x, y} : Finset (Equiv.Perm (Fin 3))).card = 2 :=
      Finset.card_pair hxy
    have heq : ({x, y} : Finset (Equiv.Perm (Fin 3))) =
        (Finset.univ : Finset (Equiv.Perm (Fin 3))) \ {s 0, s 1, t 0, t 1} := by
      apply Finset.eq_of_subset_of_card_le hxy_sub
      omega
    have hvxy : v ∈ ({x, y} : Finset (Equiv.Perm (Fin 3))) := by
      rw [heq]
      exact hvmem
    rcases Finset.mem_insert.mp hvxy with rfl | hvy
    · simp
    · rw [Finset.mem_singleton.mp hvy]
      simp
  have hone : ∀ i : Fin 2, i ≠ 0 → i = 1 := by decide
  refine ⟨fun i => if h : i = 0 then
      P0.copy (congrArg s h.symm) (congrArg t h.symm)
    else
      P1.copy (congrArg s (hone i h).symm) (congrArg t (hone i h).symm), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases h : i = 0
    · rw [dif_pos h, SimpleGraph.Walk.isPath_copy]
      exact dpc_edge_path h0
    · rw [dif_neg h, SimpleGraph.Walk.isPath_copy]
      exact hP1path
  · intro v
    rcases hcover v with hv | hv
    · refine ⟨0, ?_⟩
      dsimp only
      rw [dif_pos rfl, SimpleGraph.Walk.support_copy]
      exact hv
    · refine ⟨1, ?_⟩
      dsimp only
      rw [dif_neg (by decide : (1 : Fin 2) ≠ 0), SimpleGraph.Walk.support_copy]
      exact hv
  · intro a b hab v hv
    dsimp only at hv
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · exact hab (ha.trans hb.symm)
    · rw [dif_pos ha, SimpleGraph.Walk.support_copy, hP0s] at hv
      rw [dif_neg hb, SimpleGraph.Walk.support_copy, hP1s] at hv
      obtain ⟨h1', h2'⟩ := hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h1' h2'
      rcases h1' with rfl | rfl
      · rcases h2' with h2' | h2' | h2' | h2'
        · have := hd.2.1 h2'
          simp at this
        · exact (hxs 0) h2'.symm
        · exact (hys 0) h2'.symm
        · exact (hd.2.2.2 0 1) h2'
      · rcases h2' with h2' | h2' | h2' | h2'
        · exact (hd.2.2.2 1 0) h2'.symm
        · exact (hxt 0) h2'.symm
        · exact (hyt 0) h2'.symm
        · have := hd.2.2.1 h2'
          simp at this
    · rw [dif_pos hb, SimpleGraph.Walk.support_copy, hP0s] at hv
      rw [dif_neg ha, SimpleGraph.Walk.support_copy, hP1s] at hv
      obtain ⟨h1', h2'⟩ := hv
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h1' h2'
      rcases h2' with rfl | rfl
      · rcases h1' with h1' | h1' | h1' | h1'
        · have := hd.2.1 h1'
          simp at this
        · exact (hxs 0) h1'.symm
        · exact (hys 0) h1'.symm
        · exact (hd.2.2.2 0 1) h1'
      · rcases h1' with h1' | h1' | h1' | h1'
        · exact (hd.2.2.2 1 0) h1'.symm
        · exact (hxt 0) h1'.symm
        · exact (hyt 0) h1'.symm
        · have := hd.2.2.1 h1'
          simp at this
    · exact hab (by
        rw [hone a ha, hone b hb])

#print axioms hypercube_paired_two_base1
#print axioms hypercube_paired_two_base2
#print axioms completeTransposition3_paired_two

end Brualdi.Ledger
