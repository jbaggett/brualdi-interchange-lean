/-
Thm15.lean — Tier 3 (final stage): discharging axiom A1 (`coleman_thm15`).

Coleman et al. 2025, Theorem 1.5, by rank induction over `IsColemanTree`:
* rank 2 — part (a): Hamilton-laceable (`thm15_rank2`);
* rank 3 — part (b): paired 2-DPCs;
* rank 4 with small pieces — part (c): paired 3-DPCs;
* rank ≥ 4 with large pieces — Proposition 1.6 (`coleman_prop16`, Prop16Cases.lean).

Nothing here is wired into the mainline until the flip in Coleman.lean.
-/
import BrualdiLean.Prop16Cases

set_option linter.unusedSectionVars false

namespace Brualdi.Ledger

universe u

private theorem bool_eq_of_ne_not' {x c : Bool} (h : x ≠ !c) : x = c := by
  cases x <;> cases c <;> simp_all

private theorem bool_eq_not_of_ne' {x c : Bool} (h : x ≠ c) : x = !c := by
  cases x <;> cases c <;> simp_all

/-! ## Walk and coloring toolkit -/

/-- Two vertices on a common walk are reachable from each other. -/
theorem reachable_of_mem_support {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) :
    G.Reachable x y := by
  have hax : G.Reachable a x := ⟨p.takeUntil x hx⟩
  have hay : G.Reachable a y := ⟨p.takeUntil y hy⟩
  exact hax.symm.trans hay

/-- Exact class counts along an alternating list. -/
theorem alt_count {α : Type u} (f : α → Bool) :
    ∀ (l : List α), List.IsChain (fun x y => f x ≠ f y) l →
    ∀ (hne : l ≠ []) (c : Bool), f (l.head hne) = c →
    (l.filter (fun x => f x = c)).length = (l.length + 1) / 2 ∧
    (l.filter (fun x => f x = !c)).length = l.length / 2
  | [], _, hne, _, _ => absurd rfl hne
  | [a], _, _, c, hhead => by
    have ha : f a = c := hhead
    constructor
    · simp [ha]
    · have : ¬ (f a = !c) := by
        rw [ha]
        cases c <;> simp
      simp [this]
  | a :: b :: l, h, _, c, hhead => by
    obtain ⟨hne, htail⟩ := List.isChain_cons_cons.mp h
    have ha : f a = c := hhead
    have hb : f b = !c := by
      rw [ha] at hne
      cases hfb : f b <;> cases c <;> simp_all
    have ih := alt_count f (b :: l) htail (by simp) (!c) hb
    rw [Bool.not_not] at ih
    obtain ⟨ih1, ih2⟩ := ih
    have hfilc : ((a :: b :: l).filter (fun x => f x = c)).length
        = ((b :: l).filter (fun x => f x = c)).length + 1 := by
      rw [List.filter_cons]
      simp [ha]
    have hfilnc : ((a :: b :: l).filter (fun x => f x = !c)).length
        = ((b :: l).filter (fun x => f x = !c)).length := by
      rw [List.filter_cons]
      have : ¬ (f a = !c) := by
        rw [ha]
        cases c <;> simp
      simp [this]
    constructor
    · rw [hfilc, ih2]
      simp only [List.length_cons]
      omega
    · rw [hfilnc, ih1]
      simp only [List.length_cons]

/-- A graph carrying a Hamiltonian walk and a proper coloring on an even vertex set is
    equitable: the walk alternates. -/
theorem hamiltonian_even_equitable {W : Type u} [DecidableEq W] [Fintype W]
    {H : SimpleGraph W} {a b : W} {p : H.Walk a b} (hham : p.IsHamiltonian)
    {colH : W → Bool} (hp : IsProper2Coloring H colH)
    (heven : Even (Fintype.card W)) :
    Fintype.card {v : W // colH v = false} = Fintype.card {v : W // colH v = true} := by
  classical
  have hnd := hham.isPath.support_nodup
  have hchain : List.IsChain (fun x y => colH x ≠ colH y) p.support := by
    have h1 := p.isChain_adj_support
    exact h1.imp (fun {x y} hxy => hp x y hxy)
  have hlen : p.support.length = Fintype.card W := by
    have h1 : p.support.toFinset = Finset.univ := by
      ext w
      simp [hham.mem_support w]
    rw [← List.toFinset_card_of_nodup hnd, h1, Finset.card_univ]
  have hnenil : p.support ≠ [] := by
    have := p.start_mem_support
    intro h
    rw [h] at this
    exact absurd this (List.not_mem_nil)
  have hbridge : ∀ c : Bool, (p.support.filter (fun w => colH w = c)).length
      = Fintype.card {v : W // colH v = c} := by
    intro c
    rw [Fintype.card_subtype]
    have hnd2 : (p.support.filter (fun w => decide (colH w = c))).Nodup := hnd.filter _
    rw [← List.toFinset_card_of_nodup hnd2]
    congr 1
    ext w
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_univ,
      true_and, decide_eq_true_eq]
    exact and_iff_right (hham.mem_support w)
  obtain ⟨hc1, hc2⟩ := alt_count colH p.support hchain hnenil _ rfl
  set c0 := colH (p.support.head hnenil) with hc0
  have heq : (p.support.length + 1) / 2 = p.support.length / 2 := by
    obtain ⟨k, hk⟩ := heven
    rw [hlen] at *
    omega
  rw [heq] at hc1
  have hcc : Fintype.card {v : W // colH v = c0} = Fintype.card {v : W // colH v = !c0} := by
    rw [← hbridge, ← hbridge, hc1, hc2]
  cases hcase : c0
  · rw [hcase] at hcc
    simpa using hcc
  · rw [hcase] at hcc
    simpa using hcc.symm

/-! ## Rank-1 leaves -/

/-- A rank-1 leaf is Hamilton-laceable with respect to ANY proper coloring. -/
theorem colemanLeaf_lace {W : Type} [instW : DecidableEq W] [Fintype W] {H : SimpleGraph W}
    (hT : IsColemanTree H 1) (colH : W → Bool) (hp : IsProper2Coloring H colH) :
    IsHamLaceable H colH := by
  classical
  cases hT with
  | weld hr _ _ _ _ => omega
  | base hham hcard =>
    rename_i instD
    rw [Subsingleton.elim instD instW] at hham
    clear instD
    rcases hham with hconn | ⟨col', hp', hs', hl'⟩
    · intro u v hcne
      exact hconn u v (fun h => hcne (h ▸ rfl))
    · intro u v hcne
      have hne : u ≠ v := fun h => hcne (h ▸ rfl)
      -- there is a Hamiltonian path, so the graph is connected
      obtain ⟨a, ha⟩ := hs' false
      obtain ⟨b, hb⟩ := hs' true
      obtain ⟨p, hpham⟩ := hl' a b (by rw [ha, hb]; simp)
      have hnon : Nonempty W := ⟨a⟩
      have hconn : H.Connected :=
        ⟨fun x y => reachable_of_mem_support p (hpham.mem_support x)
          (hpham.mem_support y)⟩
      rcases proper2Coloring_eq_or_flip hconn hp' hp with hsame | hflip
      · exact hl' u v (by rw [hsame u, hsame v]; exact hcne)
      · refine hl' u v ?_
        rw [hflip u, hflip v]
        intro h
        apply hcne
        cases hcu : colH u <;> cases hcv : colH v <;> simp_all

/-- A rank-1 leaf on at least two vertices is equitable with respect to any proper
    coloring (its Hamiltonian path alternates). -/
theorem colemanLeaf_equitable {W : Type} [instW : DecidableEq W] [Fintype W]
    {H : SimpleGraph W} (hT : IsColemanTree H 1) {colH : W → Bool}
    (hp : IsProper2Coloring H colH) (hcard : 2 ≤ Fintype.card W) :
    IsEquitableBipartite H colH := by
  classical
  refine ⟨hp, ?_⟩
  cases hT with
  | weld hr _ _ _ _ => omega
  | base hham hcard' =>
    rename_i instD
    rw [Subsingleton.elim instD instW] at hham
    clear instD
    have heven : Even (Fintype.card W) := by
      rcases hcard' with h | h
      · rw [Nat.card_eq_fintype_card] at h
        exact absurd h (show Fintype.card W ≠ 1 by omega)
      · rwa [Nat.card_eq_fintype_card] at h
    -- extract some Hamiltonian path
    have hpath : ∃ (a b : W) (p : H.Walk a b), p.IsHamiltonian := by
      rcases hham with hconn | ⟨col', hp', hs', hl'⟩
      · obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp
          (show 1 < Fintype.card W by omega)
        obtain ⟨p, hpham⟩ := hconn a b hab
        exact ⟨a, b, p, hpham⟩
      · obtain ⟨a, ha⟩ := hs' false
        obtain ⟨b, hb⟩ := hs' true
        obtain ⟨p, hpham⟩ := hl' a b (by rw [ha, hb]; simp)
        exact ⟨a, b, p, hpham⟩
    obtain ⟨a, b, p, hpham⟩ := hpath
    exact hamiltonian_even_equitable hpham hp heven

/-! ## Transport through graph isomorphisms -/

/-- Paired covers transport backwards through a graph isomorphism. -/
theorem pairedKDPC_iso {V : Type} {W : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (colV : V → Bool) (colW : W → Bool)
    (hcol : ∀ v, colW (e v) = colV v) {k : ℕ}
    (h : IsPairedKDPCForOpposite H colW k) :
    IsPairedKDPCForOpposite G colV k := by
  classical
  intro s t hd
  have hd' : OppositeDemand colW (fun i => e (s i)) (fun i => e (t i)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      show colW (e (s i)) ≠ colW (e (t i))
      rw [hcol, hcol]
      exact hd.1 i
    · intro i j hij
      exact hd.2.1 (e.toEquiv.injective hij)
    · intro i j hij
      exact hd.2.2.1 (e.toEquiv.injective hij)
    · intro i j hij
      exact hd.2.2.2 i j (e.toEquiv.injective hij)
  obtain ⟨p, hp, hcov, hdisj⟩ := h _ _ hd'
  refine ⟨fun i => ((p i).map e.symm.toHom).copy (by simp) (by simp), ?_, ?_, ?_⟩
  · intro i
    rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective e.symm.toEquiv.injective (hp i)
  · intro x
    obtain ⟨i, hi⟩ := hcov (e x)
    refine ⟨i, ?_⟩
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    refine List.mem_map.mpr ⟨e x, hi, ?_⟩
    simp
  · intro i j hij x hx
    obtain ⟨hx1, hx2⟩ := hx
    dsimp only at hx1 hx2
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hx1
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hx2
    obtain ⟨y1, hy1, he1⟩ := List.mem_map.mp hx1
    obtain ⟨y2, hy2, he2⟩ := List.mem_map.mp hx2
    refine hdisj i j hij y1 ⟨hy1, ?_⟩
    have : y1 = y2 := by
      have h1 := he1.trans he2.symm
      exact e.symm.toEquiv.injective h1
    rwa [this]

/-! ## Rank 2: part (a) of the Theorem 1.5 base analysis -/

/-- **Coleman et al. 2025, Theorem 1.5 base (a)**: a rank-2 tree is Hamilton-laceable
    (as a paired 1-cover) with respect to any proper coloring. -/
theorem thm15_rank2 {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (col : V → Bool) (hT : IsColemanTree G 2) (hBB : IsProper2Coloring G col) :
    IsPairedKDPCForOpposite G col 1 := by
  classical
  cases hT with
  | @weld V' W' G' ell r Gs M hr hEll htl hM e =>
    have instFW : Fintype (Fin ell × W') := Fintype.ofEquiv V e.toEquiv
    have instDW : DecidableEq W' := Classical.decEq W'
    have hell0 : 0 < ell := by omega
    have instW : Fintype W' :=
      Fintype.ofInjective (fun w : W' => ((⟨0, hell0⟩ : Fin ell), w))
        (fun a b h => (Prod.ext_iff.mp h).2)
    apply pairedKDPC_iso e col (fun x => col (e.symm x)) (fun v => by simp)
    have hpW : IsProper2Coloring (weldGraph ell Gs M) (fun x => col (e.symm x)) := by
      intro x y hxy
      exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
    have htl1 : ∀ j, IsColemanTree (Gs j) 1 := by
      intro j
      have h := htl j
      simpa using h
    have hcopyP : ∀ j : Fin ell, IsProper2Coloring (Gs j)
        (fun w => col (e.symm (j, w))) :=
      fun j u v huv => hpW (j, u) (j, v) ((weldLift Gs M j).map_adj huv)
    have hlace : ∀ j : Fin ell, IsHamLaceable (Gs j) (fun w => col (e.symm (j, w))) :=
      fun j => colemanLeaf_lace (htl1 j) _ (hcopyP j)
    apply pairedKDPC_of_mono
    intro b s t hmono
    have hcolS : col (e.symm (s 0)) = b := hmono.1 0
    have hcolT : col (e.symm (t 0)) = !b := hmono.2.1 0
    by_cases hsame : (s 0).1 = (t 0).1
    · -- one copy: a single leaf Hamilton path
      have hpairT : ((s 0).1, (t 0).2) = t 0 := Prod.ext hsame rfl
      have hcne : col (e.symm ((s 0).1, (s 0).2)) ≠ col (e.symm ((s 0).1, (t 0).2)) := by
        rw [hpairT]
        show col (e.symm (s 0)) ≠ col (e.symm (t 0))
        rw [hcolS, hcolT]
        cases b <;> simp
      obtain ⟨p, hpham⟩ := hlace (s 0).1 (s 0).2 (t 0).2 hcne
      refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {(s 0).1}
        (fun i => ((p.map (weldLift Gs M (s 0).1)).copy rfl (Prod.ext hsame rfl)).copy
          (congrArg s (Fin.fin_one_eq_zero i).symm) (congrArg t (Fin.fin_one_eq_zero i).symm))
        (fun i => by
          rw [SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.isPath_copy]
          exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hpham.isPath)
        ?_ ?_ ?_
      · intro i x hx
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy,
          weldLift_support, mem_map_pair] at hx
        rw [Finset.mem_singleton]
        exact hx.1
      · intro x hxJ
        rw [Finset.mem_singleton] at hxJ
        refine ⟨0, ?_⟩
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy,
          weldLift_support, mem_map_pair]
        exact ⟨hxJ, hpham.mem_support x.2⟩
      · intro i j hij
        exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij
    · -- two copies
      by_cases hW1 : Fintype.card W' = 1
      · -- singleton leaves: properness forces exactly two copies, and the demand pair
        -- is the whole graph joined by its matching edge
        have hsub : Subsingleton W' := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hVne : Nonempty W' := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨w0⟩ := hVne
        have hell2 : ell = 2 := by
          by_contra hne2
          have h3 : 3 ≤ ell := by omega
          have hadj : ∀ (i j : Fin ell), i ≠ j →
              (weldGraph ell Gs M).Adj (i, w0) (j, w0) := by
            intro i j hij
            have h := weld_cross_adj (Gs := Gs) (M := M) hij w0
            have h2 : M i j w0 = w0 := Subsingleton.elim _ _
            rwa [h2] at h
          have hne01 : (⟨0, by omega⟩ : Fin ell) ≠ ⟨1, by omega⟩ := by
            intro h
            simpa using congrArg Fin.val h
          have hne02 : (⟨0, by omega⟩ : Fin ell) ≠ ⟨2, by omega⟩ := by
            intro h
            simpa using congrArg Fin.val h
          have hne12 : (⟨1, by omega⟩ : Fin ell) ≠ ⟨2, by omega⟩ := by
            intro h
            simpa using congrArg Fin.val h
          have h01 := hpW _ _ (hadj _ _ hne01)
          have h02 := hpW _ _ (hadj _ _ hne02)
          have h12 := hpW _ _ (hadj _ _ hne12)
          revert h01 h02 h12
          cases hc0 : col (e.symm ((⟨0, by omega⟩ : Fin ell), w0)) <;>
            cases hc1 : col (e.symm ((⟨1, by omega⟩ : Fin ell), w0)) <;>
            cases hc2 : col (e.symm ((⟨2, by omega⟩ : Fin ell), w0)) <;> simp_all
        have hadjst : (weldGraph ell Gs M).Adj (s 0) (t 0) := by
          have h := weld_cross_adj (Gs := Gs) (M := M) hsame (s 0).2
          have h2 : M (s 0).1 (t 0).1 (s 0).2 = (t 0).2 := Subsingleton.elim _ _
          rw [h2] at h
          exact h
        have hpath : (SimpleGraph.Walk.cons hadjst SimpleGraph.Walk.nil :
            (weldGraph ell Gs M).Walk (s 0) (t 0)).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          exact hmono.st_ne 0 0
        refine ⟨fun i => (SimpleGraph.Walk.cons hadjst SimpleGraph.Walk.nil).copy
          (congrArg s (Fin.fin_one_eq_zero i).symm) (congrArg t (Fin.fin_one_eq_zero i).symm),
          fun i => by rw [SimpleGraph.Walk.isPath_copy]; exact hpath, ?_, ?_⟩
        · intro x
          refine ⟨0, ?_⟩
          rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil]
          have hx2s : x.2 = (s 0).2 := Subsingleton.elim _ _
          by_cases hx1 : x.1 = (s 0).1
          · have : x = s 0 := Prod.ext hx1 hx2s
            rw [this]
            exact List.mem_cons_self ..
          · have hx1t : x.1 = (t 0).1 := by
              have hv1 : x.1.val < ell := x.1.isLt
              have hv2 : (s 0).1.val < ell := (s 0).1.isLt
              have hv3 : (t 0).1.val < ell := (t 0).1.isLt
              have hnev : x.1.val ≠ (s 0).1.val := fun h => hx1 (Fin.ext h)
              have hnev2 : (s 0).1.val ≠ (t 0).1.val := fun h => hsame (Fin.ext h)
              exact Fin.ext (by omega)
            have : x = t 0 := Prod.ext hx1t (Subsingleton.elim _ _)
            rw [this]
            exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
        · intro i j hij
          exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij
      · -- even leaves: route through a fresh opposite vertex and its matching partner
        have hW2 : 2 ≤ Fintype.card W' := by
          have h1 : 0 < Fintype.card W' := by
            have hne : Nonempty W' := ⟨(s 0).2⟩
            exact Fintype.card_pos_iff.mpr hne
          omega
        have hequit := colemanLeaf_equitable (htl1 (s 0).1) (hcopyP (s 0).1) hW2
        have hvex : ∃ v : W', col (e.symm ((s 0).1, v)) = !b := by
          have hcards : Fintype.card {w : W' // col (e.symm ((s 0).1, w)) = false}
              = Fintype.card {w : W' // col (e.symm ((s 0).1, w)) = true} := hequit.2
          have hsum : Fintype.card {w : W' // col (e.symm ((s 0).1, w)) = false}
              + Fintype.card {w : W' // col (e.symm ((s 0).1, w)) = true}
              = Fintype.card W' := by
            rw [Fintype.card_subtype, Fintype.card_subtype]
            have hsplit := Finset.card_filter_add_card_filter_not
              (s := (Finset.univ : Finset W'))
              (p := fun w => col (e.symm ((s 0).1, w)) = false)
            rw [Finset.card_univ] at hsplit
            rw [← hsplit]
            congr 1
            refine congrArg Finset.card ?_
            apply Finset.filter_congr
            intro w _
            cases hc : col (e.symm ((s 0).1, w)) <;> simp
          have hpos : 0 < Fintype.card {w : W' // col (e.symm ((s 0).1, w)) = !b} := by
            cases b <;> simp only [Bool.not_true, Bool.not_false] <;> omega
          obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.mp hpos
          exact ⟨v, hv⟩
        obtain ⟨v, hv⟩ := hvex
        obtain ⟨u, hu⟩ : ∃ u, u = M (s 0).1 (t 0).1 v := ⟨_, rfl⟩
        have hcolu : col (e.symm ((t 0).1, u)) = b := by
          have hadj := weld_cross_adj (Gs := Gs) (M := M) hsame v
          rw [← hu] at hadj
          have h := hpW _ _ hadj
          dsimp only at h
          rw [hv] at h
          exact bool_eq_of_ne_not' (Ne.symm h)
        have hcne1 : col (e.symm ((s 0).1, (s 0).2)) ≠ col (e.symm ((s 0).1, v)) := by
          show col (e.symm (s 0)) ≠ _
          rw [hcolS, hv]
          cases b <;> simp
        have hcne2 : col (e.symm ((t 0).1, u)) ≠ col (e.symm ((t 0).1, (t 0).2)) := by
          rw [hcolu]
          show _ ≠ col (e.symm (t 0))
          rw [hcolT]
          cases b <;> simp
        obtain ⟨p1, hp1⟩ := hlace (s 0).1 (s 0).2 v hcne1
        obtain ⟨p2, hp2⟩ := hlace (t 0).1 u (t 0).2 hcne2
        obtain ⟨R, hRp, hRs⟩ := weld_splice hsame p1 p2 hp1.isPath hp2.isPath hu
        refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {(s 0).1, (t 0).1}
          (fun i => (R.copy rfl rfl).copy
            (congrArg s (Fin.fin_one_eq_zero i).symm) (congrArg t (Fin.fin_one_eq_zero i).symm))
          (fun i => by
            rw [SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.isPath_copy]
            exact hRp) ?_ ?_ ?_
        · intro i x hx
          rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy, hRs,
            List.mem_append, mem_map_pair, mem_map_pair] at hx
          rw [Finset.mem_insert, Finset.mem_singleton]
          rcases hx with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1
        · intro x hxJ
          rw [Finset.mem_insert, Finset.mem_singleton] at hxJ
          refine ⟨0, ?_⟩
          rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy, hRs,
            List.mem_append, mem_map_pair, mem_map_pair]
          rcases hxJ with h | h
          · exact Or.inl ⟨h, hp1.mem_support x.2⟩
          · exact Or.inr ⟨h, hp2.mem_support x.2⟩
        · intro i j hij
          exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij

#print axioms Brualdi.Ledger.thm15_rank2

/-! ## Rank-2 pieces: evenness and equitability -/

/-- In a properly colored weld of singleton leaves there are exactly two copies. -/
theorem weld_singleton_two {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
    {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
    {colW : Fin ell × W' → Bool} (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hW1 : Fintype.card W' = 1) (hell : 2 ≤ ell) : ell = 2 := by
  classical
  have hsub : Subsingleton W' := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨w0⟩ : Nonempty W' := Fintype.card_pos_iff.mp (by omega)
  by_contra hne2
  have h3 : 3 ≤ ell := by omega
  have hadj : ∀ (i j : Fin ell), i ≠ j →
      (weldGraph ell Gs M).Adj (i, w0) (j, w0) := by
    intro i j hij
    have h := weld_cross_adj (Gs := Gs) (M := M) hij w0
    have h2 : M i j w0 = w0 := Subsingleton.elim _ _
    rwa [h2] at h
  have hne01 : (⟨0, by omega⟩ : Fin ell) ≠ ⟨1, by omega⟩ := by
    intro h
    simpa using congrArg Fin.val h
  have hne02 : (⟨0, by omega⟩ : Fin ell) ≠ ⟨2, by omega⟩ := by
    intro h
    simpa using congrArg Fin.val h
  have hne12 : (⟨1, by omega⟩ : Fin ell) ≠ ⟨2, by omega⟩ := by
    intro h
    simpa using congrArg Fin.val h
  have h01 := hpW _ _ (hadj _ _ hne01)
  have h02 := hpW _ _ (hadj _ _ hne02)
  have h12 := hpW _ _ (hadj _ _ hne12)
  revert h01 h02 h12
  cases hc0 : colW ((⟨0, by omega⟩ : Fin ell), w0) <;>
    cases hc1 : colW ((⟨1, by omega⟩ : Fin ell), w0) <;>
    cases hc2 : colW ((⟨2, by omega⟩ : Fin ell), w0) <;> simp_all

/-- A nonempty, properly colored rank-2 tree has an even number of vertices, at least two. -/
theorem colemanRank2_card {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {col : V → Bool} (hT : IsColemanTree G 2) (hBB : IsProper2Coloring G col)
    (hne : Nonempty V) : 2 ≤ Fintype.card V ∧ Even (Fintype.card V) := by
  classical
  cases hT with
  | @weld V' W' G' ell r Gs M hr hEll htl hM e =>
    have instDW : DecidableEq W' := Classical.decEq W'
    have hell0 : 0 < ell := by omega
    have instW : Fintype W' :=
      Fintype.ofInjective (fun w : W' => e.symm ((⟨0, hell0⟩ : Fin ell), w))
        (fun a b h => (Prod.ext_iff.mp (e.symm.toEquiv.injective h)).2)
    have hcardV : Fintype.card V = ell * Fintype.card W' := by
      rw [Fintype.card_congr e.toEquiv, Fintype.card_prod, Fintype.card_fin]
    have hWne : Nonempty W' := by
      obtain ⟨v⟩ := hne
      exact ⟨(e v).2⟩
    have hW0 : 0 < Fintype.card W' := Fintype.card_pos_iff.mpr hWne
    have hpW : IsProper2Coloring (weldGraph ell Gs M) (fun x => col (e.symm x)) := by
      intro x y hxy
      exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
    -- the leaves share the card of W'
    have hleaf := htl ⟨0, hell0⟩
    have hleafcard : Nat.card W' = 1 ∨ Even (Nat.card W') := by
      cases hleaf with
      | base hham hcard => exact hcard
      | weld hr' _ _ _ _ => omega
    rw [Nat.card_eq_fintype_card] at hleafcard
    rcases hleafcard with h1 | heven
    · have hell2 : ell = 2 := weld_singleton_two hpW h1 (by omega)
      constructor
      · rw [hcardV, hell2, h1]
      · rw [hcardV, hell2, h1]
        decide
    · constructor
      · obtain ⟨k, hk⟩ := heven
        have hk1 : 1 ≤ k := by omega
        calc 2 ≤ 1 * Fintype.card W' := by omega
        _ ≤ ell * Fintype.card W' := Nat.mul_le_mul_right _ (by omega)
        _ = Fintype.card V := hcardV.symm
      · rw [hcardV]
        exact heven.mul_left ell

/-- A nonempty, properly colored rank-2 tree is equitable. -/
theorem colemanRank2_equitable {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {col : V → Bool} (hT : IsColemanTree G 2) (hBB : IsProper2Coloring G col)
    (hne : Nonempty V) : IsEquitableBipartite G col := by
  classical
  refine ⟨hBB, ?_⟩
  obtain ⟨hcard2, heven⟩ := colemanRank2_card hT hBB hne
  -- the tree has an edge, so the coloring is not constant
  have hedge : ∃ u v : V, G.Adj u v := by
    cases hT with
    | @weld V' W' G' ell r Gs M hr hEll htl hM e =>
      have instDW : DecidableEq W' := Classical.decEq W'
      obtain ⟨v0⟩ := hne
      have hell1 : (0 : ℕ) < ell := by omega
      have instW : Fintype W' :=
        Fintype.ofInjective (fun w : W' => e.symm ((⟨0, hell1⟩ : Fin ell), w))
          (fun a b h => (Prod.ext_iff.mp (e.symm.toEquiv.injective h)).2)
      have hne01 : (⟨0, by omega⟩ : Fin ell) ≠ ⟨1, by omega⟩ := by
        intro h
        simpa using congrArg Fin.val h
      have hadj := weld_cross_adj (Gs := Gs) (M := M) hne01 (e v0).2
      exact ⟨e.symm ((⟨0, by omega⟩ : Fin ell), (e v0).2),
        e.symm ((⟨1, by omega⟩ : Fin ell), M _ _ (e v0).2),
        e.symm.map_rel_iff.mpr hadj⟩
  obtain ⟨u0, v0, hadj0⟩ := hedge
  have hlace : IsHamLaceable G col :=
    paired_one_opposite_iff_hamLaceable.mp (thm15_rank2 G col hT hBB)
  obtain ⟨p, hpham⟩ := hlace u0 v0 (hBB _ _ hadj0)
  exact hamiltonian_even_equitable hpham hBB heven

/-! ## The double split -/

/-- Split a path at an interior vertex `x` and then at a later vertex `z`: prefix,
    middle (from `x` to `z`), and suffix, with connecting adjacencies and a support
    partition. -/
theorem ham_double_split {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {a c : V}
    (p : G.Walk a c) (hp : p.IsPath) {x z : V} (hx : x ∈ p.support)
    (hz : z ∈ (p.dropUntil x hx).support)
    (hxa : x ≠ a) (hxz : x ≠ z) (hzc : z ≠ c) :
    ∃ (y1 z2 : V) (A : G.Walk a y1) (Mid : G.Walk x z) (D : G.Walk z2 c),
      A.IsPath ∧ Mid.IsPath ∧ D.IsPath ∧ G.Adj y1 x ∧ G.Adj z z2 ∧
      p.support = A.support ++ Mid.support ++ D.support := by
  classical
  have hT : (p.takeUntil x hx).IsPath := hp.takeUntil hx
  have hDr : (p.dropUntil x hx).IsPath := hp.dropUntil hx
  have hsupp : p.support = (p.takeUntil x hx).support ++ (p.dropUntil x hx).support.tail := by
    conv_lhs => rw [← p.take_spec hx]
    rw [SimpleGraph.Walk.support_append]
  -- peel x off the end of the take-part
  obtain ⟨y1, A, hA, hadj1, hTsupp, hxA⟩ :=
    path_peel_last (p.takeUntil x hx) hT hxa
  -- split the drop-part at z
  obtain ⟨y2, z2, C, D, hC, hD, hadj2, hadj3, hDrsupp⟩ :=
    path_split_interior (p.dropUntil x hx) hDr hz (Ne.symm hxz) hzc
  have hzC : z ∉ C.support := by
    intro hmem
    have hnd := hDr.support_nodup
    rw [hDrsupp] at hnd
    exact (List.nodup_append.mp hnd).2.2 z hmem z (List.mem_cons_self ..) rfl
  refine ⟨y1, z2, A, C.concat hadj2, D, hA, ?_, hD, hadj1, hadj3, ?_⟩
  · rw [SimpleGraph.Walk.concat_isPath_iff]
    exact ⟨hC, hzC⟩
  · rw [hsupp, hTsupp, hDrsupp, SimpleGraph.Walk.support_concat]
    have hChead : ∃ Ctail, C.support = x :: Ctail := ⟨C.support.tail,
      (SimpleGraph.Walk.cons_tail_support C).symm⟩
    obtain ⟨Ctail, hCt⟩ := hChead
    rw [hCt]
    simp

/-! ## Rank 3, part (b): the six cases

Throughout: `colW` properly colors the weld, every copy is Hamilton-laceable with respect
to the induced coloring (part (a) on the rank-2 pieces), and the demand is monochromatic
(`MonoDemand`), two pairs. -/

section Rank3Cases

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 1: every copy meets at most one pair. -/
theorem rank3_case1 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool), ∃ w, colW (j, w) = c)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    (hw : ∀ j, (weldWSet s t j).card ≤ 1) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔ (x.1 = (s i).1 ∨ x.1 = (t i).1) := by
    intro i
    have hcolS : colW (s i) = b := hmono.1 i
    have hcolT : colW (t i) = !b := hmono.2.1 i
    by_cases hsame : (s i).1 = (t i).1
    · have hcne : colW ((s i).1, (s i).2) ≠ colW ((s i).1, (t i).2) := by
        have hpair : ((s i).1, (t i).2) = t i := Prod.ext hsame rfl
        rw [hpair]
        show colW (s i) ≠ colW (t i)
        rw [hcolS, hcolT]
        cases b <;> simp
      obtain ⟨p, hpham⟩ := hlace (s i).1 (s i).2 (t i).2 hcne
      refine ⟨(p.map (weldLift Gs M (s i).1)).copy rfl (Prod.ext hsame rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hpham.isPath
      · intro x
        rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair]
        constructor
        · rintro ⟨h1, -⟩
          exact Or.inl h1
        · rintro (h1 | h1)
          · exact ⟨h1, hpham.mem_support x.2⟩
          · exact ⟨h1.trans hsame.symm, hpham.mem_support x.2⟩
    · obtain ⟨v, hv⟩ := hclass (s i).1 (!b)
      obtain ⟨u, hu⟩ : ∃ u, u = M (s i).1 (t i).1 v := ⟨_, rfl⟩
      have hcolu : colW ((t i).1, u) = b := by
        have hadj := weld_cross_adj (Gs := Gs) (M := M) hsame v
        rw [← hu] at hadj
        have h := hpW _ _ hadj
        rw [hv] at h
        exact bool_eq_of_ne_not' (Ne.symm h)
      have hcne1 : colW ((s i).1, (s i).2) ≠ colW ((s i).1, v) := by
        show colW (s i) ≠ _
        rw [hcolS, hv]
        cases b <;> simp
      have hcne2 : colW ((t i).1, u) ≠ colW ((t i).1, (t i).2) := by
        rw [hcolu]
        show _ ≠ colW (t i)
        rw [hcolT]
        cases b <;> simp
      obtain ⟨p1, hp1⟩ := hlace (s i).1 (s i).2 v hcne1
      obtain ⟨p2, hp2⟩ := hlace (t i).1 u (t i).2 hcne2
      obtain ⟨R, hRp, hRs⟩ := weld_splice hsame p1 p2 hp1.isPath hp2.isPath hu
      refine ⟨R.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hRp
      · intro x
        rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
          · exact Or.inl h1
          · exact Or.inr h1
        · rintro (h1 | h1)
          · exact Or.inl ⟨h1, hp1.mem_support x.2⟩
          · exact Or.inr ⟨h1, hp2.mem_support x.2⟩
  choose P hPp hPchar using hpaths
  have hdisjcopy : ∀ (i j : Fin 2), i ≠ j → ∀ jc : Fin ell,
      ((s i).1 = jc ∨ (t i).1 = jc) → ((s j).1 = jc ∨ (t j).1 = jc) → False := by
    intro i j hij jc h1 h2
    have hm1 : i ∈ weldWSet s t jc := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
    have hm2 : j ∈ weldWSet s t jc := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h2⟩
    have h2c : 2 ≤ (weldWSet s t jc).card := Finset.one_lt_card.mpr ⟨i, hm1, j, hm2, hij⟩
    have := hw jc
    omega
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0)
    {(s 0).1, (t 0).1, (s 1).1, (t 1).1} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with h | h <;> fin_cases r <;> simp_all
  · intro x hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with h | h | h | h
    · exact ⟨0, (hPchar 0 x).mpr (Or.inl h)⟩
    · exact ⟨0, (hPchar 0 x).mpr (Or.inr h)⟩
    · exact ⟨1, (hPchar 1 x).mpr (Or.inl h)⟩
    · exact ⟨1, (hPchar 1 x).mpr (Or.inr h)⟩
  · intro i j hij x hx
    refine hdisjcopy i j hij x.1 ?_ ?_
    · rcases (hPchar i x).mp hx.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rcases (hPchar j x).mp hx.2 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm

end Rank3Cases

/-- Of two distinct vertices on a path, one lies in the drop-part at the other. -/
theorem mem_dropUntil_or {V : Type} [DecidableEq V] {G : SimpleGraph V} {a c : V}
    (p : G.Walk a c) (hp : p.IsPath) {x z : V} (hx : x ∈ p.support) (hz : z ∈ p.support)
    (hxz : x ≠ z) :
    z ∈ (p.dropUntil x hx).support ∨ x ∈ (p.dropUntil z hz).support := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hz2, hx2⟩ := hcon
  have hsuppX : p.support
      = (p.takeUntil x hx).support ++ (p.dropUntil x hx).support.tail := by
    conv_lhs => rw [← p.take_spec hx]
    rw [SimpleGraph.Walk.support_append]
  have hsuppZ : p.support
      = (p.takeUntil z hz).support ++ (p.dropUntil z hz).support.tail := by
    conv_lhs => rw [← p.take_spec hz]
    rw [SimpleGraph.Walk.support_append]
  have hzT : z ∈ (p.takeUntil x hx).support := by
    have hmem := hz
    rw [hsuppX] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · exact absurd (List.mem_of_mem_tail h) hz2
  have hxT : x ∈ (p.takeUntil z hz).support := by
    have hmem := hx
    rw [hsuppZ] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · exact absurd (List.mem_of_mem_tail h) hx2
  have hpre1 : (p.takeUntil x hx).support <+: p.support := ⟨_, hsuppX.symm⟩
  have hpre2 : (p.takeUntil z hz).support <+: p.support := ⟨_, hsuppZ.symm⟩
  -- both take-parts end at their split vertex, uniquely
  have hne1 : (p.takeUntil x hx).support ≠ [] := SimpleGraph.Walk.support_ne_nil _
  have hne2 : (p.takeUntil z hz).support ≠ [] := SimpleGraph.Walk.support_ne_nil _
  have hlastX : (p.takeUntil x hx).support.dropLast ++ [x]
      = (p.takeUntil x hx).support := by
    have h := List.dropLast_append_getLast hne1
    rwa [SimpleGraph.Walk.getLast_support] at h
  have hlastZ : (p.takeUntil z hz).support.dropLast ++ [z]
      = (p.takeUntil z hz).support := by
    have h := List.dropLast_append_getLast hne2
    rwa [SimpleGraph.Walk.getLast_support] at h
  have hndX : x ∉ (p.takeUntil x hx).support.dropLast := by
    have hnd := (hp.takeUntil hx).support_nodup
    rw [← hlastX] at hnd
    exact fun hmem => (List.nodup_append.mp hnd).2.2 x hmem x (List.mem_singleton_self _) rfl
  have hndZ : z ∉ (p.takeUntil z hz).support.dropLast := by
    have hnd := (hp.takeUntil hz).support_nodup
    rw [← hlastZ] at hnd
    exact fun hmem => (List.nodup_append.mp hnd).2.2 z hmem z (List.mem_singleton_self _) rfl
  -- prefix totality forces a contradiction
  have hcontra : ∀ (l1 l2 : List V) (e1 e2 : V), l1 ++ [e1] <+: l2 ++ [e2] →
      e2 ∈ l1 ++ [e1] → e1 ≠ e2 → e2 ∉ l2 → False := by
    intro l1 l2 e1 e2 hpp hmem hne hnl
    have hlen : l1.length + 1 ≤ l2.length + 1 := by
      have h := hpp.length_le
      simpa using h
    by_cases heq : l1.length = l2.length
    · have hEq : l1 ++ [e1] = l2 ++ [e2] :=
        hpp.eq_of_length (by simp [heq])
      obtain ⟨-, h2⟩ := List.append_inj hEq (by simp [heq])
      exact hne (by simpa using h2)
    · have hstrict : l1 ++ [e1] <+: l2 := by
        rw [List.prefix_iff_eq_take] at hpp
        rw [List.take_append_of_le_length (by simp; omega)] at hpp
        exact hpp ▸ List.take_prefix _ _
      rcases List.mem_append.mp hmem with h | h
      · exact hnl (hstrict.subset (List.mem_append_left _ h))
      · rw [List.mem_singleton] at h
        exact hne (h.symm)
  rcases List.prefix_or_prefix_of_prefix hpre1 hpre2 with hpp | hpp
  · rw [← hlastX, ← hlastZ] at hpp
    exact hcontra _ _ x z hpp (hlastX.symm ▸ hzT) hxz hndZ
  · rw [← hlastX, ← hlastZ] at hpp
    exact hcontra _ _ z x hpp (hlastZ.symm ▸ hxT) (Ne.symm hxz) hndX

section Rank3Cases2

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Assembly for Case 2: given a decomposition of the `j0` Hamilton path into a prefix,
    a realized middle (pair 1), and a suffix, reroute pair 0 through a bridge copy. -/
private theorem rank3_case2_assemble
    (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    {j0 j' : Fin ell} (hj' : j' ≠ j0)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    (hS0 : (s 0).1 = j0) (hT0 : (t 0).1 = j0)
    {y1 z2 : W'} {A : (Gs j0).Walk (s 0).2 y1} {D : (Gs j0).Walk z2 (t 0).2}
    (hA : A.IsPath) (hD : D.IsPath)
    {MidL : List W'}
    (Mid2 : (weldGraph ell Gs M).Walk (s 1) (t 1)) (hMid2 : Mid2.IsPath)
    (hMid2char : ∀ x : Fin ell × W', x ∈ Mid2.support ↔ x.1 = j0 ∧ x.2 ∈ MidL)
    (hcover : ∀ w : W', w ∈ A.support ++ MidL ++ D.support)
    (hnd : (A.support ++ MidL ++ D.support).Nodup)
    (hyz : colW (j0, y1) ≠ colW (j0, z2)) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  have hndAM : ∀ w ∈ A.support, w ∉ MidL := by
    intro w hw hw2
    exact (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd)).2.2 w hw w
      (List.mem_append_left _ hw2) rfl
  have hndAD : ∀ w ∈ A.support, w ∉ D.support := by
    intro w hw hw2
    exact (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd)).2.2 w hw w
      (List.mem_append_right _ hw2) rfl
  have hndMD : ∀ w ∈ MidL, w ∉ D.support := by
    intro w hw hw2
    have h2 := (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd)).2.1
    exact (List.nodup_append.mp h2).2.2 w hw w hw2 rfl
  -- the bridge
  obtain ⟨y1s, hy1s⟩ : ∃ u, u = M j0 j' y1 := ⟨_, rfl⟩
  obtain ⟨z2s, hz2s⟩ : ∃ u, u = M j0 j' z2 := ⟨_, rfl⟩
  have hcy1s : colW (j', y1s) ≠ colW (j', z2s) := by
    have h1 := hpW _ _ (hy1s ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj') y1)
    have h2 := hpW _ _ (hz2s ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj') z2)
    intro h
    apply hyz
    have e1 : colW (j0, y1) = !colW (j', y1s) := bool_eq_not_of_ne' h1
    have e2 : colW (j0, z2) = !colW (j', z2s) := bool_eq_not_of_ne' h2
    rw [e1, e2, h]
  obtain ⟨Q, hQ⟩ := hlace j' y1s z2s hcy1s
  -- pair 0
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, y1), R.IsPath ∧
      R.support = A.support.map (fun w => (j0, w)) := by
    refine ⟨(A.map (weldLift Gs M j0)).copy (Prod.ext hS0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Q hR₀p hQ.isPath
    (hy1s ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj') y1)
    (by
      intro w' _ hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hj' hmem.1)
  obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ D hR₁p hD
    ((hz2s ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj') z2).symm)
    (by
      intro w' hw' hmem
      rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hndAD w' h2 hw'
      · exact hj' h1.symm)
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔
        ((x.1 = j0 ∧ ((i = 0 ∧ x.2 ∈ A.support ++ D.support) ∨ (i = 1 ∧ x.2 ∈ MidL))) ∨
          (x.1 = j' ∧ i = 0 ∧ x.2 ∈ Q.support)) := by
    intro i
    fin_cases i
    · refine ⟨R₂.copy rfl (Prod.ext hT0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₂p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s, List.mem_append,
          hR₀s, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_left _ h2⟩⟩
          · exact Or.inr ⟨h1, rfl, h2⟩
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_right _ h2⟩⟩
        · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, -, h2⟩)
          · rcases List.mem_append.mp h2 with h | h
            · exact Or.inl (Or.inl ⟨h1, h⟩)
            · exact Or.inr ⟨h1, h⟩
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · refine ⟨Mid2, hMid2, ?_⟩
      intro x
      constructor
      · intro hx
        obtain ⟨h1, h2⟩ := (hMid2char x).mp hx
        exact Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩
      · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨-, h0, -⟩)
        · exact absurd h0 (by decide)
        · exact (hMid2char x).mpr ⟨h1, h2⟩
        · exact absurd h0 (by decide)
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j0, j'} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl
    · have hmem := hcover xw
      rw [List.mem_append, List.mem_append] at hmem
      rcases hmem with (h | h) | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl
          ⟨rfl, List.mem_append_left _ h⟩⟩)⟩
      · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl
          ⟨rfl, List.mem_append_right _ h⟩⟩)⟩
    · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr ⟨rfl, rfl, hQ.mem_support xw⟩)⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, hi0, -⟩ <;>
      rcases h2 with ⟨hb1, ⟨hj0, hb2⟩ | ⟨hj1, hb2⟩⟩ | ⟨hb1, hj0, -⟩
    · exact hij (hi0.trans hj0.symm)
    · rcases List.mem_append.mp ha2 with h | h
      · exact hndAM x.2 h hb2
      · exact hndMD x.2 hb2 h
    · exact hj' (hb1.symm.trans ha1)
    · rcases List.mem_append.mp hb2 with h | h
      · exact hndAM x.2 h ha2
      · exact hndMD x.2 ha2 h
    · exact hij (hi1.trans hj1.symm)
    · exact hj' (hb1.symm.trans ha1)
    · exact hj' (ha1.symm.trans hb1)
    · exact hj' (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0.symm)

end Rank3Cases2

section Rank3Case2Main

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 2: all four demand vertices in one copy. -/
theorem rank3_case2 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hell : 2 ≤ ell)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j0 : Fin ell} (hall : ∀ i, (s i).1 = j0 ∧ (t i).1 = j0) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  obtain ⟨j', hj'⟩ : ∃ j' : Fin ell, j' ≠ j0 := by
    obtain ⟨j', hj'⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [Fintype.card_fin]; omega) j0
    exact ⟨j', hj'⟩
  -- pairwise distinct W'-coordinates
  have hpairS : ∀ i, (j0, (s i).2) = s i := fun i => Prod.ext (hall i).1.symm rfl
  have hpairT : ∀ i, (j0, (t i).2) = t i := fun i => Prod.ext (hall i).2.symm rfl
  have hne_s1s0 : (s 1).2 ≠ (s 0).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 1) (a₂ := 0)
      (Prod.ext ((hall 1).1.trans (hall 0).1.symm) h)
    exact absurd this (by decide)
  have hne_s1t0 : (s 1).2 ≠ (t 0).2 :=
    fun h => hmono.st_ne 1 0 (Prod.ext ((hall 1).1.trans (hall 0).2.symm) h)
  have hne_s1t1 : (s 1).2 ≠ (t 1).2 :=
    fun h => hmono.st_ne 1 1 (Prod.ext ((hall 1).1.trans (hall 1).2.symm) h)
  have hne_t1s0 : (t 1).2 ≠ (s 0).2 :=
    fun h => hmono.st_ne 0 1 (Prod.ext ((hall 0).1.trans (hall 1).2.symm) h.symm)
  have hne_t1t0 : (t 1).2 ≠ (t 0).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 1) (a₂ := 0)
      (Prod.ext ((hall 1).2.trans (hall 0).2.symm) h)
    exact absurd this (by decide)
  -- the master Hamilton path in j0
  have hcne : colW (j0, (s 0).2) ≠ colW (j0, (t 0).2) := by
    rw [hpairS 0, hpairT 0, hmono.1 0, hmono.2.1 0]
    cases b <;> simp
  obtain ⟨p, hpham⟩ := hlace j0 (s 0).2 (t 0).2 hcne
  have hx : (s 1).2 ∈ p.support := hpham.mem_support _
  have hz : (t 1).2 ∈ p.support := hpham.mem_support _
  have hcov : ∀ w : W', w ∈ p.support := hpham.mem_support
  rcases mem_dropUntil_or p hpham.isPath hx hz hne_s1t1 with hord | hord
  · -- s₁ precedes t₁
    obtain ⟨y1, z2, A, Mid, D, hA, hMid, hD, hadjy, hadjz, hpart⟩ :=
      ham_double_split p hpham.isPath hx hord hne_s1s0 hne_s1t1 hne_t1t0
    have hcy1 : colW (j0, y1) = !b := by
      have h : colW (j0, y1) ≠ colW (j0, (s 1).2) :=
        hpW _ _ ((weldLift Gs M j0).map_adj hadjy)
      have h2 : colW (j0, (s 1).2) = b := by rw [hpairS 1]; exact hmono.1 1
      rw [h2] at h
      exact bool_eq_not_of_ne' h
    have hcz2 : colW (j0, z2) = b := by
      have h : colW (j0, (t 1).2) ≠ colW (j0, z2) :=
        hpW _ _ ((weldLift Gs M j0).map_adj hadjz)
      have h2 : colW (j0, (t 1).2) = !b := by rw [hpairT 1]; exact hmono.2.1 1
      rw [h2] at h
      exact bool_eq_of_ne_not' (Ne.symm h)
    refine rank3_case2_assemble hpW hlace hj' hmono (hall 0).1 (hall 0).2 hA hD
      ((Mid.map (weldLift Gs M j0)).copy (hpairS 1) (hpairT 1)) ?_ ?_
      (fun w => hpart ▸ hcov w) (hpart ▸ hpham.isPath.support_nodup) ?_
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hMid
    · intro x
      rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair]
    · rw [hcy1, hcz2]
      cases b <;> simp
  · -- t₁ precedes s₁
    obtain ⟨y1, z2, A, Mid, D, hA, hMid, hD, hadjy, hadjz, hpart⟩ :=
      ham_double_split p hpham.isPath hz hord hne_t1s0 (Ne.symm hne_s1t1) hne_s1t0
    have hcy1 : colW (j0, y1) = b := by
      have h : colW (j0, y1) ≠ colW (j0, (t 1).2) :=
        hpW _ _ ((weldLift Gs M j0).map_adj hadjy)
      have h2 : colW (j0, (t 1).2) = !b := by rw [hpairT 1]; exact hmono.2.1 1
      rw [h2] at h
      exact bool_eq_of_ne_not' h
    have hcz2 : colW (j0, z2) = !b := by
      have h : colW (j0, (s 1).2) ≠ colW (j0, z2) :=
        hpW _ _ ((weldLift Gs M j0).map_adj hadjz)
      have h2 : colW (j0, (s 1).2) = b := by rw [hpairS 1]; exact hmono.1 1
      rw [h2] at h
      exact bool_eq_not_of_ne' (Ne.symm h)
    refine rank3_case2_assemble hpW hlace hj' hmono (hall 0).1 (hall 0).2 hA hD
      ((Mid.reverse.map (weldLift Gs M j0)).copy (hpairS 1) (hpairT 1)) ?_ ?_
      (fun w => hpart ▸ hcov w) (hpart ▸ hpham.isPath.support_nodup) ?_
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hMid.reverse
    · intro x
      rw [SimpleGraph.Walk.support_copy, weldLift_support]
      rw [SimpleGraph.Walk.support_reverse]
      constructor
      · intro hmem
        obtain ⟨w2, hw2, he⟩ := List.mem_map.mp hmem
        exact ⟨by rw [← he], by rw [← he]; simpa using List.mem_reverse.mp hw2⟩
      · rintro ⟨h1, h2⟩
        refine List.mem_map.mpr ⟨x.2, List.mem_reverse.mpr h2, ?_⟩
        rw [← h1]
    · rw [hcy1, hcz2]
      cases b <;> simp

end Rank3Case2Main

section Rank3Case3

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Assembly for Case 3: sources split a `j1` Hamilton path, targets and the second
    connector image split a `j2` Hamilton path, prefix and suffix reroute through `j3`. -/
private theorem rank3_case3_assemble
    (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    {j1 j2 j3 : Fin ell} (hj12 : j1 ≠ j2) (hj31 : j3 ≠ j1) (hj32 : j3 ≠ j2)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    (hS0 : (s 0).1 = j1) (hS1 : (s 1).1 = j1) (hT0 : (t 0).1 = j2) (hT1 : (t 1).1 = j2)
    {y2 v : W'} {A : (Gs j1).Walk (s 0).2 y2} {S1B : (Gs j1).Walk (s 1).2 v}
    (hA : A.IsPath) (hS1B : S1B.IsPath)
    (hcov1 : ∀ w : W', w ∈ A.support ++ S1B.support)
    (hnd1 : (A.support ++ S1B.support).Nodup)
    {yh zh : W'} {Ahat : (Gs j2).Walk (M j1 j2 y2) yh} {Dhat : (Gs j2).Walk zh (t 0).2}
    (hAhat : Ahat.IsPath) (hDhat : Dhat.IsPath)
    {MidL : List W'} {MidC : (Gs j2).Walk (M j1 j2 v) (t 1).2} (hMidC : MidC.IsPath)
    (hMidCs : ∀ w : W', w ∈ MidC.support ↔ w ∈ MidL)
    (hcov2 : ∀ w : W', w ∈ Ahat.support ++ MidL ++ Dhat.support)
    (hnd2 : (Ahat.support ++ MidL ++ Dhat.support).Nodup)
    (hyz : colW (j2, yh) ≠ colW (j2, zh)) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  have hndAS : ∀ w ∈ A.support, w ∉ S1B.support := by
    intro w hw hw2
    exact (List.nodup_append.mp hnd1).2.2 w hw w hw2 rfl
  have hndAM : ∀ w ∈ Ahat.support, w ∉ MidL := by
    intro w hw hw2
    exact (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd2)).2.2 w hw w
      (List.mem_append_left _ hw2) rfl
  have hndAD : ∀ w ∈ Ahat.support, w ∉ Dhat.support := by
    intro w hw hw2
    exact (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd2)).2.2 w hw w
      (List.mem_append_right _ hw2) rfl
  have hndMD : ∀ w ∈ MidL, w ∉ Dhat.support := by
    intro w hw hw2
    have h2 := (List.nodup_append.mp ((List.append_assoc _ _ _) ▸ hnd2)).2.1
    exact (List.nodup_append.mp h2).2.2 w hw w hw2 rfl
  -- the bridge in j3
  obtain ⟨yhs, hyhs⟩ : ∃ u, u = M j2 j3 yh := ⟨_, rfl⟩
  obtain ⟨zhs, hzhs⟩ : ∃ u, u = M j2 j3 zh := ⟨_, rfl⟩
  have hcbr : colW (j3, yhs) ≠ colW (j3, zhs) := by
    have h1 := hpW _ _ (hyhs ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) yh)
    have h2 := hpW _ _ (hzhs ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) zh)
    intro h
    apply hyz
    have e1 : colW (j2, yh) = !colW (j3, yhs) := bool_eq_not_of_ne' h1
    have e2 : colW (j2, zh) = !colW (j3, zhs) := bool_eq_not_of_ne' h2
    rw [e1, e2, h]
  obtain ⟨Q, hQ⟩ := hlace j3 yhs zhs hcbr
  -- pair 0: A (j1) + Ahat (j2) + Q (j3) + Dhat (j2)
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j1, y2), R.IsPath ∧
      R.support = A.support.map (fun w => (j1, w)) := by
    refine ⟨(A.map (weldLift Gs M j1)).copy (Prod.ext hS0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Ahat hR₀p hAhat
    (weld_cross_adj (Gs := Gs) (M := M) hj12 y2)
    (by
      intro w' _ hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hj12 hmem.1.symm)
  obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ Q hR₁p hQ.isPath
    (hyhs ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) yh)
    (by
      intro w' _ hmem
      rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj31 h1
      · exact hj32 h1)
  obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ Dhat hR₂p hDhat
    ((hzhs ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) zh).symm)
    (by
      intro w' hw' hmem
      rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
        mem_map_pair, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
      · exact hj12 h1.symm
      · exact hndAD w' h2 hw'
      · exact hj32 h1.symm)
  -- pair 1: S1B (j1) + MidC (j2)
  have hR0' : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j1, v), R.IsPath ∧
      R.support = S1B.support.map (fun w => (j1, w)) := by
    refine ⟨(S1B.map (weldLift Gs M j1)).copy (Prod.ext hS1.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hS1B
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀', hR₀'p, hR₀'s⟩ := hR0'
  obtain ⟨R₁', hR₁'p, hR₁'s⟩ := weld_splice_snoc R₀' MidC hR₀'p hMidC
    (weld_cross_adj (Gs := Gs) (M := M) hj12 v)
    (by
      intro w' _ hmem
      rw [hR₀'s, mem_map_pair] at hmem
      exact hj12 hmem.1.symm)
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔
        ((x.1 = j1 ∧ ((i = 0 ∧ x.2 ∈ A.support) ∨ (i = 1 ∧ x.2 ∈ S1B.support))) ∨
          (x.1 = j2 ∧ ((i = 0 ∧ x.2 ∈ Ahat.support ++ Dhat.support) ∨
            (i = 1 ∧ x.2 ∈ MidL))) ∨
          (x.1 = j3 ∧ i = 0 ∧ x.2 ∈ Q.support)) := by
    intro i
    fin_cases i
    · refine ⟨R₃.copy rfl (Prod.ext hT0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₃p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s, List.mem_append,
          hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair,
          mem_map_pair]
        constructor
        · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩
          · exact Or.inr (Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_left _ h2⟩⟩)
          · exact Or.inr (Or.inr ⟨h1, rfl, h2⟩)
          · exact Or.inr (Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_right _ h2⟩⟩)
        · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, -, h2⟩)
          · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
          · exact absurd h0 (by decide)
          · rcases List.mem_append.mp h2 with h | h
            · exact Or.inl (Or.inl (Or.inr ⟨h1, h⟩))
            · exact Or.inr ⟨h1, h⟩
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · refine ⟨R₁'.copy rfl (Prod.ext hT1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₁'p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₁'s, List.mem_append, hR₀'s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩
          · exact Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, (hMidCs x.2).mp h2⟩⟩)
        · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨-, h0, -⟩)
          · exact absurd h0 (by decide)
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact Or.inr ⟨h1, (hMidCs x.2).mpr h2⟩
          · exact absurd h0 (by decide)
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j1, j2, j3} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · rcases List.mem_append.mp (hcov1 xw) with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
    · have hmem := hcov2 xw
      rw [List.mem_append, List.mem_append] at hmem
      rcases hmem with (h | h) | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
          ⟨rfl, List.mem_append_left _ h⟩⟩))⟩
      · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩))⟩
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
          ⟨rfl, List.mem_append_right _ h⟩⟩))⟩
    · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, rfl,
        hQ.mem_support xw⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ |
      ⟨ha1, hi0, ha2⟩ <;>
      rcases h2 with ⟨hb1, ⟨hj0, hb2⟩ | ⟨hj1', hb2⟩⟩ | ⟨hb1, ⟨hj0, hb2⟩ | ⟨hj1', hb2⟩⟩ |
        ⟨hb1, hj0, hb2⟩
    · exact hij (hi0.trans hj0.symm)
    · exact hndAS x.2 ha2 hb2
    · exact hij (hi0.trans hj0.symm)
    · exact hj12 (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0.symm)
    · exact hndAS x.2 hb2 ha2
    · exact hij (hi1.trans hj1'.symm)
    · exact hj12 (ha1.symm.trans hb1)
    · exact hij (hi1.trans hj1'.symm)
    · exact hj31 (hb1.symm.trans ha1)
    · exact hij (hi0.trans hj0.symm)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hij (hi0.trans hj0.symm)
    · rcases List.mem_append.mp ha2 with h | h
      · exact hndAM x.2 h hb2
      · exact hndMD x.2 hb2 h
    · exact hij (hi0.trans hj0.symm)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hij (hi1.trans hj1'.symm)
    · rcases List.mem_append.mp hb2 with h | h
      · exact hndAM x.2 h ha2
      · exact hndMD x.2 ha2 h
    · exact hij (hi1.trans hj1'.symm)
    · exact hj32 (hb1.symm.trans ha1)
    · exact hij (hi0.trans hj0.symm)
    · exact hj31 (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0.symm)
    · exact hj32 (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0.symm)

end Rank3Case3

section Rank3Case3Main

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 3: both sources in one copy, both targets in another. -/
theorem rank3_case3 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool), ∃ w, colW (j, w) = c)
    (hell : 3 ≤ ell)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hS : ∀ i, (s i).1 = j1) (hT : ∀ i, (t i).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  obtain ⟨j3, hj31, hj32⟩ : ∃ j3, j3 ≠ j1 ∧ j3 ≠ j2 := by
    have hlt : ({j1, j2} : Finset (Fin ell)).card
        < (Finset.univ : Finset (Fin ell)).card := by
      have h1 : ({j1, j2} : Finset (Fin ell)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j3, -, hj3⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    rw [Finset.mem_insert, Finset.mem_singleton] at hj3
    exact ⟨j3, fun h => hj3 (Or.inl h), fun h => hj3 (Or.inr h)⟩
  have hcolS : ∀ i, colW (j1, (s i).2) = b := by
    intro i
    rw [show (j1, (s i).2) = s i from Prod.ext (hS i).symm rfl]
    exact hmono.1 i
  have hcolT : ∀ i, colW (j2, (t i).2) = !b := by
    intro i
    rw [show (j2, (t i).2) = t i from Prod.ext (hT i).symm rfl]
    exact hmono.2.1 i
  -- master path in j1, from s₀ to a fresh opposite vertex
  obtain ⟨v, hv⟩ := hclass j1 (!b)
  have hcne1 : colW (j1, (s 0).2) ≠ colW (j1, v) := by
    rw [hcolS 0, hv]
    cases b <;> simp
  obtain ⟨p1, hp1⟩ := hlace j1 (s 0).2 v hcne1
  have hne_s1s0 : (s 1).2 ≠ (s 0).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 1) (a₂ := 0) (Prod.ext ((hS 1).trans (hS 0).symm) h)
    exact absurd this (by decide)
  have hne_s1v : (s 1).2 ≠ v := by
    intro h
    have h1 := hcolS 1
    rw [h, hv] at h1
    cases b <;> simp at h1
  obtain ⟨y2, z2, A, B, hA, hB, hadjy, hadjz, hpart1⟩ :=
    path_split_interior p1 hp1.isPath (hp1.mem_support (s 1).2) hne_s1s0 hne_s1v
  have hnd1' : (A.support ++ (s 1).2 :: B.support).Nodup :=
    hpart1 ▸ hp1.isPath.support_nodup
  have hs1B : (s 1).2 ∉ B.support := by
    have h2 := (List.nodup_append.mp hnd1').2.1
    rw [List.nodup_cons] at h2
    exact h2.1
  have hS1Bp : (SimpleGraph.Walk.cons hadjz B).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hB, hs1B⟩
  -- connector colors and images
  have hcy2 : colW (j1, y2) = !b := by
    have h : colW (j1, y2) ≠ colW (j1, (s 1).2) :=
      hpW _ _ ((weldLift Gs M j1).map_adj hadjy)
    rw [hcolS 1] at h
    exact bool_eq_not_of_ne' h
  have hcolc1s : colW (j2, M j1 j2 y2) = b := by
    have h : colW (j1, y2) ≠ colW (j2, M j1 j2 y2) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) hj12 y2)
    rw [hcy2] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  have hcolc2s : colW (j2, M j1 j2 v) = b := by
    have h : colW (j1, v) ≠ colW (j2, M j1 j2 v) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) hj12 v)
    rw [hv] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  -- master path in j2
  have hcne2 : colW (j2, M j1 j2 y2) ≠ colW (j2, (t 0).2) := by
    rw [hcolc1s, hcolT 0]
    cases b <;> simp
  obtain ⟨p2, hp2⟩ := hlace j2 (M j1 j2 y2) (t 0).2 hcne2
  have hne_vy2 : v ≠ y2 := by
    intro h
    exact (List.nodup_append.mp hnd1').2.2 y2 A.end_mem_support v
      (List.mem_cons_of_mem _ B.end_mem_support) h.symm
  have hne_c2c1 : M j1 j2 v ≠ M j1 j2 y2 := fun h => hne_vy2 ((M j1 j2).injective h)
  have hne_c2t1 : M j1 j2 v ≠ (t 1).2 := by
    intro h
    have h1 := hcolc2s
    rw [h, hcolT 1] at h1
    cases b <;> simp at h1
  have hne_c2t0 : M j1 j2 v ≠ (t 0).2 := by
    intro h
    have h1 := hcolc2s
    rw [h, hcolT 0] at h1
    cases b <;> simp at h1
  have hne_t1c1 : (t 1).2 ≠ M j1 j2 y2 := by
    intro h
    have h1 := hcolT 1
    rw [h, hcolc1s] at h1
    cases b <;> simp at h1
  have hne_t1t0 : (t 1).2 ≠ (t 0).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 1) (a₂ := 0) (Prod.ext ((hT 1).trans (hT 0).symm) h)
    exact absurd this (by decide)
  have hcov1 : ∀ w : W', w ∈ A.support ++ (SimpleGraph.Walk.cons hadjz B).support := by
    intro w
    have h := hp1.mem_support w
    rw [hpart1] at h
    rw [SimpleGraph.Walk.support_cons]
    exact h
  have hnd1 : (A.support ++ (SimpleGraph.Walk.cons hadjz B).support).Nodup := by
    rw [SimpleGraph.Walk.support_cons]
    exact hnd1'
  rcases mem_dropUntil_or p2 hp2.isPath (hp2.mem_support (M j1 j2 v))
    (hp2.mem_support (t 1).2) hne_c2t1 with hord | hord
  · -- the connector image precedes t₁
    obtain ⟨yh, zh, Ahat, MidB, Dhat, hAhat, hMidB, hDhat, hadjyh, hadjzh, hpart2⟩ :=
      ham_double_split p2 hp2.isPath (hp2.mem_support (M j1 j2 v)) hord
        hne_c2c1 hne_c2t1 hne_t1t0
    have hyz : colW (j2, yh) ≠ colW (j2, zh) := by
      have h1 : colW (j2, yh) ≠ colW (j2, M j1 j2 v) :=
        hpW _ _ ((weldLift Gs M j2).map_adj hadjyh)
      have h2 : colW (j2, (t 1).2) ≠ colW (j2, zh) :=
        hpW _ _ ((weldLift Gs M j2).map_adj hadjzh)
      rw [hcolc2s] at h1
      rw [hcolT 1] at h2
      have e1 := bool_eq_not_of_ne' h1
      have e2 := bool_eq_of_ne_not' (Ne.symm h2)
      rw [e1, e2]
      cases b <;> simp
    exact rank3_case3_assemble hpW hlace hj12 hj31 hj32 hmono (hS 0) (hS 1)
      (hT 0) (hT 1) hA hS1Bp hcov1 hnd1 hAhat hDhat hMidB
      (fun w => Iff.rfl) (fun w => hpart2 ▸ hp2.mem_support w)
      (hpart2 ▸ hp2.isPath.support_nodup) hyz
  · -- t₁ precedes the connector image
    obtain ⟨yh, zh, Ahat, MidB, Dhat, hAhat, hMidB, hDhat, hadjyh, hadjzh, hpart2⟩ :=
      ham_double_split p2 hp2.isPath (hp2.mem_support (t 1).2) hord
        hne_t1c1 (Ne.symm hne_c2t1) hne_c2t0
    have hyz : colW (j2, yh) ≠ colW (j2, zh) := by
      have h1 : colW (j2, yh) ≠ colW (j2, (t 1).2) :=
        hpW _ _ ((weldLift Gs M j2).map_adj hadjyh)
      have h2 : colW (j2, M j1 j2 v) ≠ colW (j2, zh) :=
        hpW _ _ ((weldLift Gs M j2).map_adj hadjzh)
      rw [hcolT 1] at h1
      rw [hcolc2s] at h2
      have e1 := bool_eq_of_ne_not' h1
      have e2 := bool_eq_not_of_ne' (Ne.symm h2)
      rw [e1, e2]
      cases b <;> simp
    refine rank3_case3_assemble hpW hlace hj12 hj31 hj32 hmono (hS 0) (hS 1)
      (hT 0) (hT 1) hA hS1Bp hcov1 hnd1 hAhat hDhat
      (MidC := MidB.reverse.copy rfl rfl) ?_ ?_
      (fun w => hpart2 ▸ hp2.mem_support w)
      (hpart2 ▸ hp2.isPath.support_nodup) hyz
    · rw [SimpleGraph.Walk.isPath_copy]
      exact hMidB.reverse
    · intro w
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse]

end Rank3Case3Main

section Rank3Case4

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 4, both targets outside the source copy. -/
private theorem rank3_case4_bothout
    (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool), ∃ w, colW (j, w) = c)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hT0 : (t 0).1 ≠ j0) (hT1 : (t 1).1 ≠ j0) (hTT : (t 0).1 ≠ (t 1).1) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  have hcolS : ∀ i, colW (j0, (s i).2) = b := by
    intro i
    rw [show (j0, (s i).2) = s i from Prod.ext (hS i).symm rfl]
    exact hmono.1 i
  obtain ⟨v, hv⟩ := hclass j0 (!b)
  have hcne1 : colW (j0, (s 0).2) ≠ colW (j0, v) := by
    rw [hcolS 0, hv]
    cases b <;> simp
  obtain ⟨p1, hp1⟩ := hlace j0 (s 0).2 v hcne1
  have hne_s1s0 : (s 1).2 ≠ (s 0).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 1) (a₂ := 0) (Prod.ext ((hS 1).trans (hS 0).symm) h)
    exact absurd this (by decide)
  have hne_s1v : (s 1).2 ≠ v := by
    intro h
    have h1 := hcolS 1
    rw [h, hv] at h1
    cases b <;> simp at h1
  obtain ⟨y2, z2, A, B, hA, hB, hadjy, hadjz, hpart1⟩ :=
    path_split_interior p1 hp1.isPath (hp1.mem_support (s 1).2) hne_s1s0 hne_s1v
  have hnd1' : (A.support ++ (s 1).2 :: B.support).Nodup :=
    hpart1 ▸ hp1.isPath.support_nodup
  have hS1Bp : (SimpleGraph.Walk.cons hadjz B).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨hB, ?_⟩
    have h2 := (List.nodup_append.mp hnd1').2.1
    rw [List.nodup_cons] at h2
    exact h2.1
  -- connector colors
  have hcy2 : colW (j0, y2) = !b := by
    have h : colW (j0, y2) ≠ colW (j0, (s 1).2) :=
      hpW _ _ ((weldLift Gs M j0).map_adj hadjy)
    rw [hcolS 1] at h
    exact bool_eq_not_of_ne' h
  have hcy2s : colW ((t 0).1, M j0 (t 0).1 y2) = b := by
    have h : colW (j0, y2) ≠ colW ((t 0).1, M j0 (t 0).1 y2) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT0) y2)
    rw [hcy2] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  have hcvs : colW ((t 1).1, M j0 (t 1).1 v) = b := by
    have h : colW (j0, v) ≠ colW ((t 1).1, M j0 (t 1).1 v) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT1) v)
    rw [hv] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  -- target-copy Hamilton paths
  have hcolT : ∀ i, colW ((t i).1, (t i).2) = !b := by
    intro i
    exact hmono.2.1 i
  have hcne2 : colW ((t 0).1, M j0 (t 0).1 y2) ≠ colW ((t 0).1, (t 0).2) := by
    rw [hcy2s, hcolT 0]
    cases b <;> simp
  obtain ⟨q0, hq0⟩ := hlace (t 0).1 (M j0 (t 0).1 y2) (t 0).2 hcne2
  have hcne3 : colW ((t 1).1, M j0 (t 1).1 v) ≠ colW ((t 1).1, (t 1).2) := by
    rw [hcvs, hcolT 1]
    cases b <;> simp
  obtain ⟨q1, hq1⟩ := hlace (t 1).1 (M j0 (t 1).1 v) (t 1).2 hcne3
  -- assemble
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, y2), R.IsPath ∧
      R.support = A.support.map (fun w => (j0, w)) := by
    refine ⟨(A.map (weldLift Gs M j0)).copy (Prod.ext (hS 0).symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q0 hR₀p hq0.isPath
    (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT0) y2)
    (by
      intro w' _ hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hT0 hmem.1)
  have hR0' : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j0, v), R.IsPath ∧
      R.support = ((s 1).2 :: B.support).map (fun w => (j0, w)) := by
    refine ⟨((SimpleGraph.Walk.cons hadjz B).map (weldLift Gs M j0)).copy
      (Prod.ext (hS 1).symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hS1Bp
    · rw [SimpleGraph.Walk.support_copy, weldLift_support, SimpleGraph.Walk.support_cons]
  obtain ⟨R₀', hR₀'p, hR₀'s⟩ := hR0'
  obtain ⟨R₁', hR₁'p, hR₁'s⟩ := weld_splice_snoc R₀' q1 hR₀'p hq1.isPath
    (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT1) v)
    (by
      intro w' _ hmem
      rw [hR₀'s, mem_map_pair] at hmem
      exact hT1 hmem.1)
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔
        ((x.1 = j0 ∧ ((i = 0 ∧ x.2 ∈ A.support) ∨
            (i = 1 ∧ x.2 ∈ (s 1).2 :: B.support))) ∨
          (x.1 = (t 0).1 ∧ i = 0 ∧ x.2 ∈ q0.support) ∨
          (x.1 = (t 1).1 ∧ i = 1 ∧ x.2 ∈ q1.support)) := by
    intro i
    fin_cases i
    · refine ⟨R₁.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₁p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩
          · exact Or.inr (Or.inl ⟨h1, rfl, h2⟩)
        · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, -, h2⟩ | ⟨-, h0, -⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
    · refine ⟨R₁'.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₁'p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₁'s, List.mem_append, hR₀'s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩
          · exact Or.inr (Or.inr ⟨h1, rfl, h2⟩)
        · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨-, h0, -⟩ | ⟨h1, -, h2⟩)
          · exact absurd h0 (by decide)
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j0, (t 0).1, (t 1).1} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · have h := hp1.mem_support xw
      rw [hpart1] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
    · exact ⟨0, (hPchar 0 ((t 0).1, xw)).mpr (Or.inr (Or.inl ⟨rfl, rfl,
        hq0.mem_support xw⟩))⟩
    · exact ⟨1, (hPchar 1 ((t 1).1, xw)).mpr (Or.inr (Or.inr ⟨rfl, rfl,
        hq1.mem_support xw⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, hi0, ha2⟩ | ⟨ha1, hi1, ha2⟩ <;>
      rcases h2 with ⟨hb1, ⟨hj0', hb2⟩ | ⟨hj1', hb2⟩⟩ | ⟨hb1, hj0', hb2⟩ |
        ⟨hb1, hj1', hb2⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact (List.nodup_append.mp hnd1').2.2 x.2 ha2 x.2 hb2 rfl
    · exact hij (hi0.trans hj0'.symm)
    · exact hT1 (hb1.symm.trans ha1)
    · exact (List.nodup_append.mp hnd1').2.2 x.2 hb2 x.2 ha2 rfl
    · exact hij (hi1.trans hj1'.symm)
    · exact hT0 (hb1.symm.trans ha1)
    · exact hij (hi1.trans hj1'.symm)
    · exact hij (hi0.trans hj0'.symm)
    · exact hT0 (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0'.symm)
    · exact hTT (ha1.symm.trans hb1)
    · exact hT1 (ha1.symm.trans hb1)
    · exact hij (hi1.trans hj1'.symm)
    · exact hTT (hb1.symm.trans ha1)
    · exact hij (hi1.trans hj1'.symm)

end Rank3Case4

section Rank3Case4b

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 4, first target inside the source copy: reroute around the second source's
    freed neighbors through a fresh copy. -/
private theorem rank3_case4_tin
    (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hell : 3 ≤ ell)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hT0 : (t 0).1 = j0) (hT1 : (t 1).1 ≠ j0) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  obtain ⟨j3, hj30, hj3B⟩ : ∃ j3, j3 ≠ j0 ∧ j3 ≠ (t 1).1 := by
    have hlt : ({j0, (t 1).1} : Finset (Fin ell)).card
        < (Finset.univ : Finset (Fin ell)).card := by
      have h1 : ({j0, (t 1).1} : Finset (Fin ell)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j3, -, hj3⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    rw [Finset.mem_insert, Finset.mem_singleton] at hj3
    exact ⟨j3, fun h => hj3 (Or.inl h), fun h => hj3 (Or.inr h)⟩
  have hcolS : ∀ i, colW (j0, (s i).2) = b := by
    intro i
    rw [show (j0, (s i).2) = s i from Prod.ext (hS i).symm rfl]
    exact hmono.1 i
  have hcolT0 : colW (j0, (t 0).2) = !b := by
    rw [show (j0, (t 0).2) = t 0 from Prod.ext hT0.symm rfl]
    exact hmono.2.1 0
  -- master path in j0 between the pair-0 endpoints
  have hcne1 : colW (j0, (s 0).2) ≠ colW (j0, (t 0).2) := by
    rw [hcolS 0, hcolT0]
    cases b <;> simp
  obtain ⟨p1, hp1⟩ := hlace j0 (s 0).2 (t 0).2 hcne1
  have hne_s1s0 : (s 1).2 ≠ (s 0).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 1) (a₂ := 0) (Prod.ext ((hS 1).trans (hS 0).symm) h)
    exact absurd this (by decide)
  have hne_s1t0 : (s 1).2 ≠ (t 0).2 :=
    fun h => hmono.st_ne 1 0 (Prod.ext ((hS 1).trans hT0.symm) h)
  obtain ⟨v2, v1', A', Bsuf, hA', hBsuf, hadjy, hadjz, hpart1⟩ :=
    path_split_interior p1 hp1.isPath (hp1.mem_support (s 1).2) hne_s1s0 hne_s1t0
  have hnd1' : (A'.support ++ (s 1).2 :: Bsuf.support).Nodup :=
    hpart1 ▸ hp1.isPath.support_nodup
  -- colors around the split
  have hcv2 : colW (j0, v2) = !b := by
    have h : colW (j0, v2) ≠ colW (j0, (s 1).2) :=
      hpW _ _ ((weldLift Gs M j0).map_adj hadjy)
    rw [hcolS 1] at h
    exact bool_eq_not_of_ne' h
  have hcv1' : colW (j0, v1') = !b := by
    have h : colW (j0, (s 1).2) ≠ colW (j0, v1') :=
      hpW _ _ ((weldLift Gs M j0).map_adj hadjz)
    rw [hcolS 1] at h
    exact bool_eq_not_of_ne' (Ne.symm h)
  have hne_v2s0 : v2 ≠ (s 0).2 := by
    intro h
    have h1 := hcv2
    rw [h, hcolS 0] at h1
    cases b <;> simp at h1
  obtain ⟨u1, A'', hA'', hadju, hA'supp, hv2A''⟩ := path_peel_last A' hA' hne_v2s0
  have hcu1 : colW (j0, u1) = b := by
    have h : colW (j0, u1) ≠ colW (j0, v2) :=
      hpW _ _ ((weldLift Gs M j0).map_adj hadju)
    rw [hcv2] at h
    exact bool_eq_of_ne_not' h
  -- the bridge in j3
  have hcu1s : colW (j3, M j0 j3 u1) = !b := by
    have h : colW (j0, u1) ≠ colW (j3, M j0 j3 u1) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) u1)
    rw [hcu1] at h
    exact bool_eq_not_of_ne' (Ne.symm h)
  have hcv1s : colW (j3, M j0 j3 v1') = b := by
    have h : colW (j0, v1') ≠ colW (j3, M j0 j3 v1') :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) v1')
    rw [hcv1'] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  have hcneQ : colW (j3, M j0 j3 u1) ≠ colW (j3, M j0 j3 v1') := by
    rw [hcu1s, hcv1s]
    cases b <;> simp
  obtain ⟨Q, hQ⟩ := hlace j3 (M j0 j3 u1) (M j0 j3 v1') hcneQ
  -- the second pair's target-copy path
  have hcv2s : colW ((t 1).1, M j0 (t 1).1 v2) = b := by
    have h : colW (j0, v2) ≠ colW ((t 1).1, M j0 (t 1).1 v2) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT1) v2)
    rw [hcv2] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  have hcneq1 : colW ((t 1).1, M j0 (t 1).1 v2) ≠ colW ((t 1).1, (t 1).2) := by
    rw [hcv2s]
    have h2 : colW ((t 1).1, (t 1).2) = !b := hmono.2.1 1
    rw [h2]
    cases b <;> simp
  obtain ⟨q1, hq1⟩ := hlace (t 1).1 (M j0 (t 1).1 v2) (t 1).2 hcneq1
  -- pair 0: A'' + Q + Bsuf
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, u1), R.IsPath ∧
      R.support = A''.support.map (fun w => (j0, w)) := by
    refine ⟨(A''.map (weldLift Gs M j0)).copy (Prod.ext (hS 0).symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA''
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Q hR₀p hQ.isPath
    (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) u1)
    (by
      intro w' _ hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hj30 hmem.1)
  obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ Bsuf hR₁p hBsuf
    ((weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) v1').symm)
    (by
      intro w' hw' hmem
      rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
      · refine (List.nodup_append.mp hnd1').2.2 w' ?_ w'
          (List.mem_cons_of_mem _ hw') rfl
        rw [hA'supp]
        exact List.mem_append_left _ h2
      · exact hj30 h1.symm)
  -- pair 1: the freed edge plus the target-copy path
  have hs1v2p : (SimpleGraph.Walk.cons hadjy.symm SimpleGraph.Walk.nil :
      (Gs j0).Walk (s 1).2 v2).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    intro h
    have h1 := hcolS 1
    rw [h, hcv2] at h1
    cases b <;> simp at h1
  have hR0' : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j0, v2), R.IsPath ∧
      R.support = [(s 1).2, v2].map (fun w => (j0, w)) := by
    refine ⟨((SimpleGraph.Walk.cons hadjy.symm SimpleGraph.Walk.nil).map
      (weldLift Gs M j0)).copy (Prod.ext (hS 1).symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hs1v2p
    · rw [SimpleGraph.Walk.support_copy, weldLift_support, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil]
  obtain ⟨R₀', hR₀'p, hR₀'s⟩ := hR0'
  obtain ⟨R₁', hR₁'p, hR₁'s⟩ := weld_splice_snoc R₀' q1 hR₀'p hq1.isPath
    (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hT1) v2)
    (by
      intro w' _ hmem
      rw [hR₀'s, mem_map_pair] at hmem
      exact hT1 hmem.1)
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔
        ((x.1 = j0 ∧ ((i = 0 ∧ x.2 ∈ A''.support ++ Bsuf.support) ∨
            (i = 1 ∧ x.2 ∈ [(s 1).2, v2]))) ∨
          (x.1 = j3 ∧ i = 0 ∧ x.2 ∈ Q.support) ∨
          (x.1 = (t 1).1 ∧ i = 1 ∧ x.2 ∈ q1.support)) := by
    intro i
    fin_cases i
    · refine ⟨R₂.copy rfl (Prod.ext hT0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₂p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s, List.mem_append,
          hR₀s, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_left _ h2⟩⟩
          · exact Or.inr (Or.inl ⟨h1, rfl, h2⟩)
          · exact Or.inl ⟨h1, Or.inl ⟨rfl, List.mem_append_right _ h2⟩⟩
        · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, -, h2⟩ | ⟨-, h0, -⟩)
          · rcases List.mem_append.mp h2 with h | h
            · exact Or.inl (Or.inl ⟨h1, h⟩)
            · exact Or.inr ⟨h1, h⟩
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · exact absurd h0 (by decide)
    · refine ⟨R₁'.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₁'p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₁'s, List.mem_append, hR₀'s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩
          · exact Or.inr (Or.inr ⟨h1, rfl, h2⟩)
        · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨-, h0, -⟩ | ⟨h1, -, h2⟩)
          · exact absurd h0 (by decide)
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  have hdisj_j0 : ∀ w : W', w ∈ A''.support ++ Bsuf.support → w ∈ [(s 1).2, v2] → False := by
    intro w hw hw2
    rcases List.mem_append.mp hw with h | h
    · rcases List.mem_cons.mp hw2 with h2 | h2
      · refine (List.nodup_append.mp hnd1').2.2 w ?_ w (h2 ▸ List.mem_cons_self ..) rfl
        rw [hA'supp]
        exact List.mem_append_left _ h
      · rw [List.mem_singleton] at h2
        subst h2
        exact hv2A'' h
    · rcases List.mem_cons.mp hw2 with h2 | h2
      · have h3 := (List.nodup_append.mp hnd1').2.1
        rw [List.nodup_cons] at h3
        exact h3.1 (h2 ▸ h)
      · rw [List.mem_singleton] at h2
        refine (List.nodup_append.mp hnd1').2.2 w ?_ w
          (List.mem_cons_of_mem _ h) rfl
        rw [hA'supp, h2]
        exact List.mem_append_right _ (List.mem_singleton_self _)
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j0, j3, (t 1).1} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · have h := hp1.mem_support xw
      rw [hpart1] at h
      rcases List.mem_append.mp h with h | h
      · rw [hA'supp] at h
        rcases List.mem_append.mp h with h | h
        · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl
            ⟨rfl, List.mem_append_left _ h⟩⟩)⟩
        · rw [List.mem_singleton] at h
          exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr
            ⟨rfl, by rw [h]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩⟩)⟩
      · rcases List.mem_cons.mp h with h | h
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr
            ⟨rfl, by rw [h]; exact List.mem_cons_self ..⟩⟩)⟩
        · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl
            ⟨rfl, List.mem_append_right _ h⟩⟩)⟩
    · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, rfl,
        hQ.mem_support xw⟩))⟩
    · exact ⟨1, (hPchar 1 ((t 1).1, xw)).mpr (Or.inr (Or.inr ⟨rfl, rfl,
        hq1.mem_support xw⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, hi0, ha2⟩ | ⟨ha1, hi1, ha2⟩ <;>
      rcases h2 with ⟨hb1, ⟨hj0', hb2⟩ | ⟨hj1', hb2⟩⟩ | ⟨hb1, hj0', hb2⟩ |
        ⟨hb1, hj1', hb2⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hdisj_j0 x.2 ha2 hb2
    · exact hij (hi0.trans hj0'.symm)
    · exact hT1 (hb1.symm.trans ha1)
    · exact hdisj_j0 x.2 hb2 ha2
    · exact hij (hi1.trans hj1'.symm)
    · exact hj30 (hb1.symm.trans ha1)
    · exact hij (hi1.trans hj1'.symm)
    · exact hij (hi0.trans hj0'.symm)
    · exact hj30 (ha1.symm.trans hb1)
    · exact hij (hi0.trans hj0'.symm)
    · exact hj3B (ha1.symm.trans hb1)
    · exact hT1 (ha1.symm.trans hb1)
    · exact hij (hi1.trans hj1'.symm)
    · exact hj3B (hb1.symm.trans ha1)
    · exact hij (hi1.trans hj1'.symm)

/-- Case 4: both sources in `j0`, not both targets. -/
theorem rank3_case4 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool), ∃ w, colW (j, w) = c)
    (hell : 3 ≤ ell)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∃ i, (t i).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 1) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  by_cases hT0 : (t 0).1 = j0
  · have hT1 : (t 1).1 ≠ j0 := by
      obtain ⟨i, hi⟩ := hT
      fin_cases i
      · exact absurd hT0 hi
      · exact hi
    exact rank3_case4_tin hpW hlace hell hmono hS hT0 hT1
  · by_cases hT1 : (t 1).1 = j0
    · apply dpc_perm (Equiv.swap 0 1)
      have hmono' : MonoDemand colW b (fun i => s (Equiv.swap 0 1 i))
          (fun i => t (Equiv.swap 0 1 i)) :=
        ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
          hmono.2.2.1.comp (Equiv.swap 0 1).injective,
          hmono.2.2.2.comp (Equiv.swap 0 1).injective⟩
      refine rank3_case4_tin hpW hlace hell hmono' (fun i => hS _) ?_ ?_
      · show (t (Equiv.swap 0 1 0)).1 = j0
        rw [Equiv.swap_apply_left]
        exact hT1
      · show (t (Equiv.swap 0 1 1)).1 ≠ j0
        rw [Equiv.swap_apply_right]
        exact hT0
    · -- both targets outside
      have hTT : (t 0).1 ≠ (t 1).1 := by
        intro h
        have hm0 : (0 : Fin 2) ∈ weldWSet s t (t 0).1 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
        have hm1 : (1 : Fin 2) ∈ weldWSet s t (t 0).1 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h.symm⟩
        have h2c : 2 ≤ (weldWSet s t (t 0).1).card :=
          Finset.one_lt_card.mpr ⟨0, hm0, 1, hm1, by decide⟩
        have := hw (t 0).1 hT0
        omega
      exact rank3_case4_bothout hpW hlace hclass hmono hS hT0 hT1 hTT

end Rank3Case4b

section Rank3Case5

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 5: one copy holds a source of one pair and the target of the other. -/
theorem rank3_case5 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j0 : Fin ell} (hs0 : (s 0).1 = j0) (ht1 : (t 1).1 = j0)
    (hs1 : (s 1).1 ≠ j0) (ht0 : (t 0).1 ≠ j0) (hAB : (t 0).1 ≠ (s 1).1) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  have hcolS0v : colW (j0, (s 0).2) = b := by
    rw [show (j0, (s 0).2) = s 0 from Prod.ext hs0.symm rfl]
    exact hmono.1 0
  have hcolT1v : colW (j0, (t 1).2) = !b := by
    rw [show (j0, (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  have hne_s0t1 : (s 0).2 ≠ (t 1).2 := by
    intro h
    have h1 := hcolS0v
    rw [h, hcolT1v] at h1
    cases b <;> simp at h1
  -- master Hamilton path in j0 between the two residents
  have hcne : colW (j0, (s 0).2) ≠ colW (j0, (t 1).2) := by
    rw [hcolS0v, hcolT1v]
    cases b <;> simp
  obtain ⟨p, hpham⟩ := hlace j0 (s 0).2 (t 1).2 hcne
  -- peel the target end
  obtain ⟨u, A1, hA1, hadju, hpsupp, ht1A1⟩ :=
    path_peel_last p hpham.isPath (Ne.symm hne_s0t1)
  have hcu : colW (j0, u) = b := by
    have h : colW (j0, u) ≠ colW (j0, (t 1).2) :=
      hpW _ _ ((weldLift Gs M j0).map_adj hadju)
    rw [hcolT1v] at h
    exact bool_eq_of_ne_not' h
  by_cases hu : u = (s 0).2
  · -- degenerate copies: the resident copy has exactly the two demand vertices
    subst hu
    -- the resident copy is exactly the two demand vertices
    have hA1supp : A1.support = [(s 0).2] := by
      rw [SimpleGraph.Walk.isPath_iff_eq_nil.mp hA1, SimpleGraph.Walk.support_nil]
    have hex : ∀ w : W', w = (s 0).2 ∨ w = (t 1).2 := by
      intro w
      have h := hpham.mem_support w
      rw [hpsupp, hA1supp] at h
      rcases List.mem_append.mp h with h | h
      · exact Or.inl (List.mem_singleton.mp h)
      · exact Or.inr (List.mem_singleton.mp h)
    -- connectors
    obtain ⟨v, hvdef⟩ : ∃ v, v = M j0 (s 1).1 (s 0).2 := ⟨_, rfl⟩
    have hcv : colW ((s 1).1, v) = !b := by
      have h : colW (j0, (s 0).2) ≠ colW ((s 1).1, v) :=
        hvdef ▸ hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hs1) (s 0).2)
      rw [hcolS0v] at h
      exact bool_eq_not_of_ne' (Ne.symm h)
    have hvne : v ≠ (s 1).2 := by
      intro h
      have h1 := hcv
      rw [h] at h1
      have h2 : colW ((s 1).1, (s 1).2) = b := hmono.1 1
      rw [h2] at h1
      cases b <;> simp at h1
    obtain ⟨u', hu'def⟩ : ∃ u', u' = M (s 1).1 (t 0).1 v := ⟨_, rfl⟩
    have hcu' : colW ((t 0).1, u') = b := by
      have h : colW ((s 1).1, v) ≠ colW ((t 0).1, u') :=
        hu'def ▸ hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hAB) v)
      rw [hcv] at h
      exact bool_eq_of_ne_not' (Ne.symm h)
    have hcneA : colW ((t 0).1, u') ≠ colW ((t 0).1, (t 0).2) := by
      rw [hcu']
      have h2 : colW ((t 0).1, (t 0).2) = !b := hmono.2.1 0
      rw [h2]
      cases b <;> simp
    obtain ⟨qA, hqA⟩ := hlace (t 0).1 u' (t 0).2 hcneA
    -- the pair-1 matching partner is forced to be the resident target
    have hpB : M (s 1).1 j0 (s 1).2 = (t 1).2 := by
      have hcol : colW (j0, M (s 1).1 j0 (s 1).2) = !b := by
        have h : colW ((s 1).1, (s 1).2) ≠ colW (j0, M (s 1).1 j0 (s 1).2) :=
          hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) hs1 (s 1).2)
        have h2 : colW ((s 1).1, (s 1).2) = b := hmono.1 1
        rw [h2] at h
        exact bool_eq_not_of_ne' (Ne.symm h)
      rcases hex (M (s 1).1 j0 (s 1).2) with h | h
      · exfalso
        rw [h, hcolS0v] at hcol
        cases b <;> simp at hcol
      · exact h
    -- pair 0: cross to the source copy, cross to the target copy, Hamilton finish
    have hadj01 : (weldGraph ell Gs M).Adj (s 0) ((s 1).1, v) := by
      have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hs1) (s 0).2
      rw [← hvdef] at h
      have hpair : ((j0 : Fin ell), (s 0).2) = s 0 := Prod.ext hs0.symm rfl
      rwa [hpair] at h
    have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) ((s 1).1, v), R.IsPath ∧
        R.support = [s 0, ((s 1).1, v)] := by
      refine ⟨SimpleGraph.Walk.cons hadj01 SimpleGraph.Walk.nil, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
        intro h
        have h1 := congrArg Prod.fst h
        exact hs1 (h1.symm.trans hs0)
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
    obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ qA hR₀p hqA.isPath
      (hu'def ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hAB) v)
      (by
        intro w' _ hmem
        rw [hR₀s] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact ht0 ((congrArg Prod.fst h).trans hs0)
        · rw [List.mem_singleton] at h
          have h2 : ((t 0).1, w').1 = ((s 1).1, v).1 := congrArg Prod.fst h
          exact hAB h2)
    -- pair 1: the single matching edge into the resident copy
    have hadj11 : (weldGraph ell Gs M).Adj (s 1) (t 1) := by
      have h := weld_cross_adj (Gs := Gs) (M := M) hs1 (s 1).2
      rw [hpB] at h
      have hpair1 : ((s 1).1, (s 1).2) = s 1 := Prod.ext rfl rfl
      have hpair2 : ((j0 : Fin ell), (t 1).2) = t 1 := Prod.ext ht1.symm rfl
      rwa [hpair1, hpair2] at h
    have hpath1 : (SimpleGraph.Walk.cons hadj11 SimpleGraph.Walk.nil :
        (weldGraph ell Gs M).Walk (s 1) (t 1)).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
      exact hmono.st_ne 1 1
    have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
        ∀ x : Fin ell × W', x ∈ P.support ↔
          ((i = 0 ∧ (x = s 0 ∨ x = ((s 1).1, v) ∨
              (x.1 = (t 0).1 ∧ x.2 ∈ qA.support))) ∨
            (i = 1 ∧ (x = s 1 ∨ x = t 1))) := by
      intro i
      fin_cases i
      · refine ⟨R₁.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₁p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s, mem_map_pair]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · rcases List.mem_cons.mp h with h | h
              · exact Or.inl ⟨rfl, Or.inl h⟩
              · rw [List.mem_singleton] at h
                exact Or.inl ⟨rfl, Or.inr (Or.inl h)⟩
            · exact Or.inl ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩
          · rintro (⟨-, h | h | ⟨h1, h2⟩⟩ | ⟨h0, -⟩)
            · exact Or.inl (h ▸ List.mem_cons_self ..)
            · exact Or.inl (h ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))
            · exact Or.inr ⟨h1, h2⟩
            · exact absurd h0 (by decide)
      · refine ⟨SimpleGraph.Walk.cons hadj11 SimpleGraph.Walk.nil, hpath1, ?_⟩
        intro x
        constructor
        · intro h
          rw [SimpleGraph.Walk.support_cons] at h
          rcases List.mem_cons.mp h with h | h
          · exact Or.inr ⟨rfl, Or.inl h⟩
          · have h2 : x = t 1 := by simpa using h
            exact Or.inr ⟨rfl, Or.inr h2⟩
        · rintro (⟨h0, -⟩ | ⟨-, h | h⟩)
          · exact absurd h0 (by decide)
          · rw [SimpleGraph.Walk.support_cons, h]
            exact List.mem_cons_self ..
          · rw [SimpleGraph.Walk.support_cons, h]
            refine List.mem_cons_of_mem _ ?_
            simp
    choose P hPp hPchar using hpaths
    refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j0, (t 0).1, (s 1).1} P hPp ?_ ?_ ?_
    · intro r x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (hPchar r x).mp hx with ⟨-, h | h | ⟨h1, -⟩⟩ | ⟨-, h | h⟩
      · rw [h]
        exact Or.inl hs0
      · rw [h]
        exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl h1)
      · rw [h]
        exact Or.inr (Or.inr rfl)
      · rw [h]
        exact Or.inl ht1
    · rintro ⟨xj, xw⟩ hxJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
      rcases hxJ with rfl | rfl | rfl
      · rcases hex xw with rfl | rfl
        · exact ⟨0, (hPchar 0 _).mpr (Or.inl ⟨rfl, Or.inl (Prod.ext hs0.symm rfl)⟩)⟩
        · exact ⟨1, (hPchar 1 _).mpr (Or.inr ⟨rfl, Or.inr (Prod.ext ht1.symm rfl)⟩)⟩
      · exact ⟨0, (hPchar 0 _).mpr (Or.inl ⟨rfl, Or.inr (Or.inr
          ⟨rfl, hqA.mem_support xw⟩)⟩)⟩
      · -- the source copy: its two vertices are the connector and the second source
        rcases hex xw with h | h
        · -- xw is the first resident: it must be one of v or (s 1).2
          rcases hex v with hv1 | hv1 <;> rcases hex (s 1).2 with hs1v | hs1v
          · exact absurd (hv1.trans hs1v.symm) hvne
          · exact ⟨0, (hPchar 0 _).mpr (Or.inl ⟨rfl, Or.inr (Or.inl
              (by rw [h, ← hv1]))⟩)⟩
          · exact ⟨1, (hPchar 1 _).mpr (Or.inr ⟨rfl, Or.inl
              (by rw [h, ← hs1v])⟩)⟩
          · exact absurd (hv1.trans hs1v.symm) hvne
        · rcases hex v with hv1 | hv1 <;> rcases hex (s 1).2 with hs1v | hs1v
          · exact absurd (hv1.trans hs1v.symm) hvne
          · exact ⟨1, (hPchar 1 _).mpr (Or.inr ⟨rfl, Or.inl
              (by rw [h, ← hs1v])⟩)⟩
          · exact ⟨0, (hPchar 0 _).mpr (Or.inl ⟨rfl, Or.inr (Or.inl
              (by rw [h, ← hv1]))⟩)⟩
          · exact absurd (hv1.trans hs1v.symm) hvne
    · intro i j hij x hx
      have h1 := (hPchar i x).mp hx.1
      have h2 := (hPchar j x).mp hx.2
      rcases h1 with ⟨hi0, ha⟩ | ⟨hi1, ha⟩ <;> rcases h2 with ⟨hj0', hb⟩ | ⟨hj1', hb⟩
      · exact hij (hi0.trans hj0'.symm)
      · rcases ha with ha | ha | ⟨ha1, -⟩ <;> rcases hb with hb | hb
        · have h := ha.symm.trans hb
          have h2 := hmono.2.2.1 h
          exact absurd h2 (by decide)
        · exact hmono.st_ne 0 1 (ha.symm.trans hb)
        · exact hvne (congrArg Prod.snd (ha.symm.trans hb))
        · have h1 := congrArg Prod.fst (ha.symm.trans hb)
          exact hs1 (h1.trans ht1)
        · rw [hb] at ha1
          exact hAB ha1.symm
        · rw [hb] at ha1
          exact ht0 (ha1.symm.trans ht1)
      · rcases hb with hb | hb | ⟨hb1, -⟩ <;> rcases ha with ha | ha
        · have h := hb.symm.trans ha
          have h2 := hmono.2.2.1 h
          exact absurd h2 (by decide)
        · exact hmono.st_ne 0 1 (hb.symm.trans ha)
        · exact hvne (congrArg Prod.snd (hb.symm.trans ha))
        · have h1 := congrArg Prod.fst (hb.symm.trans ha)
          exact hs1 (h1.trans ht1)
        · rw [ha] at hb1
          exact hAB hb1.symm
        · rw [ha] at hb1
          exact ht0 (hb1.symm.trans ht1)
      · exact hij (hi1.trans hj1'.symm)

  · -- peel once more and reroute both pairs
    obtain ⟨v, A2, hA2, hadjv, hA1supp, huA2⟩ := path_peel_last A1 hA1 hu
    have hcv : colW (j0, v) = !b := by
      have h : colW (j0, v) ≠ colW (j0, u) :=
        hpW _ _ ((weldLift Gs M j0).map_adj hadjv)
      rw [hcu] at h
      exact bool_eq_not_of_ne' h
    -- pair 0: prefix in j0, Hamilton path in the target copy
    have hcvs : colW ((t 0).1, M j0 (t 0).1 v) = b := by
      have h : colW (j0, v) ≠ colW ((t 0).1, M j0 (t 0).1 v) :=
        hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm ht0) v)
      rw [hcv] at h
      exact bool_eq_of_ne_not' (Ne.symm h)
    have hcneA : colW ((t 0).1, M j0 (t 0).1 v) ≠ colW ((t 0).1, (t 0).2) := by
      rw [hcvs]
      have h2 : colW ((t 0).1, (t 0).2) = !b := hmono.2.1 0
      rw [h2]
      cases b <;> simp
    obtain ⟨qA, hqA⟩ := hlace (t 0).1 (M j0 (t 0).1 v) (t 0).2 hcneA
    -- pair 1: Hamilton path in the source copy, then the freed edge
    have hcus : colW ((s 1).1, M j0 (s 1).1 u) = !b := by
      have h : colW (j0, u) ≠ colW ((s 1).1, M j0 (s 1).1 u) :=
        hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hs1) u)
      rw [hcu] at h
      exact bool_eq_not_of_ne' (Ne.symm h)
    have hcneB : colW ((s 1).1, (s 1).2) ≠ colW ((s 1).1, M j0 (s 1).1 u) := by
      rw [hcus]
      have h2 : colW ((s 1).1, (s 1).2) = b := hmono.1 1
      rw [h2]
      cases b <;> simp
    obtain ⟨qB, hqB⟩ := hlace (s 1).1 (s 1).2 (M j0 (s 1).1 u) hcneB
    -- assemble pair 0
    have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, v), R.IsPath ∧
        R.support = A2.support.map (fun w => (j0, w)) := by
      refine ⟨(A2.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA2
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
    obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ qA hR₀p hqA.isPath
      (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm ht0) v)
      (by
        intro w' _ hmem
        rw [hR₀s, mem_map_pair] at hmem
        exact ht0 hmem.1)
    -- assemble pair 1
    have hut1p : (SimpleGraph.Walk.cons hadju SimpleGraph.Walk.nil :
        (Gs j0).Walk u (t 1).2).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
      intro h
      have h1 := hcu
      rw [h, hcolT1v] at h1
      cases b <;> simp at h1
    have hR0' : ∃ R : (weldGraph ell Gs M).Walk (s 1) ((s 1).1, M j0 (s 1).1 u),
        R.IsPath ∧ R.support = qB.support.map (fun w => ((s 1).1, w)) := by
      refine ⟨(qB.map (weldLift Gs M (s 1).1)).copy (Prod.ext rfl rfl) rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hqB.isPath
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨R₀', hR₀'p, hR₀'s⟩ := hR0'
    obtain ⟨R₁', hR₁'p, hR₁'s⟩ := weld_splice_snoc R₀'
      (SimpleGraph.Walk.cons hadju SimpleGraph.Walk.nil) hR₀'p hut1p
      ((weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hs1) u).symm)
      (by
        intro w' _ hmem
        rw [hR₀'s, mem_map_pair] at hmem
        exact hs1 hmem.1.symm)
    have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
        ∀ x : Fin ell × W', x ∈ P.support ↔
          ((x.1 = j0 ∧ ((i = 0 ∧ x.2 ∈ A2.support) ∨ (i = 1 ∧ x.2 ∈ [u, (t 1).2]))) ∨
            (x.1 = (t 0).1 ∧ i = 0 ∧ x.2 ∈ qA.support) ∨
            (x.1 = (s 1).1 ∧ i = 1 ∧ x.2 ∈ qB.support)) := by
      intro i
      fin_cases i
      · refine ⟨R₁.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₁p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s,
            mem_map_pair, mem_map_pair]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩
            · exact Or.inr (Or.inl ⟨h1, rfl, h2⟩)
          · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, -, h2⟩ | ⟨-, h0, -⟩)
            · exact Or.inl ⟨h1, h2⟩
            · exact absurd h0 (by decide)
            · exact Or.inr ⟨h1, h2⟩
            · exact absurd h0 (by decide)
      · refine ⟨R₁'.copy rfl (Prod.ext ht1.symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₁'p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₁'s, List.mem_append, hR₀'s,
            mem_map_pair, mem_map_pair]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Or.inr (Or.inr ⟨h1, rfl, h2⟩)
            · refine Or.inl ⟨h1, Or.inr ⟨rfl, ?_⟩⟩
              rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at h2
              exact h2
          · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨-, h0, -⟩ | ⟨h1, -, h2⟩)
            · exact absurd h0 (by decide)
            · refine Or.inr ⟨h1, ?_⟩
              rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
              exact h2
            · exact absurd h0 (by decide)
            · exact Or.inl ⟨h1, h2⟩
    choose P hPp hPchar using hpaths
    refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j0, (t 0).1, (s 1).1} P hPp ?_ ?_ ?_
    · intro r x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rintro ⟨xj, xw⟩ hxJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
      rcases hxJ with rfl | rfl | rfl
      · have h := hpham.mem_support xw
        rw [hpsupp] at h
        rcases List.mem_append.mp h with h | h
        · rw [hA1supp] at h
          rcases List.mem_append.mp h with h | h
          · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
          · rw [List.mem_singleton] at h
            exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr
              ⟨rfl, by rw [h]; exact List.mem_cons_self ..⟩⟩)⟩
        · rw [List.mem_singleton] at h
          exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr
            ⟨rfl, by rw [h]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩⟩)⟩
      · exact ⟨0, (hPchar 0 ((t 0).1, xw)).mpr (Or.inr (Or.inl ⟨rfl, rfl,
          hqA.mem_support xw⟩))⟩
      · exact ⟨1, (hPchar 1 ((s 1).1, xw)).mpr (Or.inr (Or.inr ⟨rfl, rfl,
          hqB.mem_support xw⟩))⟩
    · intro i j hij x hx
      have h1 := (hPchar i x).mp hx.1
      have h2 := (hPchar j x).mp hx.2
      have hdisj_j0 : ∀ w : W', w ∈ A2.support → w ∈ [u, (t 1).2] → False := by
        intro w hw hw2
        rcases List.mem_cons.mp hw2 with h | h
        · exact huA2 (h ▸ hw)
        · rw [List.mem_singleton] at h
          apply ht1A1
          rw [hA1supp]
          exact List.mem_append_left _ (h ▸ hw)
      rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, hi0, ha2⟩ |
        ⟨ha1, hi1, ha2⟩ <;>
        rcases h2 with ⟨hb1, ⟨hj0', hb2⟩ | ⟨hj1', hb2⟩⟩ | ⟨hb1, hj0', hb2⟩ |
          ⟨hb1, hj1', hb2⟩
      · exact hij (hi0.trans hj0'.symm)
      · exact hdisj_j0 x.2 ha2 hb2
      · exact hij (hi0.trans hj0'.symm)
      · exact hs1 (hb1.symm.trans ha1)
      · exact hdisj_j0 x.2 hb2 ha2
      · exact hij (hi1.trans hj1'.symm)
      · exact ht0 (hb1.symm.trans ha1)
      · exact hij (hi1.trans hj1'.symm)
      · exact hij (hi0.trans hj0'.symm)
      · exact ht0 (ha1.symm.trans hb1)
      · exact hij (hi0.trans hj0'.symm)
      · exact hAB (ha1.symm.trans hb1)
      · exact hs1 (ha1.symm.trans hb1)
      · exact hij (hi1.trans hj1'.symm)
      · exact hAB (hb1.symm.trans ha1)
      · exact hij (hi1.trans hj1'.symm)

end Rank3Case5

section Rank3Case6

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']
  {Gs : Fin ell → SimpleGraph W'} {M : Fin ell → Fin ell → (W' ≃ W')}
  {colW : Fin ell × W' → Bool}

/-- Case 6: two copies each hold a source of one pair and the target of the other. -/
theorem rank3_case6 (hpW : IsProper2Coloring (weldGraph ell Gs M) colW)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => colW (j, w)))
    (hell : 3 ≤ ell)
    {b : Bool} {s t : Fin 2 → Fin ell × W'} (hmono : MonoDemand colW b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hs0 : (s 0).1 = j1) (ht1 : (t 1).1 = j1)
    (hs1 : (s 1).1 = j2) (ht0 : (t 0).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) 2 s t := by
  classical
  obtain ⟨j3, hj31, hj32⟩ : ∃ j3, j3 ≠ j1 ∧ j3 ≠ j2 := by
    have hlt : ({j1, j2} : Finset (Fin ell)).card
        < (Finset.univ : Finset (Fin ell)).card := by
      have h1 : ({j1, j2} : Finset (Fin ell)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j3, -, hj3⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    rw [Finset.mem_insert, Finset.mem_singleton] at hj3
    exact ⟨j3, fun h => hj3 (Or.inl h), fun h => hj3 (Or.inr h)⟩
  have hcolS0 : colW (j1, (s 0).2) = b := by
    rw [show (j1, (s 0).2) = s 0 from Prod.ext hs0.symm rfl]
    exact hmono.1 0
  have hcolT1 : colW (j1, (t 1).2) = !b := by
    rw [show (j1, (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  have hcolS1 : colW (j2, (s 1).2) = b := by
    rw [show (j2, (s 1).2) = s 1 from Prod.ext hs1.symm rfl]
    exact hmono.1 1
  have hcolT0 : colW (j2, (t 0).2) = !b := by
    rw [show (j2, (t 0).2) = t 0 from Prod.ext ht0.symm rfl]
    exact hmono.2.1 0
  -- the freed neighbor of pair 0's target inside j1
  obtain ⟨u1, hu1def⟩ : ∃ u1, u1 = M j2 j1 (t 0).2 := ⟨_, rfl⟩
  have hcu1 : colW (j1, u1) = b := by
    have h : colW (j2, (t 0).2) ≠ colW (j1, u1) :=
      hu1def ▸ hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (t 0).2)
    rw [hcolT0] at h
    exact bool_eq_of_ne_not' (Ne.symm (Ne.symm h)).symm
  -- master path in j1
  have hcne1 : colW (j1, (s 0).2) ≠ colW (j1, (t 1).2) := by
    rw [hcolS0, hcolT1]
    cases b <;> simp
  obtain ⟨p1, hp1⟩ := hlace j1 (s 0).2 (t 1).2 hcne1
  have hu1mem : u1 ∈ p1.support := hp1.mem_support u1
  have hne_u1t1 : u1 ≠ (t 1).2 := by
    intro h
    have h1 := hcu1
    rw [h, hcolT1] at h1
    cases b <;> simp at h1
  -- split inclusively at u1
  have hsupp1 : p1.support = (p1.takeUntil u1 hu1mem).support
      ++ (p1.dropUntil u1 hu1mem).support.tail := by
    conv_lhs => rw [← p1.take_spec hu1mem]
    rw [SimpleGraph.Walk.support_append]
  have htakeP : (p1.takeUntil u1 hu1mem).IsPath := hp1.isPath.takeUntil hu1mem
  have hdropP : (p1.dropUntil u1 hu1mem).IsPath := hp1.isPath.dropUntil hu1mem
  obtain ⟨v2, Suf, hSuf, hadjv2, hdropsupp, hu1Suf⟩ :=
    path_peel_head (p1.dropUntil u1 hu1mem) hdropP hne_u1t1
  have hcv2 : colW (j1, v2) = !b := by
    have h : colW (j1, u1) ≠ colW (j1, v2) :=
      hpW _ _ ((weldLift Gs M j1).map_adj hadjv2)
    rw [hcu1] at h
    exact bool_eq_not_of_ne' (Ne.symm h)
  -- master path in j2, with its target end peeled
  have hcne2 : colW (j2, (s 1).2) ≠ colW (j2, (t 0).2) := by
    rw [hcolS1, hcolT0]
    cases b <;> simp
  obtain ⟨p2, hp2⟩ := hlace j2 (s 1).2 (t 0).2 hcne2
  have hne_t0s1 : (t 0).2 ≠ (s 1).2 := by
    intro h
    have h1 := hcolT0
    rw [h, hcolS1] at h1
    cases b <;> simp at h1
  obtain ⟨u2, Pre2, hPre2, hadju2, hp2supp, ht0Pre2⟩ :=
    path_peel_last p2 hp2.isPath hne_t0s1
  have hcu2 : colW (j2, u2) = b := by
    have h : colW (j2, u2) ≠ colW (j2, (t 0).2) :=
      hpW _ _ ((weldLift Gs M j2).map_adj hadju2)
    rw [hcolT0] at h
    exact bool_eq_of_ne_not' h
  -- the bridge in j3
  have hcu2s : colW (j3, M j2 j3 u2) = !b := by
    have h : colW (j2, u2) ≠ colW (j3, M j2 j3 u2) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) u2)
    rw [hcu2] at h
    exact bool_eq_not_of_ne' (Ne.symm h)
  have hcv2s : colW (j3, M j1 j3 v2) = b := by
    have h : colW (j1, v2) ≠ colW (j3, M j1 j3 v2) :=
      hpW _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) v2)
    rw [hcv2] at h
    exact bool_eq_of_ne_not' (Ne.symm h)
  have hcneQ : colW (j3, M j2 j3 u2) ≠ colW (j3, M j1 j3 v2) := by
    rw [hcu2s, hcv2s]
    cases b <;> simp
  obtain ⟨Q, hQ⟩ := hlace j3 (M j2 j3 u2) (M j1 j3 v2) hcneQ
  -- pair 0: the j1 prefix, then the matching edge to its target
  have hadjP0 : (weldGraph ell Gs M).Adj (j1, u1) (t 0) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (t 0).2
    rw [← hu1def] at h
    have hpair : ((j2 : Fin ell), (t 0).2) = t 0 := Prod.ext ht0.symm rfl
    rw [hpair] at h
    exact h.symm
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j1, u1), R.IsPath ∧
      R.support = (p1.takeUntil u1 hu1mem).support.map (fun w => (j1, w)) := by
    refine ⟨((p1.takeUntil u1 hu1mem).map (weldLift Gs M j1)).copy
      (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) htakeP
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  have hP0 : ∃ P : (weldGraph ell Gs M).Walk (s 0) (t 0), P.IsPath ∧
      P.support = (p1.takeUntil u1 hu1mem).support.map (fun w => (j1, w)) ++ [t 0] := by
    refine ⟨R₀.concat hadjP0, ?_, ?_⟩
    · rw [SimpleGraph.Walk.concat_isPath_iff]
      refine ⟨hR₀p, ?_⟩
      intro hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hj12 (hmem.1.symm.trans ht0)
    · rw [SimpleGraph.Walk.support_concat, hR₀s]
  obtain ⟨P0, hP0p, hP0s⟩ := hP0
  -- pair 1: the j2 prefix, the bridge, the freed j1 suffix
  have hR0' : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j2, u2), R.IsPath ∧
      R.support = Pre2.support.map (fun w => (j2, w)) := by
    refine ⟨(Pre2.map (weldLift Gs M j2)).copy (Prod.ext hs1.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hPre2
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀', hR₀'p, hR₀'s⟩ := hR0'
  obtain ⟨R₁', hR₁'p, hR₁'s⟩ := weld_splice_snoc R₀' Q hR₀'p hQ.isPath
    (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) u2)
    (by
      intro w' _ hmem
      rw [hR₀'s, mem_map_pair] at hmem
      exact hj32 hmem.1)
  obtain ⟨R₂', hR₂'p, hR₂'s⟩ := weld_splice_snoc R₁' Suf hR₁'p hSuf
    ((weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) v2).symm)
    (by
      intro w' _ hmem
      rw [hR₁'s, List.mem_append, hR₀'s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj12 h1
      · exact hj31 h1.symm)
  have hpaths : ∀ i : Fin 2, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W', x ∈ P.support ↔
        ((x.1 = j1 ∧ ((i = 0 ∧ x.2 ∈ (p1.takeUntil u1 hu1mem).support) ∨
            (i = 1 ∧ x.2 ∈ Suf.support))) ∨
          (x.1 = j2 ∧ ((i = 0 ∧ x.2 = (t 0).2) ∨ (i = 1 ∧ x.2 ∈ Pre2.support))) ∨
          (x.1 = j3 ∧ i = 1 ∧ x.2 ∈ Q.support)) := by
    intro i
    fin_cases i
    · refine ⟨P0.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP0p
      intro x
      rw [SimpleGraph.Walk.support_copy, hP0s, List.mem_append, mem_map_pair]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩
        · rw [List.mem_singleton] at h
          refine Or.inr (Or.inl ⟨?_, Or.inl ⟨rfl, ?_⟩⟩)
          · rw [h]
            exact ht0
          · rw [h]
      · rintro (⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨h1, ⟨-, h2⟩ | ⟨h0, -⟩⟩ | ⟨-, h0, -⟩)
        · exact Or.inl ⟨h1, h2⟩
        · exact absurd h0 (by decide)
        · refine Or.inr ?_
          rw [List.mem_singleton]
          exact Prod.ext (h1.trans ht0.symm) h2
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
    · refine ⟨R₂'.copy rfl (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₂'p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR₂'s, List.mem_append, hR₁'s,
          List.mem_append, hR₀'s, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨h1, rfl, h2⟩)
          · exact Or.inl ⟨h1, Or.inr ⟨rfl, h2⟩⟩
        · rintro (⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨h1, ⟨h0, -⟩ | ⟨-, h2⟩⟩ | ⟨h1, -, h2⟩)
          · exact absurd h0 (by decide)
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hpW hlace (hmono.st_ne 0 0) {j1, j2, j3} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · have h := hp1.mem_support xw
      rw [hsupp1] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · rw [hdropsupp] at h
        exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
    · have h := hp2.mem_support xw
      rw [hp2supp] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩))⟩
      · rw [List.mem_singleton] at h
        exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩))⟩
    · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, rfl,
        hQ.mem_support xw⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hdisj_j1 : ∀ w : W', w ∈ (p1.takeUntil u1 hu1mem).support →
        w ∈ Suf.support → False := by
      intro w hw hw2
      have hnd := hp1.isPath.support_nodup
      rw [hsupp1, hdropsupp] at hnd
      exact (List.nodup_append.mp hnd).2.2 w hw w hw2 rfl
    have hdisj_j2 : ∀ w : W', w = (t 0).2 → w ∈ Pre2.support → False := by
      intro w hw hw2
      exact ht0Pre2 (hw ▸ hw2)
    rcases h1 with ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ | ⟨ha1, ⟨hi0, ha2⟩ | ⟨hi1, ha2⟩⟩ |
      ⟨ha1, hi1, ha2⟩ <;>
      rcases h2 with ⟨hb1, ⟨hj0', hb2⟩ | ⟨hj1', hb2⟩⟩ | ⟨hb1, ⟨hj0', hb2⟩ | ⟨hj1', hb2⟩⟩ |
        ⟨hb1, hj1', hb2⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hdisj_j1 x.2 ha2 hb2
    · exact hj12 (ha1.symm.trans hb1)
    · exact hj12 (ha1.symm.trans hb1)
    · exact hj31 (hb1.symm.trans ha1)
    · exact hdisj_j1 x.2 hb2 ha2
    · exact hij (hi1.trans hj1'.symm)
    · exact hj12 (ha1.symm.trans hb1)
    · exact hj12 (ha1.symm.trans hb1)
    · exact hj31 (hb1.symm.trans ha1)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hij (hi0.trans hj0'.symm)
    · exact hdisj_j2 x.2 ha2 hb2
    · exact hj32 (hb1.symm.trans ha1)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hj12 (hb1.symm.trans ha1)
    · exact hdisj_j2 x.2 hb2 ha2
    · exact hij (hi1.trans hj1'.symm)
    · exact hj32 (hb1.symm.trans ha1)
    · exact hj31 (ha1.symm.trans hb1)
    · exact hj31 (ha1.symm.trans hb1)
    · exact hj32 (ha1.symm.trans hb1)
    · exact hj32 (ha1.symm.trans hb1)
    · exact hij (hi1.trans hj1'.symm)

end Rank3Case6

/-- An equitable coloring on at least two vertices has both classes inhabited. -/
theorem equitable_class_nonempty {W : Type} [DecidableEq W] [Fintype W]
    {H : SimpleGraph W} {colH : W → Bool} (hE : IsEquitableBipartite H colH)
    (hcard : 2 ≤ Fintype.card W) (c : Bool) : ∃ w, colH w = c := by
  classical
  have hcards := hE.2
  have hsum : Fintype.card {w : W // colH w = false} + Fintype.card {w : W // colH w = true}
      = Fintype.card W := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W)) (p := fun w => colH w = false)
    rw [Finset.card_univ] at hsplit
    rw [← hsplit]
    congr 1
    refine congrArg Finset.card ?_
    apply Finset.filter_congr
    intro w _
    cases hc : colH w <;> simp
  have hpos : 0 < Fintype.card {w : W // colH w = c} := by
    cases c <;> omega
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨w, hw⟩

/-! ## Rank 3: part (b) of the Theorem 1.5 base analysis -/

/-- **Coleman et al. 2025, Theorem 1.5 base (b)**: a rank-3 tree admits paired 2-covers
    for every legal demand. -/
theorem thm15_rank3 {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (col : V → Bool) (hT : IsColemanTree G 3) (hBB : IsProper2Coloring G col) :
    IsPairedKDPCForOpposite G col 2 := by
  classical
  cases hT with
  | @weld V' W' G' ell r Gs M hr hEll htl hM e =>
    have instFW : Fintype (Fin ell × W') := Fintype.ofEquiv V e.toEquiv
    have instDW : DecidableEq W' := Classical.decEq W'
    have hell0 : 0 < ell := by omega
    have instW : Fintype W' :=
      Fintype.ofInjective (fun w : W' => ((⟨0, hell0⟩ : Fin ell), w))
        (fun a b h => (Prod.ext_iff.mp h).2)
    apply pairedKDPC_iso e col (fun x => col (e.symm x)) (fun v => by simp)
    have hpW : IsProper2Coloring (weldGraph ell Gs M) (fun x => col (e.symm x)) := by
      intro x y hxy
      exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
    have htl2 : ∀ j, IsColemanTree (Gs j) 2 := by
      intro j
      have h := htl j
      simpa using h
    have hcopyP : ∀ j : Fin ell, IsProper2Coloring (Gs j)
        (fun w => col (e.symm (j, w))) :=
      fun j u v huv => hpW (j, u) (j, v) ((weldLift Gs M j).map_adj huv)
    have hlace : ∀ j : Fin ell, IsHamLaceable (Gs j) (fun w => col (e.symm (j, w))) :=
      fun j => paired_one_opposite_iff_hamLaceable.mp
        (thm15_rank2 (Gs j) _ (htl2 j) (hcopyP j))
    apply pairedKDPC_of_mono
    intro b s t hmono
    have hWne : Nonempty W' := ⟨(s 0).2⟩
    have hclass : ∀ (j : Fin ell) (c : Bool), ∃ w, col (e.symm (j, w)) = c := by
      intro j c
      have hequit := colemanRank2_equitable (htl2 j) (hcopyP j) hWne
      obtain ⟨hcard2, -⟩ := colemanRank2_card (htl2 j) (hcopyP j) hWne
      exact equitable_class_nonempty hequit hcard2 c
    have hell3 : 3 ≤ ell := by omega
    by_cases hfull : ∃ j, (weldWSet s t j).card = 2
    · obtain ⟨j0, hw0⟩ := hfull
      by_cases hfull2 : ∃ j', j' ≠ j0 ∧ (weldWSet s t j').card = 2
      · -- two full copies
        obtain ⟨j', hj', hw'⟩ := hfull2
        have htc : ∀ i, (s i).1 = j0 ∨ (t i).1 = j0 := fun i => weldWSet_full_touch hw0 i
        have htc' : ∀ i, (s i).1 = j' ∨ (t i).1 = j' := fun i => weldWSet_full_touch hw' i
        by_cases hS0 : (s 0).1 = j0
        · by_cases hS1 : (s 1).1 = j0
          · -- sources in j0, targets in j'
            have hTj' : ∀ i, (t i).1 = j' := by
              intro i
              rcases htc' i with h | h
              · exfalso
                fin_cases i
                · exact hj' (h.symm.trans hS0)
                · exact hj' (h.symm.trans hS1)
              · exact h
            refine rank3_case3 hpW hlace hclass hell3 hmono (Ne.symm hj') ?_ hTj'
            intro i
            fin_cases i
            · exact hS0
            · exact hS1
          · -- s0, t1 in j0; s1, t0 in j'
            have ht1 : (t 1).1 = j0 := (htc 1).resolve_left hS1
            have hs1' : (s 1).1 = j' := by
              rcases htc' 1 with h | h
              · exact h
              · exact absurd (h.symm.trans ht1) hj'
            have ht0' : (t 0).1 = j' := by
              rcases htc' 0 with h | h
              · exact absurd (h.symm.trans hS0) hj'
              · exact h
            exact rank3_case6 hpW hlace hell3 hmono (Ne.symm hj') hS0 ht1 hs1' ht0'
        · have ht0 : (t 0).1 = j0 := (htc 0).resolve_left hS0
          have hs0' : (s 0).1 = j' := by
            rcases htc' 0 with h | h
            · exact h
            · exact absurd (h.symm.trans ht0) hj'
          by_cases hS1 : (s 1).1 = j0
          · -- s1, t0 in j0; s0, t1 in j'
            have ht1' : (t 1).1 = j' := by
              rcases htc' 1 with h | h
              · exact absurd (h.symm.trans hS1) hj'
              · exact h
            exact rank3_case6 hpW hlace hell3 hmono hj' hs0' ht1' hS1 ht0
          · -- both sources in j', both targets in j0
            have ht1 : (t 1).1 = j0 := (htc 1).resolve_left hS1
            have hs1' : (s 1).1 = j' := by
              rcases htc' 1 with h | h
              · exact h
              · exact absurd (h.symm.trans ht1) hj'
            refine rank3_case3 hpW hlace hclass hell3 hmono hj' ?_ ?_
            · intro i
              fin_cases i
              · exact hs0'
              · exact hs1'
            · intro i
              fin_cases i
              · exact ht0
              · exact ht1
      · -- exactly one full copy
        have hw1 : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 1 := by
          intro j hj
          have h1 := weldWSet_card_le s t j
          have h2 : (weldWSet s t j).card ≠ 2 := fun h => hfull2 ⟨j, hj, h⟩
          omega
        have htc : ∀ i, (s i).1 = j0 ∨ (t i).1 = j0 := fun i => weldWSet_full_touch hw0 i
        by_cases hSin : ∀ i, (s i).1 = j0
        · by_cases hTin : ∀ i, (t i).1 = j0
          · exact rank3_case2 hpW hlace (by omega) hmono (fun i => ⟨hSin i, hTin i⟩)
          · have hTex : ∃ i, (t i).1 ≠ j0 := by
              by_contra h
              exact hTin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
            exact rank3_case4 hpW hlace hclass hell3 hmono hSin hTex hw1
        · by_cases hTin : ∀ i, (t i).1 = j0
          · have hSex : ∃ i, (s i).1 ≠ j0 := by
              by_contra h
              exact hSin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
            apply dpc_swap
            have hw1' : ∀ j, j ≠ j0 → (weldWSet t s j).card ≤ 1 := by
              intro j hj
              rw [weldWSet_swap]
              exact hw1 j hj
            exact rank3_case4 hpW hlace hclass hell3 hmono.swap hTin hSex hw1'
          · -- mixed: exactly one endpoint of each pair inside
            obtain ⟨iS, hiS⟩ : ∃ i, (s i).1 ≠ j0 := by
              by_contra h
              exact hSin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
            obtain ⟨iT, hiT⟩ : ∃ i, (t i).1 ≠ j0 := by
              by_contra h
              exact hTin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
            have hne : iS ≠ iT := by
              intro h
              subst h
              rcases htc iS with h | h
              · exact hiS h
              · exact hiT h
            have hAB' : ∀ {iA iB : Fin 2}, iA ≠ iB → (t iA).1 ≠ j0 → (s iB).1 ≠ j0 →
                (t iA).1 ≠ (s iB).1 := by
              intro iA iB hab hta hsb h
              have hm1 : iA ∈ weldWSet s t (t iA).1 :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
              have hm2 : iB ∈ weldWSet s t (t iA).1 :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h.symm⟩
              have h2c : 2 ≤ (weldWSet s t (t iA).1).card :=
                Finset.one_lt_card.mpr ⟨iA, hm1, iB, hm2, hab⟩
              have h3 := hw1 (t iA).1 hta
              omega
            fin_cases iS <;> fin_cases iT
            · exact absurd rfl hne
            · -- s0 out, t1 out: so t0 in, s1 in: swapped case 5
              have ht0 : (t 0).1 = j0 := (htc 0).resolve_left hiS
              have hs1 : (s 1).1 = j0 := by
                rcases htc 1 with h | h
                · exact h
                · exact absurd h hiT
              apply dpc_perm (Equiv.swap 0 1)
              have hmono' : MonoDemand (fun x => col (e.symm x)) b
                  (fun i => s (Equiv.swap 0 1 i)) (fun i => t (Equiv.swap 0 1 i)) :=
                ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
                  hmono.2.2.1.comp (Equiv.swap 0 1).injective,
                  hmono.2.2.2.comp (Equiv.swap 0 1).injective⟩
              refine rank3_case5 hpW hlace hmono' (j0 := j0) ?_ ?_ ?_ ?_ ?_
              · show (s (Equiv.swap 0 1 0)).1 = j0
                rw [Equiv.swap_apply_left]
                exact hs1
              · show (t (Equiv.swap 0 1 1)).1 = j0
                rw [Equiv.swap_apply_right]
                exact ht0
              · show (s (Equiv.swap 0 1 1)).1 ≠ j0
                rw [Equiv.swap_apply_right]
                exact hiS
              · show (t (Equiv.swap 0 1 0)).1 ≠ j0
                rw [Equiv.swap_apply_left]
                exact hiT
              · show (t (Equiv.swap 0 1 0)).1 ≠ (s (Equiv.swap 0 1 1)).1
                rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
                exact hAB' (by decide) hiT hiS
            · -- s1 out, t0 out: direct case 5
              have hs0 : (s 0).1 = j0 := by
                rcases htc 0 with h | h
                · exact h
                · exact absurd h hiT
              have ht1 : (t 1).1 = j0 := (htc 1).resolve_left hiS
              exact rank3_case5 hpW hlace hmono hs0 ht1 hiS hiT
                (hAB' (by decide) hiT hiS)
            · exact absurd rfl hne
    · -- no full copy
      have hw1 : ∀ j, (weldWSet s t j).card ≤ 1 := by
        intro j
        have h1 := weldWSet_card_le s t j
        have h2 : (weldWSet s t j).card ≠ 2 := fun h => hfull ⟨j, h⟩
        omega
      exact rank3_case1 hpW hlace hclass hmono hw1

#print axioms thm15_rank3

/-! ## Phase C: rank 4 with small pieces — the room-3 toolkit -/

section SmallTools

variable {ell : ℕ} {W' : Type} [DecidableEq W'] [Fintype W']

/-- Fresh vertex of a given color avoiding a small set, from an explicit class bound. -/
theorem exists_avoid_of_class {colW : Fin ell × W' → Bool} {rho : ℕ}
    (hclass : ∀ (j : Fin ell) (c : Bool),
      rho ≤ (Finset.univ.filter (fun w => colW (j, w) = c)).card)
    (j : Fin ell) (c : Bool) (avoid : Finset W') (h : avoid.card < rho) :
    ∃ y : W', colW (j, y) = c ∧ y ∉ avoid := by
  apply dpc_spare_avoid c avoid
  have h1 := hclass j c
  have h2 : (avoid.filter (fun w => colW (j, w) = c)).card ≤ avoid.card :=
    Finset.card_filter_le _ _
  omega

end SmallTools

section SmallGreedy

variable {W : Type} [DecidableEq W] [Fintype W]

private structure GreedyInv3 {ell n : ℕ} (col : Fin ell × W → Bool) (b : Bool)
    (s t : Fin n → Fin ell × W) (M : Fin ell → Fin ell → (W ≃ W))
    (done : Finset (Fin n)) (v u : Fin n → W) : Prop where
  vcol : ∀ i ∈ done, col ((s i).1, v i) = !b
  partner : ∀ i ∈ done, u i = M (s i).1 (t i).1 (v i)
  vT : ∀ i ∈ done, ∀ k, (t k).1 = (s i).1 → v i ≠ (t k).2
  uS : ∀ i ∈ done, ∀ k, (s k).1 = (t i).1 → u i ≠ (s k).2
  vv : ∀ i ∈ done, ∀ k ∈ done, k ≠ i → (s k).1 = (s i).1 → v k ≠ v i
  uu : ∀ i ∈ done, ∀ k ∈ done, k ≠ i → (t k).1 = (t i).1 → u k ≠ u i

private theorem small_greedy_aux {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hWne : Nonempty W)
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col) {rho : ℕ}
    (hclass : ∀ (j : Fin ell) (c : Bool),
      rho ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (b : Bool)
    (s t : Fin n → Fin ell × W) (D : Finset (Fin n))
    (hsplit : ∀ i ∈ D, (s i).1 ≠ (t i).1)
    (hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < rho) :
    ∀ (m : ℕ) (done : Finset (Fin n)), done ⊆ D → (D \ done).card = m →
      ∀ v u : Fin n → W, GreedyInv3 col b s t M done v u →
      ∃ v' u' : Fin n → W, GreedyInv3 col b s t M D v' u'
  | 0, done, hsub, hm, v, u, hInv => by
      have hDdone : D = done := by
        apply Finset.Subset.antisymm ?_ hsub
        intro x hx
        by_contra hxd
        have hmem : x ∈ D \ done := Finset.mem_sdiff.mpr ⟨hx, hxd⟩
        rw [Finset.card_eq_zero.mp hm] at hmem
        exact absurd hmem (Finset.notMem_empty x)
      refine ⟨v, u, ?_⟩
      rw [hDdone]
      exact hInv
  | m + 1, done, hsub, hm, v, u, hInv => by
      classical
      have hne : (D \ done).Nonempty := by
        rw [← Finset.card_pos, hm]; omega
      obtain ⟨i, hi⟩ := hne
      have hiD : i ∈ D := (Finset.mem_sdiff.mp hi).1
      have hidone : i ∉ done := (Finset.mem_sdiff.mp hi).2
      have hcnt := hcount i hiD
      -- the four exclusion sets in `W`-coordinates
      set Tset : Finset W :=
        (Finset.univ.filter (fun k => (t k).1 = (s i).1)).image (fun k => (t k).2)
      set Vused : Finset W :=
        (done.filter (fun k => (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).image v
      set Sset : Finset W :=
        (Finset.univ.filter (fun k => (s k).1 = (t i).1)).image (fun k => (s k).2)
      set Uused : Finset W := (done.filter (fun k => (t k).1 = (t i).1)).image u
      have hcard : (Tset ∪ Vused ∪
          (Sset ∪ Uused).image (fun w => (M (s i).1 (t i).1).symm w)).card < rho := by
        have h1 : Tset.card ≤ (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card :=
          Finset.card_image_le
        have h2 : Vused.card ≤
            (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card := by
          apply le_trans Finset.card_image_le
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hsub hk.1, fun he => hidone (he ▸ hk.1), hk.2.1, hk.2.2⟩
        have h3 : Sset.card ≤ (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card :=
          Finset.card_image_le
        have h4 : Uused.card ≤ (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card := by
          apply le_trans Finset.card_image_le
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hsub hk.1, fun he => hidone (he ▸ hk.1), hk.2⟩
        have h5 : (Tset ∪ Vused ∪
            (Sset ∪ Uused).image (fun w => (M (s i).1 (t i).1).symm w)).card
            ≤ Tset.card + Vused.card + (Sset.card + Uused.card) :=
          le_trans (Finset.card_union_le _ _)
            (add_le_add (Finset.card_union_le _ _)
              (le_trans Finset.card_image_le (Finset.card_union_le _ _)))
        omega
      obtain ⟨y, hyc, hyF⟩ := exists_avoid_of_class hclass (s i).1 (!b)
        (Tset ∪ Vused ∪ (Sset ∪ Uused).image (fun w => (M (s i).1 (t i).1).symm w)) hcard
      -- freshness helpers
      have hyT : ∀ w ∈ Tset, y ≠ w := fun w hw he =>
        hyF (he ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hw))
      have hyV : ∀ w ∈ Vused, y ≠ w := fun w hw he =>
        hyF (he ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hw))
      have hyMU : ∀ w ∈ Sset ∪ Uused, M (s i).1 (t i).1 y ≠ w := by
        intro w hw he
        apply hyF
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨w, hw, by rw [← he, Equiv.symm_apply_apply]⟩
      have hne' : ∀ k ∈ done, k ≠ i := fun k hk he => hidone (he ▸ hk)
      have hvfresh : ∀ k ∈ done, (s k).1 = (s i).1 → v k ≠ y := by
        intro k hk hsame he
        by_cases htk : (t k).1 = (t i).1
        · have h2 := hInv.partner k hk
          rw [hsame, htk, he] at h2
          exact hyMU (u k) (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, htk⟩, rfl⟩)) h2.symm
        · exact hyV (v k) (Finset.mem_image.mpr
            ⟨k, Finset.mem_filter.mpr ⟨hk, hsame, htk⟩, rfl⟩) he.symm
      have hufresh : ∀ k ∈ done, (t k).1 = (t i).1 → u k ≠ M (s i).1 (t i).1 y := by
        intro k hk htk he
        exact hyMU (u k) (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, htk⟩, rfl⟩)) he.symm
      -- extend the assignment and recurse
      refine small_greedy_aux hWne hproper hclass b s t D hsplit hcount m (insert i done)
        (Finset.insert_subset hiD hsub) ?_
        (Function.update v i y) (Function.update u i (M (s i).1 (t i).1 y)) ?_
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hi, hm]
        omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i' hi'
          rcases Finset.mem_insert.mp hi' with rfl | hi'done
          · rw [Function.update_self]
            exact hyc
          · rw [Function.update_of_ne (hne' i' hi'done)]
            exact hInv.vcol i' hi'done
        · intro i' hi'
          rcases Finset.mem_insert.mp hi' with rfl | hi'done
          · rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (hne' i' hi'done),
              Function.update_of_ne (hne' i' hi'done)]
            exact hInv.partner i' hi'done
        · intro i' hi' k hk
          rcases Finset.mem_insert.mp hi' with rfl | hi'done
          · rw [Function.update_self]
            exact hyT ((t k).2) (Finset.mem_image.mpr
              ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩)
          · rw [Function.update_of_ne (hne' i' hi'done)]
            exact hInv.vT i' hi'done k hk
        · intro i' hi' k hk
          rcases Finset.mem_insert.mp hi' with rfl | hi'done
          · rw [Function.update_self]
            exact hyMU ((s k).2) (Finset.mem_union_left _
              (Finset.mem_image.mpr
                ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩))
          · rw [Function.update_of_ne (hne' i' hi'done)]
            exact hInv.uS i' hi'done k hk
        · intro i' hi' k hk hki' hsame
          rcases Finset.mem_insert.mp hi' with rfl | hi'done <;>
            rcases Finset.mem_insert.mp hk with rfl | hkdone
          · exact absurd rfl hki'
          · rw [Function.update_of_ne (hne' k hkdone),
              Function.update_self]
            exact hvfresh k hkdone hsame
          · rw [Function.update_self,
              Function.update_of_ne (hne' i' hi'done)]
            exact (hvfresh i' hi'done hsame.symm).symm
          · rw [Function.update_of_ne (hne' k hkdone),
              Function.update_of_ne (hne' i' hi'done)]
            exact hInv.vv i' hi'done k hkdone hki' hsame
        · intro i' hi' k hk hki' hsame
          rcases Finset.mem_insert.mp hi' with rfl | hi'done <;>
            rcases Finset.mem_insert.mp hk with rfl | hkdone
          · exact absurd rfl hki'
          · rw [Function.update_of_ne (hne' k hkdone),
              Function.update_self]
            exact hufresh k hkdone hsame
          · rw [Function.update_self,
              Function.update_of_ne (hne' i' hi'done)]
            exact (hufresh i' hi'done hsame.symm).symm
          · rw [Function.update_of_ne (hne' k hkdone),
              Function.update_of_ne (hne' i' hi'done)]
            exact hInv.uu i' hi'done k hkdone hki' hsame

/-- **The greedy connector chooser** (Coleman's inductive `v_i, u_i` selection, Cases 1/5/6
    of Proposition 1.6). Produces, for every split pair `i ∈ D`, a target-colored `v i` in
    the source copy and its matching partner `u i` in the target copy, avoiding all target
    vertices of the source copy, all source vertices of the target copy, and each other. -/
theorem small_greedy {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hWne : Nonempty W)
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col) {rho : ℕ}
    (hclass : ∀ (j : Fin ell) (c : Bool),
      rho ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (b : Bool)
    (s t : Fin n → Fin ell × W) (D : Finset (Fin n))
    (hsplit : ∀ i ∈ D, (s i).1 ≠ (t i).1)
    (hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < rho) :
    ∃ v u : Fin n → W,
      (∀ i ∈ D, col ((s i).1, v i) = !b) ∧
      (∀ i ∈ D, col ((t i).1, u i) = b) ∧
      (∀ i ∈ D, u i = M (s i).1 (t i).1 (v i)) ∧
      (∀ i ∈ D, ∀ k, (t k).1 = (s i).1 → v i ≠ (t k).2) ∧
      (∀ i ∈ D, ∀ k, (s k).1 = (t i).1 → u i ≠ (s k).2) ∧
      (∀ i ∈ D, ∀ k ∈ D, k ≠ i → (s k).1 = (s i).1 → v k ≠ v i) ∧
      (∀ i ∈ D, ∀ k ∈ D, k ≠ i → (t k).1 = (t i).1 → u k ≠ u i) := by
  classical
  have hW : Nonempty W := hWne
  obtain ⟨w0⟩ := hW
  obtain ⟨v, u, hInv⟩ := small_greedy_aux hWne hproper hclass b s t D hsplit hcount (D \ ∅).card ∅
    (Finset.empty_subset D) rfl (fun _ => w0) (fun _ => w0)
    ⟨fun i hi => absurd hi (Finset.notMem_empty i),
     fun i hi => absurd hi (Finset.notMem_empty i),
     fun i hi => absurd hi (Finset.notMem_empty i),
     fun i hi => absurd hi (Finset.notMem_empty i),
     fun i hi => absurd hi (Finset.notMem_empty i),
     fun i hi => absurd hi (Finset.notMem_empty i)⟩
  refine ⟨v, u, hInv.vcol, ?_, hInv.partner, hInv.vT, hInv.uS, hInv.vv, hInv.uu⟩
  intro i hiD
  have hadj : (weldGraph ell Gs M).Adj ((s i).1, v i)
      ((t i).1, M (s i).1 (t i).1 (v i)) := weld_cross_adj (hsplit i hiD) (v i)
  rw [← hInv.partner i hiD] at hadj
  have hne := hproper _ _ hadj
  rw [hInv.vcol i hiD] at hne
  cases b <;> cases hcu : col ((t i).1, u i) <;> simp_all

end SmallGreedy

section SmallFamily

variable {W : Type} [DecidableEq W] [Fintype W]

theorem small_inner_family {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {col : Fin ell × W → Bool}
    (j : Fin ell) {b : Bool}
    (A : Finset (Fin n)) (hA1 : A.Nonempty)
    (hcovA : IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) A.card)
    (σs σt : Fin n → W)
    (hcs : ∀ i ∈ A, col (j, σs i) = b)
    (hct : ∀ i ∈ A, col (j, σt i) = !b)
    (his : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → σs i ≠ σs k)
    (hit : ∀ i ∈ A, ∀ k ∈ A, i ≠ k → σt i ≠ σt k) :
    ∃ Q : ∀ i ∈ A, (Gs j).Walk (σs i) (σt i),
      (∀ i (hi : i ∈ A), (Q i hi).IsPath) ∧
      (∀ x : W, ∃ i, ∃ hi : i ∈ A, x ∈ (Q i hi).support) ∧
      (∀ i (hi : i ∈ A), ∀ k (hk : k ∈ A), i ≠ k →
        ∀ x, ¬ (x ∈ (Q i hi).support ∧ x ∈ (Q k hk).support)) := by
  classical
  have e : {i // i ∈ A} ≃ Fin A.card :=
    Fintype.equivFinOfCardEq (Fintype.card_coe A)
  have hval : ∀ a a' : Fin A.card, (e.symm a).1 = (e.symm a').1 → a = a' := by
    intro a a' h
    have h2 := congrArg e (Subtype.ext h : e.symm a = e.symm a')
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h2
  have hd : OppositeDemand (fun w => col (j, w))
      (fun a : Fin A.card => σs (e.symm a).1) (fun a : Fin A.card => σt (e.symm a).1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      show col (j, σs (e.symm a).1) ≠ col (j, σt (e.symm a).1)
      rw [hcs _ (e.symm a).2, hct _ (e.symm a).2]
      cases b <;> simp
    · intro a a' ha
      dsimp only at ha
      by_contra hne
      exact his _ (e.symm a).2 _ (e.symm a').2 (fun h => hne (hval a a' h)) ha
    · intro a a' ha
      dsimp only at ha
      by_contra hne
      exact hit _ (e.symm a).2 _ (e.symm a').2 (fun h => hne (hval a a' h)) ha
    · intro a a' he
      dsimp only at he
      have h1 := hcs _ (e.symm a).2
      rw [he, hct _ (e.symm a').2] at h1
      cases b <;> simp_all
  obtain ⟨q, hqpath, hqcov, hqdisj⟩ := hcovA _ _ hd
  refine ⟨fun i hi => (q (e ⟨i, hi⟩)).copy
    (by simp) (by simp), ?_, ?_, ?_⟩
  · intro i hi
    rw [SimpleGraph.Walk.isPath_copy]
    exact hqpath _
  · intro x
    obtain ⟨a, ha⟩ := hqcov x
    refine ⟨(e.symm a).1, (e.symm a).2, ?_⟩
    rw [SimpleGraph.Walk.support_copy]
    have hea : e ⟨(e.symm a).1, (e.symm a).2⟩ = a := e.apply_symm_apply a
    rw [hea]
    exact ha
  · intro i hi k hk hik x hx
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hx
    refine hqdisj (e ⟨i, hi⟩) (e ⟨k, hk⟩) ?_ x hx
    intro h
    exact hik (congrArg Subtype.val (e.injective h))

end SmallFamily

section SmallCase1

variable {W : Type} [DecidableEq W] [Fintype W]

theorem small_case1 {ell : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hWne : Nonempty W)
    {b : Bool} {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    (hw : ∀ j, (weldWSet s t j).card ≤ 2) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  -- the split indices
  set D : Finset (Fin 3) := Finset.univ.filter (fun i => (s i).1 ≠ (t i).1) with hD
  have hDmem : ∀ i, i ∈ D ↔ (s i).1 ≠ (t i).1 := by
    intro i
    rw [hD, Finset.mem_filter]
    simp
  have hsplit : ∀ i ∈ D, (s i).1 ≠ (t i).1 := fun i hi => (hDmem i).mp hi
  -- the greedy room bound: both sides contribute at most `w_j − 1 ≤ n − 2`
  have hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card < 3 := by
    intro i hiD
    have hsi := hsplit i hiD
    have hi_mem1 : i ∈ (Finset.univ.filter (fun k => (s k).1 = (s i).1)) \
        (Finset.univ.filter (fun k => (t k).1 = (s i).1)) := by
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ i, rfl⟩, fun h => hsi h.2.symm⟩
    have h2 : (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
        ≤ ((Finset.univ.filter (fun k => (s k).1 = (s i).1)) \
           (Finset.univ.filter (fun k => (t k).1 = (s i).1))).card - 1 := by
      have hsub : D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)
          ⊆ (((Finset.univ.filter (fun k => (s k).1 = (s i).1)) \
             (Finset.univ.filter (fun k => (t k).1 = (s i).1))).erase i) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
        refine ⟨hk.2.1, ⟨⟨Finset.mem_univ k, hk.2.2.1⟩, ?_⟩⟩
        intro hmem
        exact (hsplit k hk.1) (hk.2.2.1.trans hmem.2.symm)
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_erase_of_mem hi_mem1] at hle
    have hid1 := weldWSet_card_split_t s t (s i).1
    have hw1 := hw (s i).1
    have hi_mem2 : i ∈ (Finset.univ.filter (fun k => (t k).1 = (t i).1)) \
        (Finset.univ.filter (fun k => (s k).1 = (t i).1)) := by
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ i, rfl⟩, fun h => hsi h.2⟩
    have h4 : (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
        ≤ ((Finset.univ.filter (fun k => (t k).1 = (t i).1)) \
           (Finset.univ.filter (fun k => (s k).1 = (t i).1))).card - 1 := by
      have hsub : D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)
          ⊆ (((Finset.univ.filter (fun k => (t k).1 = (t i).1)) \
             (Finset.univ.filter (fun k => (s k).1 = (t i).1))).erase i) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
        refine ⟨hk.2.1, ⟨⟨Finset.mem_univ k, hk.2.2⟩, ?_⟩⟩
        intro hmem
        exact (hsplit k hk.1) (hmem.2.trans hk.2.2.symm)
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_erase_of_mem hi_mem2] at hle
    have hid2 := weldWSet_card_split_s s t (t i).1
    have hw2 := hw (t i).1
    have hp1 := Finset.card_pos.mpr ⟨i, hi_mem1⟩
    have hp2 := Finset.card_pos.mpr ⟨i, hi_mem2⟩
    omega
  -- greedy connectors
  obtain ⟨v, u, hvcol, hucol, hpart, hvT, huS, hvv, huu⟩ := small_greedy hWne hproper hclass b s t D hsplit hcount
  -- the touched copies
  set J : Finset (Fin ell) := Finset.univ.filter (fun j => (weldWSet s t j).Nonempty) with hJ
  have hJmem : ∀ j, j ∈ J ↔ (weldWSet s t j).Nonempty := by
    intro j
    rw [hJ, Finset.mem_filter]
    simp
  -- one inner family per touched copy
  have hfam : ∀ j ∈ J, ∃ Q : ∀ i ∈ weldWSet s t j,
      (Gs j).Walk (wInnerS s u j i) (wInnerT t v j i),
      (∀ i (hi : i ∈ weldWSet s t j), (Q i hi).IsPath) ∧
      (∀ x : W, ∃ i, ∃ hi : i ∈ weldWSet s t j, x ∈ (Q i hi).support) ∧
      (∀ i (hi : i ∈ weldWSet s t j), ∀ k (hk : k ∈ weldWSet s t j), i ≠ k →
        ∀ x, ¬ (x ∈ (Q i hi).support ∧ x ∈ (Q k hk).support)) := by
    intro j hjJ
    have hcardw := hw j
    have hposw : 0 < (weldWSet s t j).card := Finset.card_pos.mpr ((hJmem j).mp hjJ)
    have hcovA : IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w))
        (weldWSet s t j).card := by
      rcases (by omega : (weldWSet s t j).card = 1 ∨ (weldWSet s t j).card = 2) with h | h
      · rw [h]
        exact paired_one_opposite_iff_hamLaceable.mpr (hlace j)
      · rw [h]
        exact hcov2 j
    apply small_inner_family (b := b) j (weldWSet s t j) ((hJmem j).mp hjJ) hcovA
    · -- inner sources are `b`-colored
      intro i hi
      by_cases hsij : (s i).1 = j
      · rw [wInnerS_src hsij, ← hsij]
        exact hmono.1 i
      · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
        have hiD : i ∈ D := (hDmem i).mpr (fun h => hsij (h.trans htij))
        rw [wInnerS_conn hsij, ← htij]
        exact hucol i hiD
    · -- inner targets are `!b`-colored
      intro i hi
      by_cases htij : (t i).1 = j
      · rw [wInnerT_tgt htij, ← htij]
        exact hmono.2.1 i
      · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
        have hiD : i ∈ D := (hDmem i).mpr (fun h => htij (h.symm.trans hsij))
        rw [wInnerT_conn htij, ← hsij]
        exact hvcol i hiD
    · -- inner sources are injective on the touched index set
      intro i hi k hk hik
      by_cases hsij : (s i).1 = j <;> by_cases hskj : (s k).1 = j
      · rw [wInnerS_src hsij, wInnerS_src hskj]
        intro he
        exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
      · have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
        have hkD : k ∈ D := (hDmem k).mpr (fun h => hskj (h.trans htkj))
        rw [wInnerS_src hsij, wInnerS_conn hskj]
        exact fun he => huS k hkD i (hsij.trans htkj.symm) he.symm
      · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
        have hiD : i ∈ D := (hDmem i).mpr (fun h => hsij (h.trans htij))
        rw [wInnerS_conn hsij, wInnerS_src hskj]
        exact huS i hiD k (hskj.trans htij.symm)
      · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
        have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
        have hiD : i ∈ D := (hDmem i).mpr (fun h => hsij (h.trans htij))
        have hkD : k ∈ D := (hDmem k).mpr (fun h => hskj (h.trans htkj))
        rw [wInnerS_conn hsij, wInnerS_conn hskj]
        exact huu k hkD i hiD hik (htij.trans htkj.symm)
    · -- inner targets are injective on the touched index set
      intro i hi k hk hik
      by_cases htij : (t i).1 = j <;> by_cases htkj : (t k).1 = j
      · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
        intro he
        exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
      · have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
        have hkD : k ∈ D := (hDmem k).mpr (fun h => htkj (h.symm.trans hskj))
        rw [wInnerT_tgt htij, wInnerT_conn htkj]
        exact fun he => hvT k hkD i (htij.trans hskj.symm) he.symm
      · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
        have hiD : i ∈ D := (hDmem i).mpr (fun h => htij (h.symm.trans hsij))
        rw [wInnerT_conn htij, wInnerT_tgt htkj]
        exact hvT i hiD k (htkj.trans hsij.symm)
      · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
        have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
        have hiD : i ∈ D := (hDmem i).mpr (fun h => htij (h.symm.trans hsij))
        have hkD : k ∈ D := (hDmem k).mpr (fun h => htkj (h.symm.trans hskj))
        rw [wInnerT_conn htij, wInnerT_conn htkj]
        exact hvv k hkD i hiD hik (hsij.trans hskj.symm)
  choose Q hQpath hQcov hQdisj using hfam
  -- the global path of each pair, with a support characterization
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((x.1 = (s i).1 ∨ x.1 = (t i).1) ∧
          ∃ (hj : x.1 ∈ J) (hi : i ∈ weldWSet s t x.1), x.2 ∈ (Q x.1 hj i hi).support) := by
    intro i
    have hiw1 : i ∈ weldWSet s t (s i).1 := mem_weldWSet.mpr (Or.inl rfl)
    have hiw2 : i ∈ weldWSet s t (t i).1 := mem_weldWSet.mpr (Or.inr rfl)
    have hj1 : (s i).1 ∈ J := (hJmem _).mpr ⟨i, hiw1⟩
    have hj2 : (t i).1 ∈ J := (hJmem _).mpr ⟨i, hiw2⟩
    by_cases hsp : (s i).1 = (t i).1
    · -- within-copy pair: its inner path, lifted
      have he1 : wInnerS s u (s i).1 i = (s i).2 := wInnerS_src rfl
      have he2 : wInnerT t v (s i).1 i = (t i).2 := wInnerT_tgt hsp.symm
      refine ⟨((Q (s i).1 hj1 i hiw1).map (weldLift Gs M (s i).1)).copy
        (by rw [he1]; exact Prod.ext rfl rfl)
        (by rw [he2]; exact Prod.ext hsp rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) (hQpath _ hj1 i hiw1)
      · rintro ⟨xj, xw⟩
        rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair]
        constructor
        · rintro ⟨rfl, hx2⟩
          exact ⟨Or.inl rfl, hj1, hiw1, hx2⟩
        · rintro ⟨hor, hj, hi, hx2⟩
          obtain rfl : xj = (s i).1 := by
            rcases hor with h | h
            · exact h
            · exact h.trans hsp.symm
          exact ⟨rfl, hx2⟩
    · -- split pair: source segment, matching edge, target segment
      have hiD : i ∈ D := (hDmem i).mpr hsp
      have he1 : wInnerS s u (s i).1 i = (s i).2 := wInnerS_src rfl
      have he2 : wInnerT t v (s i).1 i = v i := wInnerT_conn (fun h => hsp h.symm)
      have he3 : wInnerS s u (t i).1 i = u i := wInnerS_conn hsp
      have he4 : wInnerT t v (t i).1 i = (t i).2 := wInnerT_tgt rfl
      obtain ⟨R, hRp, hRs⟩ := weld_splice hsp
        ((Q (s i).1 hj1 i hiw1).copy he1 he2)
        ((Q (t i).1 hj2 i hiw2).copy he3 he4)
        (by rw [SimpleGraph.Walk.isPath_copy]; exact hQpath _ hj1 i hiw1)
        (by rw [SimpleGraph.Walk.isPath_copy]; exact hQpath _ hj2 i hiw2)
        (hpart i hiD)
      refine ⟨R.copy (Prod.ext rfl rfl) (Prod.ext rfl rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hRp
      · rintro ⟨xj, xw⟩
        rw [SimpleGraph.Walk.support_copy, hRs]
        rw [List.mem_append, mem_map_pair, mem_map_pair,
          SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy]
        constructor
        · rintro (⟨rfl, hx2⟩ | ⟨rfl, hx2⟩)
          · exact ⟨Or.inl rfl, hj1, hiw1, hx2⟩
          · exact ⟨Or.inr rfl, hj2, hiw2, hx2⟩
        · rintro ⟨hor, hj, hi, hx2⟩
          rcases hor with rfl | rfl
          · exact Or.inl ⟨rfl, hx2⟩
          · exact Or.inr ⟨rfl, hx2⟩
  choose P hPpath hPsupp using hpaths
  -- close with Lemma 2.1 over the untouched copies
  -- n = 3 = 2 + 1 literal
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) J P hPpath ?_ ?_ ?_
  · intro i x hx
    obtain ⟨-, hj, -, -⟩ := (hPsupp i x).mp hx
    exact hj
  · intro x hxJ
    obtain ⟨i, hi, hmem⟩ := hQcov x.1 hxJ x.2
    refine ⟨i, (hPsupp i x).mpr ⟨?_, hxJ, hi, hmem⟩⟩
    rcases mem_weldWSet.mp hi with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · intro a c hac x hx
    obtain ⟨-, hja, hia, hma⟩ := (hPsupp a x).mp hx.1
    obtain ⟨-, hjc, hic, hmc⟩ := (hPsupp c x).mp hx.2
    exact hQdisj x.1 hja a hia c hic hac x.2 ⟨hma, hmc⟩

#print axioms prop16_case1

/-! ## Case 2: all terminals in one copy

Subcase (i) core (`prop16_case2_one_core`): the inner `m`-cover of copy `j0` has one path
carrying both extra terminals `sn = (s (last)).2` and `tn = (t (last)).2`; that path splits
as `A ++ Pmid ++ C` where `Pmid` joins `sn` to `tn`. `Pmid` becomes the extra pair's path;
`A` and `C` are rejoined through a Hamilton path of a fresh copy `j2` (the two detour
endpoints have opposite colors because the two cut edges are proper). -/


end SmallCase1

section SmallCase2

variable {W : Type} [DecidableEq W] [Fintype W]

private theorem small_case2_one_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w)))
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ m →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hm2 : 2 ≤ m) (hEllm : m + 2 ≤ ell) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∀ i, (t i).1 = j0)
    (q : ∀ i : Fin m, (Gs j0).Walk (s i.castSucc).2 (t i.castSucc).2)
    (hqcov : ∀ x : W, ∃ i, x ∈ (q i).support)
    (hqdis : ∀ i k, i ≠ k → ∀ x, ¬ (x ∈ (q i).support ∧ x ∈ (q k).support))
    (a : Fin m) {y z : W}
    (A : (Gs j0).Walk (s a.castSucc).2 y)
    (Pmid : (Gs j0).Walk (s (Fin.last m)).2 (t (Fin.last m)).2)
    (C : (Gs j0).Walk z (t a.castSucc).2)
    (hA : A.IsPath) (hP : Pmid.IsPath) (hC : C.IsPath)
    (hyz : col (j0, y) ≠ col (j0, z))
    (hqpath : ∀ i, i ≠ a → (q i).IsPath)
    (hcov : ∀ x, x ∈ (q a).support → x ∈ A.support ∨ x ∈ Pmid.support ∨ x ∈ C.support)
    (hsubA : ∀ x ∈ A.support, x ∈ (q a).support)
    (hsubP : ∀ x ∈ Pmid.support, x ∈ (q a).support)
    (hsubC : ∀ x ∈ C.support, x ∈ (q a).support)
    (hdAP : ∀ x ∈ A.support, x ∉ Pmid.support)
    (hdAC : ∀ x ∈ A.support, x ∉ C.support)
    (hdPC : ∀ x ∈ Pmid.support, x ∉ C.support) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn : 3 ≤ m + 1 := by omega
  have hEll : m + 1 + 1 ≤ ell := by omega
  -- a fresh copy for the detour
  obtain ⟨j2, -, hj2, -, -⟩ := fin_exists_two_ne (by omega) j0
  have hj02 : j0 ≠ j2 := fun h => hj2 h.symm
  -- the detour endpoints and the Hamilton bridge
  have hadj_in : (weldGraph ell Gs M).Adj (j0, y) (j2, M j0 j2 y) := weld_cross_adj hj02 y
  have hadj_out : (weldGraph ell Gs M).Adj (j2, M j0 j2 z) (j0, z) :=
    (weld_cross_adj hj02 z).symm
  have hcolbridge : col (j2, M j0 j2 y) ≠ col (j2, M j0 j2 z) := by
    have h1 := hproper _ _ hadj_in
    have h2 := hproper _ _ hadj_out
    cases hcy : col (j0, y) <;> cases hcz : col (j0, z) <;>
      cases hys : col (j2, M j0 j2 y) <;> cases hzs : col (j2, M j0 j2 z) <;> simp_all
  obtain ⟨hw, hham⟩ := hlace j2 _ _ hcolbridge
  -- assemble the detoured path of pair `a`
  have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s a.castSucc) (j0, y), R.IsPath ∧
      R.support = A.support.map (fun w => (j0, w)) := by
    refine ⟨(A.map (weldLift Gs M j0)).copy (Prod.ext (hS a.castSucc).symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
  obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ hw hR₀p hham.isPath hadj_in
    (by
      intro w' _ hmem
      rw [hR₀s, mem_map_pair] at hmem
      exact hj02 hmem.1.symm)
  obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ C hR₁p hC hadj_out
    (by
      intro w' hw' hmem
      rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨-, hmem⟩ | ⟨h1, -⟩
      · exact hdAC _ hmem hw'
      · exact hj02 h1)
  -- the global family with a support characterization
  have hpaths : ∀ k : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s k) (t k), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        (if k = Fin.last m then x.1 = j0 ∧ x.2 ∈ Pmid.support
         else if k = a.castSucc then
           (x.1 = j0 ∧ (x.2 ∈ A.support ∨ x.2 ∈ C.support)) ∨ (x.1 = j2 ∧ x.2 ∈ hw.support)
         else x.1 = j0 ∧ ∃ i : Fin m, k = i.castSucc ∧ x.2 ∈ (q i).support) := by
    intro k
    by_cases hk1 : k = Fin.last m
    · subst hk1
      refine ⟨(Pmid.map (weldLift Gs M j0)).copy
        (Prod.ext (hS _).symm rfl) (Prod.ext (hT _).symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hP
      · intro x
        rw [if_pos rfl, SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair]
    · by_cases hk2 : k = a.castSucc
      · subst hk2
        refine ⟨R₂.copy rfl (Prod.ext (hT _).symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₂p
        · intro x
          rw [if_neg hk1, if_pos rfl, SimpleGraph.Walk.support_copy, hR₂s, hR₁s, hR₀s]
          rw [List.mem_append, List.mem_append, mem_map_pair, mem_map_pair, mem_map_pair]
          constructor
          · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, Or.inl h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl ⟨h1, Or.inr h2⟩
          · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
            · exact Or.inl (Or.inl ⟨h1, h2⟩)
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · obtain ⟨i, hik⟩ := Fin.eq_castSucc_of_ne_last hk1
        subst hik
        have hia : i ≠ a := fun h => hk2 (by rw [h])
        refine ⟨((q i).map (weldLift Gs M j0)).copy
          (Prod.ext (hS _).symm rfl) (Prod.ext (hT _).symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) (hqpath i hia)
        · intro x
          rw [if_neg hk1, if_neg hk2, SimpleGraph.Walk.support_copy, weldLift_support,
            mem_map_pair]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, i, rfl, h2⟩
          · rintro ⟨h1, i', hi', h2⟩
            have : i' = i := Fin.castSucc_injective m hi'.symm
            subst this
            exact ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  -- normalized membership fact
  have hnorm : ∀ (k : Fin (m + 1)) (x : Fin ell × W), x ∈ (P k).support →
      (k = Fin.last m ∧ x.1 = j0 ∧ x.2 ∈ Pmid.support) ∨
      (k = a.castSucc ∧
        ((x.1 = j0 ∧ (x.2 ∈ A.support ∨ x.2 ∈ C.support)) ∨ (x.1 = j2 ∧ x.2 ∈ hw.support))) ∨
      (k ≠ Fin.last m ∧ k ≠ a.castSucc ∧ x.1 = j0 ∧
        ∃ i : Fin m, k = i.castSucc ∧ x.2 ∈ (q i).support) := by
    intro k x hx
    have h := (hPchar k x).mp hx
    by_cases hk1 : k = Fin.last m
    · rw [if_pos hk1] at h
      exact Or.inl ⟨hk1, h⟩
    · rw [if_neg hk1] at h
      by_cases hk2 : k = a.castSucc
      · rw [if_pos hk2] at h
        exact Or.inr (Or.inl ⟨hk2, h⟩)
      · rw [if_neg hk2] at h
        exact Or.inr (Or.inr ⟨hk1, hk2, h⟩)
  -- close by Lemma 2.1 over the untouched copies
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) ({j0, j2} : Finset (Fin ell))
    P hPp ?_ ?_ ?_
  · intro k x hx
    rcases hnorm k x hx with ⟨-, h1, -⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, -, h1, -⟩ <;>
      simp [h1]
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl
    · -- copy j0 is covered by the redistributed inner cover
      obtain ⟨i, hi⟩ := hqcov xw
      by_cases hia : i = a
      · subst hia
        rcases hcov xw hi with hmem | hmem | hmem
        · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
          rw [if_neg (Fin.castSucc_lt_last i).ne, if_pos rfl]
          exact Or.inl ⟨rfl, Or.inl hmem⟩
        · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
          rw [if_pos rfl]
          exact ⟨rfl, hmem⟩
        · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
          rw [if_neg (Fin.castSucc_lt_last i).ne, if_pos rfl]
          exact Or.inl ⟨rfl, Or.inr hmem⟩
      · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
        rw [if_neg (Fin.castSucc_lt_last i).ne,
          if_neg (fun h => hia (Fin.castSucc_injective m h))]
        exact ⟨rfl, i, rfl, hi⟩
    · -- copy j2 is covered by the Hamilton bridge
      refine ⟨a.castSucc, (hPchar a.castSucc (xj, xw)).mpr ?_⟩
      rw [if_neg (Fin.castSucc_lt_last a).ne, if_pos rfl]
      exact Or.inr ⟨rfl, hham.mem_support xw⟩
  · intro k k' hkk' x hx
    rcases hnorm k x hx.1 with ⟨hk, hx1, hxm⟩ | ⟨hk, ⟨hx1, hxm⟩ | ⟨hx1, hxm⟩⟩ |
        ⟨hk1, hk2, hx1, i, hki, hxm⟩ <;>
      rcases hnorm k' x hx.2 with ⟨hk', hx1', hxm'⟩ | ⟨hk', ⟨hx1', hxm'⟩ | ⟨hx1', hxm'⟩⟩ |
        ⟨hk1', hk2', hx1', i', hki', hxm'⟩
    · exact hkk' (hk.trans hk'.symm)
    · rcases hxm' with h | h
      · exact hdAP _ h hxm
      · exact hdPC _ hxm h
    · exact hj02 (hx1.symm.trans hx1')
    · exact hqdis a i' (fun h => hk2' (by rw [hki', ← h])) x.2
        ⟨hsubP _ hxm, hxm'⟩
    · rcases hxm with h | h
      · exact hdAP _ h hxm'
      · exact hdPC _ hxm' h
    · exact hkk' (hk.trans hk'.symm)
    · exact hj02 (hx1.symm.trans hx1')
    · rcases hxm with h | h
      · exact hqdis a i' (fun hh => hk2' (by rw [hki', ← hh])) x.2 ⟨hsubA _ h, hxm'⟩
      · exact hqdis a i' (fun hh => hk2' (by rw [hki', ← hh])) x.2 ⟨hsubC _ h, hxm'⟩
    · exact hj02 (hx1'.symm.trans hx1)
    · exact hj02 (hx1'.symm.trans hx1)
    · exact hkk' (hk.trans hk'.symm)
    · exact hj02 (hx1'.symm.trans hx1)
    · exact hqdis a i (fun h => hk2 (by rw [hki, ← h])) x.2 ⟨hsubP _ hxm', hxm⟩
    · rcases hxm' with h | h
      · exact hqdis a i (fun hh => hk2 (by rw [hki, ← hh])) x.2 ⟨hsubA _ h, hxm⟩
      · exact hqdis a i (fun hh => hk2 (by rw [hki, ← hh])) x.2 ⟨hsubC _ h, hxm⟩
    · exact hj02 (hx1.symm.trans hx1')
    · have hii' : i ≠ i' := by
        intro h
        exact hkk' (by rw [hki, hki', h])
      exact hqdis i i' hii' x.2 ⟨hxm, hxm'⟩

set_option maxHeartbeats 1600000 in
/-- Case 2, subcase (i): one inner path carries both extra terminals. Split it at the two
    terminals (in whichever order they occur) and hand the pieces to the core. -/
private theorem small_case2_one {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w)))
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ m →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hm2 : 2 ≤ m) (hEllm : m + 2 ≤ ell) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∀ i, (t i).1 = j0)
    (q : ∀ i : Fin m, (Gs j0).Walk (s i.castSucc).2 (t i.castSucc).2)
    (hqp : ∀ i, (q i).IsPath)
    (hqcov : ∀ x : W, ∃ i, x ∈ (q i).support)
    (hqdis : ∀ i k, i ≠ k → ∀ x, ¬ (x ∈ (q i).support ∧ x ∈ (q k).support))
    (a : Fin m) (hsn : (s (Fin.last m)).2 ∈ (q a).support)
    (htn : (t (Fin.last m)).2 ∈ (q a).support) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hcolS : ∀ i, col (j0, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, col (j0, (t i).2) = !b := by
    intro i
    rw [← hT i]
    exact hmono.2.1 i
  have hsinj : ∀ i k : Fin (m + 1), (s i).2 = (s k).2 → i = k := by
    intro i k he
    exact hmono.2.2.1 (Prod.ext ((hS i).trans (hS k).symm) he)
  have htinj : ∀ i k : Fin (m + 1), (t i).2 = (t k).2 → i = k := by
    intro i k he
    exact hmono.2.2.2 (Prod.ext ((hT i).trans (hT k).symm) he)
  have hstne : ∀ i k : Fin (m + 1), (s i).2 ≠ (t k).2 := by
    intro i k he
    have h1 := hcolS i
    rw [he, hcolT k] at h1
    cases b <;> simp_all
  have hbal := (hcopy_eq j0).1
  have hsn_src : (s (Fin.last m)).2 ≠ (s a.castSucc).2 :=
    fun he => (Fin.castSucc_lt_last a).ne' (hsinj _ _ he)
  have hsn_tgt : (s (Fin.last m)).2 ≠ (t a.castSucc).2 := hstne _ _
  have htn_tgt : (t (Fin.last m)).2 ≠ (t a.castSucc).2 :=
    fun he => (Fin.castSucc_lt_last a).ne' (htinj _ _ he)
  have htn_src : (t (Fin.last m)).2 ≠ (s a.castSucc).2 :=
    fun he => hstne a.castSucc (Fin.last m) he.symm
  rcases dropUntil_mem_or (q a) htn hsn with horder | horder
  · -- `sn` comes first
    obtain ⟨y, z, A, Bmid, C, hA, hB, hC, hyadj, hzadj, hsupp⟩ :=
      path_split_both (q a) (hqp a) hsn horder hsn_src htn_tgt
    have hyz : col (j0, y) ≠ col (j0, z) := by
      have h1 := hbal _ _ hyadj
      have h2 := hbal _ _ hzadj
      have hcs := hcolS (Fin.last m)
      have hct := hcolT (Fin.last m)
      cases hcy : col (j0, y) <;> cases hcz : col (j0, z) <;> cases b <;> simp_all
    have hnodup := (hqp a).support_nodup
    rw [hsupp, List.nodup_append, List.nodup_append] at hnodup
    refine small_case2_one_core hproper hlace hcopy_eq hcovlev hm2 hEllm hmono hS hT q hqcov hqdis a A Bmid C hA hB hC hyz
      (fun i _ => hqp i) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append] at hx
      tauto
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx hmem
      exact hnodup.1.2.2 x hx x hmem rfl
    · intro x hx hmem
      exact hnodup.2.2 x (List.mem_append.mpr (Or.inl hx)) x hmem rfl
    · intro x hx hmem
      exact hnodup.2.2 x (List.mem_append.mpr (Or.inr hx)) x hmem rfl
  · -- `tn` comes first: same surgery, reversed middle piece
    obtain ⟨y, z, A, Bmid, C, hA, hB, hC, hyadj, hzadj, hsupp⟩ :=
      path_split_both (q a) (hqp a) htn horder htn_src hsn_tgt
    have hyz : col (j0, y) ≠ col (j0, z) := by
      have h1 := hbal _ _ hyadj
      have h2 := hbal _ _ hzadj
      have hcs := hcolS (Fin.last m)
      have hct := hcolT (Fin.last m)
      cases hcy : col (j0, y) <;> cases hcz : col (j0, z) <;> cases b <;> simp_all
    have hnodup := (hqp a).support_nodup
    rw [hsupp, List.nodup_append, List.nodup_append] at hnodup
    refine small_case2_one_core hproper hlace hcopy_eq hcovlev hm2 hEllm hmono hS hT q hqcov hqdis a A Bmid.reverse C hA
      hB.reverse hC hyz (fun i _ => hqp i) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append] at hx
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
      tauto
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx
      rw [hsupp, List.mem_append, List.mem_append]
      tauto
    · intro x hx hmem
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
      exact hnodup.1.2.2 x hx x hmem rfl
    · intro x hx hmem
      exact hnodup.2.2 x (List.mem_append.mpr (Or.inl hx)) x hmem rfl
    · intro x hx hmem
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
      exact hnodup.2.2 x (List.mem_append.mpr (Or.inr hx)) x hmem rfl

set_option maxHeartbeats 6400000 in
/-- Case 2, subcase (ii): the two extra terminals lie on two different inner paths. Each
    carrier path is cut around its terminal; the two cut paths are rerouted through a
    2-cover of a fresh copy `j2`, and the freed terminal edges are joined into the extra
    pair's path through a Hamilton bridge of a second fresh copy `j3`. -/
private theorem small_case2_two {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w)))
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ m →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hm2 : 2 ≤ m) (hEllm : m + 2 ≤ ell) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∀ i, (t i).1 = j0)
    (q : ∀ i : Fin m, (Gs j0).Walk (s i.castSucc).2 (t i.castSucc).2)
    (hqp : ∀ i, (q i).IsPath)
    (hqcov : ∀ x : W, ∃ i, x ∈ (q i).support)
    (hqdis : ∀ i k, i ≠ k → ∀ x, ¬ (x ∈ (q i).support ∧ x ∈ (q k).support))
    (a c : Fin m) (hac : a ≠ c)
    (hsn : (s (Fin.last m)).2 ∈ (q a).support)
    (htn : (t (Fin.last m)).2 ∈ (q c).support) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn : 3 ≤ m + 1 := by omega
  have hEll : m + 1 + 1 ≤ ell := by omega
  have hm2 : 2 ≤ m := by omega
  have hfin2 : ∀ i : Fin 2, i ≠ 0 → i = 1 := by decide
  have hcolS : ∀ i, col (j0, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, col (j0, (t i).2) = !b := by
    intro i
    rw [← hT i]
    exact hmono.2.1 i
  have hsinj : ∀ i k : Fin (m + 1), (s i).2 = (s k).2 → i = k := by
    intro i k he
    exact hmono.2.2.1 (Prod.ext ((hS i).trans (hS k).symm) he)
  have htinj : ∀ i k : Fin (m + 1), (t i).2 = (t k).2 → i = k := by
    intro i k he
    exact hmono.2.2.2 (Prod.ext ((hT i).trans (hT k).symm) he)
  have hstne : ∀ i k : Fin (m + 1), (s i).2 ≠ (t k).2 := by
    intro i k he
    have h1 := hcolS i
    rw [he, hcolT k] at h1
    cases b <;> simp_all
  have hbal := (hcopy_eq j0).1
  -- split the carrier of `sn` and peel its predecessor
  obtain ⟨y₁, z₁, A₁, B₁, hA₁, hB₁, hyadj₁, hzadj₁, hsupp_a⟩ :=
    path_split_interior (q a) (hqp a) hsn
      (fun he => (Fin.castSucc_lt_last a).ne' (hsinj _ _ he))
      (hstne (Fin.last m) a.castSucc)
  have hcol_y₁ : col (j0, y₁) = !b := by
    have h := hbal _ _ hyadj₁
    dsimp only at h
    rw [hcolS (Fin.last m)] at h
    cases hcy : col (j0, y₁) <;> cases b <;> simp_all
  have hcol_z₁ : col (j0, z₁) = !b := by
    have h := hbal _ _ hzadj₁
    dsimp only at h
    rw [hcolS (Fin.last m)] at h
    cases hcy : col (j0, z₁) <;> cases b <;> simp_all
  obtain ⟨u1, A₂, hA₂, hadj_u1y₁, hsuppA₁, hy₁nA₂⟩ := path_peel_last A₁ hA₁
    (by
      intro he
      rw [he, hcolS a.castSucc] at hcol_y₁
      exact absurd hcol_y₁ (by cases b <;> simp))
  have hcol_u1 : col (j0, u1) = b := by
    have h := hbal _ _ hadj_u1y₁
    dsimp only at h
    rw [hcol_y₁] at h
    cases hcy : col (j0, u1) <;> cases b <;> simp_all
  -- split the carrier of `tn` and peel its successor's successor
  obtain ⟨y₂, z₂, C₁, D₁, hC₁, hD₁, hyadj₂, hzadj₂, hsupp_c⟩ :=
    path_split_interior (q c) (hqp c) htn
      (fun he => hstne c.castSucc (Fin.last m) he.symm)
      (fun he => (Fin.castSucc_lt_last c).ne' (htinj _ _ he))
  have hcol_y₂ : col (j0, y₂) = b := by
    have h := hbal _ _ hyadj₂
    dsimp only at h
    rw [hcolT (Fin.last m)] at h
    cases hcy : col (j0, y₂) <;> cases b <;> simp_all
  have hcol_z₂ : col (j0, z₂) = b := by
    have h := hbal _ _ hzadj₂
    dsimp only at h
    rw [hcolT (Fin.last m)] at h
    cases hcy : col (j0, z₂) <;> cases b <;> simp_all
  obtain ⟨v2, D₂, hD₂, hadj_z₂v2, hsuppD₁, hz₂nD₂⟩ := path_peel_head D₁ hD₁
    (by
      intro he
      rw [he, hcolT c.castSucc] at hcol_z₂
      exact absurd hcol_z₂ (by cases b <;> simp))
  have hcol_v2 : col (j0, v2) = !b := by
    have h := hbal _ _ hadj_z₂v2
    dsimp only at h
    rw [hcol_z₂] at h
    cases hcy : col (j0, v2) <;> cases b <;> simp_all
  -- two fresh copies
  obtain ⟨j2, j3, hj2, hj3, hj23⟩ := fin_exists_two_ne (by omega) j0
  have hj02 : j0 ≠ j2 := fun h => hj2 h.symm
  have hj03 : j0 ≠ j3 := fun h => hj3 h.symm
  have hstar2 : ∀ w : W, col (j2, M j0 j2 w) = !(col (j0, w)) := by
    intro w
    have h := hproper _ _ (weld_cross_adj hj02 w)
    cases h1 : col (j0, w) <;> cases h2 : col (j2, M j0 j2 w) <;> simp_all
  have hstar3 : ∀ w : W, col (j3, M j0 j3 w) = !(col (j0, w)) := by
    intro w
    have h := hproper _ _ (weld_cross_adj hj03 w)
    cases h1 : col (j0, w) <;> cases h2 : col (j3, M j0 j3 w) <;> simp_all
  -- membership bookkeeping
  have hy₁qa : y₁ ∈ (q a).support := by
    rw [hsupp_a]
    exact List.mem_append.mpr (Or.inl A₁.end_mem_support)
  have hz₁qa : z₁ ∈ (q a).support := by
    rw [hsupp_a]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ B₁.start_mem_support))
  have hA₂sub : ∀ w ∈ A₂.support, w ∈ (q a).support := by
    intro w hw
    rw [hsupp_a]
    exact List.mem_append.mpr (Or.inl (by
      rw [hsuppA₁]
      exact List.mem_append.mpr (Or.inl hw)))
  have hu1qa : u1 ∈ (q a).support := hA₂sub _ A₂.end_mem_support
  have hB₁sub : ∀ w ∈ B₁.support, w ∈ (q a).support := by
    intro w hw
    rw [hsupp_a]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hw))
  have hy₂qc : y₂ ∈ (q c).support := by
    rw [hsupp_c]
    exact List.mem_append.mpr (Or.inl C₁.end_mem_support)
  have hz₂qc : z₂ ∈ (q c).support := by
    rw [hsupp_c]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _
      (by rw [hsuppD₁]; exact List.mem_cons_self ..)))
  have hC₁sub : ∀ w ∈ C₁.support, w ∈ (q c).support := by
    intro w hw
    rw [hsupp_c]
    exact List.mem_append.mpr (Or.inl hw)
  have hD₂sub : ∀ w ∈ D₂.support, w ∈ (q c).support := by
    intro w hw
    rw [hsupp_c]
    refine List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ?_))
    rw [hsuppD₁]
    exact List.mem_cons_of_mem _ hw
  have hv2qc : v2 ∈ (q c).support := hD₂sub _ D₂.start_mem_support
  -- fine disjointness inside the two carrier paths
  have hnodup_a := (hqp a).support_nodup
  rw [hsupp_a, hsuppA₁, List.nodup_append, List.nodup_append, List.nodup_cons,
    List.nodup_cons] at hnodup_a
  have hnodup_c := (hqp c).support_nodup
  rw [hsupp_c, hsuppD₁, List.nodup_append, List.nodup_cons, List.nodup_cons] at hnodup_c
  have hsn_nA₂ : (s (Fin.last m)).2 ∉ A₂.support := by
    intro hmem
    exact hnodup_a.2.2 _ (List.mem_append.mpr (Or.inl hmem)) _ (List.mem_cons_self ..) rfl
  have hsn_nB₁ : (s (Fin.last m)).2 ∉ B₁.support := hnodup_a.2.1.1
  have hy₁ne_sn : y₁ ≠ (s (Fin.last m)).2 := by
    intro he
    exact hnodup_a.2.2 _ (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) _
      (List.mem_cons_self ..) he
  have hy₁nB₁ : y₁ ∉ B₁.support := by
    intro hmem
    exact hnodup_a.2.2 _ (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))) _
      (List.mem_cons_of_mem _ hmem) rfl
  have hA₂B₁ : ∀ w ∈ A₂.support, w ∉ B₁.support := by
    intro w hw hmem
    exact hnodup_a.2.2 _ (List.mem_append.mpr (Or.inl hw)) _
      (List.mem_cons_of_mem _ hmem) rfl
  have htn_nC₁ : (t (Fin.last m)).2 ∉ C₁.support := by
    intro hmem
    exact hnodup_c.2.2 _ hmem _ (List.mem_cons_self ..) rfl
  have htn_ne_z₂ : (t (Fin.last m)).2 ≠ z₂ := by
    intro he
    exact hnodup_c.2.1.1 (he ▸ List.mem_cons_self ..)
  have htn_nD₂ : (t (Fin.last m)).2 ∉ D₂.support := by
    intro hmem
    exact hnodup_c.2.1.1 (List.mem_cons_of_mem _ hmem)
  have hz₂nC₁ : z₂ ∉ C₁.support := by
    intro hmem
    exact hnodup_c.2.2 _ hmem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl
  have hC₁D₂ : ∀ w ∈ C₁.support, w ∉ D₂.support := by
    intro w hw hmem
    exact hnodup_c.2.2 _ hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)) rfl
  -- the 2-cover of copy j2
  have hd2 : OppositeDemand (fun w => col (j2, w))
      (![M j0 j2 z₁, M j0 j2 v2]) (![M j0 j2 u1, M j0 j2 y₂]) := by
    have hd2scol : ∀ i : Fin 2, col (j2, (![M j0 j2 z₁, M j0 j2 v2]) i) = b := by
      intro i
      by_cases hi : i = 0
      · subst hi
        simp only [Matrix.cons_val_zero]
        rw [hstar2, hcol_z₁, Bool.not_not]
      · rw [hfin2 i hi]
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [hstar2, hcol_v2, Bool.not_not]
    have hd2tcol : ∀ i : Fin 2, col (j2, (![M j0 j2 u1, M j0 j2 y₂]) i) = !b := by
      intro i
      by_cases hi : i = 0
      · subst hi
        simp only [Matrix.cons_val_zero]
        rw [hstar2, hcol_u1]
      · rw [hfin2 i hi]
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [hstar2, hcol_y₂]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      show col (j2, _) ≠ col (j2, _)
      rw [hd2scol i, hd2tcol i]
      cases b <;> simp
    · intro i k he
      by_cases hi : i = 0 <;> by_cases hk : k = 0
      · rw [hi, hk]
      · exfalso
        rw [hi, hfin2 k hk] at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at he
        exact hqdis a c hac z₁ ⟨hz₁qa, ((M j0 j2).injective he) ▸ hv2qc⟩
      · exfalso
        rw [hk, hfin2 i hi] at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at he
        exact hqdis a c hac z₁ ⟨hz₁qa, ((M j0 j2).injective he.symm) ▸ hv2qc⟩
      · rw [hfin2 i hi, hfin2 k hk]
    · intro i k he
      by_cases hi : i = 0 <;> by_cases hk : k = 0
      · rw [hi, hk]
      · exfalso
        rw [hi, hfin2 k hk] at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at he
        exact hqdis a c hac u1 ⟨hu1qa, ((M j0 j2).injective he) ▸ hy₂qc⟩
      · exfalso
        rw [hk, hfin2 i hi] at he
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at he
        exact hqdis a c hac u1 ⟨hu1qa, ((M j0 j2).injective he.symm) ▸ hy₂qc⟩
      · rw [hfin2 i hi, hfin2 k hk]
    · intro i k he
      have h1 := hd2scol i
      rw [he, hd2tcol k] at h1
      cases b <;> simp_all
  obtain ⟨Q2, hQ2p, hQ2cov, hQ2dis⟩ :=
    hcovlev j2 _ (by omega) (by omega) _ _ hd2
  -- explicit legs of the j2-cover
  have hleg0 : ∃ L : (Gs j2).Walk (M j0 j2 u1) (M j0 j2 z₁), L.IsPath ∧
      ∀ w, w ∈ L.support ↔ w ∈ (Q2 0).support := by
    refine ⟨((Q2 0).copy (by simp) (by simp)).reverse, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.reverse
      rw [SimpleGraph.Walk.isPath_copy]
      exact hQ2p 0
    · intro w
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_copy]
  obtain ⟨L0, hL0p, hL0mem⟩ := hleg0
  have hleg1 : ∃ L : (Gs j2).Walk (M j0 j2 y₂) (M j0 j2 v2), L.IsPath ∧
      ∀ w, w ∈ L.support ↔ w ∈ (Q2 1).support := by
    refine ⟨((Q2 1).copy (by simp) (by simp)).reverse, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.reverse
      rw [SimpleGraph.Walk.isPath_copy]
      exact hQ2p 1
    · intro w
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_copy]
  obtain ⟨L1, hL1p, hL1mem⟩ := hleg1
  -- the j3 Hamilton bridge
  have hcolham : col (j3, M j0 j3 y₁) ≠ col (j3, M j0 j3 z₂) := by
    rw [hstar3, hstar3, hcol_y₁, hcol_z₂]
    cases b <;> simp
  obtain ⟨hw3, hham3⟩ := hlace j3 _ _ hcolham
  -- the terminal edges of the extra pair
  have he1 : ∃ e : (Gs j0).Walk (s (Fin.last m)).2 y₁, e.IsPath ∧
      ∀ w, w ∈ e.support ↔ (w = (s (Fin.last m)).2 ∨ w = y₁) := by
    refine ⟨SimpleGraph.Walk.cons hyadj₁.symm SimpleGraph.Walk.nil, dpc_edge_path _, ?_⟩
    intro w
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  obtain ⟨e1, he1p, he1mem⟩ := he1
  have he2 : ∃ e : (Gs j0).Walk z₂ (t (Fin.last m)).2, e.IsPath ∧
      ∀ w, w ∈ e.support ↔ (w = z₂ ∨ w = (t (Fin.last m)).2) := by
    refine ⟨SimpleGraph.Walk.cons hzadj₂.symm SimpleGraph.Walk.nil, dpc_edge_path _, ?_⟩
    intro w
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  obtain ⟨e2, he2p, he2mem⟩ := he2
  -- ownership helpers
  have he1sub : ∀ w, w ∈ e1.support → w ∈ (q a).support := by
    intro w hw
    rcases (he1mem w).mp hw with rfl | rfl
    · exact hsn
    · exact hy₁qa
  have he2sub : ∀ w, w ∈ e2.support → w ∈ (q c).support := by
    intro w hw
    rcases (he2mem w).mp hw with rfl | rfl
    · exact hz₂qc
    · exact htn
  have howner_a : ∀ w, (w ∈ A₂.support ∨ w ∈ B₁.support) → w ∈ (q a).support := by
    intro w hw
    rcases hw with hw | hw
    · exact hA₂sub w hw
    · exact hB₁sub w hw
  have howner_c : ∀ w, (w ∈ C₁.support ∨ w ∈ D₂.support) → w ∈ (q c).support := by
    intro w hw
    rcases hw with hw | hw
    · exact hC₁sub w hw
    · exact hD₂sub w hw
  have hqac : ∀ w : W, w ∈ (q a).support → w ∈ (q c).support → False :=
    fun w h1 h2 => hqdis a c hac w ⟨h1, h2⟩
  -- pair a's detoured path
  have hPa : ∃ R : (weldGraph ell Gs M).Walk (s a.castSucc) (j0, (t a.castSucc).2),
      R.IsPath ∧ R.support = A₂.support.map (fun w => (j0, w))
        ++ L0.support.map (fun w => (j2, w)) ++ B₁.support.map (fun w => (j0, w)) := by
    obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc
      ((A₂.map (weldLift Gs M j0)).copy (Prod.ext (hS a.castSucc).symm rfl) rfl) L0
      (by
        rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA₂)
      hL0p (weld_cross_adj hj02 u1)
      (by
        intro w' _ hmem
        rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair] at hmem
        exact hj02 hmem.1.symm)
    obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ B₁ hR₁p hB₁
      ((weld_cross_adj hj02 z₁).symm)
      (by
        intro w' hw' hmem
        rw [hR₁s, List.mem_append, SimpleGraph.Walk.support_copy, weldLift_support,
          mem_map_pair, mem_map_pair] at hmem
        rcases hmem with ⟨-, hmem⟩ | ⟨h1, -⟩
        · exact hA₂B₁ _ hmem hw'
        · exact hj02 h1)
    refine ⟨R₂, hR₂p, ?_⟩
    rw [hR₂s, hR₁s, SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨Pa, hPap, hPas⟩ := hPa
  -- pair c's detoured path
  have hPc : ∃ R : (weldGraph ell Gs M).Walk (s c.castSucc) (j0, (t c.castSucc).2),
      R.IsPath ∧ R.support = C₁.support.map (fun w => (j0, w))
        ++ L1.support.map (fun w => (j2, w)) ++ D₂.support.map (fun w => (j0, w)) := by
    obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc
      ((C₁.map (weldLift Gs M j0)).copy (Prod.ext (hS c.castSucc).symm rfl) rfl) L1
      (by
        rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hC₁)
      hL1p (weld_cross_adj hj02 y₂)
      (by
        intro w' _ hmem
        rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair] at hmem
        exact hj02 hmem.1.symm)
    obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ D₂ hR₁p hD₂
      ((weld_cross_adj hj02 v2).symm)
      (by
        intro w' hw' hmem
        rw [hR₁s, List.mem_append, SimpleGraph.Walk.support_copy, weldLift_support,
          mem_map_pair, mem_map_pair] at hmem
        rcases hmem with ⟨-, hmem⟩ | ⟨h1, -⟩
        · exact hC₁D₂ _ hmem hw'
        · exact hj02 h1)
    refine ⟨R₂, hR₂p, ?_⟩
    rw [hR₂s, hR₁s, SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨Pc, hPcp, hPcs⟩ := hPc
  -- the extra pair's path through the j3 bridge
  have hPn : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j0, (t (Fin.last m)).2),
      R.IsPath ∧ R.support = e1.support.map (fun w => (j0, w))
        ++ hw3.support.map (fun w => (j3, w)) ++ e2.support.map (fun w => (j0, w)) := by
    obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc
      ((e1.map (weldLift Gs M j0)).copy (Prod.ext (hS (Fin.last m)).symm rfl) rfl) hw3
      (by
        rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) he1p)
      hham3.isPath (weld_cross_adj hj03 y₁)
      (by
        intro w' _ hmem
        rw [SimpleGraph.Walk.support_copy, weldLift_support, mem_map_pair] at hmem
        exact hj03 hmem.1.symm)
    obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ e2 hR₁p he2p
      ((weld_cross_adj hj03 z₂).symm)
      (by
        intro w' hw' hmem
        rw [hR₁s, List.mem_append, SimpleGraph.Walk.support_copy, weldLift_support,
          mem_map_pair, mem_map_pair] at hmem
        rcases hmem with ⟨-, hmem⟩ | ⟨h1, -⟩
        · exact hqac w' (he1sub w' hmem) (he2sub w' hw')
        · exact hj03 h1)
    refine ⟨R₂, hR₂p, ?_⟩
    rw [hR₂s, hR₁s, SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨Pn, hPnp, hPns⟩ := hPn
  -- the global family with a four-arm support characterization
  have hpaths : ∀ k : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s k) (t k), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        (if k = Fin.last m then
          (x.1 = j0 ∧ (x.2 ∈ e1.support ∨ x.2 ∈ e2.support)) ∨
            (x.1 = j3 ∧ x.2 ∈ hw3.support)
         else if k = a.castSucc then
          (x.1 = j0 ∧ (x.2 ∈ A₂.support ∨ x.2 ∈ B₁.support)) ∨
            (x.1 = j2 ∧ x.2 ∈ L0.support)
         else if k = c.castSucc then
          (x.1 = j0 ∧ (x.2 ∈ C₁.support ∨ x.2 ∈ D₂.support)) ∨
            (x.1 = j2 ∧ x.2 ∈ L1.support)
         else x.1 = j0 ∧ ∃ i : Fin m, k = i.castSucc ∧ x.2 ∈ (q i).support) := by
    intro k
    by_cases hk1 : k = Fin.last m
    · subst hk1
      refine ⟨Pn.copy rfl (Prod.ext (hT _).symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hPnp
      · intro x
        rw [if_pos rfl, SimpleGraph.Walk.support_copy, hPns]
        rw [List.mem_append, List.mem_append, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, Or.inl h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inl ⟨h1, Or.inr h2⟩
        · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inr ⟨h1, h2⟩
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · by_cases hk2 : k = a.castSucc
      · subst hk2
        refine ⟨Pa.copy rfl (Prod.ext (hT _).symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hPap
        · intro x
          rw [if_neg hk1, if_pos rfl, SimpleGraph.Walk.support_copy, hPas]
          rw [List.mem_append, List.mem_append, mem_map_pair, mem_map_pair, mem_map_pair]
          constructor
          · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, Or.inl h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl ⟨h1, Or.inr h2⟩
          · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
            · exact Or.inl (Or.inl ⟨h1, h2⟩)
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · by_cases hk3 : k = c.castSucc
        · subst hk3
          refine ⟨Pc.copy rfl (Prod.ext (hT _).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hPcp
          · intro x
            rw [if_neg hk1, if_neg hk2, if_pos rfl, SimpleGraph.Walk.support_copy, hPcs]
            rw [List.mem_append, List.mem_append, mem_map_pair, mem_map_pair, mem_map_pair]
            constructor
            · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
              · exact Or.inl ⟨h1, Or.inl h2⟩
              · exact Or.inr ⟨h1, h2⟩
              · exact Or.inl ⟨h1, Or.inr h2⟩
            · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
              · exact Or.inl (Or.inl ⟨h1, h2⟩)
              · exact Or.inr ⟨h1, h2⟩
              · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · obtain ⟨i, hik⟩ := Fin.eq_castSucc_of_ne_last hk1
          subst hik
          have hia : i ≠ a := fun h => hk2 (by rw [h])
          have hic : i ≠ c := fun h => hk3 (by rw [h])
          refine ⟨((q i).map (weldLift Gs M j0)).copy
            (Prod.ext (hS _).symm rfl) (Prod.ext (hT _).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) (hqp i)
          · intro x
            rw [if_neg hk1, if_neg hk2, if_neg hk3, SimpleGraph.Walk.support_copy,
              weldLift_support, mem_map_pair]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨h1, i, rfl, h2⟩
            · rintro ⟨h1, i', hi', h2⟩
              have hii : i' = i := Fin.castSucc_injective m hi'.symm
              subst hii
              exact ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  -- normalized membership
  have hnorm : ∀ (k : Fin (m + 1)) (x : Fin ell × W), x ∈ (P k).support →
      (k = Fin.last m ∧ ((x.1 = j0 ∧ (x.2 ∈ e1.support ∨ x.2 ∈ e2.support)) ∨
        (x.1 = j3 ∧ x.2 ∈ hw3.support))) ∨
      (k = a.castSucc ∧ ((x.1 = j0 ∧ (x.2 ∈ A₂.support ∨ x.2 ∈ B₁.support)) ∨
        (x.1 = j2 ∧ x.2 ∈ L0.support))) ∨
      (k = c.castSucc ∧ ((x.1 = j0 ∧ (x.2 ∈ C₁.support ∨ x.2 ∈ D₂.support)) ∨
        (x.1 = j2 ∧ x.2 ∈ L1.support))) ∨
      (k ≠ Fin.last m ∧ k ≠ a.castSucc ∧ k ≠ c.castSucc ∧ x.1 = j0 ∧
        ∃ i : Fin m, k = i.castSucc ∧ x.2 ∈ (q i).support) := by
    intro k x hx
    have h := (hPchar k x).mp hx
    by_cases hk1 : k = Fin.last m
    · rw [if_pos hk1] at h
      exact Or.inl ⟨hk1, h⟩
    · rw [if_neg hk1] at h
      by_cases hk2 : k = a.castSucc
      · rw [if_pos hk2] at h
        exact Or.inr (Or.inl ⟨hk2, h⟩)
      · rw [if_neg hk2] at h
        by_cases hk3 : k = c.castSucc
        · rw [if_pos hk3] at h
          exact Or.inr (Or.inr (Or.inl ⟨hk3, h⟩))
        · rw [if_neg hk3] at h
          exact Or.inr (Or.inr (Or.inr ⟨hk1, hk2, hk3, h⟩))
  -- copy-tag facts
  have htagf : ∀ k x, x ∈ (P k).support → x.1 = j0 ∨ x.1 = j2 ∨ x.1 = j3 := by
    intro k x hx
    rcases hnorm k x hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
        ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, -, -, h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
  have hmem2 : ∀ k x, x ∈ (P k).support → x.1 = j2 →
      (k = a.castSucc ∧ x.2 ∈ L0.support) ∨ (k = c.castSucc ∧ x.2 ∈ L1.support) := by
    intro k x hx h2
    rcases hnorm k x hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨hk, ⟨h1, -⟩ | ⟨-, hm⟩⟩ |
        ⟨hk, ⟨h1, -⟩ | ⟨-, hm⟩⟩ | ⟨-, -, -, h1, -⟩
    · exact absurd (h1.symm.trans h2) hj02
    · exact absurd (h2.symm.trans h1) hj23
    · exact absurd (h1.symm.trans h2) hj02
    · exact Or.inl ⟨hk, hm⟩
    · exact absurd (h1.symm.trans h2) hj02
    · exact Or.inr ⟨hk, hm⟩
    · exact absurd (h1.symm.trans h2) hj02
  have hmem3 : ∀ k x, x ∈ (P k).support → x.1 = j3 → k = Fin.last m := by
    intro k x hx h3
    rcases hnorm k x hx with ⟨hk, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
        ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, -, -, h1, -⟩
    · exact absurd (h1.symm.trans h3) hj03
    · exact hk
    · exact absurd (h1.symm.trans h3) hj03
    · exact absurd ((h1.symm.trans h3).symm.trans rfl).symm (fun hh => hj23 hh)
    · exact absurd (h1.symm.trans h3) hj03
    · exact absurd (h1.symm.trans h3) (fun hh => hj23 hh)
    · exact absurd (h1.symm.trans h3) hj03
  have hmem0 : ∀ k x, x ∈ (P k).support → x.1 = j0 →
      (k = Fin.last m ∧ (x.2 ∈ e1.support ∨ x.2 ∈ e2.support)) ∨
      (k = a.castSucc ∧ (x.2 ∈ A₂.support ∨ x.2 ∈ B₁.support)) ∨
      (k = c.castSucc ∧ (x.2 ∈ C₁.support ∨ x.2 ∈ D₂.support)) ∨
      (k ≠ Fin.last m ∧ k ≠ a.castSucc ∧ k ≠ c.castSucc ∧
        ∃ i : Fin m, k = i.castSucc ∧ x.2 ∈ (q i).support) := by
    intro k x hx h0
    rcases hnorm k x hx with ⟨hk, ⟨-, hm⟩ | ⟨h1, -⟩⟩ | ⟨hk, ⟨-, hm⟩ | ⟨h1, -⟩⟩ |
        ⟨hk, ⟨-, hm⟩ | ⟨h1, -⟩⟩ | ⟨hk1, hk2, hk3, -, hm⟩
    · exact Or.inl ⟨hk, hm⟩
    · exact absurd (h0.symm.trans h1) hj03
    · exact Or.inr (Or.inl ⟨hk, hm⟩)
    · exact absurd (h0.symm.trans h1) hj02
    · exact Or.inr (Or.inr (Or.inl ⟨hk, hm⟩))
    · exact absurd (h0.symm.trans h1) hj02
    · exact Or.inr (Or.inr (Or.inr ⟨hk1, hk2, hk3, hm⟩))
  -- close by Lemma 2.1
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0)
    ({j0, j2, j3} : Finset (Fin ell)) P hPp ?_ ?_ ?_
  · intro k x hx
    rcases htagf k x hx with h | h | h <;> simp [h]
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · obtain ⟨i, hi⟩ := hqcov xw
      by_cases hia : i = a
      · subst hia
        rw [hsupp_a, hsuppA₁] at hi
        rcases List.mem_append.mp hi with hi1 | hi2
        · rcases List.mem_append.mp hi1 with hiA | hiy
          · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
            rw [if_neg (Fin.castSucc_lt_last i).ne, if_pos rfl]
            exact Or.inl ⟨rfl, Or.inl hiA⟩
          · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
            rw [if_pos rfl]
            exact Or.inl ⟨rfl, Or.inl ((he1mem xw).mpr (Or.inr (List.mem_singleton.mp hiy)))⟩
        · rcases List.mem_cons.mp hi2 with hisn | hiB
          · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
            rw [if_pos rfl]
            exact Or.inl ⟨rfl, Or.inl ((he1mem xw).mpr (Or.inl hisn))⟩
          · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
            rw [if_neg (Fin.castSucc_lt_last i).ne, if_pos rfl]
            exact Or.inl ⟨rfl, Or.inr hiB⟩
      · by_cases hic : i = c
        · subst hic
          rw [hsupp_c, hsuppD₁] at hi
          rcases List.mem_append.mp hi with hiC | hi2
          · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
            rw [if_neg (Fin.castSucc_lt_last i).ne,
              if_neg (fun h => hia (Fin.castSucc_injective m h)), if_pos rfl]
            exact Or.inl ⟨rfl, Or.inl hiC⟩
          · rcases List.mem_cons.mp hi2 with hitn | hi3
            · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
              rw [if_pos rfl]
              exact Or.inl ⟨rfl, Or.inr ((he2mem xw).mpr (Or.inr hitn))⟩
            · rcases List.mem_cons.mp hi3 with hiz | hiD
              · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
                rw [if_pos rfl]
                exact Or.inl ⟨rfl, Or.inr ((he2mem xw).mpr (Or.inl hiz))⟩
              · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
                rw [if_neg (Fin.castSucc_lt_last i).ne,
                  if_neg (fun h => hia (Fin.castSucc_injective m h)), if_pos rfl]
                exact Or.inl ⟨rfl, Or.inr hiD⟩
        · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
          rw [if_neg (Fin.castSucc_lt_last i).ne,
            if_neg (fun h => hia (Fin.castSucc_injective m h)),
            if_neg (fun h => hic (Fin.castSucc_injective m h))]
          exact ⟨rfl, i, rfl, hi⟩
    · obtain ⟨i2, hm⟩ := hQ2cov xw
      by_cases hi2 : i2 = 0
      · subst hi2
        refine ⟨a.castSucc, (hPchar a.castSucc (xj, xw)).mpr ?_⟩
        rw [if_neg (Fin.castSucc_lt_last a).ne, if_pos rfl]
        exact Or.inr ⟨rfl, (hL0mem xw).mpr hm⟩
      · rw [hfin2 i2 hi2] at hm
        refine ⟨c.castSucc, (hPchar c.castSucc (xj, xw)).mpr ?_⟩
        rw [if_neg (Fin.castSucc_lt_last c).ne,
          if_neg (fun h => hac (Fin.castSucc_injective m h).symm), if_pos rfl]
        exact Or.inr ⟨rfl, (hL1mem xw).mpr hm⟩
    · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
      rw [if_pos rfl]
      exact Or.inr ⟨rfl, hham3.mem_support xw⟩
  · intro k k' hkk' x hx
    rcases htagf k x hx.1 with h0 | h2 | h3
    · rcases hmem0 k x hx.1 h0 with ⟨hk, hm⟩ | ⟨hk, hm⟩ | ⟨hk, hm⟩ |
          ⟨hk1, hk2, hk3, i, hki, hm⟩ <;>
        rcases hmem0 k' x hx.2 h0 with ⟨hk', hm'⟩ | ⟨hk', hm'⟩ | ⟨hk', hm'⟩ |
          ⟨hk1', hk2', hk3', i', hki', hm'⟩
      · exact hkk' (hk.trans hk'.symm)
      · rcases hm with hm | hm
        · rcases (he1mem _).mp hm with he | he <;> rcases hm' with hm' | hm'
          · exact hsn_nA₂ (he ▸ hm')
          · exact hsn_nB₁ (he ▸ hm')
          · exact hy₁nA₂ (he ▸ hm')
          · exact hy₁nB₁ (he ▸ hm')
        · exact hqac x.2 (howner_a x.2 hm') (he2sub x.2 hm)
      · rcases hm with hm | hm
        · exact hqac x.2 (he1sub x.2 hm) (howner_c x.2 hm')
        · rcases (he2mem _).mp hm with he | he <;> rcases hm' with hm' | hm'
          · exact hz₂nC₁ (he ▸ hm')
          · exact hz₂nD₂ (he ▸ hm')
          · exact htn_nC₁ (he ▸ hm')
          · exact htn_nD₂ (he ▸ hm')
      · rcases hm with hm | hm
        · exact hqdis a i' (fun h => hk2' (by rw [hki', ← h])) x.2 ⟨he1sub x.2 hm, hm'⟩
        · exact hqdis c i' (fun h => hk3' (by rw [hki', ← h])) x.2 ⟨he2sub x.2 hm, hm'⟩
      · rcases hm' with hm' | hm'
        · rcases (he1mem _).mp hm' with he | he <;> rcases hm with hm | hm
          · exact hsn_nA₂ (he ▸ hm)
          · exact hsn_nB₁ (he ▸ hm)
          · exact hy₁nA₂ (he ▸ hm)
          · exact hy₁nB₁ (he ▸ hm)
        · exact hqac x.2 (howner_a x.2 hm) (he2sub x.2 hm')
      · exact hkk' (hk.trans hk'.symm)
      · exact hqac x.2 (howner_a x.2 hm) (howner_c x.2 hm')
      · exact hqdis a i' (fun h => hk2' (by rw [hki', ← h])) x.2 ⟨howner_a x.2 hm, hm'⟩
      · rcases hm' with hm' | hm'
        · exact hqac x.2 (he1sub x.2 hm') (howner_c x.2 hm)
        · rcases (he2mem _).mp hm' with he | he <;> rcases hm with hm | hm
          · exact hz₂nC₁ (he ▸ hm)
          · exact hz₂nD₂ (he ▸ hm)
          · exact htn_nC₁ (he ▸ hm)
          · exact htn_nD₂ (he ▸ hm)
      · exact hqac x.2 (howner_a x.2 hm') (howner_c x.2 hm)
      · exact hkk' (hk.trans hk'.symm)
      · exact hqdis c i' (fun h => hk3' (by rw [hki', ← h])) x.2 ⟨howner_c x.2 hm, hm'⟩
      · rcases hm' with hm' | hm'
        · exact hqdis a i (fun h => hk2 (by rw [hki, ← h])) x.2 ⟨he1sub x.2 hm', hm⟩
        · exact hqdis c i (fun h => hk3 (by rw [hki, ← h])) x.2 ⟨he2sub x.2 hm', hm⟩
      · exact hqdis a i (fun h => hk2 (by rw [hki, ← h])) x.2 ⟨howner_a x.2 hm', hm⟩
      · exact hqdis c i (fun h => hk3 (by rw [hki, ← h])) x.2 ⟨howner_c x.2 hm', hm⟩
      · have hii' : i ≠ i' := by
          intro h
          exact hkk' (by rw [hki, hki', h])
        exact hqdis i i' hii' x.2 ⟨hm, hm'⟩
    · rcases hmem2 k x hx.1 h2 with ⟨hk, hm⟩ | ⟨hk, hm⟩ <;>
        rcases hmem2 k' x hx.2 h2 with ⟨hk', hm'⟩ | ⟨hk', hm'⟩
      · exact hkk' (hk.trans hk'.symm)
      · exact hQ2dis 0 1 (by decide) x.2 ⟨(hL0mem _).mp hm, (hL1mem _).mp hm'⟩
      · exact hQ2dis 0 1 (by decide) x.2 ⟨(hL0mem _).mp hm', (hL1mem _).mp hm⟩
      · exact hkk' (hk.trans hk'.symm)
    · exact hkk' ((hmem3 k x hx.1 h3).trans (hmem3 k' x hx.2 h3).symm)

set_option maxHeartbeats 1600000 in
/-- Case 2 at the small setting: all terminals in one copy. -/
theorem small_case2 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w)))
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ n - 1 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hn3 : 3 ≤ n) (hElln : n + 1 ≤ ell) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∀ i, (t i).1 = j0) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcovlev' : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ m →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m' :=
    fun j m' h1 h2 => hcovlev j m' h1 (by omega)
  have hm2 : 2 ≤ m := by omega
  have hEllm : m + 2 ≤ ell := by omega
  have hcolS : ∀ i, col (j0, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, col (j0, (t i).2) = !b := by
    intro i
    rw [← hT i]
    exact hmono.2.1 i
  have hd : OppositeDemand (fun w => col (j0, w))
      (fun i : Fin m => (s i.castSucc).2) (fun i : Fin m => (t i.castSucc).2) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      show col (j0, (s i.castSucc).2) ≠ col (j0, (t i.castSucc).2)
      rw [hcolS, hcolT]
      cases b <;> simp
    · intro i k he
      dsimp only at he
      have h := hmono.2.2.1 (Prod.ext ((hS i.castSucc).trans (hS k.castSucc).symm) he)
      exact Fin.castSucc_injective m h
    · intro i k he
      dsimp only at he
      have h := hmono.2.2.2 (Prod.ext ((hT i.castSucc).trans (hT k.castSucc).symm) he)
      exact Fin.castSucc_injective m h
    · intro i k he
      dsimp only at he
      have h1 := hcolS i.castSucc
      rw [he, hcolT k.castSucc] at h1
      cases b <;> simp_all
  obtain ⟨q, hqp, hqcov, hqdis⟩ := hcovlev' j0 _ (by omega) (by omega) _ _ hd
  obtain ⟨a, ha⟩ := hqcov (s (Fin.last m)).2
  obtain ⟨c, hc⟩ := hqcov (t (Fin.last m)).2
  by_cases hac : a = c
  · subst hac
    exact small_case2_one hproper hlace hcopy_eq hcovlev' hm2 hEllm hmono hS hT
      q hqp hqcov hqdis a ha hc
  · exact small_case2_two hproper hlace hcopy_eq hcovlev' hm2 hEllm hmono hS hT
      q hqp hqcov hqdis a c hac ha hc

end SmallCase2

section SmallCase3

variable {W : Type} [DecidableEq W] [Fintype W]

private theorem fin_exists_two_avoid3 {ell : ℕ} (h : 4 ≤ ell) (a b : Fin ell) :
    ∃ c d : Fin ell, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
  have hcard : 1 < (Finset.univ \ ({a, b} : Finset (Fin ell))).card := by
    have h2 : ({a, b} : Finset (Fin ell)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hc hd
  push_neg at hc hd
  exact ⟨c, d, hc.2.1, hc.2.2, hd.2.1, hd.2.2, hcd⟩

/-- `m` pairwise-distinct vertices of a prescribed color in copy `j` (room: `m ≤ 2n − 1`). -/

private theorem small_injective_colored {ell : ℕ} {col : Fin ell × W → Bool}
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (j : Fin ell) (c : Bool) (m : ℕ)
    (hm : m ≤ 3) :
    ∃ v : Fin m → W, Function.Injective v ∧ ∀ i, col (j, v i) = c := by
  classical
  have hcard : m ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card :=
    le_trans hm (hclass j c)
  obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨fun i => (u.equivFin.symm (finCongr hucard.symm i)).1, ?_, ?_⟩
  · intro i i' h
    have h2 := u.equivFin.symm.injective (Subtype.ext h)
    exact (finCongr hucard.symm).injective h2
  · intro i
    have h2 := husub (u.equivFin.symm (finCongr hucard.symm i)).2
    rw [Finset.mem_filter] at h2
    exact h2.2

private theorem bool_eq_of_ne_not3 {x c : Bool} (h : x ≠ !c) : x = c := by
  cases x <;> cases c <;> simp_all

private theorem bool_eq_not_of_ne3 {x c : Bool} (h : x ≠ c) : x = !c := by
  cases x <;> cases c <;> simp_all

set_option maxHeartbeats 6400000 in
/-- **Case 3 of Coleman et al. 2025, Proposition 1.6**: all sources in copy `j1`, all
    targets in copy `j2 ≠ j1`. -/
theorem small_case3 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ n - 1 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hn3 : n = 3) (hElln : n + 1 ≤ ell) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2) (hS : ∀ i, (s i).1 = j1) (hT : ∀ i, (t i).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn : 3 ≤ n := by omega
  have hEll : n + 1 ≤ ell := hElln
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcolS : ∀ i, col (j1, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, col (j2, (t i).2) = !b := by
    intro i
    rw [← hT i]
    exact hmono.2.1 i
  -- `m` fresh `!b`-colored exits in copy `j1`
  obtain ⟨v, hvinj, hvcol⟩ := small_injective_colored hclass j1 (!b) m (by omega)
  -- the copy-`j1` demand: the first `m` sources against the exits
  have hd1 : OppositeDemand (fun w => col (j1, w))
      (fun i : Fin m => (s i.castSucc).2) v := by
    refine ⟨?_, ?_, hvinj, ?_⟩
    · intro i
      show col (j1, (s i.castSucc).2) ≠ col (j1, v i)
      rw [hcolS, hvcol]
      cases b <;> simp
    · intro i k he
      dsimp only at he
      have h := hmono.2.2.1 (Prod.ext ((hS i.castSucc).trans (hS k.castSucc).symm) he)
      exact Fin.castSucc_injective m h
    · intro i k he
      dsimp only at he
      have h1 := hcolS i.castSucc
      rw [he, hvcol k] at h1
      cases b <;> simp_all
  obtain ⟨q, hqp, hqcov, hqdis⟩ := hcovlev j1 _ (by omega) (by omega) _ _ hd1
  -- the `j1`-path carrying the last source, split there
  obtain ⟨a, ha⟩ := hqcov (s (Fin.last m)).2
  have hsna : (s (Fin.last m)).2 ≠ (s a.castSucc).2 := by
    intro h
    have h2 := hmono.2.2.1 (Prod.ext ((hS (Fin.last m)).trans (hS a.castSucc).symm) h)
    exact (Fin.castSucc_lt_last a).ne' h2
  have hsnv : (s (Fin.last m)).2 ≠ v a := by
    intro h
    have h1 := hcolS (Fin.last m)
    rw [h, hvcol a] at h1
    cases b <;> simp_all
  obtain ⟨y, z, A, B, hA, hB, hadj_y_sn, hadj_sn_z, hsuppA⟩ :=
    path_split_interior (q a) (hqp a) ha hsna hsnv
  have hndA := (hqp a).support_nodup
  rw [hsuppA] at hndA
  obtain ⟨hndA1, hndA2, hdisjA⟩ := List.nodup_append.mp hndA
  have hsn_notB : (s (Fin.last m)).2 ∉ B.support := (List.nodup_cons.mp hndA2).1
  have hsnBp : (SimpleGraph.Walk.cons hadj_sn_z B).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hB, hsn_notB⟩
  -- the freed exit `y` is `!b`-colored
  have hcoly : col (j1, y) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j1, y) (j1, (s (Fin.last m)).2) :=
      (weldLift Gs M j1).map_adj hadj_y_sn
    have h := hproper _ _ hadj
    have h2 := hcolS (Fin.last m)
    cases hcy : col (j1, y) <;> cases b <;> simp_all
  -- `y` differs from every chosen exit
  have hy_ne_v : ∀ i, y ≠ v i := by
    intro i h
    by_cases hia : i = a
    · subst hia
      have h1 : y ∈ A.support := SimpleGraph.Walk.end_mem_support A
      have h2 : y ∈ B.support := by
        rw [h]
        exact SimpleGraph.Walk.end_mem_support B
      exact hdisjA y h1 y (List.mem_cons_of_mem _ h2) rfl
    · have h1 : y ∈ (q a).support := by
        rw [hsuppA]
        exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support A)
      have h2 : y ∈ (q i).support := by
        rw [h]
        exact SimpleGraph.Walk.end_mem_support (q i)
      exact hqdis i a hia y ⟨h2, h1⟩
  -- the matching partners of the exits, demanded against the first `m` targets
  obtain ⟨w, hwval⟩ : ∃ w : Fin m → W, ∀ i, w i = M j1 j2 (if i = a then y else v i) :=
    ⟨_, fun _ => rfl⟩
  have hwcol : ∀ i, col (j2, w i) = b := by
    intro i
    have hcolex : col (j1, if i = a then y else v i) = !b := by
      split
      · exact hcoly
      · exact hvcol i
    have hadj : (weldGraph ell Gs M).Adj (j1, if i = a then y else v i) (j2, w i) := by
      rw [hwval]
      exact weld_cross_adj hj12 _
    have h := hproper _ _ hadj
    rw [hcolex] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  have hexinj : Function.Injective fun i => (if i = a then y else v i) := by
    intro i k h
    dsimp only at h
    by_cases hia : i = a <;> by_cases hka : k = a
    · rw [hia, hka]
    · rw [if_pos hia, if_neg hka] at h
      exact absurd h (hy_ne_v k)
    · rw [if_neg hia, if_pos hka] at h
      exact absurd h.symm (hy_ne_v i)
    · rw [if_neg hia, if_neg hka] at h
      exact hvinj h
  have hwinj : Function.Injective w := by
    intro i k h
    rw [hwval, hwval] at h
    exact hexinj ((M j1 j2).injective h)
  have hd2 : OppositeDemand (fun w' => col (j2, w')) w (fun i : Fin m => (t i.castSucc).2) := by
    refine ⟨?_, hwinj, ?_, ?_⟩
    · intro i
      show col (j2, w i) ≠ col (j2, (t i.castSucc).2)
      rw [hwcol, hcolT]
      cases b <;> simp
    · intro i k he
      dsimp only at he
      have h := hmono.2.2.2 (Prod.ext ((hT i.castSucc).trans (hT k.castSucc).symm) he)
      exact Fin.castSucc_injective m h
    · intro i k he
      dsimp only at he
      have h1 := hwcol i
      rw [he, hcolT k.castSucc] at h1
      cases b <;> simp at h1
  obtain ⟨qh, hqhp, hqhcov, hqhdis⟩ := hcovlev j2 _ (by omega) (by omega) _ _ hd2
  -- the `j2`-path carrying the last target, split there
  obtain ⟨k, hkmem⟩ := hqhcov (t (Fin.last m)).2
  have htnw : (t (Fin.last m)).2 ≠ w k := by
    intro h
    have h1 := hcolT (Fin.last m)
    rw [h, hwcol k] at h1
    cases b <;> simp at h1
  have htnt : (t (Fin.last m)).2 ≠ (t k.castSucc).2 := by
    intro h
    have h2 := hmono.2.2.2 (Prod.ext ((hT (Fin.last m)).trans (hT k.castSucc).symm) h)
    exact (Fin.castSucc_lt_last k).ne' h2
  obtain ⟨u0, un, C, D, hC, hD, hadj_u0_tn, hadj_tn_un, hsuppC⟩ :=
    path_split_interior (qh k) (hqhp k) hkmem htnw htnt
  have hndC := (hqhp k).support_nodup
  rw [hsuppC] at hndC
  obtain ⟨hndC1, hndC2, hdisjC⟩ := List.nodup_append.mp hndC
  have htn_notD : (t (Fin.last m)).2 ∉ D.support := (List.nodup_cons.mp hndC2).1
  -- the colors around the last target
  have hcolu0 : col (j2, u0) = b := by
    have hadj : (weldGraph ell Gs M).Adj (j2, u0) (j2, (t (Fin.last m)).2) :=
      (weldLift Gs M j2).map_adj hadj_u0_tn
    have h := hproper _ _ hadj
    have h2 := hcolT (Fin.last m)
    rw [h2] at h
    exact bool_eq_of_ne_not3 h
  have hcolun : col (j2, un) = b := by
    have hadj : (weldGraph ell Gs M).Adj (j2, (t (Fin.last m)).2) (j2, un) :=
      (weldLift Gs M j2).map_adj hadj_tn_un
    have h := hproper _ _ hadj
    have h2 := hcolT (Fin.last m)
    rw [h2] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- peel the freed path-neighbor `un` off the tail
  have hunt : un ≠ (t k.castSucc).2 := by
    intro h
    have h1 := hcolun
    rw [h, hcolT k.castSucc] at h1
    cases b <;> simp at h1
  obtain ⟨v0, D', hD', hadj_un_v0, hsuppD, hun_notD'⟩ := path_peel_head D hD hunt
  have hcolv0 : col (j2, v0) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j2, un) (j2, v0) :=
      (weldLift Gs M j2).map_adj hadj_un_v0
    have h := hproper _ _ hadj
    rw [hcolun] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  -- two fresh bridge copies
  obtain ⟨j3, j4, hj31, hj32, hj41, hj42, hj34⟩ := fin_exists_two_avoid3 (by omega) j1 j2
  -- the `j3` bridge rejoins the two cut ends of the target-carrier
  have hbr3 : col (j3, M j2 j3 u0) ≠ col (j3, M j2 j3 v0) := by
    have h1 := hproper _ _ (weld_cross_adj (M := M) hj32.symm u0)
    have h2 := hproper _ _ (weld_cross_adj (M := M) hj32.symm v0)
    rw [hcolu0] at h1
    rw [hcolv0] at h2
    rw [bool_eq_not_of_ne3 (Ne.symm h1), bool_eq_of_ne_not3 (Ne.symm h2)]
    cases b <;> simp
  obtain ⟨h3, hham3⟩ := hlace j3 _ _ hbr3
  -- the `j4` bridge carries the last pair from `j1` to the freed neighbor `un`
  have hbr4 : col (j4, M j1 j4 (v a)) ≠ col (j4, M j2 j4 un) := by
    have h1 := hproper _ _ (weld_cross_adj (M := M) hj41.symm (v a))
    have h2 := hproper _ _ (weld_cross_adj (M := M) hj42.symm un)
    rw [hvcol a] at h1
    rw [hcolun] at h2
    rw [bool_eq_of_ne_not3 (Ne.symm h1), bool_eq_not_of_ne3 (Ne.symm h2)]
    cases b <;> simp
  obtain ⟨h4, hham4⟩ := hlace j4 _ _ hbr4
  -- the per-pair weld paths, with a support characterization
  have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        (if r = Fin.last m then
          (x.1 = j1 ∧ x.2 ∈ (SimpleGraph.Walk.cons hadj_sn_z B).support) ∨
            (x.1 = j4 ∧ x.2 ∈ h4.support) ∨
            (x.1 = j2 ∧ (x.2 = un ∨ x.2 = (t (Fin.last m)).2))
         else ∃ i : Fin m, r = i.castSucc ∧
          ((x.1 = j1 ∧ x.2 ∈ (if i = a then A.support else (q i).support)) ∨
           (x.1 = j2 ∧ (if i = k then x.2 ∈ C.support ∨ x.2 ∈ D'.support
                        else x.2 ∈ (qh i).support)) ∨
           (i = k ∧ x.1 = j3 ∧ x.2 ∈ h3.support))) := by
    intro r
    by_cases hr : r = Fin.last m
    · subst hr
      -- the last pair: `sn ⇝ v a` in `j1`, the `j4` Hamilton bridge, then `un, tn` in `j2`
      have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j1, v a), R.IsPath ∧
          R.support = (SimpleGraph.Walk.cons hadj_sn_z B).support.map (fun w' => (j1, w')) := by
        refine ⟨((SimpleGraph.Walk.cons hadj_sn_z B).map (weldLift Gs M j1)).copy
          (Prod.ext (hS (Fin.last m)).symm rfl) rfl, ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsnBp
        · rw [SimpleGraph.Walk.support_copy, weldLift_support]
      obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
      obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ h4 hR₀p hham4.isPath
        (weld_cross_adj hj41.symm (v a))
        (by
          intro w' _ hmem
          rw [hR₀s, mem_map_pair] at hmem
          exact hj41 hmem.1)
      have hW2p : (SimpleGraph.Walk.cons hadj_tn_un.symm SimpleGraph.Walk.nil).IsPath := by
        rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
        intro h
        have h1 := hcolun
        rw [h, hcolT (Fin.last m)] at h1
        cases b <;> simp at h1
      obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁
        (SimpleGraph.Walk.cons hadj_tn_un.symm SimpleGraph.Walk.nil) hR₁p hW2p
        ((weld_cross_adj hj42.symm un).symm)
        (by
          intro w' _ hmem
          rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
          rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hj12 h1.symm
          · exact hj42 h1.symm)
      refine ⟨R₂.copy rfl (Prod.ext (hT (Fin.last m)).symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR₂p
      · intro x
        rw [SimpleGraph.Walk.support_copy, if_pos rfl, hR₂s, List.mem_append, hR₁s,
          List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (Or.inl ⟨h1, h2⟩)
          · refine Or.inr (Or.inr ⟨h1, ?_⟩)
            simpa using h2
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · refine Or.inr ⟨h1, ?_⟩
            simpa using h2
    · -- a non-last pair
      obtain ⟨i, hri⟩ : ∃ i : Fin m, r = i.castSucc :=
        ⟨r.castPred hr, (Fin.castSucc_castPred r hr).symm⟩
      subst hri
      by_cases hik : i = k
      · -- the target-carrier pair: reroute around `tn` through the `j3` bridge
        subst hik
        by_cases hia : i = a
        · -- the source-carrier coincides: its `j1` segment is `A`
          subst hia
          have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s i.castSucc) (j1, y), R.IsPath ∧
              R.support = A.support.map (fun w' => (j1, w')) := by
            refine ⟨(A.map (weldLift Gs M j1)).copy
              (Prod.ext (hS i.castSucc).symm rfl) rfl, ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA
            · rw [SimpleGraph.Walk.support_copy, weldLift_support]
          obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
          have hadjC : (weldGraph ell Gs M).Adj (j1, y) (j2, w i) := by
            rw [hwval, if_pos rfl]
            exact weld_cross_adj hj12 y
          obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ C hR₀p hC hadjC
            (by
              intro w' _ hmem
              rw [hR₀s, mem_map_pair] at hmem
              exact hj12 hmem.1.symm)
          obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ h3 hR₁p hham3.isPath
            (weld_cross_adj hj32.symm u0)
            (by
              intro w' _ hmem
              rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
              rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
              · exact hj31 h1
              · exact hj32 h1)
          obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ D' hR₂p hD'
            ((weld_cross_adj hj32.symm v0).symm)
            (by
              intro w' hw' hmem
              rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                mem_map_pair, mem_map_pair, mem_map_pair] at hmem
              rcases hmem with (⟨h1, -⟩ | ⟨h1, h2⟩) | ⟨h1, -⟩
              · exact hj12 h1.symm
              · exact hdisjC w' h2 w' (List.mem_cons_of_mem _
                  (by rw [hsuppD]; exact List.mem_cons_of_mem _ hw')) rfl
              · exact hj32 h1.symm)
          refine ⟨R₃.copy rfl (Prod.ext (hT i.castSucc).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hR₃p
          · intro x
            rw [SimpleGraph.Walk.support_copy, if_neg hr]
            have hmem : x ∈ R₃.support ↔
                ((x.1 = j1 ∧ x.2 ∈ A.support) ∨
                 (x.1 = j2 ∧ (x.2 ∈ C.support ∨ x.2 ∈ D'.support)) ∨
                 (x.1 = j3 ∧ x.2 ∈ h3.support)) := by
              rw [hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair]
              constructor
              · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, h2⟩
                · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
                · exact Or.inr (Or.inr ⟨h1, h2⟩)
                · exact Or.inr (Or.inl ⟨h1, Or.inr h2⟩)
              · rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
                · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
                · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                · exact Or.inr ⟨h1, h2⟩
                · exact Or.inl (Or.inr ⟨h1, h2⟩)
            rw [hmem]
            constructor
            · intro hb
              refine ⟨i, rfl, ?_⟩
              rw [if_pos rfl, if_pos rfl]
              rcases hb with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨rfl, h⟩)
            · rintro ⟨i', heq, hb⟩
              obtain rfl := Fin.castSucc_injective m heq
              rw [if_pos rfl, if_pos rfl] at hb
              rcases hb with h | h | ⟨-, h⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
        · -- `i = k ≠ a`: the `j1` segment is the untouched `q i`
          have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s i.castSucc) (j1, v i), R.IsPath ∧
              R.support = (q i).support.map (fun w' => (j1, w')) := by
            refine ⟨((q i).map (weldLift Gs M j1)).copy
              (Prod.ext (hS i.castSucc).symm rfl) rfl, ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) (hqp i)
            · rw [SimpleGraph.Walk.support_copy, weldLift_support]
          obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
          have hadjC : (weldGraph ell Gs M).Adj (j1, v i) (j2, w i) := by
            rw [hwval, if_neg hia]
            exact weld_cross_adj hj12 (v i)
          obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ C hR₀p hC hadjC
            (by
              intro w' _ hmem
              rw [hR₀s, mem_map_pair] at hmem
              exact hj12 hmem.1.symm)
          obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ h3 hR₁p hham3.isPath
            (weld_cross_adj hj32.symm u0)
            (by
              intro w' _ hmem
              rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
              rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
              · exact hj31 h1
              · exact hj32 h1)
          obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ D' hR₂p hD'
            ((weld_cross_adj hj32.symm v0).symm)
            (by
              intro w' hw' hmem
              rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                mem_map_pair, mem_map_pair, mem_map_pair] at hmem
              rcases hmem with (⟨h1, -⟩ | ⟨h1, h2⟩) | ⟨h1, -⟩
              · exact hj12 h1.symm
              · exact hdisjC w' h2 w' (List.mem_cons_of_mem _
                  (by rw [hsuppD]; exact List.mem_cons_of_mem _ hw')) rfl
              · exact hj32 h1.symm)
          refine ⟨R₃.copy rfl (Prod.ext (hT i.castSucc).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hR₃p
          · intro x
            rw [SimpleGraph.Walk.support_copy, if_neg hr]
            have hmem : x ∈ R₃.support ↔
                ((x.1 = j1 ∧ x.2 ∈ (q i).support) ∨
                 (x.1 = j2 ∧ (x.2 ∈ C.support ∨ x.2 ∈ D'.support)) ∨
                 (x.1 = j3 ∧ x.2 ∈ h3.support)) := by
              rw [hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair]
              constructor
              · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, h2⟩
                · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
                · exact Or.inr (Or.inr ⟨h1, h2⟩)
                · exact Or.inr (Or.inl ⟨h1, Or.inr h2⟩)
              · rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
                · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
                · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                · exact Or.inr ⟨h1, h2⟩
                · exact Or.inl (Or.inr ⟨h1, h2⟩)
            rw [hmem]
            constructor
            · intro hb
              refine ⟨i, rfl, ?_⟩
              rw [if_neg hia, if_pos rfl]
              rcases hb with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨rfl, h⟩)
            · rintro ⟨i', heq, hb⟩
              obtain rfl := Fin.castSucc_injective m heq
              rw [if_neg hia, if_pos rfl] at hb
              rcases hb with h | h | ⟨-, h⟩
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
      · -- an ordinary pair: `j1` segment spliced to the untouched `qh i`
        by_cases hia : i = a
        · subst hia
          obtain ⟨R, hRp, hRs⟩ := weld_splice hj12 A (qh i) hA (hqhp i)
            (by rw [hwval, if_pos rfl])
          refine ⟨R.copy (Prod.ext (hS i.castSucc).symm rfl)
            (Prod.ext (hT i.castSucc).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hRp
          · intro x
            rw [SimpleGraph.Walk.support_copy, if_neg hr, hRs, List.mem_append,
              mem_map_pair, mem_map_pair]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨i, rfl, by rw [if_pos rfl]; exact Or.inl ⟨h1, h2⟩⟩
              · exact ⟨i, rfl, by rw [if_neg hik]; exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
            · rintro ⟨i', heq, hb⟩
              obtain rfl := Fin.castSucc_injective m heq
              rw [if_pos rfl, if_neg hik] at hb
              rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
              · exact Or.inl ⟨h1, h2⟩
              · exact Or.inr ⟨h1, h2⟩
              · exact absurd h1 hik
        · obtain ⟨R, hRp, hRs⟩ := weld_splice hj12 (q i) (qh i) (hqp i) (hqhp i)
            (by rw [hwval, if_neg hia])
          refine ⟨R.copy (Prod.ext (hS i.castSucc).symm rfl)
            (Prod.ext (hT i.castSucc).symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hRp
          · intro x
            rw [SimpleGraph.Walk.support_copy, if_neg hr, hRs, List.mem_append,
              mem_map_pair, mem_map_pair]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨i, rfl, by rw [if_neg hia]; exact Or.inl ⟨h1, h2⟩⟩
              · exact ⟨i, rfl, by rw [if_neg hik]; exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
            · rintro ⟨i', heq, hb⟩
              obtain rfl := Fin.castSucc_injective m heq
              rw [if_neg hia, if_neg hik] at hb
              rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
              · exact Or.inl ⟨h1, h2⟩
              · exact Or.inr ⟨h1, h2⟩
              · exact absurd h1 hik
  choose P hPp hPchar using hpaths
  -- membership helpers for the covering and disjointness arguments
  have hg1 : ∀ i : Fin m, ∀ x : W, x ∈ (if i = a then A.support else (q i).support) →
      x ∈ (q i).support := by
    intro i x hx
    by_cases hia : i = a
    · subst hia
      rw [if_pos rfl] at hx
      rw [hsuppA]
      exact List.mem_append_left _ hx
    · rwa [if_neg hia] at hx
  have hg2 : ∀ i : Fin m, ∀ x : W,
      (if i = k then x ∈ C.support ∨ x ∈ D'.support else x ∈ (qh i).support) →
      x ∈ (qh i).support := by
    intro i x hx
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl] at hx
      rw [hsuppC]
      rcases hx with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _
          (by rw [hsuppD]; exact List.mem_cons_of_mem _ h))
    · rwa [if_neg hik] at hx
  have hsnB_sub : ∀ x : W, x ∈ (SimpleGraph.Walk.cons hadj_sn_z B).support →
      x ∈ (q a).support := by
    intro x hx
    rw [SimpleGraph.Walk.support_cons] at hx
    rw [hsuppA]
    exact List.mem_append_right _ hx
  have hg1_snB : ∀ i : Fin m, ∀ x : W, x ∈ (if i = a then A.support else (q i).support) →
      x ∉ (SimpleGraph.Walk.cons hadj_sn_z B).support := by
    intro i x hx hx2
    by_cases hia : i = a
    · subst hia
      rw [if_pos rfl] at hx
      rw [SimpleGraph.Walk.support_cons] at hx2
      exact hdisjA x hx x hx2 rfl
    · rw [if_neg hia] at hx
      exact hqdis i a hia x ⟨hx, hsnB_sub x hx2⟩
  have hun_mem : un ∈ (qh k).support := by
    rw [hsuppC]
    exact List.mem_append_right _ (List.mem_cons_of_mem _
      (by rw [hsuppD]; exact List.mem_cons_self ..))
  have hg2_edge : ∀ i : Fin m, ∀ x : W,
      (if i = k then x ∈ C.support ∨ x ∈ D'.support else x ∈ (qh i).support) →
      x ≠ un ∧ x ≠ (t (Fin.last m)).2 := by
    intro i x hx
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl] at hx
      constructor
      · intro he
        rcases hx with h | h
        · exact hdisjC x h x (List.mem_cons_of_mem _
            (by rw [hsuppD, he]; exact List.mem_cons_self ..)) rfl
        · rw [he] at h
          exact hun_notD' h
      · intro he
        rcases hx with h | h
        · exact hdisjC x h x (by rw [he]; exact List.mem_cons_self ..) rfl
        · rw [he] at h
          exact htn_notD (by rw [hsuppD]; exact List.mem_cons_of_mem _ h)
    · rw [if_neg hik] at hx
      constructor
      · intro he
        exact hqhdis i k hik x ⟨hx, by rw [he]; exact hun_mem⟩
      · intro he
        exact hqhdis i k hik x ⟨hx, by rw [he]; exact hkmem⟩
  -- close by Lemma 2.1 over the untouched copies
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0)
    ({j1, j2, j3, j4} : Finset (Fin ell)) P hPp ?_ ?_ ?_
  · -- every path stays inside the four touched copies
    intro r x hx
    have h := (hPchar r x).mp hx
    by_cases hrr : r = Fin.last m
    · rw [if_pos hrr] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
    · rw [if_neg hrr] at h
      obtain ⟨i, -, h⟩ := h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ <;> simp [h1]
  · -- the four touched copies are jointly covered
    rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl | rfl
    · -- copy j1
      obtain ⟨i, hi⟩ := hqcov xw
      by_cases hia : i = a
      · subst hia
        rw [hsuppA] at hi
        rcases List.mem_append.mp hi with hmem | hmem
        · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
          rw [if_neg (Fin.castSucc_lt_last i).ne]
          exact ⟨i, rfl, Or.inl ⟨rfl, by rw [if_pos rfl]; exact hmem⟩⟩
        · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
          rw [if_pos rfl]
          exact Or.inl ⟨rfl, by rw [SimpleGraph.Walk.support_cons]; exact hmem⟩
      · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
        rw [if_neg (Fin.castSucc_lt_last i).ne]
        exact ⟨i, rfl, Or.inl ⟨rfl, by rw [if_neg hia]; exact hi⟩⟩
    · -- copy j2
      obtain ⟨i, hi⟩ := hqhcov xw
      by_cases hik : i = k
      · subst hik
        rw [hsuppC] at hi
        rcases List.mem_append.mp hi with hmem | hmem
        · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
          rw [if_neg (Fin.castSucc_lt_last i).ne]
          exact ⟨i, rfl, Or.inr (Or.inl ⟨rfl, by rw [if_pos rfl]; exact Or.inl hmem⟩)⟩
        · rcases List.mem_cons.mp hmem with hmem2 | hmem2
          · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
            rw [if_pos rfl]
            exact Or.inr (Or.inr ⟨rfl, Or.inr hmem2⟩)
          · rw [hsuppD] at hmem2
            rcases List.mem_cons.mp hmem2 with hmem3 | hmem3
            · refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
              rw [if_pos rfl]
              exact Or.inr (Or.inr ⟨rfl, Or.inl hmem3⟩)
            · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
              rw [if_neg (Fin.castSucc_lt_last i).ne]
              exact ⟨i, rfl, Or.inr (Or.inl ⟨rfl, by rw [if_pos rfl]; exact Or.inr hmem3⟩)⟩
      · refine ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr ?_⟩
        rw [if_neg (Fin.castSucc_lt_last i).ne]
        exact ⟨i, rfl, Or.inr (Or.inl ⟨rfl, by rw [if_neg hik]; exact hi⟩)⟩
    · -- copy j3: the bridge inside the target-carrier's path
      refine ⟨k.castSucc, (hPchar k.castSucc (xj, xw)).mpr ?_⟩
      rw [if_neg (Fin.castSucc_lt_last k).ne]
      exact ⟨k, rfl, Or.inr (Or.inr ⟨rfl, rfl, hham3.mem_support xw⟩)⟩
    · -- copy j4: the bridge inside the last pair's path
      refine ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr ?_⟩
      rw [if_pos rfl]
      exact Or.inr (Or.inl ⟨rfl, hham4.mem_support xw⟩)
  · -- pairwise disjointness
    intro r r' hrr' x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h := (hPchar r x).mp hx1
    have h' := (hPchar r' x).mp hx2
    by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
    · exact hrr' (hr.trans hr'.symm)
    · rw [if_pos hr] at h
      rw [if_neg hr'] at h'
      obtain ⟨i, -, h'⟩ := h'
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨hik', h1', h2'⟩
      · exact hg1_snB i x.2 h2' h2
      · exact hj12 (h1.symm.trans h1')
      · exact hj31 (h1'.symm.trans h1)
      · exact hj41 (h1.symm.trans h1')
      · exact hj42 (h1.symm.trans h1')
      · exact hj34 (h1'.symm.trans h1)
      · exact hj12 (h1'.symm.trans h1)
      · rcases h2 with he | he
        · exact (hg2_edge i x.2 h2').1 he
        · exact (hg2_edge i x.2 h2').2 he
      · exact hj32 (h1'.symm.trans h1)
    · rw [if_neg hr] at h
      rw [if_pos hr'] at h'
      obtain ⟨i, -, h⟩ := h
      rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;>
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hik1, h1, h2⟩
      · exact hg1_snB i x.2 h2 h2'
      · exact hj12 (h1'.symm.trans h1)
      · exact hj31 (h1.symm.trans h1')
      · exact hj41 (h1'.symm.trans h1)
      · exact hj42 (h1'.symm.trans h1)
      · exact hj34 (h1.symm.trans h1')
      · exact hj12 (h1.symm.trans h1')
      · rcases h2' with he | he
        · exact (hg2_edge i x.2 h2).1 he
        · exact (hg2_edge i x.2 h2).2 he
      · exact hj32 (h1.symm.trans h1')
    · rw [if_neg hr] at h
      rw [if_neg hr'] at h'
      obtain ⟨i, hri, h⟩ := h
      obtain ⟨i', hri', h'⟩ := h'
      have hii' : i ≠ i' := by
        intro hh
        exact hrr' (hri.trans (by rw [hh, ← hri']))
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hik1, h1, h2⟩ <;>
        rcases h' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨hik1', h1', h2'⟩
      · exact hqdis i i' hii' x.2 ⟨hg1 i x.2 h2, hg1 i' x.2 h2'⟩
      · exact hj12 (h1.symm.trans h1')
      · exact hj31 (h1'.symm.trans h1)
      · exact hj12 (h1'.symm.trans h1)
      · exact hqhdis i i' hii' x.2 ⟨hg2 i x.2 h2, hg2 i' x.2 h2'⟩
      · exact hj32 (h1'.symm.trans h1)
      · exact hj31 (h1.symm.trans h1')
      · exact hj32 (h1.symm.trans h1')
      · exact hii' (hik1.trans hik1'.symm)



end SmallCase3

section SmallCase4

variable {W : Type} [DecidableEq W] [Fintype W]

private theorem small_injective_colored_avoid {ell : ℕ} {col : Fin ell × W → Bool}
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (j : Fin ell) (c : Bool) (m : ℕ)
    (avoid : Finset W) (hm : m + avoid.card ≤ 3) :
    ∃ v : Fin m → W, Function.Injective v ∧ (∀ i, col (j, v i) = c) ∧ ∀ i, v i ∉ avoid := by
  classical
  have h1 := hclass j c
  have h2 : ((Finset.univ.filter (fun w => col (j, w) = c)) \ avoid).card
      = (Finset.univ.filter (fun w => col (j, w) = c)).card
        - (avoid ∩ (Finset.univ.filter (fun w => col (j, w) = c))).card :=
    Finset.card_sdiff ..
  have h3 : (avoid ∩ (Finset.univ.filter (fun w => col (j, w) = c))).card ≤ avoid.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hcard : m ≤ ((Finset.univ.filter (fun w => col (j, w) = c)) \ avoid).card := by
    omega
  obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨fun i => (u.equivFin.symm (finCongr hucard.symm i)).1, ?_, ?_, ?_⟩
  · intro i i' h
    have h4 := u.equivFin.symm.injective (Subtype.ext h)
    exact (finCongr hucard.symm).injective h4
  · intro i
    have h4 := husub (u.equivFin.symm (finCongr hucard.symm i)).2
    rw [Finset.mem_sdiff, Finset.mem_filter] at h4
    exact h4.1.2
  · intro i
    have h4 := husub (u.equivFin.symm (finCongr hucard.symm i)).2
    rw [Finset.mem_sdiff] at h4
    exact h4.2

private theorem small_copy_avoiding_targets {ell n : ℕ} {t : Fin n → Fin ell × W}
    (hEll : n + 1 ≤ ell) :
    ∃ jf : Fin ell, ∀ i, (t i).1 ≠ jf := by
  classical
  have hcard : (Finset.univ.image (fun i : Fin n => (t i).1)).card < ell := by
    have h1 : (Finset.univ.image (fun i : Fin n => (t i).1)).card ≤ n :=
      le_trans (Finset.card_image_le) (by simp)
    omega
  have hne : (Finset.univ \ Finset.univ.image (fun i : Fin n => (t i).1)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jf, hjf⟩ := hne
  rw [Finset.mem_sdiff] at hjf
  refine ⟨jf, fun i he => hjf.2 ?_⟩
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_univ i, he⟩

/-- Per-target-copy covers for Case 4: in a copy `j ≠ j0` touched by some target, an
    inner `w_j`-cover pairing the matching image of each pair's `j0`-exit with its target. -/
private theorem small_case4_family {ell : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ 2 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m') {b : Bool}
    {n : ℕ}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 2)
    (exit : Fin n → W) (hexcol : ∀ i, col (j0, exit i) = !b)
    (hexinj : ∀ i k, (t i).1 ≠ j0 → (t k).1 ≠ j0 → exit i = exit k → i = k)
    (j : Fin ell) (hj0 : j ≠ j0) (hjne : (weldWSet s t j).Nonempty) :
    ∃ Q : ∀ i ∈ weldWSet s t j, (Gs j).Walk (M j0 j (exit i)) ((t i).2),
      (∀ i (hi : i ∈ weldWSet s t j), (Q i hi).IsPath) ∧
      (∀ x : W, ∃ i, ∃ hi : i ∈ weldWSet s t j, x ∈ (Q i hi).support) ∧
      (∀ i (hi : i ∈ weldWSet s t j), ∀ k (hk : k ∈ weldWSet s t j), i ≠ k →
        ∀ x, ¬ (x ∈ (Q i hi).support ∧ x ∈ (Q k hk).support)) := by
  have htmem : ∀ i ∈ weldWSet s t j, (t i).1 = j := by
    intro i hi
    rcases mem_weldWSet.mp hi with h | h
    · exact absurd ((hS i).symm.trans h) hj0.symm
    · exact h
  have hcovA : IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w))
      (weldWSet s t j).card := by
    have hcardw := hw j hj0
    have hposw : 0 < (weldWSet s t j).card := Finset.card_pos.mpr hjne
    rcases (by omega : (weldWSet s t j).card = 1 ∨ (weldWSet s t j).card = 2) with h | h
    · rw [h]
      exact paired_one_opposite_iff_hamLaceable.mpr (hlace j)
    · rw [h]
      exact hcov2 j
  apply small_inner_family (b := b) j (weldWSet s t j) hjne hcovA
  · intro i _
    have hadj := weld_cross_adj (Gs := Gs) (M := M) hj0.symm (exit i)
    have h := hproper _ _ hadj
    rw [hexcol i] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  · intro i hi
    rw [← htmem i hi]
    exact hmono.2.1 i
  · intro i hi k hk hik he
    exact hik (hexinj i k (by rw [htmem i hi]; exact hj0) (by rw [htmem k hk]; exact hj0)
      ((M j0 j).injective he))
  · intro i hi k hk hik he
    exact hik (hmono.2.2.2 (Prod.ext ((htmem i hi).trans (htmem k hk).symm) he))

set_option maxHeartbeats 12800000 in
/-- **Case 4 core**: all sources in copy `j0`, the last pair's target elsewhere, every
    other copy meeting at most `n − 1` pairs. -/
private theorem small_case4_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
(hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ 2 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m') {b : Bool}
    (hm2 : m = 2) (hEllm : m + 2 ≤ ell)
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hlast : (t (Fin.last m)).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ m + 1 - 1) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn : 3 ≤ m + 1 := by omega
  have hEll : m + 1 + 1 ≤ ell := by omega
  have hcolS : ∀ i, col (j0, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, (t i).1 = j0 → col (j0, (t i).2) = !b := by
    intro i hi
    rw [← hi]
    exact hmono.2.1 i
  -- fresh `!b` exits for the out-pairs only, folded with the in-copy targets
  obtain ⟨v, hvcol, hvinj, hvt⟩ : ∃ v : Fin m → W,
      (∀ i, col (j0, v i) = !b) ∧ Function.Injective v ∧
      (∀ i, ¬ (t i.castSucc).1 = j0 → ∀ r : Fin (m + 1), (t r).1 = j0 →
        v i ≠ (t r).2) := by
    set OutS : Finset (Fin m) :=
      Finset.univ.filter (fun i : Fin m => ¬ (t i.castSucc).1 = j0) with hOutS
    have hInOut : OutS.card
        + (Finset.univ.filter (fun i : Fin m => (t i.castSucc).1 = j0)).card = m := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (p := fun i => ¬ (t i.castSucc).1 = j0)
      rw [Finset.card_univ, Fintype.card_fin] at h
      rw [hOutS]
      have h2 : (Finset.univ.filter (fun i : Fin m => ¬¬(t i.castSucc).1 = j0)).card
          = (Finset.univ.filter (fun i : Fin m => (t i.castSucc).1 = j0)).card := by
        refine congrArg Finset.card (Finset.filter_congr ?_)
        intro k _
        constructor
        · intro hk
          exact Classical.byContradiction hk
        · intro hk hk2
          exact hk2 hk
      omega
    have hgle : ((Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).image
        (fun i => (t i).2)).card
        ≤ (Finset.univ.filter (fun i : Fin m => (t i.castSucc).1 = j0)).card := by
      have hsub : (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0))
          ⊆ (Finset.univ.filter
            (fun i : Fin m => (t i.castSucc).1 = j0)).image Fin.castSucc := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_image]
        have hine : i ≠ Fin.last m := fun h => hlast (h ▸ hi.2)
        refine ⟨i.castPred hine, ?_, Fin.castSucc_castPred i hine⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [Fin.castSucc_castPred]
        exact hi.2
      calc ((Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).image
            (fun i => (t i).2)).card
          ≤ (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).card :=
            Finset.card_image_le
        _ ≤ ((Finset.univ.filter
            (fun i : Fin m => (t i.castSucc).1 = j0)).image Fin.castSucc).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun i : Fin m => (t i.castSucc).1 = j0)).card :=
            Finset.card_image_le
    obtain ⟨vo, hvoinj, hvocol, hvoavoid⟩ := small_injective_colored_avoid hclass j0 (!b)
      OutS.card ((Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).image
        (fun i => (t i).2)) (by omega)
    refine ⟨fun i =>
      if h : (t i.castSucc).1 = j0 then (t i.castSucc).2
      else vo (OutS.equivFin ⟨i, by
        rw [hOutS, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h⟩⟩), ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split
      · next h => exact hcolT _ h
      · exact hvocol _
    · intro i k he
      dsimp only at he
      by_cases hi : (t i.castSucc).1 = j0 <;> by_cases hk : (t k.castSucc).1 = j0
      · rw [dif_pos hi, dif_pos hk] at he
        have h := hmono.2.2.2 (Prod.ext (hi.trans hk.symm) he)
        exact Fin.castSucc_injective m h
      · exfalso
        rw [dif_pos hi, dif_neg hk] at he
        refine hvoavoid (OutS.equivFin ⟨k, by
          rw [hOutS, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hk⟩⟩) ?_
        rw [← he, Finset.mem_image]
        exact ⟨i.castSucc, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hi⟩, rfl⟩
      · exfalso
        rw [dif_neg hi, dif_pos hk] at he
        refine hvoavoid (OutS.equivFin ⟨i, by
          rw [hOutS, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hi⟩⟩) ?_
        rw [he, Finset.mem_image]
        exact ⟨k.castSucc, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hk⟩, rfl⟩
      · rw [dif_neg hi, dif_neg hk] at he
        have h := hvoinj he
        have h2 := OutS.equivFin.injective h
        exact congrArg Subtype.val h2
    · intro i hi r hr he
      dsimp only at he
      rw [dif_neg hi] at he
      refine hvoavoid (OutS.equivFin ⟨i, by
        rw [hOutS, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hi⟩⟩) ?_
      rw [he, Finset.mem_image]
      exact ⟨r, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ r, hr⟩, rfl⟩
  -- the copy-`j0` demand: each of the first `m` sources against its in-copy target or a
  -- fresh exit
  have hd0 : OppositeDemand (fun w => col (j0, w))
      (fun i : Fin m => (s i.castSucc).2)
      (fun i : Fin m => if (t i.castSucc).1 = j0 then (t i.castSucc).2 else v i) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      rw [hcolS]
      split
      · next h => rw [hcolT _ h]; cases b <;> simp
      · rw [hvcol]; cases b <;> simp
    · intro i k he
      dsimp only at he
      have h := hmono.2.2.1 (Prod.ext ((hS i.castSucc).trans (hS k.castSucc).symm) he)
      exact Fin.castSucc_injective m h
    · intro i k he
      dsimp only at he
      by_cases hti : (t i.castSucc).1 = j0 <;> by_cases htk : (t k.castSucc).1 = j0
      · rw [if_pos hti, if_pos htk] at he
        have h := hmono.2.2.2 (Prod.ext (hti.trans htk.symm) he)
        exact Fin.castSucc_injective m h
      · rw [if_pos hti, if_neg htk] at he
        exact absurd he.symm (hvt k htk i.castSucc hti)
      · rw [if_neg hti, if_pos htk] at he
        exact absurd he (hvt i hti k.castSucc htk)
      · rw [if_neg hti, if_neg htk] at he
        exact hvinj he
    · intro i k he
      dsimp only at he
      have h1 := hcolS i.castSucc
      rw [he] at h1
      revert h1
      split
      · next h => rw [hcolT _ h]; cases b <;> simp
      · rw [hvcol]; cases b <;> simp
  obtain ⟨q, hqp, hqcov, hqdis⟩ := hcovlev j0 _ (by omega) (by omega) _ _ hd0
  -- the carrier of the last source, split there
  obtain ⟨a, ha⟩ := hqcov (s (Fin.last m)).2
  have hsna : (s (Fin.last m)).2 ≠ (s a.castSucc).2 := by
    intro h
    have h2 := hmono.2.2.1 (Prod.ext ((hS (Fin.last m)).trans (hS a.castSucc).symm) h)
    exact (Fin.castSucc_lt_last a).ne' h2
  have hsnend : (s (Fin.last m)).2 ≠
      (if (t a.castSucc).1 = j0 then (t a.castSucc).2 else v a) := by
    intro h
    have h1 := hcolS (Fin.last m)
    rw [h] at h1
    revert h1
    split
    · next hh => rw [hcolT _ hh]; cases b <;> simp
    · rw [hvcol]; cases b <;> simp
  obtain ⟨y, z, A, B, hA, hB, hadj_y_sn, hadj_sn_z, hsuppA⟩ :=
    path_split_interior (q a) (hqp a) ha hsna hsnend
  have hndA := (hqp a).support_nodup
  rw [hsuppA] at hndA
  obtain ⟨hndA1, hndA2, hdisjA⟩ := List.nodup_append.mp hndA
  have hsn_notB : (s (Fin.last m)).2 ∉ B.support := (List.nodup_cons.mp hndA2).1
  have hcoly : col (j0, y) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j0, y) (j0, (s (Fin.last m)).2) :=
      (weldLift Gs M j0).map_adj hadj_y_sn
    have h := hproper _ _ hadj
    have h2 := hcolS (Fin.last m)
    rw [h2] at h
    exact bool_eq_not_of_ne3 h
  have hy_ne_v : ∀ i, (t i.castSucc).1 ≠ j0 → y ≠ v i := by
    intro i hti h
    by_cases hia : i = a
    · subst hia
      have h1 : y ∈ A.support := SimpleGraph.Walk.end_mem_support A
      have h2 : y ∈ ((s (Fin.last m)).2 :: B.support) := by
        refine List.mem_cons_of_mem _ ?_
        rw [h]
        have h5 := SimpleGraph.Walk.end_mem_support (B.copy rfl (if_neg hti))
        rwa [SimpleGraph.Walk.support_copy] at h5
      exact hdisjA y h1 y h2 rfl
    · have h1 : y ∈ (q a).support := by
        rw [hsuppA]
        exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support A)
      have h2 : y ∈ (q i).support := by
        rw [h]
        have h5 := SimpleGraph.Walk.end_mem_support ((q i).copy rfl (if_neg hti))
        rwa [SimpleGraph.Walk.support_copy] at h5
      exact hqdis i a hia y ⟨h2, h1⟩
  -- the touched non-`j0` copies (shared by both subcases)
  set Jt : Finset (Fin ell) := Finset.univ.filter
    (fun j => j ≠ j0 ∧ (weldWSet s t j).Nonempty) with hJt
  have hJtmem : ∀ j, j ∈ Jt ↔ (j ≠ j0 ∧ (weldWSet s t j).Nonempty) := by
    intro j
    rw [hJt, Finset.mem_filter]
    simp
  have hlastW : Fin.last m ∈ weldWSet s t (t (Fin.last m)).1 :=
    mem_weldWSet.mpr (Or.inr rfl)
  have hsplitW : ∀ i : Fin (m + 1), i ∈ weldWSet s t (t i).1 := fun i =>
    mem_weldWSet.mpr (Or.inr rfl)
  have hsplitJt : ∀ i : Fin (m + 1), (t i).1 ≠ j0 → (t i).1 ∈ Jt := fun i hi =>
    (hJtmem _).mpr ⟨hi, ⟨i, hsplitW i⟩⟩
  have htmemJ : ∀ j ∈ Jt, ∀ i ∈ weldWSet s t j, (t i).1 = j := by
    intro j hj i hi
    rcases mem_weldWSet.mp hi with h | h
    · exact absurd ((hS i).symm.trans h) (Ne.symm ((hJtmem j).mp hj).1)
    · exact h
  by_cases hsplit_a : (t a.castSucc).1 = j0
  · -- SUBCASE (ii): the carrier pair is within `j0`
    -- SUBCASE (ii): the carrier pair is within `j0`; the last pair exits through `y`
    -- (the predecessor of the last source), and the carrier is rerouted around the cut
    -- through a Hamilton bridge of a fresh copy `jf` that no target touches
    set exit : Fin (m + 1) → W := Fin.lastCases y (fun i => v i) with hexit
    have hexlast : exit (Fin.last m) = y := by
      rw [hexit]
      exact Fin.lastCases_last
    have hexcast : ∀ i : Fin m, exit i.castSucc = v i := by
      intro i
      rw [hexit]
      exact Fin.lastCases_castSucc ..
    have hexcol : ∀ i, col (j0, exit i) = !b := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [hexlast]
        exact hcoly
      · intro i'
        rw [hexcast]
        exact hvcol i'
    have hexinjS : ∀ i k, (t i).1 ≠ j0 → (t k).1 ≠ j0 → exit i = exit k → i = k := by
      intro i k
      induction i using Fin.lastCases with
      | last =>
        induction k using Fin.lastCases with
        | last => intro _ _ _; rfl
        | cast k' =>
          intro _ htk he
          rw [hexlast, hexcast] at he
          exact absurd he (hy_ne_v k' htk)
      | cast i' =>
        induction k using Fin.lastCases with
        | last =>
          intro hti _ he
          rw [hexlast, hexcast] at he
          exact absurd he.symm (hy_ne_v i' hti)
        | cast k' =>
          intro _ _ he
          rw [hexcast, hexcast] at he
          rw [hvinj he]
    -- peel the exit `y` off the carrier's prefix
    have hyA : y ≠ (s a.castSucc).2 := by
      intro h
      have h1 := hcoly
      rw [h, hcolS a.castSucc] at h1
      cases b <;> simp at h1
    obtain ⟨u0, A', hA', hadj_u0_y, hsuppA', hy_notA'⟩ := path_peel_last A hA hyA
    have hcolu0 : col (j0, u0) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j0, u0) (j0, y) :=
        (weldLift Gs M j0).map_adj hadj_u0_y
      have h := hproper _ _ hadj
      rw [hcoly] at h
      exact bool_eq_of_ne_not3 h
    have hcolz : col (j0, z) = !b := by
      have hadj : (weldGraph ell Gs M).Adj (j0, (s (Fin.last m)).2) (j0, z) :=
        (weldLift Gs M j0).map_adj hadj_sn_z
      have h := hproper _ _ hadj
      rw [hcolS (Fin.last m)] at h
      exact bool_eq_not_of_ne3 (Ne.symm h)
    -- the fresh bridge copy
    obtain ⟨jf, hjf⟩ := small_copy_avoiding_targets (t := t) hEll
    have hjf0 : jf ≠ j0 := by
      intro h
      exact hjf a.castSucc (hsplit_a.trans h.symm)
    have hjfJt : jf ∉ Jt := by
      intro h
      obtain ⟨i, hi⟩ := ((hJtmem jf).mp h).2
      rcases mem_weldWSet.mp hi with hh | hh
      · exact hjf0 (((hS i).symm.trans hh).symm)
      · exact hjf i hh
    have hbrf : col (jf, M j0 jf u0) ≠ col (jf, M j0 jf z) := by
      have h1 := hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjf0) u0)
      have h2 := hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjf0) z)
      rw [hcolu0] at h1
      rw [hcolz] at h2
      rw [bool_eq_not_of_ne3 (Ne.symm h1), bool_eq_of_ne_not3 (Ne.symm h2)]
      cases b <;> simp
    obtain ⟨hf, hhamf⟩ := hlace jf _ _ hbrf
    -- the per-target-copy families
    have hfam := fun j hj => small_case4_family hproper hlace hcov2 hclass hcovlev hmono hS (fun j hj => by have := hw j hj; omega) exit hexcol hexinjS j
      ((hJtmem j).mp hj).1 ((hJtmem j).mp hj).2
    choose Q hQpath hQcov hQdisj using hfam
    have hQtrans : ∀ (j j' : Fin ell) (he : j = j') (hj : j ∈ Jt) (hj' : j' ∈ Jt)
        (r : Fin (m + 1)) (hi : r ∈ weldWSet s t j) (hi' : r ∈ weldWSet s t j') (x2 : W),
        x2 ∈ (Q j hj r hi).support → x2 ∈ (Q j' hj' r hi').support := by
      intro j j' he
      subst he
      intro hj hj' r hi hi' x2 h
      exact h
    -- the `j0`-side segment of each pair
    set g0 : Fin (m + 1) → List W := Fin.lastCases ((s (Fin.last m)).2 :: [y])
      (fun i => if i = a then A'.support ++ B.support else (q i).support) with hg0
    have hg0last : g0 (Fin.last m) = ((s (Fin.last m)).2 :: [y]) := by
      rw [hg0]
      exact Fin.lastCases_last
    have hg0cast : ∀ i : Fin m,
        g0 i.castSucc = if i = a then A'.support ++ B.support else (q i).support := by
      intro i
      rw [hg0]
      exact Fin.lastCases_castSucc ..
    -- membership toolkit for the `q a`-pieces
    have hsubA' : ∀ x2 : W, x2 ∈ A'.support → x2 ∈ A.support := by
      intro x2 h
      rw [hsuppA']
      exact List.mem_append_left _ h
    have hsub_qa : ∀ x2 : W, x2 ∈ g0 a.castSucc → x2 ∈ (q a).support := by
      intro x2 h
      rw [hg0cast, if_pos rfl] at h
      rw [hsuppA]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (hsubA' x2 h)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hsub_last : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ (q a).support := by
      intro x2 h
      rw [hg0last] at h
      rcases List.mem_cons.mp h with h | h
      · rw [h, hsuppA]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · rw [List.mem_singleton] at h
        rw [h, hsuppA]
        exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support A)
    have hlast_va : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ g0 a.castSucc → False := by
      intro x2 h h'
      rw [hg0last] at h
      rw [hg0cast, if_pos rfl] at h'
      rcases List.mem_cons.mp h with h | h
      · rcases List.mem_append.mp h' with h'' | h''
        · exact hdisjA x2 (hsubA' x2 (h ▸ h'')) x2 (h ▸ List.mem_cons_self ..) rfl
        · exact hsn_notB (h ▸ h'')
      · rw [List.mem_singleton] at h
        rcases List.mem_append.mp h' with h'' | h''
        · exact hy_notA' (h ▸ h'')
        · refine hdisjA x2 ?_ x2 (List.mem_cons_of_mem _ h'') rfl
          rw [h, hsuppA']
          exact List.mem_append_right _ (List.mem_singleton_self _)
    have hg0disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g0 r → x2 ∉ g0 r' := by
      intro r r'
      induction r using Fin.lastCases with
      | last =>
        induction r' using Fin.lastCases with
        | last => intro hrr'; exact absurd rfl hrr'
        | cast i' =>
          intro _ x2 h h'
          by_cases hia : i' = a
          · subst hia
            exact hlast_va x2 h h'
          · rw [hg0cast, if_neg hia] at h'
            exact hqdis i' a hia x2 ⟨h', hsub_last x2 h⟩
      | cast i =>
        induction r' using Fin.lastCases with
        | last =>
          intro _ x2 h h'
          by_cases hia : i = a
          · subst hia
            exact hlast_va x2 h' h
          · rw [hg0cast, if_neg hia] at h
            exact hqdis i a hia x2 ⟨h, hsub_last x2 h'⟩
        | cast i' =>
          intro hrr' x2 h h'
          have hii' : i ≠ i' := fun hh => hrr' (by rw [hh])
          by_cases hia : i = a <;> by_cases hia' : i' = a
          · exact absurd (hia.trans hia'.symm) hii'
          · subst hia
            rw [hg0cast, if_neg hia'] at h'
            exact hqdis i' i hia' x2 ⟨h', hsub_qa x2 h⟩
          · subst hia'
            rw [hg0cast, if_neg hia] at h
            exact hqdis i i' hii' x2 ⟨h, hsub_qa x2 h'⟩
          · rw [hg0cast, if_neg hia] at h
            rw [hg0cast, if_neg hia'] at h'
            exact hqdis i i' hii' x2 ⟨h, h'⟩
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j0 ∧ x.2 ∈ g0 r) ∨
            (∃ (hj : x.1 ∈ Jt) (hi : r ∈ weldWSet s t x.1), x.2 ∈ (Q x.1 hj r hi).support) ∨
            (r = a.castSucc ∧ x.1 = jf ∧ x.2 ∈ hf.support)) := by
      intro r
      by_cases hr : r = Fin.last m
      · subst hr
        -- the last pair: the two-vertex segment `sn, y` spliced to its family segment
        have hW2p : (SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcoly
          rw [← h, hcolS (Fin.last m)] at h1
          cases b <;> simp at h1
        obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hlast)
          (SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil)
          (Q (t (Fin.last m)).1 (hsplitJt _ hlast) (Fin.last m) hlastW)
          hW2p (hQpath _ _ _ _)
          (by rw [hexlast])
        refine ⟨R.copy (Prod.ext (hS (Fin.last m)).symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hRp
        · intro x
          rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair, mem_map_pair,
            SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, by rw [hg0last]; exact h2⟩
            · refine Or.inr (Or.inl ?_)
              have hj' : x.1 ∈ Jt := by rw [h1]; exact hsplitJt _ hlast
              have hi' : Fin.last m ∈ weldWSet s t x.1 := by rw [h1]; exact hlastW
              exact ⟨hj', hi', hQtrans _ x.1 h1.symm (hsplitJt _ hlast) hj' _ hlastW hi' x.2 h2⟩
          · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨hlast', -, -⟩)
            · exact Or.inl ⟨h1, by rw [hg0last] at h2; exact h2⟩
            · have hx1 : x.1 = (t (Fin.last m)).1 := (htmemJ x.1 hj _ hi).symm
              exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj (hsplitJt _ hlast) _ hi hlastW x.2 h2⟩
            · exact absurd hlast'.symm (Fin.castSucc_lt_last a).ne
      · obtain ⟨i, hri⟩ : ∃ i : Fin m, r = i.castSucc :=
          ⟨r.castPred hr, (Fin.castSucc_castPred r hr).symm⟩
        subst hri
        by_cases hia : i = a
        · -- the carrier pair: `A'`, the `jf` Hamilton bridge, then the suffix
          subst hia
          have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s i.castSucc) (j0, u0), R.IsPath ∧
              R.support = A'.support.map (fun w' => (j0, w')) := by
            refine ⟨(A'.map (weldLift Gs M j0)).copy
              (Prod.ext (hS i.castSucc).symm rfl) rfl, ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA'
            · rw [SimpleGraph.Walk.support_copy, weldLift_support]
          obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
          obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ hf hR₀p hhamf.isPath
            (weld_cross_adj (Ne.symm hjf0) u0)
            (by
              intro w' _ hmem
              rw [hR₀s, mem_map_pair] at hmem
              exact hjf0 hmem.1)
          obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ (B.copy rfl (if_pos hsplit_a))
            hR₁p (by rw [SimpleGraph.Walk.isPath_copy]; exact hB)
            ((weld_cross_adj (Ne.symm hjf0) z).symm)
            (by
              intro w' hw' hmem
              rw [SimpleGraph.Walk.support_copy] at hw'
              rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
              rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
              · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
              · exact hjf0 h1.symm)
          refine ⟨R₂.copy rfl (Prod.ext hsplit_a.symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hR₂p
          · intro x
            rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s, List.mem_append,
              hR₀s, mem_map_pair, mem_map_pair, mem_map_pair, SimpleGraph.Walk.support_copy]
            constructor
            · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
              · exact Or.inl ⟨h1, by
                  rw [hg0cast, if_pos rfl]
                  exact List.mem_append_left _ h2⟩
              · exact Or.inr (Or.inr ⟨rfl, h1, h2⟩)
              · exact Or.inl ⟨h1, by
                  rw [hg0cast, if_pos rfl]
                  exact List.mem_append_right _ h2⟩
            · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨-, h1, h2⟩)
              · rw [hg0cast, if_pos rfl] at h2
                rcases List.mem_append.mp h2 with h2 | h2
                · exact Or.inl (Or.inl ⟨h1, h2⟩)
                · exact Or.inr ⟨h1, h2⟩
              · have hx1 : x.1 = j0 := ((htmemJ x.1 hj _ hi).symm).trans hsplit_a
                exact absurd hx1 ((hJtmem x.1).mp hj).1
              · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · by_cases hti : (t i.castSucc).1 = j0
          · -- a within pair: its inner path, lifted
            refine ⟨(((q i).copy rfl (if_pos hti)).map (weldLift Gs M j0)).copy
              (Prod.ext (hS i.castSucc).symm rfl) (Prod.ext hti.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              refine SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) ?_
              rw [SimpleGraph.Walk.isPath_copy]
              exact hqp i
            · intro x
              rw [SimpleGraph.Walk.support_copy, weldLift_support,
                SimpleGraph.Walk.support_copy, mem_map_pair]
              constructor
              · rintro ⟨h1, h2⟩
                exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia]; exact h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨hia', -, -⟩)
                · exact ⟨h1, by rw [hg0cast, if_neg hia] at h2; exact h2⟩
                · have hx1 : x.1 = j0 := ((htmemJ x.1 hj _ hi).symm).trans hti
                  exact absurd hx1 ((hJtmem x.1).mp hj).1
                · exact absurd (Fin.castSucc_injective m hia') hia
          · -- a split pair: its inner path spliced to its family segment
            obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hti) ((q i).copy rfl (if_neg hti))
              (Q (t i.castSucc).1 (hsplitJt _ hti) i.castSucc (hsplitW _))
              (by rw [SimpleGraph.Walk.isPath_copy]; exact hqp i) (hQpath _ _ _ _)
              (by rw [hexcast])
            refine ⟨R.copy (Prod.ext (hS i.castSucc).symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hRp
            · intro x
              rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                mem_map_pair, SimpleGraph.Walk.support_copy]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia]; exact h2⟩
                · refine Or.inr (Or.inl ?_)
                  have hj' : x.1 ∈ Jt := by rw [h1]; exact hsplitJt _ hti
                  have hi' : i.castSucc ∈ weldWSet s t x.1 := by rw [h1]; exact hsplitW _
                  exact ⟨hj', hi', hQtrans _ x.1 h1.symm (hsplitJt _ hti) hj' _
                    (hsplitW _) hi' x.2 h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨hia', -, -⟩)
                · exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia] at h2; exact h2⟩
                · have hx1 : x.1 = (t i.castSucc).1 := (htmemJ x.1 hj _ hi).symm
                  exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj (hsplitJt _ hti) _ hi
                    (hsplitW _) x.2 h2⟩
                · exact absurd (Fin.castSucc_injective m hia') hia
    choose P hPp hPchar using hpaths
    refine weld_lemma21 hproper hlace (hmono.st_ne 0 0)
      (insert j0 (insert jf Jt)) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨hj, -, -⟩ | ⟨-, h1, -⟩
      · rw [h1]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
      · rw [h1]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rintro ⟨xj, xw⟩ hxJ
      rw [Finset.mem_insert, Finset.mem_insert] at hxJ
      rcases hxJ with rfl | rfl | hxJt
      · obtain ⟨i, hi⟩ := hqcov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hi
          rcases List.mem_append.mp hi with hmem | hmem
          · rw [hsuppA'] at hmem
            rcases List.mem_append.mp hmem with hmem2 | hmem2
            · exact ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr
                (Or.inl ⟨rfl, by
                  rw [hg0cast, if_pos rfl]
                  exact List.mem_append_left _ hmem2⟩)⟩
            · rw [List.mem_singleton] at hmem2
              exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
                (Or.inl ⟨rfl, by
                  rw [hg0last, hmem2]
                  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
                (Or.inl ⟨rfl, by rw [hg0last, hmem2]; exact List.mem_cons_self ..⟩)⟩
            · exact ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr
                (Or.inl ⟨rfl, by
                  rw [hg0cast, if_pos rfl]
                  exact List.mem_append_right _ hmem2⟩)⟩
        · exact ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr
            (Or.inl ⟨rfl, by rw [hg0cast, if_neg hia]; exact hi⟩)⟩
      · exact ⟨a.castSucc, (hPchar a.castSucc (xj, xw)).mpr
          (Or.inr (Or.inr ⟨rfl, rfl, hhamf.mem_support xw⟩))⟩
      · obtain ⟨i, hi, hmem⟩ := hQcov xj hxJt xw
        exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨hxJt, hi, hmem⟩))⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨hra, h1, h2⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨hj', hi', h2'⟩ | ⟨hra', h1', h2'⟩
      · exact hg0disj r r' hrr' x.2 h2 h2'
      · exact ((hJtmem x.1).mp hj').1 h1
      · exact hjf0 (h1'.symm.trans h1)
      · exact ((hJtmem x.1).mp hj).1 h1'
      · exact hQdisj x.1 hj r hi r' hi' hrr' x.2 ⟨h2, h2'⟩
      · exact hjfJt (h1' ▸ hj)
      · exact hjf0 (h1.symm.trans h1')
      · exact hjfJt (h1 ▸ hj')
      · exact hrr' (hra.trans hra'.symm)

  · -- SUBCASE (i): the carrier pair is split; its exit is renamed to `y`, the last
    -- pair inherits the carrier's old endpoint `v a`
    set exit : Fin (m + 1) → W :=
      Fin.lastCases (v a) (fun i => if i = a then y else v i) with hexit
    have hexlast : exit (Fin.last m) = v a := by
      rw [hexit]
      exact Fin.lastCases_last
    have hexcast : ∀ i : Fin m, exit i.castSucc = if i = a then y else v i := by
      intro i
      rw [hexit]
      exact Fin.lastCases_castSucc ..
    have hexcol : ∀ i, col (j0, exit i) = !b := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [hexlast]
        exact hvcol a
      · intro i'
        rw [hexcast]
        split
        · exact hcoly
        · exact hvcol i'
    have hexinjS : ∀ i k, (t i).1 ≠ j0 → (t k).1 ≠ j0 → exit i = exit k → i = k := by
      intro i k
      induction i using Fin.lastCases with
      | last =>
        induction k using Fin.lastCases with
        | last => intro _ _ _; rfl
        | cast k' =>
          intro _ htk he
          rw [hexlast, hexcast] at he
          revert he
          split
          · intro he
            exact absurd he.symm (hy_ne_v a hsplit_a)
          · next hk =>
            intro he
            exact absurd (hvinj he).symm hk
      | cast i' =>
        induction k using Fin.lastCases with
        | last =>
          intro hti _ he
          rw [hexlast, hexcast] at he
          revert he
          split
          · intro he
            exact absurd he (hy_ne_v a hsplit_a)
          · next hk =>
            intro he
            exact absurd (hvinj he) (fun hh => hk hh)
        | cast k' =>
          intro hti htk he
          rw [hexcast, hexcast] at he
          revert he
          split <;> split
          · next h1 h2 =>
            intro _
            rw [h1, h2]
          · next h1 h2 =>
            intro he
            subst h1
            exact absurd he.symm (Ne.symm (hy_ne_v k' htk))
          · next h1 h2 =>
            intro he
            subst h2
            exact absurd he (Ne.symm (hy_ne_v i' hti))
          · next h1 h2 =>
            intro he
            rw [hvinj he]
    -- the per-target-copy families
    have hfam := fun j hj => small_case4_family hproper hlace hcov2 hclass hcovlev hmono hS (fun j hj => by have := hw j hj; omega) exit hexcol hexinjS j
      ((hJtmem j).mp hj).1 ((hJtmem j).mp hj).2
    choose Q hQpath hQcov hQdisj using hfam
    have hQtrans : ∀ (j j' : Fin ell) (he : j = j') (hj : j ∈ Jt) (hj' : j' ∈ Jt)
        (r : Fin (m + 1)) (hi : r ∈ weldWSet s t j) (hi' : r ∈ weldWSet s t j') (x2 : W),
        x2 ∈ (Q j hj r hi).support → x2 ∈ (Q j' hj' r hi').support := by
      intro j j' he
      subst he
      intro hj hj' r hi hi' x2 h
      exact h
    -- the `j0`-side segment of each pair
    set g0 : Fin (m + 1) → List W := Fin.lastCases ((s (Fin.last m)).2 :: B.support)
      (fun i => if i = a then A.support else (q i).support) with hg0
    have hg0last : g0 (Fin.last m) = ((s (Fin.last m)).2 :: B.support) := by
      rw [hg0]
      exact Fin.lastCases_last
    have hg0cast : ∀ i : Fin m, g0 i.castSucc = if i = a then A.support else (q i).support := by
      intro i
      rw [hg0]
      exact Fin.lastCases_castSucc ..
    have hg0disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g0 r → x2 ∉ g0 r' := by
      intro r r'
      induction r using Fin.lastCases with
      | last =>
        induction r' using Fin.lastCases with
        | last => intro hrr'; exact absurd rfl hrr'
        | cast i' =>
          intro _ x2 h h'
          rw [hg0last] at h
          rw [hg0cast] at h'
          by_cases hia : i' = a
          · subst hia
            rw [if_pos rfl] at h'
            exact hdisjA x2 h' x2 h rfl
          · rw [if_neg hia] at h'
            have hq : x2 ∈ (q a).support := by
              rw [hsuppA]
              exact List.mem_append_right _ h
            exact hqdis i' a hia x2 ⟨h', hq⟩
      | cast i =>
        induction r' using Fin.lastCases with
        | last =>
          intro _ x2 h h'
          rw [hg0cast] at h
          rw [hg0last] at h'
          by_cases hia : i = a
          · subst hia
            rw [if_pos rfl] at h
            exact hdisjA x2 h x2 h' rfl
          · rw [if_neg hia] at h
            have hq : x2 ∈ (q a).support := by
              rw [hsuppA]
              exact List.mem_append_right _ h'
            exact hqdis i a hia x2 ⟨h, hq⟩
        | cast i' =>
          intro hrr' x2 h h'
          have hii' : i ≠ i' := fun hh => hrr' (by rw [hh])
          rw [hg0cast] at h
          rw [hg0cast] at h'
          by_cases hia : i = a <;> by_cases hia' : i' = a
          · exact absurd (hia.trans hia'.symm) hii'
          · subst hia
            rw [if_pos rfl] at h
            rw [if_neg hia'] at h'
            have hq : x2 ∈ (q i).support := by
              rw [hsuppA]
              exact List.mem_append_left _ h
            exact hqdis i' i hia' x2 ⟨h', hq⟩
          · subst hia'
            rw [if_pos rfl] at h'
            rw [if_neg hia] at h
            have hq : x2 ∈ (q i').support := by
              rw [hsuppA]
              exact List.mem_append_left _ h'
            exact hqdis i i' hii' x2 ⟨h, hq⟩
          · rw [if_neg hia] at h
            rw [if_neg hia'] at h'
            exact hqdis i i' hii' x2 ⟨h, h'⟩
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j0 ∧ x.2 ∈ g0 r) ∨
            ∃ (hj : x.1 ∈ Jt) (hi : r ∈ weldWSet s t x.1), x.2 ∈ (Q x.1 hj r hi).support) := by
      intro r
      by_cases hr : r = Fin.last m
      · subst hr
        -- the last pair: `sn ⇝ v a` in `j0` spliced to its target-copy family segment
        have hBc : (B.copy rfl (if_neg hsplit_a)).IsPath := by
          rw [SimpleGraph.Walk.isPath_copy]
          exact hB
        have hsnBp : (SimpleGraph.Walk.cons hadj_sn_z (B.copy rfl (if_neg hsplit_a))).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨hBc, ?_⟩
          rw [SimpleGraph.Walk.support_copy]
          exact hsn_notB
        obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hlast)
          (SimpleGraph.Walk.cons hadj_sn_z (B.copy rfl (if_neg hsplit_a)))
          (Q (t (Fin.last m)).1 (hsplitJt _ hlast) (Fin.last m) hlastW)
          hsnBp (hQpath _ _ _ _)
          (by rw [hexlast])
        refine ⟨R.copy (Prod.ext (hS (Fin.last m)).symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hRp
        · intro x
          rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair, mem_map_pair,
            SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_copy]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, by rw [hg0last]; exact h2⟩
            · refine Or.inr ?_
              have hj' : x.1 ∈ Jt := by rw [h1]; exact hsplitJt _ hlast
              have hi' : Fin.last m ∈ weldWSet s t x.1 := by rw [h1]; exact hlastW
              exact ⟨hj', hi', hQtrans _ x.1 h1.symm (hsplitJt _ hlast) hj' _ hlastW hi' x.2 h2⟩
          · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩)
            · exact Or.inl ⟨h1, by rw [hg0last] at h2; exact h2⟩
            · have hx1 : x.1 = (t (Fin.last m)).1 := (htmemJ x.1 hj _ hi).symm
              exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj (hsplitJt _ hlast) _ hi hlastW x.2 h2⟩
      · obtain ⟨i, hri⟩ : ∃ i : Fin m, r = i.castSucc :=
          ⟨r.castPred hr, (Fin.castSucc_castPred r hr).symm⟩
        subst hri
        by_cases hia : i = a
        · -- the carrier pair: `A` spliced to its target-copy family segment
          subst hia
          obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hsplit_a) A
            (Q (t i.castSucc).1 (hsplitJt _ hsplit_a) i.castSucc (hsplitW _))
            hA (hQpath _ _ _ _)
            (by rw [hexcast, if_pos rfl])
          refine ⟨R.copy (Prod.ext (hS i.castSucc).symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hRp
          · intro x
            rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair, mem_map_pair]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact Or.inl ⟨h1, by rw [hg0cast, if_pos rfl]; exact h2⟩
              · refine Or.inr ?_
                have hj' : x.1 ∈ Jt := by rw [h1]; exact hsplitJt _ hsplit_a
                have hi' : i.castSucc ∈ weldWSet s t x.1 := by rw [h1]; exact hsplitW _
                exact ⟨hj', hi', hQtrans _ x.1 h1.symm (hsplitJt _ hsplit_a) hj' _
                  (hsplitW _) hi' x.2 h2⟩
            · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩)
              · exact Or.inl ⟨h1, by rw [hg0cast, if_pos rfl] at h2; exact h2⟩
              · have hx1 : x.1 = (t i.castSucc).1 := (htmemJ x.1 hj _ hi).symm
                exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj (hsplitJt _ hsplit_a) _ hi
                  (hsplitW _) x.2 h2⟩
        · by_cases hti : (t i.castSucc).1 = j0
          · -- a within pair: its inner path, lifted
            refine ⟨(((q i).copy rfl (if_pos hti)).map (weldLift Gs M j0)).copy
              (Prod.ext (hS i.castSucc).symm rfl) (Prod.ext hti.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              refine SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) ?_
              rw [SimpleGraph.Walk.isPath_copy]
              exact hqp i
            · intro x
              rw [SimpleGraph.Walk.support_copy, weldLift_support,
                SimpleGraph.Walk.support_copy, mem_map_pair]
              constructor
              · rintro ⟨h1, h2⟩
                exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia]; exact h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩)
                · exact ⟨h1, by rw [hg0cast, if_neg hia] at h2; exact h2⟩
                · have hx1 : x.1 = j0 := ((htmemJ x.1 hj _ hi).symm).trans hti
                  exact absurd hx1 ((hJtmem x.1).mp hj).1
          · -- a split pair: its inner path spliced to its target-copy family segment
            obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hti) ((q i).copy rfl (if_neg hti))
              (Q (t i.castSucc).1 (hsplitJt _ hti) i.castSucc (hsplitW _))
              (by rw [SimpleGraph.Walk.isPath_copy]; exact hqp i) (hQpath _ _ _ _)
              (by rw [hexcast, if_neg hia])
            refine ⟨R.copy (Prod.ext (hS i.castSucc).symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hRp
            · intro x
              rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                mem_map_pair, SimpleGraph.Walk.support_copy]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia]; exact h2⟩
                · refine Or.inr ?_
                  have hj' : x.1 ∈ Jt := by rw [h1]; exact hsplitJt _ hti
                  have hi' : i.castSucc ∈ weldWSet s t x.1 := by rw [h1]; exact hsplitW _
                  exact ⟨hj', hi', hQtrans _ x.1 h1.symm (hsplitJt _ hti) hj' _
                    (hsplitW _) hi' x.2 h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩)
                · exact Or.inl ⟨h1, by rw [hg0cast, if_neg hia] at h2; exact h2⟩
                · have hx1 : x.1 = (t i.castSucc).1 := (htmemJ x.1 hj _ hi).symm
                  exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj (hsplitJt _ hti) _ hi
                    (hsplitW _) x.2 h2⟩
    choose P hPp hPchar using hpaths
    refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) (insert j0 Jt) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨hj, -, -⟩
      · rw [h1]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem hj
    · rintro ⟨xj, xw⟩ hxJ
      rw [Finset.mem_insert] at hxJ
      rcases hxJ with rfl | hxJt
      · obtain ⟨i, hi⟩ := hqcov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hi
          rcases List.mem_append.mp hi with hmem | hmem
          · exact ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr
              (Or.inl ⟨rfl, by rw [hg0cast, if_pos rfl]; exact hmem⟩)⟩
          · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
              (Or.inl ⟨rfl, by rw [hg0last]; exact hmem⟩)⟩
        · exact ⟨i.castSucc, (hPchar i.castSucc (xj, xw)).mpr
            (Or.inl ⟨rfl, by rw [hg0cast, if_neg hia]; exact hi⟩)⟩
      · obtain ⟨i, hi, hmem⟩ := hQcov xj hxJt xw
        exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr ⟨hxJt, hi, hmem⟩)⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨hj, hi, h2⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨hj', hi', h2'⟩
      · exact hg0disj r r' hrr' x.2 h2 h2'
      · exact ((hJtmem x.1).mp hj').1 h1
      · exact ((hJtmem x.1).mp hj).1 h1'
      · exact hQdisj x.1 hj r hi r' hi' hrr' x.2 ⟨h2, h2'⟩




/-- **Case 4 of Coleman et al. 2025, Proposition 1.6**: all sources in copy `j0`, some
    target elsewhere, and every copy other than `j0` meets at most `n − 1` pairs. (The
    paper's "WLOG `tn ∉ V(G_{j0})`" is realized by transporting the cover along the
    demand permutation swapping the offending index with the last.) -/
theorem small_case4 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ 2 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m')
    (hn3 : n = 3) (hElln : n + 1 ≤ ell) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT0 : ∃ i, (t i).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ n - 1) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn : 3 ≤ n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i₀, hi₀⟩ := hT0
  apply dpc_perm (Equiv.swap i₀ (Fin.last m))
  have hmono' : MonoDemand col b (fun i => s (Equiv.swap i₀ (Fin.last m) i))
      (fun i => t (Equiv.swap i₀ (Fin.last m) i)) :=
    ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
      hmono.2.2.1.comp (Equiv.swap i₀ (Fin.last m)).injective,
      hmono.2.2.2.comp (Equiv.swap i₀ (Fin.last m)).injective⟩
  have hS' : ∀ i, ((fun i => s (Equiv.swap i₀ (Fin.last m) i)) i).1 = j0 := fun i => hS _
  have hlast' : ((fun i => t (Equiv.swap i₀ (Fin.last m) i)) (Fin.last m)).1 ≠ j0 := by
    dsimp only
    rw [Equiv.swap_apply_right]
    exact hi₀
  have hw' : ∀ j, j ≠ j0 →
      (weldWSet (fun i => s (Equiv.swap i₀ (Fin.last m) i))
        (fun i => t (Equiv.swap i₀ (Fin.last m) i)) j).card ≤ m + 1 - 1 := by
    intro j hj
    have hcard : (weldWSet (fun i => s (Equiv.swap i₀ (Fin.last m) i))
        (fun i => t (Equiv.swap i₀ (Fin.last m) i)) j).card = (weldWSet s t j).card := by
      apply Finset.card_bij (fun i _ => Equiv.swap i₀ (Fin.last m) i)
      · intro i hi
        rw [mem_weldWSet] at hi ⊢
        exact hi
      · intro i _ i' _ he
        exact (Equiv.swap i₀ (Fin.last m)).injective he
      · intro i hi
        refine ⟨(Equiv.swap i₀ (Fin.last m)).symm i, ?_, ?_⟩
        · rw [mem_weldWSet] at hi ⊢
          simpa using hi
        · exact (Equiv.swap i₀ (Fin.last m)).apply_symm_apply i
    rw [hcard]
    exact hw j hj
  have hm2 : m = 2 := by omega
  have hEllm : m + 2 ≤ ell := by omega
  exact small_case4_core hproper hlace hcov2 hclass hcovlev hm2 hEllm hmono' hS' hlast' hw'


end SmallCase4

section SmallExplicit

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- Extract a 2-cover with explicit endpoints from the part-(b) property. -/
private theorem small_pdpc2
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (j : Fin ell) {a0 a1 b0 b1 : W}
    (hc00 : col (j, a0) ≠ col (j, b0)) (hc11 : col (j, a1) ≠ col (j, b1))
    (hss : a0 ≠ a1) (htt : b0 ≠ b1)
    (h00 : a0 ≠ b0) (h01 : a0 ≠ b1) (h10 : a1 ≠ b0) (h11 : a1 ≠ b1) :
    ∃ (P0 : (Gs j).Walk a0 b0) (P1 : (Gs j).Walk a1 b1),
      P0.IsPath ∧ P1.IsPath ∧
      (∀ w : W, w ∈ P0.support ∨ w ∈ P1.support) ∧
      (∀ w : W, w ∈ P0.support → w ∉ P1.support) := by
  classical
  have hd : OppositeDemand (fun w => col (j, w)) (pairMap a0 a1) (pairMap b0 b1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simpa using (by first | exact hc00 | exact hc11)
    · intro i k he
      fin_cases i <;> fin_cases k <;> simp_all [pairMap] <;>
        first
          | rfl
          | exact absurd he hss
          | exact absurd he hss.symm
    · intro i k he
      fin_cases i <;> fin_cases k <;> simp_all [pairMap] <;>
        first
          | rfl
          | exact absurd he htt
          | exact absurd he htt.symm
    · intro i k
      fin_cases i <;> fin_cases k <;> simp [pairMap] <;>
        first
          | exact h00
          | exact h01
          | exact h10
          | exact h11
  obtain ⟨q, hqp, hqcov, hqdis⟩ := hcov2 j _ _ hd
  refine ⟨(q 0).copy (by simp) (by simp), (q 1).copy (by simp) (by simp), ?_, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_copy]
    exact hqp 0
  · rw [SimpleGraph.Walk.isPath_copy]
    exact hqp 1
  · intro w
    obtain ⟨i, hi⟩ := hqcov w
    fin_cases i
    · exact Or.inl (by rw [SimpleGraph.Walk.support_copy]; exact hi)
    · exact Or.inr (by rw [SimpleGraph.Walk.support_copy]; exact hi)
  · intro w hw hw2
    rw [SimpleGraph.Walk.support_copy] at hw hw2
    exact hqdis 0 1 (by decide) w ⟨hw, hw2⟩

end SmallExplicit

section SmallCase6

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 6: two full copies at three pairs, normalized shape:
    `{s₀, s₁, t₂} ⊆ j1`, `{s₂, t₀, t₁} ⊆ j2`. -/
private theorem small_case6_core
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hs0 : (s 0).1 = j1) (hs1 : (s 1).1 = j1) (ht2 : (t 2).1 = j1)
    (hs2 : (s 2).1 = j2) (ht0 : (t 0).1 = j2) (ht1 : (t 1).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  obtain ⟨j3, j4, hj31, hj32, hj41, hj42, hj34⟩ := fin_exists_two_avoid3 hell4 j1 j2
  have hcS : ∀ i, (s i).1 = j1 → col (j1, (s i).2) = b := by
    intro i hi
    rw [show ((j1 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcS2 : col (j2, (s 2).2) = b := by
    rw [show ((j2 : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT2 : col (j1, (t 2).2) = !b := by
    rw [show ((j1 : Fin ell), (t 2).2) = t 2 from Prod.ext ht2.symm rfl]
    exact hmono.2.1 2
  have hcT0 : col (j2, (t 0).2) = !b := by
    rw [show ((j2 : Fin ell), (t 0).2) = t 0 from Prod.ext ht0.symm rfl]
    exact hmono.2.1 0
  have hcT1 : col (j2, (t 1).2) = !b := by
    rw [show ((j2 : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  -- the fresh white connector in j1, avoiding t₂ and the pullback of s₂
  obtain ⟨v1, hv1c, hv1a⟩ := exists_avoid_of_class hclass j1 (!b)
    ({(t 2).2} ∪ {(M j1 j2).symm (s 2).2}) (by
      refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
      simp)
  obtain ⟨u1, hu1def⟩ : ∃ u1, u1 = M j1 j2 v1 := ⟨_, rfl⟩
  have hcu1 : col (j2, u1) = b := by
    have h : col (j1, v1) ≠ col (j2, u1) :=
      hu1def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj12 v1)
    rw [hv1c] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  have hu1s2 : u1 ≠ (s 2).2 := by
    intro h
    apply hv1a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    refine Or.inr ?_
    rw [← h, hu1def, Equiv.symm_apply_apply]
  have hv1t2 : v1 ≠ (t 2).2 := by
    intro h
    apply hv1a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    exact Or.inl h
  -- pairwise distinctness of the demand coordinates
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hne_t0t1 : (t 0).2 ≠ (t 1).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 0) (a₂ := 1) (Prod.ext (ht0.trans ht1.symm) h)
    exact absurd this (by decide)
  have hne_sb : ∀ i k, (s i).1 = j1 → (t k).1 = j1 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  -- the two 2-covers
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j1
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := v1) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hv1c]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT2]; cases b <;> simp)
    hne_s0s1 hv1t2
    (by
      intro h
      have h1 := hcS 0 hs0
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hne_sb 0 2 hs0 ht2)
    (by
      intro h
      have h1 := hcS 1 hs1
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hne_sb 1 2 hs1 ht2)
  obtain ⟨B0, B1, hB0, hB1, hBcov, hBdis⟩ := small_pdpc2 hcov2 j2
    (a0 := u1) (a1 := (s 2).2) (b0 := (t 0).2) (b1 := (t 1).2)
    (by rw [hcu1, hcT0]; cases b <;> simp)
    (by rw [hcS2, hcT1]; cases b <;> simp)
    hu1s2 hne_t0t1
    (by
      intro h
      have h1 := hcu1
      rw [h, hcT0] at h1
      cases b <;> simp at h1)
    (by
      intro h
      have h1 := hcu1
      rw [h, hcT1] at h1
      cases b <;> simp at h1)
    (fun h => hmono.st_ne 2 0 (Prod.ext (hs2.trans ht0.symm) h))
    (fun h => hmono.st_ne 2 1 (Prod.ext (hs2.trans ht1.symm) h))
  -- peel the front of A1 (frees s₁) and the end of B1 (frees t₁)
  have hA1ne : (s 1).2 ≠ (t 2).2 := hne_sb 1 2 hs1 ht2
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1 hA1ne
  have hcv3 : col (j1, v3) = !b := by
    have h : col (j1, (s 1).2) ≠ col (j1, v3) :=
      hproper _ _ ((weldLift Gs M j1).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  have hB1ne : (t 1).2 ≠ (s 2).2 := by
    intro h
    exact hmono.st_ne 2 1 (Prod.ext (hs2.trans ht1.symm) h.symm)
  obtain ⟨u3, B1', hB1', hadju3, hB1supp, ht1B1'⟩ := path_peel_last B1 hB1 hB1ne
  have hcu3 : col (j2, u3) = b := by
    have h : col (j2, u3) ≠ col (j2, (t 1).2) :=
      hproper _ _ ((weldLift Gs M j2).map_adj hadju3)
    rw [hcT1] at h
    exact bool_eq_of_ne_not3 h
  -- bridge copies
  obtain ⟨v2, hv2def⟩ : ∃ v2, v2 = M j1 j3 (s 1).2 := ⟨_, rfl⟩
  have hcv2 : col (j3, v2) = !b := by
    have h : col (j1, (s 1).2) ≠ col (j3, v2) :=
      hv2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨u2, hu2def⟩ : ∃ u2, u2 = M j2 j3 (t 1).2 := ⟨_, rfl⟩
  have hcu2 : col (j3, u2) = b := by
    have h : col (j2, (t 1).2) ≠ col (j3, u2) :=
      hu2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) (t 1).2)
    rw [hcT1] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  obtain ⟨q3, hq3⟩ := hlace j3 v2 u2 (by
    show col (j3, v2) ≠ col (j3, u2)
    rw [hcv2, hcu2]
    cases b <;> simp)
  obtain ⟨u3s, hu3sdef⟩ : ∃ x, x = M j2 j4 u3 := ⟨_, rfl⟩
  have hcu3s : col (j4, u3s) = !b := by
    have h : col (j2, u3) ≠ col (j4, u3s) :=
      hu3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) u3)
    rw [hcu3] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j1 j4 v3 := ⟨_, rfl⟩
  have hcv3s : col (j4, v3s) = b := by
    have h : col (j1, v3) ≠ col (j4, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj41) v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  obtain ⟨q4, hq4⟩ := hlace j4 u3s v3s (by
    show col (j4, u3s) ≠ col (j4, v3s)
    rw [hcu3s, hcv3s]
    cases b <;> simp)
  -- pair 0: A0 in j1, cross, B0 in j2
  have hR00 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j1, v1), R.IsPath ∧
      R.support = A0.support.map (fun w => (j1, w)) := by
    refine ⟨(A0.map (weldLift Gs M j1)).copy (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R00, hR00p, hR00s⟩ := hR00
  obtain ⟨R01, hR01p, hR01s⟩ := weld_splice_snoc R00 B0 hR00p hB0
    (hu1def ▸ weld_cross_adj (Gs := Gs) (M := M) hj12 v1)
    (by
      intro w' _ hmem
      rw [hR00s, mem_map_pair] at hmem
      exact hj12 hmem.1.symm)
  -- pair 1: s₁ alone, bridge in j3, the freed edge to t₁
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (j3, v2) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) (s 1).2
    rw [← hv2def] at h
    rwa [show ((j1 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hadj1b : (weldGraph ell Gs M).Adj (j3, u2) (j2, (t 1).2) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) (t 1).2
    rw [← hu2def] at h
    exact h.symm
  have hP1 : ∃ P : (weldGraph ell Gs M).Walk (s 1) (t 1), P.IsPath ∧
      P.support = s 1 :: (q3.support.map (fun w => (j3, w)) ++ [t 1]) := by
    have hq3lift : ∃ Q : (weldGraph ell Gs M).Walk (j3, v2) (j3, u2), Q.IsPath ∧
        Q.support = q3.support.map (fun w => (j3, w)) := by
      refine ⟨(q3.map (weldLift Gs M j3)).copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq3.isPath
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hq3lift
    have hQ' : ∃ Q' : (weldGraph ell Gs M).Walk (j3, v2) (t 1), Q'.IsPath ∧
        Q'.support = q3.support.map (fun w => (j3, w)) ++ [t 1] := by
      refine ⟨(Q.concat hadj1b).copy rfl (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.concat_isPath_iff]
        refine ⟨hQp, ?_⟩
        intro hmem
        rw [hQs, mem_map_pair] at hmem
        exact hj32 hmem.1.symm
      · rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, hQs,
          show ((j2 : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    obtain ⟨Q', hQ'p, hQ's⟩ := hQ'
    refine ⟨SimpleGraph.Walk.cons hadj1a Q', ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQ'p, ?_⟩
      intro hmem
      rw [hQ's, List.mem_append, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | h1
      · exact hj31 (h1.symm.trans hs1)
      · rw [List.mem_singleton] at h1
        exact hmono.st_ne 1 1 h1
    · rw [SimpleGraph.Walk.support_cons, hQ's]
  obtain ⟨P1w, hP1p, hP1s⟩ := hP1
  -- pair 2: the peeled j2 prefix, the j4 bridge, the freed j1 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (j2, u3), R.IsPath ∧
      R.support = B1'.support.map (fun w => (j2, w)) := by
    refine ⟨(B1'.map (weldLift Gs M j2)).copy (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hB1'
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20 q4 hR20p hq4.isPath
    (hu3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) u3)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hj42 hmem.1)
  obtain ⟨R22, hR22p, hR22s⟩ := weld_splice_snoc R21 A1' hR21p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj41) v3).symm)
    (by
      intro w' _ hmem
      rw [hR21s, List.mem_append, hR20s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj12 h1
      · exact hj41 h1.symm)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ ((x.1 = j1 ∧ x.2 ∈ A0.support) ∨ (x.1 = j2 ∧ x.2 ∈ B0.support))) ∨
          (i = 1 ∧ (x = s 1 ∨ (x.1 = j3 ∧ x.2 ∈ q3.support) ∨ x = t 1)) ∨
          (i = 2 ∧ ((x.1 = j2 ∧ x.2 ∈ B1'.support) ∨ (x.1 = j4 ∧ x.2 ∈ q4.support) ∨
            (x.1 = j1 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨R01.copy rfl (Prod.ext ht0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR01p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR01s, List.mem_append, hR00s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨rfl, Or.inl ⟨h1, h2⟩⟩
          · exact Or.inl ⟨rfl, Or.inr ⟨h1, h2⟩⟩
        · rintro (⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨P1w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP1p
      intro x
      rw [SimpleGraph.Walk.support_copy, hP1s]
      constructor
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
        · rcases List.mem_append.mp h with h2 | h2
          · rw [mem_map_pair] at h2
            exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h2)⟩)
          · rw [List.mem_singleton] at h2
            exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr h2)⟩)
      · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩ | h⟩ | ⟨h0, -⟩)
        · exact absurd h0 (by decide)
        · exact h ▸ List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
          rw [mem_map_pair]
          exact ⟨h1, h2⟩
        · refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
          rw [List.mem_singleton]
          exact h
        · exact absurd h0 (by decide)
    · refine ⟨R22.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR22p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR22s, List.mem_append, hR21s,
          List.mem_append, hR20s, mem_map_pair, mem_map_pair, mem_map_pair]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨h1, h2⟩)⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j1, j2, j3, j4} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
      ⟨-, h | ⟨h1, -⟩ | h⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inr (Or.inl h1))
    · rw [h]
      exact Or.inr (Or.inl ht1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr
            ⟨rfl, h2⟩)⟩))⟩
    · rcases hBcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
      · rw [hB1supp] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
            ⟨rfl, h2⟩⟩))⟩
        · rw [List.mem_singleton] at h2
          exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr
            (Prod.ext ht1.symm h2))⟩))⟩
    · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl
        ⟨rfl, hq3.mem_support xw⟩)⟩))⟩
    · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
        ⟨rfl, hq4.mem_support xw⟩)⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hd01 : ∀ (y : Fin ell × W),
        ((y.1 = j1 ∧ y.2 ∈ A0.support) ∨ (y.1 = j2 ∧ y.2 ∈ B0.support)) →
        (y = s 1 ∨ (y.1 = j3 ∧ y.2 ∈ q3.support) ∨ y = t 1) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (h | ⟨hz1, -⟩ | h)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj31 (hz1.symm.trans hy1)
      · have hy1' : (t 1).1 = j1 := (congrArg Prod.fst h).symm.trans hy1
        exact hj12 (hy1'.symm.trans ht1)
      · have hs1' : (s 1).1 = j2 := (congrArg Prod.fst h).symm.trans hy1
        exact hj12 (hs1.symm.trans hs1')
      · exact hj32 (hz1.symm.trans hy1)
      · refine hBdis y.2 hy2 ?_
        rw [show y.2 = (t 1).2 from congrArg Prod.snd h, hB1supp]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    have hd02 : ∀ (y : Fin ell × W),
        ((y.1 = j1 ∧ y.2 ∈ A0.support) ∨ (y.1 = j2 ∧ y.2 ∈ B0.support)) →
        ((y.1 = j2 ∧ y.2 ∈ B1'.support) ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨
          (y.1 = j1 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (⟨hz1, hz2⟩ | ⟨hz1, -⟩ | ⟨hz1, hz2⟩)
      · exact hj12 (hy1.symm.trans hz1)
      · exact hj41 (hz1.symm.trans hy1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
      · refine hBdis y.2 hy2 ?_
        rw [hB1supp]
        exact List.mem_append_left _ hz2
      · exact hj42 (hz1.symm.trans hy1)
      · exact hj12 (hz1.symm.trans hy1)
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = j3 ∧ y.2 ∈ q3.support) ∨ y = t 1) →
        ((y.1 = j2 ∧ y.2 ∈ B1'.support) ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨
          (y.1 = j1 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, -⟩ | h) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have hs1' : (s 1).1 = j2 := (congrArg Prod.fst h).symm.trans hw1
        exact hj12 (hs1.symm.trans hs1')
      · have hs1' : (s 1).1 = j4 := (congrArg Prod.fst h).symm.trans hw1
        exact hj41 (hs1'.symm.trans hs1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hj32 (hz1.symm.trans hw1)
      · exact hj34 (hz1.symm.trans hw1)
      · exact hj31 (hz1.symm.trans hw1)
      · refine ht1B1' ?_
        rw [← show y.2 = (t 1).2 from congrArg Prod.snd h]
        exact hw2
      · have ht1' : (t 1).1 = j4 := (congrArg Prod.fst h).symm.trans hw1
        exact hj42 (ht1'.symm.trans ht1)
      · have ht1' : (t 1).1 = j1 := (congrArg Prod.fst h).symm.trans hw1
        exact hj12 (ht1'.symm.trans ht1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq⟩ | ⟨hj1', hq⟩ | ⟨hj2', hq⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq
    · exact hd02 x hp hq
    · exact hd01 x hq hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq
    · exact hd02 x hq hp
    · exact hd12 x hq hp
    · exact hij (hi2.trans hj2'.symm)


end SmallCase6

section SmallCase5

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- A copy avoiding three named ones, given `ℓ ≥ 4`. -/
private theorem fin_exists_one_avoid3 {ell : ℕ} (h : 4 ≤ ell) (a b c : Fin ell) :
    ∃ d : Fin ell, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  classical
  have hlt : ({a, b, c} : Finset (Fin ell)).card < (Finset.univ : Finset (Fin ell)).card := by
    have h1 : ({a, b, c} : Finset (Fin ell)).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans (by
        have := (Finset.card_insert_le b ({c} : Finset (Fin ell)))
        simp only [Finset.card_singleton] at this ⊢
        omega)
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
  exact ⟨d, fun h => hd (Or.inl h), fun h => hd (Or.inr (Or.inl h)),
    fun h => hd (Or.inr (Or.inr h))⟩

end SmallCase5

section SmallCase511

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 5.1a: `{s₀, t₀, s₁, t₂} ⊆ j0`, `t₁` and `s₂` share the copy `jB`. -/
private theorem small_case5_11
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 jB : Fin ell} (hj0B : j0 ≠ jB)
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0) (ht0 : (t 0).1 = j0)
    (ht1 : (t 1).1 = jB) (hs2 : (s 2).1 = jB) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  obtain ⟨j3, hj30, hj3B, -⟩ := fin_exists_one_avoid3 hell4 j0 jB j0
  have hcS : ∀ i, (s i).1 = j0 → col (j0, (s i).2) = b := fun i hi => by
    rw [show ((j0 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcT : ∀ i, (t i).1 = j0 → col (j0, (t i).2) = !b := fun i hi => by
    rw [show ((j0 : Fin ell), (t i).2) = t i from Prod.ext hi.symm rfl]
    exact hmono.2.1 i
  have hcS2 : col (jB, (s 2).2) = b := by
    rw [show ((jB : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT1 : col (jB, (t 1).2) = !b := by
    rw [show ((jB : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  -- the j0 2-cover
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hne_t0t2 : (t 0).2 ≠ (t 2).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 0) (a₂ := 2) (Prod.ext (ht0.trans ht2.symm) h)
    exact absurd this (by decide)
  have hst00 : ∀ i k, (s i).1 = j0 → (t k).1 = j0 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j0
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := (t 0).2) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hcT 0 ht0]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT 2 ht2]; cases b <;> simp)
    hne_s0s1 hne_t0t2
    (hst00 0 0 hs0 ht0) (hst00 0 2 hs0 ht2) (hst00 1 0 hs1 ht0) (hst00 1 2 hs1 ht2)
  -- peel the front of the second leg
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1
    (hst00 1 2 hs1 ht2)
  have hcv3 : col (j0, v3) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j0, v3) :=
      hproper _ _ ((weldLift Gs M j0).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j0 jB v3 := ⟨_, rfl⟩
  have hcv3s : col (jB, v3s) = b := by
    have h : col (j0, v3) ≠ col (jB, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0B v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- the jB Hamilton path, split inclusively at v3*
  obtain ⟨H, hH⟩ := hlace jB (s 2).2 (t 1).2 (by
    show col (jB, (s 2).2) ≠ col (jB, (t 1).2)
    rw [hcS2, hcT1]
    cases b <;> simp)
  have hv3smem : v3s ∈ H.support := hH.mem_support v3s
  have hne_v3st1 : v3s ≠ (t 1).2 := by
    intro h
    have h1 := hcv3s
    rw [h, hcT1] at h1
    cases b <;> simp at h1
  have hsuppH : H.support = (H.takeUntil v3s hv3smem).support
      ++ (H.dropUntil v3s hv3smem).support.tail := by
    conv_lhs => rw [← H.take_spec hv3smem]
    rw [SimpleGraph.Walk.support_append]
  have htakeH : (H.takeUntil v3s hv3smem).IsPath := hH.isPath.takeUntil hv3smem
  have hdropH : (H.dropUntil v3s hv3smem).IsPath := hH.isPath.dropUntil hv3smem
  obtain ⟨w2, D, hD, hadjw2, hdropsupp, hv3sD⟩ :=
    path_peel_head (H.dropUntil v3s hv3smem) hdropH hne_v3st1
  have hcw2 : col (jB, w2) = !b := by
    have h : col (jB, v3s) ≠ col (jB, w2) :=
      hproper _ _ ((weldLift Gs M jB).map_adj hadjw2)
    rw [hcv3s] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  -- the j3 bridge
  obtain ⟨u2s, hu2sdef⟩ : ∃ x, x = M j0 j3 (s 1).2 := ⟨_, rfl⟩
  have hcu2s : col (j3, u2s) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j3, u2s) :=
      hu2sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨w2s, hw2sdef⟩ : ∃ x, x = M jB j3 w2 := ⟨_, rfl⟩
  have hcw2s : col (j3, w2s) = b := by
    have h : col (jB, w2) ≠ col (j3, w2s) :=
      hw2sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj3B) w2)
    rw [hcw2] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  obtain ⟨q3, hq3⟩ := hlace j3 u2s w2s (by
    show col (j3, u2s) ≠ col (j3, w2s)
    rw [hcu2s, hcw2s]
    cases b <;> simp)
  -- pair 0
  have hP0 : ∃ P : (weldGraph ell Gs M).Walk (s 0) (t 0), P.IsPath ∧
      P.support = A0.support.map (fun w => (j0, w)) := by
    refine ⟨(A0.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl)
      (Prod.ext ht0.symm rfl), ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨P0w, hP0p, hP0s⟩ := hP0
  -- pair 1: s₁ alone, the bridge, the freed jB suffix
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (j3, u2s) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj30) (s 1).2
    rw [← hu2sdef] at h
    rwa [show ((j0 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hR10 : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j3, w2s), R.IsPath ∧
      R.support = s 1 :: q3.support.map (fun w => (j3, w)) := by
    have hq3l : ∃ Q : (weldGraph ell Gs M).Walk (j3, u2s) (j3, w2s), Q.IsPath ∧
        Q.support = q3.support.map (fun w => (j3, w)) := by
      refine ⟨(q3.map (weldLift Gs M j3)).copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq3.isPath
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hq3l
    refine ⟨SimpleGraph.Walk.cons hadj1a Q, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQp, ?_⟩
      intro hmem
      rw [hQs, mem_map_pair] at hmem
      exact hj30 (hmem.1.symm.trans hs1)
    · rw [SimpleGraph.Walk.support_cons, hQs]
  obtain ⟨R10, hR10p, hR10s⟩ := hR10
  obtain ⟨R11, hR11p, hR11s⟩ := weld_splice_snoc R10 D hR10p hD
    ((hw2sdef ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj3B) w2).symm)
    (by
      intro w' _ hmem
      rw [hR10s] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · have h1 : jB = j0 := (congrArg Prod.fst h).trans hs1
        exact hj0B h1.symm
      · rw [mem_map_pair] at h
        exact hj3B h.1.symm)
  -- pair 2: the jB prefix, back through v3, the j0 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (jB, v3s), R.IsPath ∧
      R.support = (H.takeUntil v3s hv3smem).support.map (fun w => (jB, w)) := by
    refine ⟨((H.takeUntil v3s hv3smem).map (weldLift Gs M jB)).copy
      (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) htakeH
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20 A1' hR20p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hj0B v3).symm)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hj0B hmem.1)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ x.1 = j0 ∧ x.2 ∈ A0.support) ∨
          (i = 1 ∧ (x = s 1 ∨ (x.1 = j3 ∧ x.2 ∈ q3.support) ∨
            (x.1 = jB ∧ x.2 ∈ D.support))) ∨
          (i = 2 ∧ ((x.1 = jB ∧ x.2 ∈ (H.takeUntil v3s hv3smem).support) ∨
            (x.1 = j0 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨P0w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP0p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hP0s, mem_map_pair]
        constructor
        · rintro ⟨h1, h2⟩
          exact Or.inl ⟨rfl, h1, h2⟩
        · rintro (⟨-, h1, h2⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨R11.copy rfl (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR11p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR11s, List.mem_append, hR10s,
          mem_map_pair]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · rcases List.mem_cons.mp h with h2 | h2
            · exact Or.inr (Or.inl ⟨rfl, Or.inl h2⟩)
            · rw [mem_map_pair] at h2
              exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h2)⟩)
          · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩)
          · exact absurd h0 (by decide)
          · exact Or.inl (h ▸ List.mem_cons_self ..)
          · refine Or.inl (List.mem_cons_of_mem _ ?_)
            rw [mem_map_pair]
            exact ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
    · refine ⟨R21.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR21p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR21s, List.mem_append, hR20s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨h1, h2⟩⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j0, jB, j3} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, h1, -⟩ |
      ⟨-, h | ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, rfl, h⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr
            ⟨rfl, h2⟩⟩))⟩
    · have h := hH.mem_support xw
      rw [hsuppH] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
          ⟨rfl, h⟩⟩))⟩
      · rw [hdropsupp] at h
        exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr
          ⟨rfl, h⟩)⟩))⟩
    · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl
        ⟨rfl, hq3.mem_support xw⟩)⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hdisjH : ∀ w, w ∈ (H.takeUntil v3s hv3smem).support → w ∈ D.support → False := by
      intro w hw hw2
      have hnd := hH.isPath.support_nodup
      rw [hsuppH, hdropsupp] at hnd
      exact (List.nodup_append.mp hnd).2.2 w hw w hw2 rfl
    have hd01 : ∀ (y : Fin ell × W), (y.1 = j0 ∧ y.2 ∈ A0.support) →
        (y = s 1 ∨ (y.1 = j3 ∧ y.2 ∈ q3.support) ∨ (y.1 = jB ∧ y.2 ∈ D.support)) →
        False := by
      rintro y ⟨hy1, hy2⟩ (h | ⟨hz1, -⟩ | ⟨hz1, -⟩)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj30 (hz1.symm.trans hy1)
      · exact hj0B (hy1.symm.trans hz1)
    have hd02 : ∀ (y : Fin ell × W), (y.1 = j0 ∧ y.2 ∈ A0.support) →
        ((y.1 = jB ∧ y.2 ∈ (H.takeUntil v3s hv3smem).support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y ⟨hy1, hy2⟩ (⟨hz1, -⟩ | ⟨-, hz2⟩)
      · exact hj0B (hy1.symm.trans hz1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = j3 ∧ y.2 ∈ q3.support) ∨ (y.1 = jB ∧ y.2 ∈ D.support)) →
        ((y.1 = jB ∧ y.2 ∈ (H.takeUntil v3s hv3smem).support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hj0B (hs1.symm.trans h1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hj3B (hz1.symm.trans hw1)
      · exact hj30 (hz1.symm.trans hw1)
      · exact hdisjH y.2 hw2 hz2
      · exact hj0B (hw1.symm.trans hz1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq⟩ | ⟨hj1', hq⟩ | ⟨hj2', hq⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq
    · exact hd02 x hp hq
    · exact hd01 x hq hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq
    · exact hd02 x hq hp
    · exact hd12 x hq hp
    · exact hij (hi2.trans hj2'.symm)

end SmallCase511

section SmallCase512

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 5.1b: `{s₀, t₀, s₁, t₂} ⊆ j0`, `t₁ ∈ jB`, `s₂ ∈ jC`, all distinct. -/
private theorem small_case5_12
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    {b : Bool} {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 jB jC : Fin ell} (hj0B : j0 ≠ jB) (hj0C : j0 ≠ jC) (hjBC : jB ≠ jC)
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0) (ht0 : (t 0).1 = j0)
    (ht1 : (t 1).1 = jB) (hs2 : (s 2).1 = jC) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  have hcS : ∀ i, (s i).1 = j0 → col (j0, (s i).2) = b := fun i hi => by
    rw [show ((j0 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcT : ∀ i, (t i).1 = j0 → col (j0, (t i).2) = !b := fun i hi => by
    rw [show ((j0 : Fin ell), (t i).2) = t i from Prod.ext hi.symm rfl]
    exact hmono.2.1 i
  have hcS2 : col (jC, (s 2).2) = b := by
    rw [show ((jC : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT1 : col (jB, (t 1).2) = !b := by
    rw [show ((jB : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hne_t0t2 : (t 0).2 ≠ (t 2).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 0) (a₂ := 2) (Prod.ext (ht0.trans ht2.symm) h)
    exact absurd this (by decide)
  have hst00 : ∀ i k, (s i).1 = j0 → (t k).1 = j0 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j0
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := (t 0).2) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hcT 0 ht0]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT 2 ht2]; cases b <;> simp)
    hne_s0s1 hne_t0t2
    (hst00 0 0 hs0 ht0) (hst00 0 2 hs0 ht2) (hst00 1 0 hs1 ht0) (hst00 1 2 hs1 ht2)
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1
    (hst00 1 2 hs1 ht2)
  have hcv3 : col (j0, v3) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j0, v3) :=
      hproper _ _ ((weldLift Gs M j0).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  -- connector images in jB
  obtain ⟨v2, hv2def⟩ : ∃ x, x = M j0 jB (s 1).2 := ⟨_, rfl⟩
  have hcv2 : col (jB, v2) = !b := by
    have h : col (j0, (s 1).2) ≠ col (jB, v2) :=
      hv2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0B (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j0 jB v3 := ⟨_, rfl⟩
  have hcv3s : col (jB, v3s) = b := by
    have h : col (j0, v3) ≠ col (jB, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0B v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- the jB Hamilton path from v3* to t₁, split inclusively at v2
  obtain ⟨H, hH⟩ := hlace jB v3s (t 1).2 (by
    show col (jB, v3s) ≠ col (jB, (t 1).2)
    rw [hcv3s, hcT1]
    cases b <;> simp)
  have hv2mem : v2 ∈ H.support := hH.mem_support v2
  have hne_s1v3 : (s 1).2 ≠ v3 := by
    intro h
    have hnd := hA1.support_nodup
    rw [hA1supp, List.nodup_cons] at hnd
    exact hnd.1 (h ▸ A1'.start_mem_support)
  have hne_v2v3s : v2 ≠ v3s := by
    rw [hv2def, hv3sdef]
    intro h
    exact hne_s1v3 ((M j0 jB).injective h)
  have hsuppH : H.support = (H.takeUntil v2 hv2mem).support
      ++ (H.dropUntil v2 hv2mem).support.tail := by
    conv_lhs => rw [← H.take_spec hv2mem]
    rw [SimpleGraph.Walk.support_append]
  have htakeH : (H.takeUntil v2 hv2mem).IsPath := hH.isPath.takeUntil hv2mem
  have hdropH : (H.dropUntil v2 hv2mem).IsPath := hH.isPath.dropUntil hv2mem
  obtain ⟨u3, C', hC', hadju3, htakesupp, hv2C'⟩ :=
    path_peel_last (H.takeUntil v2 hv2mem) htakeH hne_v2v3s
  have hcu3 : col (jB, u3) = b := by
    have h : col (jB, u3) ≠ col (jB, v2) :=
      hproper _ _ ((weldLift Gs M jB).map_adj hadju3)
    rw [hcv2] at h
    exact bool_eq_of_ne_not3 h
  -- the jC Hamilton path to the pulled-back cut end
  obtain ⟨u3s, hu3sdef⟩ : ∃ x, x = M jB jC u3 := ⟨_, rfl⟩
  have hcu3s : col (jC, u3s) = !b := by
    have h : col (jB, u3) ≠ col (jC, u3s) :=
      hu3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hjBC u3)
    rw [hcu3] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨q, hq⟩ := hlace jC (s 2).2 u3s (by
    show col (jC, (s 2).2) ≠ col (jC, u3s)
    rw [hcS2, hcu3s]
    cases b <;> simp)
  -- pair 0
  have hP0 : ∃ P : (weldGraph ell Gs M).Walk (s 0) (t 0), P.IsPath ∧
      P.support = A0.support.map (fun w => (j0, w)) := by
    refine ⟨(A0.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl)
      (Prod.ext ht0.symm rfl), ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨P0w, hP0p, hP0s⟩ := hP0
  -- pair 1: s₁ then the jB suffix
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (jB, v2) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) hj0B (s 1).2
    rw [← hv2def] at h
    rwa [show ((j0 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hP1 : ∃ P : (weldGraph ell Gs M).Walk (s 1) (t 1), P.IsPath ∧
      P.support = s 1 :: (H.dropUntil v2 hv2mem).support.map (fun w => (jB, w)) := by
    have hDl : ∃ Q : (weldGraph ell Gs M).Walk (jB, v2) (t 1), Q.IsPath ∧
        Q.support = (H.dropUntil v2 hv2mem).support.map (fun w => (jB, w)) := by
      refine ⟨((H.dropUntil v2 hv2mem).map (weldLift Gs M jB)).copy rfl
        (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hdropH
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hDl
    refine ⟨SimpleGraph.Walk.cons hadj1a Q, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQp, ?_⟩
      intro hmem
      rw [hQs, mem_map_pair] at hmem
      exact hj0B (hs1.symm.trans hmem.1)
    · rw [SimpleGraph.Walk.support_cons, hQs]
  obtain ⟨P1w, hP1p, hP1s⟩ := hP1
  -- pair 2: the jC Hamilton path, the reversed cut prefix, the freed j0 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (jC, u3s), R.IsPath ∧
      R.support = q.support.map (fun w => (jC, w)) := by
    refine ⟨(q.map (weldLift Gs M jC)).copy (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq.isPath
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20 C'.reverse hR20p hC'.reverse
    ((hu3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hjBC u3).symm)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hjBC hmem.1)
  obtain ⟨R22, hR22p, hR22s⟩ := weld_splice_snoc R21 A1' hR21p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hj0B v3).symm)
    (by
      intro w' _ hmem
      rw [hR21s, List.mem_append, hR20s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj0C h1
      · exact hj0B h1)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ x.1 = j0 ∧ x.2 ∈ A0.support) ∨
          (i = 1 ∧ (x = s 1 ∨
            (x.1 = jB ∧ x.2 ∈ (H.dropUntil v2 hv2mem).support))) ∨
          (i = 2 ∧ ((x.1 = jC ∧ x.2 ∈ q.support) ∨ (x.1 = jB ∧ x.2 ∈ C'.support) ∨
            (x.1 = j0 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨P0w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP0p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hP0s, mem_map_pair]
        constructor
        · rintro ⟨h1, h2⟩
          exact Or.inl ⟨rfl, h1, h2⟩
        · rintro (⟨-, h1, h2⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨P1w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP1p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hP1s]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
          · rw [mem_map_pair] at h
            exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
        · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩⟩ | ⟨h0, -⟩)
          · exact absurd h0 (by decide)
          · exact h ▸ List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ ?_
            rw [mem_map_pair]
            exact ⟨h1, h2⟩
          · exact absurd h0 (by decide)
    · refine ⟨R22.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR22p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR22s, List.mem_append, hR21s,
          List.mem_append, hR20s, mem_map_pair, mem_map_pair, mem_map_pair,
          SimpleGraph.Walk.support_reverse]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
              ⟨h1, List.mem_reverse.mp h2⟩)⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, List.mem_reverse.mpr h2⟩)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j0, jB, jC} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, h1, -⟩ |
      ⟨-, h | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, rfl, h⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr
            ⟨rfl, h2⟩)⟩))⟩
    · have h := hH.mem_support xw
      rw [hsuppH] at h
      rcases List.mem_append.mp h with h | h
      · rw [htakesupp] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
            ⟨rfl, h2⟩)⟩))⟩
        · rw [List.mem_singleton] at h2
          refine ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr
            ⟨rfl, ?_⟩⟩))⟩
          rw [h2]
          exact (H.dropUntil v2 hv2mem).start_mem_support
      · refine ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr
          ⟨rfl, List.mem_of_mem_tail h⟩⟩))⟩
    · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
        ⟨rfl, hq.mem_support xw⟩⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hdisjH : ∀ w, w ∈ C'.support → w ∈ (H.dropUntil v2 hv2mem).support → False := by
      intro w hw hw2
      have hnd := hH.isPath.support_nodup
      rw [hsuppH, htakesupp] at hnd
      rcases List.mem_cons.mp ((SimpleGraph.Walk.cons_tail_support
        (H.dropUntil v2 hv2mem)) ▸ hw2 : w ∈ v2 :: (H.dropUntil v2 hv2mem).support.tail)
        with h3 | h3
      · exact hv2C' (h3 ▸ hw)
      · have := (List.nodup_append.mp hnd).2.2 w
          (List.mem_append_left _ hw) w h3 rfl
        exact this
    have hd01 : ∀ (y : Fin ell × W), (y.1 = j0 ∧ y.2 ∈ A0.support) →
        (y = s 1 ∨ (y.1 = jB ∧ y.2 ∈ (H.dropUntil v2 hv2mem).support)) → False := by
      rintro y ⟨hy1, hy2⟩ (h | ⟨hz1, -⟩)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj0B (hy1.symm.trans hz1)
    have hd02 : ∀ (y : Fin ell × W), (y.1 = j0 ∧ y.2 ∈ A0.support) →
        ((y.1 = jC ∧ y.2 ∈ q.support) ∨ (y.1 = jB ∧ y.2 ∈ C'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y ⟨hy1, hy2⟩ (⟨hz1, -⟩ | ⟨hz1, -⟩ | ⟨-, hz2⟩)
      · exact hj0C (hy1.symm.trans hz1)
      · exact hj0B (hy1.symm.trans hz1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = jB ∧ y.2 ∈ (H.dropUntil v2 hv2mem).support)) →
        ((y.1 = jC ∧ y.2 ∈ q.support) ∨ (y.1 = jB ∧ y.2 ∈ C'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, hz2⟩) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have h1 : (s 1).1 = jC := (congrArg Prod.fst h).symm.trans hw1
        exact hj0C (hs1.symm.trans h1)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hj0B (hs1.symm.trans h1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hjBC (hz1.symm.trans hw1)
      · exact hdisjH y.2 hw2 hz2
      · exact hj0B (hw1.symm.trans hz1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq'⟩ | ⟨hj1', hq'⟩ | ⟨hj2', hq'⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq'
    · exact hd02 x hp hq'
    · exact hd01 x hq' hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq'
    · exact hd02 x hq' hp
    · exact hd12 x hq' hp
    · exact hij (hi2.trans hj2'.symm)

end SmallCase512

section SmallCase521

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 5.2a: `{s₀, s₁, t₂} ⊆ j0`, `s₂` and `t₀` share `jB`, `t₁ ∈ jC`. -/
private theorem small_case5_21
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 jB jC : Fin ell} (hj0B : j0 ≠ jB) (hj0C : j0 ≠ jC) (hjBC : jB ≠ jC)
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0)
    (hs2 : (s 2).1 = jB) (ht0 : (t 0).1 = jB) (ht1 : (t 1).1 = jC) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  obtain ⟨j4, hj40, hj4B, hj4C⟩ := fin_exists_one_avoid3 hell4 j0 jB jC
  have hcS : ∀ i, (s i).1 = j0 → col (j0, (s i).2) = b := fun i hi => by
    rw [show ((j0 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcT2 : col (j0, (t 2).2) = !b := by
    rw [show ((j0 : Fin ell), (t 2).2) = t 2 from Prod.ext ht2.symm rfl]
    exact hmono.2.1 2
  have hcS2 : col (jB, (s 2).2) = b := by
    rw [show ((jB : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT0 : col (jB, (t 0).2) = !b := by
    rw [show ((jB : Fin ell), (t 0).2) = t 0 from Prod.ext ht0.symm rfl]
    exact hmono.2.1 0
  have hcT1 : col (jC, (t 1).2) = !b := by
    rw [show ((jC : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  -- the fresh white connector in j0
  obtain ⟨v1, hv1c, hv1a⟩ := exists_avoid_of_class hclass j0 (!b)
    ({(t 2).2} ∪ {(M j0 jB).symm (s 2).2}) (by
      refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
      simp)
  obtain ⟨u1, hu1def⟩ : ∃ x, x = M j0 jB v1 := ⟨_, rfl⟩
  have hcu1 : col (jB, u1) = b := by
    have h : col (j0, v1) ≠ col (jB, u1) :=
      hu1def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0B v1)
    rw [hv1c] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  have hu1s2 : u1 ≠ (s 2).2 := by
    intro h
    apply hv1a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    refine Or.inr ?_
    rw [← h, hu1def, Equiv.symm_apply_apply]
  have hv1t2 : v1 ≠ (t 2).2 := by
    intro h
    apply hv1a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    exact Or.inl h
  -- the j0 2-cover
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hst00 : ∀ i k, (s i).1 = j0 → (t k).1 = j0 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j0
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := v1) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hv1c]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT2]; cases b <;> simp)
    hne_s0s1 hv1t2
    (by
      intro h
      have h1 := hcS 0 hs0
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 0 2 hs0 ht2)
    (by
      intro h
      have h1 := hcS 1 hs1
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 1 2 hs1 ht2)
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1
    (hst00 1 2 hs1 ht2)
  have hcv3 : col (j0, v3) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j0, v3) :=
      hproper _ _ ((weldLift Gs M j0).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j0 jC v3 := ⟨_, rfl⟩
  have hcv3s : col (jC, v3s) = b := by
    have h : col (j0, v3) ≠ col (jC, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0C v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- the black connector in jC
  obtain ⟨u3, hu3c, hu3a⟩ := exists_avoid_of_class hclass jC b
    ({v3s} ∪ {(M jC jB).symm (t 0).2}) (by
      refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
      simp)
  obtain ⟨u3s, hu3sdef⟩ : ∃ x, x = M jC jB u3 := ⟨_, rfl⟩
  have hcu3s : col (jB, u3s) = !b := by
    have h : col (jC, u3) ≠ col (jB, u3s) :=
      hu3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjBC) u3)
    rw [hu3c] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  have hu3v3s : u3 ≠ v3s := by
    intro h
    apply hu3a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    exact Or.inl h
  have hu3st0 : u3s ≠ (t 0).2 := by
    intro h
    apply hu3a
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
    refine Or.inr ?_
    rw [← h, hu3sdef, Equiv.symm_apply_apply]
  -- the jB 2-cover
  obtain ⟨B0, B1, hB0, hB1, hBcov, hBdis⟩ := small_pdpc2 hcov2 jB
    (a0 := u1) (a1 := (s 2).2) (b0 := (t 0).2) (b1 := u3s)
    (by rw [hcu1, hcT0]; cases b <;> simp)
    (by rw [hcS2, hcu3s]; cases b <;> simp)
    hu1s2 (Ne.symm hu3st0)
    (by
      intro h
      have h1 := hcu1
      rw [h, hcT0] at h1
      cases b <;> simp at h1)
    (by
      intro h
      have h1 := hcu1
      rw [h, hcu3s] at h1
      cases b <;> simp at h1)
    (fun h => hmono.st_ne 2 0 (Prod.ext (hs2.trans ht0.symm) h))
    (by
      intro h
      have h1 := hcS2
      rw [h, hcu3s] at h1
      cases b <;> simp at h1)
  -- the jC Hamilton path, split inclusively at u3
  obtain ⟨H, hH⟩ := hlace jC v3s (t 1).2 (by
    show col (jC, v3s) ≠ col (jC, (t 1).2)
    rw [hcv3s, hcT1]
    cases b <;> simp)
  have hu3mem : u3 ∈ H.support := hH.mem_support u3
  have hne_u3t1 : u3 ≠ (t 1).2 := by
    intro h
    have h1 := hu3c
    rw [h, hcT1] at h1
    cases b <;> simp at h1
  have hsuppH : H.support = (H.takeUntil u3 hu3mem).support
      ++ (H.dropUntil u3 hu3mem).support.tail := by
    conv_lhs => rw [← H.take_spec hu3mem]
    rw [SimpleGraph.Walk.support_append]
  have htakeH : (H.takeUntil u3 hu3mem).IsPath := hH.isPath.takeUntil hu3mem
  have hdropH : (H.dropUntil u3 hu3mem).IsPath := hH.isPath.dropUntil hu3mem
  obtain ⟨v2, D, hD, hadjv2, hdropsupp, hu3D⟩ :=
    path_peel_head (H.dropUntil u3 hu3mem) hdropH hne_u3t1
  have hcv2 : col (jC, v2) = !b := by
    have h : col (jC, u3) ≠ col (jC, v2) :=
      hproper _ _ ((weldLift Gs M jC).map_adj hadjv2)
    rw [hu3c] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  -- the j4 bridge
  obtain ⟨u2s, hu2sdef⟩ : ∃ x, x = M j0 j4 (s 1).2 := ⟨_, rfl⟩
  have hcu2s : col (j4, u2s) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j4, u2s) :=
      hu2sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj40) (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v2s, hv2sdef⟩ : ∃ x, x = M jC j4 v2 := ⟨_, rfl⟩
  have hcv2s : col (j4, v2s) = b := by
    have h : col (jC, v2) ≠ col (j4, v2s) :=
      hv2sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj4C) v2)
    rw [hcv2] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  obtain ⟨q4, hq4⟩ := hlace j4 u2s v2s (by
    show col (j4, u2s) ≠ col (j4, v2s)
    rw [hcu2s, hcv2s]
    cases b <;> simp)
  -- pair 0: the j0 leg, cross, the jB leg
  have hR00 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, v1), R.IsPath ∧
      R.support = A0.support.map (fun w => (j0, w)) := by
    refine ⟨(A0.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R00, hR00p, hR00s⟩ := hR00
  obtain ⟨R01, hR01p, hR01s⟩ := weld_splice_snoc R00 B0 hR00p hB0
    (hu1def ▸ weld_cross_adj (Gs := Gs) (M := M) hj0B v1)
    (by
      intro w' _ hmem
      rw [hR00s, mem_map_pair] at hmem
      exact hj0B hmem.1.symm)
  -- pair 1: s₁, the j4 bridge, the freed jC suffix
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (j4, u2s) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj40) (s 1).2
    rw [← hu2sdef] at h
    rwa [show ((j0 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hR10 : ∃ R : (weldGraph ell Gs M).Walk (s 1) (j4, v2s), R.IsPath ∧
      R.support = s 1 :: q4.support.map (fun w => (j4, w)) := by
    have hql : ∃ Q : (weldGraph ell Gs M).Walk (j4, u2s) (j4, v2s), Q.IsPath ∧
        Q.support = q4.support.map (fun w => (j4, w)) := by
      refine ⟨(q4.map (weldLift Gs M j4)).copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq4.isPath
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hql
    refine ⟨SimpleGraph.Walk.cons hadj1a Q, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQp, ?_⟩
      intro hmem
      rw [hQs, mem_map_pair] at hmem
      exact hj40 (hmem.1.symm.trans hs1)
    · rw [SimpleGraph.Walk.support_cons, hQs]
  obtain ⟨R10, hR10p, hR10s⟩ := hR10
  obtain ⟨R11, hR11p, hR11s⟩ := weld_splice_snoc R10 D hR10p hD
    ((hv2sdef ▸ weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj4C) v2).symm)
    (by
      intro w' _ hmem
      rw [hR10s] at hmem
      rcases List.mem_cons.mp hmem with h | h
      · have h1 : jC = j0 := (congrArg Prod.fst h).trans hs1
        exact hj0C h1.symm
      · rw [mem_map_pair] at h
        exact hj4C h.1.symm)
  -- pair 2: the jB leg, back through u3, the reversed jC prefix, the j0 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (jB, u3s), R.IsPath ∧
      R.support = B1.support.map (fun w => (jB, w)) := by
    refine ⟨(B1.map (weldLift Gs M jB)).copy (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hB1
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20
    (H.takeUntil u3 hu3mem).reverse hR20p htakeH.reverse
    ((hu3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hjBC.symm u3).symm)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hjBC hmem.1.symm)
  obtain ⟨R22, hR22p, hR22s⟩ := weld_splice_snoc R21 A1' hR21p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hj0C v3).symm)
    (by
      intro w' _ hmem
      rw [hR21s, List.mem_append, hR20s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj0B h1
      · exact hj0C h1)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ ((x.1 = j0 ∧ x.2 ∈ A0.support) ∨ (x.1 = jB ∧ x.2 ∈ B0.support))) ∨
          (i = 1 ∧ (x = s 1 ∨ (x.1 = j4 ∧ x.2 ∈ q4.support) ∨
            (x.1 = jC ∧ x.2 ∈ D.support))) ∨
          (i = 2 ∧ ((x.1 = jB ∧ x.2 ∈ B1.support) ∨
            (x.1 = jC ∧ x.2 ∈ (H.takeUntil u3 hu3mem).support) ∨
            (x.1 = j0 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨R01.copy rfl (Prod.ext ht0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR01p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR01s, List.mem_append, hR00s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨rfl, Or.inl ⟨h1, h2⟩⟩
          · exact Or.inl ⟨rfl, Or.inr ⟨h1, h2⟩⟩
        · rintro (⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨R11.copy rfl (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR11p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR11s, List.mem_append, hR10s, mem_map_pair]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · rcases List.mem_cons.mp h with h2 | h2
            · exact Or.inr (Or.inl ⟨rfl, Or.inl h2⟩)
            · rw [mem_map_pair] at h2
              exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h2)⟩)
          · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩)
          · exact absurd h0 (by decide)
          · exact Or.inl (h ▸ List.mem_cons_self ..)
          · refine Or.inl (List.mem_cons_of_mem _ ?_)
            rw [mem_map_pair]
            exact ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
    · refine ⟨R22.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR22p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR22s, List.mem_append, hR21s,
          List.mem_append, hR20s, mem_map_pair, mem_map_pair, mem_map_pair,
          SimpleGraph.Walk.support_reverse]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
              ⟨h1, List.mem_reverse.mp h2⟩)⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, List.mem_reverse.mpr h2⟩)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j0, jB, jC, j4} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
      ⟨-, h | ⟨h1, -⟩ | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr
            ⟨rfl, h2⟩)⟩))⟩
    · rcases hBcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
      · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
          ⟨rfl, h⟩⟩))⟩
    · have h := hH.mem_support xw
      rw [hsuppH] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
          ⟨rfl, h⟩)⟩))⟩
      · rw [hdropsupp] at h
        exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr
          ⟨rfl, h⟩)⟩))⟩
    · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl
        ⟨rfl, hq4.mem_support xw⟩)⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hdisjH : ∀ w, w ∈ (H.takeUntil u3 hu3mem).support → w ∈ D.support → False := by
      intro w hw hw2
      have hnd := hH.isPath.support_nodup
      rw [hsuppH, hdropsupp] at hnd
      exact (List.nodup_append.mp hnd).2.2 w hw w hw2 rfl
    have hd01 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jB ∧ y.2 ∈ B0.support)) →
        (y = s 1 ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨ (y.1 = jC ∧ y.2 ∈ D.support)) →
        False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (h | ⟨hz1, -⟩ | ⟨hz1, -⟩)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj40 (hz1.symm.trans hy1)
      · exact hj0C (hy1.symm.trans hz1)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hy1
        exact hj0B (hs1.symm.trans h1)
      · exact hj4B (hz1.symm.trans hy1)
      · exact hjBC (hy1.symm.trans hz1)
    have hd02 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jB ∧ y.2 ∈ B0.support)) →
        ((y.1 = jB ∧ y.2 ∈ B1.support) ∨
          (y.1 = jC ∧ y.2 ∈ (H.takeUntil u3 hu3mem).support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (⟨hz1, hz2⟩ | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩)
      · exact hj0B (hy1.symm.trans hz1)
      · exact hj0C (hy1.symm.trans hz1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
      · exact hBdis y.2 hy2 hz2
      · exact hjBC (hy1.symm.trans hz1)
      · exact hj0B (hz1.symm.trans hy1)
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨ (y.1 = jC ∧ y.2 ∈ D.support)) →
        ((y.1 = jB ∧ y.2 ∈ B1.support) ∨
          (y.1 = jC ∧ y.2 ∈ (H.takeUntil u3 hu3mem).support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hj0B (hs1.symm.trans h1)
      · have h1 : (s 1).1 = jC := (congrArg Prod.fst h).symm.trans hw1
        exact hj0C (hs1.symm.trans h1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hj4B (hz1.symm.trans hw1)
      · exact hj4C (hz1.symm.trans hw1)
      · exact hj40 (hz1.symm.trans hw1)
      · exact hjBC (hw1.symm.trans hz1)
      · exact hdisjH y.2 hw2 hz2
      · exact hj0C (hw1.symm.trans hz1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq'⟩ | ⟨hj1', hq'⟩ | ⟨hj2', hq'⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq'
    · exact hd02 x hp hq'
    · exact hd01 x hq' hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq'
    · exact hd02 x hq' hp
    · exact hd12 x hq' hp
    · exact hij (hi2.trans hj2'.symm)

end SmallCase521

section SmallCase522

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 5.2b: `{s₀, s₁, t₂} ⊆ j0`, `s₂ ∈ jB`, `{t₀, t₁} ⊆ jC`. -/
private theorem small_case5_22
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 jB jC : Fin ell} (hj0B : j0 ≠ jB) (hj0C : j0 ≠ jC) (hjBC : jB ≠ jC)
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0)
    (hs2 : (s 2).1 = jB) (ht0 : (t 0).1 = jC) (ht1 : (t 1).1 = jC) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  obtain ⟨j4, hj40, hj4B, hj4C⟩ := fin_exists_one_avoid3 hell4 j0 jB jC
  have hcS : ∀ i, (s i).1 = j0 → col (j0, (s i).2) = b := fun i hi => by
    rw [show ((j0 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcT2 : col (j0, (t 2).2) = !b := by
    rw [show ((j0 : Fin ell), (t 2).2) = t 2 from Prod.ext ht2.symm rfl]
    exact hmono.2.1 2
  have hcS2 : col (jB, (s 2).2) = b := by
    rw [show ((jB : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT0 : col (jC, (t 0).2) = !b := by
    rw [show ((jC : Fin ell), (t 0).2) = t 0 from Prod.ext ht0.symm rfl]
    exact hmono.2.1 0
  have hcT1 : col (jC, (t 1).2) = !b := by
    rw [show ((jC : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  -- the fresh white connector in j0 (avoid only t₂)
  obtain ⟨v1, hv1c, hv1a⟩ := exists_avoid_of_class hclass j0 (!b) {(t 2).2} (by simp)
  obtain ⟨u1, hu1def⟩ : ∃ x, x = M j0 jC v1 := ⟨_, rfl⟩
  have hcu1 : col (jC, u1) = b := by
    have h : col (j0, v1) ≠ col (jC, u1) :=
      hu1def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0C v1)
    rw [hv1c] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  have hv1t2 : v1 ≠ (t 2).2 := by
    intro h
    exact hv1a (h ▸ Finset.mem_singleton_self _)
  -- the j0 2-cover
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hst00 : ∀ i k, (s i).1 = j0 → (t k).1 = j0 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j0
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := v1) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hv1c]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT2]; cases b <;> simp)
    hne_s0s1 hv1t2
    (by
      intro h
      have h1 := hcS 0 hs0
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 0 2 hs0 ht2)
    (by
      intro h
      have h1 := hcS 1 hs1
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 1 2 hs1 ht2)
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1
    (hst00 1 2 hs1 ht2)
  have hcv3 : col (j0, v3) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j0, v3) :=
      hproper _ _ ((weldLift Gs M j0).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j0 jC v3 := ⟨_, rfl⟩
  have hcv3s : col (jC, v3s) = b := by
    have h : col (j0, v3) ≠ col (jC, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0C v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- the jC 2-cover
  have hne_u1v3s : u1 ≠ v3s := by
    rw [hu1def, hv3sdef]
    intro h
    have h2 := (M j0 jC).injective h
    have hnd := hA1.support_nodup
    rw [hA1supp, List.nodup_cons] at hnd
    have hv3A1' : v3 ∈ A1'.support := A1'.start_mem_support
    have hv1A0 : v1 ∈ A0.support := A0.end_mem_support
    refine hAdis v1 hv1A0 ?_
    rw [hA1supp, h2]
    exact List.mem_cons_of_mem _ hv3A1'
  have hne_t0t1 : (t 0).2 ≠ (t 1).2 := by
    intro h
    have := hmono.2.2.2 (a₁ := 0) (a₂ := 1) (Prod.ext (ht0.trans ht1.symm) h)
    exact absurd this (by decide)
  obtain ⟨C0, C1, hC0, hC1, hCcov, hCdis⟩ := small_pdpc2 hcov2 jC
    (a0 := u1) (a1 := v3s) (b0 := (t 0).2) (b1 := (t 1).2)
    (by rw [hcu1, hcT0]; cases b <;> simp)
    (by rw [hcv3s, hcT1]; cases b <;> simp)
    hne_u1v3s hne_t0t1
    (by
      intro h
      have h1 := hcu1
      rw [h, hcT0] at h1
      cases b <;> simp at h1)
    (by
      intro h
      have h1 := hcu1
      rw [h, hcT1] at h1
      cases b <;> simp at h1)
    (by
      intro h
      have h1 := hcv3s
      rw [h, hcT0] at h1
      cases b <;> simp at h1)
    (by
      intro h
      have h1 := hcv3s
      rw [h, hcT1] at h1
      cases b <;> simp at h1)
  -- peel the end of the second jC leg (frees t₁)
  have hne_v3st1 : v3s ≠ (t 1).2 := by
    intro h
    have h1 := hcv3s
    rw [h, hcT1] at h1
    cases b <;> simp at h1
  obtain ⟨u3, C1', hC1', hadju3, hC1supp, ht1C1'⟩ := path_peel_last C1 hC1
    (Ne.symm hne_v3st1)
  have hcu3 : col (jC, u3) = b := by
    have h : col (jC, u3) ≠ col (jC, (t 1).2) :=
      hproper _ _ ((weldLift Gs M jC).map_adj hadju3)
    rw [hcT1] at h
    exact bool_eq_of_ne_not3 h
  -- the jB Hamilton path
  obtain ⟨u3s, hu3sdef⟩ : ∃ x, x = M jC jB u3 := ⟨_, rfl⟩
  have hcu3s : col (jB, u3s) = !b := by
    have h : col (jC, u3) ≠ col (jB, u3s) :=
      hu3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjBC) u3)
    rw [hcu3] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨HB, hHB⟩ := hlace jB (s 2).2 u3s (by
    show col (jB, (s 2).2) ≠ col (jB, u3s)
    rw [hcS2, hcu3s]
    cases b <;> simp)
  -- the j4 bridge for pair 1
  obtain ⟨v2, hv2def⟩ : ∃ x, x = M j0 j4 (s 1).2 := ⟨_, rfl⟩
  have hcv2 : col (j4, v2) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j4, v2) :=
      hv2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj40) (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨u2, hu2def⟩ : ∃ x, x = M jC j4 (t 1).2 := ⟨_, rfl⟩
  have hcu2 : col (j4, u2) = b := by
    have h : col (jC, (t 1).2) ≠ col (j4, u2) :=
      hu2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj4C) (t 1).2)
    rw [hcT1] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  obtain ⟨q4, hq4⟩ := hlace j4 v2 u2 (by
    show col (j4, v2) ≠ col (j4, u2)
    rw [hcv2, hcu2]
    cases b <;> simp)
  -- pair 0: j0 leg, cross, jC leg
  have hR00 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, v1), R.IsPath ∧
      R.support = A0.support.map (fun w => (j0, w)) := by
    refine ⟨(A0.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R00, hR00p, hR00s⟩ := hR00
  obtain ⟨R01, hR01p, hR01s⟩ := weld_splice_snoc R00 C0 hR00p hC0
    (hu1def ▸ weld_cross_adj (Gs := Gs) (M := M) hj0C v1)
    (by
      intro w' _ hmem
      rw [hR00s, mem_map_pair] at hmem
      exact hj0C hmem.1.symm)
  -- pair 1: s₁, the j4 bridge, the freed edge to t₁
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (j4, v2) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj40) (s 1).2
    rw [← hv2def] at h
    rwa [show ((j0 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hadj1b : (weldGraph ell Gs M).Adj (j4, u2) (t 1) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj4C) (t 1).2
    rw [← hu2def] at h
    rw [show ((jC : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl] at h
    exact h.symm
  have hP1 : ∃ P : (weldGraph ell Gs M).Walk (s 1) (t 1), P.IsPath ∧
      P.support = s 1 :: (q4.support.map (fun w => (j4, w)) ++ [t 1]) := by
    have hql : ∃ Q : (weldGraph ell Gs M).Walk (j4, v2) (j4, u2), Q.IsPath ∧
        Q.support = q4.support.map (fun w => (j4, w)) := by
      refine ⟨(q4.map (weldLift Gs M j4)).copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq4.isPath
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hql
    have hQ' : ∃ Q' : (weldGraph ell Gs M).Walk (j4, v2) (t 1), Q'.IsPath ∧
        Q'.support = q4.support.map (fun w => (j4, w)) ++ [t 1] := by
      refine ⟨Q.concat hadj1b, ?_, ?_⟩
      · rw [SimpleGraph.Walk.concat_isPath_iff]
        refine ⟨hQp, ?_⟩
        intro hmem
        rw [hQs, mem_map_pair] at hmem
        exact hj4C (hmem.1.symm.trans ht1)
      · rw [SimpleGraph.Walk.support_concat, hQs]
    obtain ⟨Q', hQ'p, hQ's⟩ := hQ'
    refine ⟨SimpleGraph.Walk.cons hadj1a Q', ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQ'p, ?_⟩
      intro hmem
      rw [hQ's, List.mem_append, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | h1
      · exact hj40 (h1.symm.trans hs1)
      · rw [List.mem_singleton] at h1
        exact hmono.st_ne 1 1 h1
    · rw [SimpleGraph.Walk.support_cons, hQ's]
  obtain ⟨P1w, hP1p, hP1s⟩ := hP1
  -- pair 2: the jB Hamilton path, back through u3, the reversed jC leg, the j0 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (jB, u3s), R.IsPath ∧
      R.support = HB.support.map (fun w => (jB, w)) := by
    refine ⟨(HB.map (weldLift Gs M jB)).copy (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hHB.isPath
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20 C1'.reverse hR20p hC1'.reverse
    ((hu3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hjBC.symm u3).symm)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hjBC hmem.1.symm)
  obtain ⟨R22, hR22p, hR22s⟩ := weld_splice_snoc R21 A1' hR21p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hj0C v3).symm)
    (by
      intro w' _ hmem
      rw [hR21s, List.mem_append, hR20s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj0B h1
      · exact hj0C h1)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ ((x.1 = j0 ∧ x.2 ∈ A0.support) ∨ (x.1 = jC ∧ x.2 ∈ C0.support))) ∨
          (i = 1 ∧ (x = s 1 ∨ (x.1 = j4 ∧ x.2 ∈ q4.support) ∨ x = t 1)) ∨
          (i = 2 ∧ ((x.1 = jB ∧ x.2 ∈ HB.support) ∨ (x.1 = jC ∧ x.2 ∈ C1'.support) ∨
            (x.1 = j0 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨R01.copy rfl (Prod.ext ht0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR01p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR01s, List.mem_append, hR00s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨rfl, Or.inl ⟨h1, h2⟩⟩
          · exact Or.inl ⟨rfl, Or.inr ⟨h1, h2⟩⟩
        · rintro (⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨P1w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP1p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hP1s]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
          · rcases List.mem_append.mp h with h2 | h2
            · rw [mem_map_pair] at h2
              exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl h2)⟩)
            · rw [List.mem_singleton] at h2
              exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr h2)⟩)
        · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩ | h⟩ | ⟨h0, -⟩)
          · exact absurd h0 (by decide)
          · exact h ▸ List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
            rw [mem_map_pair]
            exact ⟨h1, h2⟩
          · refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
            rw [List.mem_singleton]
            exact h
          · exact absurd h0 (by decide)
    · refine ⟨R22.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR22p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR22s, List.mem_append, hR21s,
          List.mem_append, hR20s, mem_map_pair, mem_map_pair, mem_map_pair,
          SimpleGraph.Walk.support_reverse]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
              ⟨h1, List.mem_reverse.mp h2⟩)⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, List.mem_reverse.mpr h2⟩)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j0, jB, jC, j4} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
      ⟨-, h | ⟨h1, -⟩ | h⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inr (Or.inr h1))
    · rw [h]
      exact Or.inr (Or.inr (Or.inl ht1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr
            ⟨rfl, h2⟩)⟩))⟩
    · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
        ⟨rfl, hHB.mem_support xw⟩⟩))⟩
    · rcases hCcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr ⟨rfl, h⟩⟩)⟩
      · rw [hC1supp] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
            ⟨rfl, h2⟩)⟩))⟩
        · rw [List.mem_singleton] at h2
          exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr
            (Prod.ext ht1.symm h2))⟩))⟩
    · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl
        ⟨rfl, hq4.mem_support xw⟩)⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hd01 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jC ∧ y.2 ∈ C0.support)) →
        (y = s 1 ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨ y = t 1) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (h | ⟨hz1, -⟩ | h)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj40 (hz1.symm.trans hy1)
      · have hy1' : (t 1).1 = j0 := (congrArg Prod.fst h).symm.trans hy1
        exact hj0C (hy1'.symm.trans ht1)
      · have h1 : (s 1).1 = jC := (congrArg Prod.fst h).symm.trans hy1
        exact hj0C (hs1.symm.trans h1)
      · exact hj4C (hz1.symm.trans hy1)
      · refine hCdis y.2 hy2 ?_
        rw [show y.2 = (t 1).2 from congrArg Prod.snd h, hC1supp]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    have hd02 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jC ∧ y.2 ∈ C0.support)) →
        ((y.1 = jB ∧ y.2 ∈ HB.support) ∨ (y.1 = jC ∧ y.2 ∈ C1'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (⟨hz1, hz2⟩ | ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩)
      · exact hj0B (hy1.symm.trans hz1)
      · exact hj0C (hy1.symm.trans hz1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
      · exact hjBC (hz1.symm.trans hy1)
      · refine hCdis y.2 hy2 ?_
        rw [hC1supp]
        exact List.mem_append_left _ hz2
      · exact hj0C (hz1.symm.trans hy1)
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = j4 ∧ y.2 ∈ q4.support) ∨ y = t 1) →
        ((y.1 = jB ∧ y.2 ∈ HB.support) ∨ (y.1 = jC ∧ y.2 ∈ C1'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, hz2⟩ | h) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hj0B (hs1.symm.trans h1)
      · have h1 : (s 1).1 = jC := (congrArg Prod.fst h).symm.trans hw1
        exact hj0C (hs1.symm.trans h1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hj4B (hz1.symm.trans hw1)
      · exact hj4C (hz1.symm.trans hw1)
      · exact hj40 (hz1.symm.trans hw1)
      · have h1 : (t 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hjBC (h1.symm.trans ht1)
      · refine ht1C1' ?_
        rw [← show y.2 = (t 1).2 from congrArg Prod.snd h]
        exact hw2
      · have h1 : (t 1).1 = j0 := (congrArg Prod.fst h).symm.trans hw1
        exact hj0C (h1.symm.trans ht1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq'⟩ | ⟨hj1', hq'⟩ | ⟨hj2', hq'⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq'
    · exact hd02 x hp hq'
    · exact hd01 x hq' hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq'
    · exact hd02 x hq' hp
    · exact hd12 x hq' hp
    · exact hij (hi2.trans hj2'.symm)

end SmallCase522

section SmallCase523

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- (c)-Case 5.2c: `{s₀, s₁, t₂} ⊆ j0`, `s₂ ∈ jB`, `t₀ ∈ jC`, `t₁ ∈ jD`, all distinct. -/
private theorem small_case5_23
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    {b : Bool} {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 jB jC jD : Fin ell} (hj0B : j0 ≠ jB) (hj0C : j0 ≠ jC) (hj0D : j0 ≠ jD)
    (hjBC : jB ≠ jC) (hjBD : jB ≠ jD) (hjCD : jC ≠ jD)
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0)
    (hs2 : (s 2).1 = jB) (ht0 : (t 0).1 = jC) (ht1 : (t 1).1 = jD) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  have hcS : ∀ i, (s i).1 = j0 → col (j0, (s i).2) = b := fun i hi => by
    rw [show ((j0 : Fin ell), (s i).2) = s i from Prod.ext hi.symm rfl]
    exact hmono.1 i
  have hcT2 : col (j0, (t 2).2) = !b := by
    rw [show ((j0 : Fin ell), (t 2).2) = t 2 from Prod.ext ht2.symm rfl]
    exact hmono.2.1 2
  have hcS2 : col (jB, (s 2).2) = b := by
    rw [show ((jB : Fin ell), (s 2).2) = s 2 from Prod.ext hs2.symm rfl]
    exact hmono.1 2
  have hcT0 : col (jC, (t 0).2) = !b := by
    rw [show ((jC : Fin ell), (t 0).2) = t 0 from Prod.ext ht0.symm rfl]
    exact hmono.2.1 0
  have hcT1 : col (jD, (t 1).2) = !b := by
    rw [show ((jD : Fin ell), (t 1).2) = t 1 from Prod.ext ht1.symm rfl]
    exact hmono.2.1 1
  obtain ⟨v1, hv1c, hv1a⟩ := exists_avoid_of_class hclass j0 (!b) {(t 2).2} (by simp)
  obtain ⟨u1, hu1def⟩ : ∃ x, x = M j0 jC v1 := ⟨_, rfl⟩
  have hcu1 : col (jC, u1) = b := by
    have h : col (j0, v1) ≠ col (jC, u1) :=
      hu1def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0C v1)
    rw [hv1c] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  have hv1t2 : v1 ≠ (t 2).2 := by
    intro h
    exact hv1a (h ▸ Finset.mem_singleton_self _)
  have hne_s0s1 : (s 0).2 ≠ (s 1).2 := by
    intro h
    have := hmono.2.2.1 (a₁ := 0) (a₂ := 1) (Prod.ext (hs0.trans hs1.symm) h)
    exact absurd this (by decide)
  have hst00 : ∀ i k, (s i).1 = j0 → (t k).1 = j0 → (s i).2 ≠ (t k).2 :=
    fun i k hi hk h => hmono.st_ne i k (Prod.ext (hi.trans hk.symm) h)
  obtain ⟨A0, A1, hA0, hA1, hAcov, hAdis⟩ := small_pdpc2 hcov2 j0
    (a0 := (s 0).2) (a1 := (s 1).2) (b0 := v1) (b1 := (t 2).2)
    (by rw [hcS 0 hs0, hv1c]; cases b <;> simp)
    (by rw [hcS 1 hs1, hcT2]; cases b <;> simp)
    hne_s0s1 hv1t2
    (by
      intro h
      have h1 := hcS 0 hs0
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 0 2 hs0 ht2)
    (by
      intro h
      have h1 := hcS 1 hs1
      rw [h, hv1c] at h1
      cases b <;> simp at h1)
    (hst00 1 2 hs1 ht2)
  obtain ⟨v3, A1', hA1', hadjv3, hA1supp, hs1A1'⟩ := path_peel_head A1 hA1
    (hst00 1 2 hs1 ht2)
  have hcv3 : col (j0, v3) = !b := by
    have h : col (j0, (s 1).2) ≠ col (j0, v3) :=
      hproper _ _ ((weldLift Gs M j0).map_adj hadjv3)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  -- connector images in jD
  obtain ⟨v2, hv2def⟩ : ∃ x, x = M j0 jD (s 1).2 := ⟨_, rfl⟩
  have hcv2 : col (jD, v2) = !b := by
    have h : col (j0, (s 1).2) ≠ col (jD, v2) :=
      hv2def ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0D (s 1).2)
    rw [hcS 1 hs1] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨v3s, hv3sdef⟩ : ∃ x, x = M j0 jD v3 := ⟨_, rfl⟩
  have hcv3s : col (jD, v3s) = b := by
    have h : col (j0, v3) ≠ col (jD, v3s) :=
      hv3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj0D v3)
    rw [hcv3] at h
    exact bool_eq_of_ne_not3 (Ne.symm h)
  -- the jD Hamilton path split inclusively at v2
  obtain ⟨H, hH⟩ := hlace jD v3s (t 1).2 (by
    show col (jD, v3s) ≠ col (jD, (t 1).2)
    rw [hcv3s, hcT1]
    cases b <;> simp)
  have hv2mem : v2 ∈ H.support := hH.mem_support v2
  have hne_s1v3 : (s 1).2 ≠ v3 := by
    intro h
    have hnd := hA1.support_nodup
    rw [hA1supp, List.nodup_cons] at hnd
    exact hnd.1 (h ▸ A1'.start_mem_support)
  have hne_v2v3s : v2 ≠ v3s := by
    rw [hv2def, hv3sdef]
    intro h
    exact hne_s1v3 ((M j0 jD).injective h)
  have hsuppH : H.support = (H.takeUntil v2 hv2mem).support
      ++ (H.dropUntil v2 hv2mem).support.tail := by
    conv_lhs => rw [← H.take_spec hv2mem]
    rw [SimpleGraph.Walk.support_append]
  have htakeH : (H.takeUntil v2 hv2mem).IsPath := hH.isPath.takeUntil hv2mem
  have hdropH : (H.dropUntil v2 hv2mem).IsPath := hH.isPath.dropUntil hv2mem
  obtain ⟨u3, C', hC', hadju3, htakesupp, hv2C'⟩ :=
    path_peel_last (H.takeUntil v2 hv2mem) htakeH hne_v2v3s
  have hcu3 : col (jD, u3) = b := by
    have h : col (jD, u3) ≠ col (jD, v2) :=
      hproper _ _ ((weldLift Gs M jD).map_adj hadju3)
    rw [hcv2] at h
    exact bool_eq_of_ne_not3 h
  -- the jB and jC Hamilton paths
  obtain ⟨u3s, hu3sdef⟩ : ∃ x, x = M jD jB u3 := ⟨_, rfl⟩
  have hcu3s : col (jB, u3s) = !b := by
    have h : col (jD, u3) ≠ col (jB, u3s) :=
      hu3sdef ▸ hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjBD) u3)
    rw [hcu3] at h
    exact bool_eq_not_of_ne3 (Ne.symm h)
  obtain ⟨HB, hHB⟩ := hlace jB (s 2).2 u3s (by
    show col (jB, (s 2).2) ≠ col (jB, u3s)
    rw [hcS2, hcu3s]
    cases b <;> simp)
  obtain ⟨HC, hHC⟩ := hlace jC u1 (t 0).2 (by
    show col (jC, u1) ≠ col (jC, (t 0).2)
    rw [hcu1, hcT0]
    cases b <;> simp)
  -- pair 0: j0 leg, cross, jC Hamilton path
  have hR00 : ∃ R : (weldGraph ell Gs M).Walk (s 0) (j0, v1), R.IsPath ∧
      R.support = A0.support.map (fun w => (j0, w)) := by
    refine ⟨(A0.map (weldLift Gs M j0)).copy (Prod.ext hs0.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA0
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R00, hR00p, hR00s⟩ := hR00
  obtain ⟨R01, hR01p, hR01s⟩ := weld_splice_snoc R00 HC hR00p hHC.isPath
    (hu1def ▸ weld_cross_adj (Gs := Gs) (M := M) hj0C v1)
    (by
      intro w' _ hmem
      rw [hR00s, mem_map_pair] at hmem
      exact hj0C hmem.1.symm)
  -- pair 1: s₁ then the jD suffix
  have hadj1a : (weldGraph ell Gs M).Adj (s 1) (jD, v2) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) hj0D (s 1).2
    rw [← hv2def] at h
    rwa [show ((j0 : Fin ell), (s 1).2) = s 1 from Prod.ext hs1.symm rfl] at h
  have hP1 : ∃ P : (weldGraph ell Gs M).Walk (s 1) (t 1), P.IsPath ∧
      P.support = s 1 :: (H.dropUntil v2 hv2mem).support.map (fun w => (jD, w)) := by
    have hDl : ∃ Q : (weldGraph ell Gs M).Walk (jD, v2) (t 1), Q.IsPath ∧
        Q.support = (H.dropUntil v2 hv2mem).support.map (fun w => (jD, w)) := by
      refine ⟨((H.dropUntil v2 hv2mem).map (weldLift Gs M jD)).copy rfl
        (Prod.ext ht1.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hdropH
      · rw [SimpleGraph.Walk.support_copy, weldLift_support]
    obtain ⟨Q, hQp, hQs⟩ := hDl
    refine ⟨SimpleGraph.Walk.cons hadj1a Q, ?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQp, ?_⟩
      intro hmem
      rw [hQs, mem_map_pair] at hmem
      exact hj0D (hs1.symm.trans hmem.1)
    · rw [SimpleGraph.Walk.support_cons, hQs]
  obtain ⟨P1w, hP1p, hP1s⟩ := hP1
  -- pair 2: the jB Hamilton path, back through u3, the reversed jD prefix, the j0 suffix
  have hR20 : ∃ R : (weldGraph ell Gs M).Walk (s 2) (jB, u3s), R.IsPath ∧
      R.support = HB.support.map (fun w => (jB, w)) := by
    refine ⟨(HB.map (weldLift Gs M jB)).copy (Prod.ext hs2.symm rfl) rfl, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_copy]
      exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hHB.isPath
    · rw [SimpleGraph.Walk.support_copy, weldLift_support]
  obtain ⟨R20, hR20p, hR20s⟩ := hR20
  obtain ⟨R21, hR21p, hR21s⟩ := weld_splice_snoc R20 C'.reverse hR20p hC'.reverse
    ((hu3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hjBD.symm u3).symm)
    (by
      intro w' _ hmem
      rw [hR20s, mem_map_pair] at hmem
      exact hjBD hmem.1.symm)
  obtain ⟨R22, hR22p, hR22s⟩ := weld_splice_snoc R21 A1' hR21p hA1'
    ((hv3sdef ▸ weld_cross_adj (Gs := Gs) (M := M) hj0D v3).symm)
    (by
      intro w' _ hmem
      rw [hR21s, List.mem_append, hR20s, mem_map_pair, mem_map_pair] at hmem
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hj0B h1
      · exact hj0D h1)
  have hpaths : ∀ i : Fin 3, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
      ∀ x : Fin ell × W, x ∈ P.support ↔
        ((i = 0 ∧ ((x.1 = j0 ∧ x.2 ∈ A0.support) ∨ (x.1 = jC ∧ x.2 ∈ HC.support))) ∨
          (i = 1 ∧ (x = s 1 ∨
            (x.1 = jD ∧ x.2 ∈ (H.dropUntil v2 hv2mem).support))) ∨
          (i = 2 ∧ ((x.1 = jB ∧ x.2 ∈ HB.support) ∨ (x.1 = jD ∧ x.2 ∈ C'.support) ∨
            (x.1 = j0 ∧ x.2 ∈ A1'.support)))) := by
    intro i
    fin_cases i
    · refine ⟨R01.copy rfl (Prod.ext ht0.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR01p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR01s, List.mem_append, hR00s,
          mem_map_pair, mem_map_pair]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨rfl, Or.inl ⟨h1, h2⟩⟩
          · exact Or.inl ⟨rfl, Or.inr ⟨h1, h2⟩⟩
        · rintro (⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
    · refine ⟨P1w.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hP1p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hP1s]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
          · rw [mem_map_pair] at h
            exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
        · rintro (⟨h0, -⟩ | ⟨-, h | ⟨h1, h2⟩⟩ | ⟨h0, -⟩)
          · exact absurd h0 (by decide)
          · exact h ▸ List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ ?_
            rw [mem_map_pair]
            exact ⟨h1, h2⟩
          · exact absurd h0 (by decide)
    · refine ⟨R22.copy rfl (Prod.ext ht2.symm rfl), ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact hR22p
      · intro x
        rw [SimpleGraph.Walk.support_copy, hR22s, List.mem_append, hR21s,
          List.mem_append, hR20s, mem_map_pair, mem_map_pair, mem_map_pair,
          SimpleGraph.Walk.support_reverse]
        constructor
        · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨h1, h2⟩⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
              ⟨h1, List.mem_reverse.mp h2⟩)⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨h1, h2⟩)⟩)
        · rintro (⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
          · exact absurd h0 (by decide)
          · exact absurd h0 (by decide)
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inl (Or.inr ⟨h1, List.mem_reverse.mpr h2⟩)
          · exact Or.inr ⟨h1, h2⟩
  choose P hPp hPchar using hpaths
  refine weld_lemma21 hproper hlace (hmono.st_ne 0 0) {j0, jB, jC, jD} P hPp ?_ ?_ ?_
  · intro r x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases (hPchar r x).mp hx with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ |
      ⟨-, h | ⟨h1, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · rw [h]
      exact Or.inl hs1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inl h1
  · rintro ⟨xj, xw⟩ hxJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl | rfl | rfl
    · rcases hAcov xw with h | h
      · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inl ⟨rfl, h⟩⟩)⟩
      · rw [hA1supp] at h
        rcases List.mem_cons.mp h with h2 | h2
        · exact ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inl
            (Prod.ext hs1.symm h2)⟩))⟩
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr
            ⟨rfl, h2⟩)⟩))⟩
    · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl
        ⟨rfl, hHB.mem_support xw⟩⟩))⟩
    · exact ⟨0, (hPchar 0 (xj, xw)).mpr (Or.inl ⟨rfl, Or.inr
        ⟨rfl, hHC.mem_support xw⟩⟩)⟩
    · have h := hH.mem_support xw
      rw [hsuppH] at h
      rcases List.mem_append.mp h with h | h
      · rw [htakesupp] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact ⟨2, (hPchar 2 (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl
            ⟨rfl, h2⟩)⟩))⟩
        · rw [List.mem_singleton] at h2
          refine ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr
            ⟨rfl, ?_⟩⟩))⟩
          rw [h2]
          exact (H.dropUntil v2 hv2mem).start_mem_support
      · refine ⟨1, (hPchar 1 (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, Or.inr
          ⟨rfl, List.mem_of_mem_tail h⟩⟩))⟩
  · intro i j hij x hx
    have h1 := (hPchar i x).mp hx.1
    have h2 := (hPchar j x).mp hx.2
    have hdisjH : ∀ w, w ∈ C'.support → w ∈ (H.dropUntil v2 hv2mem).support → False := by
      intro w hw hw2
      have hnd := hH.isPath.support_nodup
      rw [hsuppH, htakesupp] at hnd
      rcases List.mem_cons.mp ((SimpleGraph.Walk.cons_tail_support
        (H.dropUntil v2 hv2mem)) ▸ hw2 : w ∈ v2 :: (H.dropUntil v2 hv2mem).support.tail)
        with h3 | h3
      · exact hv2C' (h3 ▸ hw)
      · exact (List.nodup_append.mp hnd).2.2 w (List.mem_append_left _ hw) w h3 rfl
    have hd01 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jC ∧ y.2 ∈ HC.support)) →
        (y = s 1 ∨ (y.1 = jD ∧ y.2 ∈ (H.dropUntil v2 hv2mem).support)) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (h | ⟨hz1, -⟩)
      · refine hAdis y.2 hy2 ?_
        rw [show y.2 = (s 1).2 from congrArg Prod.snd h, hA1supp]
        exact List.mem_cons_self ..
      · exact hj0D (hy1.symm.trans hz1)
      · have h1 : (s 1).1 = jC := (congrArg Prod.fst h).symm.trans hy1
        exact hj0C (hs1.symm.trans h1)
      · exact hjCD (hy1.symm.trans hz1)
    have hd02 : ∀ (y : Fin ell × W),
        ((y.1 = j0 ∧ y.2 ∈ A0.support) ∨ (y.1 = jC ∧ y.2 ∈ HC.support)) →
        ((y.1 = jB ∧ y.2 ∈ HB.support) ∨ (y.1 = jD ∧ y.2 ∈ C'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩) (⟨hz1, -⟩ | ⟨hz1, -⟩ | ⟨hz1, hz2⟩)
      · exact hj0B (hy1.symm.trans hz1)
      · exact hj0D (hy1.symm.trans hz1)
      · refine hAdis y.2 hy2 ?_
        rw [hA1supp]
        exact List.mem_cons_of_mem _ hz2
      · exact hjBC (hz1.symm.trans hy1)
      · exact hjCD (hy1.symm.trans hz1)
      · exact hj0C (hz1.symm.trans hy1)
    have hd12 : ∀ (y : Fin ell × W),
        (y = s 1 ∨ (y.1 = jD ∧ y.2 ∈ (H.dropUntil v2 hv2mem).support)) →
        ((y.1 = jB ∧ y.2 ∈ HB.support) ∨ (y.1 = jD ∧ y.2 ∈ C'.support) ∨
          (y.1 = j0 ∧ y.2 ∈ A1'.support)) → False := by
      rintro y (h | ⟨hz1, hz2⟩) (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
      · have h1 : (s 1).1 = jB := (congrArg Prod.fst h).symm.trans hw1
        exact hj0B (hs1.symm.trans h1)
      · have h1 : (s 1).1 = jD := (congrArg Prod.fst h).symm.trans hw1
        exact hj0D (hs1.symm.trans h1)
      · refine hs1A1' ?_
        rw [← show y.2 = (s 1).2 from congrArg Prod.snd h]
        exact hw2
      · exact hjBD (hw1.symm.trans hz1)
      · exact hdisjH y.2 hw2 hz2
      · exact hj0D (hw1.symm.trans hz1)
    rcases h1 with ⟨hi0, hp⟩ | ⟨hi1, hp⟩ | ⟨hi2, hp⟩ <;>
      rcases h2 with ⟨hj0', hq'⟩ | ⟨hj1', hq'⟩ | ⟨hj2', hq'⟩
    · exact hij (hi0.trans hj0'.symm)
    · exact hd01 x hp hq'
    · exact hd02 x hp hq'
    · exact hd01 x hq' hp
    · exact hij (hi1.trans hj1'.symm)
    · exact hd12 x hp hq'
    · exact hd02 x hq' hp
    · exact hd12 x hq' hp
    · exact hij (hi2.trans hj2'.symm)

end SmallCase523

section Rank3Equit

/-- A weld of equitable pieces is equitable: classes sum fiberwise. -/
private theorem weld_classes_eq {W : Type} [DecidableEq W] [Fintype W] {ell : ℕ}
    {col : Fin ell × W → Bool}
    (h : ∀ j : Fin ell,
      (Finset.univ.filter (fun w => col (j, w) = false)).card
        = (Finset.univ.filter (fun w => col (j, w) = true)).card) :
    Fintype.card {x : Fin ell × W // col x = false}
      = Fintype.card {x : Fin ell × W // col x = true} := by
  classical
  have hc : ∀ c : Bool, Fintype.card {x : Fin ell × W // col x = c}
      = ∑ j : Fin ell, (Finset.univ.filter (fun w => col (j, w) = c)).card := by
    intro c
    rw [Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin ell × W => x.1) (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have h2 := hx.2
      have h1 := hx.1
      rw [show ((j : Fin ell), x.2) = x from Prod.ext h2.symm rfl]
      exact h1
    · intro x hx y hy he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) he
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨(j, w), ?_, rfl⟩
      simp [hw]
  rw [hc false, hc true]
  exact Finset.sum_congr rfl (fun j _ => h j)

/-- A nonempty, properly colored rank-3 tree: even order at least six, and equitable. -/
theorem colemanRank3_equitable {V : Type} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    {col : V → Bool} (hT : IsColemanTree G 3) (hBB : IsProper2Coloring G col)
    (hne : Nonempty V) :
    IsEquitableBipartite G col ∧ 6 ≤ Fintype.card V := by
  classical
  cases hT with
  | @weld V' W' G' ell r Gs M hr hEll htl hM e =>
    have instDW : DecidableEq W' := Classical.decEq W'
    have hell0 : 0 < ell := by omega
    have instW : Fintype W' :=
      Fintype.ofInjective (fun w : W' => e.symm ((⟨0, hell0⟩ : Fin ell), w))
        (fun a b h => (Prod.ext_iff.mp (e.symm.toEquiv.injective h)).2)
    have hcardV : Fintype.card V = ell * Fintype.card W' := by
      rw [Fintype.card_congr e.toEquiv, Fintype.card_prod, Fintype.card_fin]
    have hWne : Nonempty W' := by
      obtain ⟨v⟩ := hne
      exact ⟨(e v).2⟩
    have hpW : IsProper2Coloring (weldGraph ell Gs M) (fun x => col (e.symm x)) := by
      intro x y hxy
      exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
    have htl2 : ∀ j, IsColemanTree (Gs j) 2 := by
      intro j
      have h := htl j
      simpa using h
    have hcopyP : ∀ j : Fin ell, IsProper2Coloring (Gs j)
        (fun w => col (e.symm (j, w))) :=
      fun j u v huv => hpW (j, u) (j, v) ((weldLift Gs M j).map_adj huv)
    have hpiece : ∀ j : Fin ell, IsEquitableBipartite (Gs j)
        (fun w => col (e.symm (j, w))) :=
      fun j => colemanRank2_equitable (htl2 j) (hcopyP j) hWne
    obtain ⟨hW2, -⟩ := colemanRank2_card (htl2 ⟨0, hell0⟩) (hcopyP _) hWne
    constructor
    · constructor
      · exact hBB
      · -- transport the weld-level class balance through the isomorphism
        have hbal : Fintype.card {x : Fin ell × W' // col (e.symm x) = false}
            = Fintype.card {x : Fin ell × W' // col (e.symm x) = true} := by
          apply weld_classes_eq
          intro j
          have h := (hpiece j).2
          rw [Fintype.card_subtype, Fintype.card_subtype] at h
          exact h
        have htrans : ∀ c : Bool, Fintype.card {v : V // col v = c}
            = Fintype.card {x : Fin ell × W' // col (e.symm x) = c} := by
          intro c
          refine Fintype.card_congr (e.toEquiv.subtypeEquiv ?_)
          intro v
          constructor
          · intro h
            show col (e.symm (e v)) = c
            rwa [e.symm_apply_apply]
          · intro h
            have h2 : col (e.symm (e v)) = c := h
            rwa [e.symm_apply_apply] at h2
        rw [htrans false, htrans true]
        exact hbal
    · calc 6 = 3 * 2 := rfl
      _ ≤ ell * Fintype.card W' := Nat.mul_le_mul (by omega) hW2
      _ = Fintype.card V := hcardV.symm
end Rank3Equit

section SmallCase5Disp

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- Case 5 at the normalized shape `{s₀, s₁, t₂} ⊆ j0`, `s₂ ∉ j0`, dispatching on the
    positions of `t₀` and `t₁`. -/
private theorem small_case5_norm
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell}
    (hs0 : (s 0).1 = j0) (hs1 : (s 1).1 = j0) (ht2 : (t 2).1 = j0)
    (hs2n : (s 2).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 2)
    (hTn : ¬ ∀ i, (t i).1 = j0) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  have hwB : ∀ (jx : Fin ell), jx ≠ j0 → ¬ ((s 2).1 = jx ∧ (t 0).1 = jx ∧ (t 1).1 = jx) := by
    rintro jx hjx ⟨h2, h0, h1⟩
    have hm : ∀ i : Fin 3, i ∈ weldWSet s t jx := by
      intro i
      fin_cases i
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h0⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h2⟩
    have h3 : 3 ≤ (weldWSet s t jx).card := by
      have huniv : (Finset.univ : Finset (Fin 3)) ⊆ weldWSet s t jx := fun i _ => hm i
      calc 3 = (Finset.univ : Finset (Fin 3)).card := by simp
      _ ≤ (weldWSet s t jx).card := Finset.card_le_card huniv
    have := hw jx hjx
    omega
  by_cases ht0 : (t 0).1 = j0
  · have ht1n : (t 1).1 ≠ j0 := by
      intro h
      exact hTn (fun i => by fin_cases i <;> assumption)
    by_cases hs2B : (s 2).1 = (t 1).1
    · exact small_case5_11 hproper hlace hcov2 hell4 hmono
        (fun h => ht1n h.symm) hs0 hs1 ht2 ht0 rfl hs2B
    · exact small_case5_12 hproper hlace hcov2 hmono
        (fun h => ht1n h.symm) (fun h => hs2n h.symm) (fun h => hs2B h.symm)
        hs0 hs1 ht2 ht0 rfl rfl
  · by_cases ht1 : (t 1).1 = j0
    · -- swap the first two pairs, then the branch above
      apply dpc_perm (Equiv.swap 0 1)
      have hmono' : MonoDemand col b (fun i => s (Equiv.swap 0 1 i))
          (fun i => t (Equiv.swap 0 1 i)) :=
        ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
          hmono.2.2.1.comp (Equiv.swap 0 1).injective,
          hmono.2.2.2.comp (Equiv.swap 0 1).injective⟩
      have hs0' : (s (Equiv.swap 0 1 0)).1 = j0 := by rw [Equiv.swap_apply_left]; exact hs1
      have hs1' : (s (Equiv.swap 0 1 1)).1 = j0 := by rw [Equiv.swap_apply_right]; exact hs0
      have ht2' : (t (Equiv.swap 0 1 2)).1 = j0 := by
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact ht2
      have ht0' : (t (Equiv.swap 0 1 0)).1 = j0 := by rw [Equiv.swap_apply_left]; exact ht1
      have ht1n' : (t (Equiv.swap 0 1 1)).1 ≠ j0 := by
        rw [Equiv.swap_apply_right]
        exact ht0
      have hs2' : (s (Equiv.swap 0 1 2)).1 ≠ j0 := by
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact hs2n
      by_cases hs2B : (s (Equiv.swap 0 1 2)).1 = (t (Equiv.swap 0 1 1)).1
      · exact small_case5_11 hproper hlace hcov2 hell4 hmono'
          (fun h => ht1n' h.symm) hs0' hs1' ht2' ht0' rfl hs2B
      · exact small_case5_12 hproper hlace hcov2 hmono'
          (fun h => ht1n' h.symm) (fun h => hs2' h.symm) (fun h => hs2B h.symm)
          hs0' hs1' ht2' ht0' rfl rfl
    · -- both remaining targets outside
      by_cases ht0B : (t 0).1 = (s 2).1
      · have ht1B : (t 1).1 ≠ (s 2).1 := by
          intro h
          exact hwB (s 2).1 hs2n ⟨rfl, ht0B, h⟩
        exact small_case5_21 hproper hlace hcov2 hclass hell4 hmono
          (fun h => hs2n h.symm) (fun h => ht1 h.symm)
          (fun h => ht1B h.symm)
          hs0 hs1 ht2 rfl ht0B rfl
      · by_cases ht1B : (t 1).1 = (s 2).1
        · -- swap the first two pairs, then the 5.2a shape
          apply dpc_perm (Equiv.swap 0 1)
          have hmono' : MonoDemand col b (fun i => s (Equiv.swap 0 1 i))
              (fun i => t (Equiv.swap 0 1 i)) :=
            ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
              hmono.2.2.1.comp (Equiv.swap 0 1).injective,
              hmono.2.2.2.comp (Equiv.swap 0 1).injective⟩
          have hs0' : (s (Equiv.swap 0 1 0)).1 = j0 := by
            rw [Equiv.swap_apply_left]; exact hs1
          have hs1' : (s (Equiv.swap 0 1 1)).1 = j0 := by
            rw [Equiv.swap_apply_right]; exact hs0
          have ht2' : (t (Equiv.swap 0 1 2)).1 = j0 := by
            rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact ht2
          have hs2' : (s (Equiv.swap 0 1 2)).1 ≠ j0 := by
            rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact hs2n
          have ht0B' : (t (Equiv.swap 0 1 0)).1 = (s (Equiv.swap 0 1 2)).1 := by
            rw [Equiv.swap_apply_left,
              Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact ht1B
          have ht1' : (t (Equiv.swap 0 1 1)).1 ≠ j0 := by
            rw [Equiv.swap_apply_right]
            exact ht0
          have ht1B' : (t (Equiv.swap 0 1 1)).1 ≠ (s (Equiv.swap 0 1 2)).1 := by
            rw [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact ht0B
          exact small_case5_21 hproper hlace hcov2 hclass hell4 hmono'
            (fun h => hs2' h.symm) (fun h => ht1' h.symm)
            (fun h => ht1B' h.symm)
            hs0' hs1' ht2' rfl ht0B' rfl
        · by_cases ht01 : (t 0).1 = (t 1).1
          · exact small_case5_22 hproper hlace hcov2 hclass hell4 hmono
              (fun h => hs2n h.symm) (fun h => ht0 h.symm) (fun h => ht0B h.symm)
              hs0 hs1 ht2 rfl rfl ht01.symm
          · exact small_case5_23 hproper hlace hcov2 hclass hmono
              (fun h => hs2n h.symm) (fun h => ht0 h.symm) (fun h => ht1 h.symm)
              (fun h => ht0B h.symm) (fun h => ht1B h.symm) ht01
              hs0 hs1 ht2 rfl rfl rfl

end SmallCase5Disp

section SmallCase5Outer

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- Case 5 with exactly one source outside the full copy: normalize that pair to
    position 2 and dispatch. -/
private theorem small_case5_A2
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hfull : (weldWSet s t j0).card = 3)
    {c : Fin 3} (hsc : (s c).1 ≠ j0) (huniq : ∀ i, i ≠ c → (s i).1 = j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 2)
    (hTn : ¬ ∀ i, (t i).1 = j0) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  have htc : (t c).1 = j0 := (weldWSet_full_touch hfull c).resolve_left hsc
  apply dpc_perm (Equiv.swap c 2)
  have hmono' : MonoDemand col b (fun i => s (Equiv.swap c 2 i))
      (fun i => t (Equiv.swap c 2 i)) :=
    ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
      hmono.2.2.1.comp (Equiv.swap c 2).injective,
      hmono.2.2.2.comp (Equiv.swap c 2).injective⟩
  have hσ0 : Equiv.swap c 2 0 ≠ c := by
    intro h
    have h2 := (Equiv.swap c 2).injective (h.trans (Equiv.swap_apply_right c 2).symm)
    exact absurd h2 (by decide)
  have hσ1 : Equiv.swap c 2 1 ≠ c := by
    intro h
    have h2 := (Equiv.swap c 2).injective (h.trans (Equiv.swap_apply_right c 2).symm)
    exact absurd h2 (by decide)
  refine small_case5_norm hproper hlace hcov2 hclass hell4 hmono'
    (huniq _ hσ0) (huniq _ hσ1) ?_ ?_ ?_ ?_
  · show (t (Equiv.swap c 2 2)).1 = j0
    rw [Equiv.swap_apply_right]
    exact htc
  · show (s (Equiv.swap c 2 2)).1 ≠ j0
    rw [Equiv.swap_apply_right]
    exact hsc
  · intro j hj
    rw [weldWSet_card_perm]
    exact hw j hj
  · intro hall
    apply hTn
    intro i
    have h := hall (Equiv.swap c 2 i)
    rwa [Equiv.swap_apply_self] at h
  
/-- Case 5, fully general: one full copy holding neither all sources nor all targets. -/
private theorem small_case5
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hfull : (weldWSet s t j0).card = 3)
    (hSn : ¬ ∀ i, (s i).1 = j0) (hTn : ¬ ∀ i, (t i).1 = j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 2) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  obtain ⟨c, hsc⟩ : ∃ c, (s c).1 ≠ j0 := by
    by_contra h
    exact hSn (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
  by_cases huniq : ∀ i, i ≠ c → (s i).1 = j0
  · exact small_case5_A2 hproper hlace hcov2 hclass hell4 hmono hfull hsc huniq hw hTn
  · push_neg at huniq
    obtain ⟨d, hdc, hsd⟩ := huniq
    -- swap the roles of sources and targets
    apply dpc_swap
    have hfull' : (weldWSet t s j0).card = 3 := by
      rw [weldWSet_swap]
      exact hfull
    have hw' : ∀ j, j ≠ j0 → (weldWSet t s j).card ≤ 2 := by
      intro j hj
      rw [weldWSet_swap]
      exact hw j hj
    -- the unique out-pair on the target side is the third index
    obtain ⟨e, hec, hed⟩ : ∃ e : Fin 3, e ≠ c ∧ e ≠ d := by
      fin_cases c <;> fin_cases d <;>
        first
          | exact absurd rfl hdc
          | exact ⟨2, by decide, by decide⟩
          | exact ⟨1, by decide, by decide⟩
          | exact ⟨0, by decide, by decide⟩
  
    have htc : (t c).1 = j0 := (weldWSet_full_touch hfull c).resolve_left hsc
    have htd : (t d).1 = j0 := (weldWSet_full_touch hfull d).resolve_left hsd
    have hte : (t e).1 ≠ j0 := by
      intro h
      apply hTn
      intro i
      by_cases hic : i = c
      · exact hic ▸ htc
      · by_cases hid : i = d
        · exact hid ▸ htd
        · have hie : i = e := by
            refine Fin.ext ?_
            have h1 : i.val ≠ c.val := fun hh => hic (Fin.ext hh)
            have h2 : i.val ≠ d.val := fun hh => hid (Fin.ext hh)
            have h3 : c.val ≠ d.val := fun hh => hdc (Fin.ext hh.symm)
            have h4 : e.val ≠ c.val := fun hh => hec (Fin.ext hh)
            have h5 : e.val ≠ d.val := fun hh => hed (Fin.ext hh)
            have hi3 := i.isLt
            have hc3 := c.isLt
            have hd3 := d.isLt
            have he3 := e.isLt
            omega
          exact hie ▸ h
    refine small_case5_A2 hproper hlace hcov2 hclass hell4 hmono.swap hfull'
      (c := e) hte ?_ hw' hSn
    intro i hie
    by_cases hic : i = c
    · exact hic ▸ htc
    · have hid : i = d := by
        refine Fin.ext ?_
        have h1 : i.val ≠ c.val := fun hh => hic (Fin.ext hh)
        have h2 : i.val ≠ e.val := fun hh => hie (Fin.ext hh)
        have h3 : c.val ≠ d.val := fun hh => hdc (Fin.ext hh.symm)
        have h4 : e.val ≠ c.val := fun hh => hec (Fin.ext hh)
        have h5 : e.val ≠ d.val := fun hh => hed (Fin.ext hh)
        have hi3 := i.isLt
        have hc3 := c.isLt
        have hd3 := d.isLt
        have he3 := e.isLt
        omega
      exact hid ▸ htd

end SmallCase5Outer

section SmallCase6Outer

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- Case 6, general: two full copies, sources in both. -/
private theorem small_case6
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) {b : Bool}
    {s t : Fin 3 → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hw1 : (weldWSet s t j1).card = 3) (hw2 : (weldWSet s t j2).card = 3)
    (hmix1 : ∃ i, (s i).1 = j1) (hmix2 : ∃ i, (s i).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) 3 s t := by
  classical
  have hsplit : ∀ i, ((s i).1 = j1 ∧ (t i).1 = j2) ∨ ((s i).1 = j2 ∧ (t i).1 = j1) := by
    intro i
    rcases weldWSet_full_touch hw1 i with h1 | h1 <;>
      rcases weldWSet_full_touch hw2 i with h2 | h2
    · exact absurd (h1.symm.trans h2) hj12
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (h1.symm.trans h2) hj12
  obtain ⟨c, hc⟩ := hmix2
  have htc : (t c).1 = j1 := by
    rcases hsplit c with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h1.symm.trans hc) hj12
    · exact h2
  by_cases huniq : ∀ i, i ≠ c → (s i).1 = j1
  · apply dpc_perm (Equiv.swap c 2)
    have hmono' : MonoDemand col b (fun i => s (Equiv.swap c 2 i))
        (fun i => t (Equiv.swap c 2 i)) :=
      ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
        hmono.2.2.1.comp (Equiv.swap c 2).injective,
        hmono.2.2.2.comp (Equiv.swap c 2).injective⟩
    have hσ0 : Equiv.swap c 2 0 ≠ c := by
      intro h
      have h2 := (Equiv.swap c 2).injective (h.trans (Equiv.swap_apply_right c 2).symm)
      exact absurd h2 (by decide)
    have hσ1 : Equiv.swap c 2 1 ≠ c := by
      intro h
      have h2 := (Equiv.swap c 2).injective (h.trans (Equiv.swap_apply_right c 2).symm)
      exact absurd h2 (by decide)
    have hs0' := huniq _ hσ0
    have hs1' := huniq _ hσ1
    refine small_case6_core hproper hlace hcov2 hclass hell4 hmono' hj12
      hs0' hs1' ?_ ?_ ?_ ?_
    · show (t (Equiv.swap c 2 2)).1 = j1
      rw [Equiv.swap_apply_right]
      exact htc
    · show (s (Equiv.swap c 2 2)).1 = j2
      rw [Equiv.swap_apply_right]
      exact hc
    · rcases hsplit (Equiv.swap c 2 0) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hs0'.symm.trans h) hj12
    · rcases hsplit (Equiv.swap c 2 1) with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hs1'.symm.trans h) hj12
  · push_neg at huniq
    obtain ⟨d, hdc, hsd⟩ := huniq
    have hd2 : (s d).1 = j2 := by
      rcases hsplit d with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hsd
      · exact h
    have htd : (t d).1 = j1 := by
      rcases hsplit d with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hsd
      · exact h
    obtain ⟨e, hec, hed⟩ : ∃ e : Fin 3, e ≠ c ∧ e ≠ d := by
      fin_cases c <;> fin_cases d <;>
        first
          | exact absurd rfl hdc
          | exact ⟨2, by decide, by decide⟩
          | exact ⟨1, by decide, by decide⟩
          | exact ⟨0, by decide, by decide⟩
    have hse : (s e).1 = j1 := by
      rcases hsplit e with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exfalso
        obtain ⟨i, hi⟩ := hmix1
        have hicases : i = c ∨ i = d ∨ i = e := by
          have hi3 := i.isLt
          have hc3 := c.isLt
          have hd3 := d.isLt
          have he3 := e.isLt
          have h1 : c.val ≠ d.val := fun hh => hdc (Fin.ext hh.symm)
          have h2 : e.val ≠ c.val := fun hh => hec (Fin.ext hh)
          have h3 : e.val ≠ d.val := fun hh => hed (Fin.ext hh)
          have : i.val = c.val ∨ i.val = d.val ∨ i.val = e.val := by omega
          rcases this with hh | hh | hh
          · exact Or.inl (Fin.ext hh)
          · exact Or.inr (Or.inl (Fin.ext hh))
          · exact Or.inr (Or.inr (Fin.ext hh))
        rcases hicases with rfl | rfl | rfl
        · exact hj12 (hi.symm.trans hc)
        · exact hj12 (hi.symm.trans hd2)
        · exact hj12 (hi.symm.trans h)
    have hte : (t e).1 = j2 := by
      rcases hsplit e with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hse.symm.trans h) (fun hh => hj12 hh)
    -- normalized to the (j2, j1)-roles: sources c, d in j2, pair e's target in j2
    apply dpc_perm (Equiv.swap e 2)
    have hmono' : MonoDemand col b (fun i => s (Equiv.swap e 2 i))
        (fun i => t (Equiv.swap e 2 i)) :=
      ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
        hmono.2.2.1.comp (Equiv.swap e 2).injective,
        hmono.2.2.2.comp (Equiv.swap e 2).injective⟩
    have hσ0 : Equiv.swap e 2 0 ≠ e := by
      intro h
      have h2 := (Equiv.swap e 2).injective (h.trans (Equiv.swap_apply_right e 2).symm)
      exact absurd h2 (by decide)
    have hσ1 : Equiv.swap e 2 1 ≠ e := by
      intro h
      have h2 := (Equiv.swap e 2).injective (h.trans (Equiv.swap_apply_right e 2).symm)
      exact absurd h2 (by decide)
    have hin2 : ∀ i, i ≠ e → (s i).1 = j2 := by
      intro i hie
      by_cases hic : i = c
      · exact hic ▸ hc
      · have hid : i = d := by
          refine Fin.ext ?_
          have h1 : i.val ≠ c.val := fun hh => hic (Fin.ext hh)
          have h2 : i.val ≠ e.val := fun hh => hie (Fin.ext hh)
          have h3 : c.val ≠ d.val := fun hh => hdc (Fin.ext hh.symm)
          have h4 : e.val ≠ c.val := fun hh => hec (Fin.ext hh)
          have h5 : e.val ≠ d.val := fun hh => hed (Fin.ext hh)
          have hi3 := i.isLt
          have hc3 := c.isLt
          have hd3 := d.isLt
          have he3 := e.isLt
          omega
        exact hid ▸ hd2
    refine small_case6_core hproper hlace hcov2 hclass hell4 hmono' (Ne.symm hj12)
      (hin2 _ hσ0) (hin2 _ hσ1) ?_ ?_ ?_ ?_
    · show (t (Equiv.swap e 2 2)).1 = j2
      rw [Equiv.swap_apply_right]
      exact hte
    · show (s (Equiv.swap e 2 2)).1 = j1
      rw [Equiv.swap_apply_right]
      exact hse
    · rcases hsplit (Equiv.swap e 2 0) with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd ((hin2 _ hσ0).symm.trans h) hj12.symm
      · exact h
    · rcases hsplit (Equiv.swap e 2 1) with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd ((hin2 _ hσ1).symm.trans h) hj12.symm
      · exact h

end SmallCase6Outer

section SmallProp16C

variable {W : Type} [DecidableEq W] [Fintype W]
  {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
  {col : Fin ell × W → Bool}

/-- **Coleman's part (c) engine**: paired 3-covers of a weld whose pieces carry Hamilton
    laceability, paired 2-covers, equitability, and color classes of size at least three.
    Unlike Proposition 1.6 this needs no piece-order floor, so it serves ALL rank-4
    trees in the induction. -/
theorem small_prop16_c
    (hproper : IsProper2Coloring (weldGraph ell Gs M) col)
    (hlace : ∀ j, IsHamLaceable (Gs j) (fun w => col (j, w)))
    (hcov2 : ∀ j, IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) 2)
    (hcopy_eq : ∀ j : Fin ell, IsEquitableBipartite (Gs j) (fun w => col (j, w)))
    (hclass : ∀ (j : Fin ell) (c : Bool),
      3 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card)
    (hell4 : 4 ≤ ell) (hWne : Nonempty W) :
    IsPairedKDPCForOpposite (weldGraph ell Gs M) col 3 := by
  classical
  apply pairedKDPC_of_mono
  intro b s t hmono
  have hcovlev : ∀ (j : Fin ell) (m' : ℕ), 1 ≤ m' → m' ≤ 2 →
      IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m' := by
    intro j m' h1 h2
    rcases (by omega : m' = 1 ∨ m' = 2) with rfl | rfl
    · exact paired_one_opposite_iff_hamLaceable.mpr (hlace j)
    · exact hcov2 j
  by_cases hfull : ∃ j, (weldWSet s t j).card = 3
  · obtain ⟨j0, hw0⟩ := hfull
    by_cases hfull2 : ∃ j', j' ≠ j0 ∧ (weldWSet s t j').card = 3
    · obtain ⟨j', hj', hw'⟩ := hfull2
      by_cases hS0 : ∃ i, (s i).1 = j0
      · by_cases hS' : ∃ i, (s i).1 = j'
        · exact small_case6 hproper hlace hcov2 hclass hell4 hmono (Ne.symm hj')
            hw0 hw' hS0 hS'
        · have hT : ∀ i, (t i).1 = j' := fun i =>
            (weldWSet_full_touch hw' i).resolve_left (fun h => hS' ⟨i, h⟩)
          have hS : ∀ i, (s i).1 = j0 := by
            intro i
            rcases weldWSet_full_touch hw0 i with h | h
            · exact h
            · exact absurd ((hT i).symm.trans h) hj'
          exact small_case3 hproper hlace hclass hcovlev rfl (by omega) hmono
            (Ne.symm hj') hS hT
      · have hT : ∀ i, (t i).1 = j0 := fun i =>
          (weldWSet_full_touch hw0 i).resolve_left (fun h => hS0 ⟨i, h⟩)
        have hS : ∀ i, (s i).1 = j' := by
          intro i
          rcases weldWSet_full_touch hw' i with h | h
          · exact h
          · exact absurd ((hT i).symm.trans h) (Ne.symm hj')
        exact small_case3 hproper hlace hclass hcovlev rfl (by omega) hmono
          hj' hS hT
    · have hw1 : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ 2 := by
        intro j hj
        have h1 := weldWSet_card_le s t j
        have h2 : (weldWSet s t j).card ≠ 3 := fun h => hfull2 ⟨j, hj, h⟩
        omega
      by_cases hSin : ∀ i, (s i).1 = j0
      · by_cases hTin : ∀ i, (t i).1 = j0
        · exact small_case2 hproper hlace hcopy_eq
            (fun j m' h1 h2 => hcovlev j m' h1 (by omega)) (by omega) (by omega)
            hmono hSin hTin
        · have hTex : ∃ i, (t i).1 ≠ j0 := by
            by_contra h
            exact hTin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
          exact small_case4 hproper hlace hcov2 hclass hcovlev rfl (by omega)
            hmono hSin hTex hw1
      · by_cases hTin : ∀ i, (t i).1 = j0
        · have hSex : ∃ i, (s i).1 ≠ j0 := by
            by_contra h
            exact hSin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
          apply dpc_swap
          have hw1' : ∀ j, j ≠ j0 → (weldWSet t s j).card ≤ 2 := by
            intro j hj
            rw [weldWSet_swap]
            exact hw1 j hj
          exact small_case4 hproper hlace hcov2 hclass hcovlev rfl (by omega)
            hmono.swap hTin hSex hw1'
        · exact small_case5 hproper hlace hcov2 hclass hell4 hmono hw0 hSin hTin hw1
  · have hw1 : ∀ j, (weldWSet s t j).card ≤ 2 := by
      intro j
      have h1 := weldWSet_card_le s t j
      have h2 : (weldWSet s t j).card ≠ 3 := fun h => hfull ⟨j, h⟩
      omega
    exact small_case1 hproper hlace hcov2 hclass hWne hmono hw1

#print axioms small_prop16_c

end SmallProp16C

/-! ## Phase D: the rank induction -/

section RankInduction

/-- Every properly colored, nonempty Coleman tree of rank at least 2 is equitable, with
    at least `r!` vertices. -/
theorem colemanTree_equitable_card : ∀ (r : ℕ), 2 ≤ r →
    ∀ {V : Type} [instD : DecidableEq V] [instF : Fintype V]
    (G : SimpleGraph V) (col : V → Bool),
    IsColemanTree G r → IsProper2Coloring G col → Nonempty V →
    IsEquitableBipartite G col ∧ r.factorial ≤ Fintype.card V := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
    intro hr V instD instF G col hT hBB hne
    by_cases hr2 : r = 2
    · subst hr2
      obtain ⟨h1, h2⟩ := colemanRank2_card hT hBB hne
      exact ⟨colemanRank2_equitable hT hBB hne, by
        rw [show Nat.factorial 2 = 2 from rfl]
        exact h1⟩
    · have hr3 : 3 ≤ r := by omega
      cases hT with
      | base hham hcard => omega
      | @weld V' W' G' ell rr Gs M hrr hEll htl hM e =>
        have instDW : DecidableEq W' := Classical.decEq W'
        have hell0 : 0 < ell := by omega
        have instW : Fintype W' :=
          Fintype.ofInjective (fun w : W' => e.symm ((⟨0, hell0⟩ : Fin ell), w))
            (fun a b h => (Prod.ext_iff.mp (e.symm.toEquiv.injective h)).2)
        have hcardV : Fintype.card V = ell * Fintype.card W' := by
          rw [Fintype.card_congr e.toEquiv, Fintype.card_prod, Fintype.card_fin]
        have hWne : Nonempty W' := by
          obtain ⟨v⟩ := hne
          exact ⟨(e v).2⟩
        have hpW : IsProper2Coloring (weldGraph ell Gs M) (fun x => col (e.symm x)) := by
          intro x y hxy
          exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
        have hcopyP : ∀ j : Fin ell, IsProper2Coloring (Gs j)
            (fun w => col (e.symm (j, w))) :=
          fun j u v huv => hpW (j, u) (j, v) ((weldLift Gs M j).map_adj huv)
        have htl' : ∀ j, IsColemanTree (Gs j) (r - 1) := htl
        have hpiece : ∀ j : Fin ell, IsEquitableBipartite (Gs j)
            (fun w => col (e.symm (j, w)))
            ∧ (r - 1).factorial ≤ Fintype.card W' :=
          fun j => IH (r - 1) (by omega) (by omega) (Gs j) _ (htl' j) (hcopyP j) hWne
        constructor
        · refine ⟨hBB, ?_⟩
          have hbal : Fintype.card {x : Fin ell × W' // col (e.symm x) = false}
              = Fintype.card {x : Fin ell × W' // col (e.symm x) = true} := by
            apply weld_classes_eq
            intro j
            have h := (hpiece j).1.2
            rw [Fintype.card_subtype, Fintype.card_subtype] at h
            exact h
          have htrans : ∀ c : Bool, Fintype.card {v : V // col v = c}
              = Fintype.card {x : Fin ell × W' // col (e.symm x) = c} := by
            intro c
            refine Fintype.card_congr (e.toEquiv.subtypeEquiv ?_)
            intro v
            constructor
            · intro h
              show col (e.symm (e v)) = c
              rwa [e.symm_apply_apply]
            · intro h
              have h2 : col (e.symm (e v)) = c := h
              rwa [e.symm_apply_apply] at h2
          rw [htrans false, htrans true]
          exact hbal
        · have hfac : r.factorial = r * (r - 1).factorial := by
            obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
            rw [Nat.factorial_succ]
            simp
          rw [hfac, hcardV]
          exact Nat.mul_le_mul (by omega) (hpiece ⟨0, hell0⟩).2

/-- `4m − 2 ≤ m!` from `m ≥ 4`. -/
private theorem four_mul_le_factorial : ∀ (m : ℕ), 4 ≤ m → 4 * m - 2 ≤ m.factorial := by
  intro m
  induction m with
  | zero => omega
  | succ k IHk =>
    intro h
    by_cases hk : k = 3
    · subst hk
      decide
    · have h4 : 4 ≤ k := by omega
      have hIH := IHk h4
      rw [Nat.factorial_succ]
      have h1 : 4 * k - 2 ≤ (k + 1) * Nat.factorial k := by
        calc 4 * k - 2 ≤ Nat.factorial k := hIH
        _ ≤ (k + 1) * Nat.factorial k := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : Nat.factorial k ≥ 4 := by
        calc 4 ≤ 4 * k - 2 := by omega
        _ ≤ Nat.factorial k := hIH
      have h3 : (k + 1) * Nat.factorial k = k * Nat.factorial k + Nat.factorial k := by
        ring
      have h5 : k * Nat.factorial k ≥ 4 * k := by
        calc k * Nat.factorial k ≥ k * 4 := Nat.mul_le_mul_left k (by omega)
        _ = 4 * k := by ring
      omega

end RankInduction

section MainInduction

/-- **Coleman et al. 2025, Theorem 1.5**, by rank induction: ranks 2 and 3 from the base
    analysis, rank 4 through the part-(c) engine, higher ranks through Proposition 1.6. -/
theorem coleman_thm15_proved : ∀ (n : Nat), 2 ≤ n →
    ∀ {V : Type} [instD : DecidableEq V] [instF : Fintype V]
    (G : SimpleGraph V) (col : V → Bool),
    IsColemanTree G n → IsProper2Coloring G col →
    IsPairedKDPCForOpposite G col (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn V instD instF G col hT hBB
    by_cases hn2 : n = 2
    · subst hn2
      exact thm15_rank2 G col hT hBB
    · by_cases hn3 : n = 3
      · subst hn3
        exact thm15_rank3 G col hT hBB
      · -- rank at least 4: unpack the weld
        have hn4 : 4 ≤ n := by omega
        cases hT with
        | base hham hcard => omega
        | @weld V' W' G' ell rr Gs M hrr hEll htl hM e =>
          have instDW : DecidableEq W' := Classical.decEq W'
          have hell0 : 0 < ell := by omega
          have instW : Fintype W' :=
            Fintype.ofInjective (fun w : W' => e.symm ((⟨0, hell0⟩ : Fin ell), w))
              (fun a b h => (Prod.ext_iff.mp (e.symm.toEquiv.injective h)).2)
          -- an empty vertex type satisfies any cover property vacuously
          by_cases hne : Nonempty V
          case neg =>
            intro sd td hd
            exact absurd ⟨sd ⟨0, by omega⟩⟩ hne
          have hWne : Nonempty W' := by
            obtain ⟨v⟩ := hne
            exact ⟨(e v).2⟩
          apply pairedKDPC_iso e col (fun x => col (e.symm x)) (fun v => by simp)
          have hpW : IsProper2Coloring (weldGraph ell Gs M)
              (fun x => col (e.symm x)) := by
            intro x y hxy
            exact hBB _ _ (e.symm.map_rel_iff.mpr hxy)
          have hcopyP : ∀ j : Fin ell, IsProper2Coloring (Gs j)
              (fun w => col (e.symm (j, w))) :=
            fun j u v huv => hpW (j, u) (j, v) ((weldLift Gs M j).map_adj huv)
          have htl' : ∀ j, IsColemanTree (Gs j) (n - 1) := htl
          -- piece facts: equitable, large, and covered at level n − 2
          have hpieceEq : ∀ j : Fin ell, IsEquitableBipartite (Gs j)
              (fun w => col (e.symm (j, w)))
              ∧ (n - 1).factorial ≤ Fintype.card W' :=
            fun j => colemanTree_equitable_card (n - 1) (by omega) (Gs j) _
              (htl' j) (hcopyP j) hWne
          have hpieceCov : ∀ j : Fin ell, IsPairedKDPCForOpposite (Gs j)
              (fun w => col (e.symm (j, w))) (n - 2) := by
            intro j
            have h := IH (n - 1) (by omega) (by omega) (Gs j) _ (htl' j) (hcopyP j)
            rwa [show n - 1 - 1 = n - 2 from by omega] at h
          have hcardW : (n - 1).factorial ≤ Fintype.card W' := (hpieceEq ⟨0, hell0⟩).2
          by_cases hn4' : n = 4
          · -- rank 4: the part-(c) engine
            subst hn4'
            have hlacePiece : ∀ j, IsHamLaceable (Gs j)
                (fun w => col (e.symm (j, w))) := by
              intro j
              apply paired_one_opposite_iff_hamLaceable.mp
              refine prop11c_proved (Gs j) _ (hpieceEq j).1 (hpieceCov j)
                (by omega) (by omega) ?_
              have := hcardW
              simp only [show (4 : ℕ) - 1 = 3 from rfl, Nat.factorial] at this
              omega
            have hclassPiece : ∀ (j : Fin ell) (c : Bool),
                3 ≤ (Finset.univ.filter
                  (fun w => col (e.symm (j, w)) = c)).card := by
              intro j c
              have hbal : (Finset.univ.filter
                  (fun w => col (e.symm (j, w)) = false)).card
                  = (Finset.univ.filter
                    (fun w => col (e.symm (j, w)) = true)).card := by
                have h := (hpieceEq j).1.2
                rw [Fintype.card_subtype, Fintype.card_subtype] at h
                exact h
              have hsum := Finset.card_filter_add_card_filter_not
                (s := (Finset.univ : Finset W'))
                (p := fun w => col (e.symm (j, w)) = false)
              rw [Finset.card_univ] at hsum
              have hconv : (Finset.univ.filter
                  (fun w => ¬ col (e.symm (j, w)) = false)).card
                  = (Finset.univ.filter (fun w => col (e.symm (j, w)) = true)).card := by
                refine congrArg Finset.card (Finset.filter_congr ?_)
                intro w _
                cases hc : col (e.symm (j, w)) <;> simp
              have hW6 : 6 ≤ Fintype.card W' := by
                have := hcardW
                simp only [show (4 : ℕ) - 1 = 3 from rfl, Nat.factorial] at this
                omega
              cases c <;> omega
            have h3 := small_prop16_c hpW hlacePiece
              (fun j => by
                have h := hpieceCov j
                rwa [show (4 : ℕ) - 2 = 2 from rfl] at h)
              (fun j => (hpieceEq j).1) hclassPiece (by omega) hWne
            rwa [show (4 : ℕ) - 1 = 3 from rfl]
          · -- rank at least 5: Proposition 1.6
            have hn5 : 5 ≤ n := by omega
            have hS : ColemanProp16Setting ell (n - 1) Gs M
                (fun x => col (e.symm x)) := by
              refine ⟨by omega, by omega, ?_, hM, hpW, fun j => (hpieceEq j).1, ?_⟩
              · -- 4(n−1) − 2 ≤ |W|
                have hfac := four_mul_le_factorial (n - 1) (by omega)
                omega
              · intro j
                have h := hpieceCov j
                rwa [show n - 2 = n - 1 - 1 from by omega] at h
            have h := prop16 hS
            rwa [show n - 1 = n - 1 from rfl]
end MainInduction

#print axioms coleman_thm15_proved
