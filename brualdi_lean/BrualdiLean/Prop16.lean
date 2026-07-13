/-
Prop16.lean — Tier 3 (continued): infrastructure for mechanizing Coleman et al. 2025,
Proposition 1.6 (the weld induction step), toward discharging axiom A1 (`coleman_thm15`).

Contents:
* mono demands and demand-reversal transport (`MonoDemand`, `dpc_swap`, `dpc_reverse_many`,
  `pairedKDPC_of_mono`) — Coleman's "S ⊆ V₁, T ⊆ V₂" convention reconciled with the
  mainline's pairwise-opposite encoding;
* the weld splice (`weld_splice`) — join two copy-level path segments across a matching edge;
* per-copy class counting (`ColemanProp16Setting.class_card`, `.exists_avoid`) — each copy
  has at least `2n − 1` vertices of each color, so a fresh vertex avoiding fewer than
  `2n − 1` exclusions always exists;
* terminal bookkeeping (`weldWSet` = the index set behind Coleman's `w_j`) and card identities;
* the greedy connector chooser (`weld_greedy`) — Coleman's inductive `v_i, u_i` selection
  (Cases 1, 5, 6 of Prop 1.6), with the exclusion count refined so that connectors whose
  pair shares BOTH copies are absorbed into the `u`-count (their Case 6 saving);
* per-copy inner covers (`ColemanProp16Setting.inner_cover`) — `w_j`-PDPCs via Tier 1's
  `prop11c_proved`.

Nothing here is wired into the mainline.
-/
import BrualdiLean.Weld

set_option linter.unusedSectionVars false

namespace Brualdi.Ledger

universe u

/-! ## Demand machinery -/

section Demand

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- A monochrome demand: all sources colored `b`, all targets `!b`, both sides injective.
    This is Coleman's `S ⊆ V₁`, `T ⊆ V₂` convention (source/target distinctness follows
    from the colors). -/
def MonoDemand (col : V → Bool) (b : Bool) {k : ℕ} (s t : Fin k → V) : Prop :=
  (∀ i, col (s i) = b) ∧ (∀ i, col (t i) = !b) ∧
    Function.Injective s ∧ Function.Injective t

theorem MonoDemand.st_ne {col : V → Bool} {b : Bool} {k : ℕ} {s t : Fin k → V}
    (h : MonoDemand col b s t) (i j : Fin k) : s i ≠ t j := by
  intro he
  have h1 := h.1 i
  rw [he, h.2.1 j] at h1
  cases b <;> simp_all

theorem MonoDemand.opposite {col : V → Bool} {b : Bool} {k : ℕ} {s t : Fin k → V}
    (h : MonoDemand col b s t) : OppositeDemand col s t := by
  refine ⟨?_, h.2.2.1, h.2.2.2, fun i j => h.st_ne i j⟩
  intro i
  rw [h.1 i, h.2.1 i]
  cases b <;> simp

/-- Swapping the roles of sources and targets transports covers (reverse every path). -/
theorem dpc_swap {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V}
    (h : IsPairedDPC G k t s) : IsPairedDPC G k s t := by
  obtain ⟨p, hpath, hcover, hdisj⟩ := h
  refine ⟨fun i => (p i).reverse, fun i => (hpath i).reverse, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse]⟩
  · intro a b hab x hx
    simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    exact hdisj a b hab x hx

/-- Reversing any selected subset of the pairs transports covers. -/
theorem dpc_reverse_many {G : SimpleGraph V} {k : ℕ} {s t : Fin k → V} (f : Fin k → Bool)
    (h : IsPairedDPC G k (fun i => if f i then t i else s i)
      (fun i => if f i then s i else t i)) :
    IsPairedDPC G k s t := by
  classical
  obtain ⟨p, hpath, hcover, hdisj⟩ := h
  refine ⟨fun i => if hf : f i then
      ((p i).copy (if_pos hf) (if_pos hf)).reverse
    else
      (p i).copy (if_neg hf) (if_neg hf), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hf : f i
    · rw [dif_pos hf]
      apply SimpleGraph.Walk.IsPath.reverse
      rw [SimpleGraph.Walk.isPath_copy]
      exact hpath i
    · rw [dif_neg hf, SimpleGraph.Walk.isPath_copy]
      exact hpath i
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨i, ?_⟩
    dsimp only
    by_cases hf : f i
    · rw [dif_pos hf]
      simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hi
    · rw [dif_neg hf]
      simpa [SimpleGraph.Walk.support_copy] using hi
  · intro a b hab x hx
    dsimp only at hx
    apply hdisj a b hab x
    constructor
    · have := hx.1
      by_cases hf : f a
      · rw [dif_pos hf] at this
        simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using this
      · rw [dif_neg hf] at this
        simpa [SimpleGraph.Walk.support_copy] using this
    · have := hx.2
      by_cases hf : f b
      · rw [dif_pos hf] at this
        simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using this
      · rw [dif_neg hf] at this
        simpa [SimpleGraph.Walk.support_copy] using this

/-- To provide `k`-PDPCs for all legal pairwise-opposite demands, it suffices to cover all
    monochrome demands: flip the wrongly-oriented pairs, cover, flip back. -/
theorem pairedKDPC_of_mono {G : SimpleGraph V} {col : V → Bool} {k : ℕ}
    (h : ∀ (b : Bool) (s t : Fin k → V), MonoDemand col b s t → IsPairedDPC G k s t) :
    IsPairedKDPCForOpposite G col k := by
  classical
  intro s t hd
  apply dpc_reverse_many (fun i => col (s i))
  apply h false
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hc : col (s i)
    · rw [if_pos hc]
      have := hd.1 i
      rw [hc] at this
      cases hct : col (t i)
      · rfl
      · rw [hct] at this; exact absurd rfl this
    · rw [if_neg hc]
      cases hcs : col (s i)
      · rfl
      · exact absurd hcs hc
  · intro i
    dsimp only
    by_cases hc : col (s i)
    · rw [if_pos hc]
      simpa using hc
    · rw [if_neg hc]
      have := hd.1 i
      cases hct : col (t i)
      · rw [hct] at this
        have hcs : col (s i) = false := by
          cases hcs : col (s i)
          · rfl
          · exact absurd hcs hc
        rw [hcs] at this
        exact absurd rfl this
      · simp
  · intro a c hac
    dsimp only at hac
    by_cases ha : col (s a) <;> by_cases hb : col (s c)
    · rw [if_pos ha, if_pos hb] at hac
      exact hd.2.2.1 hac
    · rw [if_pos ha, if_neg hb] at hac
      exact absurd hac.symm (hd.2.2.2 c a)
    · rw [if_neg ha, if_pos hb] at hac
      exact absurd hac (hd.2.2.2 a c)
    · rw [if_neg ha, if_neg hb] at hac
      exact hd.2.1 hac
  · intro a c hac
    dsimp only at hac
    by_cases ha : col (s a) <;> by_cases hb : col (s c)
    · rw [if_pos ha, if_pos hb] at hac
      exact hd.2.1 hac
    · rw [if_pos ha, if_neg hb] at hac
      exact absurd hac (hd.2.2.2 a c)
    · rw [if_neg ha, if_pos hb] at hac
      exact absurd hac.symm (hd.2.2.2 c a)
    · rw [if_neg ha, if_neg hb] at hac
      exact hd.2.2.1 hac

/-! ### Path-splitting surgery (Cases 2–6 of Prop 1.6 cut inner paths at terminals) -/

/-- Split a path at an interior vertex `x`, exposing its two path-neighbors: the support
    partitions as `A ++ [x] ++ B` with `A` ending at a neighbor of `x` and `B` starting
    at one. -/
theorem path_split_interior {G : SimpleGraph V} {sa ta x : V}
    (p : G.Walk sa ta) (hp : p.IsPath) (hx : x ∈ p.support) (hxa : x ≠ sa) (hxb : x ≠ ta) :
    ∃ (y z : V) (A : G.Walk sa y) (B : G.Walk z ta),
      A.IsPath ∧ B.IsPath ∧ G.Adj y x ∧ G.Adj x z ∧
      p.support = A.support ++ x :: B.support := by
  classical
  have hT : (p.takeUntil x hx).IsPath := hp.takeUntil hx
  have hDr : (p.dropUntil x hx).IsPath := hp.dropUntil hx
  have hsupp : p.support = (p.takeUntil x hx).support ++ (p.dropUntil x hx).support.tail := by
    conv_lhs => rw [← p.take_spec hx]
    rw [SimpleGraph.Walk.support_append]
  -- peel `x` off the end of the take-part
  obtain ⟨y, hadj, R, hRev⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hxa (p.takeUntil x hx).reverse
  have hTsupp : (p.takeUntil x hx).support = R.support.reverse ++ [x] := by
    have h1 : (p.takeUntil x hx).reverse.support = x :: R.support := by
      rw [hRev, SimpleGraph.Walk.support_cons]
    have h2 : (p.takeUntil x hx).support.reverse = x :: R.support := by
      rw [← SimpleGraph.Walk.support_reverse]
      exact h1
    have h3 := congrArg List.reverse h2
    rwa [List.reverse_reverse, List.reverse_cons] at h3
  have hRpath : R.IsPath := by
    have h := hT.reverse
    rw [hRev] at h
    exact ((SimpleGraph.Walk.cons_isPath_iff hadj R).mp h).1
  -- peel `x` off the front of the drop-part
  obtain ⟨z, hadj2, B, hB⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hxb (p.dropUntil x hx)
  have hDsupp : (p.dropUntil x hx).support = x :: B.support := by
    rw [hB, SimpleGraph.Walk.support_cons]
  have hBpath : B.IsPath := by
    have h := hDr
    rw [hB] at h
    exact ((SimpleGraph.Walk.cons_isPath_iff hadj2 B).mp h).1
  refine ⟨y, z, R.reverse, B, hRpath.reverse, hBpath, hadj.symm, hadj2, ?_⟩
  rw [hsupp, hTsupp, hDsupp, List.tail_cons, SimpleGraph.Walk.support_reverse]
  simp [List.append_assoc]

/-- Peel the final vertex off a nontrivial path: expose its last edge. -/
theorem path_peel_last {G : SimpleGraph V} {sa y : V} (A : G.Walk sa y) (hA : A.IsPath)
    (hne : y ≠ sa) :
    ∃ (u : V) (A' : G.Walk sa u), A'.IsPath ∧ G.Adj u y ∧
      A.support = A'.support ++ [y] ∧ y ∉ A'.support := by
  obtain ⟨u, hadj, R, hRev⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne A.reverse
  have hcons := hA.reverse
  rw [hRev] at hcons
  obtain ⟨hR, hymem⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj R).mp hcons
  have hsupp : A.support = R.support.reverse ++ [y] := by
    have h2 : A.support.reverse = y :: R.support := by
      rw [← SimpleGraph.Walk.support_reverse, hRev, SimpleGraph.Walk.support_cons]
    have h3 := congrArg List.reverse h2
    rwa [List.reverse_reverse, List.reverse_cons] at h3
  refine ⟨u, R.reverse, hR.reverse, hadj.symm, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_reverse]
    exact hsupp
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact hymem

/-- Peel the initial vertex off a nontrivial path: expose its first edge. -/
theorem path_peel_head {G : SimpleGraph V} {x ta : V} (B : G.Walk x ta) (hB : B.IsPath)
    (hne : x ≠ ta) :
    ∃ (v : V) (B' : G.Walk v ta), B'.IsPath ∧ G.Adj x v ∧
      B.support = x :: B'.support ∧ x ∉ B'.support := by
  obtain ⟨v, hadj, B', hcons⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne B
  have hpath := hB
  rw [hcons] at hpath
  obtain ⟨hB', hxmem⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj B').mp hpath
  exact ⟨v, B', hB', hadj, by rw [hcons, SimpleGraph.Walk.support_cons], hxmem⟩

/-- Of two members of a list, one lies in the drop-part at the other's first occurrence. -/
theorem list_mem_drop_or {α : Type u} [DecidableEq α] {l : List α} {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) :
    x ∈ l.drop (l.idxOf y) ∨ y ∈ l.drop (l.idxOf x) := by
  have hnx : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hny : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
  rcases le_total (l.idxOf y) (l.idxOf x) with h | h
  · left
    have hlen : l.idxOf x - l.idxOf y < (l.drop (l.idxOf y)).length := by
      rw [List.length_drop]
      omega
    have hget : (l.drop (l.idxOf y))[l.idxOf x - l.idxOf y] = x := by
      rw [List.getElem_drop]
      have hidx : l.idxOf y + (l.idxOf x - l.idxOf y) = l.idxOf x := by omega
      rw [show l[l.idxOf y + (l.idxOf x - l.idxOf y)]'(by omega) = l[l.idxOf x]'hnx from by
        congr 1]
      exact List.getElem_idxOf hnx
    exact hget ▸ List.getElem_mem hlen
  · right
    have hlen : l.idxOf y - l.idxOf x < (l.drop (l.idxOf x)).length := by
      rw [List.length_drop]
      omega
    have hget : (l.drop (l.idxOf x))[l.idxOf y - l.idxOf x] = y := by
      rw [List.getElem_drop]
      rw [show l[l.idxOf x + (l.idxOf y - l.idxOf x)]'(by omega) = l[l.idxOf y]'hny from by
        congr 1; omega]
      exact List.getElem_idxOf hny
    exact hget ▸ List.getElem_mem hlen

/-- Of two support vertices of a walk, one lies on the drop-part at the other. -/
theorem dropUntil_mem_or {G : SimpleGraph V} {sa ta x y : V} (p : G.Walk sa ta)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    x ∈ (p.dropUntil y hy).support ∨ y ∈ (p.dropUntil x hx).support := by
  have hdrop : ∀ (z : V) (hz : z ∈ p.support),
      (p.dropUntil z hz).support = p.support.drop (p.support.idxOf z) := by
    intro z hz
    rw [SimpleGraph.Walk.dropUntil_eq_drop, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    congr 1
    have h1 : p.support.idxOf z < p.support.length := List.idxOf_lt_length_of_mem hz
    have h2 : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
    omega
  rw [hdrop x hx, hdrop y hy]
  exact list_mem_drop_or hx hy

/-- Split a path at two interior vertices `x₁` (first) and `x₂` (second): the support
    partitions as `A ++ Bmid ++ C` where `Bmid` runs from `x₁` to `x₂`, `A` ends at a
    path-neighbor of `x₁`, and `C` starts at a path-neighbor of `x₂`. -/
theorem path_split_both {G : SimpleGraph V} {sa ta x₁ x₂ : V}
    (p : G.Walk sa ta) (hp : p.IsPath) (hx₁ : x₁ ∈ p.support)
    (hx₂ : x₂ ∈ (p.dropUntil x₁ hx₁).support)
    (hx₁a : x₁ ≠ sa) (hx₂b : x₂ ≠ ta) :
    ∃ (y z : V) (A : G.Walk sa y) (Bmid : G.Walk x₁ x₂) (C : G.Walk z ta),
      A.IsPath ∧ Bmid.IsPath ∧ C.IsPath ∧ G.Adj y x₁ ∧ G.Adj x₂ z ∧
      p.support = A.support ++ Bmid.support ++ C.support := by
  classical
  have hT : (p.takeUntil x₁ hx₁).IsPath := hp.takeUntil hx₁
  have hDr : (p.dropUntil x₁ hx₁).IsPath := hp.dropUntil hx₁
  have hsupp : p.support =
      (p.takeUntil x₁ hx₁).support ++ (p.dropUntil x₁ hx₁).support.tail := by
    conv_lhs => rw [← p.take_spec hx₁]
    rw [SimpleGraph.Walk.support_append]
  -- peel `x₁` off the end of the take-part
  obtain ⟨y, hadj, R, hRev⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hx₁a (p.takeUntil x₁ hx₁).reverse
  have hTsupp : (p.takeUntil x₁ hx₁).support = R.support.reverse ++ [x₁] := by
    have h2 : (p.takeUntil x₁ hx₁).support.reverse = x₁ :: R.support := by
      rw [← SimpleGraph.Walk.support_reverse, hRev, SimpleGraph.Walk.support_cons]
    have h3 := congrArg List.reverse h2
    rwa [List.reverse_reverse, List.reverse_cons] at h3
  have hRpath : R.IsPath := by
    have h := hT.reverse
    rw [hRev] at h
    exact ((SimpleGraph.Walk.cons_isPath_iff hadj R).mp h).1
  -- split the drop-part at `x₂`
  set Dr := p.dropUntil x₁ hx₁ with hDrdef
  have hBmid : (Dr.takeUntil x₂ hx₂).IsPath := hDr.takeUntil hx₂
  have hD₂ : (Dr.dropUntil x₂ hx₂).IsPath := hDr.dropUntil hx₂
  have hDrsupp : Dr.support =
      (Dr.takeUntil x₂ hx₂).support ++ (Dr.dropUntil x₂ hx₂).support.tail := by
    conv_lhs => rw [← Dr.take_spec hx₂]
    rw [SimpleGraph.Walk.support_append]
  -- peel `x₂` off the front of the second drop-part
  obtain ⟨z, hadj2, C, hC⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hx₂b (Dr.dropUntil x₂ hx₂)
  have hCsupp : (Dr.dropUntil x₂ hx₂).support = x₂ :: C.support := by
    rw [hC, SimpleGraph.Walk.support_cons]
  have hCpath : C.IsPath := by
    have h := hD₂
    rw [hC] at h
    exact ((SimpleGraph.Walk.cons_isPath_iff hadj2 C).mp h).1
  refine ⟨y, z, R.reverse, Dr.takeUntil x₂ hx₂, C,
    hRpath.reverse, hBmid, hCpath, hadj.symm, hadj2, ?_⟩
  have hmid : (Dr.takeUntil x₂ hx₂).support = x₁ :: (Dr.takeUntil x₂ hx₂).support.tail :=
    SimpleGraph.Walk.support_eq_cons _
  rw [hsupp, hTsupp, hDrsupp, hCsupp, List.tail_cons,
    SimpleGraph.Walk.support_reverse, hmid]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.tail_cons]

end Demand

/-! ## Weld splice -/

section WeldInfra

variable {W : Type u} [DecidableEq W] [Fintype W]

theorem weldLift_support {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    (j : Fin ell) {u v : W} (q : (Gs j).Walk u v) :
    (q.map (weldLift Gs M j)).support = q.support.map (fun w => (j, w)) :=
  SimpleGraph.Walk.support_map _ _

/-- Join a segment of copy `i` to a segment of copy `j` across the matching edge at their
    shared interface: the result is a weld path whose support is the disjoint union. -/
theorem weld_splice {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {i j : Fin ell} (hij : i ≠ j) {a x y c : W}
    (q : (Gs i).Walk a x) (r : (Gs j).Walk y c) (hq : q.IsPath) (hr : r.IsPath)
    (hy : y = M i j x) :
    ∃ R : (weldGraph ell Gs M).Walk (i, a) (j, c), R.IsPath ∧
      R.support = q.support.map (fun w => (i, w)) ++ r.support.map (fun w => (j, w)) := by
  have hadj : (weldGraph ell Gs M).Adj (i, x) (j, y) := by
    have h := weld_cross_adj (Gs := Gs) (M := M) hij x
    rwa [← hy] at h
  obtain ⟨R, hRp, hRs⟩ := dpc_splice (q.map (weldLift Gs M i)) (r.map (weldLift Gs M j))
    (SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj i) hq)
    (SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj j) hr)
    hadj
    (by
      intro v hv
      rw [weldLift_mem_support, weldLift_mem_support] at hv
      exact hij (hv.1.1.symm.trans hv.2.1))
  rw [weldLift_support, weldLift_support] at hRs
  exact ⟨R, hRp, hRs⟩

/-- Extend a weld path ending at `(j, z)` by a segment of copy `j'` entered through the
    matching edge at `z`. The segment must avoid the vertices the path already uses in
    copy `j'`. -/
theorem weld_splice_snoc {ell : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {a : Fin ell × W} {j j' : Fin ell} {z y c : W}
    (R : (weldGraph ell Gs M).Walk a (j, z)) (q : (Gs j').Walk y c)
    (hR : R.IsPath) (hq : q.IsPath)
    (hadj : (weldGraph ell Gs M).Adj (j, z) (j', y))
    (hdisj : ∀ w', w' ∈ q.support → (j', w') ∉ R.support) :
    ∃ R' : (weldGraph ell Gs M).Walk a (j', c), R'.IsPath ∧
      R'.support = R.support ++ q.support.map (fun w => (j', w)) := by
  obtain ⟨R', hp, hs⟩ := dpc_splice R (q.map (weldLift Gs M j')) hR
    (SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj j') hq) hadj
    (by
      intro e he
      have h2 := he.2
      rw [weldLift_mem_support] at h2
      have hee : e = (j', e.2) := Prod.ext h2.1 rfl
      rw [hee] at he
      exact hdisj e.2 h2.2 he.1)
  rw [weldLift_support] at hs
  exact ⟨R', hp, hs⟩

/-- Two further copies distinct from a given one (`ell ≥ 3`). -/
theorem fin_exists_two_ne {ell : ℕ} (h : 3 ≤ ell) (j0 : Fin ell) :
    ∃ j2 j3 : Fin ell, j2 ≠ j0 ∧ j3 ≠ j0 ∧ j2 ≠ j3 := by
  have hcard : 1 < (Finset.univ.erase j0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j2, hj2, j3, hj3, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨j2, j3, Finset.ne_of_mem_erase hj2, Finset.ne_of_mem_erase hj3, hne⟩

/-! ## Class counting inside the Prop 1.6 setting -/

theorem ColemanProp16Setting.class_card {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) (c : Bool) :
    2 * n - 1 ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card := by
  have h := dpc_class_card (S.hcopy_eq j) c
  have h2 := S.horder
  omega

/-- A fresh vertex of prescribed color in copy `j` avoiding fewer than `2n − 1`
    exclusions always exists. -/
theorem ColemanProp16Setting.exists_avoid {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) (c : Bool) (avoid : Finset W)
    (h : avoid.card < 2 * n - 1) :
    ∃ y : W, col (j, y) = c ∧ y ∉ avoid := by
  apply dpc_spare_avoid c avoid
  have h1 := S.class_card j c
  have h2 : (avoid.filter (fun w => col (j, w) = c)).card ≤ avoid.card :=
    Finset.card_filter_le _ _
  omega

/-- Per-copy inner covers at any level `1 ≤ m ≤ n − 1`, via Tier 1's `prop11c_proved`. -/
theorem ColemanProp16Setting.inner_cover {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) {m : ℕ}
    (hm1 : 1 ≤ m) (hmn : m ≤ n - 1) :
    IsPairedKDPCForOpposite (Gs j) (fun w => col (j, w)) m := by
  apply prop11c_proved _ _ (S.hcopy_eq j) (S.hcopy_pdpc j) hm1 hmn
  have h1 := S.horder
  have h2 := S.hn
  omega

/-! ## Terminal bookkeeping (Coleman's `w_j`) -/

/-- The pair indices with an endpoint in copy `j` (Coleman's set behind `w_j`). -/
def weldWSet {ell n : ℕ} (s t : Fin n → Fin ell × W) (j : Fin ell) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (s i).1 = j ∨ (t i).1 = j)

theorem weldWSet_card_le {ell n : ℕ} (s t : Fin n → Fin ell × W) (j : Fin ell) :
    (weldWSet s t j).card ≤ n :=
  le_trans (Finset.card_filter_le _ _) (by simp)

theorem mem_weldWSet {ell n : ℕ} {s t : Fin n → Fin ell × W} {j : Fin ell} {i : Fin n} :
    i ∈ weldWSet s t j ↔ (s i).1 = j ∨ (t i).1 = j := by
  simp [weldWSet]

/-- If `w_j = n` then every pair has an endpoint in copy `j`. -/
theorem weldWSet_touch_of_card {ell n : ℕ} {s t : Fin n → Fin ell × W} {j : Fin ell}
    (h : (weldWSet s t j).card = n) (i : Fin n) : (s i).1 = j ∨ (t i).1 = j := by
  have huniv : weldWSet s t j = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using h)
  have hi : i ∈ weldWSet s t j := huniv ▸ Finset.mem_univ i
  exact mem_weldWSet.mp hi

/-- `|S'_j| + |T_j| = w_j`: the source-only indices plus the target-touching indices. -/
theorem weldWSet_card_split_t {ell n : ℕ} (s t : Fin n → Fin ell × W) (j : Fin ell) :
    ((Finset.univ.filter (fun i => (s i).1 = j)) \
      (Finset.univ.filter (fun i => (t i).1 = j))).card
    + (Finset.univ.filter (fun i => (t i).1 = j)).card = (weldWSet s t j).card := by
  rw [Finset.card_sdiff_add_card]
  congr 1
  rw [weldWSet, Finset.filter_or]

/-- `|T'_j| + |S_j| = w_j`: the target-only indices plus the source-touching indices. -/
theorem weldWSet_card_split_s {ell n : ℕ} (s t : Fin n → Fin ell × W) (j : Fin ell) :
    ((Finset.univ.filter (fun i => (t i).1 = j)) \
      (Finset.univ.filter (fun i => (s i).1 = j))).card
    + (Finset.univ.filter (fun i => (s i).1 = j)).card = (weldWSet s t j).card := by
  rw [Finset.card_sdiff_add_card]
  congr 1
  rw [weldWSet, Finset.filter_or, Finset.union_comm]

/-! ## The greedy connector chooser (Coleman's inductive `v_i, u_i` selection)

For each split pair `i` in a processing set `D`, choose `v i` in the source copy (colored
`!b`) and its matching partner `u i` in the target copy, such that `v i` avoids all target
vertices of the source copy and all previously chosen `v`'s there, and `u i` avoids all
source vertices of the target copy and all previously chosen `u`'s there. Coleman's room
bound: each choice faces fewer than `2n − 1` exclusions. The count hypothesis refines
theirs: a previously chosen `v k` whose pair shares BOTH copies with pair `i` equals
`(M j j').symm (u k)`, so it is absorbed by the `u`-exclusion count (this is exactly the
saving Coleman uses in Case 6, where a naive per-side count would overshoot). -/

/-- Invariant of the greedy selection, restricted to the processed set `done`. -/
private structure GreedyInv {ell n : ℕ} (col : Fin ell × W → Bool) (b : Bool)
    (s t : Fin n → Fin ell × W) (M : Fin ell → Fin ell → (W ≃ W))
    (done : Finset (Fin n)) (v u : Fin n → W) : Prop where
  vcol : ∀ i ∈ done, col ((s i).1, v i) = !b
  partner : ∀ i ∈ done, u i = M (s i).1 (t i).1 (v i)
  vT : ∀ i ∈ done, ∀ k, (t k).1 = (s i).1 → v i ≠ (t k).2
  uS : ∀ i ∈ done, ∀ k, (s k).1 = (t i).1 → u i ≠ (s k).2
  vv : ∀ i ∈ done, ∀ k ∈ done, k ≠ i → (s k).1 = (s i).1 → v k ≠ v i
  uu : ∀ i ∈ done, ∀ k ∈ done, k ≠ i → (t k).1 = (t i).1 → u k ≠ u i

private theorem weld_greedy_aux {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (b : Bool)
    (s t : Fin n → Fin ell × W) (D : Finset (Fin n))
    (hsplit : ∀ i ∈ D, (s i).1 ≠ (t i).1)
    (hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < 2 * n - 1) :
    ∀ (m : ℕ) (done : Finset (Fin n)), done ⊆ D → (D \ done).card = m →
      ∀ v u : Fin n → W, GreedyInv col b s t M done v u →
      ∃ v' u' : Fin n → W, GreedyInv col b s t M D v' u'
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
          (Sset ∪ Uused).image (fun w => (M (s i).1 (t i).1).symm w)).card < 2 * n - 1 := by
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
      obtain ⟨y, hyc, hyF⟩ := S.exists_avoid (s i).1 (!b)
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
      refine weld_greedy_aux S b s t D hsplit hcount m (insert i done)
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
theorem weld_greedy {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (b : Bool)
    (s t : Fin n → Fin ell × W) (D : Finset (Fin n))
    (hsplit : ∀ i ∈ D, (s i).1 ≠ (t i).1)
    (hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < 2 * n - 1) :
    ∃ v u : Fin n → W,
      (∀ i ∈ D, col ((s i).1, v i) = !b) ∧
      (∀ i ∈ D, col ((t i).1, u i) = b) ∧
      (∀ i ∈ D, u i = M (s i).1 (t i).1 (v i)) ∧
      (∀ i ∈ D, ∀ k, (t k).1 = (s i).1 → v i ≠ (t k).2) ∧
      (∀ i ∈ D, ∀ k, (s k).1 = (t i).1 → u i ≠ (s k).2) ∧
      (∀ i ∈ D, ∀ k ∈ D, k ≠ i → (s k).1 = (s i).1 → v k ≠ v i) ∧
      (∀ i ∈ D, ∀ k ∈ D, k ≠ i → (t k).1 = (t i).1 → u k ≠ u i) := by
  classical
  have hW : Nonempty W := by
    have h1 := S.horder
    have h2 := S.hn
    have h3 : 0 < Fintype.card W := by omega
    exact Fintype.card_pos_iff.mp h3
  obtain ⟨w0⟩ := hW
  obtain ⟨v, u, hInv⟩ := weld_greedy_aux S b s t D hsplit hcount (D \ ∅).card ∅
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
  have hne := S.hproper _ _ hadj
  rw [hInv.vcol i hiD] at hne
  cases b <;> cases hcu : col ((t i).1, u i) <;> simp_all

/-! ## Per-copy inner families -/

theorem mem_map_pair {ell : ℕ} {j : Fin ell} {l : List W} {x : Fin ell × W} :
    x ∈ l.map (fun w => (j, w)) ↔ x.1 = j ∧ x.2 ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨rfl, hw⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.2, h2, Prod.ext h1.symm rfl⟩

/-- A `w_j`-PDPC of copy `j` for an on-`A` demand, reindexed by the pair indices themselves:
    a family of disjoint paths, one per index in `A`, jointly covering all of copy `j`. -/
theorem ColemanProp16Setting.inner_family {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) {b : Bool}
    (A : Finset (Fin n)) (hA1 : A.Nonempty) (hAn : A.card ≤ n - 1)
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
  have hm1 : 1 ≤ A.card := Finset.card_pos.mpr hA1
  obtain ⟨q, hqpath, hqcov, hqdisj⟩ := S.inner_cover j hm1 hAn _ _ hd
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

/-- The inner source endpoint of pair `i` seen from copy `j`: the source itself if it lives
    in copy `j`, else the connector `u i` (which lives in the target copy). -/
def wInnerS {ell n : ℕ} (s : Fin n → Fin ell × W) (u : Fin n → W) (j : Fin ell) (i : Fin n) : W :=
  if (s i).1 = j then (s i).2 else u i

/-- The inner target endpoint of pair `i` seen from copy `j`. -/
def wInnerT {ell n : ℕ} (t : Fin n → Fin ell × W) (v : Fin n → W) (j : Fin ell) (i : Fin n) : W :=
  if (t i).1 = j then (t i).2 else v i

theorem wInnerS_src {ell n : ℕ} {s : Fin n → Fin ell × W} {u : Fin n → W} {j : Fin ell}
    {i : Fin n} (h : (s i).1 = j) : wInnerS s u j i = (s i).2 := if_pos h

theorem wInnerS_conn {ell n : ℕ} {s : Fin n → Fin ell × W} {u : Fin n → W} {j : Fin ell}
    {i : Fin n} (h : (s i).1 ≠ j) : wInnerS s u j i = u i := if_neg h

theorem wInnerT_tgt {ell n : ℕ} {t : Fin n → Fin ell × W} {v : Fin n → W} {j : Fin ell}
    {i : Fin n} (h : (t i).1 = j) : wInnerT t v j i = (t i).2 := if_pos h

theorem wInnerT_conn {ell n : ℕ} {t : Fin n → Fin ell × W} {v : Fin n → W} {j : Fin ell}
    {i : Fin n} (h : (t i).1 ≠ j) : wInnerT t v j i = v i := if_neg h

end WeldInfra

end Brualdi.Ledger
