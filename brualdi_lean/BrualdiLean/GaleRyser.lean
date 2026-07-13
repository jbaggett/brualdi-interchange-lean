/-
# Gale–Ryser existence, self-contained (foundations-only)

`galeRyser_exists`: a margin class `MarginClass r s` is nonempty as soon as the total masses
agree and every column set carries no more mass than the rows can deliver to it:
`∑ r = ∑ s` and, for every `X ⊆` columns, `∑_{j∈X} s j ≤ ∑_i min (r i) |X|`.

This is the existence half of the Gale–Ryser theorem (Gale 1957; Ryser 1957), stated in the
column-set form the manuscript uses in §5 ("Line quotients as matroid base graphs"). It exists
in this development to support `AltProofs.lean`'s alternate route through the paper's printed
proof of Lemma 5.3; the mainline proof of the theorem does not use it.

The proof is a defect-repair argument rather than the textbook greedy induction (whose
invariant bookkeeping is delicate): start from a matrix with exact column sums, take one
minimizing the row-sum defect, and show a positive defect is impossible —

* if some sequence of single-cell moves can carry a unit from an over-full row to an
  under-full row (an augmenting path along the "feed" relation), the first move preserves
  both the column sums and the minimal defect while shortening the path, and a length-one
  path strictly improves the defect: induction on path length;
* if no such path exists, the columns supporting the rows reachable from an over-full row
  absorb more mass than `∑_i min (r i) |·|` allows: the hypothesis inequality applied to
  exactly that column set is violated.

Everything is foundations-only (`#print axioms galeRyser_exists` = propext,
Classical.choice, Quot.sound).
-/
import BrualdiLean.Basic

namespace Brualdi.Ledger

/-! ## Single-cell moves -/

/-- Move one unit from row `x` to row `y` inside column `c`. -/
private def grMove {m n : ℕ} (M : ZeroOneMat m n) (x y : Fin m) (c : Fin n) :
    ZeroOneMat m n :=
  fun i j => if i = x ∧ j = c then false else if i = y ∧ j = c then true else M i j

private theorem grMove_apply_other {m n : ℕ} {M : ZeroOneMat m n} {x y : Fin m}
    {c : Fin n} {i : Fin m} {j : Fin n} (h : ¬(i = x ∧ j = c)) (h' : ¬(i = y ∧ j = c)) :
    grMove M x y c i j = M i j := by
  simp [grMove, h, h']

/-- Split a sum over all rows into the `x` term, the `y` term, and the rest. -/
private theorem gr_sum_split_two {m : ℕ} {x y : Fin m} (hxy : x ≠ y) (g : Fin m → ℕ) :
    ∑ i, g i = g x + g y + ∑ i ∈ (Finset.univ.erase x).erase y, g i := by
  have hyA : y ∈ Finset.univ.erase x :=
    Finset.mem_erase.mpr ⟨fun h => hxy h.symm, Finset.mem_univ y⟩
  have h1 : ∑ i ∈ Finset.univ.erase x, g i + g x = ∑ i, g i :=
    Finset.sum_erase_add _ _ (Finset.mem_univ x)
  have h2 : ∑ i ∈ (Finset.univ.erase x).erase y, g i + g y = ∑ i ∈ Finset.univ.erase x, g i :=
    Finset.sum_erase_add _ _ hyA
  omega

private theorem grMove_colSum {m n : ℕ} {M : ZeroOneMat m n} {x y : Fin m} {c : Fin n}
    (hxy : x ≠ y) (hx : M x c = true) (hy : M y c = false) :
    ∀ j, colSum (grMove M x y c) j = colSum M j := by
  intro j
  by_cases hj : j = c
  · have hM := gr_sum_split_two (m := m) hxy (fun i => (if M i j then 1 else 0 : ℕ))
    have hM' := gr_sum_split_two (m := m) hxy
      (fun i => (if grMove M x y c i j then 1 else 0 : ℕ))
    have hrest_sum :
        ∑ i ∈ (Finset.univ.erase x).erase y, (if grMove M x y c i j then 1 else 0 : ℕ) =
          ∑ i ∈ (Finset.univ.erase x).erase y, (if M i j then 1 else 0 : ℕ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hiy : i ≠ y := (Finset.mem_erase.mp hi).1
      have hix : i ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [grMove_apply_other (fun h => hix h.1) (fun h => hiy h.1)]
    have hgx : (if grMove M x y c x j then 1 else 0 : ℕ) = 0 := by
      simp [grMove, hj]
    have hgy : (if grMove M x y c y j then 1 else 0 : ℕ) = 1 := by
      simp [grMove, hj, hxy.symm]
    have hMx : (if M x j then 1 else 0 : ℕ) = 1 := by rw [hj]; simp [hx]
    have hMy : (if M y j then 1 else 0 : ℕ) = 0 := by rw [hj]; simp [hy]
    show colSum (grMove M x y c) j = colSum M j
    rw [colSum, colSum]
    omega
  · unfold colSum
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [grMove_apply_other (fun h => hj h.2) (fun h => hj h.2)]

private theorem grMove_rowSum_x {m n : ℕ} {M : ZeroOneMat m n} {x y : Fin m} {c : Fin n}
    (hx : M x c = true) :
    rowSum (grMove M x y c) x + 1 = rowSum M x := by
  unfold rowSum
  have h1 : ∑ j ∈ Finset.univ.erase c, (if grMove M x y c x j then 1 else 0 : ℕ) +
      (if grMove M x y c x c then 1 else 0 : ℕ) = ∑ j, (if grMove M x y c x j then 1 else 0 : ℕ) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ c)
  have h2 : ∑ j ∈ Finset.univ.erase c, (if M x j then 1 else 0 : ℕ) +
      (if M x c then 1 else 0 : ℕ) = ∑ j, (if M x j then 1 else 0 : ℕ) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ c)
  have hrest : ∑ j ∈ Finset.univ.erase c, (if grMove M x y c x j then 1 else 0 : ℕ) =
      ∑ j ∈ Finset.univ.erase c, (if M x j then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjc : j ≠ c := (Finset.mem_erase.mp hj).1
    rw [grMove_apply_other (fun h => hjc h.2) (fun h => hjc h.2)]
  have hgc : (if grMove M x y c x c then 1 else 0 : ℕ) = 0 := by simp [grMove]
  have hMc : (if M x c then 1 else 0 : ℕ) = 1 := by simp [hx]
  omega

private theorem grMove_rowSum_y {m n : ℕ} {M : ZeroOneMat m n} {x y : Fin m} {c : Fin n}
    (hxy : x ≠ y) (hy : M y c = false) :
    rowSum (grMove M x y c) y = rowSum M y + 1 := by
  unfold rowSum
  have h1 : ∑ j ∈ Finset.univ.erase c, (if grMove M x y c y j then 1 else 0 : ℕ) +
      (if grMove M x y c y c then 1 else 0 : ℕ) = ∑ j, (if grMove M x y c y j then 1 else 0 : ℕ) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ c)
  have h2 : ∑ j ∈ Finset.univ.erase c, (if M y j then 1 else 0 : ℕ) +
      (if M y c then 1 else 0 : ℕ) = ∑ j, (if M y j then 1 else 0 : ℕ) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ c)
  have hrest : ∑ j ∈ Finset.univ.erase c, (if grMove M x y c y j then 1 else 0 : ℕ) =
      ∑ j ∈ Finset.univ.erase c, (if M y j then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjc : j ≠ c := (Finset.mem_erase.mp hj).1
    rw [grMove_apply_other (fun h => hjc h.2) (fun h => hjc h.2)]
  have hgc : (if grMove M x y c y c then 1 else 0 : ℕ) = 1 := by
    simp [grMove, hxy.symm]
  have hMc : (if M y c then 1 else 0 : ℕ) = 0 := by simp [hy]
  omega

private theorem grMove_rowSum_other {m n : ℕ} {M : ZeroOneMat m n} {x y : Fin m} {c : Fin n}
    {i : Fin m} (hix : i ≠ x) (hiy : i ≠ y) :
    rowSum (grMove M x y c) i = rowSum M i := by
  unfold rowSum
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [grMove_apply_other (fun h => hix h.1) (fun h => hiy h.1)]

/-! ## Defect -/

/-- The row-sum defect: the total distance of `M`'s row sums from the target `r`. -/
private def grDefect {m n : ℕ} (r : Fin m → ℕ) (M : ZeroOneMat m n) : ℕ :=
  ∑ i, ((rowSum M i - r i) + (r i - rowSum M i))

private theorem grDefect_eq_zero {m n : ℕ} {r : Fin m → ℕ} {M : ZeroOneMat m n}
    (h : grDefect r M = 0) : ∀ i, rowSum M i = r i := by
  intro i
  have hz := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  omega

/-! ## Feeds and augmenting paths -/

/-- Row `x` can feed row `y`: some column holds a `1` in `x` and a `0` in `y`. -/
private def grFeed {m n : ℕ} (M : ZeroOneMat m n) (x y : Fin m) : Prop :=
  ∃ c, M x c = true ∧ M y c = false

/-- A feed path of length `t` from `a` to `b`. -/
private def grPath {m n : ℕ} (M : ZeroOneMat m n) (a b : Fin m) (t : ℕ) : Prop :=
  ∃ f : ℕ → Fin m, f 0 = a ∧ f t = b ∧ ∀ i, i < t → grFeed M (f i) (f (i + 1))

/-! ## The stuck-minimum counting contradiction (no augmenting path) -/

private theorem gr_stuck {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hdom : ∀ X : Finset (Fin n), ∑ j ∈ X, s j ≤ ∑ i, min (r i) X.card)
    (M : ZeroOneMat m n) (hMcol : ∀ j, colSum M j = s j)
    (a : Fin m) (ha : r a < rowSum M a)
    (hreach_not_under : ∀ y, (∃ t, grPath M a y t) → r y ≤ rowSum M y) :
    False := by
  classical
  -- rows reachable from `a`, and the columns they support
  set S : Finset (Fin m) := Finset.univ.filter (fun y => ∃ t, grPath M a y t) with hSdef
  have haS : a ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨0, fun _ => a, rfl, rfl, ?_⟩⟩
    intro i hi
    omega
  have hclosed : ∀ x ∈ S, ∀ y, grFeed M x y → y ∈ S := by
    intro x hx y hfeed
    obtain ⟨t, f, hf0, hft, hstep⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ y,
      ⟨t + 1, fun i => if i ≤ t then f i else y, by simp [hf0], by
        have h : ¬(t + 1 ≤ t) := by omega
        simp [h], ?_⟩⟩
    intro i hi
    by_cases hit : i < t
    · have h1 : i ≤ t := le_of_lt hit
      have h2 : i + 1 ≤ t := hit
      simpa [h1, h2] using hstep i hit
    · have hieq : i = t := by omega
      subst hieq
      have h1 : i ≤ i := le_refl i
      have h2 : ¬(i + 1 ≤ i) := by omega
      simpa [h1, h2, hft] using hfeed
  set Cs : Finset (Fin n) := Finset.univ.filter (fun c => ∃ x ∈ S, M x c = true) with hCdef
  -- rows outside S are full on Cs
  have hfull : ∀ y, y ∉ S → ∀ c ∈ Cs, M y c = true := by
    intro y hy c hc
    obtain ⟨x, hxS, hxc⟩ := (Finset.mem_filter.mp hc).2
    by_contra hyc
    exact hy (hclosed x hxS y ⟨c, hxc, by simpa using hyc⟩)
  -- rows inside S have all their mass on Cs
  have hsupp : ∀ x ∈ S, ∀ c, M x c = true → c ∈ Cs := by
    intro x hx c hxc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨x, hx, hxc⟩⟩
  -- count the mass on Cs
  have hswap : ∑ c ∈ Cs, colSum M c = ∑ i, ∑ c ∈ Cs, (if M i c then 1 else 0 : ℕ) := by
    unfold colSum
    exact Finset.sum_comm
  have hinS : ∀ x ∈ S, ∑ c ∈ Cs, (if M x c then 1 else 0 : ℕ) = rowSum M x := by
    intro x hx
    unfold rowSum
    refine Finset.sum_subset (Finset.subset_univ Cs) ?_
    intro c _ hc
    have : ¬ M x c = true := fun h => hc (hsupp x hx c h)
    simp [this]
  have houtS : ∀ y, y ∉ S → ∑ c ∈ Cs, (if M y c then 1 else 0 : ℕ) = Cs.card := by
    intro y hy
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl ?_
    intro c hc
    simp [hfull y hy c hc]
  -- pointwise: each row contributes at least min (r i) |Cs|, strictly more at `a`
  have hpoint : ∀ i, min (r i) Cs.card ≤ ∑ c ∈ Cs, (if M i c then 1 else 0 : ℕ) := by
    intro i
    by_cases hi : i ∈ S
    · rw [hinS i hi]
      exact le_trans (min_le_left _ _)
        (hreach_not_under i (Finset.mem_filter.mp hi).2)
    · rw [houtS i hi]
      exact min_le_right _ _
  have hstrict : min (r a) Cs.card < ∑ c ∈ Cs, (if M a c then 1 else 0 : ℕ) := by
    rw [hinS a haS]
    exact lt_of_le_of_lt (min_le_left _ _) ha
  have hlt : ∑ i, min (r i) Cs.card < ∑ i, ∑ c ∈ Cs, (if M i c then 1 else 0 : ℕ) :=
    Finset.sum_lt_sum (fun i _ => hpoint i) ⟨a, Finset.mem_univ a, hstrict⟩
  have hcolmass : ∑ c ∈ Cs, s c = ∑ c ∈ Cs, colSum M c :=
    Finset.sum_congr rfl (fun c _ => (hMcol c).symm)
  have := hdom Cs
  omega

/-! ## The augmenting-path induction -/

private theorem gr_no_aug_path {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (Dmin : ℕ)
    (hDmin : ∀ M' : ZeroOneMat m n, (∀ j, colSum M' j = s j) → Dmin ≤ grDefect r M') :
    ∀ t : ℕ, ∀ M : ZeroOneMat m n, (∀ j, colSum M j = s j) → grDefect r M = Dmin →
      ∀ a b : Fin m, r a < rowSum M a → rowSum M b < r b → grPath M a b t → False := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro M hMcol hMD a b ha hb hpath
    obtain ⟨f, hf0, hft, hstep⟩ := hpath
    -- length 0: a = b is both over- and under-full
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      rw [hf0] at hft
      subst hft
      omega
    -- an under-full intermediate row gives a shorter path (prefix)
    by_cases hunder : ∃ i, 0 < i ∧ i < t ∧ rowSum M (f i) < r (f i)
    · obtain ⟨i, hi0, hit, hu⟩ := hunder
      exact ih i hit M hMcol hMD a (f i) ha hu
        ⟨f, hf0, rfl, fun j hj => hstep j (by omega)⟩
    -- an over-full intermediate row gives a shorter path (suffix)
    by_cases hover : ∃ i, 0 < i ∧ i < t ∧ r (f i) < rowSum M (f i)
    · obtain ⟨i, hi0, hit, ho⟩ := hover
      refine ih (t - i) (by omega) M hMcol hMD (f i) b ho hb
        ⟨fun j => f (j + i), by simp, by
          show f (t - i + i) = b
          rw [Nat.sub_add_cancel (le_of_lt hit)]; exact hft, ?_⟩
      intro j hj
      have := hstep (j + i) (by omega)
      simpa [Nat.add_right_comm] using this
    -- a repeat of f 1 gives a shorter path (splice)
    by_cases hrep : ∃ j, 2 ≤ j ∧ j ≤ t ∧ f j = f 1
    · obtain ⟨j, hj2, hjt, hjf⟩ := hrep
      refine ih (t - (j - 1)) (by omega) M hMcol hMD a b ha hb
        ⟨fun i => if i = 0 then a else f (i + (j - 1)), by simp, ?_, ?_⟩
      · have h1 : ¬(t - (j - 1) = 0) := by omega
        have h2 : t - (j - 1) + (j - 1) = t := by omega
        simp [h1, h2, hft]
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          have h1 : (0 : ℕ) + 1 = 1 := rfl
          have hne : ¬(1 = 0) := by omega
          have h1j : 1 + (j - 1) = j := by omega
          have := hstep 0 (by omega)
          rw [hf0] at this
          simpa [hne, h1j, hjf] using this
        · have hne : ¬(i + 1 = 0) := by omega
          have := hstep (i + (j - 1)) (by omega)
          have harith : i + 1 + (j - 1) = i + (j - 1) + 1 := by omega
          simpa [hi0, hne, harith] using this
    -- main case: build the move on the first edge
    obtain ⟨c₀, hac₀, hx₁c₀⟩ := by
      have := hstep 0 htpos
      rwa [hf0] at this
    -- t = 1: a feeds b directly, and the defect drops by 2
    rcases Nat.eq_or_lt_of_le htpos with ht1 | ht2
    · have hf1b : f 1 = b := by rw [← ht1] at hft; exact hft
      rw [hf1b] at hx₁c₀
      have hab : a ≠ b := fun h => by rw [h] at ha; omega
      set M' := grMove M a b c₀ with hM'def
      have hM'col : ∀ j, colSum M' j = s j := fun j => by
        rw [hM'def, grMove_colSum hab hac₀ hx₁c₀]; exact hMcol j
      have hra : rowSum M' a + 1 = rowSum M a := grMove_rowSum_x hac₀
      have hrb : rowSum M' b = rowSum M b + 1 := grMove_rowSum_y hab hx₁c₀
      have hDsplit := gr_sum_split_two (m := m) hab
        (fun i => ((rowSum M i - r i) + (r i - rowSum M i)))
      have hDsplit' := gr_sum_split_two (m := m) hab
        (fun i => ((rowSum M' i - r i) + (r i - rowSum M' i)))
      have hrest : ∑ i ∈ (Finset.univ.erase a).erase b,
          ((rowSum M' i - r i) + (r i - rowSum M' i)) =
            ∑ i ∈ (Finset.univ.erase a).erase b,
              ((rowSum M i - r i) + (r i - rowSum M i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hib : i ≠ b := (Finset.mem_erase.mp hi).1
        have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        rw [grMove_rowSum_other hia hib]
      have hlt : grDefect r M' < Dmin := by
        have hDM : grDefect r M = Dmin := hMD
        unfold grDefect at hDM ⊢
        omega
      exact absurd (hDmin M' hM'col) (by omega)
    -- t ≥ 2: move the first edge, keep the defect, shorten the path
    · set x₁ := f 1 with hx₁def
      have hx₁mid : 0 < 1 ∧ 1 < t := ⟨by omega, ht2⟩
      have hx₁notunder : ¬ rowSum M x₁ < r x₁ := fun h =>
        hunder ⟨1, hx₁mid.1, hx₁mid.2, h⟩
      have hx₁notover : ¬ r x₁ < rowSum M x₁ := fun h =>
        hover ⟨1, hx₁mid.1, hx₁mid.2, h⟩
      have hx₁eq : rowSum M x₁ = r x₁ := by omega
      have hax₁ : a ≠ x₁ := fun h => by rw [h] at ha; omega
      set M' := grMove M a x₁ c₀ with hM'def
      have hM'col : ∀ j, colSum M' j = s j := fun j => by
        rw [hM'def, grMove_colSum hax₁ hac₀ hx₁c₀]; exact hMcol j
      have hra : rowSum M' a + 1 = rowSum M a := grMove_rowSum_x hac₀
      have hrx₁ : rowSum M' x₁ = rowSum M x₁ + 1 := grMove_rowSum_y hax₁ hx₁c₀
      have hDsplit := gr_sum_split_two (m := m) hax₁
        (fun i => ((rowSum M i - r i) + (r i - rowSum M i)))
      have hDsplit' := gr_sum_split_two (m := m) hax₁
        (fun i => ((rowSum M' i - r i) + (r i - rowSum M' i)))
      have hrest : ∑ i ∈ (Finset.univ.erase a).erase x₁,
          ((rowSum M' i - r i) + (r i - rowSum M' i)) =
            ∑ i ∈ (Finset.univ.erase a).erase x₁,
              ((rowSum M i - r i) + (r i - rowSum M i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hix₁ : i ≠ x₁ := (Finset.mem_erase.mp hi).1
        have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        rw [grMove_rowSum_other hia hix₁]
      have hM'D : grDefect r M' = Dmin := by
        have hle := hDmin M' hM'col
        have hDM : grDefect r M = Dmin := hMD
        unfold grDefect at hDM hle ⊢
        omega
      -- endpoints in M'
      have hb_a : b ≠ a := fun h => by rw [h] at hb; omega
      have hb_x₁ : b ≠ x₁ := fun h => by rw [h, hx₁eq] at hb; omega
      have hb' : rowSum M' b < r b := by
        rw [grMove_rowSum_other hb_a hb_x₁]; exact hb
      have hx₁' : r x₁ < rowSum M' x₁ := by omega
      -- the tail is a path in M'
      have htail : grPath M' x₁ b (t - 1) := by
        refine ⟨fun i => f (i + 1), by simp [hx₁def], ?_, ?_⟩
        · show f (t - 1 + 1) = b
          have : t - 1 + 1 = t := by omega
          rw [this, hft]
        · intro i hi
          obtain ⟨c, hgive, hrecv⟩ := hstep (i + 1) (by omega)
          refine ⟨c, ?_, ?_⟩
          · -- the giver cell survives (or was upgraded to true at (x₁, c₀))
            show M' (f (i + 1)) c = true
            by_cases hcell : f (i + 1) = x₁ ∧ c = c₀
            · rw [hM'def]
              have : ¬(f (i + 1) = a ∧ c = c₀) := fun h => hax₁ (h.1 ▸ hcell.1.symm ▸ rfl)
              simp [grMove, hcell.1, hcell.2, hax₁.symm]
            · have hnota : ¬(f (i + 1) = a ∧ c = c₀) := by
                rintro ⟨hfa, -⟩
                have : 0 < i + 1 ∧ i + 1 < t := ⟨by omega, by omega⟩
                exact hover ⟨i + 1, this.1, this.2, by rw [hfa]; exact ha⟩
              rw [hM'def, grMove_apply_other hnota hcell]
              exact hgive
          · -- the receiver cell survives: it is neither (a, c₀) nor (x₁, c₀)
            have hnotx₁ : ¬(f (i + 2) = x₁ ∧ c = c₀) := by
              rintro ⟨hfx, -⟩
              exact hrep ⟨i + 2, by omega, by omega, hfx⟩
            have hnota : ¬(f (i + 2) = a ∧ c = c₀) := by
              rintro ⟨hfa, -⟩
              by_cases hi2t : i + 2 = t
              · rw [hi2t, hft] at hfa
                rw [hfa] at hb_a
                exact hb_a rfl
              · exact hover ⟨i + 2, by omega, by omega, by rw [hfa]; exact ha⟩
            show M' (f (i + 1 + 1)) c = false
            have harith : i + 1 + 1 = i + 2 := by omega
            rw [harith] at hrecv ⊢
            rw [hM'def, grMove_apply_other hnota hnotx₁]
            exact hrecv
      exact ih (t - 1) (by omega) M' hM'col hM'D x₁ b hx₁' hb' htail

/-! ## The existence theorem -/

/-- **Gale–Ryser, existence half** (Gale 1957; Ryser 1957) — self-contained, foundations-only.
    If the row and column masses agree in total and every set `X` of columns demands no more
    than the rows can supply to `|X|` columns, the margin class is nonempty. -/
theorem galeRyser_exists {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hsum : ∑ i, r i = ∑ j, s j)
    (hdom : ∀ X : Finset (Fin n), ∑ j ∈ X, s j ≤ ∑ i, min (r i) X.card) :
    Nonempty (MarginClass r s) := by
  classical
  -- each column fits in its m rows
  have hsm : ∀ j, s j ≤ m := by
    intro j
    have h := hdom {j}
    have hle : ∑ i : Fin m, min (r i) ({j} : Finset (Fin n)).card ≤ ∑ i : Fin m, 1 :=
      Finset.sum_le_sum (fun i _ => by simp)
    simp only [Finset.sum_singleton, Finset.card_singleton] at h
    simpa using le_trans h (by simpa using hle)
  -- a matrix with exact column sums
  have hM₀ : ∃ M : ZeroOneMat m n, ∀ j, colSum M j = s j := by
    refine ⟨fun i j => decide ((i : ℕ) < s j), ?_⟩
    intro j
    unfold colSum
    have : ∀ i : Fin m, (if (decide ((i : ℕ) < s j)) then 1 else 0 : ℕ) =
        (if (i : ℕ) < s j then 1 else 0 : ℕ) := by
      intro i
      by_cases h : (i : ℕ) < s j <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.card_filter]
    trans (Finset.range (s j)).card
    · refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i _ i' _ h
        exact Fin.ext h
      · intro t ht
        have htj : t < s j := Finset.mem_range.mp ht
        have htm : t < m := lt_of_lt_of_le htj (hsm j)
        exact ⟨⟨t, htm⟩, by simp [htj], rfl⟩
    · exact Finset.card_range (s j)
  -- minimize the defect over column-exact matrices
  set C : Finset (ZeroOneMat m n) :=
    Finset.univ.filter (fun M => ∀ j, colSum M j = s j) with hCdef
  have hCne : C.Nonempty := by
    obtain ⟨M₀, hM₀⟩ := hM₀
    exact ⟨M₀, Finset.mem_filter.mpr ⟨Finset.mem_univ M₀, hM₀⟩⟩
  obtain ⟨M, hMC, hMmin⟩ := Finset.exists_min_image C (grDefect r) hCne
  have hMcol : ∀ j, colSum M j = s j := (Finset.mem_filter.mp hMC).2
  have hDmin : ∀ M' : ZeroOneMat m n, (∀ j, colSum M' j = s j) → grDefect r M ≤ grDefect r M' :=
    fun M' hM' => hMmin M' (Finset.mem_filter.mpr ⟨Finset.mem_univ M', hM'⟩)
  -- a positive defect is impossible
  by_cases hD : grDefect r M = 0
  · exact ⟨⟨M, grDefect_eq_zero hD, hMcol⟩⟩
  · exfalso
    -- total masses agree
    have htotal : ∑ i, rowSum M i = ∑ i, r i := by
      have hrc : ∑ i, rowSum M i = ∑ j, colSum M j := by
        unfold rowSum colSum
        exact Finset.sum_comm
      rw [hrc, Finset.sum_congr rfl (fun j _ => hMcol j), ← hsum]
    -- an over-full and an under-full row exist
    have hex : ∃ i, rowSum M i ≠ r i := by
      by_contra hno
      push_neg at hno
      exact hD (by unfold grDefect; exact Finset.sum_eq_zero (fun i _ => by rw [hno i]; omega))
    obtain ⟨i₀, hi₀⟩ := hex
    have hover : ∃ a, r a < rowSum M a := by
      by_contra hno
      push_neg at hno
      have hunder : rowSum M i₀ < r i₀ := lt_of_le_of_ne (hno i₀) hi₀
      have hlt : ∑ i, rowSum M i < ∑ i, r i :=
        Finset.sum_lt_sum (fun i _ => hno i) ⟨i₀, Finset.mem_univ i₀, hunder⟩
      omega
    obtain ⟨a, ha⟩ := hover
    -- either every reachable row is not under-full (counting contradiction), or an
    -- augmenting path exists (path contradiction)
    by_cases hreach : ∀ y, (∃ t, grPath M a y t) → r y ≤ rowSum M y
    · exact gr_stuck r s hdom M hMcol a ha hreach
    · push_neg at hreach
      obtain ⟨b, ⟨t, hpath⟩, hb⟩ := hreach
      exact gr_no_aug_path r s (grDefect r M) hDmin t M hMcol rfl a b ha hb hpath

end Brualdi.Ledger
