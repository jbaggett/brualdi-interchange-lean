/-
  Brualdi-MH -- Ryser 2-switch existence (Tier-2 discharge of `interchange_has_edge`).

  Goal: a nontrivial interchange graph has an edge. Transported across the interchange
  isomorphism, this is the pure fact that among two distinct equal-margin (0,1)-matrices,
  one contains a *switchable* 2x2 block (Ryser's classical 2-switch), which yields an
  interchange edge. This file supplies the reduction; the core combinatorial lemma
  `switchable_block` is the Tier-2 target (currently `sorry`).
-/
import BrualdiLean.Coleman
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Brualdi.Ryser

open Brualdi Brualdi.Ledger

variable {m n : ℕ}

/-! ### Switchable blocks and the interchanged matrix. -/

/-- A switchable 2x2 block of `M`: distinct rows `i, i'`, distinct cols `j, j'`, with the
    `[[1,0],[0,1]]` pattern (`M i j = M i' j' = true`, `M i j' = M i' j = false`). -/
def SwitchBlock (M : ZeroOneMat m n) (i i' : Fin m) (j j' : Fin n) : Prop :=
  i ≠ i' ∧ j ≠ j' ∧
    M i j = true ∧ M i' j' = true ∧ M i j' = false ∧ M i' j = false

/-- `M` with a switchable block flipped to `[[0,1],[1,0]]`. -/
def switchMat (M : ZeroOneMat m n) (i i' : Fin m) (j j' : Fin n) : ZeroOneMat m n :=
  fun a b =>
    if a = i ∧ b = j then false
    else if a = i' ∧ b = j' then false
    else if a = i ∧ b = j' then true
    else if a = i' ∧ b = j then true
    else M a b

/-- Flipping a switchable block is a genuine interchange move. -/
theorem switch_interchange {M : ZeroOneMat m n} {i i' : Fin m} {j j' : Fin n}
    (hb : SwitchBlock M i i' j j') : Interchange M (switchMat M i i' j j') := by
  obtain ⟨hii, hjj, hMij, hMi'j', hMij', hMi'j⟩ := hb
  refine ⟨i, i', j, j', hii, hjj, hMij, hMi'j', hMij', hMi'j, ?_, ?_, ?_, ?_, ?_⟩
  · -- switchMat i j = false
    simp only [switchMat]; split_ifs <;> simp_all
  · -- switchMat i' j' = false
    simp only [switchMat]; split_ifs <;> simp_all
  · -- switchMat i j' = true
    simp only [switchMat]; split_ifs <;> simp_all
  · -- switchMat i' j = true
    simp only [switchMat]; split_ifs <;> simp_all
  · -- outside the block: unchanged
    intro a b hab
    simp only [switchMat]
    split_ifs with h1 h2 h3 h4
    · exact absurd ⟨Or.inl h1.1, Or.inl h1.2⟩ hab
    · exact absurd ⟨Or.inr h2.1, Or.inr h2.2⟩ hab
    · exact absurd ⟨Or.inl h3.1, Or.inr h3.2⟩ hab
    · exact absurd ⟨Or.inr h4.1, Or.inl h4.2⟩ hab
    · rfl

/-- The switched matrix genuinely differs from `M` (they disagree at cell `(i, j)`). -/
theorem switchMat_ne {M : ZeroOneMat m n} {i i' : Fin m} {j j' : Fin n}
    (hb : SwitchBlock M i i' j j') : switchMat M i i' j j' ≠ M := by
  intro h
  have hcell : switchMat M i i' j j' i j = M i j := congrFun (congrFun h i) j
  rw [hb.2.2.1] at hcell            -- M i j = true
  simp [switchMat] at hcell

/-! ### An interchange move preserves the margins. -/

/-- Two `Bool` functions that agree off a 2-element set `{x, x'}` and whose contributions on
    that set are equal have equal weighted (0/1) sums. -/
private theorem sum_bool_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : ι → Bool} {x x' : ι} (hxx : x ≠ x')
    (hxsum : (if f x then 1 else 0) + (if f x' then 1 else 0)
           = (if g x then 1 else 0) + (if g x' then (1 : ℕ) else 0))
    (hrest : ∀ b, b ≠ x → b ≠ x' → f b = g b) :
    (∑ b, if f b then 1 else 0) = ∑ b, if g b then (1 : ℕ) else 0 := by
  have hx'mem : x' ∈ (univ.erase x) := mem_erase.mpr ⟨hxx.symm, mem_univ _⟩
  have hsplit : ∀ h : ι → Bool,
      (∑ b, if h b then 1 else 0)
        = ((if h x then 1 else 0) + (if h x' then 1 else 0))
            + ∑ b ∈ (univ.erase x).erase x', (if h b then (1 : ℕ) else 0) := by
    intro h
    rw [← add_sum_erase univ (fun b => if h b then (1 : ℕ) else 0) (mem_univ x),
        ← add_sum_erase (univ.erase x) (fun b => if h b then (1 : ℕ) else 0) hx'mem,
        ← add_assoc]
  rw [hsplit f, hsplit g, hxsum]
  congr 1
  apply sum_congr rfl
  intro b hb
  have hbx : b ≠ x := (mem_erase.mp (mem_of_mem_erase hb)).1
  have hbx' : b ≠ x' := (mem_erase.mp hb).1
  rw [hrest b hbx hbx']

/-- An interchange move preserves both row and column sums, hence the margins. -/
theorem interchange_preserves_margins {M M' : ZeroOneMat m n} (h : Interchange M M')
    {r : Fin m → ℕ} {s : Fin n → ℕ} (hM : HasMargins r s M) : HasMargins r s M' := by
  obtain ⟨i, i', j, j', hii, hjj, hMij, hMi'j', hMij', hMi'j,
          hM'ij, hM'i'j', hM'ij', hM'i'j, hout⟩ := h
  refine ⟨fun i₀ => ?_, fun j₀ => ?_⟩
  · -- rows: rowSum M' i₀ = r i₀
    have hswap : rowSum M' i₀ = rowSum M i₀ := by
      unfold rowSum
      by_cases hi₀i : i₀ = i
      · subst hi₀i
        exact sum_bool_swap hjj (by simp [hM'ij, hM'ij', hMij, hMij'])
          (fun b hbj hbj' => hout i₀ b (by rintro ⟨_, (rfl | rfl)⟩ <;> simp_all))
      · by_cases hi₀i' : i₀ = i'
        · subst hi₀i'
          exact sum_bool_swap hjj (by simp [hM'i'j, hM'i'j', hMi'j, hMi'j'])
            (fun b hbj hbj' => hout i₀ b (by rintro ⟨_, (rfl | rfl)⟩ <;> simp_all))
        · apply sum_congr rfl
          intro b _
          rw [hout i₀ b (by rintro ⟨(rfl | rfl), _⟩ <;> simp_all)]
    rw [hswap]; exact hM.1 i₀
  · -- columns: colSum M' j₀ = s j₀
    have hswap : colSum M' j₀ = colSum M j₀ := by
      unfold colSum
      by_cases hj₀j : j₀ = j
      · subst hj₀j
        exact sum_bool_swap hii (by simp [hM'ij, hM'i'j, hMij, hMi'j])
          (fun a haj haj' => hout a j₀ (by rintro ⟨(rfl | rfl), _⟩ <;> simp_all))
      · by_cases hj₀j' : j₀ = j'
        · subst hj₀j'
          exact sum_bool_swap hii (by simp [hM'ij', hM'i'j', hMij', hMi'j'])
            (fun a haj haj' => hout a j₀ (by rintro ⟨(rfl | rfl), _⟩ <;> simp_all))
        · apply sum_congr rfl
          intro a _
          rw [hout a j₀ (by rintro ⟨_, (rfl | rfl)⟩ <;> simp_all)]
    rw [hswap]; exact hM.2 j₀

/-! ### The core combinatorial lemma (Tier-2 target).

    Two distinct equal-margin (0,1)-matrices ⇒ one contains a switchable block. We walk the
    difference digraph (a `+cell` `(i,j)` has `M=1, M'=0`; a `−cell` has `M=0, M'=1`), which
    is balanced because the margins agree; pigeonhole gives a simple directed cycle; the
    "first descent" along the start row extracts the block. -/

/-- A boolean sequence that is `true` at `p` and `false` at `e ≥ p` has a `true → false`
    descent somewhere in `[p, e)`. -/
private theorem bool_descent (g : ℕ → Bool) :
    ∀ e p, p ≤ e → g p = true → g e = false →
      ∃ t, p ≤ t ∧ t < e ∧ g t = true ∧ g (t + 1) = false := by
  intro e
  induction e with
  | zero =>
    intro p hpe hp he
    have hp0 : p = 0 := Nat.le_zero.mp hpe
    subst hp0
    rw [hp] at he
    exact absurd he (by decide)
  | succ e ih =>
    intro p hpe hp he
    by_cases hge : g e = true
    · refine ⟨e, ?_, Nat.lt_succ_self e, hge, he⟩
      by_contra hc
      have hpe1 : p = e + 1 := by omega
      rw [hpe1, he] at hp
      exact absurd hp (by decide)
    · have hge' : g e = false := by simpa using hge
      rcases Nat.lt_or_ge p (e + 1) with h | h
      · obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih p (Nat.lt_succ_iff.mp h) hp hge'
        exact ⟨t, ht1, Nat.lt_succ_of_lt ht2, ht3, ht4⟩
      · have hpe1 : p = e + 1 := by omega
        rw [hpe1, he] at hp
        exact absurd hp (by decide)

/-- `(i,j)` is a `+cell`: `M` has a 1 there, `M'` a 0. -/
def IsPlus (M M' : ZeroOneMat m n) (q : Fin m × Fin n) : Prop :=
  M q.1 q.2 = true ∧ M' q.1 q.2 = false

/-- Row balance: equal row sums ⇒ `#(+cells) = #(−cells)` in each row. -/
private theorem row_balance {M M' : ZeroOneMat m n} (hrow : ∀ i, rowSum M i = rowSum M' i)
    (i : Fin m) :
    (univ.filter (fun j => M i j = true ∧ M' i j = false)).card
      = (univ.filter (fun j => M i j = false ∧ M' i j = true)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have hpt : ∀ j : Fin n,
      (if M i j = true then 1 else 0) + (if M i j = false ∧ M' i j = true then (1 : ℕ) else 0)
        = (if M' i j = true then 1 else 0) + (if M i j = true ∧ M' i j = false then 1 else 0) := by
    intro j; cases M i j <;> cases M' i j <;> simp
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin n))) => hpt j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hrr : (∑ j, if M i j = true then (1 : ℕ) else 0)
           = (∑ j, if M' i j = true then 1 else 0) := hrow i
  omega

/-- Column balance: equal column sums ⇒ `#(+cells) = #(−cells)` in each column. -/
private theorem col_balance {M M' : ZeroOneMat m n} (hcol : ∀ j, colSum M j = colSum M' j)
    (j : Fin n) :
    (univ.filter (fun i => M i j = true ∧ M' i j = false)).card
      = (univ.filter (fun i => M i j = false ∧ M' i j = true)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have hpt : ∀ i : Fin m,
      (if M i j = true then 1 else 0) + (if M i j = false ∧ M' i j = true then (1 : ℕ) else 0)
        = (if M' i j = true then 1 else 0) + (if M i j = true ∧ M' i j = false then 1 else 0) := by
    intro i; cases M i j <;> cases M' i j <;> simp
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (univ : Finset (Fin m))) => hpt i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hrr : (∑ i, if M i j = true then (1 : ℕ) else 0)
           = (∑ i, if M' i j = true then 1 else 0) := hcol j
  omega

/-- A distinct pair of matrices with a common column margin has a `+cell`. -/
private theorem exists_plus {M M' : ZeroOneMat m n}
    (hcol : ∀ j, colSum M j = colSum M' j) (hne : M ≠ M') :
    ∃ q, IsPlus M M' q := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ M' i j := by
    by_contra hc
    push_neg at hc
    exact hne (funext fun i => funext fun j => hc i j)
  rcases Bool.eq_false_or_eq_true (M i j) with hM | hM
  · -- `(i,j)` is itself a `+cell`
    have hM' : M' i j = false := by
      rcases Bool.eq_false_or_eq_true (M' i j) with h | h
      · exact absurd (hM.trans h.symm) hij
      · exact h
    exact ⟨(i, j), hM, hM'⟩
  · -- `(i,j)` is a `−cell`; column balance yields a `+cell`
    have hM' : M' i j = true := by
      rcases Bool.eq_false_or_eq_true (M' i j) with h | h
      · exact h
      · exact absurd (hM.trans h.symm) hij
    have hbal := col_balance hcol j
    have hmem : i ∈ univ.filter (fun i => M i j = false ∧ M' i j = true) := by
      simp [Finset.mem_filter, hM, hM']
    have hpos : 0 < (univ.filter (fun i => M i j = false ∧ M' i j = true)).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    rw [← hbal] at hpos
    obtain ⟨i', hi'⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter] at hi'
    exact ⟨(i', j), hi'.2⟩

/-- **The step.** From a `+cell` `(i,j)` the balance gives a `−cell` `(i',j)` in the same
    column (`i' ≠ i`), and then a `+cell` `(i',j')` in that new row (`j' ≠ j`). -/
private theorem plus_step {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    {q : Fin m × Fin n} (hq : IsPlus M M' q) :
    ∃ q', IsPlus M M' q' ∧ M q'.1 q.2 = false ∧ q'.1 ≠ q.1 ∧ q'.2 ≠ q.2 := by
  obtain ⟨hMq, hM'q⟩ := hq
  -- column `q.2`: the `+cell` `(q.1, q.2)` forces a `−cell` `(i', q.2)`
  have hbalc := col_balance hcol q.2
  have hmem1 : q.1 ∈ univ.filter (fun i => M i q.2 = true ∧ M' i q.2 = false) := by
    simp [Finset.mem_filter, hMq, hM'q]
  have hpos1 : 0 < (univ.filter (fun i => M i q.2 = true ∧ M' i q.2 = false)).card :=
    Finset.card_pos.mpr ⟨q.1, hmem1⟩
  rw [hbalc] at hpos1
  obtain ⟨i', hi'⟩ := Finset.card_pos.mp hpos1
  simp only [Finset.mem_filter] at hi'
  obtain ⟨hMi', hM'i'⟩ := hi'.2
  have hi'ne : i' ≠ q.1 := by
    intro h; rw [h, hMq] at hMi'; exact absurd hMi' (by decide)
  -- row `i'`: the `−cell` `(i', q.2)` forces a `+cell` `(i', j')`
  have hbalr := row_balance hrow i'
  have hmem2 : q.2 ∈ univ.filter (fun j => M i' j = false ∧ M' i' j = true) := by
    simp [Finset.mem_filter, hMi', hM'i']
  have hpos2 : 0 < (univ.filter (fun j => M i' j = false ∧ M' i' j = true)).card :=
    Finset.card_pos.mpr ⟨q.2, hmem2⟩
  rw [← hbalr] at hpos2
  obtain ⟨j', hj'⟩ := Finset.card_pos.mp hpos2
  simp only [Finset.mem_filter] at hj'
  obtain ⟨hMj', hM'j'⟩ := hj'.2
  have hj'ne : j' ≠ q.2 := by
    intro h; rw [h, hMi'] at hMj'; exact absurd hMj' (by decide)
  exact ⟨(i', j'), ⟨hMj', hM'j'⟩, hMi', hi'ne, hj'ne⟩

/-- The choice function turning each `+cell` into the next one along the walk. -/
private noncomputable def stepFun {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    (P : {q // IsPlus M M' q}) : {q // IsPlus M M' q} :=
  ⟨(plus_step hrow hcol P.2).choose, (plus_step hrow hcol P.2).choose_spec.1⟩

private theorem stepFun_link {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    (P : {q // IsPlus M M' q}) : M (stepFun hrow hcol P).1.1 P.1.2 = false :=
  (plus_step hrow hcol P.2).choose_spec.2.1

private theorem stepFun_rowNe {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    (P : {q // IsPlus M M' q}) : (stepFun hrow hcol P).1.1 ≠ P.1.1 :=
  (plus_step hrow hcol P.2).choose_spec.2.2.1

private theorem stepFun_colNe {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    (P : {q // IsPlus M M' q}) : (stepFun hrow hcol P).1.2 ≠ P.1.2 :=
  (plus_step hrow hcol P.2).choose_spec.2.2.2

/-- **Ryser's 2-switch existence.** Two distinct (0,1)-matrices with equal row and column
    sums: at least one contains a switchable 2x2 block. -/
theorem switchable_block {M M' : ZeroOneMat m n}
    (hrow : ∀ i, rowSum M i = rowSum M' i) (hcol : ∀ j, colSum M j = colSum M' j)
    (hne : M ≠ M') :
    ∃ (i i' : Fin m) (j j' : Fin n), SwitchBlock M i i' j j' := by
  classical
  -- initial `+cell`
  obtain ⟨q0, hq0⟩ := exists_plus hcol hne
  let P0 : {q // IsPlus M M' q} := ⟨q0, hq0⟩
  -- the walk and its row/column projections
  let seq : ℕ → {q // IsPlus M M' q} := fun k => (stepFun hrow hcol)^[k] P0
  let r : ℕ → Fin m := fun k => (seq k).1.1
  let c : ℕ → Fin n := fun k => (seq k).1.2
  have hstep : ∀ k, seq (k + 1) = stepFun hrow hcol (seq k) :=
    fun k => Function.iterate_succ_apply' _ _ _
  have P1 : ∀ k, M (r k) (c k) = true := fun k => (seq k).2.1
  have P2 : ∀ k, M (r (k + 1)) (c k) = false := by
    intro k
    have h := stepFun_link hrow hcol (seq k)
    rw [← hstep k] at h; exact h
  have P3 : ∀ k, r (k + 1) ≠ r k := by
    intro k
    have h := stepFun_rowNe hrow hcol (seq k)
    rw [← hstep k] at h; exact h
  have Pc : ∀ k, c (k + 1) ≠ c k := by
    intro k
    have h := stepFun_colNe hrow hcol (seq k)
    rw [← hstep k] at h; exact h
  -- pigeonhole: the rows `r 0, …, r m` repeat
  have hex : ∃ k, ∃ p, p < k ∧ r p = r k := by
    have hlt : Fintype.card (Fin m) < Fintype.card (Fin (m + 1)) := by simp
    obtain ⟨x, y, hxy, hfxy⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (m + 1) => r k.val) hlt
    rcases lt_or_gt_of_ne (fun h : x.val = y.val => hxy (Fin.ext h)) with h | h
    · exact ⟨y.val, x.val, h, hfxy⟩
    · exact ⟨x.val, y.val, h, hfxy.symm⟩
  -- first repeat: `q` closes the cycle, and the prefix `r 0, …, r (q-1)` is injective
  let q := Nat.find hex
  obtain ⟨p, hpq, hrpq⟩ := Nat.find_spec hex
  have hdist : ∀ s t, t < q → s < t → r s ≠ r t := by
    intro s t htq hst heq
    exact Nat.find_min hex htq ⟨s, hst, heq⟩
  have hq1 : 1 ≤ q := Nat.one_le_of_lt hpq
  -- the descent along the start row `r p`
  have gp : M (r p) (c p) = true := P1 p
  have gq : M (r p) (c (q - 1)) = false := by
    have h := P2 (q - 1)
    rw [Nat.sub_add_cancel hq1] at h
    rw [← hrpq] at h
    exact h
  obtain ⟨t, hpt, htq, gt, gt1⟩ :=
    bool_descent (fun t => M (r p) (c t)) (q - 1) p (by omega) gp gq
  -- extract the switchable block
  refine ⟨r p, r (t + 1), c t, c (t + 1), ?_, (Pc t).symm, gt, P1 (t + 1), gt1, P2 t⟩
  exact hdist p (t + 1) (by omega) (by omega)

/-! ### The reduction: a nontrivial interchange graph has an edge. -/

/-- **Discharges `interchange_has_edge`.** A nontrivial interchange graph has an edge. -/
theorem interchange_has_edge {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (hIG : IsInterchangeGraph G) (hcard : 2 ≤ Fintype.card V) : ∃ u v, G.Adj u v := by
  obtain ⟨m, n, r, s, φ, hφ⟩ := hIG
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hcard
  -- Two distinct margin matrices.
  set Ma := (φ a).val with hMa
  set Mb := (φ b).val with hMb
  have hMaMb : Ma ≠ Mb := fun h => hab (φ.injective (Subtype.ext h))
  have hrow : ∀ i, rowSum Ma i = rowSum Mb i :=
    fun i => ((φ a).property.1 i).trans ((φ b).property.1 i).symm
  have hcol : ∀ j, colSum Ma j = colSum Mb j :=
    fun j => ((φ a).property.2 j).trans ((φ b).property.2 j).symm
  -- Ryser: Ma contains a switchable block.
  obtain ⟨i, i', j, j', hb⟩ := switchable_block hrow hcol hMaMb
  -- Flip it to get an interchange neighbour of `φ a`.
  set M'' := switchMat Ma i i' j j' with hM''
  have hint : Interchange Ma M'' := switch_interchange hb
  have hmarg : HasMargins r s M'' :=
    interchange_preserves_margins hint (φ a).property
  have hne'' : M'' ≠ Ma := switchMat_ne hb
  let Ypp : MarginClass r s := ⟨M'', hmarg⟩
  have hadjF : (flipGraph r s).Adj (φ a) Ypp := by
    refine ⟨fun h => hne'' (congrArg Subtype.val h).symm, Or.inl hint⟩
  refine ⟨a, φ.symm Ypp, ?_⟩
  rw [hφ a (φ.symm Ypp), Equiv.apply_symm_apply]
  exact hadjF

end Brualdi.Ryser
