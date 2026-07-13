import BrualdiLean.Coleman
import BrualdiLean.FiniteCerts

set_option autoImplicit false

namespace Brualdi.Ledger

private theorem head?_eq_head_of_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    l.head? = some (l.head h) := by
  exact List.head?_eq_some_head h

private theorem hasHamPath_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (l : List V) {u v : V}
    (hhead : l.head? = some u) (hlast : l.getLast? = some v)
    (hchain : l.IsChain G.Adj) (hnodup : l.Nodup) (hcover : ∀ x : V, x ∈ l) :
    HasHamPath G u v := by
  have hl_ne : l ≠ [] := by
    intro hnil
    rw [hnil] at hhead
    simp at hhead
  let p₀ : G.Walk (l.head hl_ne) (l.getLast hl_ne) :=
    SimpleGraph.Walk.ofSupport l hl_ne hchain
  have hstart : l.head hl_ne = u := by
    have hsome : some (l.head hl_ne) = some u :=
      (head?_eq_head_of_ne_nil hl_ne).symm.trans hhead
    exact Option.some.inj hsome
  have hend : l.getLast hl_ne = v := by
    have hsome : some (l.getLast hl_ne) = some v :=
      (List.getLast?_eq_getLast_of_ne_nil hl_ne).symm.trans hlast
    exact Option.some.inj hsome
  let p : G.Walk u v := p₀.copy hstart hend
  refine ⟨p, ?_⟩
  have hp₀_support : p₀.support = l := by simp [p₀]
  have hp₀_path : p₀.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hp₀_support]
    exact hnodup)
  have hp₀_ham : p₀.IsHamiltonian := hp₀_path.isHamiltonian_of_mem (fun x => by
    rw [hp₀_support]
    exact hcover x)
  intro x
  simpa [p, SimpleGraph.Walk.support_copy] using hp₀_ham x

private theorem pathOK_isChain {n : ℕ} (adj : Fin n → Fin n → Bool)
    {l : List (Fin n)}
    (hok : Brualdi.FiniteCerts.pathOK adj l = true) (hnodup : l.Nodup) :
    l.IsChain (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      cases t with
      | nil =>
          simp
      | cons b t =>
          have hok_parts :
              adj a b = true ∧ Brualdi.FiniteCerts.pathOK adj (b :: t) = true := by
            simpa [Brualdi.FiniteCerts.pathOK, Bool.and_eq_true] using hok
          have ha_not_mem : a ∉ b :: t := hnodup.notMem
          have hab_ne : a ≠ b := by
            intro hab
            exact ha_not_mem (by simp [hab])
          have hab_adj :
              (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj a b := by
            rw [SimpleGraph.fromRel_adj]
            exact ⟨hab_ne, Or.inl hok_parts.1⟩
          exact List.IsChain.cons_cons hab_adj (ih hok_parts.2 hnodup.of_cons)

def hpAux {n : ℕ} (adj : Fin n → Fin n → Bool) (target : Fin n) :
    ℕ → Fin n → List (Fin n) → Bool
  | 0,      current, _    => current == target
  | fuel+1, current, todo => todo.any (fun nx => adj current nx && hpAux adj target fuel nx (todo.erase nx))

def hpFrom {n : ℕ} (adj : Fin n → Fin n → Bool) (u v : Fin n) : Bool :=
  hpAux adj v (n - 1) u ((List.finRange n).erase u)

def hcAll {n : ℕ} (adj : Fin n → Fin n → Bool) : Bool :=
  (List.finRange n).all (fun u => (List.finRange n).all (fun v => (u == v) || hpFrom adj u v))

def hlAll {n : ℕ} (adj : Fin n → Fin n → Bool) (col : Fin n → Bool) : Bool :=
  (List.finRange n).all (fun u => (List.finRange n).all (fun v => (col u == col v) || hpFrom adj u v))

private theorem hpAux_exists_list {n : ℕ} (adj : Fin n → Fin n → Bool) (target : Fin n) :
    ∀ {fuel : ℕ} {current : Fin n} {todo : List (Fin n)},
      fuel = todo.length → current ∉ todo → todo.Nodup →
        hpAux adj target fuel current todo = true →
          ∃ l : List (Fin n),
            l.head? = some current ∧
              l.getLast? = some target ∧
              l.IsChain (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj ∧
              l.Nodup ∧ l.Perm (current :: todo) := by
  intro fuel
  induction fuel with
  | zero =>
      intro current todo hfuel _hcurrent hnodup hhp
      have htodo : todo = [] := List.eq_nil_of_length_eq_zero hfuel.symm
      have hcur_target : current = target := by
        change (current == target) = true at hhp
        exact beq_iff_eq.mp hhp
      refine ⟨[current], ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simpa [hcur_target]
      · simp
      · simp
      · simp [htodo]
  | succ fuel ih =>
      intro current todo hfuel hcurrent hnodup hhp
      change todo.any
          (fun nx => adj current nx && hpAux adj target fuel nx (todo.erase nx)) = true at hhp
      rcases List.any_eq_true.mp hhp with ⟨nx, hnx_mem, hnx_bool⟩
      have hparts :
          adj current nx = true ∧ hpAux adj target fuel nx (todo.erase nx) = true := by
        simpa [Bool.and_eq_true] using hnx_bool
      have hlen_erase_add : (todo.erase nx).length + 1 = todo.length :=
        List.length_erase_add_one hnx_mem
      have hlen_erase : fuel = (todo.erase nx).length := by
        omega
      have hnx_not_mem_erase : nx ∉ todo.erase nx := by
        intro hx
        exact ((List.Nodup.mem_erase_iff hnodup).mp hx).1 rfl
      have herase_nodup : (todo.erase nx).Nodup := hnodup.erase nx
      rcases ih hlen_erase hnx_not_mem_erase herase_nodup hparts.2 with
        ⟨l, hhead, hlast, hchain, hlnodup, hperm⟩
      have hl_ne : l ≠ [] := by
        intro hnil
        rw [hnil] at hhead
        simp at hhead
      have hhead_eq : l.head hl_ne = nx := by
        have hsome : some (l.head hl_ne) = some nx :=
          (head?_eq_head_of_ne_nil hl_ne).symm.trans hhead
        exact Option.some.inj hsome
      have hcurrent_ne_nx : current ≠ nx := by
        intro hcur_nx
        exact hcurrent (by simpa [hcur_nx] using hnx_mem)
      have hadj :
          (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj current nx := by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hcurrent_ne_nx, Or.inl hparts.1⟩
      have hchain_cons :
          (current :: l).IsChain
            (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj := by
        exact List.IsChain.cons_of_ne_nil hl_ne hchain (by simpa [hhead_eq] using hadj)
      have hcurrent_not_mem_l : current ∉ l := by
        intro hmem_l
        have hmem_rhs : current ∈ nx :: todo.erase nx := (hperm.mem_iff).mp hmem_l
        rcases List.mem_cons.mp hmem_rhs with h_eq | h_erase
        · exact hcurrent (by simpa [h_eq] using hnx_mem)
        · exact hcurrent (List.mem_of_mem_erase h_erase)
      have hnodup_cons : (current :: l).Nodup := hlnodup.cons hcurrent_not_mem_l
      have hperm_cons : (current :: l).Perm (current :: todo) :=
        (hperm.trans (List.perm_cons_erase hnx_mem).symm).cons current
      refine ⟨current :: l, ?_, ?_, hchain_cons, hnodup_cons, hperm_cons⟩
      · simp
      · simpa [List.getLast?_cons_of_ne_nil hl_ne] using hlast

private theorem hasHamPath_of_hpFrom {n : ℕ} (adj : Fin n → Fin n → Bool) {u v : Fin n}
    (h : hpFrom adj u v = true) :
    HasHamPath (SimpleGraph.fromRel (fun a b => adj a b = true)) u v := by
  have haux :
      hpAux adj v (n - 1) u ((List.finRange n).erase u) = true := by
    simpa [hpFrom] using h
  have hlen_erase_add :
      (((List.finRange n).erase u).length + 1 = n) := by
    simpa [List.length_finRange] using
      (List.length_erase_add_one (a := u) (l := List.finRange n) (List.mem_finRange u))
  have hlen : n - 1 = ((List.finRange n).erase u).length :=
    (Nat.eq_sub_of_add_eq hlen_erase_add).symm
  have hu_not_mem : u ∉ (List.finRange n).erase u := by
    intro hu
    exact ((List.Nodup.mem_erase_iff (List.nodup_finRange n)).mp hu).1 rfl
  have herase_nodup : ((List.finRange n).erase u).Nodup :=
    (List.nodup_finRange n).erase u
  rcases hpAux_exists_list (adj := adj) (target := v) hlen hu_not_mem herase_nodup haux with
    ⟨l, hhead, hlast, hchain, hnodup, hperm⟩
  have hcover : ∀ x : Fin n, x ∈ l := by
    intro x
    have hx_rhs : x ∈ u :: (List.finRange n).erase u := by
      by_cases hx : x = u
      · simp [hx]
      · exact List.mem_cons.mpr
          (Or.inr ((List.mem_erase_of_ne hx).2 (List.mem_finRange x)))
    exact (hperm.mem_iff).mpr hx_rhs
  exact hasHamPath_of_list l hhead hlast hchain hnodup hcover

private theorem hasHamPath_of_boolean {n : ℕ} (adj : Fin n → Fin n → Bool) {u v : Fin n}
    (h : Brualdi.FiniteCerts.hasHamPath adj u v = true) :
    HasHamPath (SimpleGraph.fromRel (fun a b => adj a b = true)) u v := by
  rw [Brualdi.FiniteCerts.hasHamPath] at h
  rcases List.any_eq_true.mp h with ⟨p, hp_mem, hp_bool⟩
  have hp_parts :
      p.head? = some u ∧
        p.getLast? = some v ∧ Brualdi.FiniteCerts.pathOK adj p = true := by
    simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using hp_bool
  have hp_perm : p.Perm (List.finRange n) := List.mem_permutations.mp hp_mem
  have hp_nodup : p.Nodup := (hp_perm.nodup_iff).mpr (List.nodup_finRange n)
  have hp_cover : ∀ x : Fin n, x ∈ p := by
    intro x
    exact (hp_perm.mem_iff).mpr (List.mem_finRange x)
  have hp_chain :
      p.IsChain (SimpleGraph.fromRel (fun a b => adj a b = true)).Adj :=
    pathOK_isChain adj hp_parts.2.2 hp_nodup
  exact hasHamPath_of_list p hp_parts.1 hp_parts.2.1 hp_chain hp_nodup hp_cover

theorem isHamConnected_of_boolean {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hsymm : ∀ a b, adj a b = adj b a)
    (h : Brualdi.FiniteCerts.hamConnected adj = true) :
    IsHamConnected (SimpleGraph.fromRel (fun a b => adj a b = true)) := by
  have _hsymm := hsymm
  intro u v huv
  rw [Brualdi.FiniteCerts.hamConnected] at h
  have hu_all :
      (List.finRange n).all (fun v => (u == v) || Brualdi.FiniteCerts.hasHamPath adj u v) =
        true :=
    (List.all_eq_true.mp h) u (List.mem_finRange u)
  have huv_bool : ((u == v) || Brualdi.FiniteCerts.hasHamPath adj u v) = true :=
    (List.all_eq_true.mp hu_all) v (List.mem_finRange v)
  have hpath : Brualdi.FiniteCerts.hasHamPath adj u v = true := by
    rcases (by simpa [Bool.or_eq_true] using huv_bool :
        (u == v) = true ∨ Brualdi.FiniteCerts.hasHamPath adj u v = true) with h_eq | h_path
    · exact (huv (beq_iff_eq.mp h_eq)).elim
    · exact h_path
  exact hasHamPath_of_boolean adj hpath

theorem isHamLaceable_of_boolean {n : ℕ} (adj : Fin n → Fin n → Bool) (col : Fin n → Bool)
    (hsymm : ∀ a b, adj a b = adj b a)
    (h : Brualdi.FiniteCerts.hamLaceable adj col = true) :
    IsHamLaceable (SimpleGraph.fromRel (fun a b => adj a b = true)) col := by
  have _hsymm := hsymm
  intro u v hcol
  rw [Brualdi.FiniteCerts.hamLaceable] at h
  have hu_all :
      (List.finRange n).all
          (fun v => (col u == col v) || Brualdi.FiniteCerts.hasHamPath adj u v) =
        true :=
    (List.all_eq_true.mp h) u (List.mem_finRange u)
  have huv_bool : ((col u == col v) || Brualdi.FiniteCerts.hasHamPath adj u v) = true :=
    (List.all_eq_true.mp hu_all) v (List.mem_finRange v)
  have hpath : Brualdi.FiniteCerts.hasHamPath adj u v = true := by
    rcases (by simpa [Bool.or_eq_true] using huv_bool :
        (col u == col v) = true ∨ Brualdi.FiniteCerts.hasHamPath adj u v = true) with h_eq | h_path
    · exact (hcol (beq_iff_eq.mp h_eq)).elim
    · exact h_path
  exact hasHamPath_of_boolean adj hpath

theorem isHamConnected_of_hcAll {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hsymm : ∀ a b, adj a b = adj b a) (h : hcAll adj = true) :
    IsHamConnected (SimpleGraph.fromRel (fun a b => adj a b = true)) := by
  have _hsymm := hsymm
  intro u v huv
  rw [hcAll] at h
  have hu_all :
      (List.finRange n).all (fun v => (u == v) || hpFrom adj u v) = true :=
    (List.all_eq_true.mp h) u (List.mem_finRange u)
  have huv_bool : ((u == v) || hpFrom adj u v) = true :=
    (List.all_eq_true.mp hu_all) v (List.mem_finRange v)
  have hpath : hpFrom adj u v = true := by
    rcases (by simpa [Bool.or_eq_true] using huv_bool :
        (u == v) = true ∨ hpFrom adj u v = true) with h_eq | h_path
    · exact (huv (beq_iff_eq.mp h_eq)).elim
    · exact h_path
  exact hasHamPath_of_hpFrom adj hpath

theorem isHamLaceable_of_hlAll {n : ℕ} (adj : Fin n → Fin n → Bool) (col : Fin n → Bool)
    (hsymm : ∀ a b, adj a b = adj b a) (h : hlAll adj col = true) :
    IsHamLaceable (SimpleGraph.fromRel (fun a b => adj a b = true)) col := by
  have _hsymm := hsymm
  intro u v hcol
  rw [hlAll] at h
  have hu_all :
      (List.finRange n).all (fun v => (col u == col v) || hpFrom adj u v) = true :=
    (List.all_eq_true.mp h) u (List.mem_finRange u)
  have huv_bool : ((col u == col v) || hpFrom adj u v) = true :=
    (List.all_eq_true.mp hu_all) v (List.mem_finRange v)
  have hpath : hpFrom adj u v = true := by
    rcases (by simpa [Bool.or_eq_true] using huv_bool :
        (col u == col v) = true ∨ hpFrom adj u v = true) with h_eq | h_path
    · exact (hcol (beq_iff_eq.mp h_eq)).elim
    · exact h_path
  exact hasHamPath_of_hpFrom adj hpath

/-! ### Deleting a zero row from a margin class. -/

private def dropRow {m n : ℕ} (i : Fin (m + 1)) (M : ZeroOneMat (m + 1) n) :
    ZeroOneMat m n :=
  fun a b => M (i.succAbove a) b

private def insertFalseRow {m n : ℕ} (i : Fin (m + 1)) (M : ZeroOneMat m n) :
    ZeroOneMat (m + 1) n :=
  fun a b => Fin.insertNth (α := fun _ : Fin (m + 1) => Bool) i false (fun k => M k b) a

private theorem row_eq_false_of_rowSum_zero {m n : ℕ} (M : ZeroOneMat m n) {i : Fin m}
    (h : rowSum M i = 0) : ∀ j, M i j = false := by
  intro j
  have hsum : (∑ x : Fin n, (if M i x then 1 else 0 : ℕ)) = 0 := by
    simpa only [rowSum] using h
  have hterm : (if M i j then 1 else 0 : ℕ) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun x hx => by split <;> norm_num)).mp hsum j (Finset.mem_univ j)
  cases hM : M i j <;> simp [hM] at hterm ⊢

private theorem margin_row_false {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M : MarginClass r s} {i : Fin m} (hi : r i = 0) : ∀ j, M.val i j = false := by
  exact row_eq_false_of_rowSum_zero M.val (by simpa only [hi] using M.property.1 i)

private theorem dropRow_hasMargins {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {i : Fin (m + 1)} (hi : r i = 0) (M : MarginClass r s) :
    HasMargins (fun a : Fin m => r (i.succAbove a)) s (dropRow i M.val) := by
  constructor
  · intro a
    change rowSum M.val (i.succAbove a) = r (i.succAbove a)
    exact M.property.1 (i.succAbove a)
  · intro b
    have hirow : M.val i b = false := margin_row_false (M := M) hi b
    calc
      colSum (dropRow i M.val) b
          = ∑ a : Fin m, (if M.val (i.succAbove a) b then 1 else 0 : ℕ) := by
              rfl
      _ = colSum M.val b := by
          have hsplit := Fin.sum_univ_succAbove
            (fun a : Fin (m + 1) => (if M.val a b then 1 else 0 : ℕ)) i
          simpa only [colSum, hirow, Bool.false_eq_true, if_false, zero_add] using hsplit.symm
      _ = s b := M.property.2 b

private theorem insertFalseRow_hasMargins {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = 0)
    (M : MarginClass (fun a : Fin m => r (i.succAbove a)) s) :
    HasMargins r s (insertFalseRow i M.val) := by
  constructor
  · intro a
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      calc
        rowSum (insertFalseRow i M.val) i
            = ∑ b : Fin n, (if false then 1 else 0 : ℕ) := by
                simp only [rowSum, insertFalseRow, Fin.insertNth_apply_same]
        _ = r i := by simp [hi]
    · rw [hsucc]
      calc
        rowSum (insertFalseRow i M.val) (i.succAbove a0)
            = rowSum M.val a0 := by
                simp only [rowSum, insertFalseRow, Fin.insertNth_apply_succAbove]
        _ = r (i.succAbove a0) := M.property.1 a0
  · intro b
    calc
      colSum (insertFalseRow i M.val) b
          = ∑ a : Fin (m + 1), (if insertFalseRow i M.val a b then 1 else 0 : ℕ) := by
              rfl
      _ = (if insertFalseRow i M.val i b then 1 else 0 : ℕ) +
            ∑ a : Fin m, (if insertFalseRow i M.val (i.succAbove a) b then 1 else 0 : ℕ) := by
          exact Fin.sum_univ_succAbove
            (fun a : Fin (m + 1) => (if insertFalseRow i M.val a b then 1 else 0 : ℕ)) i
      _ = colSum M.val b := by
          simp only [colSum, insertFalseRow, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove, Bool.false_eq_true, if_false, zero_add]
      _ = s b := M.property.2 b

private def deleteZeroRowEquiv {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (i : Fin (m + 1)) (hi : r i = 0) :
    MarginClass r s ≃ MarginClass (fun a : Fin m => r (i.succAbove a)) s where
  toFun M := ⟨dropRow i M.val, dropRow_hasMargins (i := i) hi M⟩
  invFun M := ⟨insertFalseRow i M.val, insertFalseRow_hasMargins (i := i) hi M⟩
  left_inv M := by
    apply Subtype.ext
    funext a b
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      simp only [insertFalseRow, Fin.insertNth_apply_same]
      exact (margin_row_false (M := M) hi b).symm
    · rw [hsucc]
      simp only [dropRow, insertFalseRow, Fin.insertNth_apply_succAbove]
  right_inv M := by
    apply Subtype.ext
    funext a b
    simp only [dropRow, insertFalseRow, Fin.insertNth_apply_succAbove]

private theorem interchange_drop_iff_of_row_false {m n : ℕ} {M N : ZeroOneMat (m + 1) n}
    {i : Fin (m + 1)} (hM : ∀ b, M i b = false) (hN : ∀ b, N i b = false) :
    Interchange M N ↔ Interchange (dropRow i M) (dropRow i N) := by
  constructor
  · rintro ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    have hr₁_ne_i : r₁ ≠ i := by
      intro hri
      have hfalse : M r₁ c₁ = false := by simpa only [hri] using hM c₁
      rw [hfalse] at hM₁₁
      exact Bool.false_ne_true hM₁₁
    have hr₂_ne_i : r₂ ≠ i := by
      intro hri
      have hfalse : M r₂ c₂ = false := by simpa only [hri] using hM c₂
      rw [hfalse] at hM₂₂
      exact Bool.false_ne_true hM₂₂
    rcases Fin.exists_succAbove_eq (x := r₁) (y := i) hr₁_ne_i with ⟨a₁, ha₁⟩
    rcases Fin.exists_succAbove_eq (x := r₂) (y := i) hr₂_ne_i with ⟨a₂, ha₂⟩
    refine ⟨a₁, a₂, c₁, c₂, ?_, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ha
      exact hrne (by rw [← ha₁, ← ha₂, ha])
    · simpa only [dropRow, ha₁] using hM₁₁
    · simpa only [dropRow, ha₂] using hM₂₂
    · simpa only [dropRow, ha₁] using hM₁₂
    · simpa only [dropRow, ha₂] using hM₂₁
    · simpa only [dropRow, ha₁] using hN₁₁
    · simpa only [dropRow, ha₂] using hN₂₂
    · simpa only [dropRow, ha₁] using hN₁₂
    · simpa only [dropRow, ha₂] using hN₂₁
    · intro a b hnot
      exact hout (i.succAbove a) b (by
        intro hblock
        apply hnot
        rcases hblock with ⟨hr, hc⟩
        constructor
        · rcases hr with hr | hr
          · left
            exact Fin.succAbove_right_injective (by rw [hr, ha₁])
          · right
            exact Fin.succAbove_right_injective (by rw [hr, ha₂])
        · exact hc)
  · rintro ⟨a₁, a₂, c₁, c₂, hane, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨i.succAbove a₁, i.succAbove a₂, c₁, c₂, ?_, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hane (Fin.succAbove_right_injective h)
    · simpa only [dropRow] using hM₁₁
    · simpa only [dropRow] using hM₂₂
    · simpa only [dropRow] using hM₁₂
    · simpa only [dropRow] using hM₂₁
    · simpa only [dropRow] using hN₁₁
    · simpa only [dropRow] using hN₂₂
    · simpa only [dropRow] using hN₁₂
    · simpa only [dropRow] using hN₂₁
    · intro a b hnot
      rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
      · rw [hsame, hN b, hM b]
      · rw [hsucc]
        exact hout a0 b (by
          intro hblock
          apply hnot
          rcases hblock with ⟨hr, hc⟩
          constructor
          · rcases hr with hr | hr
            · left
              rw [hsucc, hr]
            · right
              rw [hsucc, hr]
          · exact hc)

private theorem deleteZeroRowEquiv_interchange_iff {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = 0)
    (M N : MarginClass r s) :
    Interchange ((deleteZeroRowEquiv r s i hi M).val)
      ((deleteZeroRowEquiv r s i hi N).val) ↔ Interchange M.val N.val := by
  exact (interchange_drop_iff_of_row_false (i := i)
    (M := M.val) (N := N.val)
    (margin_row_false (M := M) hi) (margin_row_false (M := N) hi)).symm

theorem flipGraph_delete_zero_row {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (i : Fin (m + 1)) (hi : r i = 0) :
    Nonempty (Brualdi.flipGraph r s ≃g Brualdi.flipGraph (fun a => r (i.succAbove a)) s) := by
  let e := deleteZeroRowEquiv r s i hi
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [Brualdi.flipGraph, Brualdi.flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using
          (deleteZeroRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi M N).mp hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using
          (deleteZeroRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi N M).mp hrel
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using
          (deleteZeroRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi M N).mpr hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using
          (deleteZeroRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi N M).mpr hrel

/-! ### Deleting a full row from a nonempty margin class. -/

private def insertTrueRow {m n : ℕ} (i : Fin (m + 1)) (M : ZeroOneMat m n) :
    ZeroOneMat (m + 1) n :=
  fun a b => Fin.insertNth (α := fun _ : Fin (m + 1) => Bool) i true (fun k => M k b) a

private theorem row_eq_true_of_rowSum_full {m n : ℕ} (M : ZeroOneMat m n) {i : Fin m}
    (h : rowSum M i = n) : ∀ j, M i j = true := by
  intro j
  by_contra hj
  have hfalse : M i j = false := by
    cases hM : M i j <;> simp [hM] at hj ⊢
  let t : Finset (Fin n) := Finset.univ.filter (fun x => M i x = true)
  have hcard : t.card = n := by
    have hsum := Finset.sum_boole (R := ℕ) (fun x : Fin n => M i x = true) Finset.univ
    have hsum' : (∑ x : Fin n, (if M i x = true then 1 else 0 : ℕ)) = t.card := by
      simpa [t] using hsum
    have hrow : (∑ x : Fin n, (if M i x = true then 1 else 0 : ℕ)) = n := by
      simpa [rowSum] using h
    exact hsum'.symm ▸ hrow
  have ht_sub : t ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · exact Finset.filter_subset _ _
    · intro hEq
      have hj_mem : j ∈ t := by
        have : j ∈ (Finset.univ : Finset (Fin n)) := by simp
        simpa [hEq] using this
      simp [t, hfalse] at hj_mem
  have hlt : t.card < n := by
    have := Finset.card_lt_card ht_sub
    simpa [t, Finset.card_univ, Fintype.card_fin] using this
  omega

private theorem margin_row_true {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M : MarginClass r s} {i : Fin m} (hi : r i = n) : ∀ j, M.val i j = true := by
  exact row_eq_true_of_rowSum_full M.val (by simpa only [hi] using M.property.1 i)

private theorem col_pos_of_full_row_nonempty {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = n)
    (hne : Nonempty (MarginClass r s)) : ∀ b, 0 < s b := by
  intro b
  rcases hne with ⟨M⟩
  have hirow : M.val i b = true := margin_row_true (M := M) hi b
  have hcol :
      1 + colSum (dropRow i M.val) b = s b := by
    calc
      1 + colSum (dropRow i M.val) b
          = colSum M.val b := by
              have hsplit := Fin.sum_univ_succAbove
                (fun a : Fin (m + 1) => (if M.val a b then 1 else 0 : ℕ)) i
              change 1 + (∑ a : Fin m,
                  (if M.val (i.succAbove a) b then 1 else 0 : ℕ)) =
                ∑ a : Fin (m + 1), (if M.val a b then 1 else 0 : ℕ)
              simpa [hirow] using hsplit.symm
      _ = s b := M.property.2 b
  omega

private theorem dropRow_hasMargins_full {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = n) (M : MarginClass r s) :
    HasMargins (fun a : Fin m => r (i.succAbove a)) (fun b => s b - 1)
      (dropRow i M.val) := by
  constructor
  · intro a
    change rowSum M.val (i.succAbove a) = r (i.succAbove a)
    exact M.property.1 (i.succAbove a)
  · intro b
    have hirow : M.val i b = true := margin_row_true (M := M) hi b
    have hcol :
        1 + colSum (dropRow i M.val) b = s b := by
      calc
        1 + colSum (dropRow i M.val) b
            = colSum M.val b := by
                have hsplit := Fin.sum_univ_succAbove
                  (fun a : Fin (m + 1) => (if M.val a b then 1 else 0 : ℕ)) i
                change 1 + (∑ a : Fin m,
                    (if M.val (i.succAbove a) b then 1 else 0 : ℕ)) =
                  ∑ a : Fin (m + 1), (if M.val a b then 1 else 0 : ℕ)
                simpa [hirow] using hsplit.symm
        _ = s b := M.property.2 b
    exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hcol)

private theorem insertTrueRow_hasMargins {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = n) (hpos : ∀ b, 0 < s b)
    (M : MarginClass (fun a : Fin m => r (i.succAbove a)) (fun b => s b - 1)) :
    HasMargins r s (insertTrueRow i M.val) := by
  constructor
  · intro a
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      calc
        rowSum (insertTrueRow i M.val) i
            = ∑ b : Fin n, (1 : ℕ) := by
                simp only [rowSum, insertTrueRow, Fin.insertNth_apply_same, if_true]
        _ = r i := by simp [hi]
    · rw [hsucc]
      calc
        rowSum (insertTrueRow i M.val) (i.succAbove a0)
            = rowSum M.val a0 := by
                simp only [rowSum, insertTrueRow, Fin.insertNth_apply_succAbove]
        _ = r (i.succAbove a0) := M.property.1 a0
  · intro b
    calc
      colSum (insertTrueRow i M.val) b
          = ∑ a : Fin (m + 1), (if insertTrueRow i M.val a b then 1 else 0 : ℕ) := by
              rfl
      _ = (if insertTrueRow i M.val i b then 1 else 0 : ℕ) +
            ∑ a : Fin m, (if insertTrueRow i M.val (i.succAbove a) b then 1 else 0 : ℕ) := by
          exact Fin.sum_univ_succAbove
            (fun a : Fin (m + 1) => (if insertTrueRow i M.val a b then 1 else 0 : ℕ)) i
      _ = 1 + colSum M.val b := by
          simp only [colSum, insertTrueRow, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove, if_true]
      _ = 1 + (s b - 1) := by rw [M.property.2 b]
      _ = s b := by
          have hb : 0 < s b := hpos b
          omega

private def deleteFullRowEquiv {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (i : Fin (m + 1)) (hi : r i = n) (hpos : ∀ b, 0 < s b) :
    MarginClass r s ≃ MarginClass (fun a : Fin m => r (i.succAbove a)) (fun b => s b - 1) where
  toFun M := ⟨dropRow i M.val, dropRow_hasMargins_full (i := i) hi M⟩
  invFun M := ⟨insertTrueRow i M.val, insertTrueRow_hasMargins (i := i) hi hpos M⟩
  left_inv M := by
    apply Subtype.ext
    funext a b
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      simp only [insertTrueRow, Fin.insertNth_apply_same]
      exact (margin_row_true (M := M) hi b).symm
    · rw [hsucc]
      simp only [dropRow, insertTrueRow, Fin.insertNth_apply_succAbove]
  right_inv M := by
    apply Subtype.ext
    funext a b
    simp only [dropRow, insertTrueRow, Fin.insertNth_apply_succAbove]

private theorem interchange_drop_iff_of_row_true {m n : ℕ} {M N : ZeroOneMat (m + 1) n}
    {i : Fin (m + 1)} (hM : ∀ b, M i b = true) (hN : ∀ b, N i b = true) :
    Interchange M N ↔ Interchange (dropRow i M) (dropRow i N) := by
  constructor
  · rintro ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    have hr₁_ne_i : r₁ ≠ i := by
      intro hri
      have htrue : M r₁ c₂ = true := by simpa only [hri] using hM c₂
      rw [htrue] at hM₁₂
      exact Bool.noConfusion hM₁₂
    have hr₂_ne_i : r₂ ≠ i := by
      intro hri
      have htrue : M r₂ c₁ = true := by simpa only [hri] using hM c₁
      rw [htrue] at hM₂₁
      exact Bool.noConfusion hM₂₁
    rcases Fin.exists_succAbove_eq (x := r₁) (y := i) hr₁_ne_i with ⟨a₁, ha₁⟩
    rcases Fin.exists_succAbove_eq (x := r₂) (y := i) hr₂_ne_i with ⟨a₂, ha₂⟩
    refine ⟨a₁, a₂, c₁, c₂, ?_, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ha
      exact hrne (by rw [← ha₁, ← ha₂, ha])
    · simpa only [dropRow, ha₁] using hM₁₁
    · simpa only [dropRow, ha₂] using hM₂₂
    · simpa only [dropRow, ha₁] using hM₁₂
    · simpa only [dropRow, ha₂] using hM₂₁
    · simpa only [dropRow, ha₁] using hN₁₁
    · simpa only [dropRow, ha₂] using hN₂₂
    · simpa only [dropRow, ha₁] using hN₁₂
    · simpa only [dropRow, ha₂] using hN₂₁
    · intro a b hnot
      exact hout (i.succAbove a) b (by
        intro hblock
        apply hnot
        rcases hblock with ⟨hr, hc⟩
        constructor
        · rcases hr with hr | hr
          · left
            exact Fin.succAbove_right_injective (by rw [hr, ha₁])
          · right
            exact Fin.succAbove_right_injective (by rw [hr, ha₂])
        · exact hc)
  · rintro ⟨a₁, a₂, c₁, c₂, hane, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨i.succAbove a₁, i.succAbove a₂, c₁, c₂, ?_, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hane (Fin.succAbove_right_injective h)
    · simpa only [dropRow] using hM₁₁
    · simpa only [dropRow] using hM₂₂
    · simpa only [dropRow] using hM₁₂
    · simpa only [dropRow] using hM₂₁
    · simpa only [dropRow] using hN₁₁
    · simpa only [dropRow] using hN₂₂
    · simpa only [dropRow] using hN₁₂
    · simpa only [dropRow] using hN₂₁
    · intro a b hnot
      rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
      · rw [hsame, hN b, hM b]
      · rw [hsucc]
        exact hout a0 b (by
          intro hblock
          apply hnot
          rcases hblock with ⟨hr, hc⟩
          constructor
          · rcases hr with hr | hr
            · left
              rw [hsucc, hr]
            · right
              rw [hsucc, hr]
          · exact hc)

private theorem deleteFullRowEquiv_interchange_iff {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} (hi : r i = n) (hpos : ∀ b, 0 < s b)
    (M N : MarginClass r s) :
    Interchange ((deleteFullRowEquiv r s i hi hpos M).val)
      ((deleteFullRowEquiv r s i hi hpos N).val) ↔ Interchange M.val N.val := by
  exact (interchange_drop_iff_of_row_true (i := i)
    (M := M.val) (N := N.val)
    (margin_row_true (M := M) hi) (margin_row_true (M := N) hi)).symm

theorem flipGraph_delete_full_row {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (i : Fin (m + 1)) (hi : r i = n) (hne : Nonempty (MarginClass r s)) :
    Nonempty (Brualdi.flipGraph r s ≃g
      Brualdi.flipGraph (fun a => r (i.succAbove a)) (fun j => s j - 1)) := by
  let hpos : ∀ b, 0 < s b := col_pos_of_full_row_nonempty (r := r) (i := i) hi hne
  let e := deleteFullRowEquiv r s i hi hpos
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [Brualdi.flipGraph, Brualdi.flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hneMN, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hneMN (congrArg e hMN)
      · simpa only [e] using
          (deleteFullRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi hpos M N).mp hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro hMN
        exact hneMN (congrArg e hMN)
      · simpa only [e] using
          (deleteFullRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi hpos N M).mp hrel
  · rintro ⟨hneMN, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hneMN (e.injective heq)
      · simpa only [e] using
          (deleteFullRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi hpos M N).mpr hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hneMN (e.injective heq)
      · simpa only [e] using
          (deleteFullRowEquiv_interchange_iff (r := r) (s := s) (i := i) hi hpos N M).mpr hrel

/-! ### Transposing a margin class. -/

private def transposeMat {m n : ℕ} (M : ZeroOneMat m n) : ZeroOneMat n m :=
  fun j i => M i j

private theorem transpose_hasMargins {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) : HasMargins s r (transposeMat M.val) := by
  constructor
  · intro j
    change colSum M.val j = s j
    exact M.property.2 j
  · intro i
    change rowSum M.val i = r i
    exact M.property.1 i

private def transposeEquiv {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    MarginClass r s ≃ MarginClass s r where
  toFun M := ⟨transposeMat M.val, transpose_hasMargins M⟩
  invFun M := ⟨transposeMat M.val, transpose_hasMargins M⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    rfl
  right_inv M := by
    apply Subtype.ext
    funext j i
    rfl

private theorem interchange_transpose_iff {m n : ℕ} {M N : ZeroOneMat m n} :
    Interchange (transposeMat M) (transposeMat N) ↔ Interchange M N := by
  constructor
  · rintro ⟨c₁, c₂, r₁, r₂, hcne, hrne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨r₁, r₂, c₁, c₂, hrne, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [transposeMat] using hM₁₁
    · simpa only [transposeMat] using hM₂₂
    · simpa only [transposeMat] using hM₂₁
    · simpa only [transposeMat] using hM₁₂
    · simpa only [transposeMat] using hN₁₁
    · simpa only [transposeMat] using hN₂₂
    · simpa only [transposeMat] using hN₂₁
    · simpa only [transposeMat] using hN₁₂
    · intro a b hnot
      exact hout b a (by
        intro hblock
        apply hnot
        rcases hblock with ⟨hc, hr⟩
        exact ⟨hr, hc⟩)
  · rintro ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    refine ⟨c₁, c₂, r₁, r₂, hcne, hrne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [transposeMat] using hM₁₁
    · simpa only [transposeMat] using hM₂₂
    · simpa only [transposeMat] using hM₂₁
    · simpa only [transposeMat] using hM₁₂
    · simpa only [transposeMat] using hN₁₁
    · simpa only [transposeMat] using hN₂₂
    · simpa only [transposeMat] using hN₂₁
    · simpa only [transposeMat] using hN₁₂
    · intro a b hnot
      exact hout b a (by
        intro hblock
        apply hnot
        rcases hblock with ⟨hr, hc⟩
        exact ⟨hc, hr⟩)

private theorem transposeEquiv_interchange_iff {m n : ℕ} {r : Fin m → ℕ}
    {s : Fin n → ℕ} (M N : MarginClass r s) :
    Interchange ((transposeEquiv r s M).val) ((transposeEquiv r s N).val) ↔
      Interchange M.val N.val := by
  exact interchange_transpose_iff

theorem flipGraph_transpose {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    Nonempty (Brualdi.flipGraph r s ≃g Brualdi.flipGraph s r) := by
  let e := transposeEquiv r s
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [Brualdi.flipGraph, Brualdi.flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using (transposeEquiv_interchange_iff M N).mp hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · simpa only [e] using (transposeEquiv_interchange_iff N M).mp hrel
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using (transposeEquiv_interchange_iff M N).mpr hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa only [e] using (transposeEquiv_interchange_iff N M).mpr hrel

theorem flipGraph_delete_zero_col {m n : ℕ} (r : Fin m → ℕ) (s : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (hj : s j = 0) :
    Nonempty (Brualdi.flipGraph r s ≃g
      Brualdi.flipGraph r (fun b => s (j.succAbove b))) := by
  obtain ⟨e₁⟩ := flipGraph_transpose r s
  obtain ⟨e₂⟩ := flipGraph_delete_zero_row s r j hj
  obtain ⟨e₃⟩ := flipGraph_transpose (fun b : Fin n => s (j.succAbove b)) r
  exact ⟨(e₁.trans e₂).trans e₃⟩

private theorem transpose_nonempty {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (hne : Nonempty (MarginClass r s)) : Nonempty (MarginClass s r) := by
  rcases hne with ⟨M⟩
  exact ⟨transposeEquiv r s M⟩

theorem flipGraph_delete_full_col {m n : ℕ} (r : Fin m → ℕ) (s : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (hj : s j = m) (hne : Nonempty (MarginClass r s)) :
    Nonempty (Brualdi.flipGraph r s ≃g
      Brualdi.flipGraph (fun i => r i - 1) (fun b => s (j.succAbove b))) := by
  obtain ⟨e₁⟩ := flipGraph_transpose r s
  have hneT : Nonempty (MarginClass s r) := transpose_nonempty hne
  obtain ⟨e₂⟩ := flipGraph_delete_full_row s r j hj hneT
  obtain ⟨e₃⟩ := flipGraph_transpose (fun b : Fin n => s (j.succAbove b)) (fun i => r i - 1)
  exact ⟨(e₁.trans e₂).trans e₃⟩

def IsActive {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) : Prop :=
  (∀ i, 0 < r i ∧ r i < n) ∧ (∀ j, 0 < s j ∧ s j < m)

private theorem rowSum_le_cols {m n : ℕ} (M : ZeroOneMat m n) (i : Fin m) :
    rowSum M i ≤ n := by
  calc
    rowSum M i = ∑ j : Fin n, (if M i j then 1 else 0 : ℕ) := by rfl
    _ ≤ ∑ j : Fin n, (1 : ℕ) := by
        exact Finset.sum_le_sum (fun j hj => by split <;> norm_num)
    _ = n := by simp

private theorem colSum_le_rows {m n : ℕ} (M : ZeroOneMat m n) (j : Fin n) :
    colSum M j ≤ m := by
  calc
    colSum M j = ∑ i : Fin m, (if M i j then 1 else 0 : ℕ) := by rfl
    _ ≤ ∑ i : Fin m, (1 : ℕ) := by
        exact Finset.sum_le_sum (fun i hi => by split <;> norm_num)
    _ = m := by simp

private theorem active_of_no_forced_lines {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (hne : Nonempty (MarginClass r s))
    (hrow : ¬ ∃ i : Fin m, r i = 0 ∨ r i = n)
    (hcol : ¬ ∃ j : Fin n, s j = 0 ∨ s j = m) : IsActive r s := by
  rcases hne with ⟨M⟩
  constructor
  · intro i
    have hne0 : r i ≠ 0 := by
      intro h
      exact hrow ⟨i, Or.inl h⟩
    have hnen : r i ≠ n := by
      intro h
      exact hrow ⟨i, Or.inr h⟩
    have hle : r i ≤ n := by
      rw [← M.property.1 i]
      exact rowSum_le_cols M.val i
    exact ⟨Nat.pos_of_ne_zero hne0, Nat.lt_of_le_of_ne hle hnen⟩
  · intro j
    have hne0 : s j ≠ 0 := by
      intro h
      exact hcol ⟨j, Or.inl h⟩
    have hnem : s j ≠ m := by
      intro h
      exact hcol ⟨j, Or.inr h⟩
    have hle : s j ≤ m := by
      rw [← M.property.2 j]
      exact colSum_le_rows M.val j
    exact ⟨Nat.pos_of_ne_zero hne0, Nat.lt_of_le_of_ne hle hnem⟩

private theorem marginClass_nonempty_of_iso {m n m' n' : ℕ} {r : Fin m → ℕ}
    {s : Fin n → ℕ} {r' : Fin m' → ℕ} {s' : Fin n' → ℕ}
    (e : Brualdi.flipGraph r s ≃g Brualdi.flipGraph r' s')
    (hne : Nonempty (MarginClass r s)) : Nonempty (MarginClass r' s') := by
  rcases hne with ⟨M⟩
  exact ⟨e M⟩

theorem exists_active_iso {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hne : Nonempty (MarginClass r s)) :
    ∃ (m' n' : ℕ) (r' : Fin m' → ℕ) (s' : Fin n' → ℕ),
      IsActive r' s' ∧ Nonempty (Brualdi.flipGraph r s ≃g Brualdi.flipGraph r' s') := by
  classical
  by_cases hrow : ∃ i : Fin m, r i = 0 ∨ r i = n
  · rcases hrow with ⟨i, hi0 | hifull⟩
    · cases m with
      | zero =>
          exact Fin.elim0 i
      | succ m0 =>
          obtain ⟨e⟩ := flipGraph_delete_zero_row (m := m0) (n := n) r s i hi0
          have hneSmall :
              Nonempty (MarginClass (fun a : Fin m0 => r (i.succAbove a)) s) :=
            marginClass_nonempty_of_iso e hne
          rcases exists_active_iso (r := fun a : Fin m0 => r (i.succAbove a)) (s := s)
              hneSmall with
            ⟨m', n', r', s', hactive, ⟨e'⟩⟩
          exact ⟨m', n', r', s', hactive, ⟨e.trans e'⟩⟩
    · cases m with
      | zero =>
          exact Fin.elim0 i
      | succ m0 =>
          obtain ⟨e⟩ := flipGraph_delete_full_row (m := m0) (n := n) r s i hifull hne
          have hneSmall :
              Nonempty (MarginClass (fun a : Fin m0 => r (i.succAbove a)) (fun j => s j - 1)) :=
            marginClass_nonempty_of_iso e hne
          rcases exists_active_iso (r := fun a : Fin m0 => r (i.succAbove a))
              (s := fun j => s j - 1) hneSmall with
            ⟨m', n', r', s', hactive, ⟨e'⟩⟩
          exact ⟨m', n', r', s', hactive, ⟨e.trans e'⟩⟩
  · by_cases hcol : ∃ j : Fin n, s j = 0 ∨ s j = m
    · rcases hcol with ⟨j, hj0 | hjfull⟩
      · cases n with
        | zero =>
            exact Fin.elim0 j
        | succ n0 =>
            obtain ⟨e⟩ := flipGraph_delete_zero_col (m := m) (n := n0) r s j hj0
            have hneSmall :
                Nonempty (MarginClass r (fun b : Fin n0 => s (j.succAbove b))) :=
              marginClass_nonempty_of_iso e hne
            rcases exists_active_iso (r := r) (s := fun b : Fin n0 => s (j.succAbove b))
                hneSmall with
              ⟨m', n', r', s', hactive, ⟨e'⟩⟩
            exact ⟨m', n', r', s', hactive, ⟨e.trans e'⟩⟩
      · cases n with
        | zero =>
            exact Fin.elim0 j
        | succ n0 =>
            obtain ⟨e⟩ := flipGraph_delete_full_col (m := m) (n := n0) r s j hjfull hne
            have hneSmall :
                Nonempty (MarginClass (fun i => r i - 1) (fun b : Fin n0 => s (j.succAbove b))) :=
              marginClass_nonempty_of_iso e hne
            rcases exists_active_iso (r := fun i => r i - 1)
                (s := fun b : Fin n0 => s (j.succAbove b)) hneSmall with
              ⟨m', n', r', s', hactive, ⟨e'⟩⟩
            exact ⟨m', n', r', s', hactive, ⟨e.trans e'⟩⟩
    · have hactive : IsActive r s := active_of_no_forced_lines hne hrow hcol
      exact ⟨m, n, r, s, hactive, ⟨SimpleGraph.Iso.refl⟩⟩
termination_by m + n
decreasing_by
  all_goals
    simp_wf
    omega

/-! ### The two-row all-column-one case is a Johnson graph. -/

private theorem inter_insert_erase_eq_erase {α : Type*} [DecidableEq α] {S : Finset α} {a b : α}
    (ha : a ∈ S) (hb : b ∉ S) :
    S ∩ insert b (S.erase a) = S.erase a := by
  ext x
  by_cases hxb : x = b
  · subst x
    simp [hb]
  · by_cases hxa : x = a
    · subst x
      simp [ha, hb]
    · simp [hxa, hxb]

private theorem card_inter_insert_erase {α : Type*} [DecidableEq α] {S : Finset α} {a b : α}
    (ha : a ∈ S) (hb : b ∉ S) :
    (S ∩ insert b (S.erase a)).card = S.card - 1 := by
  rw [inter_insert_erase_eq_erase ha hb, Finset.card_erase_of_mem ha]

private def twoRowTopSet {n : ℕ} {k : ℕ}
    (M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)) : Finset (Fin n) :=
  Finset.univ.filter fun j => M.val (0 : Fin 2) j = true

private theorem twoRowTopSet_card {n : ℕ} {k : ℕ}
    (M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)) :
    (twoRowTopSet M).card = k := by
  have hrow := M.property.1 (0 : Fin 2)
  simpa [twoRowTopSet, rowSum] using hrow

private theorem twoRowTop_true_of_mem {n k : ℕ}
    {M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {j : Fin n}
    (h : j ∈ twoRowTopSet M) : M.val (0 : Fin 2) j = true := by
  simpa [twoRowTopSet] using h

private theorem twoRowTop_mem_of_true {n k : ℕ}
    {M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {j : Fin n}
    (h : M.val (0 : Fin 2) j = true) : j ∈ twoRowTopSet M := by
  simp [twoRowTopSet, h]

private theorem twoRowTop_false_of_not_mem {n k : ℕ}
    {M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {j : Fin n}
    (h : j ∉ twoRowTopSet M) : M.val (0 : Fin 2) j = false := by
  cases hM : M.val (0 : Fin 2) j
  · rfl
  · exact False.elim (h (by simp [twoRowTopSet, hM]))

private theorem twoRowTop_not_mem_of_false {n k : ℕ}
    {M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {j : Fin n}
    (h : M.val (0 : Fin 2) j = false) : j ∉ twoRowTopSet M := by
  simp [twoRowTopSet, h]

private theorem twoRowBottom_eq_not_top {n : ℕ} {k : ℕ}
    (M : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)) (j : Fin n) :
    M.val (1 : Fin 2) j = !M.val (0 : Fin 2) j := by
  have hcol := M.property.2 j
  rw [colSum, Fin.sum_univ_two] at hcol
  cases h0 : M.val (0 : Fin 2) j <;> cases h1 : M.val (1 : Fin 2) j <;>
    simp [h0, h1] at hcol ⊢

private def twoRowMatOfSet {n k : ℕ} (S : Brualdi.Johnson.JV n k) : ZeroOneMat 2 n :=
  fun i j => if i = 0 then decide (j ∈ S.1) else decide (j ∉ S.1)

private theorem twoRowMatOfSet_hasMargins {n k : ℕ} (S : Brualdi.Johnson.JV n k) :
    HasMargins (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1) (twoRowMatOfSet S) := by
  constructor
  · intro i
    fin_cases i
    · change rowSum (twoRowMatOfSet S) (0 : Fin 2) = k
      calc
        rowSum (twoRowMatOfSet S) (0 : Fin 2)
            = (Finset.univ.filter fun j : Fin n => j ∈ S.1).card := by
              simp [rowSum, twoRowMatOfSet]
        _ = S.1.card := by
              apply congrArg Finset.card
              ext j
              simp
        _ = k := S.2
    · change rowSum (twoRowMatOfSet S) (1 : Fin 2) = n - k
      calc
        rowSum (twoRowMatOfSet S) (1 : Fin 2)
            = (Finset.univ.filter fun j : Fin n => j ∉ S.1).card := by
              calc
                (∑ j : Fin n, if twoRowMatOfSet S (1 : Fin 2) j = true then 1 else 0 : ℕ)
                    = (∑ j : Fin n, if j ∉ S.1 then 1 else 0 : ℕ) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      by_cases h : j ∈ S.1 <;> simp [twoRowMatOfSet, h]
                _ = (Finset.univ.filter fun j : Fin n => j ∉ S.1).card := by
                      simpa using (Finset.sum_boole (R := ℕ)
                        (fun j : Fin n => j ∉ S.1) (Finset.univ : Finset (Fin n)))
        _ = (S.1ᶜ).card := by
              apply congrArg Finset.card
              ext j
              simp
        _ = n - k := by
              simp [Finset.card_compl, S.2]
  · intro j
    rw [colSum, Fin.sum_univ_two]
    by_cases hj : j ∈ S.1 <;> simp [twoRowMatOfSet, hj]

private def twoRowJohnsonEquiv (n k : ℕ) :
    MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1) ≃ Brualdi.Johnson.JV n k where
  toFun M := ⟨twoRowTopSet M, twoRowTopSet_card M⟩
  invFun S := ⟨twoRowMatOfSet S, twoRowMatOfSet_hasMargins S⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    fin_cases i
    · simp [twoRowMatOfSet, twoRowTopSet]
    · have hb := twoRowBottom_eq_not_top M j
      cases h0 : M.val (0 : Fin 2) j <;> simp [twoRowMatOfSet, twoRowTopSet, h0, hb]
  right_inv S := by
    apply Subtype.ext
    ext j
    simp [twoRowTopSet, twoRowMatOfSet]

private theorem twoRowTop_entry_eq_of_mem_iff {n k : ℕ}
    {M N : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {j : Fin n}
    (h : (j ∈ twoRowTopSet M ↔ j ∈ twoRowTopSet N)) :
    N.val (0 : Fin 2) j = M.val (0 : Fin 2) j := by
  cases hM : M.val (0 : Fin 2) j <;> cases hN : N.val (0 : Fin 2) j <;>
    simp [twoRowTopSet, hM, hN] at h ⊢

private theorem twoRow_entry_eq_of_top_mem_iff {n k : ℕ}
    (M N : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1))
    (j : Fin n) (a : Fin 2)
    (h : (j ∈ twoRowTopSet M ↔ j ∈ twoRowTopSet N)) :
    N.val a j = M.val a j := by
  fin_cases a
  · exact twoRowTop_entry_eq_of_mem_iff h
  · have htop := twoRowTop_entry_eq_of_mem_iff h
    have hN := twoRowBottom_eq_not_top N j
    have hM := twoRowBottom_eq_not_top M j
    simp [hN, hM, htop]

private theorem twoRowTopSet_eq_insert_erase {n k : ℕ}
    {M N : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)} {a b : Fin n}
    (hab : a ≠ b) (hNa : N.val (0 : Fin 2) a = false)
    (hNb : N.val (0 : Fin 2) b = true)
    (hout : ∀ x : Fin n, x ≠ a → x ≠ b → N.val (0 : Fin 2) x = M.val (0 : Fin 2) x) :
    twoRowTopSet N = insert b ((twoRowTopSet M).erase a) := by
  ext x
  by_cases hxa : x = a
  · subst x
    simp [twoRowTopSet, hNa, hab]
  · by_cases hxb : x = b
    · subst x
      simp [twoRowTopSet, hNb]
    · have hxout := hout x hxa hxb
      simp [twoRowTopSet, hxout, hxa, hxb]

private theorem twoRow_interchange_to_inter_card {n k : ℕ}
    (M N : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1))
    (h : Interchange M.val N.val) :
    (twoRowTopSet M ∩ twoRowTopSet N).card = k - 1 := by
  rcases h with ⟨i, i', j, j', hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
      hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
  fin_cases i <;> fin_cases i'
  · exact False.elim (hrne rfl)
  · have houtTop : ∀ x : Fin n, x ≠ j → x ≠ j' →
        N.val (0 : Fin 2) x = M.val (0 : Fin 2) x := by
      intro x hxj hxj'
      exact hout (0 : Fin 2) x (by
        intro hblock
        exact hblock.2.elim hxj hxj')
    have htop := twoRowTopSet_eq_insert_erase (M := M) (N := N) (a := j) (b := j')
      hcne (by simpa using hN₁₁) (by simpa using hN₁₂) houtTop
    have hjM : j ∈ twoRowTopSet M := twoRowTop_mem_of_true (by simpa using hM₁₁)
    have hj'M : j' ∉ twoRowTopSet M := twoRowTop_not_mem_of_false (by simpa using hM₁₂)
    calc
      (twoRowTopSet M ∩ twoRowTopSet N).card
          = (twoRowTopSet M ∩ insert j' ((twoRowTopSet M).erase j)).card := by rw [htop]
      _ = (twoRowTopSet M).card - 1 := card_inter_insert_erase hjM hj'M
      _ = k - 1 := by rw [twoRowTopSet_card]
  · have houtTop : ∀ x : Fin n, x ≠ j' → x ≠ j →
        N.val (0 : Fin 2) x = M.val (0 : Fin 2) x := by
      intro x hxj' hxj
      exact hout (0 : Fin 2) x (by
        intro hblock
        exact hblock.2.elim hxj hxj')
    have htop := twoRowTopSet_eq_insert_erase (M := M) (N := N) (a := j') (b := j)
      (Ne.symm hcne) (by simpa using hN₂₂) (by simpa using hN₂₁) houtTop
    have hj'M : j' ∈ twoRowTopSet M := twoRowTop_mem_of_true (by simpa using hM₂₂)
    have hjM : j ∉ twoRowTopSet M := twoRowTop_not_mem_of_false (by simpa using hM₂₁)
    calc
      (twoRowTopSet M ∩ twoRowTopSet N).card
          = (twoRowTopSet M ∩ insert j ((twoRowTopSet M).erase j')).card := by rw [htop]
      _ = (twoRowTopSet M).card - 1 := card_inter_insert_erase hj'M hjM
      _ = k - 1 := by rw [twoRowTopSet_card]
  · exact False.elim (hrne rfl)

private theorem twoRow_interchange_of_inter_card {n k : ℕ} (hk : 0 < k)
    (M N : MarginClass (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1))
    (hcard : (twoRowTopSet M ∩ twoRowTopSet N).card = k - 1) :
    Interchange M.val N.val := by
  classical
  let S := twoRowTopSet M
  let T := twoRowTopSet N
  have hS : S.card = k := by simpa [S] using twoRowTopSet_card M
  have hT : T.card = k := by simpa [T] using twoRowTopSet_card N
  have hI : (S ∩ T).card = k - 1 := by simpa [S, T] using hcard
  have hSdiff_card : (S \ T).card = 1 := by
    have hsum := Finset.card_sdiff_add_card_inter S T
    rw [hI, hS] at hsum
    omega
  have hTdiff_card : (T \ S).card = 1 := by
    have hsum := Finset.card_sdiff_add_card_inter T S
    have hI' : (T ∩ S).card = k - 1 := by simpa [Finset.inter_comm] using hI
    rw [hI', hT] at hsum
    omega
  obtain ⟨j, hST_single⟩ := Finset.card_eq_one.mp hSdiff_card
  obtain ⟨j', hTS_single⟩ := Finset.card_eq_one.mp hTdiff_card
  have hj_sdiff : j ∈ S \ T := by simp [hST_single]
  have hj'_sdiff : j' ∈ T \ S := by simp [hTS_single]
  have hjS : j ∈ S := (Finset.mem_sdiff.mp hj_sdiff).1
  have hjNotT : j ∉ T := (Finset.mem_sdiff.mp hj_sdiff).2
  have hj'T : j' ∈ T := (Finset.mem_sdiff.mp hj'_sdiff).1
  have hj'NotS : j' ∉ S := (Finset.mem_sdiff.mp hj'_sdiff).2
  have hjne : j ≠ j' := by
    intro hjeq
    exact hjNotT (by simpa [hjeq] using hj'T)
  have hsame_mem : ∀ x : Fin n, x ≠ j → x ≠ j' → (x ∈ S ↔ x ∈ T) := by
    intro x hxj hxj'
    constructor
    · intro hxS
      by_cases hxT : x ∈ T
      · exact hxT
      · have hxsd : x ∈ S \ T := Finset.mem_sdiff.mpr ⟨hxS, hxT⟩
        have hx_single : x ∈ ({j} : Finset (Fin n)) := by simpa [hST_single] using hxsd
        exact False.elim (hxj (by simpa using hx_single))
    · intro hxT
      by_cases hxS : x ∈ S
      · exact hxS
      · have hxsd : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
        have hx_single : x ∈ ({j'} : Finset (Fin n)) := by simpa [hTS_single] using hxsd
        exact False.elim (hxj' (by simpa using hx_single))
  have hM0j : M.val (0 : Fin 2) j = true := twoRowTop_true_of_mem (by simpa [S] using hjS)
  have hN0j : N.val (0 : Fin 2) j = false := twoRowTop_false_of_not_mem (by simpa [T] using hjNotT)
  have hN0j' : N.val (0 : Fin 2) j' = true := twoRowTop_true_of_mem (by simpa [T] using hj'T)
  have hM0j' : M.val (0 : Fin 2) j' = false :=
    twoRowTop_false_of_not_mem (by simpa [S] using hj'NotS)
  have hM1j' : M.val (1 : Fin 2) j' = true := by
    simp [twoRowBottom_eq_not_top M j', hM0j']
  have hM1j : M.val (1 : Fin 2) j = false := by
    simp [twoRowBottom_eq_not_top M j, hM0j]
  have hN1j' : N.val (1 : Fin 2) j' = false := by
    simp [twoRowBottom_eq_not_top N j', hN0j']
  have hN1j : N.val (1 : Fin 2) j = true := by
    simp [twoRowBottom_eq_not_top N j, hN0j]
  refine ⟨(0 : Fin 2), (1 : Fin 2), j, j', ?_, hjne, hM0j, hM1j', hM0j', hM1j,
    hN0j, hN1j', hN0j', hN1j, ?_⟩
  · decide
  · intro a b hnot
    have hrow : a = (0 : Fin 2) ∨ a = (1 : Fin 2) := by
      fin_cases a <;> simp
    have hb_ne_j : b ≠ j := by
      intro hbj
      exact hnot ⟨hrow, Or.inl hbj⟩
    have hb_ne_j' : b ≠ j' := by
      intro hbj'
      exact hnot ⟨hrow, Or.inr hbj'⟩
    have hiffST : b ∈ S ↔ b ∈ T := hsame_mem b hb_ne_j hb_ne_j'
    have hiffTop : b ∈ twoRowTopSet M ↔ b ∈ twoRowTopSet N := by simpa [S, T] using hiffST
    exact twoRow_entry_eq_of_top_mem_iff M N b a hiffTop

theorem flipGraph_two_row_iso_johnson {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Nonempty (Brualdi.flipGraph (![k, n - k] : Fin 2 → ℕ) (fun _ : Fin n => 1)
              ≃g Brualdi.Johnson.Jgraph n k) := by
  classical
  have _hkn : k < n := hkn
  let e := twoRowJohnsonEquiv n k
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [Brualdi.flipGraph, Brualdi.Johnson.Jgraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · apply twoRow_interchange_of_inter_card hk M N
        simpa [e, twoRowJohnsonEquiv] using hrel
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hne (congrArg e hMN)
      · apply twoRow_interchange_of_inter_card hk M N
        simpa [e, twoRowJohnsonEquiv, Finset.inter_comm] using hrel
  · rintro ⟨hne, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa [e, twoRowJohnsonEquiv] using twoRow_interchange_to_inter_card M N hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hne (e.injective heq)
      · simpa [e, twoRowJohnsonEquiv] using twoRow_interchange_to_inter_card N M hrel

/-! ### The §6 base cores, certified PURE-KERNEL (foundations-only, no `native_decide`). -/

private instance instDecidableHasMargins {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (M : ZeroOneMat m n) : Decidable (HasMargins r s M) := by
  unfold HasMargins
  infer_instance

private instance instDecidableInterchange {m n : ℕ} (M N : ZeroOneMat m n) :
    Decidable (Interchange M N) := by
  unfold Interchange
  infer_instance

private def encA : Fin 5 → Fin 3 → Fin 3 → Bool :=
  ![
    ![![true, false, true], ![false, true, false], ![true, false, false]],
    ![![true, false, true], ![true, false, false], ![false, true, false]],
    ![![true, true, false], ![false, false, true], ![true, false, false]],
    ![![true, true, false], ![true, false, false], ![false, false, true]],
    ![![false, true, true], ![true, false, false], ![true, false, false]]
  ]

private theorem encA_hasMargins (i : Fin 5) :
    HasMargins (![2,1,1] : Fin 3 → ℕ) (![2,1,1] : Fin 3 → ℕ) (encA i) := by
  fin_cases i <;> decide

private def decA :
    Fin 5 → MarginClass (![2,1,1] : Fin 3 → ℕ) (![2,1,1] : Fin 3 → ℕ) :=
  fun i => ⟨encA i, encA_hasMargins i⟩

private theorem decA_bijective : Function.Bijective decA := by
  exact (Fintype.bijective_iff_injective_and_card decA).2 ⟨by decide, by decide⟩

private theorem flipGraph_211_adj_decA_iff (i j : Fin 5) :
    (Brualdi.flipGraph (![2,1,1] : Fin 3 → ℕ) (![2,1,1] : Fin 3 → ℕ)).Adj
        (decA i) (decA j) ↔
      (SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreA a b = true)).Adj i j := by
  rw [Brualdi.flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  fin_cases i <;> fin_cases j <;> decide

theorem flipGraph_211_iso_coreA :
    Nonempty (Brualdi.flipGraph (![2,1,1] : Fin 3 → ℕ) (![2,1,1] : Fin 3 → ℕ)
              ≃g SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreA a b = true)) := by
  let e : Fin 5 ≃ MarginClass (![2,1,1] : Fin 3 → ℕ) (![2,1,1] : Fin 3 → ℕ) :=
    Equiv.ofBijective decA decA_bijective
  refine ⟨{ toEquiv := e.symm, map_rel_iff' := ?_ }⟩
  intro M N
  have hM : decA (e.symm M) = M := by
    change e (e.symm M) = M
    exact Equiv.apply_symm_apply e M
  have hN : decA (e.symm N) = N := by
    change e (e.symm N) = N
    exact Equiv.apply_symm_apply e N
  have h := flipGraph_211_adj_decA_iff (e.symm M) (e.symm N)
  simpa [hM, hN] using h.symm

private def encB : Fin 5 → Fin 3 → Fin 3 → Bool :=
  ![
    ![![true, true, false], ![true, true, false], ![false, false, true]],
    ![![false, true, true], ![true, true, false], ![true, false, false]],
    ![![true, false, true], ![true, true, false], ![false, true, false]],
    ![![true, true, false], ![false, true, true], ![true, false, false]],
    ![![true, true, false], ![true, false, true], ![false, true, false]]
  ]

private theorem encB_hasMargins (i : Fin 5) :
    HasMargins (![2,2,1] : Fin 3 → ℕ) (![2,2,1] : Fin 3 → ℕ) (encB i) := by
  fin_cases i <;> decide

private def decB :
    Fin 5 → MarginClass (![2,2,1] : Fin 3 → ℕ) (![2,2,1] : Fin 3 → ℕ) :=
  fun i => ⟨encB i, encB_hasMargins i⟩

private theorem decB_bijective : Function.Bijective decB := by
  exact (Fintype.bijective_iff_injective_and_card decB).2 ⟨by decide, by decide⟩

private theorem flipGraph_221_adj_decB_iff (i j : Fin 5) :
    (Brualdi.flipGraph (![2,2,1] : Fin 3 → ℕ) (![2,2,1] : Fin 3 → ℕ)).Adj
        (decB i) (decB j) ↔
      (SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreB a b = true)).Adj i j := by
  rw [Brualdi.flipGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  fin_cases i <;> fin_cases j <;> decide

theorem flipGraph_221_iso_coreB :
    Nonempty (Brualdi.flipGraph (![2,2,1] : Fin 3 → ℕ) (![2,2,1] : Fin 3 → ℕ)
              ≃g SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreB a b = true)) := by
  let e : Fin 5 ≃ MarginClass (![2,2,1] : Fin 3 → ℕ) (![2,2,1] : Fin 3 → ℕ) :=
    Equiv.ofBijective decB decB_bijective
  refine ⟨{ toEquiv := e.symm, map_rel_iff' := ?_ }⟩
  intro M N
  have hM : decB (e.symm M) = M := by
    change e (e.symm M) = M
    exact Equiv.apply_symm_apply e M
  have hN : decB (e.symm N) = N := by
    change e (e.symm N) = N
    exact Equiv.apply_symm_apply e N
  have h := flipGraph_221_adj_decB_iff (e.symm M) (e.symm N)
  simpa [hM, hN] using h.symm

/-- `G((2,1,1),(2,1,1))` (core A) is Hamilton-connected — pure-kernel `decide` + the checker bridge. -/
theorem coreA_isHamConnected :
    IsHamConnected (SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreA a b = true)) :=
  isHamConnected_of_hcAll Brualdi.FiniteCerts.coreA (by decide) (by decide)

/-- `G((2,2,1),(2,2,1))` (core B) is Hamilton-connected — pure-kernel. -/
theorem coreB_isHamConnected :
    IsHamConnected (SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.coreB a b = true)) :=
  isHamConnected_of_hcAll Brualdi.FiniteCerts.coreB (by decide) (by decide)

/-- `CT₃ = K₃,₃` is Hamilton-laceable (its bipartition colour) — pure-kernel. -/
theorem ct3_isHamLaceable :
    IsHamLaceable (SimpleGraph.fromRel (fun a b => Brualdi.FiniteCerts.ct3 a b = true))
      Brualdi.FiniteCerts.ct3col :=
  isHamLaceable_of_hlAll Brualdi.FiniteCerts.ct3 Brualdi.FiniteCerts.ct3col (by decide) (by decide)

end Brualdi.Ledger
