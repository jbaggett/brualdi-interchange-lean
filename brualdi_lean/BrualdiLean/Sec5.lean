/-
  §5 (reduction_pivot): abstract pivot quotients and the fibre-threading assembly.

  This file deliberately stays independent of `Ledger.lean`: it imports only the common Coleman layer and
  exposes the reusable pivot decomposition and threading statements needed by the §5 branch.
-/
import BrualdiLean.Coleman
import BrualdiLean.Ryser
import BrualdiLean.Sec6
import BrualdiLean.GaleRyser

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace List

/-- Compatibility alias for the manuscript notation: join a list of lists by flattening it. -/
abbrev join {α : Type*} (L : List (List α)) : List α :=
  L.flatten

end List

namespace Brualdi.Ledger

open SimpleGraph

noncomputable section

universe u v

/-! ## D1. Abstract pivot decompositions -/

/-- A bundled projection onto a finite quotient vertex type. -/
structure PivotProjection (V : Type u) (Q : Type v) [Fintype V] [Fintype Q] [DecidableEq Q] where
  proj : V → Q

/-- The fibre over a quotient vertex. -/
def fibre {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (π : V → Q) (q : Q) : Finset V :=
  Finset.univ.filter (fun v => π v = q)

/-- Adjacency in the quotient: two distinct fibres with at least one crossing edge. -/
def quotientAdj {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) : Q → Q → Prop :=
  fun q q' => q ≠ q' ∧ ∃ u ∈ fibre π q, ∃ v ∈ fibre π q', G.Adj u v

theorem quotientAdj_symm {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    {G : SimpleGraph V} {π : V → Q} {q q' : Q}
    (h : quotientAdj G π q q') : quotientAdj G π q' q := by
  rcases h with ⟨hne, u, hu, v, hv, huv⟩
  exact ⟨hne.symm, v, hv, u, hu, huv.symm⟩

/-- The quotient graph induced by `quotientAdj`. -/
def quotientGraph {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) : SimpleGraph Q where
  Adj := quotientAdj G π
  symm := { symm := fun _ _ h => quotientAdj_symm h }
  loopless := { irrefl := fun _ h => h.1 rfl }

/-- Vertices of one fibre incident to the neighbouring fibre. -/
def interface {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) (q q' : Q) : Finset V := by
  classical
  exact (fibre π q).filter (fun u => ∃ v ∈ fibre π q', G.Adj u v)

theorem mem_interface_iff {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    {G : SimpleGraph V} {π : V → Q} {q q' : Q} {u : V} :
    u ∈ interface G π q q' ↔ u ∈ fibre π q ∧ ∃ v ∈ fibre π q', G.Adj u v := by
  classical
  unfold interface
  simp only [Finset.mem_filter]

theorem interface_sub_fibre {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) (q q' : Q) :
    interface G π q q' ⊆ fibre π q := by
  classical
  intro u hu
  exact (mem_interface_iff.mp hu).1

theorem fibres_partition {V : Type u} {Q : Type v} [Fintype V] [Fintype Q]
    [DecidableEq V] [DecidableEq Q] (π : V → Q) :
    Finset.univ = Finset.biUnion Finset.univ (fibre π) := by
  ext v
  simp [fibre]

theorem fibres_disjoint {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (π : V → Q) {q q' : Q} (hne : q ≠ q') :
    Disjoint (fibre π q) (fibre π q') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  exact hne ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hv').2)

/-! ## D2. Threading fibres along a quotient path -/

/-- Boundary adjacency between the last vertex of one list and the first vertex of the next. -/
def listBoundaryAdj5 {α : Type*} (R : α → α → Prop) (l₁ l₂ : List α) : Prop :=
  ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y

/-- The boundary relation between consecutive quotient vertices, read through their runs. -/
def runBoundaryAdj {V : Type u} {Q : Type v} (G : SimpleGraph V) (runs : Q → List V) :
    Q → Q → Prop :=
  fun q q' => listBoundaryAdj5 G.Adj (runs q) (runs q')

/-- The threaded vertex list, written in the manuscript form as a join of quotient-indexed runs. -/
def threadedList {V : Type u} {Q : Type v} (qs : List Q) (runs : Q → List V) : List V :=
  List.join (qs.map runs)

/-- A list-level Hamilton path certificate: simple, spanning, and edge-consecutive. -/
structure IsHamiltonVertexList {V : Type u} (G : SimpleGraph V) (l : List V) : Prop where
  nodup : l.Nodup
  cover : ∀ v : V, v ∈ l
  isChain : l.IsChain G.Adj

theorem thread_fibres {V : Type u} {Q : Type v} [Fintype V] [Fintype Q]
    [DecidableEq V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) (qs : List Q) (runs : Q → List V)
    (_hqs_chain : qs.IsChain (quotientAdj G π))
    (hqs_nodup : qs.Nodup) (hqs_cover : ∀ q : Q, q ∈ qs)
    (hrun_sub : ∀ q : Q, ∀ v ∈ runs q, v ∈ fibre π q)
    (hrun_nodup : ∀ q : Q, (runs q).Nodup)
    (hrun_cover : ∀ q : Q, ∀ v : V, v ∈ fibre π q → v ∈ runs q)
    (hrun_ne : ∀ q : Q, q ∈ qs → runs q ≠ [])
    (hcross : qs.IsChain (runBoundaryAdj G runs))
    (hrun_chain : ∀ q : Q, (runs q).IsChain G.Adj) :
    IsHamiltonVertexList G (threadedList qs runs) := by
  classical
  have hrun_mem_fibre : ∀ {q : Q} {v : V}, v ∈ runs q → v ∈ fibre π q := by
    intro q v hv
    exact hrun_sub q v hv
  refine ⟨?_, ?_, ?_⟩
  · rw [threadedList]
    simpa [List.join, List.flatMap] using
      (List.nodup_flatMap.2
        ⟨fun q _hq => hrun_nodup q,
          hqs_nodup.imp (fun {q q'} hne v hv hv' => by
            have hd : Disjoint (fibre π q) (fibre π q') := fibres_disjoint π hne
            rw [Finset.disjoint_left] at hd
            exact hd (hrun_mem_fibre hv) (hrun_mem_fibre hv'))⟩)
  · intro v
    have hvf : v ∈ fibre π (π v) := by
      simp [fibre]
    have hv_run : v ∈ runs (π v) := hrun_cover (π v) v hvf
    have hq : π v ∈ qs := hqs_cover (π v)
    rw [threadedList]
    simpa [List.join, List.flatMap] using (List.mem_flatMap.mpr ⟨π v, hq, hv_run⟩)
  · rw [threadedList]
    have hno_nil : [] ∉ qs.map runs := by
      intro hnil
      rcases List.mem_map.mp hnil with ⟨q, hq, hqnil⟩
      exact hrun_ne q hq hqnil
    have hinternal : ∀ l ∈ qs.map runs, l.IsChain G.Adj := by
      intro l hl
      rcases List.mem_map.mp hl with ⟨q, _hq, rfl⟩
      exact hrun_chain q
    have hboundary : (qs.map runs).IsChain
        (fun l₁ l₂ => listBoundaryAdj5 G.Adj l₁ l₂) := by
      rw [List.isChain_map]
      exact hcross
    have hflat : (qs.map runs).flatten.IsChain G.Adj :=
      (List.isChain_flatten (R := G.Adj) hno_nil).2 ⟨hinternal, hboundary⟩
    simpa [List.join] using hflat

/-! ## D3. Pivot branch skeleton and assembly -/


/-- The induced graph on one pivot fibre. -/
def fibreGraph {V : Type u} {Q : Type v} [Fintype V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) (q : Q) : SimpleGraph {v : V // π v = q} :=
  G.induce {v : V | π v = q}

-- `flipGraph_connected` (A8, Ryser 1957) was RELOCATED to Coleman.lean on 2026-07-06 so the
-- derived `weak_ct_product` there can transport connectivity; the statement is unchanged.

def CellVaries {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (i : Fin m) (j : Fin n) : Prop :=
  ∃ M N : MarginClass r s, M.val i j ≠ N.val i j

/-- CITED — Brualdi & Manber 1983 (JCTB 35(2):156-170), Theorem 9: for 1≤rᵢ≤n-1 and 1≤sⱼ≤m-1
    (= `IsActive r s`), G(R,S) is prime iff 𝔄(R,S) has no invariant positions. Used direction
    (prime ⇒ invariant-free = pivot-freedom, manuscript Lemma 5.2): "prime" = ¬IsDecomposable (their Thm 1
    + Sabidussi unique factorization ⇒ interchange-graph factors); "no invariant position" = every cell
    varies. AUDITED FAITHFUL 2026-07-03 (full text read). The `hne` guard carries B–M's standing
    nonemptiness assumption: `IsActive` does NOT imply feasibility (r=(2,2,2), s=(1,1,1) is active
    with an empty class, where no cell varies), so without `hne` the axiom was FALSE
    (kernel-checked `False`, 2026-07-04 unsoundness certificate #3). -/
axiom active_prime_cell_varies {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hprime : ¬ IsDecomposable (Brualdi.flipGraph r s))
    (hne : Nonempty (MarginClass r s)) :
    ∀ i j, CellVaries r s i j

/-- CITED **verbatim** — Brualdi 2006 ("Combinatorial Matrix Classes") Thm 6.3.4, the (ii)⟹(i)
    contrapositive: in a nonempty class with **no invariant positions** (= every cell varies, which is
    the book's exact hypothesis), a non-bipartite interchange graph contains a triangle. Nonemptiness
    is supplied by `hnb` (an empty class admits the trivial proper colouring). RE-AUDITED 2026-07-04
    against the book PDF (statement extracted verbatim; no sortedness hypothesis in 6.3.4);
    previously this axiom bundled the Brualdi–Manber Thm 9 bridge — now debundled below. -/
axiom invariantFree_nonbip_has_triangle {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hvar : ∀ i j, CellVaries r s i j)
    (hnb : ¬ ∃ col : MarginClass r s → Bool, ∀ M N, (flipGraph r s).Adj M N → col M ≠ col N) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧ (flipGraph r s).Adj M0 M2

/-- The active/prime form used by §5, now a **theorem**: the invariant-free hypothesis of
    Thm 6.3.4 is supplied by Brualdi–Manber Thm 9 (`active_prime_cell_varies`). -/
theorem nonbip_has_triangle {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hprime : ¬ IsDecomposable (flipGraph r s))
    (hnb : ¬ ∃ col : MarginClass r s → Bool, ∀ M N, (flipGraph r s).Adj M N → col M ≠ col N) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧ (flipGraph r s).Adj M0 M2 := by
  have hne : Nonempty (MarginClass r s) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hnb ⟨fun _ => false, fun M => (h.false M).elim⟩
  exact invariantFree_nonbip_has_triangle r s (active_prime_cell_varies r s hact hprime hne) hnb

/-- The concrete data needed after the §5 line-choice, parity, and IH path extraction are complete. -/
structure PivotThreadData {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) where
  Q : Type u
  [instFintypeQ : Fintype Q]
  [instDecidableEqQ : DecidableEq Q]
  π : V → Q
  qs : List Q
  runs : Q → List V
  hqs_chain : qs.IsChain (quotientAdj G π)
  hqs_nodup : qs.Nodup
  hqs_cover : ∀ q : Q, q ∈ qs
  hrun_sub : ∀ q : Q, ∀ v ∈ runs q, v ∈ fibre π q
  hrun_nodup : ∀ q : Q, (runs q).Nodup
  hrun_cover : ∀ q : Q, ∀ v : V, v ∈ fibre π q → v ∈ runs q
  hrun_ne : ∀ q : Q, q ∈ qs → runs q ≠ []
  hcross : qs.IsChain (runBoundaryAdj G runs)
  hrun_chain : ∀ q : Q, (runs q).IsChain G.Adj
  hhead : (threadedList qs runs).head? = some a
  hlast : (threadedList qs runs).getLast? = some b

attribute [instance] PivotThreadData.instFintypeQ PivotThreadData.instDecidableEqQ


private theorem head?_eq_head_of_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    l.head? = some (l.head h) := by
  cases l with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

theorem hasHamPath_of_pivotThreadData {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (d : PivotThreadData G a b) :
    HasHamPath G a b := by
  classical
  let l : List V := threadedList d.qs d.runs
  have hthread : IsHamiltonVertexList G l := by
    simpa [l] using
      thread_fibres G d.π d.qs d.runs d.hqs_chain d.hqs_nodup d.hqs_cover
        d.hrun_sub d.hrun_nodup d.hrun_cover d.hrun_ne d.hcross d.hrun_chain
  have hhead : l.head? = some a := by
    simpa [l] using d.hhead
  have hlast : l.getLast? = some b := by
    simpa [l] using d.hlast
  have hl_ne : l ≠ [] := by
    intro hnil
    rw [hnil] at hhead
    simp at hhead
  have hstart : l.head hl_ne = a := by
    have hsome : some (l.head hl_ne) = some a :=
      (head?_eq_head_of_ne_nil hl_ne).symm.trans hhead
    exact Option.some.inj hsome
  have hend : l.getLast hl_ne = b := by
    have hsome : some (l.getLast hl_ne) = some b :=
      (List.getLast?_eq_getLast_of_ne_nil hl_ne).symm.trans hlast
    exact Option.some.inj hsome
  let p₀ : G.Walk (l.head hl_ne) (l.getLast hl_ne) :=
    SimpleGraph.Walk.ofSupport l hl_ne hthread.isChain
  let p : G.Walk a b := p₀.copy hstart hend
  refine ⟨p, ?_⟩
  have hp₀_support : p₀.support = l := by
    simp [p₀]
  have hp₀_path : p₀.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hp₀_support]
    exact hthread.nodup)
  have hp₀_ham : p₀.IsHamiltonian := hp₀_path.isHamiltonian_of_mem (fun x => by
    rw [hp₀_support]
    exact hthread.cover x)
  intro x
  simpa [p, SimpleGraph.Walk.support_copy] using hp₀_ham x


/-! ## Block 1: row-pattern fibres of margin classes -/

/-- The row pattern of a margin-class matrix along a fixed row. -/
def rowPat {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ} (L : Fin m) :
    MarginClass r s → (Fin n → Bool) :=
  fun M b => M.val L b

private def dropRow {m n : ℕ} (i : Fin (m + 1)) (M : ZeroOneMat (m + 1) n) :
    ZeroOneMat m n :=
  fun a b => M (i.succAbove a) b

private def insertRow {m n : ℕ} (i : Fin (m + 1)) (p : Fin n → Bool)
    (M : ZeroOneMat m n) : ZeroOneMat (m + 1) n :=
  fun a b => Fin.insertNth (α := fun _ : Fin (m + 1) => Bool) i (p b) (fun k => M k b) a

private theorem rowPat_count_eq {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {i : Fin (m + 1)} {p : Fin n → Bool} (M : MarginClass r s)
    (hM : rowPat i M = p) :
    (∑ b : Fin n, (if p b then 1 else 0 : ℕ)) = r i := by
  calc
    (∑ b : Fin n, (if p b then 1 else 0 : ℕ))
        = rowSum M.val i := by
            simp only [rowSum]
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hb : M.val i b = p b := congrFun hM b
            rw [← hb]
    _ = r i := M.property.1 i

private theorem rowPat_col_le {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {i : Fin (m + 1)} {p : Fin n → Bool} (M : MarginClass r s)
    (hM : rowPat i M = p) :
    ∀ b : Fin n, (if p b then 1 else 0 : ℕ) ≤ s b := by
  intro b
  have hirow : M.val i b = p b := congrFun hM b
  have hcol :
      (if p b then 1 else 0 : ℕ) + colSum (dropRow i M.val) b = s b := by
    calc
      (if p b then 1 else 0 : ℕ) + colSum (dropRow i M.val) b
          = colSum M.val b := by
              have hsplit := Fin.sum_univ_succAbove
                (fun a : Fin (m + 1) => (if M.val a b then 1 else 0 : ℕ)) i
              change (if p b then 1 else 0 : ℕ) +
                  (∑ a : Fin m, (if M.val (i.succAbove a) b then 1 else 0 : ℕ)) =
                ∑ a : Fin (m + 1), (if M.val a b then 1 else 0 : ℕ)
              simpa [hirow] using hsplit.symm
      _ = s b := M.property.2 b
  omega

private theorem dropRow_hasMargins_pattern {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} {p : Fin n → Bool} (M : MarginClass r s)
    (hM : rowPat i M = p) :
    HasMargins (fun a : Fin m => r (i.succAbove a))
      (fun b => s b - (if p b then 1 else 0)) (dropRow i M.val) := by
  constructor
  · intro a
    change rowSum M.val (i.succAbove a) = r (i.succAbove a)
    exact M.property.1 (i.succAbove a)
  · intro b
    have hirow : M.val i b = p b := congrFun hM b
    have hcol :
        (if p b then 1 else 0 : ℕ) + colSum (dropRow i M.val) b = s b := by
      calc
        (if p b then 1 else 0 : ℕ) + colSum (dropRow i M.val) b
            = colSum M.val b := by
                have hsplit := Fin.sum_univ_succAbove
                  (fun a : Fin (m + 1) => (if M.val a b then 1 else 0 : ℕ)) i
                change (if p b then 1 else 0 : ℕ) +
                    (∑ a : Fin m, (if M.val (i.succAbove a) b then 1 else 0 : ℕ)) =
                  ∑ a : Fin (m + 1), (if M.val a b then 1 else 0 : ℕ)
                simpa [hirow] using hsplit.symm
        _ = s b := M.property.2 b
    exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hcol)

private theorem insertRow_hasMargins {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} {p : Fin n → Bool}
    (hrow : (∑ b : Fin n, (if p b then 1 else 0 : ℕ)) = r i)
    (hcol_le : ∀ b : Fin n, (if p b then 1 else 0 : ℕ) ≤ s b)
    (M : MarginClass (fun a : Fin m => r (i.succAbove a))
      (fun b => s b - (if p b then 1 else 0))) :
    HasMargins r s (insertRow i p M.val) := by
  constructor
  · intro a
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      calc
        rowSum (insertRow i p M.val) i
            = ∑ b : Fin n, (if p b then 1 else 0 : ℕ) := by
                simp only [rowSum, insertRow, Fin.insertNth_apply_same]
        _ = r i := hrow
    · rw [hsucc]
      calc
        rowSum (insertRow i p M.val) (i.succAbove a0)
            = rowSum M.val a0 := by
                simp only [rowSum, insertRow, Fin.insertNth_apply_succAbove]
        _ = r (i.succAbove a0) := M.property.1 a0
  · intro b
    calc
      colSum (insertRow i p M.val) b
          = ∑ a : Fin (m + 1), (if insertRow i p M.val a b then 1 else 0 : ℕ) := by
              rfl
      _ = (if insertRow i p M.val i b then 1 else 0 : ℕ) +
            ∑ a : Fin m, (if insertRow i p M.val (i.succAbove a) b then 1 else 0 : ℕ) := by
          exact Fin.sum_univ_succAbove
            (fun a : Fin (m + 1) => (if insertRow i p M.val a b then 1 else 0 : ℕ)) i
      _ = (if p b then 1 else 0 : ℕ) + colSum M.val b := by
          simp only [colSum, insertRow, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove]
      _ = (if p b then 1 else 0 : ℕ) + (s b - (if p b then 1 else 0 : ℕ)) := by
          rw [M.property.2 b]
      _ = s b := by
          have hb := hcol_le b
          omega

private def fibreRowEquiv {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (i : Fin (m + 1)) (p : Fin n → Bool)
    (hne : Nonempty {M : MarginClass r s // rowPat i M = p}) :
    {M : MarginClass r s // rowPat i M = p} ≃
      MarginClass (fun a : Fin m => r (i.succAbove a))
        (fun b => s b - (if p b then 1 else 0)) where
  toFun M := ⟨dropRow i M.val.val, dropRow_hasMargins_pattern (i := i) M.val M.property⟩
  invFun M :=
    let hrow : (∑ b : Fin n, (if p b then 1 else 0 : ℕ)) = r i := by
      rcases hne with ⟨W⟩
      exact rowPat_count_eq W.val W.property
    let hcol_le : ∀ b : Fin n, (if p b then 1 else 0 : ℕ) ≤ s b := by
      rcases hne with ⟨W⟩
      exact rowPat_col_le W.val W.property
    ⟨⟨insertRow i p M.val, insertRow_hasMargins (i := i) hrow hcol_le M⟩, by
      funext b
      simp only [rowPat, insertRow, Fin.insertNth_apply_same]⟩
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    funext a b
    rcases Fin.eq_self_or_eq_succAbove i a with hsame | ⟨a0, hsucc⟩
    · rw [hsame]
      simp only [insertRow, Fin.insertNth_apply_same]
      exact (congrFun M.property b).symm
    · rw [hsucc]
      simp only [dropRow, insertRow, Fin.insertNth_apply_succAbove]
  right_inv M := by
    apply Subtype.ext
    funext a b
    simp only [dropRow, insertRow, Fin.insertNth_apply_succAbove]

private theorem interchange_drop_iff_of_row_eq {m n : ℕ} {M N : ZeroOneMat (m + 1) n}
    {i : Fin (m + 1)} {p : Fin n → Bool}
    (hM : ∀ b, M i b = p b) (hN : ∀ b, N i b = p b) :
    Interchange M N ↔ Interchange (dropRow i M) (dropRow i N) := by
  constructor
  · rintro ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
        hN₁₁, hN₂₂, hN₁₂, hN₂₁, hout⟩
    have hr₁_ne_i : r₁ ≠ i := by
      intro hri
      have hsame : M r₁ c₁ = N r₁ c₁ := by rw [hri, hM c₁, hN c₁]
      rw [hsame, hN₁₁] at hM₁₁
      exact Bool.false_ne_true hM₁₁
    have hr₂_ne_i : r₂ ≠ i := by
      intro hri
      have hsame : M r₂ c₂ = N r₂ c₂ := by rw [hri, hM c₂, hN c₂]
      rw [hsame, hN₂₂] at hM₂₂
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

private theorem fibreRowEquiv_interchange_iff {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {i : Fin (m + 1)} {p : Fin n → Bool}
    (hne : Nonempty {M : MarginClass r s // rowPat i M = p})
    (M N : {M : MarginClass r s // rowPat i M = p}) :
    Interchange ((fibreRowEquiv r s i p hne M).val)
      ((fibreRowEquiv r s i p hne N).val) ↔ Interchange M.val.val N.val.val := by
  exact (interchange_drop_iff_of_row_eq (i := i)
    (M := M.val.val) (N := N.val.val)
    (p := p) (congrFun M.property) (congrFun N.property)).symm

theorem flipGraph_fibre_row {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (p : Fin n → Bool)
    (hne : Nonempty {M : MarginClass r s // rowPat L M = p}) :
    Nonempty (fibreGraph (flipGraph r s) (rowPat L) p ≃g
      flipGraph (fun a => r (L.succAbove a)) (fun b => s b - (if p b then 1 else 0))) := by
  let e := fibreRowEquiv r s L p hne
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  rw [fibreGraph, Brualdi.flipGraph, Brualdi.flipGraph, SimpleGraph.induce_adj,
    SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hneMN, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro hMN
        exact hneMN (congrArg e (Subtype.ext hMN))
      · simpa only [e] using (fibreRowEquiv_interchange_iff (r := r) (s := s)
          (i := L) (p := p) hne M N).mp hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro hMN
        exact hneMN (congrArg e (Subtype.ext hMN))
      · simpa only [e] using (fibreRowEquiv_interchange_iff (r := r) (s := s)
          (i := L) (p := p) hne N M).mp hrel
  · rintro ⟨hneMN, hrel | hrel⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro heq
        exact hneMN (congrArg Subtype.val (e.injective heq))
      · simpa only [e] using (fibreRowEquiv_interchange_iff (r := r) (s := s)
          (i := L) (p := p) hne M N).mpr hrel
    · refine ⟨?_, Or.inr ?_⟩
      · intro heq
        exact hneMN (congrArg Subtype.val (e.injective heq))
      · simpa only [e] using (fibreRowEquiv_interchange_iff (r := r) (s := s)
          (i := L) (p := p) hne N M).mpr hrel

theorem isInterchangeGraph_of_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hH : IsInterchangeGraph H) : IsInterchangeGraph G := by
  rcases hH with ⟨m, n, r, s, φ, hφ⟩
  refine ⟨m, n, r, s, e.toEquiv.trans φ, ?_⟩
  intro a b
  exact e.map_rel_iff.symm.trans (hφ (e a) (e b))

theorem fibre_isInterchangeGraph {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (p : Fin n → Bool)
    (hne : Nonempty {M : MarginClass r s // rowPat L M = p}) :
    IsInterchangeGraph (fibreGraph (flipGraph r s) (rowPat L) p) := by
  rcases flipGraph_fibre_row r s L p hne with ⟨e⟩
  exact isInterchangeGraph_of_iso e
    ⟨m, n, (fun a => r (L.succAbove a)), (fun b => s b - (if p b then 1 else 0)),
      Equiv.refl _, fun _ _ => Iff.rfl⟩

theorem card_fibre_lt {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (p : Fin n → Bool)
    (hwit : ∃ M : MarginClass r s, rowPat L M ≠ p) :
    Fintype.card {M : MarginClass r s // rowPat L M = p} < Fintype.card (MarginClass r s) := by
  rcases hwit with ⟨M, hM⟩
  exact Fintype.card_subtype_lt (p := fun M : MarginClass r s => rowPat L M = p)
    (x := M) hM

/-! ## Block 2a: concrete row-quotient infrastructure (reuses Block 1; no cited axioms) -/

/-- Two distinct matrices of a class differ on some row, so a separating row exists. -/
theorem exists_separating_row {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    (a b : MarginClass r s) (hab : a ≠ b) : ∃ L : Fin (m + 1), rowPat L a ≠ rowPat L b := by
  by_contra h
  push_neg at h
  apply hab
  apply Subtype.ext
  funext i j
  exact congrFun (h i) j

/-- Every realizable fibre of a separating row is a strictly smaller interchange graph. -/
theorem rowFibre_interchange_and_smaller {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {a b : MarginClass r s} (hsep : rowPat L a ≠ rowPat L b)
    (p : Fin n → Bool) (hne : Nonempty {M : MarginClass r s // rowPat L M = p}) :
    IsInterchangeGraph (fibreGraph (flipGraph r s) (rowPat L) p) ∧
      Fintype.card {M : MarginClass r s // rowPat L M = p} <
        Fintype.card (MarginClass r s) := by
  refine ⟨fibre_isInterchangeGraph r s L p hne, ?_⟩
  have hwit : ∃ M : MarginClass r s, rowPat L M ≠ p := by
    by_cases ha : rowPat L a = p
    · exact ⟨b, fun hb => hsep (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  exact card_fibre_lt r s L p hwit

/-- Each realizable fibre of a separating row is `IsMH`, via the induction hypothesis. -/
theorem rowFibre_isMH {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {a b : MarginClass r s} (hsep : rowPat L a ≠ rowPat L b)
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card (MarginClass r s) → IsInterchangeGraph H → IsMH H)
    (p : Fin n → Bool) (hne : Nonempty {M : MarginClass r s // rowPat L M = p}) :
    IsMH (fibreGraph (flipGraph r s) (rowPat L) p) := by
  obtain ⟨hIG, hcard⟩ := rowFibre_interchange_and_smaller (a := a) (b := b) hsep p hne
  exact IH _ hcard hIG

/-! ## Block 2-I: row-pattern matroid quotient and crossing exchange edges -/

/-! ### Lemma 5.3 machinery (Stage A): difference-count calculus (paper numbers per the 2026-07-04 renumbering: old 5.4→5.3, 5.4a→5.4, 5.7c→5.8, 5.7d→5.9, 5.7b→5.10, 5.8→5.11, 5.8a→5.12, 5.9–5.11→5.13–5.15) -/

/-- Number of cells where two matrices differ. -/
private def diffCount {m n : ℕ} (M N : ZeroOneMat m n) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin n)).filter (fun x => M x.1 x.2 ≠ N x.1 x.2)).card

/-- A switch leaves rows outside the switched pair untouched. -/
private theorem switchMat_row_untouched {m n : ℕ} (M : ZeroOneMat m n)
    (i i' : Fin m) (j j' : Fin n) {w : Fin m} (hwi : w ≠ i) (hwi' : w ≠ i') (b : Fin n) :
    Brualdi.Ryser.switchMat M i i' j j' w b = M w b := by
  simp [Brualdi.Ryser.switchMat, hwi, hwi']

/-- A switch leaves columns outside the switched pair untouched. -/
private theorem switchMat_col_untouched {m n : ℕ} (M : ZeroOneMat m n)
    (i i' : Fin m) (j j' : Fin n) (w : Fin m) {b : Fin n} (hbj : b ≠ j) (hbj' : b ≠ j') :
    Brualdi.Ryser.switchMat M i i' j j' w b = M w b := by
  simp [Brualdi.Ryser.switchMat, hbj, hbj']

/-- The four cells of a switch block, as a finset of index pairs. -/
private def blockCells {m n : ℕ} (i i' : Fin m) (j j' : Fin n) :
    Finset (Fin m × Fin n) :=
  {(i, j), (i, j'), (i', j), (i', j')}

private theorem mem_blockCells {m n : ℕ} {i i' : Fin m} {j j' : Fin n}
    {x : Fin m × Fin n} :
    x ∈ blockCells i i' j j' ↔
      x = (i, j) ∨ x = (i, j') ∨ x = (i', j) ∨ x = (i', j') := by
  simp [blockCells]

private theorem blockCells_card {m n : ℕ} {i i' : Fin m} {j j' : Fin n}
    (hii : i ≠ i') (hjj : j ≠ j') : (blockCells i i' j j').card = 4 := by
  have h1 : ((i, j) : Fin m × Fin n) ≠ (i, j') := fun h => hjj (congrArg Prod.snd h)
  have h2 : ((i, j) : Fin m × Fin n) ≠ (i', j) := fun h => hii (congrArg Prod.fst h)
  have h3 : ((i, j) : Fin m × Fin n) ≠ (i', j') := fun h => hii (congrArg Prod.fst h)
  have h4 : ((i, j') : Fin m × Fin n) ≠ (i', j) := fun h => hii (congrArg Prod.fst h)
  have h5 : ((i, j') : Fin m × Fin n) ≠ (i', j') := fun h => hii (congrArg Prod.fst h)
  have h6 : ((i', j) : Fin m × Fin n) ≠ (i', j') := fun h => hjj (congrArg Prod.snd h)
  simp [blockCells, h1, h2, h3, h4, h5, h6]

/-- On the block, a switch flips the cell value. -/
private theorem switch_flips_block {m n : ℕ} {M : ZeroOneMat m n}
    {i i' : Fin m} {j j' : Fin n} (hb : Brualdi.Ryser.SwitchBlock M i i' j j')
    {x : Fin m × Fin n} (hx : x ∈ blockCells i i' j j') :
    Brualdi.Ryser.switchMat M i i' j j' x.1 x.2 = ! M x.1 x.2 := by
  obtain ⟨hii, hjj, h11, h22, h12, h21⟩ := hb
  rcases mem_blockCells.mp hx with rfl | rfl | rfl | rfl
  · simp [Brualdi.Ryser.switchMat, h11]
  · simp [Brualdi.Ryser.switchMat, hjj.symm, hii, h12]
  · simp [Brualdi.Ryser.switchMat, hii.symm, hjj, h21]
  · simp [Brualdi.Ryser.switchMat, hii.symm, hjj.symm, h22]

/-- Off the block, a switch leaves the cell untouched. -/
private theorem switch_off_block {m n : ℕ} (M : ZeroOneMat m n)
    (i i' : Fin m) (j j' : Fin n) {x : Fin m × Fin n}
    (hx : x ∉ blockCells i i' j j') :
    Brualdi.Ryser.switchMat M i i' j j' x.1 x.2 = M x.1 x.2 := by
  simp only [mem_blockCells, not_or] at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  by_cases hxi : x.1 = i
  · exact switchMat_col_untouched M i i' j j' x.1
      (fun h => h1 (Prod.ext hxi h)) (fun h => h2 (Prod.ext hxi h))
  · by_cases hxi' : x.1 = i'
    · exact switchMat_col_untouched M i i' j j' x.1
        (fun h => h3 (Prod.ext hxi' h)) (fun h => h4 (Prod.ext hxi' h))
    · exact switchMat_row_untouched M i i' j j' hxi hxi' x.2

/-- If at least three of the four block cells differ from `N`, the switch strictly
    decreases the difference count. -/
private theorem diffCount_switch_lt {m n : ℕ} {M N : ZeroOneMat m n}
    {i i' : Fin m} {j j' : Fin n} (hb : Brualdi.Ryser.SwitchBlock M i i' j j')
    (hthree : 3 ≤ ((blockCells i i' j j').filter
      (fun x => M x.1 x.2 ≠ N x.1 x.2)).card) :
    diffCount (Brualdi.Ryser.switchMat M i i' j j') N < diffCount M N := by
  classical
  set M' := Brualdi.Ryser.switchMat M i i' j j' with hM'
  set Bl := blockCells i i' j j' with hBl
  have hcard4 : Bl.card = 4 := blockCells_card hb.1 hb.2.1
  have hsplit : ∀ P : Fin m × Fin n → Prop, ∀ _ : DecidablePred P,
      ((Finset.univ : Finset (Fin m × Fin n)).filter P).card
        = (Bl.filter P).card + ((Finset.univ \ Bl).filter P).card := by
    intro P _
    rw [← Finset.card_union_of_disjoint]
    · rw [← Finset.filter_union, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    · exact Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have hoff : ((Finset.univ \ Bl).filter (fun x => M' x.1 x.2 ≠ N x.1 x.2))
      = ((Finset.univ \ Bl).filter (fun x => M x.1 x.2 ≠ N x.1 x.2)) := by
    apply Finset.filter_congr
    intro x hx
    rw [hM', switch_off_block M i i' j j' (Finset.mem_sdiff.mp hx).2]
  have hblock : (Bl.filter (fun x => M' x.1 x.2 ≠ N x.1 x.2)).card
      = 4 - (Bl.filter (fun x => M x.1 x.2 ≠ N x.1 x.2)).card := by
    have hcompl : Bl.filter (fun x => M' x.1 x.2 ≠ N x.1 x.2)
        = Bl.filter (fun x => ¬ (M x.1 x.2 ≠ N x.1 x.2)) := by
      apply Finset.filter_congr
      intro x hx
      rw [hM', switch_flips_block hb hx]
      cases hMx : M x.1 x.2 <;> cases hNx : N x.1 x.2 <;> simp
    rw [hcompl, Finset.filter_not, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hcard4]
  have hblock_le : (Bl.filter (fun x => M x.1 x.2 ≠ N x.1 x.2)).card ≤ 4 := by
    calc (Bl.filter (fun x => M x.1 x.2 ≠ N x.1 x.2)).card
        ≤ Bl.card := Finset.card_filter_le _ _
      _ = 4 := hcard4
  have hM'count := hsplit (fun x => M' x.1 x.2 ≠ N x.1 x.2) (by infer_instance)
  have hMcount := hsplit (fun x => M x.1 x.2 ≠ N x.1 x.2) (by infer_instance)
  unfold diffCount
  rw [hM'count, hMcount, hoff, hblock]
  omega


/-- Difference count is symmetric. -/
private theorem diffCount_comm {m n : ℕ} (M N : ZeroOneMat m n) :
    diffCount M N = diffCount N M := by
  unfold diffCount
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [ne_comm]

/-- Split a Bool-count by the value of a second Bool function. -/
private theorem count_split_pair {α : Type*} [DecidableEq α] (s : Finset α)
    (f g : α → Bool) :
    (s.filter (fun a => f a = true)).card
      = (s.filter (fun a => f a = true ∧ g a = true)).card
        + (s.filter (fun a => f a = true ∧ g a = false)).card := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s.filter (fun a => f a = true)) (p := fun a => g a = true)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have h2 : (s.filter (fun a => f a = true ∧ ¬ g a = true))
      = (s.filter (fun a => f a = true ∧ g a = false)) := by
    apply Finset.filter_congr
    intro a _
    simp [Bool.not_eq_true]
  rw [h2] at h
  omega

/-- Column balance: same column sums split into P/Q/both parts over the non-`L` rows. -/
private theorem pq_col_balance {m n : ℕ} {M N : ZeroOneMat (m + 1) n}
    {c : Fin n} (hcol : colSum M c = colSum N c) (L : Fin (m + 1)) :
    ((Finset.univ.erase L).filter (fun a => M a c = true ∧ N a c = false)).card
        + (if M L c = true then 1 else 0)
      = ((Finset.univ.erase L).filter (fun a => M a c = false ∧ N a c = true)).card
        + (if N L c = true then 1 else 0) := by
  classical
  have hsumM : colSum M c
      = (if M L c = true then 1 else 0)
        + ((Finset.univ.erase L).filter (fun a => M a c = true)).card := by
    unfold colSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L)]
    congr 1
    rw [Finset.sum_boole]
    simp
  have hsumN : colSum N c
      = (if N L c = true then 1 else 0)
        + ((Finset.univ.erase L).filter (fun a => N a c = true)).card := by
    unfold colSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L)]
    congr 1
    rw [Finset.sum_boole]
    simp
  have hMsplit := count_split_pair (Finset.univ.erase L)
    (fun a => M a c) (fun a => N a c)
  have hNsplit := count_split_pair (Finset.univ.erase L)
    (fun a => N a c) (fun a => M a c)
  have hcomm : ((Finset.univ.erase L).filter (fun a => N a c = true ∧ M a c = true))
      = ((Finset.univ.erase L).filter (fun a => M a c = true ∧ N a c = true)) := by
    apply Finset.filter_congr
    intro a _
    constructor <;> exact fun h => ⟨h.2, h.1⟩
  have hcomm2 : ((Finset.univ.erase L).filter (fun a => N a c = true ∧ M a c = false))
      = ((Finset.univ.erase L).filter (fun a => M a c = false ∧ N a c = true)) := by
    apply Finset.filter_congr
    intro a _
    constructor <;> exact fun h => ⟨h.2, h.1⟩
  rw [hsumM, hsumN, hMsplit, hNsplit, hcomm, hcomm2] at hcol
  omega

/-- Row balance over the columns, for a non-pivot row of two same-margin matrices. -/
private theorem pq_row_balance {m n : ℕ} {M N : ZeroOneMat m n}
    {a : Fin m} (hrow : rowSum M a = rowSum N a) :
    ((Finset.univ : Finset (Fin n)).filter (fun c => M a c = true ∧ N a c = false)).card
      = ((Finset.univ : Finset (Fin n)).filter (fun c => M a c = false ∧ N a c = true)).card := by
  classical
  have hsumM : rowSum M a
      = ((Finset.univ : Finset (Fin n)).filter (fun c => M a c = true)).card := by
    unfold rowSum
    rw [Finset.sum_boole]
    simp
  have hsumN : rowSum N a
      = ((Finset.univ : Finset (Fin n)).filter (fun c => N a c = true)).card := by
    unfold rowSum
    rw [Finset.sum_boole]
    simp
  have hMsplit := count_split_pair (Finset.univ : Finset (Fin n))
    (fun c => M a c) (fun c => N a c)
  have hNsplit := count_split_pair (Finset.univ : Finset (Fin n))
    (fun c => N a c) (fun c => M a c)
  have hcomm : ((Finset.univ : Finset (Fin n)).filter (fun c => N a c = true ∧ M a c = true))
      = ((Finset.univ : Finset (Fin n)).filter (fun c => M a c = true ∧ N a c = true)) := by
    apply Finset.filter_congr
    intro c _
    constructor <;> exact fun h => ⟨h.2, h.1⟩
  have hcomm2 : ((Finset.univ : Finset (Fin n)).filter (fun c => N a c = true ∧ M a c = false))
      = ((Finset.univ : Finset (Fin n)).filter (fun c => M a c = false ∧ N a c = true)) := by
    apply Finset.filter_congr
    intro c _
    constructor <;> exact fun h => ⟨h.2, h.1⟩
  rw [hsumM, hsumN, hMsplit, hNsplit, hcomm, hcomm2] at hrow
  omega

/-- Counting swap: summing filtered column-counts over rows equals summing filtered
    row-counts over columns. -/
private theorem sum_card_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    (∑ a ∈ S, (T.filter (fun c => P a c)).card)
      = ∑ c ∈ T, (S.filter (fun a => P a c)).card := by
  classical
  have h1 : ∀ a, (T.filter (fun c => P a c)).card
      = ∑ c ∈ T, (if P a c then 1 else 0) := by
    intro a
    rw [Finset.sum_boole]
    simp
  have h2 : ∀ c, (S.filter (fun a => P a c)).card
      = ∑ a ∈ S, (if P a c then 1 else 0) := by
    intro c
    rw [Finset.sum_boole]
    simp
  simp only [h1, h2]
  exact Finset.sum_comm

/-- A finite matroid base family, packaged only by the base-exchange axiom needed in §5. -/
structure BaseFamily (α : Type u) [Fintype α] [DecidableEq α] where
  Base : Finset α → Prop
  exists_base : ∃ B, Base B
  exchange : ∀ {A B : Finset α} {e : α}, Base A → Base B → e ∈ A → e ∉ B →
      ∃ f ∈ B, f ∉ A ∧ Base (insert f (A.erase e))

/-- The usual base-exchange graph: two bases are adjacent iff they differ by one element each way. -/
def baseExchangeGraph {α : Type u} [Fintype α] [DecidableEq α] (B : BaseFamily α) :
    SimpleGraph {X : Finset α // B.Base X} :=
  SimpleGraph.fromRel (fun X Y => (X.val \ Y.val).card = 1 ∧ (Y.val \ X.val).card = 1)

/-- CITED — Naddef & Pulleyblank 1981, "Hamiltonicity and combinatorial polyhedra", JCTB 31:297-312,
    Thm 3.3.1 + Cor 3.3.2: matroid bases form a combinatorial set and the base-exchange graph of a
    matroid is a hypercube or Hamilton-connected; a NON-bipartite one is thus Hamilton-connected.
    AUDITED 2026-07-03 (PDF read; faithful; 1981 is the correct/sufficient paper — not 1984). -/
axiom naddef_pulleyblank_baseExchange {α} [Fintype α] [DecidableEq α] (B : BaseFamily α) :
    ¬ (∃ col : {X : Finset α // B.Base X} → Bool,
        ∀ X Y, (baseExchangeGraph B).Adj X Y → col X ≠ col Y) →
      IsHamConnected (baseExchangeGraph B)

/-- Transferring a single 1 from position `j` to position `i` within a Bool row preserves the count. -/
private theorem sum_boolfun_transfer {n : ℕ} {f g : Fin n → Bool} {i j : Fin n}
    (hij : i ≠ j) (hfi : f i = false) (hgi : g i = true)
    (hfj : f j = true) (hgj : g j = false)
    (hrest : ∀ y, y ≠ i → y ≠ j → f y = g y) :
    (∑ y, (if f y = true then (1:ℕ) else 0)) = ∑ y, (if g y = true then (1:ℕ) else 0) := by
  classical
  have hji : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
  have hrest' : (∑ y ∈ (Finset.univ.erase i).erase j, (if f y = true then (1:ℕ) else 0))
      = ∑ y ∈ (Finset.univ.erase i).erase j, (if g y = true then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hrest y (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
      (Finset.mem_erase.mp hy).1]
  calc (∑ y, (if f y = true then (1:ℕ) else 0))
      = (if f i = true then (1:ℕ) else 0)
          + ∑ y ∈ Finset.univ.erase i, (if f y = true then (1:ℕ) else 0) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    _ = (if f i = true then (1:ℕ) else 0) + ((if f j = true then (1:ℕ) else 0)
          + ∑ y ∈ (Finset.univ.erase i).erase j, (if f y = true then (1:ℕ) else 0)) := by
        rw [Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase i)
          (fun y => if f y = true then (1:ℕ) else 0) hji]
    _ = (if g i = true then (1:ℕ) else 0) + ((if g j = true then (1:ℕ) else 0)
          + ∑ y ∈ (Finset.univ.erase i).erase j, (if g y = true then (1:ℕ) else 0)) := by
        rw [hrest']
        simp [hfi, hfj, hgi, hgj]
    _ = (if g i = true then (1:ℕ) else 0)
          + ∑ y ∈ Finset.univ.erase i, (if g y = true then (1:ℕ) else 0) := by
        rw [Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase i)
          (fun y => if g y = true then (1:ℕ) else 0) hji]
    _ = ∑ y, (if g y = true then (1:ℕ) else 0) :=
        Finset.add_sum_erase Finset.univ
          (fun y => if g y = true then (1:ℕ) else 0) (Finset.mem_univ i)

/-- Flipping a single position from 1 down to 0 drops the count by one. -/
private theorem sum_boolfun_flipdown {m : ℕ} {f g : Fin m → Bool} {a : Fin m}
    (hfa : f a = false) (hga : g a = true)
    (hrest : ∀ x, x ≠ a → f x = g x) :
    (∑ x, (if f x = true then (1:ℕ) else 0)) + 1 = ∑ x, (if g x = true then (1:ℕ) else 0) := by
  classical
  have hrest' : (∑ x ∈ Finset.univ.erase a, (if f x = true then (1:ℕ) else 0))
      = ∑ x ∈ Finset.univ.erase a, (if g x = true then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hrest x (Finset.mem_erase.mp hx).1]
  have hf := (Finset.add_sum_erase _
    (fun x => if f x = true then (1:ℕ) else 0) (Finset.mem_univ a)).symm
  have hg := (Finset.add_sum_erase _
    (fun x => if g x = true then (1:ℕ) else 0) (Finset.mem_univ a)).symm
  rw [hf, hg, hrest']
  simp [hfa, hga, Nat.add_comm]

/-- **Unit transfer — PROVED** (was a derived-citation axiom; the 2026-07-04 re-read of Brualdi 2006
    Ch. 3 found the "specialization of Thm 3.4.1(iii)" audit record too thin, so it is now a theorem):
    in a nonempty class A(r,c), transferring one unit of column demand from `i` to `j` keeps the class
    nonempty iff some member has a `(1,0)` entry-pair in columns `(i,j)`. Backward: the elementary
    single-cell transfer. Forward: the minimal-difference-pair argument (as in `rowSupport_exchange`):
    minimize `diffCount` over `A(r,c) × A(r,c′)`; two switch-minimality forcings close the P-rows of
    the Q-columns into `S`, and counting forces `|S| = 0` against the column-`i` imbalance. -/
theorem ryser_fulkerson_unitTransfer {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    {i j : Fin n} (hij : i ≠ j) (hci : 0 < c i) (hne : Nonempty (MarginClass r c)) :
    Nonempty (MarginClass r (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k)) ↔
      ∃ (M : MarginClass r c) (a : Fin m), M.val a i = true ∧ M.val a j = false := by
  classical
  constructor
  · -- forward: minimal-pair argument
    intro hne'
    by_contra hno
    have hno' : ∀ (M : MarginClass r c) (a : Fin m), M.val a i = true → M.val a j = true := by
      intro M a h
      cases hj : M.val a j
      · exact absurd ⟨M, a, h, hj⟩ hno
      · rfl
    obtain ⟨pr, -, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset (MarginClass r c ×
        MarginClass r (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k)))
      (fun MB => diffCount MB.1.val MB.2.val)
      (by
        obtain ⟨M0⟩ := hne
        obtain ⟨B0⟩ := hne'
        exact ⟨(M0, B0), Finset.mem_univ _⟩)
    set M := pr.1 with hM_def
    set B := pr.2 with hB_def
    have hmin' : ∀ (M' : MarginClass r c)
        (B' : MarginClass r (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k)),
        diffCount M.val B.val ≤ diffCount M'.val B'.val :=
      fun M' B' => hmin (M', B') (Finset.mem_univ _)
    -- column balance: |P_k| + colSum B k = |Q_k| + colSum M k
    have hcolbal : ∀ k : Fin n,
        ((Finset.univ : Finset (Fin m)).filter
            (fun a => M.val a k = true ∧ B.val a k = false)).card + colSum B.val k
          = ((Finset.univ : Finset (Fin m)).filter
              (fun a => M.val a k = false ∧ B.val a k = true)).card + colSum M.val k := by
      intro k
      have hM := count_split_pair (Finset.univ : Finset (Fin m))
        (fun a => M.val a k) (fun a => B.val a k)
      have hB := count_split_pair (Finset.univ : Finset (Fin m))
        (fun a => B.val a k) (fun a => M.val a k)
      have hMsum : colSum M.val k = ((Finset.univ : Finset (Fin m)).filter
          (fun a => M.val a k = true)).card := by
        unfold colSum
        rw [Finset.sum_boole]
        simp
      have hBsum : colSum B.val k = ((Finset.univ : Finset (Fin m)).filter
          (fun a => B.val a k = true)).card := by
        unfold colSum
        rw [Finset.sum_boole]
        simp
      have hcomm : ((Finset.univ : Finset (Fin m)).filter
            (fun a => B.val a k = true ∧ M.val a k = true))
          = ((Finset.univ : Finset (Fin m)).filter
              (fun a => M.val a k = true ∧ B.val a k = true)) := by
        apply Finset.filter_congr
        intro a _
        constructor <;> exact fun h => ⟨h.2, h.1⟩
      have hcomm2 : ((Finset.univ : Finset (Fin m)).filter
            (fun a => B.val a k = true ∧ M.val a k = false))
          = ((Finset.univ : Finset (Fin m)).filter
              (fun a => M.val a k = false ∧ B.val a k = true)) := by
        apply Finset.filter_congr
        intro a _
        constructor <;> exact fun h => ⟨h.2, h.1⟩
      rw [hcomm, hcomm2] at hB
      rw [hMsum, hBsum, hM, hB]
      omega
    set S : Finset (Fin m) := Finset.univ.filter
      (fun a => M.val a i = true ∧ B.val a i = false) with hS_def
    have hS_mem : ∀ a, a ∈ S ↔ M.val a i = true ∧ B.val a i = false := by
      intro a
      simp [hS_def]
    have hMci : colSum M.val i = c i := M.property.2 i
    have hBci : colSum B.val i = c i - 1 := by
      simpa using B.property.2 i
    have hS_ne : S.Nonempty := by
      have h := hcolbal i
      rw [hMci, hBci] at h
      have hpos : 0 < ((Finset.univ : Finset (Fin m)).filter
          (fun a => M.val a i = true ∧ B.val a i = false)).card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      exact ⟨a, by rw [hS_def]; exact ha⟩
    set T : Finset (Fin n) := Finset.univ.filter
      (fun k => ∃ a ∈ S, M.val a k = false ∧ B.val a k = true) with hT_def
    have hT_mem : ∀ k, k ∈ T ↔ ∃ a ∈ S, M.val a k = false ∧ B.val a k = true := by
      intro k
      simp [hT_def]
    have hiT : i ∉ T := by
      rw [hT_mem]
      rintro ⟨a, haS, hMai, -⟩
      rw [((hS_mem a).mp haS).1] at hMai
      cases hMai
    have hjT : j ∉ T := by
      rw [hT_mem]
      rintro ⟨a, haS, hMaj, -⟩
      have hj := hno' M a ((hS_mem a).mp haS).1
      rw [hj] at hMaj
      cases hMaj
    have hclose : ∀ k ∈ T, ∀ b, M.val b k = true → B.val b k = false → b ∈ S := by
      intro k hkT b hMbk hBbk
      obtain ⟨a, haS, hMak, hBak⟩ := (hT_mem k).mp hkT
      obtain ⟨hMai, hBai⟩ := (hS_mem a).mp haS
      have hab : a ≠ b := by
        intro h
        rw [h, hMbk] at hMak
        cases hMak
      have hik : i ≠ k := by
        intro h
        rw [← h, hMai] at hMak
        cases hMak
      have hMbi : M.val b i = true := by
        by_contra hne2
        have hMbi0 : M.val b i = false := by
          cases h : M.val b i
          · rfl
          · exact absurd h hne2
        have hblockM : Brualdi.Ryser.SwitchBlock M.val a b i k :=
          ⟨hab, hik, hMai, hMbk, hMak, hMbi0⟩
        have hM₂ : HasMargins r c (Brualdi.Ryser.switchMat M.val a b i k) :=
          Brualdi.Ryser.interchange_preserves_margins
            (Brualdi.Ryser.switch_interchange hblockM) M.property
        have hdiffs : 3 ≤ ((blockCells a b i k).filter
            (fun y => M.val y.1 y.2 ≠ B.val y.1 y.2)).card := by
          have hsub : ({(a, i), (a, k), (b, k)} : Finset (Fin m × Fin n))
              ⊆ (blockCells a b i k).filter (fun y => M.val y.1 y.2 ≠ B.val y.1 y.2) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inl rfl),
                by rw [hMai, hBai]; decide⟩
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inl rfl)),
                by rw [hMak, hBak]; decide⟩
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inr (Or.inr rfl))),
                by rw [hMbk, hBbk]; decide⟩
          have hcard3 : ({(a, i), (a, k), (b, k)} : Finset (Fin m × Fin n)).card = 3 := by
            have h1 : ((a, i) : Fin m × Fin n) ≠ (a, k) := fun h => hik (congrArg Prod.snd h)
            have h2 : ((a, i) : Fin m × Fin n) ≠ (b, k) := fun h => hab (congrArg Prod.fst h)
            have h3 : ((a, k) : Fin m × Fin n) ≠ (b, k) := fun h => hab (congrArg Prod.fst h)
            simp [h1, h2, h3]
          calc 3 = ({(a, i), (a, k), (b, k)} : Finset (Fin m × Fin n)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hsub
        have hlt := diffCount_switch_lt hblockM hdiffs
        have hge : diffCount M.val B.val
            ≤ diffCount (Brualdi.Ryser.switchMat M.val a b i k) B.val :=
          hmin' ⟨_, hM₂⟩ B
        omega
      have hBbi : B.val b i = false := by
        by_contra hne2
        have hBbi1 : B.val b i = true := by
          cases h : B.val b i
          · exact absurd h hne2
          · rfl
        have hblockB : Brualdi.Ryser.SwitchBlock B.val b a i k :=
          ⟨Ne.symm hab, hik, hBbi1, hBak, hBbk, hBai⟩
        have hB₂ : HasMargins r
            (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k)
            (Brualdi.Ryser.switchMat B.val b a i k) :=
          Brualdi.Ryser.interchange_preserves_margins
            (Brualdi.Ryser.switch_interchange hblockB) B.property
        have hdiffs : 3 ≤ ((blockCells b a i k).filter
            (fun y => B.val y.1 y.2 ≠ M.val y.1 y.2)).card := by
          have hsub : ({(b, k), (a, i), (a, k)} : Finset (Fin m × Fin n))
              ⊆ (blockCells b a i k).filter (fun y => B.val y.1 y.2 ≠ M.val y.1 y.2) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inl rfl)),
                by rw [hBbk, hMbk]; decide⟩
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inr (Or.inl rfl))),
                by rw [hBai, hMai]; decide⟩
            · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inr (Or.inr rfl))),
                by rw [hBak, hMak]; decide⟩
          have hcard3 : ({(b, k), (a, i), (a, k)} : Finset (Fin m × Fin n)).card = 3 := by
            have h1 : ((b, k) : Fin m × Fin n) ≠ (a, i) := fun h => hab ((congrArg Prod.fst h).symm)
            have h2 : ((b, k) : Fin m × Fin n) ≠ (a, k) := fun h => hab ((congrArg Prod.fst h).symm)
            have h3 : ((a, i) : Fin m × Fin n) ≠ (a, k) := fun h => hik (congrArg Prod.snd h)
            simp [h1, h2, h3]
          calc 3 = ({(b, k), (a, i), (a, k)} : Finset (Fin m × Fin n)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hsub
        have hlt := diffCount_switch_lt hblockB hdiffs
        have hge : diffCount M.val B.val
            ≤ diffCount M.val (Brualdi.Ryser.switchMat B.val b a i k) :=
          hmin' M ⟨_, hB₂⟩
        have h1 := diffCount_comm M.val B.val
        have h2 := diffCount_comm M.val (Brualdi.Ryser.switchMat B.val b a i k)
        omega
      exact (hS_mem b).mpr ⟨hMbi, hBbi⟩
    have hswapP : (∑ a ∈ S, (T.filter
          (fun k => M.val a k = true ∧ B.val a k = false)).card)
        = ∑ k ∈ T, (S.filter (fun a => M.val a k = true ∧ B.val a k = false)).card :=
      sum_card_filter_comm S T _
    have hswapQ : (∑ a ∈ S, (T.filter
          (fun k => M.val a k = false ∧ B.val a k = true)).card)
        = ∑ k ∈ T, (S.filter (fun a => M.val a k = false ∧ B.val a k = true)).card :=
      sum_card_filter_comm S T _
    have hrow_eqQ : ∀ a ∈ S,
        (T.filter (fun k => M.val a k = false ∧ B.val a k = true)).card
          = ((Finset.univ : Finset (Fin n)).filter
              (fun k => M.val a k = false ∧ B.val a k = true)).card := by
      intro a haS
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT_mem]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨h1, h2⟩
        exact ⟨⟨a, haS, h1, h2⟩, h1, h2⟩
    have hrow_bal : ∀ a ∈ S,
        ((Finset.univ : Finset (Fin n)).filter
            (fun k => M.val a k = true ∧ B.val a k = false)).card
          = ((Finset.univ : Finset (Fin n)).filter
              (fun k => M.val a k = false ∧ B.val a k = true)).card := by
      intro a _
      exact pq_row_balance (by rw [M.property.1 a, B.property.1 a])
    have hrow_geP : ∀ a ∈ S,
        (T.filter (fun k => M.val a k = true ∧ B.val a k = false)).card + 1
          ≤ ((Finset.univ : Finset (Fin n)).filter
              (fun k => M.val a k = true ∧ B.val a k = false)).card := by
      intro a haS
      obtain ⟨hMai, hBai⟩ := (hS_mem a).mp haS
      have hi_mem : i ∈ (Finset.univ : Finset (Fin n)).filter
          (fun k => M.val a k = true ∧ B.val a k = false) := by
        simp [hMai, hBai]
      have hi_not : i ∉ T.filter (fun k => M.val a k = true ∧ B.val a k = false) :=
        fun h => hiT (Finset.mem_filter.mp h).1
      have hsub : insert i (T.filter (fun k => M.val a k = true ∧ B.val a k = false))
          ⊆ (Finset.univ : Finset (Fin n)).filter
              (fun k => M.val a k = true ∧ B.val a k = false) := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hi_mem
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      calc (T.filter (fun k => M.val a k = true ∧ B.val a k = false)).card + 1
          = (insert i (T.filter (fun k => M.val a k = true ∧ B.val a k = false))).card :=
            (Finset.card_insert_of_notMem hi_not).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hcol_ge : ∀ k ∈ T,
        (S.filter (fun a => M.val a k = false ∧ B.val a k = true)).card
          ≤ (S.filter (fun a => M.val a k = true ∧ B.val a k = false)).card := by
      intro k hkT
      have hki : k ≠ i := fun h => hiT (h ▸ hkT)
      have hkj : k ≠ j := fun h => hjT (h ▸ hkT)
      have hBck : colSum B.val k = c k := by
        simpa [hki, hkj] using B.property.2 k
      have hbal := hcolbal k
      rw [hBck, M.property.2 k] at hbal
      have hPeq : S.filter (fun a => M.val a k = true ∧ B.val a k = false)
          = (Finset.univ : Finset (Fin m)).filter
              (fun a => M.val a k = true ∧ B.val a k = false) := by
        ext x
        constructor
        · intro hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · intro hx
          obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hclose k hkT x h1 h2, h1, h2⟩
      have hQle : (S.filter (fun a => M.val a k = false ∧ B.val a k = true)).card
          ≤ ((Finset.univ : Finset (Fin m)).filter
              (fun a => M.val a k = false ∧ B.val a k = true)).card :=
        Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
      rw [hPeq]
      omega
    have hsum_geP : (∑ a ∈ S, (T.filter
          (fun k => M.val a k = true ∧ B.val a k = false)).card) + S.card
        ≤ ∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
            (fun k => M.val a k = true ∧ B.val a k = false)).card := by
      calc (∑ a ∈ S, (T.filter
              (fun k => M.val a k = true ∧ B.val a k = false)).card) + S.card
          = ∑ a ∈ S, ((T.filter
              (fun k => M.val a k = true ∧ B.val a k = false)).card + 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hrow_geP
    have hsum_balQ : (∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
          (fun k => M.val a k = true ∧ B.val a k = false)).card)
        = ∑ a ∈ S, (T.filter (fun k => M.val a k = false ∧ B.val a k = true)).card := by
      calc (∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
            (fun k => M.val a k = true ∧ B.val a k = false)).card)
          = ∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
              (fun k => M.val a k = false ∧ B.val a k = true)).card :=
            Finset.sum_congr rfl hrow_bal
        _ = _ := (Finset.sum_congr rfl hrow_eqQ).symm
    have hsum_col : (∑ k ∈ T, (S.filter
          (fun a => M.val a k = false ∧ B.val a k = true)).card)
        ≤ ∑ k ∈ T, (S.filter (fun a => M.val a k = true ∧ B.val a k = false)).card :=
      Finset.sum_le_sum hcol_ge
    have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    omega
  · -- backward: elementary single-cell transfer
    rintro ⟨M, a, hai, haj⟩
    set N : ZeroOneMat m n := fun x y =>
      if x = a ∧ y = i then false else if x = a ∧ y = j then true else M.val x y with hN
    have hNai : N a i = false := by simp [hN]
    have hNaj : N a j = true := by simp [hN, Ne.symm hij]
    have hNrow : ∀ x, x ≠ a → ∀ y, N x y = M.val x y := by
      intro x hx y
      simp [hN, hx]
    have hNcol : ∀ y, y ≠ i → y ≠ j → ∀ x, N x y = M.val x y := by
      intro y hyi hyj x
      simp [hN, hyi, hyj]
    refine ⟨⟨N, ?_, ?_⟩⟩
    · intro x
      by_cases hx : x = a
      · subst hx
        have htr := sum_boolfun_transfer (f := fun y => N x y) (g := fun y => M.val x y)
          hij hNai hai hNaj haj
          (fun y h1 h2 => by simp [hN, h1, h2])
        have hMx := M.property.1 x
        unfold rowSum at hMx ⊢
        rw [htr]
        exact hMx
      · have hMx := M.property.1 x
        unfold rowSum at hMx ⊢
        calc (∑ y, if N x y = true then (1:ℕ) else 0)
            = ∑ y, (if M.val x y = true then (1:ℕ) else 0) := by
              apply Finset.sum_congr rfl
              intro y _
              rw [hNrow x hx y]
          _ = r x := hMx
    · intro k
      by_cases hki : k = i
      · subst hki
        have hflip := sum_boolfun_flipdown (f := fun x => N x k) (g := fun x => M.val x k)
          (a := a) hNai hai (fun x hx => hNrow x hx k)
        have hMk := M.property.2 k
        have hrhs : (if k = k then c k - 1 else if k = j then c k + 1 else c k) = c k - 1 := by
          simp
        unfold colSum at hMk ⊢
        show (∑ x, if N x k = true then (1:ℕ) else 0)
            = if k = k then c k - 1 else if k = j then c k + 1 else c k
        rw [hrhs]
        omega
      · by_cases hkj : k = j
        · subst hkj
          have hflip := sum_boolfun_flipdown (f := fun x => M.val x k) (g := fun x => N x k)
            (a := a) haj hNaj (fun x hx => (hNrow x hx k).symm)
          have hMk := M.property.2 k
          have hrhs : (if k = i then c k - 1 else if k = k then c k + 1 else c k) = c k + 1 := by
            simp [hki]
          unfold colSum at hMk ⊢
          show (∑ x, if N x k = true then (1:ℕ) else 0)
              = if k = i then c k - 1 else if k = k then c k + 1 else c k
          rw [hrhs]
          omega
        · have hMk := M.property.2 k
          have hrhs : (if k = i then c k - 1 else if k = j then c k + 1 else c k) = c k := by
            simp [hki, hkj]
          unfold colSum at hMk ⊢
          show (∑ x, if N x k = true then (1:ℕ) else 0)
              = if k = i then c k - 1 else if k = j then c k + 1 else c k
          rw [hrhs]
          calc (∑ x, if N x k = true then (1:ℕ) else 0)
              = ∑ x, (if M.val x k = true then (1:ℕ) else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                rw [hNcol k hki hkj x]
            _ = c k := hMk

/-- The column support of row `L`. -/
def rowSupport {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ} (L : Fin m)
    (M : MarginClass r s) : Finset (Fin n) :=
  Finset.univ.filter (fun b => M.val L b = true)

private def patOfSet {n : ℕ} (X : Finset (Fin n)) : Fin n → Bool :=
  fun b => decide (b ∈ X)

private theorem sum_patOfSet_eq_card {n : ℕ} (X : Finset (Fin n)) :
    (∑ b : Fin n, (if patOfSet X b then 1 else 0 : ℕ)) = X.card := by
  classical
  rw [← Finset.card_filter]
  congr 1
  ext b
  simp [patOfSet]

private theorem rowSupport_insert_erase_mem {n : ℕ} {X : Finset (Fin n)} {a b k : Fin n}
    (hab : a ≠ b) (ha : a ∉ X) :
    k ∈ insert a (X.erase b) ↔
      if k = a then True else if k = b then False else k ∈ X := by
  classical
  by_cases hka : k = a
  · subst k
    simp [ha]
  · by_cases hkb : k = b
    · subst k
      simp [hab.symm]
    · simp [hka, hkb]

private theorem residual_eq_insert_erase {n : ℕ} (s : Fin n → ℕ)
    {X : Finset (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (hb : b ∈ X) (ha : a ∉ X) (hsb : 1 ≤ s b) :
    (fun k : Fin n =>
        if k = a then s k - (if patOfSet X k then 1 else 0) - 1
        else if k = b then s k - (if patOfSet X k then 1 else 0) + 1
        else s k - (if patOfSet X k then 1 else 0)) =
      (fun k : Fin n => s k - (if patOfSet (insert a (X.erase b)) k then 1 else 0)) := by
  classical
  funext k
  by_cases hka : k = a
  · subst k
    simp [patOfSet, ha]
  · by_cases hkb : k = b
    · subst k
      simp [patOfSet, hb, hab.symm, Nat.sub_add_cancel hsb]
    · have hk :
        k ∈ insert a (X.erase b) ↔ k ∈ X := by
          simpa [hka, hkb] using
            (rowSupport_insert_erase_mem (X := X) (a := a) (b := b) (k := k) hab ha)
      by_cases hkX : k ∈ X <;> simp [patOfSet, hka, hkb, hk, hkX]

private theorem rowPat_eq_patOfSet_of_rowSupport {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {L : Fin m} {M : MarginClass r s} {X : Finset (Fin n)} (hX : rowSupport L M = X) :
    rowPat L M = patOfSet X := by
  classical
  funext b
  have hb := congrArg (fun S : Finset (Fin n) => b ∈ S) hX
  simp [rowSupport, rowPat, patOfSet] at hb ⊢
  by_cases hMb : M.val L b = true
  · simp [hMb, hb.mp hMb]
  · have hbX : b ∉ X := by
      intro hbX
      exact hMb (hb.mpr hbX)
    simp [hMb, hbX]

private theorem rowSupport_eq_of_rowPat_patOfSet {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {L : Fin m} {M : MarginClass r s} {X : Finset (Fin n)}
    (hX : rowPat L M = patOfSet X) :
    rowSupport L M = X := by
  classical
  ext b
  have hb := congrFun hX b
  simp [rowSupport, rowPat, patOfSet] at hb ⊢
  by_cases hbX : b ∈ X
  · simp [hbX] at hb
    exact ⟨fun _ => hbX, fun _ => hb⟩
  · simp [hbX] at hb
    exact ⟨fun h => by
      rw [hb] at h
      exact (Bool.false_ne_true h).elim, fun h => False.elim (hbX h)⟩

private theorem fibre_nonempty_of_support_nonempty {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {L : Fin m} {X : Finset (Fin n)}
    (hX : Nonempty {M : MarginClass r s // rowSupport L M = X}) :
    Nonempty {M : MarginClass r s // rowPat L M = patOfSet X} := by
  rcases hX with ⟨M⟩
  exact ⟨⟨M.val, rowPat_eq_patOfSet_of_rowSupport M.property⟩⟩

/-! ### The paper's Gale-Ryser route (Lemma 5.3 as printed; feasibility layer, moved
    before `rowPattern_shifted` 2026-07-05 so shiftedness can be proved as printed) -/

/-- The support of a row of a class member has that row's margin as cardinality. -/
private theorem alt_support_card {m n : ℕ} {r : Fin (m+1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m+1)} (M : MarginClass r s) : (rowSupport L M).card = r L := by
  classical
  have hcard : (rowSupport L M).card = rowSum M.val L := by
    rw [rowSupport, Finset.card_filter, rowSum]
  rw [hcard, M.property.1 L]

/-- Row sums of a 0/1 matrix are at most the number of columns. -/
private theorem alt_rowSum_le {m n : ℕ} (M : ZeroOneMat m n) (i : Fin m) :
    rowSum M i ≤ n := by
  calc rowSum M i ≤ ∑ _j : Fin n, 1 :=
        Finset.sum_le_sum (fun j _ => by by_cases h : M i j <;> simp [h])
    _ = n := by simp

/-- The paper's row-supply function `h(q) = ∑_t min(r'_t, q)` (residual row sums). -/
private def altH {m n : ℕ} (r : Fin (m + 1) → ℕ) (L : Fin (m + 1)) (q : ℕ) : ℕ :=
  ∑ t : Fin m, min (r (L.succAbove t)) q

private theorem altH_le {m n : ℕ} (r : Fin (m + 1) → ℕ) (L : Fin (m + 1)) (q : ℕ) :
    altH (m := m) (n := n) r L q ≤ ∑ t : Fin m, r (L.succAbove t) :=
  Finset.sum_le_sum (fun t _ => min_le_left _ _)

/-- `h` as a sum of decreasing increments: `h(q) = ∑_{t<q} #{i : t < r'_i}`. -/
private theorem altH_eq_range {m n : ℕ} (r : Fin (m + 1) → ℕ) (L : Fin (m + 1)) (q : ℕ) :
    altH (m := m) (n := n) r L q =
      ∑ t ∈ Finset.range q, ∑ i : Fin m, (if t < r (L.succAbove i) then 1 else 0 : ℕ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.card_filter]
  have : (Finset.range q).filter (fun t => t < r (L.succAbove i)) =
      Finset.range (min (r (L.succAbove i)) q) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [this, Finset.card_range]

/-- Supermodularity input: `h(c) + h(d) ≤ h(a) + h(b)` whenever `c ≤ a ≤ d`, `a + b = c + d`. -/
private theorem altH_supermod {m n : ℕ} (r : Fin (m + 1) → ℕ) (L : Fin (m + 1))
    {a b c d : ℕ} (hca : c ≤ a) (had : a ≤ d) (habcd : a + b = c + d) :
    altH (m := m) (n := n) r L c + altH (m := m) (n := n) r L d ≤
      altH (m := m) (n := n) r L a + altH (m := m) (n := n) r L b := by
  have hcb : c ≤ b := by omega
  have hbd : b ≤ d := by omega
  set cnt : ℕ → ℕ := fun t => ∑ i : Fin m, (if t < r (L.succAbove i) then 1 else 0 : ℕ)
    with hcnt
  have hsplit : ∀ {u v : ℕ}, u ≤ v →
      (∑ t ∈ Finset.range v, cnt t) =
        (∑ t ∈ Finset.range u, cnt t) + ∑ t ∈ Finset.Ico u v, cnt t := by
    intro u v huv
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive cnt (Nat.zero_le u) huv).symm
  have hIco : ∑ t ∈ Finset.Ico b d, cnt t ≤ ∑ t ∈ Finset.Ico c a, cnt t := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hlen : d - b = a - c := by omega
    rw [hlen]
    refine Finset.sum_le_sum ?_
    intro i _
    have hle : c + i ≤ b + i := by omega
    exact Finset.sum_le_sum (fun t _ => by
      by_cases h1 : b + i < r (L.succAbove t)
      · have h2 : c + i < r (L.succAbove t) := by omega
        simp [h1, h2]
      · by_cases h2 : c + i < r (L.succAbove t) <;> simp [h1, h2])
  have hval : ∀ q : ℕ, altH (m := m) (n := n) r L q = ∑ t ∈ Finset.range q, cnt t := by
    intro q
    rw [altH_eq_range]
  have h1 := hsplit hca
  have h2 := hsplit hbd
  rw [hval a, hval b, hval c, hval d]
  omega

/-- The paper's Gale–Ryser inequality system for a pattern `p` of line `L`
    (subtraction-free form of `ℓ(X) ≤ |p ∩ X|`). -/
private def altFeas {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ) (L : Fin (m + 1))
    (p : Finset (Fin n)) : Prop :=
  p.card = r L ∧
    ∀ X : Finset (Fin n), ∑ j ∈ X, s j ≤ (p ∩ X).card + altH (m := m) (n := n) r L X.card

/-- Realizable patterns satisfy the inequalities (the counting direction of Gale–Ryser). -/
private theorem altFeas_of_realizable {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {p : Finset (Fin n)}
    (h : Nonempty {M : MarginClass r s // rowSupport L M = p}) :
    altFeas r s L p := by
  classical
  obtain ⟨⟨M, hM⟩⟩ := h
  constructor
  · rw [← hM]
    exact alt_support_card M
  · intro X
    have hmass : ∑ j ∈ X, s j =
        ∑ i : Fin (m + 1), ∑ j ∈ X, (if M.val i j then 1 else 0 : ℕ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← M.property.2 j]
      rfl
    have hsplitL := Fin.sum_univ_succAbove
      (fun i : Fin (m + 1) => ∑ j ∈ X, (if M.val i j then 1 else 0 : ℕ)) L
    have hLterm : ∑ j ∈ X, (if M.val L j then 1 else 0 : ℕ) = (p ∩ X).card := by
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_inter, ← hM, rowSupport,
        Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hres : ∀ t : Fin m,
        ∑ j ∈ X, (if M.val (L.succAbove t) j then 1 else 0 : ℕ) ≤
          min (r (L.succAbove t)) X.card := by
      intro t
      refine le_min ?_ ?_
      · calc ∑ j ∈ X, (if M.val (L.succAbove t) j then 1 else 0 : ℕ)
            ≤ ∑ j : Fin n, (if M.val (L.succAbove t) j then 1 else 0 : ℕ) :=
              Finset.sum_le_sum_of_subset (Finset.subset_univ X)
          _ = r (L.succAbove t) := M.property.1 (L.succAbove t)
      · calc ∑ j ∈ X, (if M.val (L.succAbove t) j then 1 else 0 : ℕ)
            ≤ ∑ _j ∈ X, 1 := Finset.sum_le_sum (fun j _ => by
              by_cases h : M.val (L.succAbove t) j <;> simp [h])
          _ = X.card := by simp
    have hressum : ∑ t : Fin m, ∑ j ∈ X, (if M.val (L.succAbove t) j then 1 else 0 : ℕ) ≤
        altH (m := m) (n := n) r L X.card :=
      Finset.sum_le_sum (fun t _ => hres t)
    unfold altH at hressum ⊢
    omega

/-- The inequalities imply realizability (Gale–Ryser, hard direction, via
    `galeRyser_exists` on the residual class). -/
private theorem alt_realizable_of_feas {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} (hne : Nonempty (MarginClass r s)) {p : Finset (Fin n)}
    (hfeas : altFeas r s L p) :
    Nonempty {M : MarginClass r s // rowSupport L M = p} := by
  classical
  obtain ⟨M₀⟩ := hne
  -- ambient totals from the witness
  have htot : ∑ j, s j = r L + ∑ t : Fin m, r (L.succAbove t) := by
    have h1 : ∑ j, s j = ∑ j, colSum M₀.val j :=
      Finset.sum_congr rfl (fun j _ => (M₀.property.2 j).symm)
    have h2 : ∑ j : Fin n, colSum M₀.val j = ∑ i : Fin (m + 1), rowSum M₀.val i := by
      unfold colSum rowSum
      exact Finset.sum_comm
    have h3 : ∑ i : Fin (m + 1), rowSum M₀.val i = ∑ i : Fin (m + 1), r i :=
      Finset.sum_congr rfl (fun i _ => M₀.property.1 i)
    have h4 := Fin.sum_univ_succAbove (fun i : Fin (m + 1) => r i) L
    omega
  -- every column used by the pattern is nonempty
  have hp1 : ∀ j ∈ p, 1 ≤ s j := by
    intro j hj
    have hX := hfeas.2 (Finset.univ.erase j)
    have hsum_er : ∑ b ∈ Finset.univ.erase j, s b + s j = ∑ b, s b :=
      Finset.sum_erase_add _ _ (Finset.mem_univ j)
    have hpinter : p ∩ Finset.univ.erase j = p.erase j := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    have hpcard : (p.erase j).card + 1 = p.card := Finset.card_erase_add_one hj
    have hHle := altH_le (m := m) (n := n) r L (Finset.univ.erase j).card
    rw [hpinter] at hX
    have hk := hfeas.1
    omega
  -- the residual column margins
  set pb : Fin n → Bool := fun j => decide (j ∈ p) with hpbdef
  have hpb_ite : ∀ j, (if pb j then 1 else 0 : ℕ) = (if j ∈ p then 1 else 0 : ℕ) := by
    intro j
    by_cases h : j ∈ p <;> simp [pb, h]
  set s' : Fin n → ℕ := fun j => s j - (if pb j then 1 else 0) with hs'def
  have hpt : ∀ j, (if pb j then 1 else 0 : ℕ) ≤ s j := by
    intro j
    rw [hpb_ite]
    by_cases h : j ∈ p
    · simpa [h] using hp1 j h
    · simp [h]
  have hite_card : ∀ X : Finset (Fin n),
      ∑ j ∈ X, (if j ∈ p then 1 else 0 : ℕ) = (p ∩ X).card := by
    intro X
    rw [← Finset.card_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  have hs'_split : ∀ X : Finset (Fin n),
      ∑ j ∈ X, s' j + (p ∩ X).card = ∑ j ∈ X, s j := by
    intro X
    rw [← hite_card X, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h1 := hpt j
    have h2 := hpb_ite j
    show s j - (if pb j then 1 else 0) + (if j ∈ p then 1 else 0) = s j
    omega
  -- Gale–Ryser hypotheses on the residual class
  have hpuniv : p ∩ Finset.univ = p := by simp
  have hsum' : ∑ t : Fin m, r (L.succAbove t) = ∑ j, s' j := by
    have h := hs'_split Finset.univ
    rw [hpuniv] at h
    have hk := hfeas.1
    omega
  have hdom' : ∀ X : Finset (Fin n),
      ∑ j ∈ X, s' j ≤ ∑ t : Fin m, min (r (L.succAbove t)) X.card := by
    intro X
    have h1 := hs'_split X
    have h2 := hfeas.2 X
    unfold altH at h2
    omega
  obtain ⟨W⟩ := galeRyser_exists (fun t : Fin m => r (L.succAbove t)) s' hsum' hdom'
  -- assemble the full matrix
  have hrow : (∑ b : Fin n, (if pb b then 1 else 0 : ℕ)) = r L := by
    rw [Finset.sum_congr rfl (fun b _ => hpb_ite b), hite_card Finset.univ, hpuniv]
    exact hfeas.1
  refine ⟨⟨⟨insertRow L pb W.val, insertRow_hasMargins (i := L) hrow hpt W⟩, ?_⟩⟩
  rw [rowSupport]
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, insertRow,
    Fin.insertNth_apply_same]
  simp [pb]


/-- **Shiftedness, as printed (Lemma 5.12's input)** — the paper's Gale–Ryser argument:
    moving a pattern element `b` to a column `a` with `s a ≥ s b` preserves every
    Gale–Ryser inequality, because a test set `X` with `a ∉ X ∋ b` can be exchanged to
    `X' = X - b + a` of the same size and no smaller column mass, where the old pattern
    meets the inequality with the same intersection count. The development's original
    unit-transfer proof is kept as `rowPattern_shifted_transfer`. -/
theorem rowPattern_shifted {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    (B : BaseFamily (Fin n)) (hB : ∀ p, B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {a b : Fin n} (hsab : s b ≤ s a) {X : Finset (Fin n)} (hb : b ∈ X) (ha : a ∉ X)
    (hX : B.Base X) :
    B.Base (insert a (X.erase b)) := by
  classical
  have hab : a ≠ b := by
    intro h
    exact ha (by simpa [h] using hb)
  rcases (hB X).mp hX with ⟨M₀⟩
  have hne : Nonempty (MarginClass r s) := ⟨M₀.val⟩
  have hfeas : altFeas r s L X := altFeas_of_realizable ⟨M₀⟩
  set X' : Finset (Fin n) := insert a (X.erase b) with hX'def
  have haX'e : a ∉ X.erase b := fun h => ha (Finset.mem_of_mem_erase h)
  have hcard' : X'.card = X.card := by
    rw [hX'def, Finset.card_insert_of_notMem haX'e, Finset.card_erase_of_mem hb]
    have : 1 ≤ X.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hfeas' : altFeas r s L X' := by
    constructor
    · rw [hcard']
      exact hfeas.1
    · intro T
      by_cases hbT : b ∈ T
      · by_cases haT : a ∈ T
        · -- both a, b ∈ T: the intersection count does not drop
          have hXT : (X ∩ T).card ≤ (X' ∩ T).card := by
            have hsplit : X' ∩ T = insert a ((X ∩ T).erase b) := by
              ext c
              simp only [hX'def, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro ⟨hc | ⟨hcb, hcX⟩, hcT⟩
                · exact Or.inl hc
                · exact Or.inr ⟨hcb, hcX, hcT⟩
              · rintro (rfl | ⟨hcb, hcX, hcT⟩)
                · exact ⟨Or.inl rfl, haT⟩
                · exact ⟨Or.inr ⟨hcb, hcX⟩, hcT⟩
            have hanotin : a ∉ (X ∩ T).erase b :=
              fun h => ha (Finset.mem_inter.mp (Finset.mem_of_mem_erase h)).1
            rw [hsplit, Finset.card_insert_of_notMem hanotin]
            by_cases hbXT : b ∈ X ∩ T
            · rw [Finset.card_erase_of_mem hbXT]
              have : 1 ≤ (X ∩ T).card := Finset.card_pos.mpr ⟨b, hbXT⟩
              omega
            · rw [Finset.erase_eq_of_notMem hbXT]
              omega
          calc ∑ j ∈ T, s j ≤ (X ∩ T).card + altH (m := m) (n := n) r L T.card := hfeas.2 T
            _ ≤ (X' ∩ T).card + altH (m := m) (n := n) r L T.card := by omega
        · -- b ∈ T, a ∉ T: exchange the test set
          set T' : Finset (Fin n) := insert a (T.erase b) with hT'def
          have haTe : a ∉ T.erase b := fun h => haT (Finset.mem_of_mem_erase h)
          have hTcard : T'.card = T.card := by
            rw [hT'def, Finset.card_insert_of_notMem haTe, Finset.card_erase_of_mem hbT]
            have : 1 ≤ T.card := Finset.card_pos.mpr ⟨b, hbT⟩
            omega
          have hsum : ∑ j ∈ T, s j + s a = ∑ j ∈ T', s j + s b := by
            have h1 : s b + ∑ j ∈ T.erase b, s j = ∑ j ∈ T, s j :=
              Finset.add_sum_erase T s hbT
            have h2 : ∑ j ∈ T', s j = s a + ∑ j ∈ T.erase b, s j := by
              rw [hT'def, Finset.sum_insert haTe]
            omega
          have hint : X ∩ T' = X' ∩ T := by
            ext c
            simp only [hX'def, hT'def, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hcX, rfl | ⟨hcb, hcT⟩⟩
              · exact absurd hcX ha
              · exact ⟨Or.inr ⟨hcb, hcX⟩, hcT⟩
            · rintro ⟨rfl | ⟨hcb, hcX⟩, hcT⟩
              · exact absurd hcT haT
              · exact ⟨hcX, Or.inr ⟨hcb, hcT⟩⟩
          have hfT' := hfeas.2 T'
          rw [hint, hTcard] at hfT'
          omega
      · -- b ∉ T: the old intersection is contained in the new one
        have hXT : (X ∩ T).card ≤ (X' ∩ T).card := by
          apply Finset.card_le_card
          intro c hc
          obtain ⟨hcX, hcT⟩ := Finset.mem_inter.mp hc
          have hcb : c ≠ b := fun h => hbT (h ▸ hcT)
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcb, hcX⟩), hcT⟩
        calc ∑ j ∈ T, s j ≤ (X ∩ T).card + altH (m := m) (n := n) r L T.card := hfeas.2 T
          _ ≤ (X' ∩ T).card + altH (m := m) (n := n) r L T.card := by omega
  exact (hB X').mpr (alt_realizable_of_feas hne hfeas')

/-- **ALTERNATE proof of shiftedness** (the development's original route: a residual
    unit transfer via `ryser_fulkerson_unitTransfer`, then reinsert the pivot row). The
    mainline is `rowPattern_shifted` above — the paper's Gale–Ryser inequality argument. -/
theorem rowPattern_shifted_transfer {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    (B : BaseFamily (Fin n)) (hB : ∀ p, B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {a b : Fin n} (hsab : s b ≤ s a) {X : Finset (Fin n)} (hb : b ∈ X) (ha : a ∉ X)
    (hX : B.Base X) :
    B.Base (insert a (X.erase b)) := by
  classical
  have hab : a ≠ b := by
    intro h
    exact ha (by simpa [h] using hb)
  rcases (hB X).mp hX with ⟨M₀⟩
  let M : MarginClass r s := M₀.val
  have hMX : rowSupport L M = X := M₀.property
  have hPat : rowPat L M = patOfSet X := rowPat_eq_patOfSet_of_rowSupport hMX
  let r' : Fin m → ℕ := fun t => r (L.succAbove t)
  let c : Fin n → ℕ := fun k => s k - (if patOfSet X k then 1 else 0)
  let W₀ : MarginClass r' c :=
    ⟨dropRow L M.val, by
      simpa [r', c] using dropRow_hasMargins_pattern (i := L) M hPat⟩
  have hneRes : Nonempty (MarginClass r' c) := ⟨W₀⟩
  have hsb_pos : 1 ≤ s b := by
    have hle := rowPat_col_le M hPat b
    simpa [patOfSet, hb] using hle
  have hsa_pos : 1 ≤ s a := le_trans hsb_pos hsab
  have hca_pos : 0 < c a := by
    have : c a = s a := by simp [c, patOfSet, ha]
    rw [this]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one hsa_pos
  have hcb_lt_ca : c b < c a := by
    have hcb : c b = s b - 1 := by simp [c, patOfSet, hb]
    have hca : c a = s a := by simp [c, patOfSet, ha]
    rw [hcb, hca]
    omega
  have hexRow : ∃ (W : MarginClass r' c) (t : Fin m), W.val t a = true ∧ W.val t b = false := by
    by_contra hno
    have hpoint :
        ∀ t : Fin m,
          (if W₀.val t a then 1 else 0 : ℕ) ≤ (if W₀.val t b then 1 else 0 : ℕ) := by
      intro t
      by_cases hta : W₀.val t a = true <;> by_cases htb : W₀.val t b = true
      · simp [hta, htb]
      · exfalso
        exact hno ⟨W₀, t, hta, by simpa using htb⟩
      · simp [hta, htb]
      · simp [hta, htb]
    have hsum :
        (∑ t : Fin m, (if W₀.val t a then 1 else 0 : ℕ)) ≤
          ∑ t : Fin m, (if W₀.val t b then 1 else 0 : ℕ) :=
      Finset.sum_le_sum (by intro t _; exact hpoint t)
    have hca : colSum W₀.val a = c a := W₀.property.2 a
    have hcb : colSum W₀.val b = c b := W₀.property.2 b
    have hle : c a ≤ c b := by
      have hsum' : colSum W₀.val a ≤ colSum W₀.val b := by
        simpa [colSum] using hsum
      rwa [hca, hcb] at hsum'
    omega
  obtain ⟨W₁⟩ :=
    (ryser_fulkerson_unitTransfer r' c hab hca_pos hneRes).mpr hexRow
  let X' : Finset (Fin n) := insert a (X.erase b)
  let p' : Fin n → Bool := patOfSet X'
  have hres :
      (fun k : Fin n => if k = a then c k - 1 else if k = b then c k + 1 else c k) =
        (fun k : Fin n => s k - (if p' k then 1 else 0)) := by
    simpa [c, p', X'] using
      residual_eq_insert_erase s (X := X) (a := a) (b := b) hab hb ha hsb_pos
  let W' : MarginClass r' (fun k : Fin n => s k - (if p' k then 1 else 0)) :=
    ⟨W₁.val, by simpa [hres] using W₁.property⟩
  have hrow' : (∑ k : Fin n, (if p' k then 1 else 0 : ℕ)) = r L := by
    have hcardX' : X'.card = X.card := by
      have haerase : a ∉ X.erase b := by simp [ha]
      have herase : (X.erase b).card = X.card - 1 := Finset.card_erase_of_mem hb
      have hXcard_pos : 1 ≤ X.card := Finset.card_pos.mpr ⟨b, hb⟩
      have hcard : (insert a (X.erase b)).card = X.card := by
        rw [Finset.card_insert_of_notMem haerase, herase, Nat.sub_add_cancel hXcard_pos]
      simpa [X'] using hcard
    calc
      (∑ k : Fin n, (if p' k then 1 else 0 : ℕ)) = X'.card := sum_patOfSet_eq_card X'
      _ = X.card := hcardX'
      _ = (∑ k : Fin n, (if patOfSet X k then 1 else 0 : ℕ)) := (sum_patOfSet_eq_card X).symm
      _ = r L := rowPat_count_eq M hPat
  have hcol' : ∀ k : Fin n, (if p' k then 1 else 0 : ℕ) ≤ s k := by
    intro k
    by_cases hk : k = a
    · subst k
      simp [p', X', patOfSet, hsa_pos]
    · by_cases hkb : k = b
      · subst k
        simpa [p', X', patOfSet, hb, hab.symm] using hsb_pos
      · by_cases hkX : k ∈ X
        · have hle := rowPat_col_le M hPat k
          have hkX' : k ∈ X' := by simp [X', hk, hkb, hkX]
          have hle1 : 1 ≤ s k := by simpa [patOfSet, hkX] using hle
          simpa [p', patOfSet, hkX'] using hle1
        · have hkX' : k ∉ X' := by
            intro hkX'
            simp [X', Finset.mem_insert, Finset.mem_erase] at hkX'
            rcases hkX' with hk_eq_a | ⟨_hk_ne_b, hk_mem⟩
            · exact hk hk_eq_a
            · exact hkX hk_mem
          simp [p', patOfSet, hkX']
  let M' : MarginClass r s :=
    ⟨insertRow L p' W'.val, insertRow_hasMargins (i := L) hrow' hcol' W'⟩
  have hsupport : rowSupport L M' = X' := by
    apply rowSupport_eq_of_rowPat_patOfSet
    funext k
    simp [rowPat, M', insertRow, p']
  exact (hB X').mpr ⟨M', hsupport⟩

theorem fibre_crossing_of_exchange {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    (p q : Fin n → Bool) {i j : Fin n} (hij : i ≠ j)
    (hp : p i = true) (hpj : p j = false)
    (hq : ∀ b, q b = if b = i then false else if b = j then true else p b)
    (hFp : Nonempty {M : MarginClass r s // rowPat L M = p})
    (hFq : Nonempty {M : MarginClass r s // rowPat L M = q}) :
    ∃ (Mp : MarginClass r s) (Mq : MarginClass r s),
      rowPat L Mp = p ∧ rowPat L Mq = q ∧ (flipGraph r s).Adj Mp Mq := by
  classical
  rcases hFp with ⟨Wp⟩
  rcases hFq with ⟨Wq⟩
  let r' : Fin m → ℕ := fun a => r (L.succAbove a)
  let c : Fin n → ℕ := fun b => s b - (if q b then 1 else 0)
  have hrowq : (∑ b : Fin n, (if q b then 1 else 0 : ℕ)) = r L :=
    rowPat_count_eq Wq.val Wq.property
  have hcolq : ∀ b : Fin n, (if q b then 1 else 0 : ℕ) ≤ s b :=
    rowPat_col_le Wq.val Wq.property
  have hneRes : Nonempty (MarginClass r' c) := by
    exact ⟨⟨dropRow L Wq.val.val, by
      simpa [r', c] using dropRow_hasMargins_pattern (i := L) Wq.val Wq.property⟩⟩
  have hci : 0 < c i := by
    have hle : 1 ≤ s i := by
      simpa [hp] using rowPat_col_le Wp.val Wp.property i
    have hqi : q i = false := by
      simp [hq]
    simp [c, hqi, Nat.lt_of_lt_of_le Nat.zero_lt_one hle]
  have htransfer :
      Nonempty (MarginClass r'
        (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k)) := by
    have hcols :
        (fun b : Fin n => s b - (if p b then 1 else 0)) =
          (fun k => if k = i then c k - 1 else if k = j then c k + 1 else c k) := by
      funext k
      by_cases hki : k = i
      · subst k
        have hqi : q i = false := by
          simp [hq]
        simp [c, hqi, hp]
      · by_cases hkj : k = j
        · subst k
          have hqj : q j = true := by
            simp [hq, hij.symm]
          have hsj : 1 ≤ s j := by
            simpa [hqj] using hcolq j
          simpa [c, hqj, hpj, hij.symm] using (Nat.sub_add_cancel hsj).symm
        · have hqk : q k = p k := by
            simp [hq, hki, hkj]
          simp [c, hki, hkj, hqk]
    exact ⟨⟨dropRow L Wp.val.val, by
      simpa [r', hcols] using dropRow_hasMargins_pattern (i := L) Wp.val Wp.property⟩⟩
  obtain ⟨W, a, hai, haj⟩ :=
    (ryser_fulkerson_unitTransfer r' c hij hci hneRes).mp htransfer
  let Mq : MarginClass r s :=
    ⟨insertRow L q W.val, insertRow_hasMargins (i := L) hrowq hcolq W⟩
  have hMqrow : rowPat L Mq = q := by
    funext b
    simp [rowPat, Mq, insertRow]
  have hb : Brualdi.Ryser.SwitchBlock Mq.val (L.succAbove a) L i j := by
    refine ⟨Fin.succAbove_ne L a, hij, ?_, ?_, ?_, ?_⟩
    · change insertRow L q W.val (L.succAbove a) i = true
      simpa [insertRow] using hai
    · change insertRow L q W.val L j = true
      have hqj : q j = true := by
        simp [hq, hij.symm]
      simpa [insertRow, hqj]
    · change insertRow L q W.val (L.succAbove a) j = false
      simpa [insertRow] using haj
    · change insertRow L q W.val L i = false
      have hqi : q i = false := by
        simp [hq]
      simpa [insertRow, hqi]
  let Mp : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat Mq.val (L.succAbove a) L i j,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb) Mq.property⟩
  refine ⟨Mp, Mq, ?_, hMqrow, ?_⟩
  · funext b
    by_cases hbi : b = i
    · subst b
      simp [rowPat, Mp, Brualdi.Ryser.switchMat, Fin.ne_succAbove, hp, hij]
    · by_cases hbj : b = j
      · subst b
        simp [rowPat, Mp, Brualdi.Ryser.switchMat, Fin.ne_succAbove, hpj, hij]
      · have hqb : q b = p b := by
          simp [hq, hbi, hbj]
        have hMqLb : Mq.val L b = p b := by
          change rowPat L Mq b = p b
          rw [congrFun hMqrow b, hqb]
        simp [rowPat, Mp, Brualdi.Ryser.switchMat, Fin.ne_succAbove, hbi, hbj, hMqLb]
  · have hint : Interchange Mq.val Mp.val := by
      simpa [Mp] using Brualdi.Ryser.switch_interchange hb
    have hneMpMq : Mp ≠ Mq := by
      intro heq
      have hval : Mp.val = Mq.val := congrArg Subtype.val heq
      exact Brualdi.Ryser.switchMat_ne hb (by simpa [Mp] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hneMpMq, Or.inr hint⟩

private theorem rowSupport_eq_of_interchange_row_ne {m n : ℕ} {M N : ZeroOneMat m n}
    {L i i' : Fin m} {j j' : Fin n}
    (hLi : L ≠ i) (hLi' : L ≠ i')
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → N a b = M a b) :
    (fun b => M L b) = fun b => N L b := by
  funext b
  exact (hout L b (by
    intro hblock
    exact hLi' (hblock.1.resolve_left hLi))).symm

private theorem rowSupport_sdiff_left_eq_singleton {m n : ℕ} {M N : ZeroOneMat m n}
    {L i i' : Fin m} {j j' : Fin n} (hL : L = i)
    (hMij : M i j = true) (hMij' : M i j' = false)
    (hNij : N i j = false)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → N a b = M a b) :
    ((Finset.univ.filter (fun b => M L b = true)) \
      (Finset.univ.filter (fun b => N L b = true))) = {j} := by
  classical
  ext b
  constructor
  · intro hb
    have hbM : M L b = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
    have hbN : N L b ≠ true := by
      intro h
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [Finset.mem_singleton]
    by_cases hbj : b = j
    · exact hbj
    · by_cases hbj' : b = j'
      · subst L
        subst b
        rw [hMij'] at hbM
        exact (Bool.false_ne_true hbM).elim
      · subst L
        have hsame : N i b = M i b := hout i b (by
          intro hblock
          exact hbj' (hblock.2.resolve_left hbj))
        exact False.elim (hbN (by rw [hsame, hbM]))
  · intro hb
    rw [Finset.mem_singleton] at hb
    subst b
    subst L
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMij⟩, by
        intro h
        have htrue : N i j = true := (Finset.mem_filter.mp h).2
        rw [hNij] at htrue
        exact Bool.false_ne_true htrue⟩

private theorem rowSupport_sdiff_right_eq_singleton {m n : ℕ} {M N : ZeroOneMat m n}
    {L i i' : Fin m} {j j' : Fin n} (hL : L = i)
    (hMij' : M i j' = false) (hNij' : N i j' = true)
    (hNij : N i j = false)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → N a b = M a b) :
    ((Finset.univ.filter (fun b => N L b = true)) \
      (Finset.univ.filter (fun b => M L b = true))) = {j'} := by
  classical
  ext b
  constructor
  · intro hb
    have hbN : N L b = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
    have hbM : M L b ≠ true := by
      intro h
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [Finset.mem_singleton]
    by_cases hbj : b = j
    · subst L
      subst b
      rw [hNij] at hbN
      exact (Bool.false_ne_true hbN).elim
    · by_cases hbj' : b = j'
      · exact hbj'
      · subst L
        have hsame : N i b = M i b := hout i b (by
          intro hblock
          exact hbj' (hblock.2.resolve_left hbj))
        exact False.elim (hbM (by rw [← hsame, hbN]))
  · intro hb
    rw [Finset.mem_singleton] at hb
    subst b
    subst L
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNij'⟩, by
        intro h
        have htrue : M i j' = true := (Finset.mem_filter.mp h).2
        rw [hMij'] at htrue
        exact Bool.false_ne_true htrue⟩

private theorem rowSupport_sdiff_left_eq_singleton_of_second_row {m n : ℕ}
    {M N : ZeroOneMat m n} {L i i' : Fin m} {j j' : Fin n} (hL : L = i')
    (hMi'j' : M i' j' = true) (hMi'j : M i' j = false)
    (hNi'j' : N i' j' = false)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → N a b = M a b) :
    ((Finset.univ.filter (fun b => M L b = true)) \
      (Finset.univ.filter (fun b => N L b = true))) = {j'} := by
  exact rowSupport_sdiff_left_eq_singleton (M := M) (N := N) (L := L) (i := i') (i' := i)
    (j := j') (j' := j) hL hMi'j' hMi'j hNi'j' (by
      intro a b hnot
      exact hout a b (by
        intro hblock
        apply hnot
        exact ⟨hblock.1.symm, hblock.2.symm⟩))

private theorem rowSupport_sdiff_right_eq_singleton_of_second_row {m n : ℕ}
    {M N : ZeroOneMat m n} {L i i' : Fin m} {j j' : Fin n} (hL : L = i')
    (hMi'j : M i' j = false) (hNi'j : N i' j = true)
    (hNi'j' : N i' j' = false)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → N a b = M a b) :
    ((Finset.univ.filter (fun b => N L b = true)) \
      (Finset.univ.filter (fun b => M L b = true))) = {j} := by
  exact rowSupport_sdiff_right_eq_singleton (M := M) (N := N) (L := L) (i := i') (i' := i)
    (j := j') (j' := j) hL hMi'j hNi'j hNi'j' (by
      intro a b hnot
      exact hout a b (by
        intro hblock
        apply hnot
        exact ⟨hblock.1.symm, hblock.2.symm⟩))

theorem exchange_of_fibre_crossing {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    {Mp Mq : MarginClass r s} (hne : rowPat L Mp ≠ rowPat L Mq) (hadj : (flipGraph r s).Adj Mp Mq) :
    ((Finset.univ.filter (fun b => rowPat L Mp b = true)) \
       (Finset.univ.filter (fun b => rowPat L Mq b = true))).card = 1 ∧
    ((Finset.univ.filter (fun b => rowPat L Mq b = true)) \
       (Finset.univ.filter (fun b => rowPat L Mp b = true))).card = 1 := by
  classical
  rw [flipGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨_hneMat, hint | hint⟩
  · rcases hint with
      ⟨i, i', j, j', hi_ne, _hj_ne, hMij, hMi'j', hMij', hMi'j,
        hNij, hNi'j', hNij', hNi'j, hout⟩
    have hrow : L = i ∨ L = i' := by
      by_contra h
      push_neg at h
      apply hne
      exact rowSupport_eq_of_interchange_row_ne (M := Mp.val) (N := Mq.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') h.1 h.2 hout
    rcases hrow with hL | hL
    · have hleft := rowSupport_sdiff_left_eq_singleton (M := Mp.val) (N := Mq.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMij hMij' hNij hout
      have hright := rowSupport_sdiff_right_eq_singleton (M := Mp.val) (N := Mq.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMij' hNij' hNij hout
      constructor <;> simp [rowPat, hleft, hright]
    · have hleft := rowSupport_sdiff_left_eq_singleton_of_second_row (M := Mp.val) (N := Mq.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMi'j' hMi'j hNi'j' hout
      have hright := rowSupport_sdiff_right_eq_singleton_of_second_row (M := Mp.val) (N := Mq.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMi'j hNi'j hNi'j' hout
      constructor <;> simp [rowPat, hleft, hright]
  · rcases hint with
      ⟨i, i', j, j', hi_ne, _hj_ne, hMij, hMi'j', hMij', hMi'j,
        hNij, hNi'j', hNij', hNi'j, hout⟩
    have hrow : L = i ∨ L = i' := by
      by_contra h
      push_neg at h
      apply hne
      have hfun := rowSupport_eq_of_interchange_row_ne (M := Mq.val) (N := Mp.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') h.1 h.2 hout
      exact hfun.symm
    rcases hrow with hL | hL
    · have hleftForMq := rowSupport_sdiff_left_eq_singleton (M := Mq.val) (N := Mp.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMij hMij' hNij hout
      have hrightForMq := rowSupport_sdiff_right_eq_singleton (M := Mq.val) (N := Mp.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMij' hNij' hNij hout
      constructor <;> simp [rowPat, hleftForMq, hrightForMq]
    · have hleftForMq := rowSupport_sdiff_left_eq_singleton_of_second_row (M := Mq.val) (N := Mp.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMi'j' hMi'j hNi'j' hout
      have hrightForMq := rowSupport_sdiff_right_eq_singleton_of_second_row (M := Mq.val) (N := Mp.val)
        (L := L) (i := i) (i' := i') (j := j) (j' := j') hL hMi'j hNi'j hNi'j' hout
      constructor <;> simp [rowPat, hleftForMq, hrightForMq]

/-- The quotient on realizable row patterns: two base supports are adjacent when some crossing
    interchange edge joins their row-pattern fibres. -/
def rowQuotientGraph {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n)) :
    SimpleGraph {X : Finset (Fin n) // B.Base X} :=
  SimpleGraph.fromRel (fun X Y =>
    ∃ (Mp Mq : MarginClass r s),
      rowSupport L Mp = X.val ∧ rowSupport L Mq = Y.val ∧ (flipGraph r s).Adj Mp Mq)

private theorem patOfSet_single_exchange {n : ℕ} {X Y : Finset (Fin n)} {i j : Fin n}
    (hXY : X \ Y = {i}) (hYX : Y \ X = {j}) :
    i ≠ j ∧ patOfSet X i = true ∧ patOfSet X j = false ∧
      (∀ b, patOfSet Y b =
        if b = i then false else if b = j then true else patOfSet X b) := by
  classical
  have hi_sdiff : i ∈ X \ Y := by simp [hXY]
  have hj_sdiff : j ∈ Y \ X := by simp [hYX]
  have hiX : i ∈ X := (Finset.mem_sdiff.mp hi_sdiff).1
  have hiY : i ∉ Y := (Finset.mem_sdiff.mp hi_sdiff).2
  have hjY : j ∈ Y := (Finset.mem_sdiff.mp hj_sdiff).1
  have hjX : j ∉ X := (Finset.mem_sdiff.mp hj_sdiff).2
  have hij : i ≠ j := by
    intro h
    exact hiY (by simpa [h] using hjY)
  refine ⟨hij, by simp [patOfSet, hiX], by simp [patOfSet, hjX], ?_⟩
  intro b
  by_cases hbi : b = i
  · subst b
    simp [patOfSet, hiY]
  · by_cases hbj : b = j
    · subst b
      simp [patOfSet, hjY, hij.symm]
    · by_cases hbX : b ∈ X
      · have hbY : b ∈ Y := by
          by_contra hbY
          have hsd : b ∈ X \ Y := Finset.mem_sdiff.mpr ⟨hbX, hbY⟩
          have hbi' : b = i := by simpa [hXY] using hsd
          exact hbi hbi'
        simp [patOfSet, hbi, hbj, hbX, hbY]
      · have hbY : b ∉ Y := by
          intro hbY
          have hsd : b ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hbY, hbX⟩
          have hbj' : b = j := by simpa [hYX] using hsd
          exact hbj hbj'
        simp [patOfSet, hbi, hbj, hbX, hbY]

theorem rowQuotient_adj_iff_exchange {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (X Y : {X : Finset (Fin n) // B.Base X}) :
    (rowQuotientGraph r s L B).Adj X Y ↔
      (X.val \ Y.val).card = 1 ∧ (Y.val \ X.val).card = 1 := by
  classical
  constructor
  · rw [rowQuotientGraph, SimpleGraph.fromRel_adj]
    rintro ⟨_hneXY, hcross | hcross⟩
    · rcases hcross with ⟨Mp, Mq, hMp, hMq, hadj⟩
      have hrowne : rowPat L Mp ≠ rowPat L Mq := by
        intro hrow
        apply _hneXY
        apply Subtype.ext
        rw [← hMp, ← hMq]
        ext b
        rw [rowSupport, rowSupport]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hbrow : Mp.val L b = Mq.val L b := congrFun hrow b
        rw [hbrow]
      have h := exchange_of_fibre_crossing r s L hrowne hadj
      rw [← hMp, ← hMq]
      simpa [rowSupport, rowPat] using h
    · rcases hcross with ⟨Mq, Mp, hMq, hMp, hadj⟩
      have hrowne : rowPat L Mq ≠ rowPat L Mp := by
        intro hrow
        apply _hneXY
        apply Subtype.ext
        rw [← hMp, ← hMq]
        ext b
        rw [rowSupport, rowSupport]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hbrow : Mq.val L b = Mp.val L b := congrFun hrow b
        rw [← hbrow]
      have h := exchange_of_fibre_crossing r s L hrowne hadj
      rw [← hMp, ← hMq]
      exact ⟨by simpa [rowSupport, rowPat] using h.2,
        by simpa [rowSupport, rowPat] using h.1⟩
  · intro hcard
    obtain ⟨i, hXYsingle⟩ := Finset.card_eq_one.mp hcard.1
    obtain ⟨j, hYXsingle⟩ := Finset.card_eq_one.mp hcard.2
    obtain ⟨hij, hp_i, hp_j, hq⟩ :=
      patOfSet_single_exchange (X := X.val) (Y := Y.val) hXYsingle hYXsingle
    have hFp : Nonempty {M : MarginClass r s // rowPat L M = patOfSet X.val} :=
      fibre_nonempty_of_support_nonempty ((hB X.val).mp X.property)
    have hFq : Nonempty {M : MarginClass r s // rowPat L M = patOfSet Y.val} :=
      fibre_nonempty_of_support_nonempty ((hB Y.val).mp Y.property)
    obtain ⟨Mp, Mq, hMpPat, hMqPat, hadj⟩ :=
      fibre_crossing_of_exchange r s L (patOfSet X.val) (patOfSet Y.val)
        hij hp_i hp_j hq hFp hFq
    rw [rowQuotientGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨Mp, Mq, ?_, ?_, hadj⟩⟩
    · intro hXY
      have hval : X.val = Y.val := congrArg Subtype.val hXY
      rw [hval] at hcard
      simpa using hcard.1
    · exact rowSupport_eq_of_rowPat_patOfSet hMpPat
    · exact rowSupport_eq_of_rowPat_patOfSet hMqPat

theorem rowQuotient_iso_baseExchange {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}) :
    Nonempty (rowQuotientGraph r s L B ≃g baseExchangeGraph B) := by
  classical
  refine ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩
  intro X Y
  rw [rowQuotient_adj_iff_exchange r s L B hB X Y, baseExchangeGraph,
    SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_hne, h | h⟩
    · exact h
    · exact ⟨h.2, h.1⟩
  · rintro ⟨hcardXY, hcardYX⟩
    refine ⟨?_, Or.inl ⟨hcardXY, hcardYX⟩⟩
    intro hXY
    have hval : X.val = Y.val := congrArg Subtype.val hXY
    rw [hval] at hcardXY
    simpa using hcardXY

private theorem isHamConnected_iso_sec5 {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (h : IsHamConnected H) :
    IsHamConnected G := by
  intro u v huv
  exact hasHamPath_iso e (h (e u) (e v) (e.injective.ne huv))

private theorem bipartite_no_triangle_rowQuotient {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {col : V → Bool} (hbip : IsProper2Coloring G col)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    False := by
  have habc := hbip a b hab
  have hbcc := hbip b c hbc
  have hcac := hbip c a hca
  cases ha : col a <;> cases hb : col b <;> cases hc : col c <;>
    simp [ha, hb, hc] at habc hbcc hcac

theorem rowQuotient_hamConnected {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hnb : ¬ ∃ col : {X : Finset (Fin n) // B.Base X} → Bool,
      ∀ X Y, (rowQuotientGraph r s L B).Adj X Y → col X ≠ col Y) :
    IsHamConnected (rowQuotientGraph r s L B) := by
  classical
  rcases rowQuotient_iso_baseExchange r s L B hB with ⟨e⟩
  refine isHamConnected_iso_sec5 e ?_
  apply naddef_pulleyblank_baseExchange
  intro hbase
  rcases hbase with ⟨col, hcol⟩
  apply hnb
  refine ⟨fun X => col (e X), ?_⟩
  intro X Y hXY
  exact hcol (e X) (e Y) (e.map_rel_iff.mpr hXY)

private theorem rowPattern_base_card_eq {m n : ℕ}
    {r : Fin (m+1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m+1)} {B : BaseFamily (Fin n)}
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X : Finset (Fin n)} (hX : B.Base X) :
    X.card = r L := by
  classical
  rcases (hB X).mp hX with ⟨M⟩
  have hPat : rowPat L M.val = patOfSet X :=
    rowPat_eq_patOfSet_of_rowSupport M.property
  calc
    X.card = ∑ b : Fin n, (if patOfSet X b then 1 else 0 : ℕ) :=
      (sum_patOfSet_eq_card X).symm
    _ = r L := rowPat_count_eq M.val hPat

private theorem rowPattern_base_key_lt_s_ge {n : ℕ} (s : Fin n → ℕ) {a b : Fin n}
    (h :
      (toLex (OrderDual.toDual (s a), a.val) : Lex (OrderDual ℕ × ℕ)) <
        (toLex (OrderDual.toDual (s b), b.val) : Lex (OrderDual ℕ × ℕ))) :
    s b ≤ s a := by
  simp only [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact le_of_eq h.1.symm

private theorem rowPattern_base_key_injective {n : ℕ} (s : Fin n → ℕ) :
    Function.Injective
      (fun c : Fin n =>
        (toLex (OrderDual.toDual (s c), c.val) : Lex (OrderDual ℕ × ℕ))) := by
  intro a b h
  have hpair :
      (OrderDual.toDual (s a), a.val) = (OrderDual.toDual (s b), b.val) :=
    toLex.injective h
  exact Fin.ext (congrArg Prod.snd hpair)

private structure RowPatternCol (n : ℕ) where
  val : Fin n
deriving DecidableEq, Fintype

private def RowPatternCol.equivFin {n : ℕ} : RowPatternCol n ≃ Fin n where
  toFun c := c.val
  invFun c := ⟨c⟩
  left_inv c := by cases c; rfl
  right_inv c := rfl

private theorem rowPattern_exists_rank {n : ℕ} (s : Fin n → ℕ) :
    ∃ rank : Fin n ≃ Fin n,
      ∀ {a b : Fin n}, (rank a : ℕ) < (rank b : ℕ) → s b ≤ s a := by
  classical
  let key : RowPatternCol n → Lex (OrderDual ℕ × ℕ) :=
    fun c => toLex (OrderDual.toDual (s c.val), c.val.val)
  have hkey : Function.Injective key := by
    intro a b h
    have hpair :
        (OrderDual.toDual (s a.val), a.val.val) =
          (OrderDual.toDual (s b.val), b.val.val) := toLex.injective h
    have hval : a.val = b.val := Fin.ext (congrArg Prod.snd hpair)
    cases a
    cases b
    simp at hval ⊢
    exact hval
  letI : LinearOrder (RowPatternCol n) := LinearOrder.lift' key hkey
  have hcard : (Finset.univ : Finset (RowPatternCol n)).card = n := by
    rw [Finset.card_univ]
    simpa using Fintype.card_congr (RowPatternCol.equivFin (n := n))
  let emb := Finset.orderEmbOfFin (Finset.univ : Finset (RowPatternCol n)) hcard
  have hemb_inj : Function.Injective emb := emb.injective
  have hbij : Function.Bijective emb := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hemb_inj, ?_⟩
    rw [Fintype.card_fin]
    simpa using (Fintype.card_congr (RowPatternCol.equivFin (n := n))).symm
  let colOfRankWrapped : Fin n ≃ RowPatternCol n := Equiv.ofBijective emb hbij
  let colOfRank : Fin n ≃ Fin n := colOfRankWrapped.trans RowPatternCol.equivFin
  let rank : Fin n ≃ Fin n := colOfRank.symm
  refine ⟨rank, ?_⟩
  intro a b hab
  have habFin : rank a < rank b := by exact hab
  have hcola : colOfRank (rank a) = a := by simp [rank, colOfRank]
  have hcolb : colOfRank (rank b) = b := by simp [rank, colOfRank]
  have hltWrapped : (⟨a⟩ : RowPatternCol n) < ⟨b⟩ := by
    have hltEmb : emb (rank a) < emb (rank b) :=
      (OrderEmbedding.lt_iff_lt emb).2 habFin
    have haWrapped : emb (rank a) = (⟨a⟩ : RowPatternCol n) := by
      have hval : (emb (rank a)).val = a := by
        simpa [colOfRank, RowPatternCol.equivFin, colOfRankWrapped] using hcola
      cases h : emb (rank a)
      simp [h] at hval ⊢
      exact hval
    have hbWrapped : emb (rank b) = (⟨b⟩ : RowPatternCol n) := by
      have hval : (emb (rank b)).val = b := by
        simpa [colOfRank, RowPatternCol.equivFin, colOfRankWrapped] using hcolb
      cases h : emb (rank b)
      simp [h] at hval ⊢
      exact hval
    simpa [haWrapped, hbWrapped] using hltEmb
  change key (⟨a⟩ : RowPatternCol n) < key ⟨b⟩ at hltWrapped
  simp only [key, Prod.Lex.toLex_lt_toLex] at hltWrapped
  rcases hltWrapped with h | h
  · exact h.le
  · exact le_of_eq h.1.symm

private theorem rowPattern_rank_filter_lt_card {n : ℕ} (rank : Fin n ≃ Fin n)
    {t : ℕ} (ht : t ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun c => (rank c : ℕ) < t)).card = t := by
  classical
  trans (Finset.range t).card
  · refine Finset.card_bij (fun c hc => (rank c : ℕ)) ?_ ?_ ?_
    · intro c hc
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2
    · intro a ha b hb h
      apply rank.injective
      exact Fin.ext h
    · intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have hjn : j < n := lt_of_lt_of_le hjt ht
      refine ⟨rank.symm ⟨j, hjn⟩, ?_, ?_⟩
      · simp [hjt]
      · simp
  · exact Finset.card_range t

private theorem rowPattern_sum_insert_erase_lt {α : Type*} [DecidableEq α]
    {X : Finset α} {c d : α} {f : α → ℕ}
    (hd : d ∈ X) (hc : c ∉ X) (hlt : f c < f d) :
    (∑ x ∈ insert c (X.erase d), f x) < (∑ x ∈ X, f x) := by
  have hcErase : c ∉ X.erase d := by simp [hc]
  have hleft : (∑ x ∈ insert c (X.erase d), f x) =
      f c + ∑ x ∈ X.erase d, f x := by
    rw [Finset.sum_insert hcErase]
  have hright0 := Finset.sum_erase_add X f hd
  have hright : (∑ x ∈ X, f x) = (∑ x ∈ X.erase d, f x) + f d := hright0.symm
  rw [hleft, hright]
  omega

private theorem rowPattern_min_base {n : ℕ} (B : BaseFamily (Fin n))
    (w : Finset (Fin n) → ℕ) (P : Finset (Fin n) → Prop) [DecidablePred P]
    (hne : ∃ X, B.Base X ∧ P X) :
    ∃ X, B.Base X ∧ P X ∧
      ∀ Y, B.Base Y → P Y → w X ≤ w Y := by
  classical
  let F : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun X => B.Base X ∧ P X)
  have hF : F.Nonempty := by
    rcases hne with ⟨X, hX, hPX⟩
    refine ⟨X, ?_⟩
    simp [F, hX, hPX]
  rcases Finset.exists_min_image F w hF with ⟨X, hXF, hmin⟩
  refine ⟨X, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hXF).2.1
  · exact (Finset.mem_filter.mp hXF).2.2
  · intro Y hY hPY
    exact hmin Y (by simp [F, hY, hPY])

private theorem rowPattern_pin_min {n : ℕ}
    (B : BaseFamily (Fin n)) (rankCol : Fin n → ℕ)
    (w : Finset (Fin n) → ℕ) (F : Finset (Fin n) → Prop)
    {X T : Finset (Fin n)} {k : ℕ}
    (hXcard : X.card = k) (hTcard : T.card = k)
    (hXmin : B.Base X ∧ F X ∧ ∀ Y, B.Base Y → F Y → w X ≤ w Y)
    (hshift_base : ∀ {c d}, rankCol c < rankCol d → d ∈ X → c ∉ X →
      B.Base X → B.Base (insert c (X.erase d)))
    (hshift_ok : ∀ {c d}, c ∈ T → d ∉ T → rankCol c < rankCol d →
      F X → d ∈ X → c ∉ X → F (insert c (X.erase d)))
    (hweight : ∀ {c d}, rankCol c < rankCol d → d ∈ X → c ∉ X →
      w (insert c (X.erase d)) < w X)
    (hkey : ∀ c ∈ T, c ∉ X → ∃ d ∈ X, d ∉ T ∧ rankCol c < rankCol d) :
    X = T := by
  classical
  have hsub : T ⊆ X := by
    intro c hcT
    by_contra hcX
    rcases hkey c hcT hcX with ⟨d, hdX, hdT, hlt⟩
    let Y := insert c (X.erase d)
    have hYbase : B.Base Y := hshift_base hlt hdX hcX hXmin.1
    have hYF : F Y := hshift_ok hcT hdT hlt hXmin.2.1 hdX hcX
    have hltw : w Y < w X := hweight hlt hdX hcX
    have hminle : w X ≤ w Y := hXmin.2.2 Y hYbase hYF
    exact (not_lt_of_ge hminle hltw).elim
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

private theorem rowPattern_base_triangle_of_shifted {m n : ℕ}
    (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hact : IsActive r s) (hn : 3 ≤ n)
    (not_loop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∈ X)
    (not_coloop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∉ X) :
    ∃ X Y Z : Finset (Fin n),
      B.Base X ∧ B.Base Y ∧ B.Base Z ∧
      (X \ Y).card = 1 ∧ (Y \ X).card = 1 ∧
      (Y \ Z).card = 1 ∧ (Z \ Y).card = 1 ∧
      (Z \ X).card = 1 ∧ (X \ Z).card = 1 := by
  classical
  obtain ⟨rank, hrank⟩ := rowPattern_exists_rank s
  set rc : Fin n → ℕ := fun c => (rank c : ℕ) with hrc
  set w : Finset (Fin n) → ℕ := fun Z => ∑ c ∈ Z, rc c with hw
  set k : ℕ := r L with hkdef
  have hkpos : 0 < k := by simpa [k] using (hact.1 L).1
  have hkltn : k < n := by simpa [k] using (hact.1 L).2
  have hbc : ∀ {Z : Finset (Fin n)}, B.Base Z → Z.card = k := by
    intro Z hZ
    simpa [k] using rowPattern_base_card_eq hB hZ
  have hcolval : ∀ (t : ℕ) (ht : t < n), rc (rank.symm ⟨t, ht⟩) = t := by
    intro t ht
    simp [rc]
  have hSB : ∀ {c d : Fin n} {Z : Finset (Fin n)}, rc c < rc d → d ∈ Z → c ∉ Z →
      B.Base Z → B.Base (insert c (Z.erase d)) := by
    intro c d Z hlt hd hc hZ
    exact rowPattern_shifted r s L B hB (hrank hlt) hd hc hZ
  have hW : ∀ {c d : Fin n} {Z : Finset (Fin n)}, rc c < rc d → d ∈ Z → c ∉ Z →
      w (insert c (Z.erase d)) < w Z := by
    intro c d Z hlt hd hc
    exact rowPattern_sum_insert_erase_lt (f := rc) hd hc hlt
  have hpick : ∀ {T Z : Finset (Fin n)}, Z.card = k → T.card = k → ∀ c ∈ T, c ∉ Z →
      ∃ d, d ∈ Z ∧ d ∉ T := by
    intro T Z hZc hTc c hcT hcZ
    have hTZne : (T \ Z).Nonempty := ⟨c, Finset.mem_sdiff.mpr ⟨hcT, hcZ⟩⟩
    have hcards : (Z \ T).card = (T \ Z).card := Finset.card_sdiff_comm (by rw [hZc, hTc])
    have hZTne : (Z \ T).Nonempty := by
      rw [← Finset.card_pos, hcards, Finset.card_pos]
      exact hTZne
    rcases hZTne with ⟨d, hd⟩
    exact ⟨d, (Finset.mem_sdiff.mp hd).1, (Finset.mem_sdiff.mp hd).2⟩
  by_cases hk1 : k = 1
  · have h0 : (0 : ℕ) < n := by omega
    have h1 : (1 : ℕ) < n := by omega
    have h2 : (2 : ℕ) < n := by omega
    let a0 : Fin n := rank.symm ⟨0, h0⟩
    let a1 : Fin n := rank.symm ⟨1, h1⟩
    let a2 : Fin n := rank.symm ⟨2, h2⟩
    have hBsingle : ∀ a : Fin n, B.Base ({a} : Finset (Fin n)) := by
      intro a
      rcases not_loop a with ⟨X, hX, haX⟩
      have hXcard : X.card = 1 := by rw [hbc hX, hk1]
      have huniq : ∀ y ∈ X, y = a := by
        intro y hy
        exact Finset.card_le_one.mp (le_of_eq hXcard) y hy a haX
      have hXeq : X = {a} := by
        ext y
        constructor
        · intro hy
          simp [huniq y hy]
        · intro hy
          rw [Finset.mem_singleton] at hy
          rw [hy]
          exact haX
      simpa [hXeq] using hX
    have ha01 : a0 ≠ a1 := by
      intro h
      have := congrArg rank h
      simp [a0, a1] at this
    have ha12 : a1 ≠ a2 := by
      intro h
      have := congrArg rank h
      simp [a1, a2] at this
    have ha20 : a2 ≠ a0 := by
      intro h
      have := congrArg rank h
      simp [a2, a0] at this
    have hsdiff_single {a b : Fin n} (hab : a ≠ b) :
        (({a} : Finset (Fin n)) \ ({b} : Finset (Fin n))).card = 1 := by
      have heq : ({a} : Finset (Fin n)) \ ({b} : Finset (Fin n)) = {a} := by
        ext x
        by_cases hxa : x = a
        · subst x
          simp [hab]
        · simp [hxa]
      rw [heq, Finset.card_singleton]
    refine ⟨{a0}, {a1}, {a2}, hBsingle a0, hBsingle a1, hBsingle a2,
      hsdiff_single ha01, hsdiff_single ha01.symm,
      hsdiff_single ha12, hsdiff_single ha12.symm,
      hsdiff_single ha20, hsdiff_single ha20.symm⟩
  · have hk2 : 2 ≤ k := by omega
    have hkm2 : k - 2 < n := by omega
    have hkm1 : k - 1 < n := by omega
    have hkn' : k < n := hkltn
    set e2 : Fin n := rank.symm ⟨k - 2, hkm2⟩ with he2
    set e1 : Fin n := rank.symm ⟨k - 1, hkm1⟩ with he1
    set e0 : Fin n := rank.symm ⟨k, hkn'⟩ with he0
    have hrce2 : rc e2 = k - 2 := hcolval _ _
    have hrce1 : rc e1 = k - 1 := hcolval _ _
    have hrce0 : rc e0 = k := hcolval _ _
    have he2e1 : e2 ≠ e1 := by
      intro h
      have := congrArg rc h
      omega
    have he2e0 : e2 ≠ e0 := by
      intro h
      have := congrArg rc h
      omega
    have he1e0 : e1 ≠ e0 := by
      intro h
      have := congrArg rc h
      omega
    set T0 : Finset (Fin n) := Finset.univ.filter (fun c => rc c < k) with hT0
    have hT0card : T0.card = k := by
      simpa [T0, rc] using rowPattern_rank_filter_lt_card rank (by omega)
    obtain ⟨X0, hX0base, _, hX0min⟩ :=
      rowPattern_min_base B w (fun _ => True) ⟨Classical.choose B.exists_base,
        Classical.choose_spec B.exists_base, trivial⟩
    have hX0T0 : X0 = T0 := by
      refine rowPattern_pin_min B rc w (fun _ => True) (hbc hX0base) hT0card
        ⟨hX0base, trivial, hX0min⟩
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) (fun _ _ _ _ _ _ => trivial)
        (fun hlt hd hc => hW hlt hd hc) ?_
      intro c hcT hcX
      obtain ⟨d, hdX, hdT⟩ := hpick (hbc hX0base) hT0card c hcT hcX
      have hck : rc c < k := by simpa [T0] using hcT
      have hdk : k ≤ rc d := by
        by_contra h
        exact hdT (by simp [T0]; omega)
      exact ⟨d, hdX, hdT, by omega⟩
    have hB0 : B.Base T0 := hX0T0 ▸ hX0base
    set T1 : Finset (Fin n) := (Finset.univ.filter (fun c => rc c ≤ k - 2)) ∪ {e0} with hT1
    have hT1card : T1.card = k := by
      rw [hT1, Finset.card_union_of_disjoint]
      · have hfilter :
            (Finset.univ.filter (fun c : Fin n => rc c ≤ k - 2)) =
              Finset.univ.filter (fun c : Fin n => rc c < k - 1) := by
          ext c
          simp
          omega
        rw [hfilter]
        rw [show (Finset.univ.filter (fun c : Fin n => rc c < k - 1)).card = k - 1 by
          simpa [rc] using rowPattern_rank_filter_lt_card rank (t := k - 1) (by omega)]
        simp
        omega
      · rw [Finset.disjoint_singleton_right]
        simp [hrce0]
        omega
    obtain ⟨X1, hX1base, hX1mem, hX1min⟩ :=
      rowPattern_min_base B w (fun X => e0 ∈ X)
        (by rcases not_loop e0 with ⟨X, hX, hm⟩; exact ⟨X, hX, hm⟩)
    have hX1T1 : X1 = T1 := by
      refine rowPattern_pin_min B rc w (fun X => e0 ∈ X) (hbc hX1base) hT1card
        ⟨hX1base, hX1mem, hX1min⟩
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) ?_
        (fun hlt hd hc => hW hlt hd hc) ?_
      · intro c d hcT hdT hlt hFX hdX hcX
        have hdne0 : d ≠ e0 := by
          intro hd
          apply hdT
          rw [hd]
          simp [T1]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hdne0.symm, hFX⟩)
      · intro c hcT hcX
        obtain ⟨d, hdX, hdT⟩ := hpick (hbc hX1base) hT1card c hcT hcX
        have hce0 : c ≠ e0 := by
          intro h
          exact hcX (h ▸ hX1mem)
        have hck : rc c ≤ k - 2 := by
          have := hcT
          rw [hT1, Finset.mem_union, Finset.mem_singleton] at this
          rcases this with h | h
          · simpa using h
          · exact (hce0 h).elim
        have hdk : k - 1 ≤ rc d := by
          by_contra h
          exact hdT (by rw [hT1, Finset.mem_union]; left; simp; omega)
        exact ⟨d, hdX, hdT, by omega⟩
    have hB1 : B.Base T1 := hX1T1 ▸ hX1base
    set T2 : Finset (Fin n) := (Finset.univ.filter (fun c => rc c < k - 2)) ∪ {e1, e0} with hT2
    have hT2card : T2.card = k := by
      rw [hT2, Finset.card_union_of_disjoint]
      · rw [show (Finset.univ.filter (fun c : Fin n => rc c < k - 2)).card = k - 2 by
          simpa [rc] using rowPattern_rank_filter_lt_card rank (t := k - 2) (by omega)]
        have hpair : ({e1, e0} : Finset (Fin n)).card = 2 := by
          simp [he1e0]
        rw [hpair]
        omega
      · rw [Finset.disjoint_left]
        intro c hc hc2
        rw [Finset.mem_insert, Finset.mem_singleton] at hc2
        rcases hc2 with h | h
        · subst c
          simp [hrce1] at hc
          omega
        · subst c
          simp [hrce0] at hc
          omega
    obtain ⟨X2, hX2base, hX2mem, hX2min⟩ :=
      rowPattern_min_base B w (fun X => e2 ∉ X)
        (by rcases not_coloop e2 with ⟨X, hX, hm⟩; exact ⟨X, hX, hm⟩)
    have hX2T2 : X2 = T2 := by
      refine rowPattern_pin_min B rc w (fun X => e2 ∉ X) (hbc hX2base) hT2card
        ⟨hX2base, hX2mem, hX2min⟩
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) ?_
        (fun hlt hd hc => hW hlt hd hc) ?_
      · intro c d hcT hdT hlt hFX hdX hcX
        have hce2 : c ≠ e2 := by
          intro h
          subst c
          rw [hT2, Finset.mem_union] at hcT
          rcases hcT with hsmall | hpair
          · simp [hrce2] at hsmall
          · rw [Finset.mem_insert, Finset.mem_singleton] at hpair
            rcases hpair with h | h
            · exact he2e1 h
            · exact he2e0 h
        intro hmem
        rw [Finset.mem_insert] at hmem
        rcases hmem with h | h
        · exact hce2 h.symm
        · exact hFX (Finset.mem_of_mem_erase h)
      · intro c hcT hcX
        obtain ⟨d, hdX, hdT⟩ := hpick (hbc hX2base) hT2card c hcT hcX
        have hcle : rc c ≤ k := by
          rw [hT2, Finset.mem_union] at hcT
          rcases hcT with h | h
          · simp at h
            omega
          · rw [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · subst c
              rw [hrce1]
              omega
            · subst c
              rw [hrce0]
        have hdne2 : rc d ≠ k - 2 := by
          intro hdrc
          have hd_eq_e2 : d = e2 := by
            apply rank.injective
            exact Fin.ext (by simpa [rc, e2] using hdrc)
          exact hX2mem (hd_eq_e2 ▸ hdX)
        have hdk : k < rc d := by
          by_contra h
          apply hdT
          rw [hT2, Finset.mem_union]
          by_cases hsmall : rc d < k - 2
          · left
            simp [hsmall]
          · right
            rw [Finset.mem_insert, Finset.mem_singleton]
            have : rc d = k - 1 ∨ rc d = k := by omega
            rcases this with hd1 | hd0
            · left
              apply rank.injective
              exact Fin.ext (by simpa [rc, e1, hrce1] using hd1)
            · right
              apply rank.injective
              exact Fin.ext (by simpa [rc, e0, hrce0] using hd0)
        exact ⟨d, hdX, hdT, by omega⟩
    have hB2 : B.Base T2 := hX2T2 ▸ hX2base
    have hrc_inj {a b : Fin n} (h : rc a = rc b) : a = b := by
      apply rank.injective
      exact Fin.ext (by simpa [rc] using h)
    refine ⟨T0, T1, T2, hB0, hB1, hB2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have heq : T0 \ T1 = {e1} := by
        ext c
        constructor
        · intro hc
          have hc0 : c ∈ T0 := (Finset.mem_sdiff.mp hc).1
          have hc1 : c ∉ T1 := (Finset.mem_sdiff.mp hc).2
          have hclt : rc c < k := by simpa [T0] using hc0
          have hnotle : ¬ rc c ≤ k - 2 := by
            intro hle
            apply hc1
            rw [hT1, Finset.mem_union]
            left
            simp [hle]
          have hne0 : c ≠ e0 := by
            intro h
            apply hc1
            rw [h, hT1, Finset.mem_union]
            right
            simp
          have hrc_eq : rc c = k - 1 := by omega
          have hce1 : c = e1 := hrc_inj (by rw [hrc_eq, hrce1])
          simpa [hce1]
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · simp [T0, hrce1]
            omega
          · rw [hT1, Finset.mem_union, Finset.mem_singleton]
            intro h
            rcases h with hsmall | hzero
            · simp [hrce1] at hsmall
              omega
            · exact he1e0 hzero
      rw [heq, Finset.card_singleton]
    · have heq : T1 \ T0 = {e0} := by
        ext c
        constructor
        · intro hc
          have hc1 : c ∈ T1 := (Finset.mem_sdiff.mp hc).1
          have hc0 : c ∉ T0 := (Finset.mem_sdiff.mp hc).2
          rw [hT1, Finset.mem_union, Finset.mem_singleton] at hc1
          rcases hc1 with hsmall | hzero
          · exfalso
            apply hc0
            have hle : rc c ≤ k - 2 := by simpa using hsmall
            have : rc c < k := by omega
            simpa [T0] using this
          · simpa [hzero]
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · simp [T1]
          · simp [T0, hrce0]
      rw [heq, Finset.card_singleton]
    · have heq : T1 \ T2 = {e2} := by
        ext c
        constructor
        · intro hc
          have hc1 : c ∈ T1 := (Finset.mem_sdiff.mp hc).1
          have hc2 : c ∉ T2 := (Finset.mem_sdiff.mp hc).2
          rw [hT1, Finset.mem_union, Finset.mem_singleton] at hc1
          rcases hc1 with hsmall | hzero
          · have hnotlt : ¬ rc c < k - 2 := by
              intro hlt
              apply hc2
              rw [hT2, Finset.mem_union]
              left
              simp [hlt]
            have hle : rc c ≤ k - 2 := by simpa using hsmall
            have hrc_eq : rc c = k - 2 := by omega
            have hce2 : c = e2 := hrc_inj (by rw [hrc_eq, hrce2])
            simpa [hce2]
          · subst c
            exfalso
            apply hc2
            simp [T2]
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · rw [hT1, Finset.mem_union]
            left
            simp [hrce2]
          · rw [hT2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            intro h
            rcases h with hsmall | hpair
            · simp [hrce2] at hsmall
            · rcases hpair with h | h
              · exact he2e1 h
              · exact he2e0 h
      rw [heq, Finset.card_singleton]
    · have heq : T2 \ T1 = {e1} := by
        ext c
        constructor
        · intro hc
          have hc2 : c ∈ T2 := (Finset.mem_sdiff.mp hc).1
          have hc1 : c ∉ T1 := (Finset.mem_sdiff.mp hc).2
          rw [hT2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc2
          rcases hc2 with hsmall | hpair
          · exfalso
            apply hc1
            have hlt : rc c < k - 2 := by simpa using hsmall
            rw [hT1, Finset.mem_union]
            left
            simp
            omega
          · rcases hpair with h | h
            · simpa [h]
            · exfalso
              apply hc1
              rw [h, hT1, Finset.mem_union]
              right
              simp
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · simp [T2]
          · rw [hT1, Finset.mem_union, Finset.mem_singleton]
            intro h
            rcases h with hsmall | hzero
            · simp [hrce1] at hsmall
              omega
            · exact he1e0 hzero
      rw [heq, Finset.card_singleton]
    · have heq : T2 \ T0 = {e0} := by
        ext c
        constructor
        · intro hc
          have hc2 : c ∈ T2 := (Finset.mem_sdiff.mp hc).1
          have hc0 : c ∉ T0 := (Finset.mem_sdiff.mp hc).2
          rw [hT2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc2
          rcases hc2 with hsmall | hpair
          · exfalso
            apply hc0
            have hlt : rc c < k - 2 := by simpa using hsmall
            have : rc c < k := by omega
            simpa [T0] using this
          · rcases hpair with h | h
            · subst c
              exfalso
              apply hc0
              simp [T0, hrce1]
              omega
            · simpa [h]
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · simp [T2]
          · simp [T0, hrce0]
      rw [heq, Finset.card_singleton]
    · have heq : T0 \ T2 = {e2} := by
        ext c
        constructor
        · intro hc
          have hc0 : c ∈ T0 := (Finset.mem_sdiff.mp hc).1
          have hc2 : c ∉ T2 := (Finset.mem_sdiff.mp hc).2
          have hclt : rc c < k := by simpa [T0] using hc0
          have hnotlt : ¬ rc c < k - 2 := by
            intro hlt
            apply hc2
            rw [hT2, Finset.mem_union]
            left
            simp [hlt]
          have hne1 : c ≠ e1 := by
            intro h
            apply hc2
            rw [h, hT2, Finset.mem_union]
            right
            simp
          have hne0 : c ≠ e0 := by
            intro h
            apply hc2
            rw [h, hT2, Finset.mem_union]
            right
            simp
          have hrc_eq : rc c = k - 2 := by
            by_contra hneq
            have : rc c = k - 1 ∨ rc c = k := by omega
            rcases this with h1 | h0
            · exact hne1 (hrc_inj (by rw [h1, hrce1]))
            · exact hne0 (hrc_inj (by rw [h0, hrce0]))
          have hce2 : c = e2 := hrc_inj (by rw [hrc_eq, hrce2])
          simpa [hce2]
        · intro hc
          rw [Finset.mem_singleton] at hc
          subst c
          rw [Finset.mem_sdiff]
          constructor
          · simp [T0, hrce2]
            omega
          · rw [hT2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            intro h
            rcases h with hsmall | hpair
            · simp [hrce2] at hsmall
            · rcases hpair with h | h
              · exact he2e1 h
              · exact he2e0 h
      rw [heq, Finset.card_singleton]


/-! ### The paper's lexicographic compression (Lemma 5.12 as printed) -/

/-- If two `k`-sets built over a common part `A` as `A ∪ {x, y}` and `A ∪ {x, z}` differ
    in their second added element only, the difference each way is a single element. -/
private theorem rowPattern_sdiff_pair_card {n : ℕ} {A : Finset (Fin n)} {x y z : Fin n}
    (hy : y ∉ A) (hyx : y ≠ x) (hyz : y ≠ z) :
    ((A ∪ {x, y}) \ (A ∪ {x, z})).card = 1 := by
  have heq : (A ∪ {x, y}) \ (A ∪ {x, z}) = {y} := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hin, hout⟩
      rcases hin with h | h | h
      · exact absurd (Or.inl h) hout
      · exact absurd (Or.inr (Or.inl h)) hout
      · exact h
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), by
        rintro (h | h | h)
        · exact hy h
        · exact hyx h
        · exact hyz h⟩
  rw [heq, Finset.card_singleton]

/-- The compression walk. `hlex` states T's lexicographic minimality in
    min-of-symmetric-difference form: for every other candidate `Y`, some element of
    `T \ Y` has rank at most everything in the symmetric difference — exactly the paper's
    "otherwise `Y` would be lexicographically earlier than `T`". -/
private theorem rowPattern_pin_lex {n : ℕ} (B : BaseFamily (Fin n)) (rc : Fin n → ℕ)
    (hrcinj : Function.Injective rc)
    (F : Finset (Fin n) → Prop) {T : Finset (Fin n)} {k : ℕ}
    (hTcard : T.card = k)
    (hbc : ∀ {Z : Finset (Fin n)}, B.Base Z → Z.card = k)
    (hshift_base : ∀ {c d : Fin n} {Z : Finset (Fin n)}, rc c < rc d → d ∈ Z → c ∉ Z →
        B.Base Z → B.Base (insert c (Z.erase d)))
    (hshift_ok : ∀ {c d : Fin n} {Z : Finset (Fin n)}, c ∈ T → d ∉ T → rc c < rc d →
        F Z → d ∈ Z → c ∉ Z → F (insert c (Z.erase d)))
    (hlex : ∀ Y : Finset (Fin n), F Y → Y.card = k → Y ≠ T →
        ∃ a ∈ T \ Y, ∀ b ∈ (T \ Y) ∪ (Y \ T), rc a ≤ rc b)
    (hstart : ∃ X, B.Base X ∧ F X) :
    B.Base T := by
  classical
  obtain ⟨X0, hX0, hF0⟩ := hstart
  suffices h : ∀ (W : ℕ) (X : Finset (Fin n)),
      (∑ c ∈ X, rc c) < W → B.Base X → F X → B.Base T by
    exact h ((∑ c ∈ X0, rc c) + 1) X0 (Nat.lt_succ_self _) hX0 hF0
  intro W
  induction W with
  | zero => intro X hw _ _; omega
  | succ W ih =>
      intro X hw hX hFX
      by_cases hXT : X = T
      · exact hXT ▸ hX
      · obtain ⟨a, haTX, hamin⟩ := hlex X hFX (hbc hX) hXT
        have haT : a ∈ T := (Finset.mem_sdiff.mp haTX).1
        have haX : a ∉ X := (Finset.mem_sdiff.mp haTX).2
        -- X \ T is nonempty (equal cardinalities, X ≠ T).
        have hXTne : (X \ T).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro hsub
          exact hXT (Finset.eq_of_subset_of_card_le hsub (by rw [hTcard, hbc hX]))
        obtain ⟨b, hbXT⟩ := hXTne
        have hbX : b ∈ X := (Finset.mem_sdiff.mp hbXT).1
        have hbT : b ∉ T := (Finset.mem_sdiff.mp hbXT).2
        have hab : a ≠ b := fun h => hbT (h ▸ haT)
        have hlt : rc a < rc b :=
          lt_of_le_of_ne (hamin b (Finset.mem_union_right _ hbXT))
            (fun h => hab (hrcinj h))
        have hsum : (∑ c ∈ insert a (X.erase b), rc c) < ∑ c ∈ X, rc c :=
          rowPattern_sum_insert_erase_lt hbX haX hlt
        exact ih (insert a (X.erase b)) (by omega)
          (hshift_base hlt hbX haX hX)
          (hshift_ok haT hbT hlt hFX hbX haX)

/-- **The paper's compression (Lemma 5.12, as printed).** Same conclusion as
    `rowPattern_base_triangle_of_shifted`, obtained by the paper's LEXICOGRAPHIC compression
    walk (`rowPattern_pin_lex`) in place of the rank-sum minimizer: the three bases are
    B0 = {ranks < k}, B1 = {ranks <= k-2} u {rank k}, B2 = {ranks < k-2} u {ranks k-1, k},
    pairwise one exchange apart. This is the route `rowQuotient_nonbip` (the mainline) uses;
    the original rank-sum route is kept as `rowQuotient_nonbip_rankmin`. -/
private theorem rowPattern_base_triangle_lex {m n : ℕ}
    (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hact : IsActive r s) (hn : 3 ≤ n)
    (not_loop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∈ X)
    (not_coloop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∉ X) :
    ∃ X Y Z : Finset (Fin n),
      B.Base X ∧ B.Base Y ∧ B.Base Z ∧
      (X \ Y).card = 1 ∧ (Y \ X).card = 1 ∧
      (Y \ Z).card = 1 ∧ (Z \ Y).card = 1 ∧
      (Z \ X).card = 1 ∧ (X \ Z).card = 1 := by
  classical
  -- Rank the columns by weakly decreasing column sum.
  obtain ⟨rank, hrank⟩ := rowPattern_exists_rank s
  set rc : Fin n → ℕ := fun c => (rank c : ℕ) with hrc
  have hrcinj : Function.Injective rc := fun a b h => rank.injective (Fin.ext h)
  set k : ℕ := r L with hkdef
  have hkpos : 0 < k := by simpa [k] using (hact.1 L).1
  have hkltn : k < n := by simpa [k] using (hact.1 L).2
  have hbc : ∀ {Z : Finset (Fin n)}, B.Base Z → Z.card = k := by
    intro Z hZ
    simpa [k] using rowPattern_base_card_eq hB hZ
  have hSB : ∀ {c d : Fin n} {Z : Finset (Fin n)}, rc c < rc d → d ∈ Z → c ∉ Z →
      B.Base Z → B.Base (insert c (Z.erase d)) := by
    intro c d Z hlt hd hc hZ
    exact rowPattern_shifted r s L B hB (hrank hlt) hd hc hZ
  by_cases hk1 : k = 1
  -- k = 1: every singleton is a basis (no loops); any three of the n ≥ 3 columns
  -- give a triangle directly. (Identical to the mainline; no compression is needed.)
  · have h0 : (0 : ℕ) < n := by omega
    have h1 : (1 : ℕ) < n := by omega
    have h2 : (2 : ℕ) < n := by omega
    let a0 : Fin n := rank.symm ⟨0, h0⟩
    let a1 : Fin n := rank.symm ⟨1, h1⟩
    let a2 : Fin n := rank.symm ⟨2, h2⟩
    have hBsingle : ∀ a : Fin n, B.Base ({a} : Finset (Fin n)) := by
      intro a
      rcases not_loop a with ⟨X, hX, haX⟩
      have hXcard : X.card = 1 := by rw [hbc hX, hk1]
      have hXeq : X = {a} := by
        ext y
        constructor
        · intro hy
          simp [Finset.card_le_one.mp (le_of_eq hXcard) y hy a haX]
        · intro hy
          rw [Finset.mem_singleton] at hy
          exact hy ▸ haX
      exact hXeq ▸ hX
    have hne : ∀ {i j : ℕ} (hi : i < n) (hj : j < n), i ≠ j →
        rank.symm ⟨i, hi⟩ ≠ rank.symm ⟨j, hj⟩ := by
      intro i j hi hj hij h
      have h2 := congrArg rank h
      simp only [Equiv.apply_symm_apply, Fin.mk.injEq] at h2
      exact hij h2
    have hsdiff : ∀ {a b : Fin n}, a ≠ b →
        (({a} : Finset (Fin n)) \ ({b} : Finset (Fin n))).card = 1 := by
      intro a b hab
      have heq : ({a} : Finset (Fin n)) \ ({b} : Finset (Fin n)) = {a} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro ⟨h, _⟩
          exact h
        · rintro rfl
          exact ⟨rfl, hab⟩
      rw [heq, Finset.card_singleton]
    have h01 : a0 ≠ a1 := hne h0 h1 (by omega)
    have h12 : a1 ≠ a2 := hne h1 h2 (by omega)
    have h20 : a2 ≠ a0 := hne h2 h0 (by omega)
    exact ⟨{a0}, {a1}, {a2}, hBsingle a0, hBsingle a1, hBsingle a2,
      hsdiff h01, hsdiff h01.symm, hsdiff h12, hsdiff h12.symm,
      hsdiff h20, hsdiff h20.symm⟩
  -- k ≥ 2: the paper's three compressions.
  · have hk2 : 2 ≤ k := by omega
    have hkm2 : k - 2 < n := by omega
    have hkm1 : k - 1 < n := by omega
    set e2 : Fin n := rank.symm ⟨k - 2, hkm2⟩ with he2def
    set e1 : Fin n := rank.symm ⟨k - 1, hkm1⟩ with he1def
    set e0 : Fin n := rank.symm ⟨k, hkltn⟩ with he0def
    have hrce2 : rc e2 = k - 2 := by simp [rc, e2]
    have hrce1 : rc e1 = k - 1 := by simp [rc, e1]
    have hrce0 : rc e0 = k := by simp [rc, e0]
    have he2e1 : e2 ≠ e1 := fun h => by
      have := congrArg rc h
      omega
    have he2e0 : e2 ≠ e0 := fun h => by
      have := congrArg rc h
      omega
    have he1e0 : e1 ≠ e0 := fun h => by
      have := congrArg rc h
      omega
    -- The common part A (ranks below k−2) and the three targets.
    set A : Finset (Fin n) := Finset.univ.filter (fun c => rc c < k - 2) with hAdef
    have hAcard : A.card = k - 2 := by
      simpa [A, rc] using rowPattern_rank_filter_lt_card rank (t := k - 2) (by omega)
    have hmemA : ∀ c, c ∈ A ↔ rc c < k - 2 := by
      intro c
      simp [A]
    have he2A : e2 ∉ A := by rw [hmemA]; omega
    have he1A : e1 ∉ A := by rw [hmemA]; omega
    have he0A : e0 ∉ A := by rw [hmemA]; omega
    -- Rank characterization: a column of rank t is the column rank.symm t.
    have hof_rc : ∀ {c : Fin n} {t : ℕ} (ht : t < n), rc c = t → c = rank.symm ⟨t, ht⟩ := by
      intro c t ht h
      have : rank c = ⟨t, ht⟩ := Fin.ext h
      simpa using congrArg rank.symm this
    set T0 : Finset (Fin n) := A ∪ {e2, e1} with hT0def
    set T1 : Finset (Fin n) := A ∪ {e2, e0} with hT1def
    set T2 : Finset (Fin n) := A ∪ {e1, e0} with hT2def
    have hpaircard : ∀ {x y : Fin n}, x ≠ y → ({x, y} : Finset (Fin n)).card = 2 := by
      intro x y hxy
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    have hTcard : ∀ {x y : Fin n}, x ∉ A → y ∉ A → x ≠ y → (A ∪ {x, y}).card = k := by
      intro x y hx hy hxy
      rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_right]
        intro c hc
        rcases Finset.mem_insert.mp hc with h | h
        · exact h ▸ hx
        · exact (Finset.mem_singleton.mp h) ▸ hy), hAcard, hpaircard hxy]
      omega
    have hT0card : T0.card = k := hTcard he2A he1A he2e1
    have hT1card : T1.card = k := hTcard he2A he0A he2e0
    have hT2card : T2.card = k := hTcard he1A he0A he1e0
    -- Membership characterizations by rank value.
    have hmemT0 : ∀ c, c ∈ T0 ↔ rc c < k := by
      intro c
      rw [hT0def, Finset.mem_union, hmemA, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | rfl | rfl) <;> omega
      · intro h
        by_cases h2 : rc c < k - 2
        · exact Or.inl h2
        · by_cases h1 : rc c = k - 2
          · exact Or.inr (Or.inl (hof_rc hkm2 h1))
          · exact Or.inr (Or.inr (hof_rc hkm1 (by omega)))
    have hmemT1 : ∀ c, c ∈ T1 ↔ (rc c ≤ k - 2 ∨ rc c = k) := by
      intro c
      rw [hT1def, Finset.mem_union, hmemA, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | rfl | rfl) <;> omega
      · rintro (h | h)
        · by_cases h2 : rc c < k - 2
          · exact Or.inl h2
          · exact Or.inr (Or.inl (hof_rc hkm2 (by omega)))
        · exact Or.inr (Or.inr (hof_rc hkltn h))
    have hmemT2 : ∀ c, c ∈ T2 ↔ (rc c < k - 2 ∨ rc c = k - 1 ∨ rc c = k) := by
      intro c
      rw [hT2def, Finset.mem_union, hmemA, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | rfl | rfl) <;> omega
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl (hof_rc hkm1 h))
        · exact Or.inr (Or.inr (hof_rc hkltn h))
    -- Nonemptiness of T \ Y for a same-size Y ≠ T.
    have hTdiff_ne : ∀ {T' Y : Finset (Fin n)}, T'.card = k → Y.card = k → Y ≠ T' →
        (T' \ Y).Nonempty := by
      intro T' Y hT' hY hne
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    -- The three compressions (the paper's lex-first arguments).
    have hB0 : B.Base T0 := by
      refine rowPattern_pin_lex B rc hrcinj (fun _ => True) hT0card (fun h => hbc h)
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) (fun _ _ _ _ _ _ => trivial) ?_
        ⟨Classical.choose B.exists_base, Classical.choose_spec B.exists_base, trivial⟩
      intro Y _ hYcard hYT
      obtain ⟨a, ha⟩ := Finset.exists_min_image _ rc (hTdiff_ne hT0card hYcard hYT)
      refine ⟨a, ha.1, ?_⟩
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact ha.2 b hb
      · -- b ∈ Y \ T0 has rank ≥ k; a ∈ T0 has rank < k.
        have hbT0 : rc b ≥ k := by
          have := (Finset.mem_sdiff.mp hb).2
          rw [hmemT0] at this
          omega
        have haT0 : rc a < k := by
          have := (Finset.mem_sdiff.mp ha.1).1
          rwa [hmemT0] at this
        omega
    have hB1 : B.Base T1 := by
      obtain ⟨Xs, hXs, hXse0⟩ := not_loop e0
      refine rowPattern_pin_lex B rc hrcinj (fun Y => e0 ∈ Y) hT1card (fun h => hbc h)
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) ?_ ?_ ⟨Xs, hXs, hXse0⟩
      · -- the requirement "contains e0" is preserved: the shifted-out column d ∉ T1
        -- cannot be e0 ∈ T1.
        intro c d Z hcT hdT _ hFZ hd _
        have hde0 : d ≠ e0 := fun h => hdT (h ▸ (by rw [hmemT1]; omega))
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hde0 h.symm, hFZ⟩)
      · intro Y hFY hYcard hYT
        obtain ⟨a, ha⟩ := Finset.exists_min_image _ rc (hTdiff_ne hT1card hYcard hYT)
        refine ⟨a, ha.1, ?_⟩
        intro b hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact ha.2 b hb
        · -- a ∈ T1 \ Y: a ≠ e0 (e0 ∈ Y), so rc a ≤ k−2; b ∉ T1 has rank k−1 or > k.
          have hae0 : a ≠ e0 := fun h =>
            (Finset.mem_sdiff.mp ha.1).2 (h ▸ hFY)
          have haT1 : rc a ≤ k - 2 := by
            have := (Finset.mem_sdiff.mp ha.1).1
            rw [hmemT1] at this
            rcases this with h | h
            · exact h
            · exact absurd (hof_rc hkltn h) hae0
          have hbT1 : ¬(rc b ≤ k - 2 ∨ rc b = k) := by
            have := (Finset.mem_sdiff.mp hb).2
            rwa [hmemT1] at this
          omega
    have hB2 : B.Base T2 := by
      obtain ⟨Xs, hXs, hXse2⟩ := not_coloop e2
      refine rowPattern_pin_lex B rc hrcinj (fun Y => e2 ∉ Y) hT2card (fun h => hbc h)
        (fun hlt hd hc hZ => hSB hlt hd hc hZ) ?_ ?_ ⟨Xs, hXs, hXse2⟩
      · -- the requirement "avoids e2" is preserved: the shifted-in column c ∈ T2
        -- cannot be e2 ∉ T2.
        intro c d Z hcT _ _ hFZ _ _
        have hce2 : c ≠ e2 := fun h => by
          rw [h, hmemT2] at hcT
          omega
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hce2 h.symm
        · exact hFZ (Finset.mem_of_mem_erase h)
      · intro Y hFY hYcard hYT
        obtain ⟨a, ha⟩ := Finset.exists_min_image _ rc (hTdiff_ne hT2card hYcard hYT)
        refine ⟨a, ha.1, ?_⟩
        intro b hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact ha.2 b hb
        · -- b ∈ Y \ T2: b ≠ e2 (Y avoids e2), so rc b > k; a ∈ T2 has rank ≤ k.
          have hbe2 : b ≠ e2 := fun h => hFY (h ▸ (Finset.mem_sdiff.mp hb).1)
          have hbT2 : ¬(rc b < k - 2 ∨ rc b = k - 1 ∨ rc b = k) := by
            have := (Finset.mem_sdiff.mp hb).2
            rwa [hmemT2] at this
          have hbne : rc b ≠ k - 2 := fun h => hbe2 (hof_rc hkm2 h)
          have haT2 : rc a ≤ k := by
            have := (Finset.mem_sdiff.mp ha.1).1
            rw [hmemT2] at this
            omega
          omega
    -- The pairwise single exchanges.
    have hT0T1 : (T0 \ T1).card = 1 := rowPattern_sdiff_pair_card he1A he2e1.symm he1e0
    have hT1T0 : (T1 \ T0).card = 1 := rowPattern_sdiff_pair_card he0A he2e0.symm he1e0.symm
    have hT1T2 : (T1 \ T2).card = 1 := by
      rw [hT1def, hT2def, Finset.pair_comm e2 e0, Finset.pair_comm e1 e0]
      exact rowPattern_sdiff_pair_card he2A he2e0 he2e1
    have hT2T1 : (T2 \ T1).card = 1 := by
      rw [hT1def, hT2def, Finset.pair_comm e2 e0, Finset.pair_comm e1 e0]
      exact rowPattern_sdiff_pair_card he1A he1e0 he2e1.symm
    have hT2T0 : (T2 \ T0).card = 1 := by
      rw [hT0def, hT2def, Finset.pair_comm e2 e1]
      exact rowPattern_sdiff_pair_card he0A he1e0.symm he2e0.symm
    have hT0T2 : (T0 \ T2).card = 1 := by
      rw [hT0def, hT2def, Finset.pair_comm e2 e1]
      exact rowPattern_sdiff_pair_card he2A he2e1 he2e0
    exact ⟨T0, T1, T2, hB0, hB1, hB2, hT0T1, hT1T0, hT1T2, hT2T1, hT2T0, hT0T2⟩

theorem rowQuotient_nonbip {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hact : IsActive r s) (hn : 3 ≤ n)
    (hvar : ∀ j, CellVaries r s L j) :
    ¬ ∃ col : {X : Finset (Fin n) // B.Base X} → Bool,
        ∀ P Q, (rowQuotientGraph r s L B).Adj P Q → col P ≠ col Q := by
  classical
  have not_loop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∈ X := by
    intro j
    rcases hvar j with ⟨M, N, hMN⟩
    cases hM : M.val L j <;> cases hN : N.val L j
    · exact False.elim (hMN (by rw [hM, hN]))
    · refine ⟨rowSupport L N, (hB _).mpr ⟨N, rfl⟩, ?_⟩
      simp [rowSupport, hN]
    · refine ⟨rowSupport L M, (hB _).mpr ⟨M, rfl⟩, ?_⟩
      simp [rowSupport, hM]
    · exact False.elim (hMN (by rw [hM, hN]))
  have not_coloop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∉ X := by
    intro j
    rcases hvar j with ⟨M, N, hMN⟩
    cases hM : M.val L j <;> cases hN : N.val L j
    · exact False.elim (hMN (by rw [hM, hN]))
    · refine ⟨rowSupport L M, (hB _).mpr ⟨M, rfl⟩, ?_⟩
      simp [rowSupport, hM]
    · refine ⟨rowSupport L N, (hB _).mpr ⟨N, rfl⟩, ?_⟩
      simp [rowSupport, hN]
    · exact False.elim (hMN (by rw [hM, hN]))
  have hbase_tri :
      ∃ X Y Z : Finset (Fin n),
        B.Base X ∧ B.Base Y ∧ B.Base Z ∧
        (X \ Y).card = 1 ∧ (Y \ X).card = 1 ∧
        (Y \ Z).card = 1 ∧ (Z \ Y).card = 1 ∧
        (Z \ X).card = 1 ∧ (X \ Z).card = 1 := by
    exact rowPattern_base_triangle_lex r s L B hB hact hn not_loop not_coloop
  rcases hbase_tri with
    ⟨X, Y, Z, hX, hY, hZ, hXY, hYX, hYZ, hZY, hZX, hXZ⟩
  let PX : {X : Finset (Fin n) // B.Base X} := ⟨X, hX⟩
  let PY : {X : Finset (Fin n) // B.Base X} := ⟨Y, hY⟩
  let PZ : {X : Finset (Fin n) // B.Base X} := ⟨Z, hZ⟩
  have hPX_PY : (rowQuotientGraph r s L B).Adj PX PY := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hXY, hYX⟩
  have hPY_PZ : (rowQuotientGraph r s L B).Adj PY PZ := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hYZ, hZY⟩
  have hPZ_PX : (rowQuotientGraph r s L B).Adj PZ PX := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hZX, hXZ⟩
  rintro ⟨col, hcol⟩
  exact bipartite_no_triangle_rowQuotient (G := rowQuotientGraph r s L B)
    (col := col) hcol hPX_PY hPY_PZ hPZ_PX

/-- **ALTERNATE proof of Lemma 5.12** (the development's original route): the same
    statement as `rowQuotient_nonbip`, with the triangle obtained by MINIMIZING the rank
    sum (`rowPattern_pin_min` via `rowPattern_base_triangle_of_shifted`) instead of the
    paper's lexicographic walk. Kept so both compression devices stay machine-checked. -/
theorem rowQuotient_nonbip_rankmin {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m+1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hact : IsActive r s) (hn : 3 ≤ n)
    (hvar : ∀ j, CellVaries r s L j) :
    ¬ ∃ col : {X : Finset (Fin n) // B.Base X} → Bool,
        ∀ P Q, (rowQuotientGraph r s L B).Adj P Q → col P ≠ col Q := by
  classical
  have not_loop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∈ X := by
    intro j
    rcases hvar j with ⟨M, N, hMN⟩
    cases hM : M.val L j <;> cases hN : N.val L j
    · exact False.elim (hMN (by rw [hM, hN]))
    · refine ⟨rowSupport L N, (hB _).mpr ⟨N, rfl⟩, ?_⟩
      simp [rowSupport, hN]
    · refine ⟨rowSupport L M, (hB _).mpr ⟨M, rfl⟩, ?_⟩
      simp [rowSupport, hM]
    · exact False.elim (hMN (by rw [hM, hN]))
  have not_coloop : ∀ j : Fin n, ∃ X, B.Base X ∧ j ∉ X := by
    intro j
    rcases hvar j with ⟨M, N, hMN⟩
    cases hM : M.val L j <;> cases hN : N.val L j
    · exact False.elim (hMN (by rw [hM, hN]))
    · refine ⟨rowSupport L M, (hB _).mpr ⟨M, rfl⟩, ?_⟩
      simp [rowSupport, hM]
    · refine ⟨rowSupport L N, (hB _).mpr ⟨N, rfl⟩, ?_⟩
      simp [rowSupport, hN]
    · exact False.elim (hMN (by rw [hM, hN]))
  have hbase_tri :
      ∃ X Y Z : Finset (Fin n),
        B.Base X ∧ B.Base Y ∧ B.Base Z ∧
        (X \ Y).card = 1 ∧ (Y \ X).card = 1 ∧
        (Y \ Z).card = 1 ∧ (Z \ Y).card = 1 ∧
        (Z \ X).card = 1 ∧ (X \ Z).card = 1 := by
    exact rowPattern_base_triangle_of_shifted r s L B hB hact hn not_loop not_coloop
  rcases hbase_tri with
    ⟨X, Y, Z, hX, hY, hZ, hXY, hYX, hYZ, hZY, hZX, hXZ⟩
  let PX : {X : Finset (Fin n) // B.Base X} := ⟨X, hX⟩
  let PY : {X : Finset (Fin n) // B.Base X} := ⟨Y, hY⟩
  let PZ : {X : Finset (Fin n) // B.Base X} := ⟨Z, hZ⟩
  have hPX_PY : (rowQuotientGraph r s L B).Adj PX PY := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hXY, hYX⟩
  have hPY_PZ : (rowQuotientGraph r s L B).Adj PY PZ := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hYZ, hZY⟩
  have hPZ_PX : (rowQuotientGraph r s L B).Adj PZ PX := by
    rw [rowQuotient_adj_iff_exchange r s L B hB]
    exact ⟨hZX, hXZ⟩
  rintro ⟨col, hcol⟩
  exact bipartite_no_triangle_rowQuotient (G := rowQuotientGraph r s L B)
    (col := col) hcol hPX_PY hPY_PZ hPZ_PX

/-! ## Block 3a: concrete row-quotient plumbing skeleton -/

/-- The concrete quotient vertices are the realizable row-support bases. -/
abbrev RowQ {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n)) :=
  {X : Finset (Fin n) // B.Base X}

noncomputable instance rowQ_fintype {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)} :
    Fintype (RowQ r s L B) := by
  classical
  infer_instance

noncomputable instance rowQ_decidableEq {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)} :
    DecidableEq (RowQ r s L B) := by
  classical
  infer_instance

/-- Projection from a matrix to its realizable row-support quotient vertex. -/
def rowProj {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}) :
    MarginClass r s → RowQ r s L B :=
  fun M => ⟨rowSupport L M, (hB _).mpr ⟨M, rfl⟩⟩

/-- The abstract quotient relation for `rowProj` is the concrete row-quotient graph. -/
theorem quotientAdj_rowProj_iff_rowQuotientAdj {m n : ℕ}
    (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ) (L : Fin (m + 1))
    (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (X Y : RowQ r s L B) :
    quotientAdj (flipGraph r s) (rowProj hB) X Y ↔
      (rowQuotientGraph r s L B).Adj X Y := by
  classical
  constructor
  · rintro ⟨hXY, Mp, hMp, Mq, hMq, hadj⟩
    rw [rowQuotientGraph, SimpleGraph.fromRel_adj]
    refine ⟨hXY, Or.inl ⟨Mp, Mq, ?_, ?_, hadj⟩⟩
    · exact congrArg Subtype.val (Finset.mem_filter.mp hMp).2
    · exact congrArg Subtype.val (Finset.mem_filter.mp hMq).2
  · rw [rowQuotientGraph, SimpleGraph.fromRel_adj]
    rintro ⟨hXY, hcross | hcross⟩
    · rcases hcross with ⟨Mp, Mq, hMp, hMq, hadj⟩
      refine ⟨hXY, Mp, ?_, Mq, ?_, hadj⟩
      · simp [fibre, rowProj, hMp]
      · simp [fibre, rowProj, hMq]
    · rcases hcross with ⟨Mq, Mp, hMq, hMp, hadj⟩
      refine ⟨hXY, Mp, ?_, Mq, ?_, hadj.symm⟩
      · simp [fibre, rowProj, hMp]
      · simp [fibre, rowProj, hMq]

/-- A row-quotient edge changes the source and target row supports by one column each. -/
theorem rowQuotient_singletons_of_quotientAdj {m n : ℕ}
    (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ) (L : Fin (m + 1))
    (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B}
    (hXY : quotientAdj (flipGraph r s) (rowProj hB) X Y) :
    ∃ i j : Fin n, X.val \ Y.val = {i} ∧ Y.val \ X.val = {j} := by
  classical
  have hrowAdj : (rowQuotientGraph r s L B).Adj X Y :=
    (quotientAdj_rowProj_iff_rowQuotientAdj r s L B hB X Y).mp hXY
  have hcard :
      (X.val \ Y.val).card = 1 ∧ (Y.val \ X.val).card = 1 :=
    (rowQuotient_adj_iff_exchange r s L B hB X Y).mp hrowAdj
  rcases Finset.card_eq_one.mp hcard.1 with ⟨i, hi⟩
  rcases Finset.card_eq_one.mp hcard.2 with ⟨j, hj⟩
  exact ⟨i, j, hi, hj⟩

/-- The `rowProj` fibre over a support is the same induced graph as the Boolean row-pattern fibre. -/
theorem rowProj_fibre_iso_patOfSet {m n : ℕ}
    (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ) (L : Fin (m + 1))
    (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (X : RowQ r s L B) :
    Nonempty (fibreGraph (flipGraph r s) (rowProj hB) X ≃g
      fibreGraph (flipGraph r s) (rowPat L) (patOfSet X.val)) := by
  classical
  let e :
      {M : MarginClass r s // rowProj hB M = X} ≃
        {M : MarginClass r s // rowPat L M = patOfSet X.val} :=
    { toFun := fun (M : {M : MarginClass r s // rowProj hB M = X}) =>
        (⟨M.val, rowPat_eq_patOfSet_of_rowSupport
          (congrArg Subtype.val M.property)⟩ :
          {M : MarginClass r s // rowPat L M = patOfSet X.val})
      invFun := fun (M : {M : MarginClass r s // rowPat L M = patOfSet X.val}) =>
        (⟨M.val, by
          show rowProj hB M.val = X
          apply Subtype.ext
          exact rowSupport_eq_of_rowPat_patOfSet M.property⟩ :
          {M : MarginClass r s // rowProj hB M = X})
      left_inv := by
        intro M
        apply Subtype.ext
        rfl
      right_inv := by
        intro M
        apply Subtype.ext
        rfl }
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro M N
  change (flipGraph r s).Adj M.val N.val ↔ (flipGraph r s).Adj M.val N.val
  rfl

private theorem isMH_iso_sec5 {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hH : IsMH H) : IsMH G := by
  have transport : ∀ {u v : V}, HasHamPath H (e u) (e v) → HasHamPath G u v := by
    intro u v h
    exact hasHamPath_iso e h
  rcases hH with hHC | ⟨colH, hproper, hsurj, hlace⟩
  · exact Or.inl fun u v huv => transport (hHC (e u) (e v) (e.injective.ne huv))
  · refine Or.inr ⟨fun v => colH (e v),
      fun u v huv => hproper (e u) (e v) (e.map_rel_iff.mpr huv), ?_,
      fun u v hc => transport (hlace (e u) (e v) hc)⟩
    intro b
    obtain ⟨w, hw⟩ := hsurj b
    obtain ⟨v, hv⟩ := e.surjective w
    exact ⟨v, by simpa [hv] using hw⟩

/-- The concrete `rowProj` fibres inherit `IsMH` from the Boolean row-pattern fibres. -/
theorem rowProj_fibre_isMH {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {a b : MarginClass r s} (hsep : rowPat L a ≠ rowPat L b)
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card (MarginClass r s) → IsInterchangeGraph H → IsMH H)
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (X : RowQ r s L B) :
    IsMH (fibreGraph (flipGraph r s) (rowProj hB) X) := by
  classical
  rcases rowProj_fibre_iso_patOfSet r s L B hB X with ⟨e⟩
  refine isMH_iso_sec5 e ?_
  exact rowFibre_isMH hsep IH (patOfSet X.val)
    (fibre_nonempty_of_support_nonempty ((hB X.val).mp X.property))

/-- A Hamilton run inside one fibre, flattened to vertices of the ambient graph. -/
structure FibreRun {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V] [DecidableEq Q]
    (G : SimpleGraph V) (π : V → Q) (q : Q) (x y : V) where
  run : List V
  hsub : ∀ v ∈ run, v ∈ fibre π q
  hnodup : run.Nodup
  hcover : ∀ v : V, v ∈ fibre π q → v ∈ run
  hne : run ≠ []
  hchain : run.IsChain G.Adj
  hhead : run.head? = some x
  hlast : run.getLast? = some y

private theorem walk_support_head?_sec5 {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : p.support.head? = some u := by
  rw [head?_eq_head_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.head_support p)

private theorem walk_support_getLast?_sec5 {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : p.support.getLast? = some v := by
  rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.getLast_support p)

/-- Extract the list-level run consumed by `thread_fibres` from a Hamilton path in a fibre graph. -/
def FibreRun.of_hasHamPath {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] {G : SimpleGraph V} {π : V → Q} {q : Q}
    (x y : {v : V // π v = q})
    (hpath : HasHamPath (fibreGraph G π q) x y) :
    FibreRun G π q x.val y.val := by
  classical
  let p := Classical.choose hpath
  have hp : p.IsHamiltonian := Classical.choose_spec hpath
  refine
    { run := p.support.map Subtype.val
      hsub := ?_
      hnodup := ?_
      hcover := ?_
      hne := ?_
      hchain := ?_
      hhead := ?_
      hlast := ?_ }
  · intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, _hw, rfl⟩ := hv
    simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
    exact w.property
  · exact List.Nodup.map Subtype.val_injective hp.isPath.support_nodup
  · intro v hv
    rw [List.mem_map]
    have hq : π v = q := (Finset.mem_filter.mp hv).2
    exact ⟨⟨v, hq⟩, hp.mem_support ⟨v, hq⟩, rfl⟩
  · intro hnil
    cases hs : p.support with
    | nil => exact p.support_ne_nil hs
    | cons z zs => simp [hs] at hnil
  · exact List.isChain_map_of_isChain Subtype.val (by
      intro M N hMN
      exact SimpleGraph.induce_adj.mp hMN) p.isChain_adj_support
  · rw [List.head?_map, walk_support_head?_sec5 p]
    rfl
  · rw [List.getLast?_map, walk_support_getLast?_sec5 p]
    rfl

/-- The one-vertex fibre run. -/
def FibreRun.singleton {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] {G : SimpleGraph V} {π : V → Q} {q : Q}
    (x : V) (hx : x ∈ fibre π q)
    (huniq : ∀ v : V, v ∈ fibre π q → v = x) :
    FibreRun G π q x x := by
  classical
  refine
    { run := [x]
      hsub := ?_
      hnodup := by simp
      hcover := ?_
      hne := by simp
      hchain := by simp
      hhead := by simp
      hlast := by simp }
  · intro v hv
    rw [List.mem_singleton] at hv
    exact hv ▸ hx
  · intro v hv
    simp [huniq v hv]

private theorem threadedList_head?_of_head {V : Type u} {Q : Type v}
    (qs : List Q) (runs : Q → List V) {q₀ : Q} {a : V}
    (hqs : qs.head? = some q₀) (hrun : (runs q₀).head? = some a) :
    (threadedList qs runs).head? = some a := by
  cases qs with
  | nil =>
      simp at hqs
  | cons q qs =>
      simp at hqs
      subst q
      rw [threadedList, List.join]
      change ((runs q₀) ++ (qs.map runs).flatten).head? = some a
      rw [List.head?_append, hrun]
      rfl

private theorem threadedList_getLast?_of_getLast {V : Type u} {Q : Type v}
    (qs : List Q) (runs : Q → List V) {q₁ : Q} {b : V}
    (hqs : qs.getLast? = some q₁) (hrun : (runs q₁).getLast? = some b)
    (hrun_ne : ∀ q : Q, q ∈ qs → runs q ≠ []) :
    (threadedList qs runs).getLast? = some b := by
  induction qs with
  | nil =>
      simp at hqs
  | cons q qs ih =>
      cases qs with
      | nil =>
          simp at hqs
          subst q
          simpa [threadedList, List.join] using hrun
      | cons q' qs =>
          have htail_last : (q' :: qs).getLast? = some q₁ := by
            simpa [List.getLast?_cons_of_ne_nil (by simp : q' :: qs ≠ [])] using hqs
          have htail_ne : ∀ q₂ : Q, q₂ ∈ q' :: qs → runs q₂ ≠ [] := by
            intro q₂ hq₂
            exact hrun_ne q₂ (by simp [hq₂])
          have htail_thread :
              (threadedList (q' :: qs) runs).getLast? = some b :=
            ih htail_last htail_ne
          have htail_thread_ne : threadedList (q' :: qs) runs ≠ [] := by
            intro hnil
            rw [hnil] at htail_thread
            simp at htail_thread
          rw [threadedList, List.join]
          change ((runs q) ++ threadedList (q' :: qs) runs).getLast? = some b
          rw [List.getLast?_append_of_ne_nil _ htail_thread_ne]
          exact htail_thread

/-- The terminal compatibility cases from which a fibre run can be extracted. -/
inductive FibreTerminalChoice {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] (G : SimpleGraph V) (π : V → Q) (q : Q)
    (x y : {v : V // π v = q}) where
  | hamConnected (hconn : IsHamConnected (fibreGraph G π q)) (hne : x ≠ y)
  | hamLaceable (col : {v : V // π v = q} → Bool)
      (hlace : IsHamLaceable (fibreGraph G π q) col) (hopp : col x ≠ col y)
  | singleton (hxy : x = y) (huniq : ∀ v : V, v ∈ fibre π q → v = x.val)

/-- Reverse a compatible terminal choice inside a fibre. -/
def FibreTerminalChoice.symm {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] {G : SimpleGraph V} {π : V → Q} {q : Q}
    {x y : {v : V // π v = q}}
    (hchoice : FibreTerminalChoice G π q x y) :
    FibreTerminalChoice G π q y x := by
  rcases hchoice with ⟨hconn, hne⟩ | ⟨col, hlace, hopp⟩ | ⟨hxy, huniq⟩
  · exact FibreTerminalChoice.hamConnected hconn hne.symm
  · exact FibreTerminalChoice.hamLaceable col hlace hopp.symm
  · exact FibreTerminalChoice.singleton hxy.symm (by
      intro v hv
      simpa [hxy] using huniq v hv)

/-- Build a list-level fibre run once the chosen terminals match the fibre's MH mode. -/
def fibre_run_of_terminals {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] {G : SimpleGraph V} {π : V → Q} {q : Q}
    (x y : {v : V // π v = q})
    (hchoice : FibreTerminalChoice G π q x y) :
    FibreRun G π q x.val y.val := by
  classical
  rcases hchoice with ⟨hconn, hne⟩ | ⟨col, hlace, hopp⟩ | ⟨hxy, huniq⟩
  · exact FibreRun.of_hasHamPath x y (hconn x y hne)
  · exact FibreRun.of_hasHamPath x y (hlace x y hopp)
  · subst y
    exact FibreRun.singleton x.val (by simp [fibre, x.property]) huniq

/-- A fibre run with its quotient-indexed endpoints bundled as subtype vertices. -/
structure FibrePack {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] (G : SimpleGraph V) (π : V → Q) (q : Q) where
  entry : {v : V // π v = q}
  exit : {v : V // π v = q}
  run : FibreRun G π q entry.val exit.val

/-- Adjacent pack endpoints give the boundary relation required by the threaded list. -/
theorem FibrePack.boundary_of_adj {V : Type u} {Q : Type v} [Fintype V]
    [DecidableEq V] [DecidableEq Q] {G : SimpleGraph V} {π : V → Q}
    {q q' : Q} (P : FibrePack G π q) (P' : FibrePack G π q')
    (hadj : G.Adj P.exit.val P'.entry.val) :
    listBoundaryAdj5 G.Adj P.run.run P'.run.run := by
  simpa [listBoundaryAdj5, P.run.hlast, P'.run.hhead] using hadj

/-- A quotient walk carrying the edge proof at each step. -/
inductive QWalk {Q : Type u} (R : Q → Q → Prop) : Q → Q → Type u where
  | nil (q : Q) : QWalk R q q
  | cons {q q' q'' : Q} (hstep : R q q') (tail : QWalk R q' q'') :
      QWalk R q q''

namespace QWalk

/-- Append one edge to the right end of a quotient walk. -/
def concat {Q : Type u} {R : Q → Q → Prop} :
    ∀ {q q' q'' : Q}, QWalk R q q' → R q' q'' → QWalk R q q''
  | _, _, _, nil q, h => cons h (nil _)
  | _, _, _, cons hstep tail, h => cons hstep (concat tail h)

/-- Reverse a walk across a symmetric relation. -/
def symm {Q : Type u} {R : Q → Q → Prop} (hsymm : ∀ {q q'}, R q q' → R q' q) :
    ∀ {q q' : Q}, QWalk R q q' → QWalk R q' q
  | _, _, nil q => nil q
  | _, _, cons hstep tail => by
      exact concat (symm hsymm tail) (hsymm hstep)

/-- The vertex list of a quotient walk, `q₀ :: … :: q₁`. -/
def support {Q : Type u} {R : Q → Q → Prop} :
    ∀ {q q' : Q}, QWalk R q q' → List Q
  | q, _, nil _ => [q]
  | q, _, cons _ tail => q :: support tail

theorem support_nil {Q : Type u} {R : Q → Q → Prop} (q : Q) :
    support (nil (R := R) q) = [q] := rfl

theorem support_cons {Q : Type u} {R : Q → Q → Prop}
    {q q' q'' : Q} (h : R q q') (tail : QWalk R q' q'') :
    support (cons h tail) = q :: support tail := rfl

theorem support_ne_nil {Q : Type u} {R : Q → Q → Prop} {q q' : Q}
    (w : QWalk R q q') : support w ≠ [] := by
  cases w <;> simp [support]

theorem head_mem_support {Q : Type u} {R : Q → Q → Prop} {q q' : Q}
    (w : QWalk R q q') : q ∈ support w := by
  cases w <;> simp [support]

theorem end_mem_support {Q : Type u} {R : Q → Q → Prop} {q q' : Q}
    (w : QWalk R q q') : q' ∈ support w := by
  induction w with
  | nil q => simp [support]
  | cons h tail ih => simp [support]; exact Or.inr ih

end QWalk

private theorem List.isChain_mono_on {α : Type u} {R S : α → α → Prop}
    {l : List α} (hchain : l.IsChain R)
    (himp : ∀ {x y : α}, x ∈ l → y ∈ l → R x y → S x y) :
    l.IsChain S := by
  induction l with
  | nil =>
      simpa using hchain
  | cons x xs ih =>
      rw [List.isChain_cons] at hchain ⊢
      constructor
      · intro y hy
        exact himp (by simp) (by simp [List.mem_of_mem_head? hy]) (hchain.1 y hy)
      · exact ih hchain.2 (fun {y z} hy hz hyz =>
          himp (by simp [hy]) (by simp [hz]) hyz)

private def qwalk_of_isChain {Q : Type u} {R : Q → Q → Prop} :
    ∀ {qs : List Q} {q q' : Q}, qs.IsChain R → qs.head? = some q →
      qs.getLast? = some q' → QWalk R q q'
  | [], q, _q', _hchain, hhead, _hlast => by
      simp at hhead
  | [x], q, q', _hchain, hhead, hlast => by
      simp at hhead hlast
      subst x
      subst q'
      exact QWalk.nil q
  | x :: y :: xs, q, q', hchain, hhead, hlast => by
      simp at hhead
      subst x
      rw [List.isChain_cons] at hchain
      have htail_last : (y :: xs).getLast? = some q' := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : y :: xs ≠ [])] using hlast
      exact QWalk.cons (hchain.1 y (by simp))
        (qwalk_of_isChain hchain.2 (by simp) htail_last)

private theorem qwalk_of_isChain_support {Q : Type u} {R : Q → Q → Prop} :
    ∀ {qs : List Q} {q q' : Q} (hchain : qs.IsChain R)
      (hhead : qs.head? = some q) (hlast : qs.getLast? = some q'),
      QWalk.support (qwalk_of_isChain hchain hhead hlast) = qs
  | [], q, _q', _hchain, hhead, _hlast => by
      simp at hhead
  | [x], q, q', _hchain, hhead, hlast => by
      simp at hhead hlast
      subst x
      subst q'
      rfl
  | x :: y :: xs, q, q', hchain, hhead, hlast => by
      simp at hhead
      subst x
      rw [List.isChain_cons] at hchain
      have htail_last : (y :: xs).getLast? = some q' := by
        simpa [List.getLast?_cons_of_ne_nil (by simp : y :: xs ≠ [])] using hlast
      have htail_support :
          QWalk.support (qwalk_of_isChain hchain.2
            (by simp : (y :: xs).head? = some y) htail_last) = y :: xs :=
        qwalk_of_isChain_support (q := y) (q' := q') hchain.2
          (by simp) htail_last
      simp [qwalk_of_isChain, QWalk.support, htail_support]

/-- Endpoint choices and fibre runs along a quotient thread.  Later blocks construct this data. -/
structure ThreadTerminals {V : Type u} {Q : Type v} [Fintype V] [DecidableEq V]
    [DecidableEq Q] (G : SimpleGraph V) (π : V → Q) (qs : List Q) (a b : V) where
  entry : Q → V
  exit : Q → V
  hentry_fibre : ∀ q : Q, entry q ∈ fibre π q
  hexit_fibre : ∀ q : Q, exit q ∈ fibre π q
  hrun : ∀ q : Q, FibreRun G π q (entry q) (exit q)
  hfirst : (threadedList qs (fun q => (hrun q).run)).head? = some a
  hlast : (threadedList qs (fun q => (hrun q).run)).getLast? = some b
  hcross : qs.IsChain (runBoundaryAdj G (fun q => (hrun q).run))

/-- Packer from terminal choices into the abstract pivot-thread data consumed by
`reduction_pivot_from_components`. -/
def thread_from_terminals {V : Type u} {Q : Type u} [Fintype V] [Fintype Q]
    [DecidableEq V] [DecidableEq Q] {G : SimpleGraph V} {π : V → Q}
    {qs : List Q} {a b : V}
    (hqs_chain : qs.IsChain (quotientAdj G π))
    (hqs_nodup : qs.Nodup) (hqs_cover : ∀ q : Q, q ∈ qs)
    (T : ThreadTerminals G π qs a b) :
    PivotThreadData G a b where
  Q := Q
  π := π
  qs := qs
  runs := fun q => (T.hrun q).run
  hqs_chain := hqs_chain
  hqs_nodup := hqs_nodup
  hqs_cover := hqs_cover
  hrun_sub := fun q => (T.hrun q).hsub
  hrun_nodup := fun q => (T.hrun q).hnodup
  hrun_cover := fun q => (T.hrun q).hcover
  hrun_ne := fun q _hq => (T.hrun q).hne
  hcross := T.hcross
  hrun_chain := fun q => (T.hrun q).hchain
  hhead := T.hfirst
  hlast := T.hlast

/-- The quotient Hamilton path as the list data consumed by the threading layer. -/
structure QuotientHamPathList {Q : Type u} [Fintype Q] [DecidableEq Q]
    (R : Q → Q → Prop) (Xa Xb : Q) where
  qs : List Q
  hchain : qs.IsChain R
  hnodup : qs.Nodup
  hcover : ∀ X : Q, X ∈ qs
  hhead : qs.head? = some Xa
  hlast : qs.getLast? = some Xb

/-- Extract the RowQ quotient support list from Corollary 5.5 Hamilton-connectedness. -/
def quotient_ham_path_list {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hQnb : ¬ ∃ col : RowQ r s L B → Bool,
      IsProper2Coloring (rowQuotientGraph r s L B) col)
    (Xa Xb : RowQ r s L B) (hXaXb : Xa ≠ Xb) :
    QuotientHamPathList (quotientAdj (flipGraph r s) (rowProj hB)) Xa Xb := by
  classical
  have hQhc : IsHamConnected (rowQuotientGraph r s L B) :=
    rowQuotient_hamConnected r s L B hB (by
      intro hbip
      apply hQnb
      rcases hbip with ⟨col, hcol⟩
      exact ⟨col, by simpa [IsProper2Coloring] using hcol⟩)
  let p := Classical.choose (hQhc Xa Xb hXaXb)
  have hp : p.IsHamiltonian := Classical.choose_spec (hQhc Xa Xb hXaXb)
  refine
    { qs := p.support
      hchain := ?_
      hnodup := hp.isPath.support_nodup
      hcover := fun X => hp.mem_support X
      hhead := walk_support_head?_sec5 p
      hlast := walk_support_getLast?_sec5 p }
  exact p.isChain_adj_support.imp (fun {X Y} hXY =>
    (quotientAdj_rowProj_iff_rowQuotientAdj r s L B hB X Y).mpr hXY)

/-- Block 3b will prove the row interfaces needed to choose compatible terminal vertices. -/
theorem interchange_symm {m n : ℕ} {M N : ZeroOneMat m n} :
    Interchange M N → Interchange N M := by
  rintro ⟨i, i', j, j', hii, hjj, hMij, hMi'j', hMij', hMi'j,
    hNij, hNi'j', hNij', hNi'j, hout⟩
  refine ⟨i, i', j', j, hii, hjj.symm, hNij', hNi'j, hNij, hNi'j',
    hMij', hMi'j, hMij, hMi'j', ?_⟩
  intro a b hnot
  exact (hout a b (by
    intro hblock
    apply hnot
    rcases hblock with ⟨hrow, hcol⟩
    refine ⟨hrow, ?_⟩
    rcases hcol with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl)).symm

/-- The raw three-switch triangle behind the §5 alternate-interface argument. -/
theorem alternate_switch_triangle_core {m n : ℕ} {M : ZeroOneMat m n}
    {u v : Fin m} {i j c : Fin n}
    (huv : u ≠ v) (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (hui : M u i = true) (huj : M u j = true) (huc : M u c = false)
    (hvi : M v i = false) (hvj : M v j = false) (hvc : M v c = true) :
    Brualdi.Ryser.SwitchBlock M u v i c ∧
    Brualdi.Ryser.SwitchBlock M u v j c ∧
    Brualdi.Ryser.SwitchBlock (Brualdi.Ryser.switchMat M u v i c) u v j i ∧
    Brualdi.Ryser.switchMat M u v j c =
      Brualdi.Ryser.switchMat (Brualdi.Ryser.switchMat M u v i c) u v j i := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨huv, hic, hui, hvc, huc, hvi⟩
  · exact ⟨huv, hjc, huj, hvc, huc, hvj⟩
  · refine ⟨huv, hij.symm, ?_, ?_, ?_, ?_⟩
    · simp [Brualdi.Ryser.switchMat, huv, huv.symm, hij.symm, hjc, huj]
    · simp [Brualdi.Ryser.switchMat, huv.symm, hic]
    · simp [Brualdi.Ryser.switchMat]
    · simp [Brualdi.Ryser.switchMat, huv.symm, hij.symm, hjc, hvj]
  · funext a b
    simp only [Brualdi.Ryser.switchMat]
    split_ifs <;> simp_all

def Nested {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : Prop :=
  ∀ a, a ≠ L → M a j = true → M a i = true

def HasWitness {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : Prop :=
  ∃ a, a ≠ L ∧ M a i = false ∧ M a j = true

theorem nested_iff_not_hasWitness {m n : ℕ} {L : Fin (m + 1)} {i j : Fin n}
    {M : ZeroOneMat (m + 1) n} :
    Nested L i j M ↔ ¬ HasWitness L i j M := by
  classical
  constructor
  · intro h hW
    rcases hW with ⟨a, haL, hai, haj⟩
    have := h a haL haj
    rw [hai] at this
    exact Bool.false_ne_true this
  · intro h a haL haj
    by_cases hai : M a i = true
    · exact hai
    · have hfalse : M a i = false := by
        cases hcell : M a i <;> simp_all
      exact False.elim (h ⟨a, haL, hfalse, haj⟩)

private theorem rowSupport_eq_after_single_switch {m n : ℕ}
    {L a : Fin (m + 1)} {i j : Fin n} {M : ZeroOneMat (m + 1) n}
    {X Y : Finset (Fin n)}
    (hML : (Finset.univ.filter (fun b => M L b = true)) = X)
    (hXY : X \ Y = {i}) (hYX : Y \ X = {j})
    (haL : a ≠ L) :
    (Finset.univ.filter (fun b =>
      Brualdi.Ryser.switchMat M L a i j L b = true)) = Y := by
  classical
  ext b
  have hi_sdiff : i ∈ X \ Y := by rw [hXY]; simp
  have hj_sdiff : j ∈ Y \ X := by rw [hYX]; simp
  have hiY : i ∉ Y := (Finset.mem_sdiff.mp hi_sdiff).2
  have hjY : j ∈ Y := (Finset.mem_sdiff.mp hj_sdiff).1
  have hij : i ≠ j := by
    intro h
    exact hiY (by simpa [← h] using hjY)
  by_cases hbi : b = i
  · subst b
    simp [rowSupport, Brualdi.Ryser.switchMat, haL, hiY]
  · by_cases hbj : b = j
    · subst b
      simp [Brualdi.Ryser.switchMat, haL.symm, hij.symm, hjY]
    · have hiff : b ∈ X ↔ b ∈ Y := by
        constructor
        · intro hbX
          by_contra hbY
          have hb : b ∈ X \ Y := Finset.mem_sdiff.mpr ⟨hbX, hbY⟩
          have : b = i := by simpa [hXY] using hb
          exact hbi this
        · intro hbY
          by_contra hbX
          have hb : b ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hbY, hbX⟩
          have : b = j := by simpa [hYX] using hb
          exact hbj this
      have hrow : M L b = true ↔ b ∈ X := by
        constructor
        · intro hb
          have : b ∈ Finset.univ.filter (fun b => M L b = true) := by simp [hb]
          simpa [hML] using this
        · intro hb
          have : b ∈ Finset.univ.filter (fun b => M L b = true) := by simpa [hML] using hb
          exact (Finset.mem_filter.mp this).2
      simp [Brualdi.Ryser.switchMat, haL, hbi, hbj, hrow, hiff]


/-- **Lemma 5.3, exchange step (PROVED).** If patterns `A` and `B₀` of row `L` are both realizable
    and `e ∈ A \ B₀`, some `f ∈ B₀ \ A` gives a realizable pattern `A - e + f`. Proof: take
    realizations `(M, N)` minimizing the number of differing cells; local switch arguments force a
    closure property, and a counting argument over the difference cells yields a direct one-switch
    witness. (Independent of the manuscript's Gale–Ryser/deficiency proof.) -/
private theorem rowSupport_exchange {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    (L : Fin (m + 1)) {A B₀ : Finset (Fin n)} {e : Fin n}
    (hA : Nonempty {M : MarginClass r s // rowSupport L M = A})
    (hB : Nonempty {M : MarginClass r s // rowSupport L M = B₀})
    (heA : e ∈ A) (heB : e ∉ B₀) :
    ∃ f ∈ B₀, f ∉ A ∧
      Nonempty {M : MarginClass r s // rowSupport L M = insert f (A.erase e)} := by
  classical
  obtain ⟨pair, hpair_mem, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (MarginClass r s × MarginClass r s)).filter
      (fun MN => rowSupport L MN.1 = A ∧ rowSupport L MN.2 = B₀))
    (fun MN => diffCount MN.1.val MN.2.val)
    (by
      obtain ⟨MA⟩ := hA
      obtain ⟨MB⟩ := hB
      exact ⟨(MA.val, MB.val), by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨MA.property, MB.property⟩⟩)
  obtain ⟨hMA, hNB⟩ := (Finset.mem_filter.mp hpair_mem).2
  set M : MarginClass r s := pair.1 with hM_def
  set N : MarginClass r s := pair.2 with hN_def
  have hmin' : ∀ (M' N' : MarginClass r s), rowSupport L M' = A → rowSupport L N' = B₀ →
      diffCount M.val N.val ≤ diffCount M'.val N'.val := by
    intro M' N' h1 h2
    exact hmin (M', N') (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1, h2⟩)
  have hMmem : ∀ b : Fin n, M.val L b = true ↔ b ∈ A := by
    intro b
    rw [← hMA]
    simp [rowSupport]
  have hNmem : ∀ b : Fin n, N.val L b = true ↔ b ∈ B₀ := by
    intro b
    rw [← hNB]
    simp [rowSupport]
  have hMLe : M.val L e = true := (hMmem e).mpr heA
  have hNLe : N.val L e = false := by
    cases h : N.val L e
    · rfl
    · exact absurd ((hNmem e).mp h) heB
  set S : Finset (Fin (m + 1)) := (Finset.univ.erase L).filter
    (fun a => M.val a e = false ∧ N.val a e = true) with hS_def
  have hS_mem : ∀ a, a ∈ S ↔ a ≠ L ∧ M.val a e = false ∧ N.val a e = true := by
    intro a
    simp [hS_def]
  have hS_ne : S.Nonempty := by
    have hbal := pq_col_balance (M := M.val) (N := N.val) (c := e)
      (by rw [M.property.2 e, N.property.2 e]) L
    rw [if_pos hMLe, if_neg (by rw [hNLe]; decide)] at hbal
    have hpos : 0 < ((Finset.univ.erase L).filter
        (fun a => M.val a e = false ∧ N.val a e = true)).card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨a, by rw [hS_def]; exact ha⟩
  by_cases hterm : ∃ a ∈ S, ∃ c, M.val a c = true ∧ N.val a c = false ∧
      M.val L c = false ∧ N.val L c = true
  · -- termination: a single switch realizes the exchange
    obtain ⟨a, haS, c, hMac, hNac, hMLc, hNLc⟩ := hterm
    obtain ⟨haL, haMe, _haNe⟩ := (hS_mem a).mp haS
    have hec : e ≠ c := by
      intro h
      rw [← h, hMLe] at hMLc
      cases hMLc
    have hblock : Brualdi.Ryser.SwitchBlock M.val L a e c :=
      ⟨Ne.symm haL, hec, hMLe, hMac, hMLc, haMe⟩
    have hM'_margins : HasMargins r s (Brualdi.Ryser.switchMat M.val L a e c) :=
      Brualdi.Ryser.interchange_preserves_margins (Brualdi.Ryser.switch_interchange hblock) M.property
    have hcA : c ∉ A := by
      intro hcA
      rw [(hMmem c).mpr hcA] at hMLc
      cases hMLc
    have hXY : A \ insert c (A.erase e) = {e} := by
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hbA, hb⟩
        by_contra hbe
        exact hb (Or.inr ⟨hbe, hbA⟩)
      · rintro rfl
        refine ⟨heA, ?_⟩
        rintro (rfl | ⟨hee, -⟩)
        · exact hcA heA
        · exact hee rfl
    have hYX : insert c (A.erase e) \ A = {c} := by
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hbc | ⟨-, hbA⟩, hnbA⟩
        · exact hbc
        · exact absurd hbA hnbA
      · rintro rfl
        exact ⟨Or.inl rfl, hcA⟩
    have hsup : rowSupport L (⟨Brualdi.Ryser.switchMat M.val L a e c, hM'_margins⟩ :
        MarginClass r s) = insert c (A.erase e) := by
      unfold rowSupport
      exact rowSupport_eq_after_single_switch (M := M.val) hMA hXY hYX haL
    exact ⟨c, (hNmem c).mp hNLc, hcA, ⟨⟨_, hsup⟩⟩⟩
  · -- no termination: derive a contradiction by closure + counting
    exfalso
    have hterm' : ∀ a ∈ S, ∀ c, M.val a c = true → N.val a c = false →
        M.val L c = false → N.val L c = false := by
      intro a ha c h1 h2 h3
      cases h : N.val L c
      · rfl
      · exact absurd ⟨a, ha, c, h1, h2, h3, h⟩ hterm
    set T : Finset (Fin n) := Finset.univ.filter
      (fun c => ∃ a ∈ S, M.val a c = true ∧ N.val a c = false) with hT_def
    have hT_mem : ∀ c, c ∈ T ↔ ∃ a ∈ S, M.val a c = true ∧ N.val a c = false := by
      intro c
      simp [hT_def]
    have heT : e ∉ T := by
      rw [hT_mem]
      rintro ⟨a, haS, hMae, -⟩
      rw [((hS_mem a).mp haS).2.1] at hMae
      cases hMae
    -- Closure 1: a Q-cell in a T-column has N-value true at e
    have hclose1 : ∀ c ∈ T, ∀ x, x ≠ L → M.val x c = false → N.val x c = true →
        N.val x e = true := by
      intro c hcT x hxL hMxc hNxc
      obtain ⟨a, haS, hMac, hNac⟩ := (hT_mem c).mp hcT
      obtain ⟨haL, haMe, haNe⟩ := (hS_mem a).mp haS
      by_contra hne
      have hNxe : N.val x e = false := by
        cases h : N.val x e
        · rfl
        · exact absurd h hne
      have hax : a ≠ x := by
        intro h
        rw [h, hMxc] at hMac
        cases hMac
      have hec : e ≠ c := by
        intro h
        rw [← h, haMe] at hMac
        cases hMac
      have hblockN : Brualdi.Ryser.SwitchBlock N.val a x e c :=
        ⟨hax, hec, haNe, hNxc, hNac, hNxe⟩
      have hN₂m : HasMargins r s (Brualdi.Ryser.switchMat N.val a x e c) :=
        Brualdi.Ryser.interchange_preserves_margins (Brualdi.Ryser.switch_interchange hblockN) N.property
      have hN₂sup : rowSupport L (⟨Brualdi.Ryser.switchMat N.val a x e c, hN₂m⟩ :
          MarginClass r s) = B₀ := by
        rw [← hNB]
        unfold rowSupport
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [switchMat_row_untouched N.val a x e c (Ne.symm haL) (Ne.symm hxL) b]
      have hdiffs : 3 ≤ ((blockCells a x e c).filter
          (fun y => N.val y.1 y.2 ≠ M.val y.1 y.2)).card := by
        have hsub : ({(a, e), (a, c), (x, c)} : Finset (Fin (m + 1) × Fin n))
            ⊆ (blockCells a x e c).filter (fun y => N.val y.1 y.2 ≠ M.val y.1 y.2) := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inl rfl),
              by rw [haNe, haMe]; decide⟩
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inl rfl)),
              by rw [hNac, hMac]; decide⟩
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inr (Or.inr rfl))),
              by rw [hNxc, hMxc]; decide⟩
        have hcard3 : ({(a, e), (a, c), (x, c)} : Finset (Fin (m + 1) × Fin n)).card = 3 := by
          have h1 : ((a, e) : Fin (m + 1) × Fin n) ≠ (a, c) := fun h => hec (congrArg Prod.snd h)
          have h2 : ((a, e) : Fin (m + 1) × Fin n) ≠ (x, c) := fun h => hax (congrArg Prod.fst h)
          have h3 : ((a, c) : Fin (m + 1) × Fin n) ≠ (x, c) := fun h => hax (congrArg Prod.fst h)
          simp [h1, h2, h3]
        calc 3 = ({(a, e), (a, c), (x, c)} : Finset (Fin (m + 1) × Fin n)).card := hcard3.symm
          _ ≤ _ := Finset.card_le_card hsub
      have hlt : diffCount (Brualdi.Ryser.switchMat N.val a x e c) M.val
          < diffCount N.val M.val :=
        diffCount_switch_lt hblockN hdiffs
      have hge : diffCount M.val N.val
          ≤ diffCount M.val (Brualdi.Ryser.switchMat N.val a x e c) :=
        hmin' M ⟨Brualdi.Ryser.switchMat N.val a x e c, hN₂m⟩ hMA hN₂sup
      have h1 := diffCount_comm M.val N.val
      have h2 := diffCount_comm M.val (Brualdi.Ryser.switchMat N.val a x e c)
      omega
    -- Closure 2: a Q-cell in a T-column has M-value false at e
    have hclose2 : ∀ c ∈ T, ∀ x, x ≠ L → M.val x c = false → N.val x c = true →
        M.val x e = false := by
      intro c hcT x hxL hMxc hNxc
      obtain ⟨a, haS, hMac, hNac⟩ := (hT_mem c).mp hcT
      obtain ⟨haL, haMe, haNe⟩ := (hS_mem a).mp haS
      by_contra hne
      have hMxe : M.val x e = true := by
        cases h : M.val x e
        · exact absurd h hne
        · rfl
      have hNxe : N.val x e = true := hclose1 c hcT x hxL hMxc hNxc
      have hax : a ≠ x := by
        intro h
        rw [h, hMxc] at hMac
        cases hMac
      have hec : e ≠ c := by
        intro h
        rw [← h, haMe] at hMac
        cases hMac
      have hblockM : Brualdi.Ryser.SwitchBlock M.val a x c e :=
        ⟨hax, Ne.symm hec, hMac, hMxe, haMe, hMxc⟩
      have hM₂m : HasMargins r s (Brualdi.Ryser.switchMat M.val a x c e) :=
        Brualdi.Ryser.interchange_preserves_margins (Brualdi.Ryser.switch_interchange hblockM) M.property
      have hM₂sup : rowSupport L (⟨Brualdi.Ryser.switchMat M.val a x c e, hM₂m⟩ :
          MarginClass r s) = A := by
        rw [← hMA]
        unfold rowSupport
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [switchMat_row_untouched M.val a x c e (Ne.symm haL) (Ne.symm hxL) b]
      have hdiffs : 3 ≤ ((blockCells a x c e).filter
          (fun y => M.val y.1 y.2 ≠ N.val y.1 y.2)).card := by
        have hsub : ({(a, c), (a, e), (x, c)} : Finset (Fin (m + 1) × Fin n))
            ⊆ (blockCells a x c e).filter (fun y => M.val y.1 y.2 ≠ N.val y.1 y.2) := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inl rfl),
              by rw [hMac, hNac]; decide⟩
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inl rfl)),
              by rw [haMe, haNe]; decide⟩
          · exact Finset.mem_filter.mpr ⟨mem_blockCells.mpr (Or.inr (Or.inr (Or.inl rfl))),
              by rw [hMxc, hNxc]; decide⟩
        have hcard3 : ({(a, c), (a, e), (x, c)} : Finset (Fin (m + 1) × Fin n)).card = 3 := by
          have h1 : ((a, c) : Fin (m + 1) × Fin n) ≠ (a, e) := fun h => hec ((congrArg Prod.snd h).symm)
          have h2 : ((a, c) : Fin (m + 1) × Fin n) ≠ (x, c) := fun h => hax (congrArg Prod.fst h)
          have h3 : ((a, e) : Fin (m + 1) × Fin n) ≠ (x, c) := fun h => hax (congrArg Prod.fst h)
          simp [h1, h2, h3]
        calc 3 = ({(a, c), (a, e), (x, c)} : Finset (Fin (m + 1) × Fin n)).card := hcard3.symm
          _ ≤ _ := Finset.card_le_card hsub
      have hlt : diffCount (Brualdi.Ryser.switchMat M.val a x c e) N.val
          < diffCount M.val N.val :=
        diffCount_switch_lt hblockM hdiffs
      have hge : diffCount M.val N.val
          ≤ diffCount (Brualdi.Ryser.switchMat M.val a x c e) N.val :=
        hmin' ⟨Brualdi.Ryser.switchMat M.val a x c e, hM₂m⟩ N hM₂sup hNB
      omega
    -- the counting contradiction
    have hswapP := sum_card_filter_comm S T
      (fun a c => M.val a c = true ∧ N.val a c = false)
    have hswapQ := sum_card_filter_comm S T
      (fun a c => M.val a c = false ∧ N.val a c = true)
    have hrow_eq : ∀ a ∈ S,
        (T.filter (fun c => M.val a c = true ∧ N.val a c = false)).card
          = ((Finset.univ : Finset (Fin n)).filter
              (fun c => M.val a c = true ∧ N.val a c = false)).card := by
      intro a haS
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT_mem]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨h1, h2⟩
        exact ⟨⟨a, haS, h1, h2⟩, h1, h2⟩
    have hrow_bal : ∀ a ∈ S,
        ((Finset.univ : Finset (Fin n)).filter
            (fun c => M.val a c = true ∧ N.val a c = false)).card
          = ((Finset.univ : Finset (Fin n)).filter
              (fun c => M.val a c = false ∧ N.val a c = true)).card := by
      intro a _
      exact pq_row_balance (by rw [M.property.1 a, N.property.1 a])
    have hrow_ge : ∀ a ∈ S,
        (T.filter (fun c => M.val a c = false ∧ N.val a c = true)).card + 1
          ≤ ((Finset.univ : Finset (Fin n)).filter
              (fun c => M.val a c = false ∧ N.val a c = true)).card := by
      intro a haS
      obtain ⟨-, haMe, haNe⟩ := (hS_mem a).mp haS
      have he_mem : e ∈ (Finset.univ : Finset (Fin n)).filter
          (fun c => M.val a c = false ∧ N.val a c = true) := by
        simp [haMe, haNe]
      have he_not : e ∉ T.filter (fun c => M.val a c = false ∧ N.val a c = true) :=
        fun h => heT (Finset.mem_filter.mp h).1
      have hsub : insert e (T.filter (fun c => M.val a c = false ∧ N.val a c = true))
          ⊆ (Finset.univ : Finset (Fin n)).filter
              (fun c => M.val a c = false ∧ N.val a c = true) := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact he_mem
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      calc (T.filter (fun c => M.val a c = false ∧ N.val a c = true)).card + 1
          = (insert e (T.filter (fun c => M.val a c = false ∧ N.val a c = true))).card :=
            (Finset.card_insert_of_notMem he_not).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hcol_le : ∀ c ∈ T,
        (S.filter (fun a => M.val a c = true ∧ N.val a c = false)).card
          ≤ (S.filter (fun a => M.val a c = false ∧ N.val a c = true)).card := by
      intro c hcT
      have hPsub : S.filter (fun a => M.val a c = true ∧ N.val a c = false)
          ⊆ (Finset.univ.erase L).filter (fun a => M.val a c = true ∧ N.val a c = false) := by
        intro x hx
        obtain ⟨hxS, hpred⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨((hS_mem x).mp hxS).1, Finset.mem_univ _⟩, hpred⟩
      have hQeq : S.filter (fun a => M.val a c = false ∧ N.val a c = true)
          = (Finset.univ.erase L).filter (fun a => M.val a c = false ∧ N.val a c = true) := by
        ext x
        constructor
        · intro hx
          obtain ⟨hxS, hpred⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
            ⟨((hS_mem x).mp hxS).1, Finset.mem_univ _⟩, hpred⟩
        · intro hx
          obtain ⟨hxE, hpred⟩ := Finset.mem_filter.mp hx
          have hxL : x ≠ L := (Finset.mem_erase.mp hxE).1
          exact Finset.mem_filter.mpr
            ⟨(hS_mem x).mpr ⟨hxL, hclose2 c hcT x hxL hpred.1 hpred.2,
              hclose1 c hcT x hxL hpred.1 hpred.2⟩, hpred⟩
      have hbal := pq_col_balance (M := M.val) (N := N.val) (c := c)
        (by rw [M.property.2 c, N.property.2 c]) L
      obtain ⟨a, haS, hMac, hNac⟩ := (hT_mem c).mp hcT
      have hPle : (S.filter (fun a => M.val a c = true ∧ N.val a c = false)).card
          ≤ ((Finset.univ.erase L).filter
              (fun a => M.val a c = true ∧ N.val a c = false)).card :=
        Finset.card_le_card hPsub
      rw [hQeq]
      cases hMLc : M.val L c with
      | true =>
          rw [if_pos hMLc] at hbal
          cases hNLc : N.val L c with
          | true => rw [if_pos hNLc] at hbal; omega
          | false => rw [if_neg (by rw [hNLc]; decide)] at hbal; omega
      | false =>
          have hNLc : N.val L c = false := hterm' a haS c hMac hNac hMLc
          rw [if_neg (by rw [hMLc]; decide), if_neg (by rw [hNLc]; decide)] at hbal
          omega
    -- assemble: Σ_S |T-Q| + |S| ≤ Σ_S |univ-Q| = Σ_S |univ-P| = Σ_S |T-P| = Σ_T |S-P|
    --           ≤ Σ_T |S-Q| = Σ_S |T-Q|  ⇒  |S| ≤ 0, contradiction
    have hsum_ge : (∑ a ∈ S, (T.filter (fun c => M.val a c = false ∧ N.val a c = true)).card)
        + S.card
        ≤ ∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
            (fun c => M.val a c = false ∧ N.val a c = true)).card := by
      calc (∑ a ∈ S, (T.filter (fun c => M.val a c = false ∧ N.val a c = true)).card) + S.card
          = ∑ a ∈ S, ((T.filter (fun c => M.val a c = false ∧ N.val a c = true)).card + 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum hrow_ge
    have hsum_eq1 : (∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
          (fun c => M.val a c = false ∧ N.val a c = true)).card)
        = ∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
            (fun c => M.val a c = true ∧ N.val a c = false)).card :=
      Finset.sum_congr rfl (fun a ha => (hrow_bal a ha).symm)
    have hsum_eq2 : (∑ a ∈ S, ((Finset.univ : Finset (Fin n)).filter
          (fun c => M.val a c = true ∧ N.val a c = false)).card)
        = ∑ a ∈ S, (T.filter (fun c => M.val a c = true ∧ N.val a c = false)).card :=
      Finset.sum_congr rfl (fun a ha => (hrow_eq a ha).symm)
    have hsum_le : (∑ c ∈ T, (S.filter (fun a => M.val a c = true ∧ N.val a c = false)).card)
        ≤ ∑ c ∈ T, (S.filter (fun a => M.val a c = false ∧ N.val a c = true)).card :=
      Finset.sum_le_sum hcol_le
    have hS_pos : 0 < S.card := Finset.card_pos.mpr hS_ne
    omega


/-- The exchange step, the paper's way: deficient sets are closed under intersection, their
    total intersection `Z` is deficient, and `B`'s feasibility on `Z` produces the element to
    swap in. -/
private theorem alt_exchange_GR {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} (hne : Nonempty (MarginClass r s)) {A B : Finset (Fin n)} {e : Fin n}
    (hA : Nonempty {M : MarginClass r s // rowSupport L M = A})
    (hB : Nonempty {M : MarginClass r s // rowSupport L M = B})
    (heA : e ∈ A) (heB : e ∉ B) :
    ∃ f ∈ B, f ∉ A ∧ Nonempty {M : MarginClass r s // rowSupport L M = insert f (A.erase e)} := by
  classical
  have hAfeas := altFeas_of_realizable hA
  have hBfeas := altFeas_of_realizable hB
  obtain ⟨M₀⟩ := hne
  have htot : ∑ j, s j = r L + ∑ t : Fin m, r (L.succAbove t) := by
    have h1 : ∑ j, s j = ∑ j, colSum M₀.val j :=
      Finset.sum_congr rfl (fun j _ => (M₀.property.2 j).symm)
    have h2 : ∑ j : Fin n, colSum M₀.val j = ∑ i : Fin (m + 1), rowSum M₀.val i := by
      unfold colSum rowSum
      exact Finset.sum_comm
    have h3 : ∑ i : Fin (m + 1), rowSum M₀.val i = ∑ i : Fin (m + 1), r i :=
      Finset.sum_congr rfl (fun i _ => M₀.property.1 i)
    have h4 := Fin.sum_univ_succAbove (fun i : Fin (m + 1) => r i) L
    omega
  have hrn : ∀ t : Fin m, r (L.succAbove t) ≤ n := by
    intro t
    rw [← M₀.property.1 (L.succAbove t)]
    exact alt_rowSum_le M₀.val (L.succAbove t)
  set A₀ : Finset (Fin n) := A.erase e with hA₀def
  have hA₀card : A₀.card + 1 = A.card := Finset.card_erase_add_one heA
  have heA₀ : e ∉ A₀ := Finset.notMem_erase e A
  -- deficient sets
  set Def : Finset (Fin n) → Prop :=
    fun X => (A₀ ∩ X).card + altH (m := m) (n := n) r L X.card < ∑ j ∈ X, s j with hDefdef
  -- a deficient set contains e, and its deficiency is exactly one
  have hAX : ∀ X : Finset (Fin n), e ∈ X → (A ∩ X).card = (A₀ ∩ X).card + 1 := by
    intro X heX
    have hsub : A₀ ∩ X = (A ∩ X).erase e := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_erase, hA₀def]
      tauto
    have heAX : e ∈ A ∩ X := Finset.mem_inter.mpr ⟨heA, heX⟩
    rw [hsub]
    exact (Finset.card_erase_add_one heAX).symm
  have hdef_e : ∀ X : Finset (Fin n), Def X →
      e ∈ X ∧ ∑ j ∈ X, s j = (A₀ ∩ X).card + 1 + altH (m := m) (n := n) r L X.card := by
    intro X hX
    have heX : e ∈ X := by
      by_contra heX
      have hsame : A₀ ∩ X = A ∩ X := by
        ext b
        simp only [Finset.mem_inter, Finset.mem_erase, hA₀def]
        constructor
        · rintro ⟨⟨_, hb⟩, hbX⟩
          exact ⟨hb, hbX⟩
        · rintro ⟨hbA, hbX⟩
          exact ⟨⟨fun h => heX (h ▸ hbX), hbA⟩, hbX⟩
      have := hAfeas.2 X
      have hX' : (A₀ ∩ X).card + altH (m := m) (n := n) r L X.card < ∑ j ∈ X, s j := hX
      rw [hsame] at hX'
      omega
    refine ⟨heX, ?_⟩
    have h1 := hAfeas.2 X
    have h2 := hAX X heX
    have hX' : (A₀ ∩ X).card + altH (m := m) (n := n) r L X.card < ∑ j ∈ X, s j := hX
    omega
  -- deficient sets are closed under intersection
  have hdef_inter : ∀ X Y : Finset (Fin n), Def X → Def Y → Def (X ∩ Y) := by
    intro X Y hX hY
    obtain ⟨heX, hEX⟩ := hdef_e X hX
    obtain ⟨heY, hEY⟩ := hdef_e Y hY
    -- feasibility on the union, relaxed to A₀
    have hAU : (A ∩ (X ∪ Y)).card ≤ (A₀ ∩ (X ∪ Y)).card + 1 := by
      have h := hAX (X ∪ Y) (Finset.mem_union_left Y heX)
      omega
    have hUfeas : ∑ j ∈ X ∪ Y, s j ≤
        (A₀ ∩ (X ∪ Y)).card + 1 + altH (m := m) (n := n) r L (X ∪ Y).card := by
      have := hAfeas.2 (X ∪ Y)
      omega
    -- modularity of the column mass
    have hsum_mod : ∑ j ∈ X ∪ Y, s j + ∑ j ∈ X ∩ Y, s j = ∑ j ∈ X, s j + ∑ j ∈ Y, s j :=
      Finset.sum_union_inter
    -- modularity of the A₀ trace
    have hU : (A₀ ∩ X) ∪ (A₀ ∩ Y) = A₀ ∩ (X ∪ Y) := by
      ext b
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have hI : (A₀ ∩ X) ∩ (A₀ ∩ Y) = A₀ ∩ (X ∩ Y) := by
      ext b
      simp only [Finset.mem_inter]
      tauto
    have hcard_mod : (A₀ ∩ (X ∪ Y)).card + (A₀ ∩ (X ∩ Y)).card =
        (A₀ ∩ X).card + (A₀ ∩ Y).card := by
      have := Finset.card_union_add_card_inter (A₀ ∩ X) (A₀ ∩ Y)
      rw [hU, hI] at this
      exact this
    -- supermodularity of h at the four cardinalities
    have hcXY := Finset.card_union_add_card_inter X Y
    have hsuper := altH_supermod (m := m) (n := n) r L
      (Finset.card_le_card (Finset.inter_subset_left (s₂ := Y)))
      (Finset.card_le_card (Finset.subset_union_left (s₂ := Y)))
      (by omega : X.card + Y.card = (X ∩ Y).card + (X ∪ Y).card)
    have hXd : (A₀ ∩ X).card + altH (m := m) (n := n) r L X.card < ∑ j ∈ X, s j := hX
    have hYd : (A₀ ∩ Y).card + altH (m := m) (n := n) r L Y.card < ∑ j ∈ Y, s j := hY
    show (A₀ ∩ (X ∩ Y)).card + altH (m := m) (n := n) r L (X ∩ Y).card < ∑ j ∈ X ∩ Y, s j
    omega
  -- the ground set is deficient
  have hdef_univ : Def Finset.univ := by
    have hHn : altH (m := m) (n := n) r L (Finset.univ : Finset (Fin n)).card =
        ∑ t : Fin m, r (L.succAbove t) := by
      unfold altH
      refine Finset.sum_congr rfl ?_
      intro t _
      have := hrn t
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hAuniv : A₀ ∩ Finset.univ = A₀ := by simp
    have hk := hAfeas.1
    have hkpos : 1 ≤ A.card := Finset.card_pos.mpr ⟨e, heA⟩
    show (A₀ ∩ Finset.univ).card +
        altH (m := m) (n := n) r L (Finset.univ : Finset (Fin n)).card <
      ∑ j ∈ (Finset.univ : Finset (Fin n)), s j
    rw [hAuniv, hHn]
    omega
  -- Z: the intersection of all deficient sets
  set D : Finset (Finset (Fin n)) := Finset.univ.filter Def with hDdef
  have hDne : D.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdef_univ⟩⟩
  have hinf : ∀ (F : Finset (Finset (Fin n))) (hF : F.Nonempty),
      (∀ X ∈ F, Def X) → Def (F.inf id) := by
    intro F hF
    induction hF using Finset.Nonempty.cons_induction with
    | singleton X =>
        intro h
        simpa using h X (Finset.mem_singleton_self X)
    | cons X F hXF hFne ih =>
        intro h
        rw [Finset.inf_cons]
        have h1 : Def X := h X (Finset.mem_cons_self X F)
        have h2 : Def (F.inf id) := ih (fun Y hY => h Y (Finset.mem_cons_of_mem hY))
        have := hdef_inter X (F.inf id) h1 h2
        simpa [Finset.inf_eq_inter, id] using this
  set Z : Finset (Fin n) := D.inf id with hZdef
  have hZDef : Def Z := hinf D hDne (fun X hX => (Finset.mem_filter.mp hX).2)
  have hZsub : ∀ X : Finset (Fin n), Def X → Z ⊆ X := by
    intro X hX
    have h : Z ≤ id X :=
      Finset.inf_le (f := (id : Finset (Fin n) → Finset (Fin n)))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ X, hX⟩)
    simpa using h
  -- B's feasibility on Z yields the incoming element f
  obtain ⟨heZ, hZeq⟩ := hdef_e Z hZDef
  have hBZ := hBfeas.2 Z
  have hcardlt : (A₀ ∩ Z).card < (B ∩ Z).card := by omega
  obtain ⟨f, hfBZ, hfA₀Z⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hfB : f ∈ B := (Finset.mem_inter.mp hfBZ).1
  have hfZ : f ∈ Z := (Finset.mem_inter.mp hfBZ).2
  have hfA₀ : f ∉ A₀ := fun h => hfA₀Z (Finset.mem_inter.mpr ⟨h, hfZ⟩)
  have hfe : f ≠ e := fun h => heB (h ▸ hfB)
  have hfA : f ∉ A := by
    intro h
    exact hfA₀ (Finset.mem_erase.mpr ⟨hfe, h⟩)
  -- the exchanged pattern is feasible, hence realizable
  set A' : Finset (Fin n) := insert f A₀ with hA'def
  have hA'feas : altFeas r s L A' := by
    constructor
    · rw [hA'def, Finset.card_insert_of_notMem hfA₀]
      have hk := hAfeas.1
      omega
    · intro X
      by_cases hX : Def X
      · obtain ⟨heX, hEX⟩ := hdef_e X hX
        have hfX : f ∈ X := hZsub X hX hfZ
        have hins : A' ∩ X = insert f (A₀ ∩ X) := by
          ext b
          simp only [Finset.mem_inter, Finset.mem_insert, hA'def]
          constructor
          · rintro ⟨hb | hb, hbX⟩
            · exact Or.inl hb
            · exact Or.inr ⟨hb, hbX⟩
          · rintro (rfl | ⟨hb, hbX⟩)
            · exact ⟨Or.inl rfl, hfX⟩
            · exact ⟨Or.inr hb, hbX⟩
        have hfnotin : f ∉ A₀ ∩ X := fun h => hfA₀ (Finset.mem_inter.mp h).1
        have hcard' : (A' ∩ X).card = (A₀ ∩ X).card + 1 := by
          rw [hins, Finset.card_insert_of_notMem hfnotin]
        omega
      · have hle : (A₀ ∩ X).card ≤ (A' ∩ X).card :=
          Finset.card_le_card (fun b hb => by
            have := Finset.mem_inter.mp hb
            exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem this.1, this.2⟩)
        have hX' : ¬((A₀ ∩ X).card + altH (m := m) (n := n) r L X.card < ∑ j ∈ X, s j) := hX
        omega
  exact ⟨f, hfB, hfA, alt_realizable_of_feas ⟨M₀⟩ hA'feas⟩

/-- **Manuscript Lemma 5.3 — PROVED, the paper's way**: the realizable patterns of a single
    line `L` form the bases of a matroid on the columns. `exists_base` from nonemptiness; the
    exchange axiom by the PAPER's printed argument — the Gale-Ryser characterization
    (`galeRyser_exists`, self-contained) plus the deficient-set/supermodularity exchange
    (`alt_exchange_GR`). The development's original minimal-pair route is kept as
    `rowPattern_baseFamily_minpair` (deliberate two-proof redundancy). -/
theorem rowPattern_baseFamily {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    (hne : Nonempty (MarginClass r s)) :
    ∃ B : BaseFamily (Fin n), ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s //
        (Finset.univ.filter (fun b => M.val L b = true)) = p} := by
  classical
  refine ⟨{ Base := fun p => Nonempty {M : MarginClass r s // rowSupport L M = p}
            exists_base := ?_
            exchange := ?_ }, fun p => Iff.rfl⟩
  · obtain ⟨M⟩ := hne
    exact ⟨rowSupport L M, ⟨M, rfl⟩⟩
  · intro A B e hA hB heA heB
    obtain ⟨f, hfB, hfA, hreal⟩ := alt_exchange_GR hne hA hB heA heB
    exact ⟨f, hfB, hfA, hreal⟩

/-- **ALTERNATE proof of Lemma 5.3** (the development's original route): exchange via the
    self-contained minimal-pair/counting argument `rowSupport_exchange`, independent of the
    paper's Gale-Ryser/deficiency proof (which is now the mainline `rowPattern_baseFamily`).
    Kept so both proofs stay machine-checked. -/
theorem rowPattern_baseFamily_minpair {m n : ℕ} (r : Fin (m+1) → ℕ) (s : Fin n → ℕ) (L : Fin (m+1))
    (hne : Nonempty (MarginClass r s)) :
    ∃ B : BaseFamily (Fin n), ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s //
        (Finset.univ.filter (fun b => M.val L b = true)) = p} := by
  classical
  refine ⟨{ Base := fun p => Nonempty {M : MarginClass r s // rowSupport L M = p}
            exists_base := ?_
            exchange := ?_ }, fun p => Iff.rfl⟩
  · obtain ⟨M⟩ := hne
    exact ⟨rowSupport L M, ⟨M, rfl⟩⟩
  · intro A B e hA hB heA heB
    exact rowSupport_exchange L hA hB heA heB

private theorem hasWitness_of_interchange_row_flip {m n : ℕ}
    {M N : ZeroOneMat (m + 1) n} {L : Fin (m + 1)} {i j : Fin n}
    (hMLi : M L i = true) (hMLj : M L j = false)
    (hNLi : N L i = false) (hNLj : N L j = true)
    (hint : Interchange M N) :
    HasWitness L i j M := by
  classical
  rcases hint with
    ⟨r₁, r₂, c₁, c₂, hr, hc, hM11, hM22, hM12, hM21,
      hN11, hN22, hN12, hN21, hout⟩
  have hrow : L = r₁ ∨ L = r₂ := by
    by_contra h
    push_neg at h
    have hsame : N L i = M L i := hout L i (by
      intro hb
      exact hb.1.elim h.1 h.2)
    rw [hNLi, hMLi] at hsame
    exact Bool.false_ne_true hsame
  rcases hrow with hL | hL
  · subst L
    have hic₁ : i = c₁ := by
      by_cases hi1 : i = c₁
      · exact hi1
      · by_cases hi2 : i = c₂
        · subst i
          rw [hM12] at hMLi
          exact False.elim (Bool.false_ne_true hMLi)
        · have hsame : N r₁ i = M r₁ i := hout r₁ i (by
            intro hb
            exact hb.2.elim hi1 hi2)
          rw [hNLi, hMLi] at hsame
          exact False.elim (Bool.false_ne_true hsame)
    have hjc₂ : j = c₂ := by
      by_cases hj2 : j = c₂
      · exact hj2
      · by_cases hj1 : j = c₁
        · subst j
          rw [hM11] at hMLj
          exact False.elim (Bool.false_ne_true hMLj.symm)
        · have hsame : N r₁ j = M r₁ j := hout r₁ j (by
            intro hb
            exact hb.2.elim hj1 hj2)
          rw [hNLj, hMLj] at hsame
          exact False.elim (Bool.false_ne_true hsame.symm)
    refine ⟨r₂, hr.symm, ?_, ?_⟩
    · simpa [hic₁] using hM21
    · simpa [hjc₂] using hM22
  · subst L
    have hic₂ : i = c₂ := by
      by_cases hi2 : i = c₂
      · exact hi2
      · by_cases hi1 : i = c₁
        · subst i
          rw [hM21] at hMLi
          exact False.elim (Bool.false_ne_true hMLi)
        · have hsame : N r₂ i = M r₂ i := hout r₂ i (by
            intro hb
            exact hb.2.elim hi1 hi2)
          rw [hNLi, hMLi] at hsame
          exact False.elim (Bool.false_ne_true hsame)
    have hjc₁ : j = c₁ := by
      by_cases hj1 : j = c₁
      · exact hj1
      · by_cases hj2 : j = c₂
        · subst j
          rw [hM22] at hMLj
          exact False.elim (Bool.false_ne_true hMLj.symm)
        · have hsame : N r₂ j = M r₂ j := hout r₂ j (by
            intro hb
            exact hb.2.elim hj1 hj2)
          rw [hNLj, hMLj] at hsame
          exact False.elim (Bool.false_ne_true hsame.symm)
    refine ⟨r₁, hr, ?_, ?_⟩
    · simpa [hic₂] using hM12
    · simpa [hjc₁] using hM11

theorem row_interface_iff_hasWitness {m n : ℕ}
    (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ) (L : Fin (m + 1))
    (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B} {i j : Fin n}
    (hXY : X.val \ Y.val = {i}) (hYX : Y.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X}) :
    M.val ∈ interface (flipGraph r s) (rowProj hB) X Y ↔
      HasWitness L i j M.val.val := by
  classical
  constructor
  · intro hmem
    rcases (mem_interface_iff.mp hmem).2 with ⟨N, hNfib, hadj⟩
    have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
    have hNY : rowSupport L N = Y.val := by
      have hproj : rowProj hB N = Y := (Finset.mem_filter.mp hNfib).2
      exact congrArg Subtype.val hproj
    have hMLi : M.val.val L i = true := by
      have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
      have hiX : i ∈ X.val := (Finset.mem_sdiff.mp hi).1
      have hiRow : i ∈ rowSupport L M.val := by simpa [hMX] using hiX
      simpa [rowSupport] using (Finset.mem_filter.mp hiRow).2
    have hMLj : M.val.val L j = false := by
      have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
      have hjX : j ∉ X.val := (Finset.mem_sdiff.mp hj).2
      have hjRow : j ∉ rowSupport L M.val := by simpa [hMX] using hjX
      cases hcell : M.val.val L j
      · rfl
      · exact False.elim (hjRow (by simp [rowSupport, hcell]))
    have hNLi : N.val L i = false := by
      have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
      have hiY : i ∉ Y.val := (Finset.mem_sdiff.mp hi).2
      have hiRow : i ∉ rowSupport L N := by simpa [hNY] using hiY
      cases hcell : N.val L i
      · rfl
      · exact False.elim (hiRow (by simp [rowSupport, hcell]))
    have hNLj : N.val L j = true := by
      have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
      have hjY : j ∈ Y.val := (Finset.mem_sdiff.mp hj).1
      have hjRow : j ∈ rowSupport L N := by simpa [hNY] using hjY
      simpa [rowSupport] using (Finset.mem_filter.mp hjRow).2
    rw [flipGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_hne, hint | hint⟩
    · exact hasWitness_of_interchange_row_flip hMLi hMLj hNLi hNLj hint
    · exact hasWitness_of_interchange_row_flip hMLi hMLj hNLi hNLj (interchange_symm hint)
  · rintro ⟨a, haL, hai, haj⟩
    have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
    let hb : Brualdi.Ryser.SwitchBlock M.val.val L a i j := by
      refine ⟨haL.symm, ?_, ?_, haj, ?_, hai⟩
      · have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
        have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
        exact fun hij => (Finset.mem_sdiff.mp hi).2 (by simpa [hij] using
          (Finset.mem_sdiff.mp hj).1)
      · have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
        have hiX : i ∈ X.val := (Finset.mem_sdiff.mp hi).1
        have hiRow : i ∈ rowSupport L M.val := by simpa [hMX] using hiX
        simpa [rowSupport] using (Finset.mem_filter.mp hiRow).2
      · have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
        have hjX : j ∉ X.val := (Finset.mem_sdiff.mp hj).2
        have hjRow : j ∉ rowSupport L M.val := by simpa [hMX] using hjX
        cases hcell : M.val.val L j
        · rfl
        · exact False.elim (hjRow (by simp [rowSupport, hcell]))
    let N : MarginClass r s :=
      ⟨Brualdi.Ryser.switchMat M.val.val L a i j,
        Brualdi.Ryser.interchange_preserves_margins
          (Brualdi.Ryser.switch_interchange hb) M.val.property⟩
    have hNY : rowSupport L N = Y.val := by
      change (Finset.univ.filter (fun b =>
        Brualdi.Ryser.switchMat M.val.val L a i j L b = true)) = Y.val
      exact rowSupport_eq_after_single_switch
        (L := L) (a := a) (i := i) (j := j) (M := M.val.val)
        (X := X.val) (Y := Y.val) (by simpa [rowSupport] using hMX) hXY hYX haL
    have hNfib : N ∈ fibre (rowProj hB) Y := by
      simp [fibre, rowProj, hNY]
    have hAdj : (flipGraph r s).Adj M.val N := by
      have hint : Interchange M.val.val N.val := by
        simpa [N] using Brualdi.Ryser.switch_interchange hb
      have hne : M.val ≠ N := by
        intro heq
        have hval : M.val.val = N.val := congrArg Subtype.val heq
        exact Brualdi.Ryser.switchMat_ne hb (by simpa [N] using hval.symm)
      rw [flipGraph, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl hint⟩
    rw [mem_interface_iff]
    refine ⟨?_, N, hNfib, hAdj⟩
    simp [fibre, M.property]

theorem isMH_connected {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} :
    IsMH G → G.Connected := by
  classical
  intro hMH
  refine ⟨?_⟩
  intro u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.rfl
  rcases hMH with hHC | ⟨col, _hproper, hsurj, hlace⟩
  · rcases hHC u v huv with ⟨p, _hp⟩
    exact p.reachable
  · by_cases hcol : col u ≠ col v
    · rcases hlace u v hcol with ⟨p, _hp⟩
      exact p.reachable
    · have hsame : col u = col v := by
        by_contra hne
        exact hcol hne
      rcases hsurj (! col u) with ⟨w, hw⟩
      have huw : col u ≠ col w := by
        rw [hw]
        cases col u <;> decide
      have hwv : col w ≠ col v := by
        rw [hw, ← hsame]
        cases col u <;> decide
      rcases hlace u w huw with ⟨p, _hp⟩
      rcases hlace w v hwv with ⟨q, _hq⟩
      exact p.reachable.trans q.reachable

private theorem boundary_edge_of_walk {V : Type u} {G : SimpleGraph V} {S : Finset V}
    {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil =>
      exact False.elim (hv hu)
  | @cons u w v huw p ih =>
      by_cases hwS : w ∈ S
      · exact ih hwS hv
      · exact ⟨u, hu, w, hwS, huw⟩

theorem connected_boundary_edge {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) {S : Finset V}
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  classical
  rcases hne with ⟨s, hs⟩
  have hout : ∃ t : V, t ∉ S := by
    by_contra h
    push_neg at h
    apply hproper
    ext v
    simp [h v]
  rcases hout with ⟨t, ht⟩
  rcases hconn.preconnected s t with ⟨p⟩
  exact boundary_edge_of_walk p hs ht

private theorem interchange_eq_switchMat_of_witness {m n : ℕ}
    {M M' : ZeroOneMat m n} {r₁ r₂ : Fin m} {c₁ c₂ : Fin n}
    (hM'₁₁ : M' r₁ c₁ = false) (hM'₂₂ : M' r₂ c₂ = false)
    (hM'₁₂ : M' r₁ c₂ = true) (hM'₂₁ : M' r₂ c₁ = true)
    (hout : ∀ a b, ¬ ((a = r₁ ∨ a = r₂) ∧ (b = c₁ ∨ b = c₂)) → M' a b = M a b) :
    M' = Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ := by
  funext a b
  simp only [Brualdi.Ryser.switchMat]
  split_ifs with h₁₁ h₂₂ h₁₂ h₂₁
  · simpa [h₁₁.1, h₁₁.2] using hM'₁₁
  · simpa [h₂₂.1, h₂₂.2] using hM'₂₂
  · simpa [h₁₂.1, h₁₂.2] using hM'₁₂
  · simpa [h₂₁.1, h₂₁.2] using hM'₂₁
  · exact hout a b (by
      intro hblock
      rcases hblock with ⟨hr, hc⟩
      rcases hr with rfl | rfl
      · rcases hc with rfl | rfl
        · exact h₁₁ ⟨rfl, rfl⟩
        · exact h₁₂ ⟨rfl, rfl⟩
      · rcases hc with rfl | rfl
        · exact h₂₁ ⟨rfl, rfl⟩
        · exact h₂₂ ⟨rfl, rfl⟩)

private theorem switchMat_swap_rows_cols {m n : ℕ} (M : ZeroOneMat m n)
    (r₁ r₂ : Fin m) (c₁ c₂ : Fin n) :
    Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ =
      Brualdi.Ryser.switchMat M r₂ r₁ c₂ c₁ := by
  funext a b
  simp only [Brualdi.Ryser.switchMat]
  split_ifs <;> simp_all

private theorem crossing_eq_switchMat {m n : ℕ}
    {M N : ZeroOneMat (m + 1) n} {L : Fin (m + 1)} {i j : Fin n}
    (hMLi : M L i = true) (hMLj : M L j = false)
    (hNLi : N L i = false) (hNLj : N L j = true)
    (hint : Interchange M N) :
    ∃ a, a ≠ L ∧ M a i = false ∧ M a j = true ∧
      N = Brualdi.Ryser.switchMat M L a i j := by
  classical
  rcases hint with
    ⟨r₁, r₂, c₁, c₂, hr, hc, hM11, hM22, hM12, hM21,
      hN11, hN22, hN12, hN21, hout⟩
  have hrow : L = r₁ ∨ L = r₂ := by
    by_contra h
    push_neg at h
    have hsame : N L i = M L i := hout L i (by
      intro hb
      exact hb.1.elim h.1 h.2)
    rw [hNLi, hMLi] at hsame
    exact Bool.false_ne_true hsame
  rcases hrow with hL | hL
  · subst L
    have hic₁ : i = c₁ := by
      by_cases hi1 : i = c₁
      · exact hi1
      · by_cases hi2 : i = c₂
        · subst i
          rw [hM12] at hMLi
          exact False.elim (Bool.false_ne_true hMLi)
        · have hsame : N r₁ i = M r₁ i := hout r₁ i (by
            intro hb
            exact hb.2.elim hi1 hi2)
          rw [hNLi, hMLi] at hsame
          exact False.elim (Bool.false_ne_true hsame)
    have hjc₂ : j = c₂ := by
      by_cases hj2 : j = c₂
      · exact hj2
      · by_cases hj1 : j = c₁
        · subst j
          rw [hM11] at hMLj
          exact False.elim (Bool.false_ne_true hMLj.symm)
        · have hsame : N r₁ j = M r₁ j := hout r₁ j (by
            intro hb
            exact hb.2.elim hj1 hj2)
          rw [hNLj, hMLj] at hsame
          exact False.elim (Bool.false_ne_true hsame.symm)
    refine ⟨r₂, hr.symm, ?_, ?_, ?_⟩
    · simpa [hic₁] using hM21
    · simpa [hjc₂] using hM22
    · have hEq : N = Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ :=
        interchange_eq_switchMat_of_witness hN11 hN22 hN12 hN21 hout
      simpa [hic₁, hjc₂] using hEq
  · subst L
    have hic₂ : i = c₂ := by
      by_cases hi2 : i = c₂
      · exact hi2
      · by_cases hi1 : i = c₁
        · subst i
          rw [hM21] at hMLi
          exact False.elim (Bool.false_ne_true hMLi)
        · have hsame : N r₂ i = M r₂ i := hout r₂ i (by
            intro hb
            exact hb.2.elim hi1 hi2)
          rw [hNLi, hMLi] at hsame
          exact False.elim (Bool.false_ne_true hsame)
    have hjc₁ : j = c₁ := by
      by_cases hj1 : j = c₁
      · exact hj1
      · by_cases hj2 : j = c₂
        · subst j
          rw [hM22] at hMLj
          exact False.elim (Bool.false_ne_true hMLj.symm)
        · have hsame : N r₂ j = M r₂ j := hout r₂ j (by
            intro hb
            exact hb.2.elim hj1 hj2)
          rw [hNLj, hMLj] at hsame
          exact False.elim (Bool.false_ne_true hsame.symm)
    refine ⟨r₁, hr, ?_, ?_, ?_⟩
    · simpa [hic₂] using hM12
    · simpa [hjc₁] using hM11
    · have hEq : N = Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ :=
        interchange_eq_switchMat_of_witness hN11 hN22 hN12 hN21 hout
      have hswap := switchMat_swap_rows_cols M r₁ r₂ c₁ c₂
      simpa [hic₂, hjc₁] using hEq.trans hswap

theorem bipartite_no_triangle {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {col : V → Bool} (hbip : IsProper2Coloring G col)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    False := by
  have habc := hbip a b hab
  have hbcc := hbip b c hbc
  have hcac := hbip c a hca
  cases ha : col a <;> cases hb : col b <;> cases hc : col c <;>
    simp [ha, hb, hc] at habc hbcc hcac

/-! ## Block 3c: triangle classification and wide pairs -/

def DiffTri {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M0 M1 M2 : MarginClass r s) (x : Fin m) (c : Fin n) : Prop :=
  M0.val x c ≠ M1.val x c ∨ M1.val x c ≠ M2.val x c ∨ M0.val x c ≠ M2.val x c

private def diffCells {m n : ℕ} (M N : ZeroOneMat m n) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p : Fin m × Fin n => M p.1 p.2 ≠ N p.1 p.2)

private theorem adj_interchange {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M N : MarginClass r s} (h : (flipGraph r s).Adj M N) :
    Interchange M.val N.val := by
  rw [flipGraph, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨_hne, hint | hint⟩
  · exact hint
  · exact interchange_symm hint

private theorem interchange_diffCells_prod {m n : ℕ} {M N : ZeroOneMat m n}
    (hint : Interchange M N) :
    ∃ a b : Fin m, ∃ i j : Fin n,
      a ≠ b ∧ i ≠ j ∧
      diffCells M N = ({a, b} : Finset (Fin m)) ×ˢ ({i, j} : Finset (Fin n)) ∧
      M a i = true ∧ M b j = true ∧ M a j = false ∧ M b i = false := by
  classical
  rcases hint with
    ⟨a, b, i, j, hab, hij, hMai, hMbj, hMaj, hMbi,
      hNai, hNbj, hNaj, hNbi, hout⟩
  refine ⟨a, b, i, j, hab, hij, ?_, hMai, hMbj, hMaj, hMbi⟩
  ext p
  constructor
  · intro hp
    have hdiff : M p.1 p.2 ≠ N p.1 p.2 := by
      simpa [diffCells] using hp
    have hblock : (p.1 = a ∨ p.1 = b) ∧ (p.2 = i ∨ p.2 = j) := by
      by_contra hnot
      have hsame := hout p.1 p.2 hnot
      exact hdiff hsame.symm
    simpa using hblock
  · intro hp
    rcases (by simpa using hp :
        (p.1 = a ∨ p.1 = b) ∧ (p.2 = i ∨ p.2 = j)) with ⟨hrow, hcol⟩
    rcases hrow with rfl | rfl <;> rcases hcol with rfl | rfl
    · simp [diffCells, hMai, hNai]
    · simp [diffCells, hMaj, hNaj]
    · simp [diffCells, hMbi, hNbi]
    · simp [diffCells, hMbj, hNbj]

private theorem diffCells_card_of_interchange {m n : ℕ} {M N : ZeroOneMat m n}
    (hint : Interchange M N) :
    (diffCells M N).card = 4 := by
  classical
  rcases interchange_diffCells_prod hint with
    ⟨a, b, i, j, hab, hij, hD, _⟩
  rw [hD, Finset.card_product, Finset.card_pair hab, Finset.card_pair hij]

private theorem diffCells_triangle {m n : ℕ} (M0 M1 M2 : ZeroOneMat m n) :
    diffCells M0 M2 = symmDiff (diffCells M0 M1) (diffCells M1 M2) := by
  classical
  ext p
  simp only [diffCells, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  cases h0 : M0 p.1 p.2 <;> cases h1 : M1 p.1 p.2 <;> cases h2 : M2 p.1 p.2 <;>
    simp [h0, h1, h2]

private theorem card_symmDiff_add_twice_inter {α : Type*} [DecidableEq α]
    (A B : Finset α) :
    (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
  classical
  have hsymm : symmDiff A B = A \ B ∪ B \ A := by
    rw [Finset.symmDiff_def]
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_sdiff.mp hxB).1
  have hcard_symm :
      (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [hsymm]
    exact Finset.card_union_of_disjoint hdisj
  have hA := Finset.card_inter_add_card_sdiff A B
  have hB := Finset.card_inter_add_card_sdiff B A
  have hBA : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
  omega

private theorem inter_card_eq_two_of_triangle {m n : ℕ}
    {M0 M1 M2 : ZeroOneMat m n}
    (h01 : Interchange M0 M1) (h12 : Interchange M1 M2) (h02 : Interchange M0 M2) :
    (diffCells M0 M1 ∩ diffCells M1 M2).card = 2 := by
  classical
  have h01c := diffCells_card_of_interchange h01
  have h12c := diffCells_card_of_interchange h12
  have h02c := diffCells_card_of_interchange h02
  have htri := diffCells_triangle M0 M1 M2
  have hsymm :
      (symmDiff (diffCells M0 M1) (diffCells M1 M2)).card = 4 := by
    simpa [htri] using h02c
  have hcard := card_symmDiff_add_twice_inter (diffCells M0 M1) (diffCells M1 M2)
  omega

private theorem pair_inter_card_two_eq {α : Type*} [DecidableEq α]
    {a b c d : α} (hab : a ≠ b) (hcard : (({a, b} : Finset α) ∩ {c, d}).card = 2) :
    ({a, b} : Finset α) = ({c, d} : Finset α) := by
  classical
  have hleft : ({a, b} : Finset α) ∩ {c, d} = {a, b} := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hcard, Finset.card_pair hab]
  have hcd_le : ({c, d} : Finset α).card ≤ 2 := by
    by_cases hcd : c = d
    · subst d
      simp
    · rw [Finset.card_pair hcd]
  have hright : ({a, b} : Finset α) ∩ {c, d} = {c, d} := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [hcard]
    exact hcd_le
  exact hleft.symm.trans hright

/-- Lemma 5.10 (né 5.7b): every interchange-graph triangle is supported on either two rows and
    three columns, or three rows and two columns. -/
theorem triangle_classification {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M0 M1 M2 : MarginClass r s}
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2) :
    (∃ a b : Fin m, a ≠ b ∧ ∀ x c, DiffTri M0 M1 M2 x c → x = a ∨ x = b) ∨
    (∃ i j : Fin n, i ≠ j ∧ ∀ x c, DiffTri M0 M1 M2 x c → c = i ∨ c = j) := by
  classical
  have hi01 := adj_interchange h01
  have hi12 := adj_interchange h12
  have hi02 := adj_interchange h02
  rcases interchange_diffCells_prod hi01 with
    ⟨a1, b1, i1, j1, hab1, hij1, hD01, _⟩
  rcases interchange_diffCells_prod hi12 with
    ⟨a2, b2, i2, j2, hab2, hij2, hD12, _⟩
  let R1 : Finset (Fin m) := {a1, b1}
  let R2 : Finset (Fin m) := {a2, b2}
  let C1 : Finset (Fin n) := {i1, j1}
  let C2 : Finset (Fin n) := {i2, j2}
  have hInter : (R1 ∩ R2).card * (C1 ∩ C2).card = 2 := by
    have hcard := inter_card_eq_two_of_triangle hi01 hi12 hi02
    rw [hD01, hD12, Finset.product_inter_product, Finset.card_product] at hcard
    simpa [R1, R2, C1, C2] using hcard
  have hRle : (R1 ∩ R2).card ≤ 2 := by
    have hR1 : R1.card = 2 := by simpa [R1] using Finset.card_pair hab1
    rw [← hR1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hCle : (C1 ∩ C2).card ≤ 2 := by
    have hC1 : C1.card = 2 := by simpa [C1] using Finset.card_pair hij1
    rw [← hC1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hcases : ((R1 ∩ R2).card = 2 ∧ (C1 ∩ C2).card = 1) ∨
      ((R1 ∩ R2).card = 1 ∧ (C1 ∩ C2).card = 2) := by
    have hRpos : 0 < (R1 ∩ R2).card := by
      by_contra h
      have hz : (R1 ∩ R2).card = 0 := by omega
      rw [hz] at hInter
      norm_num at hInter
    have hCpos : 0 < (C1 ∩ C2).card := by
      by_contra h
      have hz : (C1 ∩ C2).card = 0 := by omega
      rw [hz, Nat.mul_zero] at hInter
      norm_num at hInter
    have hRcases : (R1 ∩ R2).card = 1 ∨ (R1 ∩ R2).card = 2 := by omega
    have hCcases : (C1 ∩ C2).card = 1 ∨ (C1 ∩ C2).card = 2 := by omega
    rcases hRcases with hR | hR <;> rcases hCcases with hC | hC
    · exfalso
      have hbad : (1 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
    · exact Or.inr ⟨hR, hC⟩
    · exact Or.inl ⟨hR, hC⟩
    · exfalso
      have hbad : (4 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
  rcases hcases with hrow | hcol
  · left
    have hR_eq : R1 = R2 := by
      simpa [R1, R2] using pair_inter_card_two_eq hab1 hrow.1
    refine ⟨a1, b1, hab1, ?_⟩
    intro x c hdiff
    have in_R1_of_D01 (hp : (x, c) ∈ diffCells M0.val M1.val) : x = a1 ∨ x = b1 := by
      rw [hD01] at hp
      exact by simpa [R1, C1] using (by simpa [R1, C1] using hp : x ∈ R1 ∧ c ∈ C1).1
    have in_R1_of_D12 (hp : (x, c) ∈ diffCells M1.val M2.val) : x = a1 ∨ x = b1 := by
      rw [hD12] at hp
      have hp' : x ∈ R2 ∧ c ∈ C2 := by simpa [R2, C2] using hp
      have hxR1 : x ∈ R1 := by simpa [hR_eq] using hp'.1
      exact by simpa [R1] using hxR1
    have in_R1_of_D02 (hp : (x, c) ∈ diffCells M0.val M2.val) : x = a1 ∨ x = b1 := by
      rw [diffCells_triangle M0.val M1.val M2.val, Finset.mem_symmDiff] at hp
      rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩
      · exact in_R1_of_D01 hp
      · exact in_R1_of_D12 hp
    rcases hdiff with h | h | h
    · exact in_R1_of_D01 (by simpa [diffCells] using h)
    · exact in_R1_of_D12 (by simpa [diffCells] using h)
    · exact in_R1_of_D02 (by simpa [diffCells] using h)
  · right
    have hC_eq : C1 = C2 := by
      simpa [C1, C2] using pair_inter_card_two_eq hij1 hcol.2
    refine ⟨i1, j1, hij1, ?_⟩
    intro x c hdiff
    have in_C1_of_D01 (hp : (x, c) ∈ diffCells M0.val M1.val) : c = i1 ∨ c = j1 := by
      rw [hD01] at hp
      exact by simpa [C1] using (by simpa [R1, C1] using hp : x ∈ R1 ∧ c ∈ C1).2
    have in_C1_of_D12 (hp : (x, c) ∈ diffCells M1.val M2.val) : c = i1 ∨ c = j1 := by
      rw [hD12] at hp
      have hp' : x ∈ R2 ∧ c ∈ C2 := by simpa [R2, C2] using hp
      have hcC1 : c ∈ C1 := by simpa [hC_eq] using hp'.2
      exact by simpa [C1] using hcC1
    have in_C1_of_D02 (hp : (x, c) ∈ diffCells M0.val M2.val) : c = i1 ∨ c = j1 := by
      rw [diffCells_triangle M0.val M1.val M2.val, Finset.mem_symmDiff] at hp
      rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩
      · exact in_C1_of_D01 hp
      · exact in_C1_of_D12 hp
    rcases hdiff with h | h | h
    · exact in_C1_of_D01 (by simpa [diffCells] using h)
    · exact in_C1_of_D12 (by simpa [diffCells] using h)
    · exact in_C1_of_D02 (by simpa [diffCells] using h)

def WideRowPair {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (p q : Fin m) : Prop :=
  p ≠ q ∧ ∃ M : MarginClass r s,
    (∃ c, M.val p c = true ∧ M.val q c = false) ∧
    (∃ c, M.val p c = false ∧ M.val q c = true) ∧
    3 ≤ (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)).card

def WideColPair {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ ∃ M : MarginClass r s,
    (∃ x, M.val x i = true ∧ M.val x j = false) ∧
    (∃ x, M.val x i = false ∧ M.val x j = true) ∧
    3 ≤ (Finset.univ.filter (fun x => M.val x i ≠ M.val x j)).card

private theorem source_interchange_rows_differ_on_col {m n : ℕ} {M : ZeroOneMat m n}
    {a b x y : Fin m} {i j c : Fin n}
    (hab : a ≠ b) (hij : i ≠ j)
    (hMai : M a i = true) (hMbj : M b j = true)
    (hMaj : M a j = false) (hMbi : M b i = false)
    (hxy : x ≠ y) (hx : x ∈ ({a, b} : Finset (Fin m)))
    (hy : y ∈ ({a, b} : Finset (Fin m)))
    (hc : c ∈ ({i, j} : Finset (Fin n))) :
    M x c ≠ M y c := by
  classical
  rcases (by simpa using hx : x = a ∨ x = b) with hx_a | hx_b
  · rcases (by simpa using hy : y = a ∨ y = b) with hy_a | hy_b
    · exact False.elim (hxy (hx_a.trans hy_a.symm))
    · rcases (by simpa using hc : c = i ∨ c = j) with hc_i | hc_j
      · simpa [hx_a, hy_b, hc_i, hMai, hMbi]
      · simpa [hx_a, hy_b, hc_j, hMaj, hMbj]
  · rcases (by simpa using hy : y = a ∨ y = b) with hy_a | hy_b
    · rcases (by simpa using hc : c = i ∨ c = j) with hc_i | hc_j
      · simpa [hx_b, hy_a, hc_i, hMbi, hMai]
      · simpa [hx_b, hy_a, hc_j, hMbj, hMaj]
    · exact False.elim (hxy (hx_b.trans hy_b.symm))

private theorem source_interchange_cols_differ_on_row {m n : ℕ} {M : ZeroOneMat m n}
    {a b x : Fin m} {i j c d : Fin n}
    (hab : a ≠ b) (hij : i ≠ j)
    (hMai : M a i = true) (hMbj : M b j = true)
    (hMaj : M a j = false) (hMbi : M b i = false)
    (hcd : c ≠ d) (hx : x ∈ ({a, b} : Finset (Fin m)))
    (hc : c ∈ ({i, j} : Finset (Fin n)))
    (hd : d ∈ ({i, j} : Finset (Fin n))) :
    M x c ≠ M x d := by
  classical
  rcases (by simpa using hx : x = a ∨ x = b) with hx_a | hx_b
  · rcases (by simpa using hc : c = i ∨ c = j) with hc_i | hc_j
    · rcases (by simpa using hd : d = i ∨ d = j) with hd_i | hd_j
      · exact False.elim (hcd (hc_i.trans hd_i.symm))
      · simpa [hx_a, hc_i, hd_j, hMai, hMaj]
    · rcases (by simpa using hd : d = i ∨ d = j) with hd_i | hd_j
      · simpa [hx_a, hc_j, hd_i, hMaj, hMai]
      · exact False.elim (hcd (hc_j.trans hd_j.symm))
  · rcases (by simpa using hc : c = i ∨ c = j) with hc_i | hc_j
    · rcases (by simpa using hd : d = i ∨ d = j) with hd_i | hd_j
      · exact False.elim (hcd (hc_i.trans hd_i.symm))
      · simpa [hx_b, hc_i, hd_j, hMbi, hMbj]
    · rcases (by simpa using hd : d = i ∨ d = j) with hd_i | hd_j
      · simpa [hx_b, hc_j, hd_i, hMbj, hMbi]
      · exact False.elim (hcd (hc_j.trans hd_j.symm))

theorem triangle_wide_pair {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M0 M1 M2 : MarginClass r s}
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2) :
    (∃ p q : Fin m, WideRowPair r s p q) ∨
      (∃ i j : Fin n, WideColPair r s i j) := by
  classical
  have hi01 := adj_interchange h01
  have hi12 := adj_interchange h12
  have hi02 := adj_interchange h02
  rcases interchange_diffCells_prod hi01 with
    ⟨a1, b1, i1, j1, hab1, hij1, hD01, hM0a1i1, hM0b1j1, hM0a1j1, hM0b1i1⟩
  rcases interchange_diffCells_prod hi12 with
    ⟨a2, b2, i2, j2, hab2, hij2, hD12, hM1a2i2, hM1b2j2, hM1a2j2, hM1b2i2⟩
  let R1 : Finset (Fin m) := {a1, b1}
  let R2 : Finset (Fin m) := {a2, b2}
  let C1 : Finset (Fin n) := {i1, j1}
  let C2 : Finset (Fin n) := {i2, j2}
  have hInter : (R1 ∩ R2).card * (C1 ∩ C2).card = 2 := by
    have hcard := inter_card_eq_two_of_triangle hi01 hi12 hi02
    rw [hD01, hD12, Finset.product_inter_product, Finset.card_product] at hcard
    simpa [R1, R2, C1, C2] using hcard
  have hRle : (R1 ∩ R2).card ≤ 2 := by
    have hR1 : R1.card = 2 := by simpa [R1] using Finset.card_pair hab1
    rw [← hR1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hCle : (C1 ∩ C2).card ≤ 2 := by
    have hC1 : C1.card = 2 := by simpa [C1] using Finset.card_pair hij1
    rw [← hC1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hcases : ((R1 ∩ R2).card = 2 ∧ (C1 ∩ C2).card = 1) ∨
      ((R1 ∩ R2).card = 1 ∧ (C1 ∩ C2).card = 2) := by
    have hRpos : 0 < (R1 ∩ R2).card := by
      by_contra h
      have hz : (R1 ∩ R2).card = 0 := by omega
      rw [hz] at hInter
      norm_num at hInter
    have hCpos : 0 < (C1 ∩ C2).card := by
      by_contra h
      have hz : (C1 ∩ C2).card = 0 := by omega
      rw [hz, Nat.mul_zero] at hInter
      norm_num at hInter
    have hRcases : (R1 ∩ R2).card = 1 ∨ (R1 ∩ R2).card = 2 := by omega
    have hCcases : (C1 ∩ C2).card = 1 ∨ (C1 ∩ C2).card = 2 := by omega
    rcases hRcases with hR | hR <;> rcases hCcases with hC | hC
    · exfalso
      have hbad : (1 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
    · exact Or.inr ⟨hR, hC⟩
    · exact Or.inl ⟨hR, hC⟩
    · exfalso
      have hbad : (4 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
  rcases hcases with hrow | hcol
  · left
    have hR_eq : R1 = R2 := by
      simpa [R1, R2] using pair_inter_card_two_eq hab1 hrow.1
    have hc_extra : ∃ c ∈ C2, c ∉ C1 := by
      by_contra h
      push_neg at h
      have hsub : C2 ⊆ C1 := fun c hc => h c hc
      have hCinter : C1 ∩ C2 = C2 := by
        ext c
        constructor
        · intro hc
          exact (Finset.mem_inter.mp hc).2
        · intro hc
          exact Finset.mem_inter.mpr ⟨hsub hc, hc⟩
      have hcard2 : (C1 ∩ C2).card = 2 := by
        rw [hCinter]
        simpa [C2] using Finset.card_pair hij2
      omega
    rcases hc_extra with ⟨c3, hc3C2, hc3notC1⟩
    have hc3ne_i1 : c3 ≠ i1 := by
      intro h
      exact hc3notC1 (by simp [C1, h])
    have hc3ne_j1 : c3 ≠ j1 := by
      intro h
      exact hc3notC1 (by simp [C1, h])
    have hM0M1a : M0.val a1 c3 = M1.val a1 c3 := by
      by_contra hne
      have hmem : (a1, c3) ∈ diffCells M0.val M1.val := by simpa [diffCells] using hne
      have hprod : a1 ∈ R1 ∧ c3 ∈ C1 := by
        rw [hD01] at hmem
        simpa [R1, C1] using hmem
      exact hc3notC1 hprod.2
    have hM0M1b : M0.val b1 c3 = M1.val b1 c3 := by
      by_contra hne
      have hmem : (b1, c3) ∈ diffCells M0.val M1.val := by simpa [diffCells] using hne
      have hprod : b1 ∈ R1 ∧ c3 ∈ C1 := by
        rw [hD01] at hmem
        simpa [R1, C1] using hmem
      exact hc3notC1 hprod.2
    have ha1R2 : a1 ∈ R2 := by
      have ha1R1 : a1 ∈ R1 := by simp [R1]
      simpa [hR_eq] using ha1R1
    have hb1R2 : b1 ∈ R2 := by
      have hb1R1 : b1 ∈ R1 := by simp [R1]
      simpa [hR_eq] using hb1R1
    have hM1diff :
        M1.val a1 c3 ≠ M1.val b1 c3 :=
      source_interchange_rows_differ_on_col hab2 hij2 hM1a2i2 hM1b2j2
        hM1a2j2 hM1b2i2 hab1 ha1R2 hb1R2 hc3C2
    have hM0diff3 : M0.val a1 c3 ≠ M0.val b1 c3 := by
      intro hsame
      apply hM1diff
      rw [← hM0M1a, ← hM0M1b, hsame]
    have hcard : 3 ≤ (Finset.univ.filter (fun c => M0.val a1 c ≠ M0.val b1 c)).card := by
      let T : Finset (Fin n) := {i1, j1, c3}
      have hTcard : T.card = 3 := by
        simp [T, hij1, hij1.symm, hc3ne_i1, hc3ne_i1.symm, hc3ne_j1, hc3ne_j1.symm]
      have hTsub : T ⊆ Finset.univ.filter (fun c => M0.val a1 c ≠ M0.val b1 c) := by
        intro c hc
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl | rfl
        · simp [hM0a1i1, hM0b1i1]
        · simp [hM0a1j1, hM0b1j1]
        · simp [hM0diff3]
      have hle := Finset.card_le_card hTsub
      omega
    exact ⟨a1, b1, hab1, M0,
      ⟨i1, hM0a1i1, hM0b1i1⟩,
      ⟨j1, hM0a1j1, hM0b1j1⟩, hcard⟩
  · right
    have hC_eq : C1 = C2 := by
      simpa [C1, C2] using pair_inter_card_two_eq hij1 hcol.2
    have hr_extra : ∃ x ∈ R2, x ∉ R1 := by
      by_contra h
      push_neg at h
      have hsub : R2 ⊆ R1 := fun x hx => h x hx
      have hRinter : R1 ∩ R2 = R2 := by
        ext x
        constructor
        · intro hx
          exact (Finset.mem_inter.mp hx).2
        · intro hx
          exact Finset.mem_inter.mpr ⟨hsub hx, hx⟩
      have hcard2 : (R1 ∩ R2).card = 2 := by
        rw [hRinter]
        simpa [R2] using Finset.card_pair hab2
      omega
    rcases hr_extra with ⟨x3, hx3R2, hx3notR1⟩
    have hx3ne_a1 : x3 ≠ a1 := by
      intro h
      exact hx3notR1 (by simp [R1, h])
    have hx3ne_b1 : x3 ≠ b1 := by
      intro h
      exact hx3notR1 (by simp [R1, h])
    have hM0M1i : M0.val x3 i1 = M1.val x3 i1 := by
      by_contra hne
      have hmem : (x3, i1) ∈ diffCells M0.val M1.val := by simpa [diffCells] using hne
      have hprod : x3 ∈ R1 ∧ i1 ∈ C1 := by
        rw [hD01] at hmem
        simpa [R1, C1] using hmem
      exact hx3notR1 hprod.1
    have hM0M1j : M0.val x3 j1 = M1.val x3 j1 := by
      by_contra hne
      have hmem : (x3, j1) ∈ diffCells M0.val M1.val := by simpa [diffCells] using hne
      have hprod : x3 ∈ R1 ∧ j1 ∈ C1 := by
        rw [hD01] at hmem
        simpa [R1, C1] using hmem
      exact hx3notR1 hprod.1
    have hi1C2 : i1 ∈ C2 := by
      have hi1C1 : i1 ∈ C1 := by simp [C1]
      simpa [hC_eq] using hi1C1
    have hj1C2 : j1 ∈ C2 := by
      have hj1C1 : j1 ∈ C1 := by simp [C1]
      simpa [hC_eq] using hj1C1
    have hM1diff :
        M1.val x3 i1 ≠ M1.val x3 j1 :=
      source_interchange_cols_differ_on_row hab2 hij2 hM1a2i2 hM1b2j2
        hM1a2j2 hM1b2i2 hij1 hx3R2 hi1C2 hj1C2
    have hM0diff3 : M0.val x3 i1 ≠ M0.val x3 j1 := by
      intro hsame
      apply hM1diff
      rw [← hM0M1i, ← hM0M1j, hsame]
    have hcard : 3 ≤ (Finset.univ.filter (fun x => M0.val x i1 ≠ M0.val x j1)).card := by
      let T : Finset (Fin m) := {a1, b1, x3}
      have hTcard : T.card = 3 := by
        simp [T, hab1, hab1.symm, hx3ne_a1, hx3ne_a1.symm, hx3ne_b1, hx3ne_b1.symm]
      have hTsub : T ⊆ Finset.univ.filter (fun x => M0.val x i1 ≠ M0.val x j1) := by
        intro x hx
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simp [hM0a1i1, hM0a1j1]
        · simp [hM0b1i1, hM0b1j1]
        · simp [hM0diff3]
      have hle := Finset.card_le_card hTsub
      omega
    exact ⟨i1, j1, hij1, M0,
      ⟨a1, hM0a1i1, hM0a1j1⟩,
      ⟨b1, hM0b1i1, hM0b1j1⟩, hcard⟩

private theorem row_three_pattern_supports_triangle {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) {u v : Fin m} {i j c : Fin n}
    (huv : u ≠ v) (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (hui : M.val u i = true) (huj : M.val u j = true) (huc : M.val u c = false)
    (hvi : M.val v i = false) (hvj : M.val v j = false) (hvc : M.val v c = true) :
    ∃ M0 M1 M2 : MarginClass r s,
      M0 = M ∧
      M1.val = Brualdi.Ryser.switchMat M.val u v i c ∧
      M2.val = Brualdi.Ryser.switchMat M.val u v j c ∧
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 := by
  classical
  rcases alternate_switch_triangle_core huv hij hic hjc hui huj huc hvi hvj hvc with
    ⟨hb_i, hb_j, hb_ji, heq_j⟩
  let M0 : MarginClass r s := M
  let M1 : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val u v i c,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb_i) M.property⟩
  let M2 : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val u v j c,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb_j) M.property⟩
  refine ⟨M0, M1, M2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have hint : Interchange M0.val M1.val := by
      simpa [M0, M1] using Brualdi.Ryser.switch_interchange hb_i
    have hne : M0 ≠ M1 := by
      intro h
      have hval : M1.val = M0.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_i (by simpa [M0, M1] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩
  · have hint : Interchange M1.val M2.val := by
      have hsw := Brualdi.Ryser.switch_interchange hb_ji
      simpa [M1, M2, heq_j] using hsw
    have hne : M1 ≠ M2 := by
      intro h
      have hval : M2.val = M1.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_ji (by simpa [M1, M2, heq_j] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩
  · have hint : Interchange M0.val M2.val := by
      simpa [M0, M2] using Brualdi.Ryser.switch_interchange hb_j
    have hne : M0 ≠ M2 := by
      intro h
      have hval : M2.val = M0.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_j (by simpa [M0, M2] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩

private theorem col_three_pattern_supports_triangle {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) {a b c : Fin m} {u v : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (huv : u ≠ v)
    (hau : M.val a u = true) (hav : M.val a v = false)
    (hbu : M.val b u = true) (hbv : M.val b v = false)
    (hcu : M.val c u = false) (hcv : M.val c v = true) :
    ∃ M0 M1 M2 : MarginClass r s,
      M0 = M ∧
      M1.val = Brualdi.Ryser.switchMat M.val a c u v ∧
      M2.val = Brualdi.Ryser.switchMat M.val b c u v ∧
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 := by
  classical
  have hb_a : Brualdi.Ryser.SwitchBlock M.val a c u v :=
    ⟨hac, huv, hau, hcv, hav, hcu⟩
  have hb_b : Brualdi.Ryser.SwitchBlock M.val b c u v :=
    ⟨hbc, huv, hbu, hcv, hbv, hcu⟩
  have hb_ba : Brualdi.Ryser.SwitchBlock (Brualdi.Ryser.switchMat M.val a c u v) b a u v := by
    refine ⟨hab.symm, huv, ?_, ?_, ?_, ?_⟩
    · simp [Brualdi.Ryser.switchMat, hab.symm, hbc, hbu]
    · simp [Brualdi.Ryser.switchMat, hac, huv.symm]
    · simp [Brualdi.Ryser.switchMat, hab.symm, hbc, hbv]
    · simp [Brualdi.Ryser.switchMat]
  have heq_b :
      Brualdi.Ryser.switchMat M.val b c u v =
        Brualdi.Ryser.switchMat (Brualdi.Ryser.switchMat M.val a c u v) b a u v := by
    funext x y
    simp only [Brualdi.Ryser.switchMat]
    split_ifs <;> simp_all
  let M0 : MarginClass r s := M
  let M1 : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val a c u v,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb_a) M.property⟩
  let M2 : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val b c u v,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb_b) M.property⟩
  refine ⟨M0, M1, M2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have hint : Interchange M0.val M1.val := by
      simpa [M0, M1] using Brualdi.Ryser.switch_interchange hb_a
    have hne : M0 ≠ M1 := by
      intro h
      have hval : M1.val = M0.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_a (by simpa [M0, M1] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩
  · have hint : Interchange M1.val M2.val := by
      have hsw := Brualdi.Ryser.switch_interchange hb_ba
      simpa [M1, M2, heq_b] using hsw
    have hne : M1 ≠ M2 := by
      intro h
      have hval : M2.val = M1.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_ba (by simpa [M1, M2, heq_b] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩
  · have hint : Interchange M0.val M2.val := by
      simpa [M0, M2] using Brualdi.Ryser.switch_interchange hb_b
    have hne : M0 ≠ M2 := by
      intro h
      have hval : M2.val = M0.val := congrArg Subtype.val h.symm
      exact Brualdi.Ryser.switchMat_ne hb_b (by simpa [M0, M2] using hval)
    rw [flipGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hint⟩

theorem wide_row_pair_supports_triangle {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q : Fin m} (hwide : WideRowPair r s p q) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 := by
  rcases hwide with ⟨hpq, M, htf, hft, hcard⟩
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = false ∧ M.val q c = true)
  let D : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c ≠ M.val q c)
  have hD_eq : D = A ∪ B := by
    ext c
    simp only [D, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hp : M.val p c <;> cases hq : M.val q c <;> simp [hp, hq]
  have hDcard : 3 ≤ D.card := by
    simpa [D] using hcard
  have hwide_or : 1 < A.card ∨ 1 < B.card := by
    by_contra h
    push_neg at h
    have hle_union : D.card ≤ A.card + B.card := by
      rw [hD_eq]
      exact Finset.card_union_le A B
    have hle_two : D.card ≤ 2 := by omega
    omega
  rcases hwide_or with hA | hB
  · rcases (Finset.one_lt_card.mp hA) with ⟨i, hiA, j, hjA, hij⟩
    rcases hft with ⟨c, hpc, hqc⟩
    have hi : M.val p i = true ∧ M.val q i = false := by simpa [A] using hiA
    have hj : M.val p j = true ∧ M.val q j = false := by simpa [A] using hjA
    have hic : i ≠ c := by
      intro h
      rw [h] at hi
      rw [hpc] at hi
      exact Bool.false_ne_true hi.1
    have hjc : j ≠ c := by
      intro h
      rw [h] at hj
      rw [hpc] at hj
      exact Bool.false_ne_true hj.1
    rcases row_three_pattern_supports_triangle M hpq hij hic hjc
        hi.1 hj.1 hpc hi.2 hj.2 hqc with
      ⟨M0, M1, M2, _hM0, _hM1, _hM2, h01, h12, h02⟩
    exact ⟨M0, M1, M2, h01, h12, h02⟩
  · rcases (Finset.one_lt_card.mp hB) with ⟨i, hiB, j, hjB, hij⟩
    rcases htf with ⟨c, hpc, hqc⟩
    have hi : M.val p i = false ∧ M.val q i = true := by simpa [B] using hiB
    have hj : M.val p j = false ∧ M.val q j = true := by simpa [B] using hjB
    have hic : i ≠ c := by
      intro h
      rw [h] at hi
      rw [hpc] at hi
      exact Bool.false_ne_true hi.1.symm
    have hjc : j ≠ c := by
      intro h
      rw [h] at hj
      rw [hpc] at hj
      exact Bool.false_ne_true hj.1.symm
    rcases row_three_pattern_supports_triangle M hpq.symm hij hic hjc
        hi.2 hj.2 hqc hi.1 hj.1 hpc with
      ⟨M0, M1, M2, _hM0, _hM1, _hM2, h01, h12, h02⟩
    exact ⟨M0, M1, M2, h01, h12, h02⟩

theorem wide_col_pair_supports_triangle {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {i j : Fin n} (hwide : WideColPair r s i j) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 := by
  rcases hwide with ⟨hij, M, htf, hft, hcard⟩
  classical
  let A : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i = true ∧ M.val x j = false)
  let B : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i = false ∧ M.val x j = true)
  let D : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i ≠ M.val x j)
  have hD_eq : D = A ∪ B := by
    ext x
    simp only [D, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hi : M.val x i <;> cases hj : M.val x j <;> simp [hi, hj]
  have hDcard : 3 ≤ D.card := by
    simpa [D] using hcard
  have hwide_or : 1 < A.card ∨ 1 < B.card := by
    by_contra h
    push_neg at h
    have hle_union : D.card ≤ A.card + B.card := by
      rw [hD_eq]
      exact Finset.card_union_le A B
    have hle_two : D.card ≤ 2 := by omega
    omega
  rcases hwide_or with hA | hB
  · rcases (Finset.one_lt_card.mp hA) with ⟨a, haA, b, hbA, hab⟩
    rcases hft with ⟨c, hci, hcj⟩
    have ha : M.val a i = true ∧ M.val a j = false := by simpa [A] using haA
    have hb : M.val b i = true ∧ M.val b j = false := by simpa [A] using hbA
    have hac : a ≠ c := by
      intro h
      rw [h] at ha
      rw [hci] at ha
      exact Bool.false_ne_true ha.1
    have hbc : b ≠ c := by
      intro h
      rw [h] at hb
      rw [hci] at hb
      exact Bool.false_ne_true hb.1
    rcases col_three_pattern_supports_triangle M hab hac hbc hij
        ha.1 ha.2 hb.1 hb.2 hci hcj with
      ⟨M0, M1, M2, _hM0, _hM1, _hM2, h01, h12, h02⟩
    exact ⟨M0, M1, M2, h01, h12, h02⟩
  · rcases (Finset.one_lt_card.mp hB) with ⟨a, haB, b, hbB, hab⟩
    rcases htf with ⟨c, hci, hcj⟩
    have ha : M.val a i = false ∧ M.val a j = true := by simpa [B] using haB
    have hb : M.val b i = false ∧ M.val b j = true := by simpa [B] using hbB
    have hac : a ≠ c := by
      intro h
      rw [h] at ha
      rw [hci] at ha
      exact Bool.false_ne_true ha.1.symm
    have hbc : b ≠ c := by
      intro h
      rw [h] at hb
      rw [hci] at hb
      exact Bool.false_ne_true hb.1.symm
    rcases col_three_pattern_supports_triangle M hab hac hbc hij.symm
        ha.2 ha.1 hb.2 hb.1 hcj hci with
      ⟨M0, M1, M2, _hM0, _hM1, _hM2, h01, h12, h02⟩
    exact ⟨M0, M1, M2, h01, h12, h02⟩

/-! ## Block 3d: Lemma 5.11 (buffer existence) Stage A residue scaffolding -/

/-- The column pattern of a margin-class matrix along a fixed column. -/
def colPat {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ} (C : Fin n) :
    MarginClass r s → (Fin m → Bool) :=
  fun M i => M.val i C

/-- Rows on which two matrices differ. -/
def sepRowSet {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (a b : MarginClass r s) : Finset (Fin m) :=
  Finset.univ.filter (fun L => rowPat L a ≠ rowPat L b)

/-- Columns on which two matrices differ. -/
def sepColSet {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (a b : MarginClass r s) : Finset (Fin n) :=
  Finset.univ.filter (fun C => colPat C a ≠ colPat C b)

/-- Rows used by a triangle, measured by `DiffTri`. -/
def triRows {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M0 M1 M2 : MarginClass r s) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun x => ∃ c : Fin n, DiffTri M0 M1 M2 x c)

/-- Columns used by a triangle, measured by `DiffTri`. -/
def triCols {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M0 M1 M2 : MarginClass r s) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => ∃ x : Fin m, DiffTri M0 M1 M2 x c)

/-- A row-or-column line separates two vertices. -/
def lineSeparates {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (a b : MarginClass r s) : Fin m ⊕ Fin n → Prop
  | Sum.inl L => rowPat L a ≠ rowPat L b
  | Sum.inr C => colPat C a ≠ colPat C b

/-- A line has at least one non-bipartite pattern fibre. -/
def lineFibreNonbip {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ} :
    Fin m ⊕ Fin n → Prop
  | Sum.inl L =>
      ∃ γ : Fin n → Bool,
        ¬ ∃ col : {M : MarginClass r s // rowPat L M = γ} → Bool,
          IsProper2Coloring (fibreGraph (flipGraph r s) (rowPat L) γ) col
  | Sum.inr C =>
      ∃ γ : Fin m → Bool,
        ¬ ∃ col : {M : MarginClass r s // colPat C M = γ} → Bool,
          IsProper2Coloring (fibreGraph (flipGraph r s) (colPat C) γ) col

private theorem exists_ne_of_bool_sum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → Bool) {i : α}
    (hsum : (∑ x : α, (if f x then 1 else 0 : ℕ)) =
      (∑ x : α, (if g x then 1 else 0 : ℕ)))
    (hdiff : f i ≠ g i) :
    ∃ k : α, k ≠ i ∧ f k ≠ g k := by
  classical
  by_cases hex : ∃ k : α, k ≠ i ∧ f k ≠ g k
  · exact hex
  exfalso
  have hsame : ∀ k : α, k ≠ i → f k = g k := by
    intro k hki
    by_contra hfg
    exact hex ⟨k, hki, hfg⟩
  have hrest :
      (∑ x ∈ (Finset.univ.erase i), (if f x then 1 else 0 : ℕ)) =
        (∑ x ∈ (Finset.univ.erase i), (if g x then 1 else 0 : ℕ)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [hsame x (Finset.mem_erase.mp hx).1]
  have hf_split := Finset.add_sum_erase Finset.univ
    (fun x => (if f x then 1 else 0 : ℕ)) (Finset.mem_univ i)
  have hg_split := Finset.add_sum_erase Finset.univ
    (fun x => (if g x then 1 else 0 : ℕ)) (Finset.mem_univ i)
  rw [← hf_split, ← hg_split, hrest] at hsum
  cases hfi : f i <;> cases hgi : g i <;> simp [hfi, hgi] at hdiff hsum <;> omega

/-- Two distinct vertices differ on at least two rows. -/
theorem sepRowSet_card_ge_two {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {a b : MarginClass r s} (hab : a ≠ b) :
    2 ≤ (sepRowSet a b).card := by
  classical
  have hcell : ∃ i : Fin m, ∃ j : Fin n, a.val i j ≠ b.val i j := by
    by_contra h
    push_neg at h
    apply hab
    apply Subtype.ext
    funext i j
    exact h i j
  rcases hcell with ⟨i, j, hij⟩
  have hsum :
      (∑ x : Fin m, (if a.val x j then 1 else 0 : ℕ)) =
        (∑ x : Fin m, (if b.val x j then 1 else 0 : ℕ)) := by
    change colSum a.val j = colSum b.val j
    rw [a.property.2 j, b.property.2 j]
  rcases exists_ne_of_bool_sum_eq (fun x : Fin m => a.val x j)
      (fun x : Fin m => b.val x j) hsum hij with ⟨k, hki, hkdiff⟩
  have hi_sep : rowPat i a ≠ rowPat i b := by
    intro h
    exact hij (congrFun h j)
  have hk_sep : rowPat k a ≠ rowPat k b := by
    intro h
    exact hkdiff (congrFun h j)
  have hsub : ({i, k} : Finset (Fin m)) ⊆ sepRowSet a b := by
    intro x hx
    rcases (by simpa using hx : x = i ∨ x = k) with rfl | rfl
    · simp [sepRowSet, hi_sep]
    · simp [sepRowSet, hk_sep]
  have hle := Finset.card_le_card hsub
  have hpair : ({i, k} : Finset (Fin m)).card = 2 := by
    simpa using Finset.card_pair hki.symm
  omega

/-- Two distinct vertices differ on at least two columns. -/
theorem sepColSet_card_ge_two {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {a b : MarginClass r s} (hab : a ≠ b) :
    2 ≤ (sepColSet a b).card := by
  classical
  have hcell : ∃ i : Fin m, ∃ j : Fin n, a.val i j ≠ b.val i j := by
    by_contra h
    push_neg at h
    apply hab
    apply Subtype.ext
    funext i j
    exact h i j
  rcases hcell with ⟨i, j, hij⟩
  have hsum :
      (∑ y : Fin n, (if a.val i y then 1 else 0 : ℕ)) =
        (∑ y : Fin n, (if b.val i y then 1 else 0 : ℕ)) := by
    change rowSum a.val i = rowSum b.val i
    rw [a.property.1 i, b.property.1 i]
  rcases exists_ne_of_bool_sum_eq (fun y : Fin n => a.val i y)
      (fun y : Fin n => b.val i y) hsum hij with ⟨k, hkj, hkdiff⟩
  have hj_sep : colPat j a ≠ colPat j b := by
    intro h
    exact hij (congrFun h i)
  have hk_sep : colPat k a ≠ colPat k b := by
    intro h
    exact hkdiff (congrFun h i)
  have hsub : ({j, k} : Finset (Fin n)) ⊆ sepColSet a b := by
    intro x hx
    rcases (by simpa using hx : x = j ∨ x = k) with rfl | rfl
    · simp [sepColSet, hj_sep]
    · simp [sepColSet, hk_sep]
  have hle := Finset.card_le_card hsub
  have hpair : ({j, k} : Finset (Fin n)).card = 2 := by
    simpa using Finset.card_pair hkj.symm
  omega

/-- If a triangle avoids a row, it is a triangle inside that row-pattern fibre, so the fibre is non-bipartite. -/
theorem row_fibre_nonbip_of_triangle_avoids_row {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {M0 M1 M2 : MarginClass r s} {L : Fin m}
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2)
    (havoid : ∀ c : Fin n, ¬ DiffTri M0 M1 M2 L c) :
    ¬ ∃ col : {M : MarginClass r s // rowPat L M = rowPat L M0} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowPat L) (rowPat L M0)) col := by
  classical
  have hM1 : rowPat L M1 = rowPat L M0 := by
    funext c
    symm
    by_contra hdiff
    exact havoid c (Or.inl hdiff)
  have hM2 : rowPat L M2 = rowPat L M0 := by
    funext c
    symm
    by_contra hdiff
    exact havoid c (Or.inr (Or.inr hdiff))
  let A : {M : MarginClass r s // rowPat L M = rowPat L M0} := ⟨M0, rfl⟩
  let B : {M : MarginClass r s // rowPat L M = rowPat L M0} := ⟨M1, hM1⟩
  let C : {M : MarginClass r s // rowPat L M = rowPat L M0} := ⟨M2, hM2⟩
  have hAB : (fibreGraph (flipGraph r s) (rowPat L) (rowPat L M0)).Adj A B := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h01
  have hBC : (fibreGraph (flipGraph r s) (rowPat L) (rowPat L M0)).Adj B C := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h12
  have hCA : (fibreGraph (flipGraph r s) (rowPat L) (rowPat L M0)).Adj C A := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h02.symm
  rintro ⟨col, hbip⟩
  exact bipartite_no_triangle hbip hAB hBC hCA

/-- If a triangle avoids a column, it is a triangle inside that column-pattern fibre, so the fibre is non-bipartite. -/
theorem col_fibre_nonbip_of_triangle_avoids_col {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {M0 M1 M2 : MarginClass r s} {C₀ : Fin n}
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2)
    (havoid : ∀ x : Fin m, ¬ DiffTri M0 M1 M2 x C₀) :
    ¬ ∃ col : {M : MarginClass r s // colPat C₀ M = colPat C₀ M0} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (colPat C₀) (colPat C₀ M0)) col := by
  classical
  have hM1 : colPat C₀ M1 = colPat C₀ M0 := by
    funext x
    symm
    by_contra hdiff
    exact havoid x (Or.inl hdiff)
  have hM2 : colPat C₀ M2 = colPat C₀ M0 := by
    funext x
    symm
    by_contra hdiff
    exact havoid x (Or.inr (Or.inr hdiff))
  let A : {M : MarginClass r s // colPat C₀ M = colPat C₀ M0} := ⟨M0, rfl⟩
  let B : {M : MarginClass r s // colPat C₀ M = colPat C₀ M0} := ⟨M1, hM1⟩
  let C : {M : MarginClass r s // colPat C₀ M = colPat C₀ M0} := ⟨M2, hM2⟩
  have hAB : (fibreGraph (flipGraph r s) (colPat C₀) (colPat C₀ M0)).Adj A B := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h01
  have hBC : (fibreGraph (flipGraph r s) (colPat C₀) (colPat C₀ M0)).Adj B C := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h12
  have hCA : (fibreGraph (flipGraph r s) (colPat C₀) (colPat C₀ M0)).Adj C A := by
    rw [fibreGraph, SimpleGraph.induce_adj]
    exact h02.symm
  rintro ⟨col, hbip⟩
  exact bipartite_no_triangle hbip hAB hBC hCA

/-- If no separating line has a non-bipartite fibre, every triangle uses every separating row and column. -/
theorem no_buffer_forces_triangle_uses_sep {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {a b M0 M1 M2 : MarginClass r s}
    (hno : ∀ line : Fin m ⊕ Fin n, lineSeparates a b line → ¬ lineFibreNonbip (r := r) (s := s) line)
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2) :
    (∀ L : Fin m, rowPat L a ≠ rowPat L b → ∃ c : Fin n, DiffTri M0 M1 M2 L c) ∧
      (∀ C : Fin n, colPat C a ≠ colPat C b → ∃ x : Fin m, DiffTri M0 M1 M2 x C) := by
  classical
  constructor
  · intro L hsep
    by_contra hnone
    push_neg at hnone
    exact hno (Sum.inl L) hsep
      ⟨rowPat L M0, row_fibre_nonbip_of_triangle_avoids_row h01 h12 h02 hnone⟩
  · intro C hsep
    by_contra hnone
    push_neg at hnone
    exact hno (Sum.inr C) hsep
      ⟨colPat C M0, col_fibre_nonbip_of_triangle_avoids_col h01 h12 h02 hnone⟩

private theorem sepRowSet_subset_triRows_of_uses {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {a b M0 M1 M2 : MarginClass r s}
    (huses : ∀ L : Fin m, rowPat L a ≠ rowPat L b → ∃ c : Fin n, DiffTri M0 M1 M2 L c) :
    sepRowSet a b ⊆ triRows M0 M1 M2 := by
  intro L hL
  have hsep : rowPat L a ≠ rowPat L b := by
    simpa [sepRowSet] using hL
  rcases huses L hsep with ⟨c, hc⟩
  simp [triRows]
  exact ⟨c, hc⟩

private theorem sepColSet_subset_triCols_of_uses {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {a b M0 M1 M2 : MarginClass r s}
    (huses : ∀ C : Fin n, colPat C a ≠ colPat C b → ∃ x : Fin m, DiffTri M0 M1 M2 x C) :
    sepColSet a b ⊆ triCols M0 M1 M2 := by
  intro C hC
  have hsep : colPat C a ≠ colPat C b := by
    simpa [sepColSet] using hC
  rcases huses C hsep with ⟨x, hx⟩
  simp [triCols]
  exact ⟨x, hx⟩

private theorem triangle_rows_cols_bounds {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {M0 M1 M2 : MarginClass r s}
    (h01 : (flipGraph r s).Adj M0 M1) (h12 : (flipGraph r s).Adj M1 M2)
    (h02 : (flipGraph r s).Adj M0 M2) :
    ((triRows M0 M1 M2).card ≤ 2 ∧ (triCols M0 M1 M2).card ≤ 3) ∨
      ((triRows M0 M1 M2).card ≤ 3 ∧ (triCols M0 M1 M2).card ≤ 2) := by
  classical
  have hi01 := adj_interchange h01
  have hi12 := adj_interchange h12
  have hi02 := adj_interchange h02
  rcases interchange_diffCells_prod hi01 with
    ⟨a1, b1, i1, j1, hab1, hij1, hD01, _⟩
  rcases interchange_diffCells_prod hi12 with
    ⟨a2, b2, i2, j2, hab2, hij2, hD12, _⟩
  let R1 : Finset (Fin m) := {a1, b1}
  let R2 : Finset (Fin m) := {a2, b2}
  let C1 : Finset (Fin n) := {i1, j1}
  let C2 : Finset (Fin n) := {i2, j2}
  have hInter : (R1 ∩ R2).card * (C1 ∩ C2).card = 2 := by
    have hcard := inter_card_eq_two_of_triangle hi01 hi12 hi02
    rw [hD01, hD12, Finset.product_inter_product, Finset.card_product] at hcard
    simpa [R1, R2, C1, C2] using hcard
  have hRle : (R1 ∩ R2).card ≤ 2 := by
    have hR1 : R1.card = 2 := by simpa [R1] using Finset.card_pair hab1
    rw [← hR1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hCle : (C1 ∩ C2).card ≤ 2 := by
    have hC1 : C1.card = 2 := by simpa [C1] using Finset.card_pair hij1
    rw [← hC1]
    exact Finset.card_le_card Finset.inter_subset_left
  have hcases : ((R1 ∩ R2).card = 2 ∧ (C1 ∩ C2).card = 1) ∨
      ((R1 ∩ R2).card = 1 ∧ (C1 ∩ C2).card = 2) := by
    have hRpos : 0 < (R1 ∩ R2).card := by
      by_contra h
      have hz : (R1 ∩ R2).card = 0 := by omega
      rw [hz] at hInter
      norm_num at hInter
    have hCpos : 0 < (C1 ∩ C2).card := by
      by_contra h
      have hz : (C1 ∩ C2).card = 0 := by omega
      rw [hz, Nat.mul_zero] at hInter
      norm_num at hInter
    have hRcases : (R1 ∩ R2).card = 1 ∨ (R1 ∩ R2).card = 2 := by omega
    have hCcases : (C1 ∩ C2).card = 1 ∨ (C1 ∩ C2).card = 2 := by omega
    rcases hRcases with hR | hR <;> rcases hCcases with hC | hC
    · exfalso
      have hbad : (1 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
    · exact Or.inr ⟨hR, hC⟩
    · exact Or.inl ⟨hR, hC⟩
    · exfalso
      have hbad : (4 : ℕ) = 2 := by simpa [hR, hC] using hInter
      omega
  have hRowsSubUnion : triRows M0 M1 M2 ⊆ R1 ∪ R2 := by
    intro x hx
    rcases (by simpa [triRows] using hx : ∃ c : Fin n, DiffTri M0 M1 M2 x c) with ⟨c, hdiff⟩
    have in_R1_of_D01 (hp : (x, c) ∈ diffCells M0.val M1.val) : x ∈ R1 := by
      rw [hD01] at hp
      exact (by simpa [R1, C1] using hp : x ∈ R1 ∧ c ∈ C1).1
    have in_R2_of_D12 (hp : (x, c) ∈ diffCells M1.val M2.val) : x ∈ R2 := by
      rw [hD12] at hp
      exact (by simpa [R2, C2] using hp : x ∈ R2 ∧ c ∈ C2).1
    have in_union_of_D02 (hp : (x, c) ∈ diffCells M0.val M2.val) : x ∈ R1 ∪ R2 := by
      rw [diffCells_triangle M0.val M1.val M2.val, Finset.mem_symmDiff] at hp
      rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩
      · exact Finset.mem_union_left R2 (in_R1_of_D01 hp)
      · exact Finset.mem_union_right R1 (in_R2_of_D12 hp)
    rcases hdiff with h | h | h
    · exact Finset.mem_union_left R2 (in_R1_of_D01 (by simpa [diffCells] using h))
    · exact Finset.mem_union_right R1 (in_R2_of_D12 (by simpa [diffCells] using h))
    · exact in_union_of_D02 (by simpa [diffCells] using h)
  have hColsSubUnion : triCols M0 M1 M2 ⊆ C1 ∪ C2 := by
    intro c hc
    rcases (by simpa [triCols] using hc : ∃ x : Fin m, DiffTri M0 M1 M2 x c) with ⟨x, hdiff⟩
    have in_C1_of_D01 (hp : (x, c) ∈ diffCells M0.val M1.val) : c ∈ C1 := by
      rw [hD01] at hp
      exact (by simpa [R1, C1] using hp : x ∈ R1 ∧ c ∈ C1).2
    have in_C2_of_D12 (hp : (x, c) ∈ diffCells M1.val M2.val) : c ∈ C2 := by
      rw [hD12] at hp
      exact (by simpa [R2, C2] using hp : x ∈ R2 ∧ c ∈ C2).2
    have in_union_of_D02 (hp : (x, c) ∈ diffCells M0.val M2.val) : c ∈ C1 ∪ C2 := by
      rw [diffCells_triangle M0.val M1.val M2.val, Finset.mem_symmDiff] at hp
      rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩
      · exact Finset.mem_union_left C2 (in_C1_of_D01 hp)
      · exact Finset.mem_union_right C1 (in_C2_of_D12 hp)
    rcases hdiff with h | h | h
    · exact Finset.mem_union_left C2 (in_C1_of_D01 (by simpa [diffCells] using h))
    · exact Finset.mem_union_right C1 (in_C2_of_D12 (by simpa [diffCells] using h))
    · exact in_union_of_D02 (by simpa [diffCells] using h)
  rcases hcases with hrow | hcol
  · left
    have hR_eq : R1 = R2 := by
      simpa [R1, R2] using pair_inter_card_two_eq hab1 hrow.1
    have hRowsSub : triRows M0 M1 M2 ⊆ R1 := by
      intro x hx
      have hxU := hRowsSubUnion hx
      simpa [hR_eq] using hxU
    have hRowsLe : (triRows M0 M1 M2).card ≤ 2 := by
      have hle := Finset.card_le_card hRowsSub
      have hR1 : R1.card = 2 := by simpa [R1] using Finset.card_pair hab1
      omega
    have hC1card : C1.card = 2 := by simpa [C1] using Finset.card_pair hij1
    have hC2card : C2.card = 2 := by simpa [C2] using Finset.card_pair hij2
    have hCunion : (C1 ∪ C2).card = 3 := by
      have h := Finset.card_union_add_card_inter C1 C2
      omega
    have hColsLe : (triCols M0 M1 M2).card ≤ 3 := by
      have hle := Finset.card_le_card hColsSubUnion
      omega
    exact ⟨hRowsLe, hColsLe⟩
  · right
    have hC_eq : C1 = C2 := by
      simpa [C1, C2] using pair_inter_card_two_eq hij1 hcol.2
    have hColsSub : triCols M0 M1 M2 ⊆ C1 := by
      intro c hc
      have hcU := hColsSubUnion hc
      simpa [hC_eq] using hcU
    have hColsLe : (triCols M0 M1 M2).card ≤ 2 := by
      have hle := Finset.card_le_card hColsSub
      have hC1 : C1.card = 2 := by simpa [C1] using Finset.card_pair hij1
      omega
    have hR1card : R1.card = 2 := by simpa [R1] using Finset.card_pair hab1
    have hR2card : R2.card = 2 := by simpa [R2] using Finset.card_pair hab2
    have hRunion : (R1 ∪ R2).card = 3 := by
      have h := Finset.card_union_add_card_inter R1 R2
      omega
    have hRowsLe : (triRows M0 M1 M2).card ≤ 3 := by
      have hle := Finset.card_le_card hRowsSubUnion
      omega
    exact ⟨hRowsLe, hColsLe⟩

private theorem row_three_pattern_supports_triangle_supported {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) {u v : Fin m} {i j c : Fin n}
    (huv : u ≠ v) (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (hui : M.val u i = true) (huj : M.val u j = true) (huc : M.val u c = false)
    (hvi : M.val v i = false) (hvj : M.val v j = false) (hvc : M.val v c = true) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        ∀ x d, DiffTri M0 M1 M2 x d → x = u ∨ x = v := by
  classical
  rcases row_three_pattern_supports_triangle M huv hij hic hjc
      hui huj huc hvi hvj hvc with
    ⟨M0, M1, M2, hM0, hM1, hM2, h01, h12, h02⟩
  refine ⟨M0, M1, M2, h01, h12, h02, ?_⟩
  intro x d hdiff
  by_cases hxuv : x = u ∨ x = v
  · exact hxuv
  have hxu : x ≠ u := fun h => hxuv (Or.inl h)
  have hxv : x ≠ v := fun h => hxuv (Or.inr h)
  have h01same : M0.val x d = M1.val x d := by
    rw [hM0, hM1]
    simp [Brualdi.Ryser.switchMat, hxu, hxv]
  have h12same : M1.val x d = M2.val x d := by
    rw [hM1, hM2]
    simp [Brualdi.Ryser.switchMat, hxu, hxv]
  have h02same : M0.val x d = M2.val x d := by
    rw [hM0, hM2]
    simp [Brualdi.Ryser.switchMat, hxu, hxv]
  rcases hdiff with h | h | h
  · exact False.elim (h h01same)
  · exact False.elim (h h12same)
  · exact False.elim (h h02same)

private theorem col_three_pattern_supports_triangle_supported {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) {a b c : Fin m} {u v : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (huv : u ≠ v)
    (hau : M.val a u = true) (hav : M.val a v = false)
    (hbu : M.val b u = true) (hbv : M.val b v = false)
    (hcu : M.val c u = false) (hcv : M.val c v = true) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        ∀ x d, DiffTri M0 M1 M2 x d → d = u ∨ d = v := by
  classical
  rcases col_three_pattern_supports_triangle M hab hac hbc huv
      hau hav hbu hbv hcu hcv with
    ⟨M0, M1, M2, hM0, hM1, hM2, h01, h12, h02⟩
  refine ⟨M0, M1, M2, h01, h12, h02, ?_⟩
  intro x d hdiff
  by_cases hduv : d = u ∨ d = v
  · exact hduv
  have hdu : d ≠ u := fun h => hduv (Or.inl h)
  have hdv : d ≠ v := fun h => hduv (Or.inr h)
  have h01same : M0.val x d = M1.val x d := by
    rw [hM0, hM1]
    simp [Brualdi.Ryser.switchMat, hdu, hdv]
  have h12same : M1.val x d = M2.val x d := by
    rw [hM1, hM2]
    simp [Brualdi.Ryser.switchMat, hdu, hdv]
  have h02same : M0.val x d = M2.val x d := by
    rw [hM0, hM2]
    simp [Brualdi.Ryser.switchMat, hdu, hdv]
  rcases hdiff with h | h | h
  · exact False.elim (h h01same)
  · exact False.elim (h h12same)
  · exact False.elim (h h02same)

private theorem wide_row_pair_supports_triangle_supported {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {p q : Fin m}
    (hwide : WideRowPair r s p q) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        ∀ x c, DiffTri M0 M1 M2 x c → x ∈ ({p, q} : Finset (Fin m)) := by
  rcases hwide with ⟨hpq, M, htf, hft, hcard⟩
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)
  let B : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = false ∧ M.val q c = true)
  let D : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c ≠ M.val q c)
  have hD_eq : D = A ∪ B := by
    ext c
    simp only [D, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hp : M.val p c <;> cases hq : M.val q c <;> simp [hp, hq]
  have hDcard : 3 ≤ D.card := by
    simpa [D] using hcard
  have hwide_or : 1 < A.card ∨ 1 < B.card := by
    by_contra h
    push_neg at h
    have hle_union : D.card ≤ A.card + B.card := by
      rw [hD_eq]
      exact Finset.card_union_le A B
    have hle_two : D.card ≤ 2 := by omega
    omega
  rcases hwide_or with hA | hB
  · rcases (Finset.one_lt_card.mp hA) with ⟨i, hiA, j, hjA, hij⟩
    rcases hft with ⟨c, hpc, hqc⟩
    have hi : M.val p i = true ∧ M.val q i = false := by simpa [A] using hiA
    have hj : M.val p j = true ∧ M.val q j = false := by simpa [A] using hjA
    have hic : i ≠ c := by
      intro h
      rw [h] at hi
      rw [hpc] at hi
      exact Bool.false_ne_true hi.1
    have hjc : j ≠ c := by
      intro h
      rw [h] at hj
      rw [hpc] at hj
      exact Bool.false_ne_true hj.1
    rcases row_three_pattern_supports_triangle_supported M hpq hij hic hjc
        hi.1 hj.1 hpc hi.2 hj.2 hqc with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    exact ⟨M0, M1, M2, h01, h12, h02, by
      intro x d hdiff
      rcases hsupp x d hdiff with rfl | rfl <;> simp⟩
  · rcases (Finset.one_lt_card.mp hB) with ⟨i, hiB, j, hjB, hij⟩
    rcases htf with ⟨c, hpc, hqc⟩
    have hi : M.val p i = false ∧ M.val q i = true := by simpa [B] using hiB
    have hj : M.val p j = false ∧ M.val q j = true := by simpa [B] using hjB
    have hic : i ≠ c := by
      intro h
      rw [h] at hi
      rw [hpc] at hi
      exact Bool.false_ne_true hi.1.symm
    have hjc : j ≠ c := by
      intro h
      rw [h] at hj
      rw [hpc] at hj
      exact Bool.false_ne_true hj.1.symm
    rcases row_three_pattern_supports_triangle_supported M hpq.symm hij hic hjc
        hi.2 hj.2 hqc hi.1 hj.1 hpc with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    exact ⟨M0, M1, M2, h01, h12, h02, by
      intro x d hdiff
      rcases hsupp x d hdiff with rfl | rfl <;> simp⟩

private theorem wide_col_pair_supports_triangle_supported {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ} {i j : Fin n}
    (hwide : WideColPair r s i j) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧
        (flipGraph r s).Adj M0 M2 ∧
        ∀ x c, DiffTri M0 M1 M2 x c → c ∈ ({i, j} : Finset (Fin n)) := by
  rcases hwide with ⟨hij, M, htf, hft, hcard⟩
  classical
  let A : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i = true ∧ M.val x j = false)
  let B : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i = false ∧ M.val x j = true)
  let D : Finset (Fin m) :=
    Finset.univ.filter (fun x => M.val x i ≠ M.val x j)
  have hD_eq : D = A ∪ B := by
    ext x
    simp only [D, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hi : M.val x i <;> cases hj : M.val x j <;> simp [hi, hj]
  have hDcard : 3 ≤ D.card := by
    simpa [D] using hcard
  have hwide_or : 1 < A.card ∨ 1 < B.card := by
    by_contra h
    push_neg at h
    have hle_union : D.card ≤ A.card + B.card := by
      rw [hD_eq]
      exact Finset.card_union_le A B
    have hle_two : D.card ≤ 2 := by omega
    omega
  rcases hwide_or with hA | hB
  · rcases (Finset.one_lt_card.mp hA) with ⟨a, haA, b, hbA, hab⟩
    rcases hft with ⟨c, hci, hcj⟩
    have ha : M.val a i = true ∧ M.val a j = false := by simpa [A] using haA
    have hb : M.val b i = true ∧ M.val b j = false := by simpa [A] using hbA
    have hac : a ≠ c := by
      intro h
      rw [h] at ha
      rw [hci] at ha
      exact Bool.false_ne_true ha.1
    have hbc : b ≠ c := by
      intro h
      rw [h] at hb
      rw [hci] at hb
      exact Bool.false_ne_true hb.1
    rcases col_three_pattern_supports_triangle_supported M hab hac hbc hij
        ha.1 ha.2 hb.1 hb.2 hci hcj with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    exact ⟨M0, M1, M2, h01, h12, h02, by
      intro x d hdiff
      rcases hsupp x d hdiff with rfl | rfl <;> simp⟩
  · rcases (Finset.one_lt_card.mp hB) with ⟨a, haB, b, hbB, hab⟩
    rcases htf with ⟨c, hci, hcj⟩
    have ha : M.val a i = false ∧ M.val a j = true := by simpa [B] using haB
    have hb : M.val b i = false ∧ M.val b j = true := by simpa [B] using hbB
    have hac : a ≠ c := by
      intro h
      rw [h] at ha
      rw [hci] at ha
      exact Bool.false_ne_true ha.1.symm
    have hbc : b ≠ c := by
      intro h
      rw [h] at hb
      rw [hci] at hb
      exact Bool.false_ne_true hb.1.symm
    rcases col_three_pattern_supports_triangle_supported M hab hac hbc hij.symm
        ha.2 ha.1 hb.2 hb.1 hcj hci with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    exact ⟨M0, M1, M2, h01, h12, h02, by
      intro x d hdiff
      rcases hsupp x d hdiff with rfl | rfl <;> simp⟩

/-- The residue alternatives left after the no-buffer triangle case analysis. -/
def ResidueCases {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (a b : MarginClass r s) : Prop :=
  ((sepRowSet a b).card = 2 ∧ (sepColSet a b).card = 2) ∨
  ((sepRowSet a b).card = 2 ∧ (sepColSet a b).card = 3) ∨
  ((sepRowSet a b).card = 3 ∧ (sepColSet a b).card = 2)

/-- Stage A residue case split for Lemma 5.11 (buffer existence) under the no-buffer hypothesis. -/
theorem residue_cases_of_no_buffer {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hprime : ¬ IsDecomposable (flipGraph r s))
    (hnb : ¬ ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col)
    (a b : MarginClass r s) (hab : a ≠ b)
    (hno : ∀ line : Fin m ⊕ Fin n, lineSeparates a b line → ¬ lineFibreNonbip (r := r) (s := s) line) :
    ResidueCases a b := by
  classical
  rcases nonbip_has_triangle r s hact hprime hnb with ⟨M0, M1, M2, h01, h12, h02⟩
  have _huses := no_buffer_forces_triangle_uses_sep (a := a) (b := b)
    (M0 := M0) (M1 := M1) (M2 := M2) hno h01 h12 h02
  have _hclass := triangle_classification h01 h12 h02
  have _hrow_ge := sepRowSet_card_ge_two (a := a) (b := b) hab
  have _hcol_ge := sepColSet_card_ge_two (a := a) (b := b) hab
  have hRsub : sepRowSet a b ⊆ triRows M0 M1 M2 :=
    sepRowSet_subset_triRows_of_uses _huses.1
  have hCsub : sepColSet a b ⊆ triCols M0 M1 M2 :=
    sepColSet_subset_triCols_of_uses _huses.2
  have hR_le_tri : (sepRowSet a b).card ≤ (triRows M0 M1 M2).card :=
    Finset.card_le_card hRsub
  have hC_le_tri : (sepColSet a b).card ≤ (triCols M0 M1 M2).card :=
    Finset.card_le_card hCsub
  rcases triangle_rows_cols_bounds h01 h12 h02 with hrow | hcol
  · have hR_le_two : (sepRowSet a b).card ≤ 2 := hR_le_tri.trans hrow.1
    have hC_le_three : (sepColSet a b).card ≤ 3 := hC_le_tri.trans hrow.2
    have hR_eq_two : (sepRowSet a b).card = 2 := by omega
    have hC_cases : (sepColSet a b).card = 2 ∨ (sepColSet a b).card = 3 := by omega
    rcases hC_cases with hC_eq_two | hC_eq_three
    · exact Or.inl ⟨hR_eq_two, hC_eq_two⟩
    · exact Or.inr (Or.inl ⟨hR_eq_two, hC_eq_three⟩)
  · have hR_le_three : (sepRowSet a b).card ≤ 3 := hR_le_tri.trans hcol.1
    have hC_le_two : (sepColSet a b).card ≤ 2 := hC_le_tri.trans hcol.2
    have hC_eq_two : (sepColSet a b).card = 2 := by omega
    have hR_cases : (sepRowSet a b).card = 2 ∨ (sepRowSet a b).card = 3 := by omega
    rcases hR_cases with hR_eq_two | hR_eq_three
    · exact Or.inl ⟨hR_eq_two, hC_eq_two⟩
    · exact Or.inr (Or.inr ⟨hR_eq_three, hC_eq_two⟩)

/-- Under the Stage A residue alternatives, wide row pairs have a unique two-row support. -/
theorem atMostOne_wide_row_pair {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {a b : MarginClass r s}
    (hno : ∀ line : Fin m ⊕ Fin n, lineSeparates a b line → ¬ lineFibreNonbip (r := r) (s := s) line)
    (hres : ResidueCases a b) :
    ∀ p q p' q' : Fin m, WideRowPair r s p q → WideRowPair r s p' q' →
      ({p, q} : Finset (Fin m)) = ({p', q'} : Finset (Fin m)) := by
  classical
  intro p q p' q' hpq hpq'
  have hsep_card_ge : 2 ≤ (sepRowSet a b).card := by
    rcases hres with h22 | h23 | h32
    · rw [h22.1]
    · rw [h23.1]
    · rw [h32.1]
      omega
  have sep_eq_pair :
      ∀ x y : Fin m, WideRowPair r s x y →
        sepRowSet a b = ({x, y} : Finset (Fin m)) := by
    intro x y hxy
    rcases wide_row_pair_supports_triangle_supported hxy with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    have huses := no_buffer_forces_triangle_uses_sep (a := a) (b := b)
      (M0 := M0) (M1 := M1) (M2 := M2) hno h01 h12 h02
    have hRsubTri : sepRowSet a b ⊆ triRows M0 M1 M2 :=
      sepRowSet_subset_triRows_of_uses huses.1
    have hTriSubPair : triRows M0 M1 M2 ⊆ ({x, y} : Finset (Fin m)) := by
      intro z hz
      rcases (by simpa [triRows] using hz : ∃ c : Fin n, DiffTri M0 M1 M2 z c) with
        ⟨c, hc⟩
      exact hsupp z c hc
    have hsub : sepRowSet a b ⊆ ({x, y} : Finset (Fin m)) :=
      fun z hz => hTriSubPair (hRsubTri hz)
    have hpair : ({x, y} : Finset (Fin m)).card = 2 := Finset.card_pair hxy.1
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [hpair]
      exact hsep_card_ge)
  exact (sep_eq_pair p q hpq).symm.trans (sep_eq_pair p' q' hpq')

/-- Under the Stage A residue alternatives, wide column pairs have a unique two-column support. -/
theorem atMostOne_wide_col_pair {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    {a b : MarginClass r s}
    (hno : ∀ line : Fin m ⊕ Fin n, lineSeparates a b line → ¬ lineFibreNonbip (r := r) (s := s) line)
    (hres : ResidueCases a b) :
    ∀ i j i' j' : Fin n, WideColPair r s i j → WideColPair r s i' j' →
      ({i, j} : Finset (Fin n)) = ({i', j'} : Finset (Fin n)) := by
  classical
  intro i j i' j' hij hij'
  have hsep_card_ge : 2 ≤ (sepColSet a b).card := by
    rcases hres with h22 | h23 | h32
    · rw [h22.2]
    · rw [h23.2]
      omega
    · rw [h32.2]
  have sep_eq_pair :
      ∀ x y : Fin n, WideColPair r s x y →
        sepColSet a b = ({x, y} : Finset (Fin n)) := by
    intro x y hxy
    rcases wide_col_pair_supports_triangle_supported hxy with
      ⟨M0, M1, M2, h01, h12, h02, hsupp⟩
    have huses := no_buffer_forces_triangle_uses_sep (a := a) (b := b)
      (M0 := M0) (M1 := M1) (M2 := M2) hno h01 h12 h02
    have hCsubTri : sepColSet a b ⊆ triCols M0 M1 M2 :=
      sepColSet_subset_triCols_of_uses huses.2
    have hTriSubPair : triCols M0 M1 M2 ⊆ ({x, y} : Finset (Fin n)) := by
      intro z hz
      rcases (by simpa [triCols] using hz : ∃ row : Fin m, DiffTri M0 M1 M2 row z) with
        ⟨row, hrow⟩
      exact hsupp row z hrow
    have hsub : sepColSet a b ⊆ ({x, y} : Finset (Fin n)) :=
      fun z hz => hTriSubPair (hCsubTri hz)
    have hpair : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair hxy.1
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [hpair]
      exact hsep_card_ge)
  exact (sep_eq_pair i j hij).symm.trans (sep_eq_pair i' j' hij')

private theorem mixed_switch_second_wide_row {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q x' : Fin m} {j j' : Fin n}
    (hpq : p ≠ q) (hx'p : x' ≠ p) (hx'q : x' ≠ q) (hjj : j ≠ j')
    (N N' : MarginClass r s)
    (hNpj : N.val p j = true) (hNx'j' : N.val x' j' = true)
    (hNpj' : N.val p j' = false) (hNx'j : N.val x' j = false)
    (hN'x'j : N'.val x' j = true) (hN'x'j' : N'.val x' j' = false)
    (hout : ∀ a b, ¬ ((a = p ∨ a = x') ∧ (b = j ∨ b = j')) →
      N'.val a b = N.val a b)
    (hrow_unique :
      ∀ a b a' b' : Fin m, WideRowPair r s a b → WideRowPair r s a' b' →
        ({a, b} : Finset (Fin m)) = ({a', b'} : Finset (Fin m)))
    (hNwide :
      (∃ c, N.val p c = true ∧ N.val q c = false) ∧
      (∃ c, N.val p c = false ∧ N.val q c = true) ∧
      3 ≤ (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)).card) :
    WideRowPair r s x' q := by
  classical
  -- L1: a switch on rows {p, x'} (x' ∉ {p,q}) transports the wide witness (p,q) → (x',q).
  have hqp : q ≠ p := Ne.symm hpq
  have hqx' : q ≠ x' := Ne.symm hx'q
  -- q is untouched by the switch (q ∉ {p, x'})
  have hNq : ∀ c, N'.val q c = N.val q c := by
    intro c
    refine hout q c ?_
    rintro ⟨hrow, -⟩
    rcases hrow with h | h
    · exact hqp h
    · exact hqx' h
  have hpqwide : WideRowPair r s p q := ⟨hpq, N, hNwide.1, hNwide.2.1, hNwide.2.2⟩
  -- {p, x'} is not wide (else a second wide row pair contradicts uniqueness)
  have hnpx' : ¬ WideRowPair r s p x' := by
    intro hw
    have hset := hrow_unique p q p x' hpqwide hw
    have hqmem : q ∈ ({p, x'} : Finset (Fin m)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
    rcases hqmem with h | h
    · exact hqp h
    · exact hqx' h
  -- p and x' are incomparable in N (checkerboard) but not wide, so they differ in ≤ 2 columns
  have hcard_le :
      (Finset.univ.filter (fun c => N.val p c ≠ N.val x' c)).card ≤ 2 := by
    by_contra h
    push_neg at h
    exact hnpx' ⟨Ne.symm hx'p, N, ⟨j, hNpj, hNx'j⟩, ⟨j', hNpj', hNx'j'⟩, by omega⟩
  -- hence they agree off {j, j'}
  have hagree : ∀ c, c ≠ j → c ≠ j' → N.val p c = N.val x' c := by
    intro c hcj hcj'
    by_contra hne
    have hjc : j ∉ ({j', c} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
      exact ⟨hjj, Ne.symm hcj⟩
    have hj'c : j' ∉ ({c} : Finset (Fin n)) := by
      simp only [Finset.mem_singleton]; exact Ne.symm hcj'
    have hcard3 : ({j, j', c} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem hjc, Finset.card_insert_of_notMem hj'c,
        Finset.card_singleton]
    have hsub : ({j, j', c} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun c => N.val p c ≠ N.val x' c) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · simp [hNpj, hNx'j]
      · simp [hNpj', hNx'j']
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hne
    have := Finset.card_le_card hsub
    rw [hcard3] at this
    omega
  -- therefore row x' in N' equals row p in N, everywhere
  have hx'copy : ∀ c, N'.val x' c = N.val p c := by
    intro c
    by_cases hcj : c = j
    · subst c; rw [hN'x'j, hNpj]
    · by_cases hcj' : c = j'
      · subst c; rw [hN'x'j', hNpj']
      · have h1 : N'.val x' c = N.val x' c := by
          refine hout x' c ?_
          rintro ⟨-, hb⟩
          rcases hb with h | h
          · exact hcj h
          · exact hcj' h
        rw [h1, ← hagree c hcj hcj']
  -- {x', q} is a second wide row pair, witnessed by N'
  refine ⟨hx'q, N', ?_, ?_, ?_⟩
  · obtain ⟨c, hpc, hqc⟩ := hNwide.1
    exact ⟨c, by rw [hx'copy c]; exact hpc, by rw [hNq c]; exact hqc⟩
  · obtain ⟨c, hpc, hqc⟩ := hNwide.2.1
    exact ⟨c, by rw [hx'copy c]; exact hpc, by rw [hNq c]; exact hqc⟩
  · have heq :
        (Finset.univ.filter (fun c => N'.val x' c ≠ N'.val q c)) =
          (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) := by
      ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx'copy c, hNq c]
    rw [heq]; exact hNwide.2.2

private theorem pq_switch_preserves_ordered {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q : Fin m} {j j' : Fin n}
    (hpq : p ≠ q) (hjj : j ≠ j') (N N' : MarginClass r s)
    (hNpj : N.val p j = true) (hNqj' : N.val q j' = true)
    (hNpj' : N.val p j' = false) (hNqj : N.val q j = false)
    (hN'pj : N'.val p j = false) (hN'qj' : N'.val q j' = false)
    (hN'pj' : N'.val p j' = true) (hN'qj : N'.val q j = true)
    (hout : ∀ a b, ¬ ((a = p ∨ a = q) ∧ (b = j ∨ b = j')) →
      N'.val a b = N.val a b) :
    (Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
      (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) ∧
    (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
      (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card ∧
    ∀ z c, z ≠ p → z ≠ q → N'.val z c = N.val z c := by
  classical
  let A : Finset (Fin n) :=
    Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)
  let A' : Finset (Fin n) :=
    Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)
  have hdiff :
      (Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
        (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) := by
    ext c
    by_cases hcj : c = j
    · subst c
      simp [hNpj, hNqj, hN'pj, hN'qj]
    · by_cases hcj' : c = j'
      · subst c
        simp [hNpj', hNqj', hN'pj', hN'qj']
      · have hp_same : N'.val p c = N.val p c := hout p c (by
          intro hblock
          exact hblock.2.elim hcj hcj')
        have hq_same : N'.val q c = N.val q c := hout q c (by
          intro hblock
          exact hblock.2.elim hcj hcj')
        simp [hp_same, hq_same]
  have hAj : j ∈ A := by
    simp [A, hNpj, hNqj]
  have hA'j' : j' ∈ A' := by
    simp [A', hN'pj', hN'qj']
  have herase : A.erase j = A'.erase j' := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_erase.mp hc with ⟨hcne_j, hcA⟩
      have hcne_j' : c ≠ j' := by
        intro hcj'
        subst c
        have hbad := (Finset.mem_filter.mp hcA).2.1
        rw [hNpj'] at hbad
        exact Bool.false_ne_true hbad
      have hp_same : N'.val p c = N.val p c := hout p c (by
        intro hblock
        exact hblock.2.elim hcne_j hcne_j')
      have hq_same : N'.val q c = N.val q c := hout q c (by
        intro hblock
        exact hblock.2.elim hcne_j hcne_j')
      refine Finset.mem_erase.mpr ⟨hcne_j', ?_⟩
      rcases (Finset.mem_filter.mp hcA).2 with ⟨hp, hq⟩
      simp [A', hp_same, hq_same, hp, hq]
    · intro hc
      rcases Finset.mem_erase.mp hc with ⟨hcne_j', hcA'⟩
      have hcne_j : c ≠ j := by
        intro hcj
        subst c
        have hbad := (Finset.mem_filter.mp hcA').2.1
        rw [hN'pj] at hbad
        exact Bool.false_ne_true hbad
      have hp_same : N'.val p c = N.val p c := hout p c (by
        intro hblock
        exact hblock.2.elim hcne_j hcne_j')
      have hq_same : N'.val q c = N.val q c := hout q c (by
        intro hblock
        exact hblock.2.elim hcne_j hcne_j')
      refine Finset.mem_erase.mpr ⟨hcne_j, ?_⟩
      rcases (Finset.mem_filter.mp hcA').2 with ⟨hp, hq⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ c, ⟨hp_same.symm.trans hp, hq_same.symm.trans hq⟩⟩
  have hcardA := Finset.card_erase_add_one hAj
  have hcardA' := Finset.card_erase_add_one hA'j'
  have hcard :
      A'.card = A.card := by
    have herase_card : (A.erase j).card = (A'.erase j').card := by
      rw [herase]
    omega
  refine ⟨hdiff, ?_, ?_⟩
  · simpa [A, A'] using hcard
  · intro z c hzp hzq
    exact hout z c (by
      intro hblock
      rcases hblock.1 with hz | hz
      · exact hzp hz
      · exact hzq hz)

private theorem pq_switch_preserves {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q i i' : Fin m} {j j' : Fin n}
    (hpq : p ≠ q) (N N' : MarginClass r s)
    (hrows : ({i, i'} : Finset (Fin m)) = ({p, q} : Finset (Fin m)))
    (hii : i ≠ i') (hjj : j ≠ j')
    (hNij : N.val i j = true) (hNi'j' : N.val i' j' = true)
    (hNij' : N.val i j' = false) (hNi'j : N.val i' j = false)
    (hN'ij : N'.val i j = false) (hN'i'j' : N'.val i' j' = false)
    (hN'ij' : N'.val i j' = true) (hN'i'j : N'.val i' j = true)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) →
      N'.val a b = N.val a b) :
    (Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
      (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) ∧
    (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
      (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card ∧
    ∀ z c, z ≠ p → z ≠ q → N'.val z c = N.val z c := by
  classical
  have hp_mem : p = i ∨ p = i' := by
    have hp : p ∈ ({i, i'} : Finset (Fin m)) := by
      rw [hrows]
      simp [hpq]
    simpa using hp
  have hq_mem : q = i ∨ q = i' := by
    have hq : q ∈ ({i, i'} : Finset (Fin m)) := by
      rw [hrows]
      simp [hpq.symm]
    simpa using hq
  rcases hp_mem with hp_i | hp_i'
  · rcases hq_mem with hq_i | hq_i'
    · exact False.elim (hpq (hp_i.trans hq_i.symm))
    · exact pq_switch_preserves_ordered (p := p) (q := q) hpq hjj N N'
        (by simpa [hp_i] using hNij)
        (by simpa [hq_i'] using hNi'j')
        (by simpa [hp_i] using hNij')
        (by simpa [hq_i'] using hNi'j)
        (by simpa [hp_i] using hN'ij)
        (by simpa [hq_i'] using hN'i'j')
        (by simpa [hp_i] using hN'ij')
        (by simpa [hq_i'] using hN'i'j)
        (by
          intro a b hnot
          exact hout a b (by
            intro hblock
            apply hnot
            rcases hblock with ⟨hr, hc⟩
            constructor
            · rcases hr with hr | hr
              · exact Or.inl (hr.trans hp_i.symm)
              · exact Or.inr (hr.trans hq_i'.symm)
            · exact hc))
  · rcases hq_mem with hq_i | hq_i'
    · exact pq_switch_preserves_ordered (p := p) (q := q) hpq hjj.symm N N'
        (by simpa [hp_i'] using hNi'j')
        (by simpa [hq_i] using hNij)
        (by simpa [hp_i'] using hNi'j)
        (by simpa [hq_i] using hNij')
        (by simpa [hp_i'] using hN'i'j')
        (by simpa [hq_i] using hN'ij)
        (by simpa [hp_i'] using hN'i'j)
        (by simpa [hq_i] using hN'ij')
        (by
          intro a b hnot
          exact hout a b (by
            intro hblock
            apply hnot
            rcases hblock with ⟨hr, hc⟩
            constructor
            · rcases hr with hr | hr
              · exact Or.inr (hr.trans hq_i.symm)
              · exact Or.inl (hr.trans hp_i'.symm)
            · rcases hc with hc | hc
              · exact Or.inr hc
              · exact Or.inl hc))
    · exact False.elim (hpq (hp_i'.trans hq_i'.symm))

private theorem outside_switch_preserves {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q i i' : Fin m} {j j' : Fin n}
    (N N' : MarginClass r s)
    (hi_p : i ≠ p) (hi_q : i ≠ q) (hi'_p : i' ≠ p) (hi'_q : i' ≠ q)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) →
      N'.val a b = N.val a b) :
    ∀ c, N'.val p c = N.val p c ∧ N'.val q c = N.val q c := by
  classical
  intro c
  constructor
  · exact hout p c (by
      intro hblock
      rcases hblock.1 with hp | hp
      · exact hi_p hp.symm
      · exact hi'_p hp.symm)
  · exact hout q c (by
      intro hblock
      rcases hblock.1 with hq | hq
      · exact hi_q hq.symm
      · exact hi'_q hq.symm)

private theorem not_wide_col_outside_equal {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q z : Fin m} {c d : Fin n} (N : MarginClass r s)
    (hcd : c ≠ d)
    (hpc : N.val p c = true) (hpd : N.val p d = false)
    (hqc : N.val q c = false) (hqd : N.val q d = true)
    (hnot : ¬ WideColPair r s c d)
    (hzp : z ≠ p) (hzq : z ≠ q) :
    N.val z c = N.val z d := by
  classical
  by_contra hneq
  apply hnot
  refine ⟨hcd, N, ?_, ?_, ?_⟩
  · exact ⟨p, hpc, hpd⟩
  · exact ⟨q, hqc, hqd⟩
  · let T : Finset (Fin m) := {p, q, z}
    have hpq : p ≠ q := by
      intro hpq
      rw [hpq] at hpc
      rw [hqc] at hpc
      exact Bool.false_ne_true hpc
    have hTcard : T.card = 3 := by
      simp [T, hpq, hpq.symm, hzp, hzp.symm, hzq, hzq.symm]
    have hTsub : T ⊆ Finset.univ.filter (fun x => N.val x c ≠ N.val x d) := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simp [hpc, hpd]
      · simp [hqc, hqd]
      · simpa using hneq
    have hle := Finset.card_le_card hTsub
    omega

private theorem exists_not_mem_pair_of_card_three {m : ℕ}
    (_hm : 3 ≤ m) {p q : Fin m} (hpq : p ≠ q) :
    ∃ x : Fin m, x ∉ ({p, q} : Finset (Fin m)) := by
  classical
  by_contra hnone
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ ({p, q} : Finset (Fin m)) := by
    intro x _hx
    by_contra hx
    exact hnone ⟨x, hx⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({p, q} : Finset (Fin m)).card = 2 := Finset.card_pair hpq
  rw [Finset.card_univ, Fintype.card_fin, hpair] at hle
  omega

private theorem exists_mem_sdiff_of_card_ge_three_card_le_two {α : Type*} [DecidableEq α]
    {A B : Finset α} (hA : 3 ≤ A.card) (hB : B.card ≤ 2) :
    ∃ x : α, x ∈ A \ B := by
  classical
  by_contra hnone
  have hsub : A ⊆ B := by
    intro x hxA
    by_contra hxB
    exact hnone ⟨x, Finset.mem_sdiff.mpr ⟨hxA, hxB⟩⟩
  have hle := Finset.card_le_card hsub
  omega

private theorem row_switch_cases {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    {p q x i i' : Fin m} {d j j' : Fin n}
    {V : Finset (Fin n)}
    (hpq : p ≠ q) (hxp : x ≠ p) (hxq : x ≠ q) (hii : i ≠ i') (hjj : j ≠ j')
    (M N N' : MarginClass r s)
    (hM_A : ∃ c, M.val p c = true ∧ M.val q c = false)
    (hM_B : ∃ c, M.val p c = false ∧ M.val q c = true)
    (hM_card : 3 ≤ (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)).card)
    (hN_D :
      (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) =
        (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)))
    (hN_A :
      (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card =
        (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card)
    (hN_xd : N.val x d = M.val x d)
    (hN'not :
      ¬ ((Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
            (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)) ∧
          (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
            (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card ∧
          N'.val x d = M.val x d))
    (hdD0 : M.val p d ≠ M.val q d)
    (hV_support :
      ∀ c d : Fin n, WideColPair r s c d →
        ({c, d} : Finset (Fin n)) = V)
    (hdV' : d ∉ V)
    (hrow_unique :
      ∀ a b a' b' : Fin m, WideRowPair r s a b → WideRowPair r s a' b' →
        ({a, b} : Finset (Fin m)) = ({a', b'} : Finset (Fin m)))
    (hcol_unique :
      ∀ c d c' d' : Fin n, WideColPair r s c d → WideColPair r s c' d' →
        ({c, d} : Finset (Fin n)) = ({c', d'} : Finset (Fin n)))
    (hNij : N.val i j = true) (hNi'j' : N.val i' j' = true)
    (hNij' : N.val i j' = false) (hNi'j : N.val i' j = false)
    (hN'ij : N'.val i j = false) (hN'i'j' : N'.val i' j' = false)
    (hN'ij' : N'.val i j' = true) (hN'i'j : N'.val i' j = true)
    (hout : ∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) →
      N'.val a b = N.val a b) :
    False := by
  classical
  let P : Finset (Fin m) := {p, q}
  let AN : Finset (Fin n) :=
    Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)
  let DN : Finset (Fin n) :=
    Finset.univ.filter (fun c => N.val p c ≠ N.val q c)
  let AM : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)
  let DM : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c ≠ M.val q c)
  have hAN_ex : ∃ c, N.val p c = true ∧ N.val q c = false := by
    have hAM_nonempty : AM.Nonempty := by
      rcases hM_A with ⟨c, hc⟩
      exact ⟨c, by simpa [AM] using hc⟩
    have hAN_card_pos : 0 < AN.card := by
      have hAM_card_pos : 0 < AM.card := Finset.card_pos.mpr hAM_nonempty
      simpa [AN, AM] using hAM_card_pos.trans_eq hN_A.symm
    rcases Finset.card_pos.mp hAN_card_pos with ⟨c, hc⟩
    exact ⟨c, by simpa [AN] using hc⟩
  have hBN_ex : ∃ c, N.val p c = false ∧ N.val q c = true := by
    by_contra hno
    have hAN_sub_DN : AN ⊆ DN := by
      intro c hc
      rcases (by simpa [AN] using hc : N.val p c = true ∧ N.val q c = false) with ⟨hp, hq⟩
      exact by
        simp [DN, hp, hq]
    have hDN_sub_AN : DN ⊆ AN := by
      intro c hc
      have hdiff : N.val p c ≠ N.val q c :=
        (by simpa [DN] using hc)
      cases hp : N.val p c <;> cases hq : N.val q c
      · exact False.elim (hdiff (by simp [hp, hq]))
      · exact False.elim (hno ⟨c, hp, hq⟩)
      · simp [AN, hp, hq]
      · exact False.elim (hdiff (by simp [hp, hq]))
    have hANeqDN : AN = DN := Finset.Subset.antisymm hAN_sub_DN hDN_sub_AN
    have hAM_sub_DM : AM ⊆ DM := by
      intro c hc
      rcases (by simpa [AM] using hc : M.val p c = true ∧ M.val q c = false) with ⟨hp, hq⟩
      simp [DM, hp, hq]
    have hAM_ssub_DM : AM ⊂ DM := by
      rcases hM_B with ⟨c, hpc, hqc⟩
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hAM_sub_DM, ?_⟩
      intro heq
      have hcDM : c ∈ DM := by
        simp [DM, hpc, hqc]
      have hcAM : c ∈ AM := by
        simpa [heq] using hcDM
      have hbad : M.val p c = true := (by simpa [AM] using hcAM : M.val p c = true ∧ M.val q c = false).1
      rw [hpc] at hbad
      exact Bool.false_ne_true hbad
    have hAMltDM : AM.card < DM.card := Finset.card_lt_card hAM_ssub_DM
    have hDNcard : DN.card = DM.card := by
      simpa [DN, DM] using congrArg Finset.card hN_D
    have hANcard : AN.card = AM.card := by
      simpa [AN, AM] using hN_A
    have hcard_eq : AM.card = DM.card := by
      calc
        AM.card = AN.card := hANcard.symm
        _ = DN.card := congrArg Finset.card hANeqDN
        _ = DM.card := hDNcard
    omega
  have hNwide_pq :
      (∃ c, N.val p c = true ∧ N.val q c = false) ∧
      (∃ c, N.val p c = false ∧ N.val q c = true) ∧
      3 ≤ (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)).card := by
    exact ⟨hAN_ex, hBN_ex, by simpa [DN, DM] using hM_card.trans_eq (congrArg Finset.card hN_D).symm⟩
  have hNwide_qp :
      (∃ c, N.val q c = true ∧ N.val p c = false) ∧
      (∃ c, N.val q c = false ∧ N.val p c = true) ∧
      3 ≤ (Finset.univ.filter (fun c => N.val q c ≠ N.val p c)).card := by
    refine ⟨?_, ?_, ?_⟩
    · rcases hBN_ex with ⟨c, hp, hq⟩
      exact ⟨c, hq, hp⟩
    · rcases hAN_ex with ⟨c, hp, hq⟩
      exact ⟨c, hq, hp⟩
    · have heq :
          (Finset.univ.filter (fun c => N.val q c ≠ N.val p c)) =
            (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ne_comm
      rw [heq]
      exact hNwide_pq.2.2
  by_cases hiP : i ∈ P
  · by_cases hi'P : i' ∈ P
    · have hrows : ({i, i'} : Finset (Fin m)) = ({p, q} : Finset (Fin m)) := by
        have hsub : ({i, i'} : Finset (Fin m)) ⊆ ({p, q} : Finset (Fin m)) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simpa [P] using hiP
          · simpa [P] using hi'P
        have hcard : ({p, q} : Finset (Fin m)).card ≤ ({i, i'} : Finset (Fin m)).card := by
          rw [Finset.card_pair hpq, Finset.card_pair hii]
        exact Finset.eq_of_subset_of_card_le hsub hcard
      have hpres := pq_switch_preserves (p := p) (q := q) (i := i) (i' := i')
        (j := j) (j' := j') hpq N N' hrows hii hjj hNij hNi'j' hNij' hNi'j
        hN'ij hN'i'j' hN'ij' hN'i'j hout
      exact hN'not ⟨by rw [hpres.1, hN_D], by rw [hpres.2.1, hN_A],
        by rw [hpres.2.2 x d hxp hxq, hN_xd]⟩
    · have hi'_p : i' ≠ p := by
        intro hip
        exact hi'P (by simp [P, hip])
      have hi'_q : i' ≠ q := by
        intro hiq
        exact hi'P (by simp [P, hiq])
      have hi_eq : i = p ∨ i = q := by
        simpa [P] using hiP
      rcases hi_eq with hip | hiq
      · subst i
        have hw2 : WideRowPair r s i' q :=
          mixed_switch_second_wide_row (p := p) (q := q) (x' := i') (j := j) (j' := j')
            hpq hi'_p hi'_q hjj N N' hNij hNi'j' hNij' hNi'j
            hN'i'j hN'i'j' hout hrow_unique hNwide_pq
        have hw1 : WideRowPair r s p q :=
          ⟨hpq, N, hNwide_pq.1, hNwide_pq.2.1, hNwide_pq.2.2⟩
        have hset := hrow_unique p q i' q hw1 hw2
        have hi'_mem : i' ∈ ({p, q} : Finset (Fin m)) := by
          rw [hset]
          simp
        exact hi'P (by simpa [P] using hi'_mem)
      · subst i
        have hw2 : WideRowPair r s i' p :=
          mixed_switch_second_wide_row (p := q) (q := p) (x' := i') (j := j) (j' := j')
            hpq.symm hi'_q hi'_p hjj N N' hNij hNi'j' hNij' hNi'j
            hN'i'j hN'i'j' hout hrow_unique hNwide_qp
        have hw1 : WideRowPair r s p q :=
          ⟨hpq, N, hNwide_pq.1, hNwide_pq.2.1, hNwide_pq.2.2⟩
        have hset := hrow_unique p q i' p hw1 hw2
        have hi'_mem : i' ∈ ({p, q} : Finset (Fin m)) := by
          rw [hset]
          simp
        exact hi'P (by simpa [P] using hi'_mem)
  · by_cases hi'P : i' ∈ P
    · have hi_p : i ≠ p := by
        intro hip
        exact hiP (by simp [P, hip])
      have hi_q : i ≠ q := by
        intro hiq
        exact hiP (by simp [P, hiq])
      have hi'_eq : i' = p ∨ i' = q := by
        simpa [P] using hi'P
      rcases hi'_eq with hi'p | hi'q
      · subst i'
        have hout_swap :
            ∀ a b, ¬ ((a = p ∨ a = i) ∧ (b = j' ∨ b = j)) →
              N'.val a b = N.val a b := by
          intro a b hnot
          exact hout a b (by
            intro hblock
            apply hnot
            constructor
            · rcases hblock.1 with hai | hap
              · exact Or.inr hai
              · exact Or.inl hap
            · rcases hblock.2 with hbj | hbj'
              · exact Or.inr hbj
              · exact Or.inl hbj')
        have hw2 : WideRowPair r s i q :=
          mixed_switch_second_wide_row (p := p) (q := q) (x' := i) (j := j') (j' := j)
            hpq hi_p hi_q hjj.symm N N' hNi'j' hNij hNi'j hNij'
            hN'ij' hN'ij hout_swap hrow_unique hNwide_pq
        have hw1 : WideRowPair r s p q :=
          ⟨hpq, N, hNwide_pq.1, hNwide_pq.2.1, hNwide_pq.2.2⟩
        have hset := hrow_unique p q i q hw1 hw2
        have hi_mem : i ∈ ({p, q} : Finset (Fin m)) := by
          rw [hset]
          simp
        exact hiP (by simpa [P] using hi_mem)
      · subst i'
        have hout_swap :
            ∀ a b, ¬ ((a = q ∨ a = i) ∧ (b = j' ∨ b = j)) →
              N'.val a b = N.val a b := by
          intro a b hnot
          exact hout a b (by
            intro hblock
            apply hnot
            constructor
            · rcases hblock.1 with hai | haq
              · exact Or.inr hai
              · exact Or.inl haq
            · rcases hblock.2 with hbj | hbj'
              · exact Or.inr hbj
              · exact Or.inl hbj')
        have hw2 : WideRowPair r s i p :=
          mixed_switch_second_wide_row (p := q) (q := p) (x' := i) (j := j') (j' := j)
            hpq.symm hi_q hi_p hjj.symm N N' hNi'j' hNij hNi'j hNij'
            hN'ij' hN'ij hout_swap hrow_unique hNwide_qp
        have hw1 : WideRowPair r s p q :=
          ⟨hpq, N, hNwide_pq.1, hNwide_pq.2.1, hNwide_pq.2.2⟩
        have hset := hrow_unique p q i p hw1 hw2
        have hi_mem : i ∈ ({p, q} : Finset (Fin m)) := by
          rw [hset]
          simp
        exact hiP (by simpa [P] using hi_mem)
    · have hi_p : i ≠ p := by
        intro hip
        exact hiP (by simp [P, hip])
      have hi_q : i ≠ q := by
        intro hiq
        exact hiP (by simp [P, hiq])
      have hi'_p : i' ≠ p := by
        intro hip
        exact hi'P (by simp [P, hip])
      have hi'_q : i' ≠ q := by
        intro hiq
        exact hi'P (by simp [P, hiq])
      have hpres := outside_switch_preserves (p := p) (q := q) (i := i) (i' := i')
        (j := j) (j' := j') N N' hi_p hi_q hi'_p hi'_q hout
      have hdiff :
          (Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
            (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(hpres c).1, (hpres c).2]
      have hA :
          (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
            (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card := by
        congr 1
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(hpres c).1, (hpres c).2]
      have hthird_bad : N'.val x d ≠ M.val x d := by
        intro hthird
        exact hN'not ⟨by rw [hdiff, hN_D], by rw [hA, hN_A], hthird⟩
      have hxd_changed : N'.val x d ≠ N.val x d := by
        intro hsame
        exact hthird_bad (hsame.trans hN_xd)
      have hxd_block : (x = i ∨ x = i') ∧ (d = j ∨ d = j') := by
        by_contra hb
        exact hxd_changed (hout x d hb)
      have hd_mem_N :
          d ∈ Finset.univ.filter (fun c => N.val p c ≠ N.val q c) := by
        rw [hN_D]
        simp [hdD0]
      have hd_ne : N.val p d ≠ N.val q d := (Finset.mem_filter.mp hd_mem_N).2
      by_cases hpd : N.val p d = true
      · have hqd : N.val q d = false := by
          cases hqv : N.val q d
          · rfl
          · exact False.elim (hd_ne (by simp [hpd, hqv]))
        rcases hBN_ex with ⟨cc, hpcc, hqcc⟩
        have hcc_ne_d : cc ≠ d := by
          intro h
          subst cc
          rw [hpd] at hpcc
          exact Bool.false_ne_true hpcc.symm
        have hnotwide : ¬ WideColPair r s d cc := by
          intro hw
          have hset := hV_support d cc hw
          apply hdV'
          simpa [hset] using (by simp : d ∈ ({d, cc} : Finset (Fin n)))
        have hxdc : N.val x d = N.val x cc :=
          not_wide_col_outside_equal (p := p) (q := q) (z := x) (c := d) (d := cc)
            N (Ne.symm hcc_ne_d) hpd hpcc hqd hqcc hnotwide hxp hxq
        have hxcc : N.val x cc = N.val x d := hxdc.symm
        have hcc_ne_j : cc ≠ j := by
          intro hcj
          rcases hxd_block.2 with hdj | hdj'
          · exact hcc_ne_d (hcj.trans hdj.symm)
          · rcases hxd_block.1 with hxi | hxi'
            · have hccv : N.val x cc = true := by rw [hxi, hcj]; exact hNij
              have hdv : N.val x d = false := by rw [hxi, hdj']; exact hNij'
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq.symm
            · have hccv : N.val x cc = false := by rw [hxi', hcj]; exact hNi'j
              have hdv : N.val x d = true := by rw [hxi', hdj']; exact hNi'j'
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq
        have hcc_ne_j' : cc ≠ j' := by
          intro hcj'
          rcases hxd_block.2 with hdj | hdj'
          · rcases hxd_block.1 with hxi | hxi'
            · have hccv : N.val x cc = false := by rw [hxi, hcj']; exact hNij'
              have hdv : N.val x d = true := by rw [hxi, hdj]; exact hNij
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq
            · have hccv : N.val x cc = true := by rw [hxi', hcj']; exact hNi'j'
              have hdv : N.val x d = false := by rw [hxi', hdj]; exact hNi'j
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq.symm
          · exact hcc_ne_d (hcj'.trans hdj'.symm)
        have hcc_fixed : N'.val x cc = N.val x cc := by
          refine hout x cc ?_
          rintro ⟨-, hc⟩
          rcases hc with hcj | hcj'
          · exact hcc_ne_j hcj
          · exact hcc_ne_j' hcj'
        have hx_dcc : N'.val x d ≠ N'.val x cc := by
          intro hsame
          apply hxd_changed
          calc
            N'.val x d = N'.val x cc := hsame
            _ = N.val x cc := hcc_fixed
            _ = N.val x d := hxcc
        have hw : WideColPair r s d cc := by
          refine ⟨Ne.symm hcc_ne_d, N', ?_, ?_, ?_⟩
          · exact ⟨p, by rw [(hpres d).1]; exact hpd,
              by rw [(hpres cc).1]; exact hpcc⟩
          · exact ⟨q, by rw [(hpres d).2]; exact hqd,
              by rw [(hpres cc).2]; exact hqcc⟩
          · let T : Finset (Fin m) := {p, q, x}
            have hTcard : T.card = 3 := by
              simp [T, hpq, hpq.symm, hxp, hxp.symm, hxq, hxq.symm]
            have hTsub : T ⊆
                Finset.univ.filter (fun z => N'.val z d ≠ N'.val z cc) := by
              intro z hz
              simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · simp [(hpres d).1, (hpres cc).1, hpd, hpcc]
              · simp [(hpres d).2, (hpres cc).2, hqd, hqcc]
              · simpa using hx_dcc
            have hle := Finset.card_le_card hTsub
            omega
        have hset := hV_support d cc hw
        exact hdV' (by simpa [hset] using (by simp : d ∈ ({d, cc} : Finset (Fin n))))
      · have hpd_false : N.val p d = false := by
          cases hpv : N.val p d
          · rfl
          · exact False.elim (hpd hpv)
        have hqd : N.val q d = true := by
          cases hqv : N.val q d
          · exact False.elim (hd_ne (by simp [hpd_false, hqv]))
          · rfl
        rcases hAN_ex with ⟨cc, hpcc, hqcc⟩
        have hcc_ne_d : cc ≠ d := by
          intro h
          subst cc
          rw [hpd_false] at hpcc
          exact Bool.false_ne_true hpcc
        have hnotwide : ¬ WideColPair r s cc d := by
          intro hw
          have hset := hV_support cc d hw
          apply hdV'
          simpa [hset] using (by simp : d ∈ ({cc, d} : Finset (Fin n)))
        have hxcc : N.val x cc = N.val x d :=
          not_wide_col_outside_equal (p := p) (q := q) (z := x) (c := cc) (d := d)
            N hcc_ne_d hpcc hpd_false hqcc hqd hnotwide hxp hxq
        have hcc_ne_j : cc ≠ j := by
          intro hcj
          rcases hxd_block.2 with hdj | hdj'
          · exact hcc_ne_d (hcj.trans hdj.symm)
          · rcases hxd_block.1 with hxi | hxi'
            · have hccv : N.val x cc = true := by rw [hxi, hcj]; exact hNij
              have hdv : N.val x d = false := by rw [hxi, hdj']; exact hNij'
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq.symm
            · have hccv : N.val x cc = false := by rw [hxi', hcj]; exact hNi'j
              have hdv : N.val x d = true := by rw [hxi', hdj']; exact hNi'j'
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq
        have hcc_ne_j' : cc ≠ j' := by
          intro hcj'
          rcases hxd_block.2 with hdj | hdj'
          · rcases hxd_block.1 with hxi | hxi'
            · have hccv : N.val x cc = false := by rw [hxi, hcj']; exact hNij'
              have hdv : N.val x d = true := by rw [hxi, hdj]; exact hNij
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq
            · have hccv : N.val x cc = true := by rw [hxi', hcj']; exact hNi'j'
              have hdv : N.val x d = false := by rw [hxi', hdj]; exact hNi'j
              have heq := hxcc
              rw [hccv, hdv] at heq
              exact Bool.false_ne_true heq.symm
          · exact hcc_ne_d (hcj'.trans hdj'.symm)
        have hcc_fixed : N'.val x cc = N.val x cc := by
          refine hout x cc ?_
          rintro ⟨-, hc⟩
          rcases hc with hcj | hcj'
          · exact hcc_ne_j hcj
          · exact hcc_ne_j' hcj'
        have hx_ccd : N'.val x cc ≠ N'.val x d := by
          intro hsame
          apply hxd_changed
          calc
            N'.val x d = N'.val x cc := hsame.symm
            _ = N.val x cc := hcc_fixed
            _ = N.val x d := hxcc
        have hw : WideColPair r s cc d := by
          refine ⟨hcc_ne_d, N', ?_, ?_, ?_⟩
          · exact ⟨p, by rw [(hpres cc).1]; exact hpcc,
              by rw [(hpres d).1]; exact hpd_false⟩
          · exact ⟨q, by rw [(hpres cc).2]; exact hqcc,
              by rw [(hpres d).2]; exact hqd⟩
          · let T : Finset (Fin m) := {p, q, x}
            have hTcard : T.card = 3 := by
              simp [T, hpq, hpq.symm, hxp, hxp.symm, hxq, hxq.symm]
            have hTsub : T ⊆
                Finset.univ.filter (fun z => N'.val z cc ≠ N'.val z d) := by
              intro z hz
              simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · simp [(hpres cc).1, (hpres d).1, hpcc, hpd_false]
              · simp [(hpres cc).2, (hpres d).2, hqcc, hqd]
              · simpa using hx_ccd
            have hle := Finset.card_le_card hTsub
            omega
        have hset := hV_support cc d hw
        exact hdV' (by simpa [hset] using (by simp : d ∈ ({cc, d} : Finset (Fin n))))

private theorem unique_wide_pair_stageB_row_branch_contradiction {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    (hact : IsActive r s) (_hm : 3 ≤ m) (_hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    {p q : Fin m} (hpqwide : WideRowPair r s p q)
    (hrow_unique :
      ∀ p q p' q' : Fin m, WideRowPair r s p q → WideRowPair r s p' q' →
        ({p, q} : Finset (Fin m)) = ({p', q'} : Finset (Fin m)))
    (hcol_unique :
      ∀ i j i' j' : Fin n, WideColPair r s i j → WideColPair r s i' j' →
        ({i, j} : Finset (Fin n)) = ({i', j'} : Finset (Fin n))) :
    False := by
  classical
  rcases hpqwide with ⟨hpq, M, hA_nonempty, hB_nonempty, hcardM⟩
  let A0 : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)
  let D0 : Finset (Fin n) :=
    Finset.univ.filter (fun c => M.val p c ≠ M.val q c)
  have hA0_nonempty : A0.Nonempty := by
    rcases hA_nonempty with ⟨c, hc⟩
    exact ⟨c, by simpa [A0] using hc⟩
  have hD0_card : 3 ≤ D0.card := by
    simpa [D0] using hcardM
  let V : Finset (Fin n) :=
    if h : ∃ i j : Fin n, WideColPair r s i j then
      ({Classical.choose h, Classical.choose (Classical.choose_spec h)} : Finset (Fin n))
    else ∅
  have hV_card : V.card ≤ 2 := by
    by_cases h : ∃ i j : Fin n, WideColPair r s i j
    · let i0 : Fin n := Classical.choose h
      let j0 : Fin n := Classical.choose (Classical.choose_spec h)
      have hw : WideColPair r s i0 j0 := Classical.choose_spec (Classical.choose_spec h)
      have hcard : ({i0, j0} : Finset (Fin n)).card = 2 := Finset.card_pair hw.1
      simpa [V, h, i0, j0] using hcard.le
    · simp [V, h]
  have hV_support :
      ∀ c d : Fin n, WideColPair r s c d →
        ({c, d} : Finset (Fin n)) = V := by
    intro c d hcdwide
    by_cases h : ∃ i j : Fin n, WideColPair r s i j
    · let i0 : Fin n := Classical.choose h
      let j0 : Fin n := Classical.choose (Classical.choose_spec h)
      have hw : WideColPair r s i0 j0 := Classical.choose_spec (Classical.choose_spec h)
      have huniq := hcol_unique c d i0 j0 hcdwide hw
      simpa [V, h, i0, j0] using huniq
    · exact False.elim (h ⟨c, d, hcdwide⟩)
  rcases exists_mem_sdiff_of_card_ge_three_card_le_two hD0_card hV_card with ⟨d, hdD0V⟩
  have hdD0 : d ∈ D0 := (Finset.mem_sdiff.mp hdD0V).1
  have hdV : d ∉ V := (Finset.mem_sdiff.mp hdD0V).2
  rcases exists_not_mem_pair_of_card_three _hm hpq with ⟨x, hxpair⟩
  have hxp : x ≠ p := by
    intro hxp
    apply hxpair
    simp [hxp]
  have hxq : x ≠ q := by
    intro hxq
    apply hxpair
    simp [hxq]
  let S : Finset (MarginClass r s) :=
    Finset.univ.filter (fun N : MarginClass r s =>
      (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) = D0 ∧
      (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card = A0.card ∧
      N.val x d = M.val x d)
  have hMS : M ∈ S := by
    simp [S, A0, D0]
  rcases active_prime_cell_varies r s hact hprime ⟨M⟩ x d with ⟨M1, M2, hvar⟩
  have hvarM : M1.val x d ≠ M.val x d ∨ M2.val x d ≠ M.val x d := by
    by_cases h1 : M1.val x d = M.val x d
    · right
      intro h2
      exact hvar (h1.trans h2.symm)
    · exact Or.inl h1
  rcases hvarM with hM1 | hM2
  · have hM1not : M1 ∉ S := by
      intro hM1S
      have hthird := (Finset.mem_filter.mp hM1S).2.2.2
      exact hM1 hthird
    have hSproper : S ≠ Finset.univ := by
      intro hSuniv
      exact hM1not (by simpa [hSuniv])
    rcases connected_boundary_edge (G := flipGraph r s) (flipGraph_connected r s ⟨M⟩)
        (S := S) ⟨M, hMS⟩ hSproper with
      ⟨N, hNS, N', hN'S, hNN'⟩
    have hint : Interchange N.val N'.val := adj_interchange hNN'
    rcases hint with
      ⟨i, i', j, j', hii, hjj, hNij, hNi'j', hNij', hNi'j,
        hN'ij, hN'i'j', hN'ij', hN'i'j, hout⟩
    have hNS_D :
        (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) = D0 :=
      (Finset.mem_filter.mp hNS).2.1
    have hNS_A :
        (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card =
          A0.card :=
      (Finset.mem_filter.mp hNS).2.2.1
    have hNS_xd : N.val x d = M.val x d :=
      (Finset.mem_filter.mp hNS).2.2.2
    have hN_D :
        (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) =
          (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)) := by
      simpa [D0] using hNS_D
    have hN_A :
        (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card =
          (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card := by
      simpa [A0] using hNS_A
    have hN'not :
        ¬ ((Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
              (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)) ∧
            (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
              (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card ∧
            N'.val x d = M.val x d) := by
      intro hclauses
      apply hN'S
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ N', by simpa [S, A0, D0] using hclauses⟩
    have hdD0_val : M.val p d ≠ M.val q d := by
      simpa [D0] using hdD0
    exact row_switch_cases
      (r := r) (s := s) (p := p) (q := q) (x := x) (i := i) (i' := i')
      (d := d) (j := j) (j' := j') (V := V) hpq hxp hxq hii hjj M N N'
      hA_nonempty hB_nonempty hcardM hN_D hN_A hNS_xd hN'not hdD0_val hV_support hdV
      hrow_unique hcol_unique hNij hNi'j' hNij' hNi'j
      hN'ij hN'i'j' hN'ij' hN'i'j hout
  · have hM2not : M2 ∉ S := by
      intro hM2S
      have hthird := (Finset.mem_filter.mp hM2S).2.2.2
      exact hM2 hthird
    have hSproper : S ≠ Finset.univ := by
      intro hSuniv
      exact hM2not (by simpa [hSuniv])
    rcases connected_boundary_edge (G := flipGraph r s) (flipGraph_connected r s ⟨M⟩)
        (S := S) ⟨M, hMS⟩ hSproper with
      ⟨N, hNS, N', hN'S, hNN'⟩
    have hint : Interchange N.val N'.val := adj_interchange hNN'
    rcases hint with
      ⟨i, i', j, j', hii, hjj, hNij, hNi'j', hNij', hNi'j,
        hN'ij, hN'i'j', hN'ij', hN'i'j, hout⟩
    have hNS_D :
        (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) = D0 :=
      (Finset.mem_filter.mp hNS).2.1
    have hNS_A :
        (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card =
          A0.card :=
      (Finset.mem_filter.mp hNS).2.2.1
    have hNS_xd : N.val x d = M.val x d :=
      (Finset.mem_filter.mp hNS).2.2.2
    have hN_D :
        (Finset.univ.filter (fun c => N.val p c ≠ N.val q c)) =
          (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)) := by
      simpa [D0] using hNS_D
    have hN_A :
        (Finset.univ.filter (fun c => N.val p c = true ∧ N.val q c = false)).card =
          (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card := by
      simpa [A0] using hNS_A
    have hN'not :
        ¬ ((Finset.univ.filter (fun c => N'.val p c ≠ N'.val q c)) =
              (Finset.univ.filter (fun c => M.val p c ≠ M.val q c)) ∧
            (Finset.univ.filter (fun c => N'.val p c = true ∧ N'.val q c = false)).card =
              (Finset.univ.filter (fun c => M.val p c = true ∧ M.val q c = false)).card ∧
            N'.val x d = M.val x d) := by
      intro hclauses
      apply hN'S
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ N', by simpa [S, A0, D0] using hclauses⟩
    have hdD0_val : M.val p d ≠ M.val q d := by
      simpa [D0] using hdD0
    exact row_switch_cases
      (r := r) (s := s) (p := p) (q := q) (x := x) (i := i) (i' := i')
      (d := d) (j := j) (j' := j') (V := V) hpq hxp hxq hii hjj M N N'
      hA_nonempty hB_nonempty hcardM hN_D hN_A hNS_xd hN'not hdD0_val hV_support hdV
      hrow_unique hcol_unique hNij hNi'j' hNij' hNi'j
      hN'ij hN'i'j' hN'ij' hN'i'j hout

private def stageBTransposeMat {m n : ℕ} (M : ZeroOneMat m n) : ZeroOneMat n m :=
  fun j i => M i j

private theorem stageBTranspose_hasMargins {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) : HasMargins s r (stageBTransposeMat M.val) := by
  constructor
  · intro j
    change colSum M.val j = s j
    exact M.property.2 j
  · intro i
    change rowSum M.val i = r i
    exact M.property.1 i

private def stageBTransposeMargin {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) : MarginClass s r :=
  ⟨stageBTransposeMat M.val, stageBTranspose_hasMargins M⟩

private theorem wideCol_iff_wideRow_transpose {m n : ℕ}
    (r : Fin m → ℕ) (s : Fin n → ℕ) (a b : Fin n) :
    WideColPair r s a b ↔ WideRowPair s r a b := by
  constructor
  · rintro ⟨hab, M, htf, hft, hcard⟩
    refine ⟨hab, stageBTransposeMargin M, ?_, ?_, ?_⟩
    · rcases htf with ⟨x, hx⟩
      exact ⟨x, by simpa [stageBTransposeMargin, stageBTransposeMat] using hx⟩
    · rcases hft with ⟨x, hx⟩
      exact ⟨x, by simpa [stageBTransposeMargin, stageBTransposeMat] using hx⟩
    · simpa [stageBTransposeMargin, stageBTransposeMat] using hcard
  · rintro ⟨hab, M, htf, hft, hcard⟩
    refine ⟨hab, stageBTransposeMargin M, ?_, ?_, ?_⟩
    · rcases htf with ⟨x, hx⟩
      exact ⟨x, by simpa [stageBTransposeMargin, stageBTransposeMat] using hx⟩
    · rcases hft with ⟨x, hx⟩
      exact ⟨x, by simpa [stageBTransposeMargin, stageBTransposeMat] using hx⟩
    · simpa [stageBTransposeMargin, stageBTransposeMat] using hcard

private theorem stageB_isDecomposable_congr {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    IsDecomposable G → IsDecomposable H := by
  rintro ⟨W₁, W₂, dW₁, dW₂, fW₁, fW₂, A, B, hnt₁, hnt₂, hIA, hIB, ⟨eprod⟩⟩
  exact ⟨W₁, W₂, dW₁, dW₂, fW₁, fW₂, A, B, hnt₁, hnt₂, hIA, hIB,
    ⟨e.symm.trans eprod⟩⟩

private theorem unique_wide_pair_stageB_col_branch_contradiction {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    (hact : IsActive r s) (_hm : 3 ≤ m) (_hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    {i j : Fin n} (hijwide : WideColPair r s i j)
    (hrow_unique :
      ∀ p q p' q' : Fin m, WideRowPair r s p q → WideRowPair r s p' q' →
        ({p, q} : Finset (Fin m)) = ({p', q'} : Finset (Fin m)))
    (hcol_unique :
      ∀ i j i' j' : Fin n, WideColPair r s i j → WideColPair r s i' j' →
        ({i, j} : Finset (Fin n)) = ({i', j'} : Finset (Fin n))) :
    False := by
  classical
  have hprimeT : ¬ IsDecomposable (flipGraph s r) := by
    intro hdec
    rcases flipGraph_transpose r s with ⟨e⟩
    exact hprime (stageB_isDecomposable_congr e.symm hdec)
  exact unique_wide_pair_stageB_row_branch_contradiction
    (r := s) (s := r) ⟨hact.2, hact.1⟩ _hn _hm hprimeT
    ((wideCol_iff_wideRow_transpose r s i j).mp hijwide)
    (by
      intro p q p' q' hpq hpq'
      exact hcol_unique p q p' q'
        ((wideCol_iff_wideRow_transpose r s p q).mpr hpq)
        ((wideCol_iff_wideRow_transpose r s p' q').mpr hpq'))
    (by
      intro a b a' b' hab hab'
      exact hrow_unique a b a' b'
        ((wideCol_iff_wideRow_transpose s r a b).mp hab)
        ((wideCol_iff_wideRow_transpose s r a' b').mp hab'))

private theorem unique_wide_pair_stageB_contradiction {m n : ℕ}
    {r : Fin m → ℕ} {s : Fin n → ℕ}
    (hact : IsActive r s) (_hm : 3 ≤ m) (_hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    (hwide :
      (∃ p q : Fin m, WideRowPair r s p q) ∨
        (∃ i j : Fin n, WideColPair r s i j))
    (hrow_unique :
      ∀ p q p' q' : Fin m, WideRowPair r s p q → WideRowPair r s p' q' →
        ({p, q} : Finset (Fin m)) = ({p', q'} : Finset (Fin m)))
    (hcol_unique :
      ∀ i j i' j' : Fin n, WideColPair r s i j → WideColPair r s i' j' →
        ({i, j} : Finset (Fin n)) = ({i', j'} : Finset (Fin n))) :
    False := by
  classical
  rcases hwide with hrow | hcol
  · rcases hrow with ⟨p, q, hpqwide⟩
    exact unique_wide_pair_stageB_row_branch_contradiction
      (r := r) (s := s) hact _hm _hn hprime hpqwide hrow_unique hcol_unique
  · rcases hcol with ⟨i, j, hijwide⟩
    exact unique_wide_pair_stageB_col_branch_contradiction
      (r := r) (s := s) hact _hm _hn hprime hijwide hrow_unique hcol_unique

/-- Lemma 5.11 (buffer existence): a separating row or column has a non-bipartite fibre. -/
theorem buffer_line_exists {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (_hm : 3 ≤ m) (_hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    (hnb : ¬ ∃ col : MarginClass r s → Bool, IsProper2Coloring (flipGraph r s) col)
    (a b : MarginClass r s) (hab : a ≠ b) :
    ∃ line : Fin m ⊕ Fin n, lineSeparates a b line ∧ lineFibreNonbip (r := r) (s := s) line := by
  classical
  by_contra hnone
  have hno : ∀ line : Fin m ⊕ Fin n,
      lineSeparates a b line → ¬ lineFibreNonbip (r := r) (s := s) line := by
    intro line hsep hnbuf
    exact hnone ⟨line, hsep, hnbuf⟩
  have hres := residue_cases_of_no_buffer r s hact hprime hnb a b hab hno
  have hwide :
      (∃ p q : Fin m, WideRowPair r s p q) ∨
        (∃ i j : Fin n, WideColPair r s i j) := by
    rcases nonbip_has_triangle r s hact hprime hnb with ⟨M0, M1, M2, h01, h12, h02⟩
    exact triangle_wide_pair h01 h12 h02
  have _hrow_unique := atMostOne_wide_row_pair (a := a) (b := b) hno hres
  have _hcol_unique := atMostOne_wide_col_pair (a := a) (b := b) hno hres
  exact False.elim
    (unique_wide_pair_stageB_contradiction (r := r) (s := s) hact _hm _hn hprime
      hwide _hrow_unique _hcol_unique)

theorem boundary_interchange_yields_alternate_config {m n : ℕ}
    {L : Fin (m + 1)} {i j : Fin n} {M M' : ZeroOneMat (m + 1) n} (hij : i ≠ j)
    (hN : Nested L i j M) (hW' : HasWitness L i j M')
    (hrowL : ∀ b, M L b = M' L b)
    (hMLi : M L i = true) (hMLj : M L j = false)
    (hint : Interchange M M') :
    ∃ u v c, u ≠ L ∧ v ≠ L ∧ u ≠ v ∧ i ≠ c ∧ j ≠ c ∧
      M u i = true ∧ M u j = true ∧ M u c = false ∧
      M v i = false ∧ M v j = false ∧ M v c = true ∧
      (M' = Brualdi.Ryser.switchMat M u v i c ∨
        M' = Brualdi.Ryser.switchMat M u v j c) := by
  classical
  rcases hint with
    ⟨r₁, r₂, c₁, c₂, hrne, hcne, hM₁₁, hM₂₂, hM₁₂, hM₂₁,
      hM'₁₁, hM'₂₂, hM'₁₂, hM'₂₁, hout⟩
  have hM'_eq : M' = Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ :=
    interchange_eq_switchMat_of_witness hM'₁₁ hM'₂₂ hM'₁₂ hM'₂₁ hout
  have hr₁L : r₁ ≠ L := by
    intro h
    have hsame := hrowL c₁
    rw [← h, hM₁₁, hM'₁₁] at hsame
    exact Bool.false_ne_true hsame.symm
  have hr₂L : r₂ ≠ L := by
    intro h
    have hsame := hrowL c₂
    rw [← h, hM₂₂, hM'₂₂] at hsame
    exact Bool.false_ne_true hsame.symm
  rcases hW' with ⟨w, hwL, hw'i, hw'j⟩
  have hnoW : ¬ HasWitness L i j M := (nested_iff_not_hasWitness.mp hN)
  have witness_contra (a : Fin (m + 1)) (haL : a ≠ L)
      (hai : M a i = false) (haj : M a j = true) : False :=
    hnoW ⟨a, haL, hai, haj⟩
  have hwrow : w = r₁ ∨ w = r₂ := by
    by_contra h
    push_neg at h
    have hMi : M w i = false := by
      have hsame := hout w i (by
        intro hb
        exact hb.1.elim h.1 h.2)
      rw [← hsame]
      exact hw'i
    have hMj : M w j = true := by
      have hsame := hout w j (by
        intro hb
        exact hb.1.elim h.1 h.2)
      rw [← hsame]
      exact hw'j
    exact witness_contra w hwL hMi hMj
  let iBlock : Prop := c₁ = i ∨ c₂ = i
  let jBlock : Prop := c₁ = j ∨ c₂ = j
  have hmeet : iBlock ∨ jBlock := by
    by_contra h
    simp only [iBlock, jBlock, not_or] at h
    have hMi : M w i = false := by
      have hsame := hout w i (by
        intro hb
        exact hb.2.elim (fun hc => h.1.1 hc.symm) (fun hc => h.1.2 hc.symm))
      rw [← hsame]
      exact hw'i
    have hMj : M w j = true := by
      have hsame := hout w j (by
        intro hb
        exact hb.2.elim (fun hc => h.2.1 hc.symm) (fun hc => h.2.2 hc.symm))
      rw [← hsame]
      exact hw'j
    exact witness_contra w hwL hMi hMj
  have hnotBoth : ¬ (iBlock ∧ jBlock) := by
    rintro ⟨hiB, hjB⟩
    rcases hiB with hc₁i | hc₂i
    · rcases hjB with hc₁j | hc₂j
      · exact hij (hc₁i.symm.trans hc₁j)
      · exact witness_contra r₂ hr₂L (by simpa [hc₁i] using hM₂₁)
          (by simpa [hc₂j] using hM₂₂)
    · rcases hjB with hc₁j | hc₂j
      · exact witness_contra r₁ hr₁L (by simpa [hc₂i] using hM₁₂)
          (by simpa [hc₁j] using hM₁₁)
      · exact hij (hc₂i.symm.trans hc₂j)
  rcases hmeet with hiB | hjB
  · have hjNot : ¬ jBlock := fun hjB => hnotBoth ⟨hiB, hjB⟩
    rcases hiB with hc₁i | hc₂i
    · have hc₂i_ne : c₂ ≠ i := by
        intro h
        exact hcne (hc₁i.trans h.symm)
      have hc₂j_ne : c₂ ≠ j := by
        intro h
        exact hjNot (Or.inr h)
      rcases hwrow with hw | hw
      · subst w
        have huj : M r₁ j = true := by
          have hsame := hout r₁ j (by
            intro hb
            exact hb.2.elim (fun h => hjNot (Or.inl h.symm))
              (fun h => hjNot (Or.inr h.symm)))
          rw [← hsame]
          exact hw'j
        have hvj : M r₂ j = false := by
          by_cases htrue : M r₂ j = true
          · have hforced := hN r₂ hr₂L htrue
            rw [show M r₂ i = false by simpa [hc₁i] using hM₂₁] at hforced
            exact False.elim (Bool.false_ne_true hforced)
          · cases hcell : M r₂ j <;> simp_all
        refine ⟨r₁, r₂, c₂, hr₁L, hr₂L, hrne, ?_, (fun h => hc₂j_ne h.symm), ?_, huj, ?_, ?_, hvj, ?_, Or.inl ?_⟩
        · exact fun h => hc₂i_ne h.symm
        · simpa [hc₁i] using hM₁₁
        · exact hM₁₂
        · simpa [hc₁i] using hM₂₁
        · exact hM₂₂
        · rw [hM'_eq, hc₁i]
      · subst w
        have hbad : M' r₂ i = true := by simpa [hc₁i] using hM'₂₁
        rw [hw'i] at hbad
        exact False.elim (Bool.false_ne_true hbad)
    · have hc₁i_ne : c₁ ≠ i := by
        intro h
        exact hcne (h.trans hc₂i.symm)
      have hc₁j_ne : c₁ ≠ j := by
        intro h
        exact hjNot (Or.inl h)
      rcases hwrow with hw | hw
      · subst w
        have hbad : M' r₁ i = true := by simpa [hc₂i] using hM'₁₂
        rw [hw'i] at hbad
        exact False.elim (Bool.false_ne_true hbad)
      · subst w
        have huj : M r₂ j = true := by
          have hsame := hout r₂ j (by
            intro hb
            exact hb.2.elim (fun h => hjNot (Or.inl h.symm))
              (fun h => hjNot (Or.inr h.symm)))
          rw [← hsame]
          exact hw'j
        have hvj : M r₁ j = false := by
          by_cases htrue : M r₁ j = true
          · have hforced := hN r₁ hr₁L htrue
            rw [show M r₁ i = false by simpa [hc₂i] using hM₁₂] at hforced
            exact False.elim (Bool.false_ne_true hforced)
          · cases hcell : M r₁ j <;> simp_all
        have hsw :
            Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ =
              Brualdi.Ryser.switchMat M r₂ r₁ i c₁ := by
          simpa [hc₂i] using switchMat_swap_rows_cols M r₁ r₂ c₁ c₂
        refine ⟨r₂, r₁, c₁, hr₂L, hr₁L, hrne.symm, ?_, (fun h => hc₁j_ne h.symm), ?_, huj, ?_, ?_, hvj, ?_, Or.inl ?_⟩
        · exact fun h => hc₁i_ne h.symm
        · simpa [hc₂i] using hM₂₂
        · exact hM₂₁
        · simpa [hc₂i] using hM₁₂
        · exact hM₁₁
        · exact hM'_eq.trans hsw
  · have hiNot : ¬ iBlock := fun hiB => hnotBoth ⟨hiB, hjB⟩
    rcases hjB with hc₁j | hc₂j
    · have hc₂j_ne : c₂ ≠ j := by
        intro h
        exact hcne (hc₁j.trans h.symm)
      have hc₂i_ne : c₂ ≠ i := by
        intro h
        exact hiNot (Or.inr h)
      rcases hwrow with hw | hw
      · subst w
        have hbad : M' r₁ j = false := by simpa [hc₁j] using hM'₁₁
        rw [hw'j] at hbad
        exact False.elim (Bool.false_ne_true hbad.symm)
      · subst w
        have hvi : M r₂ i = false := by
          have hsame := hout r₂ i (by
            intro hb
            exact hb.2.elim (fun h => hiNot (Or.inl h.symm))
              (fun h => hiNot (Or.inr h.symm)))
          rw [← hsame]
          exact hw'i
        have hui : M r₁ i = true := hN r₁ hr₁L (by simpa [hc₁j] using hM₁₁)
        refine ⟨r₁, r₂, c₂, hr₁L, hr₂L, hrne, (fun h => hc₂i_ne h.symm), ?_, hui, ?_, ?_, hvi, ?_, ?_, Or.inr ?_⟩
        · exact fun h => hc₂j_ne h.symm
        · simpa [hc₁j] using hM₁₁
        · exact hM₁₂
        · simpa [hc₁j] using hM₂₁
        · exact hM₂₂
        · rw [hM'_eq, hc₁j]
    · have hc₁j_ne : c₁ ≠ j := by
        intro h
        exact hcne (h.trans hc₂j.symm)
      have hc₁i_ne : c₁ ≠ i := by
        intro h
        exact hiNot (Or.inl h)
      rcases hwrow with hw | hw
      · subst w
        have hvi : M r₁ i = false := by
          have hsame := hout r₁ i (by
            intro hb
            exact hb.2.elim (fun h => hiNot (Or.inl h.symm))
              (fun h => hiNot (Or.inr h.symm)))
          rw [← hsame]
          exact hw'i
        have hui : M r₂ i = true := hN r₂ hr₂L (by simpa [hc₂j] using hM₂₂)
        have hsw :
            Brualdi.Ryser.switchMat M r₁ r₂ c₁ c₂ =
              Brualdi.Ryser.switchMat M r₂ r₁ j c₁ := by
          simpa [hc₂j] using switchMat_swap_rows_cols M r₁ r₂ c₁ c₂
        refine ⟨r₂, r₁, c₁, hr₂L, hr₁L, hrne.symm, (fun h => hc₁i_ne h.symm), ?_, hui, ?_, ?_, hvi, ?_, ?_, Or.inr ?_⟩
        · exact fun h => hc₁j_ne h.symm
        · simpa [hc₂j] using hM₂₂
        · exact hM₂₁
        · simpa [hc₂j] using hM₁₂
        · exact hM₁₁
        · exact hM'_eq.trans hsw
      · subst w
        have hbad : M' r₂ j = false := by simpa [hc₂j] using hM'₂₂
        rw [hw'j] at hbad
        exact False.elim (Bool.false_ne_true hbad.symm)

private theorem card_ge_three_of_not_bip_sec5 {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hnb : ¬ ∃ col, IsProper2Coloring G col) :
    3 ≤ Fintype.card V := by
  classical
  by_contra hcard
  have hle_two : Fintype.card V ≤ 2 := by omega
  have hle_bool : Fintype.card V ≤ Fintype.card Bool := by
    simpa [Fintype.card_bool] using hle_two
  rcases Function.Embedding.nonempty_of_card_le (α := V) (β := Bool) hle_bool with ⟨e⟩
  apply hnb
  refine ⟨fun w => e w, ?_⟩
  intro u v huv hcol
  have huv_eq : u = v := e.injective hcol
  subst v
  exact G.loopless.irrefl u huv

private theorem rowSupport_eq_after_switch_off_row {m n : ℕ}
    {M : ZeroOneMat (m + 1) n} {L u v : Fin (m + 1)} {a b : Fin n}
    (huL : u ≠ L) (hvL : v ≠ L) :
    (Finset.univ.filter (fun c =>
      Brualdi.Ryser.switchMat M u v a b L c = true)) =
      Finset.univ.filter (fun c => M L c = true) := by
  classical
  ext c
  simp [Brualdi.Ryser.switchMat, huL.symm, hvL.symm]

private theorem rowSupport_switch_margin_eq {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {M : MarginClass r s} {L u v : Fin (m + 1)} {a b : Fin n}
    (huL : u ≠ L) (hvL : v ≠ L)
    (hprop : HasMargins r s (Brualdi.Ryser.switchMat M.val u v a b)) :
    rowSupport L
      (⟨Brualdi.Ryser.switchMat M.val u v a b, hprop⟩ : MarginClass r s) =
      rowSupport L M := by
  change (Finset.univ.filter (fun c =>
    Brualdi.Ryser.switchMat M.val u v a b L c = true)) =
      Finset.univ.filter (fun c => M.val L c = true)
  exact rowSupport_eq_after_switch_off_row huL hvL

private theorem row_cell_true_of_fibre_left {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ} {L : Fin (m + 1)}
    {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X Y : RowQ r s L B} {i j : Fin n}
    (hXY : X.val \ Y.val = {i})
    (M : {M : MarginClass r s // rowProj hB M = X}) :
    M.val.val L i = true := by
  classical
  have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
  have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
  have hiX : i ∈ X.val := (Finset.mem_sdiff.mp hi).1
  have hiRow : i ∈ rowSupport L M.val := by simpa [hMX] using hiX
  simpa [rowSupport] using (Finset.mem_filter.mp hiRow).2

private theorem row_cell_false_of_fibre_right_missing {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ} {L : Fin (m + 1)}
    {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X Y : RowQ r s L B} {i j : Fin n}
    (hYX : Y.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X}) :
    M.val.val L j = false := by
  classical
  have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
  have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
  have hjX : j ∉ X.val := (Finset.mem_sdiff.mp hj).2
  have hjRow : j ∉ rowSupport L M.val := by simpa [hMX] using hjX
  cases hcell : M.val.val L j
  · rfl
  · exact False.elim (hjRow (by simp [rowSupport, hcell]))

private theorem row_eq_of_same_rowSupport {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ} {L : Fin (m + 1)}
    {M N : MarginClass r s} (h : rowSupport L M = rowSupport L N) :
    ∀ b, M.val L b = N.val L b := by
  classical
  intro b
  cases hM : M.val L b <;> cases hN : N.val L b <;> try rfl
  · have hbN : b ∈ rowSupport L N := by simp [rowSupport, hN]
    have hbM : b ∈ rowSupport L M := by simpa [h] using hbN
    have := (Finset.mem_filter.mp hbM).2
    rw [hM] at this
    exact False.elim (Bool.false_ne_true this)
  · have hbM : b ∈ rowSupport L M := by simp [rowSupport, hM]
    have hbN : b ∈ rowSupport L N := by simpa [h] using hbM
    have := (Finset.mem_filter.mp hbN).2
    rw [hN] at this
    exact False.elim (Bool.false_ne_true this)

private def switch_margin_fibre_vertex {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ} {L : Fin (m + 1)}
    {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X : RowQ r s L B} (M : {M : MarginClass r s // rowProj hB M = X})
    {u v : Fin (m + 1)} {a b : Fin n}
    (huL : u ≠ L) (hvL : v ≠ L)
    (hb : Brualdi.Ryser.SwitchBlock M.val.val u v a b) :
    {N : MarginClass r s // rowProj hB N = X} := by
  classical
  let N : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val.val u v a b,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb) M.val.property⟩
  refine ⟨N, ?_⟩
  apply Subtype.ext
  have hrow : rowSupport L N = rowSupport L M.val := by
    exact rowSupport_switch_margin_eq (M := M.val) (L := L) (u := u) (v := v)
      (a := a) (b := b) huL hvL _
  exact hrow.trans (congrArg Subtype.val M.property)

private theorem fibre_adj_of_switch {m n : ℕ}
    {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {BF : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      BF.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X : RowQ r s L BF}
    {A B : {M : MarginClass r s // rowProj hB M = X}}
    (hint : Interchange A.val.val B.val.val) (hne : A.val ≠ B.val) :
    (fibreGraph (flipGraph r s) (rowProj hB) X).Adj A B := by
  rw [fibreGraph, SimpleGraph.induce_adj, flipGraph, SimpleGraph.fromRel_adj]
  exact ⟨hne, Or.inl hint⟩

def rowsB {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun a => a ≠ L ∧ M a i = false ∧ M a j = true)

def rowsA {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun a => a ≠ L ∧ M a i = true ∧ M a j = false)

def rowsT {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun a => a ≠ L ∧ M a i = true ∧ M a j = true)

def bcount {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : ℕ :=
  (rowsB L i j M).card

def acount {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : ℕ :=
  (rowsA L i j M).card

def tcount {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) : ℕ :=
  (rowsT L i j M).card

theorem colSum_i_split {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) :
    colSum M i = (if M L i then 1 else 0) + acount L i j M + tcount L i j M := by
  classical
  let S : Finset (Fin (m + 1)) := (Finset.univ.erase L).filter (fun a => M a i = true)
  have hS :
      S = rowsA L i j M ∪ rowsT L i j M := by
    ext a
    by_cases haj : M a j = true
    · simp [S, rowsA, rowsT, haj]
    · have hajf : M a j = false := by
        cases h : M a j <;> simp_all
      simp [S, rowsA, rowsT, hajf]
  have hdisj : Disjoint (rowsA L i j M) (rowsT L i j M) := by
    rw [Finset.disjoint_left]
    intro a haA haT
    have hAf : M a j = false := (Finset.mem_filter.mp haA).2.2.2
    have hTt : M a j = true := (Finset.mem_filter.mp haT).2.2.2
    rw [hAf] at hTt
    exact Bool.false_ne_true hTt
  have hsum_erase :
      (∑ a ∈ Finset.univ.erase L, (if M a i then 1 else 0 : ℕ)) =
        acount L i j M + tcount L i j M := by
    have hsum_bool :=
      Finset.sum_boole (R := ℕ) (fun a : Fin (m + 1) => M a i = true)
        (Finset.univ.erase L)
    have hcardS :
        (∑ a ∈ Finset.univ.erase L, (if M a i = true then 1 else 0 : ℕ)) =
          S.card := by
      simpa [S] using hsum_bool
    calc
      (∑ a ∈ Finset.univ.erase L, (if M a i then 1 else 0 : ℕ))
          = (∑ a ∈ Finset.univ.erase L, (if M a i = true then 1 else 0 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            cases M a i <;> rfl
      _ = S.card := hcardS
      _ = (rowsA L i j M ∪ rowsT L i j M).card := by rw [hS]
      _ = acount L i j M + tcount L i j M := by
            rw [Finset.card_union_of_disjoint hdisj]
            rfl
  have hsplit :=
    Finset.add_sum_erase Finset.univ (fun a : Fin (m + 1) =>
      (if M a i then 1 else 0 : ℕ)) (Finset.mem_univ L)
  calc
    colSum M i = (∑ a : Fin (m + 1), (if M a i then 1 else 0 : ℕ)) := by
      rfl
    _ = (if M L i then 1 else 0 : ℕ) +
        ∑ a ∈ Finset.univ.erase L, (if M a i then 1 else 0 : ℕ) := by
          simpa using hsplit.symm
    _ = (if M L i then 1 else 0 : ℕ) + acount L i j M + tcount L i j M := by
          rw [hsum_erase]
          omega

theorem colSum_j_split {m n : ℕ} (L : Fin (m + 1)) (i j : Fin n)
    (M : ZeroOneMat (m + 1) n) :
    colSum M j = (if M L j then 1 else 0) + bcount L i j M + tcount L i j M := by
  classical
  let S : Finset (Fin (m + 1)) := (Finset.univ.erase L).filter (fun a => M a j = true)
  have hS :
      S = rowsB L i j M ∪ rowsT L i j M := by
    ext a
    by_cases hai : M a i = true
    · simp [S, rowsB, rowsT, hai]
    · have haif : M a i = false := by
        cases h : M a i <;> simp_all
      simp [S, rowsB, rowsT, haif]
  have hdisj : Disjoint (rowsB L i j M) (rowsT L i j M) := by
    rw [Finset.disjoint_left]
    intro a haB haT
    have hBf : M a i = false := (Finset.mem_filter.mp haB).2.2.1
    have hTt : M a i = true := (Finset.mem_filter.mp haT).2.2.1
    rw [hBf] at hTt
    exact Bool.false_ne_true hTt
  have hsum_erase :
      (∑ a ∈ Finset.univ.erase L, (if M a j then 1 else 0 : ℕ)) =
        bcount L i j M + tcount L i j M := by
    have hsum_bool :=
      Finset.sum_boole (R := ℕ) (fun a : Fin (m + 1) => M a j = true)
        (Finset.univ.erase L)
    have hcardS :
        (∑ a ∈ Finset.univ.erase L, (if M a j = true then 1 else 0 : ℕ)) =
          S.card := by
      simpa [S] using hsum_bool
    calc
      (∑ a ∈ Finset.univ.erase L, (if M a j then 1 else 0 : ℕ))
          = (∑ a ∈ Finset.univ.erase L, (if M a j = true then 1 else 0 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            cases M a j <;> rfl
      _ = S.card := hcardS
      _ = (rowsB L i j M ∪ rowsT L i j M).card := by rw [hS]
      _ = bcount L i j M + tcount L i j M := by
            rw [Finset.card_union_of_disjoint hdisj]
            rfl
  have hsplit :=
    Finset.add_sum_erase Finset.univ (fun a : Fin (m + 1) =>
      (if M a j then 1 else 0 : ℕ)) (Finset.mem_univ L)
  calc
    colSum M j = (∑ a : Fin (m + 1), (if M a j then 1 else 0 : ℕ)) := by
      rfl
    _ = (if M L j then 1 else 0 : ℕ) +
        ∑ a ∈ Finset.univ.erase L, (if M a j then 1 else 0 : ℕ) := by
          simpa using hsplit.symm
    _ = (if M L j then 1 else 0 : ℕ) + bcount L i j M + tcount L i j M := by
          rw [hsum_erase]
          omega

theorem count_identity_source {m n : ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {i j : Fin n} {M : ZeroOneMat (m + 1) n}
    (hLi : M L i = true) (hLj : M L j = false)
    (hci : colSum M i = s i) (hcj : colSum M j = s j) :
    bcount L i j M + s i = acount L i j M + s j + 1 := by
  have hi := colSum_i_split L i j M
  have hj := colSum_j_split L i j M
  rw [hci, hLi] at hi
  rw [hcj, hLj] at hj
  simp at hi hj
  omega

theorem count_identity_target {m n : ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {i j : Fin n} {M : ZeroOneMat (m + 1) n}
    (hLi : M L i = false) (hLj : M L j = true)
    (hci : colSum M i = s i) (hcj : colSum M j = s j) :
    acount L i j M + s j = bcount L i j M + s i + 1 := by
  have hi := colSum_i_split L i j M
  have hj := colSum_j_split L i j M
  rw [hci, hLi] at hi
  rw [hcj, hLj] at hj
  simp at hi hj
  omega

def crossTo {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X : RowQ r s L B} (E : RowQ r s L B)
    (M : {M : MarginClass r s // rowProj hB M = X}) :
    Finset {N : MarginClass r s // rowProj hB N = E} := by
  classical
  exact Finset.univ.filter (fun N => (flipGraph r s).Adj M.val N.val)

private def crossSwitchVertex {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X})
    {a : Fin (m + 1)} (ha : a ∈ rowsB L i j M.val.val) :
    {N : MarginClass r s // rowProj hB N = E} := by
  classical
  have haL : a ≠ L := (Finset.mem_filter.mp ha).2.1
  have hai : M.val.val a i = false := (Finset.mem_filter.mp ha).2.2.1
  have haj : M.val.val a j = true := (Finset.mem_filter.mp ha).2.2.2
  have hMLi : M.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXi M
  have hMLj : M.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj M
  have hij : i ≠ j := by
    have hi : i ∈ X.val \ E.val := by rw [hXi]; simp
    have hj : j ∈ E.val \ X.val := by rw [hXj]; simp
    intro h
    exact (Finset.mem_sdiff.mp hi).2 (by simpa [h] using (Finset.mem_sdiff.mp hj).1)
  let hb : Brualdi.Ryser.SwitchBlock M.val.val L a i j :=
    ⟨haL.symm, hij, hMLi, haj, hMLj, hai⟩
  let N : MarginClass r s :=
    ⟨Brualdi.Ryser.switchMat M.val.val L a i j,
      Brualdi.Ryser.interchange_preserves_margins
        (Brualdi.Ryser.switch_interchange hb) M.val.property⟩
  refine ⟨N, ?_⟩
  apply Subtype.ext
  have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
  have hNE : rowSupport L N = E.val := by
    change (Finset.univ.filter (fun b =>
      Brualdi.Ryser.switchMat M.val.val L a i j L b = true)) = E.val
    exact rowSupport_eq_after_single_switch
      (L := L) (a := a) (i := i) (j := j) (M := M.val.val)
      (X := X.val) (Y := E.val) (by simpa [rowSupport] using hMX) hXi hXj haL
  exact hNE

private theorem crossSwitchVertex_adj {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X})
    {a : Fin (m + 1)} (ha : a ∈ rowsB L i j M.val.val) :
    (flipGraph r s).Adj M.val (crossSwitchVertex (hB := hB) hXi hXj M ha).val := by
  classical
  have haL : a ≠ L := (Finset.mem_filter.mp ha).2.1
  have hai : M.val.val a i = false := (Finset.mem_filter.mp ha).2.2.1
  have haj : M.val.val a j = true := (Finset.mem_filter.mp ha).2.2.2
  have hMLi : M.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXi M
  have hMLj : M.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj M
  have hij : i ≠ j := by
    have hi : i ∈ X.val \ E.val := by rw [hXi]; simp
    have hj : j ∈ E.val \ X.val := by rw [hXj]; simp
    intro h
    exact (Finset.mem_sdiff.mp hi).2 (by simpa [h] using (Finset.mem_sdiff.mp hj).1)
  let hb : Brualdi.Ryser.SwitchBlock M.val.val L a i j :=
    ⟨haL.symm, hij, hMLi, haj, hMLj, hai⟩
  have hint : Interchange M.val.val (crossSwitchVertex (hB := hB) hXi hXj M ha).val.val := by
    simpa [crossSwitchVertex, hb] using Brualdi.Ryser.switch_interchange hb
  have hne : M.val ≠ (crossSwitchVertex (hB := hB) hXi hXj M ha).val := by
    intro heq
    have hval : (crossSwitchVertex (hB := hB) hXi hXj M ha).val.val = M.val.val :=
      congrArg Subtype.val heq.symm
    exact Brualdi.Ryser.switchMat_ne hb
      (by simpa [crossSwitchVertex, hb] using hval)
  rw [flipGraph, SimpleGraph.fromRel_adj]
  exact ⟨hne, Or.inl hint⟩

private theorem crossWitness_exists {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X})
    (N : {N : MarginClass r s // rowProj hB N = E})
    (hN : N ∈ crossTo (hB := hB) E M) :
    ∃ a, a ∈ rowsB L i j M.val.val ∧
      N.val.val = Brualdi.Ryser.switchMat M.val.val L a i j := by
  classical
  have hMLi : M.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXi M
  have hMLj : M.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj M
  have hNLi : N.val.val L i = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X)
      (i := j) (j := i) hXi N
  have hNLj : N.val.val L j = true :=
    row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X)
      (i := j) (j := i) hXj N
  have hadj : (flipGraph r s).Adj M.val N.val := by
    simpa [crossTo] using hN
  rw [flipGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨_hne, hint | hint⟩
  · rcases crossing_eq_switchMat hMLi hMLj hNLi hNLj hint with
      ⟨a, haL, hai, haj, hEq⟩
    refine ⟨a, ?_, hEq⟩
    simp [rowsB, haL, hai, haj]
  · rcases crossing_eq_switchMat hMLi hMLj hNLi hNLj (interchange_symm hint) with
      ⟨a, haL, hai, haj, hEq⟩
    refine ⟨a, ?_, hEq⟩
    simp [rowsB, haL, hai, haj]

theorem cross_card_eq_bcount {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = X}) :
    (crossTo (hB := hB) E M).card = bcount L i j M.val.val := by
  classical
  let rawE : {N : MarginClass r s // rowSupport L N = E.val} :=
    Classical.choice ((hB E.val).mp E.property)
  let defaultE : {N : MarginClass r s // rowProj hB N = E} :=
    ⟨rawE.val, Subtype.ext rawE.property⟩
  let fwd : Fin (m + 1) → {N : MarginClass r s // rowProj hB N = E} := fun a =>
    if ha : a ∈ rowsB L i j M.val.val then
      crossSwitchVertex (hB := hB) hXi hXj M ha
    else defaultE
  have hij : i ≠ j := by
    have hi : i ∈ X.val \ E.val := by rw [hXi]; simp
    have hj : j ∈ E.val \ X.val := by rw [hXj]; simp
    intro h
    exact (Finset.mem_sdiff.mp hi).2 (by simpa [h] using (Finset.mem_sdiff.mp hj).1)
  have hle_fwd :
      (rowsB L i j M.val.val).card ≤ (crossTo (hB := hB) E M).card := by
    refine Finset.card_le_card_of_injOn fwd ?_ ?_
    · intro a ha
      have hfa :
          fwd a = crossSwitchVertex (hB := hB) hXi hXj M ha := by
        exact dif_pos ha
      rw [hfa]
      simp [crossTo, crossSwitchVertex_adj (hB := hB) hXi hXj M ha]
    · intro a ha b hb h
      have hmat :
          (crossSwitchVertex (hB := hB) hXi hXj M ha).val.val =
            (crossSwitchVertex (hB := hB) hXi hXj M hb).val.val := by
        have hfa :
            fwd a = crossSwitchVertex (hB := hB) hXi hXj M ha := by
          exact dif_pos ha
        have hfb :
            fwd b = crossSwitchVertex (hB := hB) hXi hXj M hb := by
          exact dif_pos hb
        simpa [hfa, hfb] using congrArg (fun N => N.val.val) h
      by_contra hab
      have haL : a ≠ L := (Finset.mem_filter.mp ha).2.1
      have hbL : b ≠ L := (Finset.mem_filter.mp hb).2.1
      have hai : M.val.val a i = false := (Finset.mem_filter.mp ha).2.2.1
      have hcell := congrFun (congrFun hmat a) i
      simp [crossSwitchVertex, Brualdi.Ryser.switchMat, haL, hbL, hij, hab,
        Ne.symm hab, hai] at hcell
  let inv : {N : MarginClass r s // rowProj hB N = E} → Fin (m + 1) := fun N =>
    if hN : N ∈ crossTo (hB := hB) E M then
      Classical.choose (crossWitness_exists (hB := hB) hXi hXj M N hN)
    else L
  have hle_inv :
      (crossTo (hB := hB) E M).card ≤ (rowsB L i j M.val.val).card := by
    refine Finset.card_le_card_of_injOn inv ?_ ?_
    · intro N hN
      have hspec := Classical.choose_spec (crossWitness_exists (hB := hB) hXi hXj M N hN)
      have hinv :
          inv N = Classical.choose (crossWitness_exists (hB := hB) hXi hXj M N hN) := by
        exact dif_pos hN
      simpa [hinv] using hspec.1
    · intro N hN N' hN' h
      have hspecN := Classical.choose_spec (crossWitness_exists (hB := hB) hXi hXj M N hN)
      have hspecN' := Classical.choose_spec (crossWitness_exists (hB := hB) hXi hXj M N' hN')
      have hinvN :
          inv N = Classical.choose (crossWitness_exists (hB := hB) hXi hXj M N hN) := by
        exact dif_pos hN
      have hinvN' :
          inv N' = Classical.choose (crossWitness_exists (hB := hB) hXi hXj M N' hN') := by
        exact dif_pos hN'
      have hEqN :
          N.val.val = Brualdi.Ryser.switchMat M.val.val L (inv N) i j := by
        simpa [hinvN] using hspecN.2
      have hEqN' :
          N'.val.val = Brualdi.Ryser.switchMat M.val.val L (inv N') i j := by
        simpa [hinvN'] using hspecN'.2
      apply Subtype.ext
      apply Subtype.ext
      rw [hEqN, hEqN', h]
  rw [bcount]
  exact le_antisymm hle_inv hle_fwd

theorem cross_card_eq_acount {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (M : {M : MarginClass r s // rowProj hB M = E}) :
    (crossTo (hB := hB) X M).card = acount L i j M.val.val := by
  have h := cross_card_eq_bcount r s L B hB hXj hXi M
  simpa [acount, bcount, rowsA, rowsB, and_assoc, and_left_comm, and_comm] using h

theorem bcount_flip {m n : ℕ} {L a : Fin (m + 1)} {i j : Fin n}
    {M : ZeroOneMat (m + 1) n}
    (hLi : M L i = false) (hLj : M L j = true)
    (ha : a ∈ rowsA L i j M) :
    bcount L i j (Brualdi.Ryser.switchMat M L a j i) = bcount L i j M + 1 := by
  classical
  have haL : a ≠ L := (Finset.mem_filter.mp ha).2.1
  have hai : M a i = true := (Finset.mem_filter.mp ha).2.2.1
  have haj : M a j = false := (Finset.mem_filter.mp ha).2.2.2
  have hnot : a ∉ rowsB L i j M := by
    intro haB
    have haB_i : M a i = false := (Finset.mem_filter.mp haB).2.2.1
    rw [hai] at haB_i
    exact Bool.false_ne_true haB_i.symm
  have hij : i ≠ j := by
    intro h
    subst j
    rw [hLi] at hLj
    exact Bool.false_ne_true hLj
  have hrows :
      rowsB L i j (Brualdi.Ryser.switchMat M L a j i) =
        insert a (rowsB L i j M) := by
    ext c
    by_cases hcL : c = L
    · subst c
      simp [rowsB, Brualdi.Ryser.switchMat, hLi, Ne.symm haL, Ne.symm hij]
    · by_cases hca : c = a
      · subst c
        simp [rowsB, Brualdi.Ryser.switchMat, haL, hij, Ne.symm hij, hai, haj]
      · simp [rowsB, Brualdi.Ryser.switchMat, hcL, hca, Ne.symm hcL, Ne.symm hca]
  rw [bcount, hrows, Finset.card_insert_of_notMem hnot]
  rfl

private theorem flips_of_common_adj {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {X E : RowQ r s L B} {i j : Fin n}
    (bad : {M : MarginClass r s // rowProj hB M = E})
    (X₁ X₂ : {M : MarginClass r s // rowProj hB M = X})
    {a₁ a₂ : Fin (m + 1)}
    (ha₁ : a₁ ∈ rowsA L i j bad.val.val)
    (ha₂ : a₂ ∈ rowsA L i j bad.val.val) (ha₁₂ : a₁ ≠ a₂)
    (hX₁ : X₁.val.val = Brualdi.Ryser.switchMat bad.val.val L a₁ j i)
    (hX₂ : X₂.val.val = Brualdi.Ryser.switchMat bad.val.val L a₂ j i) :
    (fibreGraph (flipGraph r s) (rowProj hB) X).Adj X₁ X₂ := by
  classical
  have ha₁L : a₁ ≠ L := (Finset.mem_filter.mp ha₁).2.1
  have ha₁i : bad.val.val a₁ i = true := (Finset.mem_filter.mp ha₁).2.2.1
  have ha₁j : bad.val.val a₁ j = false := (Finset.mem_filter.mp ha₁).2.2.2
  have ha₂L : a₂ ≠ L := (Finset.mem_filter.mp ha₂).2.1
  have ha₂i : bad.val.val a₂ i = true := (Finset.mem_filter.mp ha₂).2.2.1
  have ha₂j : bad.val.val a₂ j = false := (Finset.mem_filter.mp ha₂).2.2.2
  have hij : i ≠ j := by
    intro h
    have h2 : bad.val.val a₁ j = true := h ▸ ha₁i
    rw [ha₁j] at h2
    exact Bool.false_ne_true h2
  have hji : j ≠ i := hij.symm
  have e1pc : X₁.val.val a₁ j = true := by
    rw [hX₁]; simp [Brualdi.Ryser.switchMat, ha₁L, hji]
  have e1qd : X₁.val.val a₂ i = true := by
    rw [hX₁]; simp [Brualdi.Ryser.switchMat, ha₂L, Ne.symm ha₁₂, ha₂i]
  have e1pd : X₁.val.val a₁ i = false := by
    rw [hX₁]; simp [Brualdi.Ryser.switchMat, ha₁L]
  have e1qc : X₁.val.val a₂ j = false := by
    rw [hX₁]; simp [Brualdi.Ryser.switchMat, ha₂L, Ne.symm ha₁₂, ha₂j]
  have e2pc : X₂.val.val a₁ j = false := by
    rw [hX₂]; simp [Brualdi.Ryser.switchMat, ha₁L, ha₁₂, ha₁j]
  have e2qd : X₂.val.val a₂ i = false := by
    rw [hX₂]; simp [Brualdi.Ryser.switchMat, ha₂L]
  have e2pd : X₂.val.val a₁ i = true := by
    rw [hX₂]; simp [Brualdi.Ryser.switchMat, ha₁L, ha₁₂, ha₁i]
  have e2qc : X₂.val.val a₂ j = true := by
    rw [hX₂]; simp [Brualdi.Ryser.switchMat, ha₂L, hji]
  have hint : Interchange X₁.val.val X₂.val.val := by
    refine ⟨a₁, a₂, j, i, ha₁₂, hji, e1pc, e1qd, e1pd, e1qc,
      e2pc, e2qd, e2pd, e2qc, ?_⟩
    intro c d hcd
    push_neg at hcd
    rw [hX₁, hX₂]
    by_cases hcL : c = L
    · subst c
      simp [Brualdi.Ryser.switchMat, Ne.symm ha₁L, Ne.symm ha₂L]
    · by_cases hca₁ : c = a₁
      · subst c
        obtain ⟨hdj, hdi⟩ := hcd (Or.inl rfl)
        simp [Brualdi.Ryser.switchMat, ha₁L, ha₁₂, Ne.symm ha₁₂, hdj, hdi]
      · by_cases hca₂ : c = a₂
        · subst c
          obtain ⟨hdj, hdi⟩ := hcd (Or.inr rfl)
          simp [Brualdi.Ryser.switchMat, ha₂L, ha₁₂, Ne.symm ha₁₂, hdj, hdi]
        · simp [Brualdi.Ryser.switchMat, hcL, hca₁, hca₂]
  have hne : X₁.val ≠ X₂.val := by
    intro h
    have hval : X₁.val.val = X₂.val.val := congrArg Subtype.val h
    have hcell : X₁.val.val a₁ i = X₂.val.val a₁ i := congrFun (congrFun hval a₁) i
    rw [e1pd, e2pd] at hcell
    exact Bool.false_ne_true hcell
  exact fibre_adj_of_switch (hB := hB) (X := X) hint hne

theorem fiber_card_eq_of_col_eq {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j}) (hsij : s i = s j) :
    Fintype.card {M : MarginClass r s // rowProj hB M = X} =
      Fintype.card {M : MarginClass r s // rowProj hB M = E} := by
  classical
  have hiX : i ∈ X.val := (Finset.mem_sdiff.mp (by rw [hXi]; exact Finset.mem_singleton_self i)).1
  have hiE : i ∉ E.val := (Finset.mem_sdiff.mp (by rw [hXi]; exact Finset.mem_singleton_self i)).2
  have hjE : j ∈ E.val := (Finset.mem_sdiff.mp (by rw [hXj]; exact Finset.mem_singleton_self j)).1
  have hjX : j ∉ X.val := (Finset.mem_sdiff.mp (by rw [hXj]; exact Finset.mem_singleton_self j)).2
  have hXE_out : ∀ c, c ≠ i → c ≠ j → (c ∈ X.val ↔ c ∈ E.val) := by
    intro c hci hcj
    constructor
    · intro hcX
      by_contra hcE
      have hmem : c ∈ X.val \ E.val := Finset.mem_sdiff.mpr ⟨hcX, hcE⟩
      rw [hXi] at hmem
      exact hci (Finset.mem_singleton.mp hmem)
    · intro hcE
      by_contra hcX
      have hmem : c ∈ E.val \ X.val := Finset.mem_sdiff.mpr ⟨hcE, hcX⟩
      rw [hXj] at hmem
      exact hcj (Finset.mem_singleton.mp hmem)
  have hswapX_mem : ∀ c, Equiv.swap i j c ∈ X.val ↔ c ∈ E.val := by
    intro c
    by_cases hci : c = i
    · subst c
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => absurd h hjX, fun h => absurd h hiE⟩
    · by_cases hcj : c = j
      · subst c
        rw [Equiv.swap_apply_right]
        exact ⟨fun _ => hjE, fun _ => hiX⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hci hcj]
        exact hXE_out c hci hcj
  have hswapE_mem : ∀ c, Equiv.swap i j c ∈ E.val ↔ c ∈ X.val := by
    intro c
    by_cases hci : c = i
    · subst c
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => hiX, fun _ => hjE⟩
    · by_cases hcj : c = j
      · subst c
        rw [Equiv.swap_apply_right]
        exact ⟨fun h => absurd h hiE, fun h => absurd h hjX⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hci hcj]
        exact (hXE_out c hci hcj).symm
  have hmargins : ∀ M : MarginClass r s,
      HasMargins r s (fun a b => M.val a (Equiv.swap i j b)) := by
    intro M
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have hre : rowSum (fun a b => M.val a (Equiv.swap i j b)) a = rowSum M.val a := by
        unfold rowSum
        exact Fintype.sum_equiv (Equiv.swap i j)
          (fun b => (if M.val a (Equiv.swap i j b) then 1 else 0 : ℕ))
          (fun b => (if M.val a b then 1 else 0 : ℕ)) (fun b => rfl)
      rw [hre]
      exact M.property.1 a
    · have hcol : colSum (fun a b => M.val a (Equiv.swap i j b)) b =
          colSum M.val (Equiv.swap i j b) := rfl
      have hs : s (Equiv.swap i j b) = s b := by
        by_cases hbi : b = i
        · subst b
          rw [Equiv.swap_apply_left]
          exact hsij.symm
        · by_cases hbj : b = j
          · subst b
            rw [Equiv.swap_apply_right]
            exact hsij
          · rw [Equiv.swap_apply_of_ne_of_ne hbi hbj]
      rw [hcol, M.property.2 (Equiv.swap i j b), hs]
  refine Fintype.card_congr
    { toFun := fun M => ⟨⟨fun a b => M.val.val a (Equiv.swap i j b), hmargins M.val⟩, ?_⟩
      invFun := fun M => ⟨⟨fun a b => M.val.val a (Equiv.swap i j b), hmargins M.val⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    have hMX : rowSupport L M.val = X.val := congrArg Subtype.val M.property
    ext b
    simp only [rowProj, rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hb
      have hmem : Equiv.swap i j b ∈ X.val := by
        rw [← hMX]
        simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      exact (hswapX_mem b).mp hmem
    · intro hbE
      have hmem : Equiv.swap i j b ∈ X.val := (hswapX_mem b).mpr hbE
      rw [← hMX] at hmem
      simpa only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  · apply Subtype.ext
    have hME : rowSupport L M.val = E.val := congrArg Subtype.val M.property
    ext b
    simp only [rowProj, rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hb
      have hmem : Equiv.swap i j b ∈ E.val := by
        rw [← hME]
        simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      exact (hswapE_mem b).mp hmem
    · intro hbX
      have hmem : Equiv.swap i j b ∈ E.val := (hswapE_mem b).mpr hbX
      rw [← hME] at hmem
      simpa only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  · intro M
    apply Subtype.ext
    apply Subtype.ext
    funext a b
    show M.val.val a (Equiv.swap i j (Equiv.swap i j b)) = M.val.val a b
    rw [Equiv.swap_apply_self]
  · intro M
    apply Subtype.ext
    apply Subtype.ext
    funext a b
    show M.val.val a (Equiv.swap i j (Equiv.swap i j b)) = M.val.val a b
    rw [Equiv.swap_apply_self]

private theorem exists_ne_of_card_ge_three {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (x : α) :
    ∃ y : α, y ≠ x := by
  classical
  have hpos : 0 < (Finset.univ.erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
  exact ⟨y, (Finset.mem_erase.mp hy).1⟩

private theorem exists_two_ne_of_card_ge_three {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (x : α) :
    ∃ y z : α, y ≠ x ∧ z ≠ x ∧ y ≠ z := by
  classical
  have htwo : 1 < (Finset.univ.erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  rcases Finset.one_lt_card.mp htwo with ⟨y, hy, z, hz, hyz⟩
  exact ⟨y, z, (Finset.mem_erase.mp hy).1, (Finset.mem_erase.mp hz).1, hyz⟩

private theorem exists_mem_ne_of_one_lt_card {α : Type*} [DecidableEq α]
    {S : Finset α} {x : α} (hcard : 1 < S.card) :
    ∃ y ∈ S, y ≠ x := by
  classical
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hab⟩
  by_cases hax : a = x
  · refine ⟨b, hb, ?_⟩
    intro hbx
    exact hab (hax.trans hbx.symm)
  · exact ⟨a, ha, hax⟩

theorem row_two_of_nonbip_avoid {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X E)
    (hXnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = X} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col)
    (hEnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = E} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) E) col)
    (hXconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (x : {M : MarginClass r s // rowProj hB M = X})
    (bad : {M : MarginClass r s // rowProj hB M = E}) :
    ∃ y : {M : MarginClass r s // rowProj hB M = X},
      ∃ z : {M : MarginClass r s // rowProj hB M = E},
        y ≠ x ∧ z ≠ bad ∧ (flipGraph r s).Adj y.val z.val := by
  classical
  have hX3 : 3 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = X} :=
    card_ge_three_of_not_bip_sec5
      (G := fibreGraph (flipGraph r s) (rowProj hB) X) hXnb
  have hE3 : 3 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = E} :=
    card_ge_three_of_not_bip_sec5
      (G := fibreGraph (flipGraph r s) (rowProj hB) E) hEnb
  let cC : ℤ := (s j : ℤ) - s i + 1
  have source_count :
      ∀ Y : {M : MarginClass r s // rowProj hB M = X},
        bcount L i j Y.val.val + s i =
          acount L i j Y.val.val + s j + 1 := by
    intro Y
    have hLi : Y.val.val L i = true :=
      row_cell_true_of_fibre_left (hB := hB) (j := j) hXi Y
    have hLj : Y.val.val L j = false :=
      row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj Y
    exact count_identity_source hLi hLj (Y.val.property.2 i) (Y.val.property.2 j)
  have target_count :
      ∀ Z : {M : MarginClass r s // rowProj hB M = E},
        acount L i j Z.val.val + s j =
          bcount L i j Z.val.val + s i + 1 := by
    intro Z
    have hLi : Z.val.val L i = false :=
      row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X)
        (i := j) (j := i) hXi Z
    have hLj : Z.val.val L j = true :=
      row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X)
        (i := j) (j := i) hXj Z
    exact count_identity_target hLi hLj (Z.val.property.2 i) (Z.val.property.2 j)
  by_cases hc2 : (2 : ℤ) ≤ cC
  · rcases exists_ne_of_card_ge_three hX3 x with ⟨Xp, hXp_ne⟩
    have hsrc := source_count Xp
    have hb_ge_two : 2 ≤ bcount L i j Xp.val.val := by
      have hsrcZ :
          ((bcount L i j Xp.val.val : ℕ) : ℤ) + s i =
            ((acount L i j Xp.val.val : ℕ) : ℤ) + s j + 1 := by
        exact_mod_cast hsrc
      have hac_nonneg : (0 : ℤ) ≤ (acount L i j Xp.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
      have hbZ : (2 : ℤ) ≤ (bcount L i j Xp.val.val : ℤ) := by
        dsimp [cC] at hc2
        omega
      exact_mod_cast hbZ
    have hcross_card := cross_card_eq_bcount r s L B hB hXi hXj Xp
    have hcross_gt_one : 1 < (crossTo (hB := hB) E Xp).card := by
      rw [hcross_card]
      omega
    rcases exists_mem_ne_of_one_lt_card (S := crossTo (hB := hB) E Xp)
        (x := bad) hcross_gt_one with ⟨z, hz, hz_ne_bad⟩
    have hadj : (flipGraph r s).Adj Xp.val z.val := by
      simpa [crossTo] using hz
    exact ⟨Xp, z, hXp_ne, hz_ne_bad, hadj⟩
  have hc_le_one : cC ≤ 1 := by omega
  by_cases hc0 : cC ≤ 0
  · rcases exists_ne_of_card_ge_three hE3 bad with ⟨Ep, hEp_ne⟩
    have htgt := target_count Ep
    have ha_ge_two : 2 ≤ acount L i j Ep.val.val := by
      have htgtZ :
          ((acount L i j Ep.val.val : ℕ) : ℤ) + s j =
            ((bcount L i j Ep.val.val : ℕ) : ℤ) + s i + 1 := by
        exact_mod_cast htgt
      have hb_nonneg : (0 : ℤ) ≤ (bcount L i j Ep.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
      have haZ : (2 : ℤ) ≤ (acount L i j Ep.val.val : ℤ) := by
        dsimp [cC] at hc0
        omega
      exact_mod_cast haZ
    have hcross_card := cross_card_eq_acount r s L B hB hXi hXj Ep
    have hcross_gt_one : 1 < (crossTo (hB := hB) X Ep).card := by
      rw [hcross_card]
      omega
    rcases exists_mem_ne_of_one_lt_card (S := crossTo (hB := hB) X Ep)
        (x := x) hcross_gt_one with ⟨y, hy, hy_ne_x⟩
    have hadj_E_y : (flipGraph r s).Adj Ep.val y.val := by
      simpa [crossTo] using hy
    exact ⟨y, Ep, hy_ne_x, hEp_ne, hadj_E_y.symm⟩
  have hc_eq_one : cC = 1 := by omega
  have hsi_eq_sj : s i = s j := by
    have hZ : (s i : ℤ) = s j := by
      dsimp [cC] at hc_eq_one
      omega
    exact_mod_cast hZ
  by_contra hgoal
  push_neg at hgoal
  rcases exists_two_ne_of_card_ge_three hX3 x with
    ⟨X₁, X₂, hX₁_ne_x, hX₂_ne_x, hX₁_ne_X₂⟩
  have source_bcount_pos
      (Y : {M : MarginClass r s // rowProj hB M = X}) :
      0 < bcount L i j Y.val.val := by
    have hsrc := source_count Y
    have hsrcZ :
        ((bcount L i j Y.val.val : ℕ) : ℤ) + s i =
          ((acount L i j Y.val.val : ℕ) : ℤ) + s j + 1 := by
      exact_mod_cast hsrc
    have hac_nonneg : (0 : ℤ) ≤ (acount L i j Y.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
    have hbZ : (1 : ℤ) ≤ (bcount L i j Y.val.val : ℤ) := by
      dsimp [cC] at hc_eq_one
      omega
    exact_mod_cast hbZ
  have crossing_hits_bad
      (Y : {M : MarginClass r s // rowProj hB M = X}) (hY_ne_x : Y ≠ x) :
      (flipGraph r s).Adj Y.val bad.val := by
    have hcard := cross_card_eq_bcount r s L B hB hXi hXj Y
    have hpos_card : 0 < (crossTo (hB := hB) E Y).card := by
      rw [hcard]
      exact source_bcount_pos Y
    rcases Finset.card_pos.mp hpos_card with ⟨N, hN⟩
    have hadj : (flipGraph r s).Adj Y.val N.val := by
      simpa [crossTo] using hN
    have hN_eq_bad : N = bad := by
      by_contra hN_ne_bad
      exact hgoal Y N hY_ne_x hN_ne_bad hadj
    simpa [hN_eq_bad] using hadj
  have hX₁_bad : (flipGraph r s).Adj X₁.val bad.val :=
    crossing_hits_bad X₁ hX₁_ne_x
  have hX₂_bad : (flipGraph r s).Adj X₂.val bad.val :=
    crossing_hits_bad X₂ hX₂_ne_x
  have hX₁_mem : X₁ ∈ crossTo (hB := hB) X bad := by
    simpa [crossTo] using hX₁_bad.symm
  have hX₂_mem : X₂ ∈ crossTo (hB := hB) X bad := by
    simpa [crossTo] using hX₂_bad.symm
  have hbad_cross_gt_one : 1 < (crossTo (hB := hB) X bad).card :=
    Finset.one_lt_card.mpr ⟨X₁, hX₁_mem, X₂, hX₂_mem, hX₁_ne_X₂⟩
  have hac_bad_ge_two : 2 ≤ acount L i j bad.val.val := by
    have hcard := cross_card_eq_acount r s L B hB hXi hXj bad
    rw [← hcard]
    omega
  have hcross_X₁_le_one : (crossTo (hB := hB) E X₁).card ≤ 1 := by
    have hsub : crossTo (hB := hB) E X₁ ⊆ ({bad} : Finset {M : MarginClass r s // rowProj hB M = E}) := by
      intro N hN
      have hadj : (flipGraph r s).Adj X₁.val N.val := by
        simpa [crossTo] using hN
      have hN_eq_bad : N = bad := by
        by_contra hN_ne_bad
        exact hgoal X₁ N hX₁_ne_x hN_ne_bad hadj
      simp [hN_eq_bad]
    have hle := Finset.card_le_card hsub
    simpa using hle
  have hb_X₁_le_one : bcount L i j X₁.val.val ≤ 1 := by
    have hcard := cross_card_eq_bcount r s L B hB hXi hXj X₁
    rw [← hcard]
    exact hcross_X₁_le_one
  have hbadLi : bad.val.val L i = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X)
      (i := j) (j := i) hXi bad
  have hbadLj : bad.val.val L j = true :=
    row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X)
      (i := j) (j := i) hXj bad
  have hX₁Li : X₁.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXi X₁
  have hX₁Lj : X₁.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj X₁
  have hint_bad_X₁ : Interchange bad.val.val X₁.val.val := by
    have hadj : (flipGraph r s).Adj bad.val X₁.val := hX₁_bad.symm
    rw [flipGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_hne, hint | hint⟩
    · exact hint
    · exact interchange_symm hint
  rcases crossing_eq_switchMat (M := bad.val.val) (N := X₁.val.val)
      (L := L) (i := j) (j := i)
      hbadLj hbadLi hX₁Lj hX₁Li hint_bad_X₁ with
    ⟨a, haL, haj_false, hai_true, hX₁_eq_switch⟩
  have haA : a ∈ rowsA L i j bad.val.val := by
    simp [rowsA, haL, hai_true, haj_false]
  have hflip := bcount_flip (L := L) (a := a) (i := i) (j := j)
    (M := bad.val.val) hbadLi hbadLj haA
  have hflip_X₁ :
      bcount L i j X₁.val.val = bcount L i j bad.val.val + 1 := by
    simpa [hX₁_eq_switch] using hflip
  have hbad_counts :
      bcount L i j bad.val.val + 1 = acount L i j bad.val.val := by
    have htgt := target_count bad
    omega
  have hb_X₁_ge_two : 2 ≤ bcount L i j X₁.val.val := by
    rw [hflip_X₁, hbad_counts]
    exact hac_bad_ge_two
  omega

theorem row_interface_all_of_bip_source {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B} {i j : Fin n}
    (hXY : X.val \ Y.val = {i}) (hYX : Y.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (hconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    {col : {M : MarginClass r s // rowProj hB M = X} → Bool}
    (hbip : IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col) :
    ∀ M : {M : MarginClass r s // rowProj hB M = X},
      M.val ∈ interface (flipGraph r s) (rowProj hB) X Y := by
  classical
  let S : Finset {M : MarginClass r s // rowProj hB M = X} :=
    Finset.univ.filter (fun M =>
      M.val ∉ interface (flipGraph r s) (rowProj hB) X Y)
  have hinterface_nonempty :
      ∃ M : {M : MarginClass r s // rowProj hB M = X},
        M.val ∈ interface (flipGraph r s) (rowProj hB) X Y := by
    rcases hused with ⟨_hXYne, u, hu, v, hv, huv⟩
    have huX : rowProj hB u = X := (Finset.mem_filter.mp hu).2
    have huI : u ∈ interface (flipGraph r s) (rowProj hB) X Y := by
      rw [mem_interface_iff]
      exact ⟨hu, v, hv, huv⟩
    exact ⟨⟨u, huX⟩, huI⟩
  have hSproper : S ≠ Finset.univ := by
    rcases hinterface_nonempty with ⟨M, hM⟩
    intro h
    have hMinS : M ∈ S := by simpa [h]
    exact (Finset.mem_filter.mp hMinS).2 hM
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨M₀, hM₀⟩
  have hSne : S.Nonempty := ⟨M₀, by simp [S, hM₀]⟩
  rcases connected_boundary_edge (G := fibreGraph (flipGraph r s) (rowProj hB) X)
      hconn hSne hSproper with ⟨M, hMS, M', hM'S, hadj⟩
  have hM_not_interface : M.val ∉ interface (flipGraph r s) (rowProj hB) X Y :=
    (Finset.mem_filter.mp hMS).2
  have hM'_interface : M'.val ∈ interface (flipGraph r s) (rowProj hB) X Y := by
    by_contra h
    exact hM'S (by simp [S, h])
  have hW' : HasWitness L i j M'.val.val :=
    (row_interface_iff_hasWitness r s L B hB hXY hYX M').mp hM'_interface
  have hN : Nested L i j M.val.val :=
    (nested_iff_not_hasWitness.mpr (by
      intro hW
      exact hM_not_interface
        ((row_interface_iff_hasWitness r s L B hB hXY hYX M).mpr hW)))
  have hMLi : M.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXY M
  have hMLj : M.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hYX M
  have hrowL : ∀ b, M.val.val L b = M'.val.val L b := by
    have hsame : rowSupport L M.val = rowSupport L M'.val := by
      exact (congrArg Subtype.val M.property).trans
        (congrArg Subtype.val M'.property).symm
    exact row_eq_of_same_rowSupport hsame
  have hint : Interchange M.val.val M'.val.val := by
    rw [fibreGraph, SimpleGraph.induce_adj, flipGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_hne, hint | hint⟩
    · exact hint
    · exact interchange_symm hint
  have hij : i ≠ j := by
    have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
    have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
    intro h
    exact (Finset.mem_sdiff.mp hi).2 (by simpa [h] using (Finset.mem_sdiff.mp hj).1)
  rcases boundary_interchange_yields_alternate_config
      (L := L) (i := i) (j := j) hij hN hW' hrowL hMLi hMLj hint with
    ⟨u, v, c, huL, hvL, huv, hic, hjc, hui, huj, huc, hvi, hvj, hvc, hcorner⟩
  rcases alternate_switch_triangle_core huv hij hic hjc hui huj huc hvi hvj hvc with
    ⟨hb_i, hb_j, hb_ji, heq_j⟩
  let Mi : {N : MarginClass r s // rowProj hB N = X} :=
    switch_margin_fibre_vertex (hB := hB) M huL hvL hb_i
  let Mj : {N : MarginClass r s // rowProj hB N = X} :=
    switch_margin_fibre_vertex (hB := hB) M huL hvL hb_j
  have hM_Mi : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj M Mi := by
    have hint_i : Interchange M.val.val Mi.val.val := by
      simpa [Mi, switch_margin_fibre_vertex] using Brualdi.Ryser.switch_interchange hb_i
    have hne_i : M.val ≠ Mi.val := by
      intro heq
      have hval : Mi.val.val = M.val.val := congrArg Subtype.val heq.symm
      exact Brualdi.Ryser.switchMat_ne hb_i (by simpa [Mi, switch_margin_fibre_vertex] using hval)
    exact fibre_adj_of_switch (hB := hB) (X := X) hint_i hne_i
  have hMi_Mj : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj Mi Mj := by
    have hint_ij : Interchange Mi.val.val Mj.val.val := by
      have hsw := Brualdi.Ryser.switch_interchange hb_ji
      simpa [Mi, Mj, switch_margin_fibre_vertex, heq_j] using hsw
    have hne_ij : Mi.val ≠ Mj.val := by
      intro heq
      have hval : Mj.val.val = Mi.val.val := congrArg Subtype.val heq.symm
      exact Brualdi.Ryser.switchMat_ne hb_ji
        (by simpa [Mi, Mj, switch_margin_fibre_vertex, heq_j] using hval)
    exact fibre_adj_of_switch (hB := hB) (X := X) hint_ij hne_ij
  have hMj_M : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj Mj M := by
    have hM_Mj : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj M Mj := by
      have hint_j : Interchange M.val.val Mj.val.val := by
        simpa [Mj, switch_margin_fibre_vertex] using Brualdi.Ryser.switch_interchange hb_j
      have hne_j : M.val ≠ Mj.val := by
        intro heq
        have hval : Mj.val.val = M.val.val := congrArg Subtype.val heq.symm
        exact Brualdi.Ryser.switchMat_ne hb_j
          (by simpa [Mj, switch_margin_fibre_vertex] using hval)
      exact fibre_adj_of_switch (hB := hB) (X := X) hint_j hne_j
    exact hM_Mj.symm
  exact bipartite_no_triangle hbip hM_Mi hMi_Mj hMj_M

theorem row_interface_two_of_nonbip {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B} {i j : Fin n}
    (hXY : X.val \ Y.val = {i}) (hYX : Y.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (hconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = X} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col) :
    ∃ M₁ ∈ interface (flipGraph r s) (rowProj hB) X Y,
      ∃ M₂ ∈ interface (flipGraph r s) (rowProj hB) X Y, M₁ ≠ M₂ := by
  classical
  let I : Finset {M : MarginClass r s // rowProj hB M = X} :=
    Finset.univ.filter (fun M =>
      M.val ∈ interface (flipGraph r s) (rowProj hB) X Y)
  have hI_nonempty : I.Nonempty := by
    rcases hused with ⟨_hXYne, u, hu, v, hv, huv⟩
    have huX : rowProj hB u = X := (Finset.mem_filter.mp hu).2
    have huI : u ∈ interface (flipGraph r s) (rowProj hB) X Y := by
      rw [mem_interface_iff]
      exact ⟨hu, v, hv, huv⟩
    refine ⟨⟨u, huX⟩, ?_⟩
    simp [I, huI]
  rcases hI_nonempty with ⟨M₁, hM₁I⟩
  have hM₁_interface : M₁.val ∈ interface (flipGraph r s) (rowProj hB) X Y :=
    (Finset.mem_filter.mp hM₁I).2
  by_cases hsecond : ∃ M₂ : {M : MarginClass r s // rowProj hB M = X},
      M₂.val ∈ interface (flipGraph r s) (rowProj hB) X Y ∧ M₁ ≠ M₂
  · rcases hsecond with ⟨M₂, hM₂I, hne⟩
    exact ⟨M₁.val, hM₁_interface, M₂.val, hM₂I, by
      intro hval
      exact hne (Subtype.ext hval)⟩
  have hunique : ∀ M₂ : {M : MarginClass r s // rowProj hB M = X},
      M₂.val ∈ interface (flipGraph r s) (rowProj hB) X Y → M₂ = M₁ := by
    intro M₂ hM₂
    by_contra hne
    exact hsecond ⟨M₂, hM₂, by exact fun h => hne h.symm⟩
  have hcard3 :
      3 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = X} :=
    card_ge_three_of_not_bip_sec5
      (G := fibreGraph (flipGraph r s) (rowProj hB) X) hnb
  let S : Finset {M : MarginClass r s // rowProj hB M = X} := {M₁}
  have hSproper : S ≠ Finset.univ := by
    intro h
    have hcard_le_one :
        Fintype.card {M : MarginClass r s // rowProj hB M = X} ≤ 1 := by
      rw [← Finset.card_univ]
      have hcardS : S.card = 1 := by simp [S]
      rw [← h, hcardS]
    omega
  rcases connected_boundary_edge (G := fibreGraph (flipGraph r s) (rowProj hB) X)
      hconn (S := S) (by simp [S]) hSproper with
    ⟨A, hAS, N, hNS, hadj⟩
  have hAeq : A = M₁ := by simpa [S] using hAS
  subst A
  have hN_not_interface : N.val ∉ interface (flipGraph r s) (rowProj hB) X Y := by
    intro hNint
    have hN_eq : N = M₁ := hunique N hNint
    exact hNS (by simp [S, hN_eq])
  have hW₁ : HasWitness L i j M₁.val.val :=
    (row_interface_iff_hasWitness r s L B hB hXY hYX M₁).mp hM₁_interface
  have hNestedN : Nested L i j N.val.val :=
    (nested_iff_not_hasWitness.mpr (by
      intro hW
      exact hN_not_interface
        ((row_interface_iff_hasWitness r s L B hB hXY hYX N).mpr hW)))
  have hNLi : N.val.val L i = true :=
    row_cell_true_of_fibre_left (hB := hB) (j := j) hXY N
  have hNLj : N.val.val L j = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hYX N
  have hrowL : ∀ b, N.val.val L b = M₁.val.val L b := by
    have hsame : rowSupport L N.val = rowSupport L M₁.val := by
      exact (congrArg Subtype.val N.property).trans
        (congrArg Subtype.val M₁.property).symm
    exact row_eq_of_same_rowSupport hsame
  have hint : Interchange N.val.val M₁.val.val := by
    rw [fibreGraph, SimpleGraph.induce_adj, flipGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨_hne, hint | hint⟩
    · exact interchange_symm hint
    · exact hint
  have hij : i ≠ j := by
    have hi : i ∈ X.val \ Y.val := by rw [hXY]; simp
    have hj : j ∈ Y.val \ X.val := by rw [hYX]; simp
    intro h
    exact (Finset.mem_sdiff.mp hi).2 (by simpa [h] using (Finset.mem_sdiff.mp hj).1)
  rcases boundary_interchange_yields_alternate_config
      (L := L) (i := i) (j := j) hij hNestedN hW₁ hrowL hNLi hNLj hint with
    ⟨u, v, c, huL, hvL, huv, hic, hjc, hui, huj, huc, hvi, hvj, hvc, hcorner⟩
  rcases alternate_switch_triangle_core huv hij hic hjc hui huj huc hvi hvj hvc with
    ⟨hb_i, hb_j, _hb_ji, _heq_j⟩
  let Ni : {P : MarginClass r s // rowProj hB P = X} :=
    switch_margin_fibre_vertex (hB := hB) N huL hvL hb_i
  let Nj : {P : MarginClass r s // rowProj hB P = X} :=
    switch_margin_fibre_vertex (hB := hB) N huL hvL hb_j
  rcases hcorner with hM₁i | hM₁j
  · have hNjW : HasWitness L i j Nj.val.val := by
      refine ⟨v, hvL, ?_, ?_⟩
      · simp [Nj, switch_margin_fibre_vertex, Brualdi.Ryser.switchMat,
          huv.symm, hij, hic, hvi]
      · simp [Nj, switch_margin_fibre_vertex, Brualdi.Ryser.switchMat, huv.symm, hjc]
    have hNjI : Nj.val ∈ interface (flipGraph r s) (rowProj hB) X Y :=
      (row_interface_iff_hasWitness r s L B hB hXY hYX Nj).mpr hNjW
    have hNj_ne_M₁ : Nj.val ≠ M₁.val := by
      intro hval
      have hbad : Brualdi.Ryser.switchMat N.val.val u v j c =
          Brualdi.Ryser.switchMat N.val.val u v i c := by
        exact (congrArg Subtype.val hval).trans hM₁i
      have hcell : Brualdi.Ryser.switchMat N.val.val u v j c u j =
          Brualdi.Ryser.switchMat N.val.val u v i c u j := by
        exact congrFun (congrFun hbad u) j
      simp [Brualdi.Ryser.switchMat, huv, hij.symm, hjc, huj] at hcell
    exact ⟨M₁.val, hM₁_interface, Nj.val, hNjI, by
      intro hval
      exact hNj_ne_M₁ hval.symm⟩
  · have hNiW : HasWitness L i j Ni.val.val := by
      refine ⟨u, huL, ?_, ?_⟩
      · simp [Ni, switch_margin_fibre_vertex, Brualdi.Ryser.switchMat]
      · simp [Ni, switch_margin_fibre_vertex, Brualdi.Ryser.switchMat,
          huv, hij.symm, hjc, huj]
    have hNiI : Ni.val ∈ interface (flipGraph r s) (rowProj hB) X Y :=
      (row_interface_iff_hasWitness r s L B hB hXY hYX Ni).mpr hNiW
    have hNi_ne_M₁ : Ni.val ≠ M₁.val := by
      intro hval
      have hbad : Brualdi.Ryser.switchMat N.val.val u v i c =
          Brualdi.Ryser.switchMat N.val.val u v j c := by
        exact (congrArg Subtype.val hval).trans hM₁j
      have hcell : Brualdi.Ryser.switchMat N.val.val u v i c u i =
          Brualdi.Ryser.switchMat N.val.val u v j c u i := by
        exact congrFun (congrFun hbad u) i
      simp [Brualdi.Ryser.switchMat, huv, hij, hic, hui] at hcell
    exact ⟨M₁.val, hM₁_interface, Ni.val, hNiI, by
      intro hval
      exact hNi_ne_M₁ hval.symm⟩

/-- A separating row-pattern gives distinct quotient endpoints. -/
theorem rowProj_ne_of_rowPat_ne {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    {a b : MarginClass r s} (hsep : rowPat L a ≠ rowPat L b) :
    rowProj hB a ≠ rowProj hB b := by
  classical
  intro hproj
  have hsupport : rowSupport L a = rowSupport L b := congrArg Subtype.val hproj
  apply hsep
  calc
    rowPat L a = patOfSet (rowSupport L a) :=
      rowPat_eq_patOfSet_of_rowSupport rfl
    _ = patOfSet (rowSupport L b) := by rw [hsupport]
    _ = rowPat L b := (rowPat_eq_patOfSet_of_rowSupport rfl).symm

/-- In a non-bipartite MH graph, the MH witness is the Hamilton-connected branch. -/
theorem isMH_hamConnected_of_nonbip {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hMH : IsMH G)
    (hnb : ¬ ∃ col : V → Bool, IsProper2Coloring G col) :
    IsHamConnected G := by
  rcases hMH with hconn | ⟨col, hproper, _hsurj, _hlace⟩
  · exact hconn
  · exact False.elim (hnb ⟨col, hproper⟩)

/-- Buffer and local-interface data assumed from Block 3c / 5.8 and later interface bookkeeping. -/
structure PivotBufferData {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}) where
  hQnb : ¬ ∃ col : RowQ r s L B → Bool,
    IsProper2Coloring (rowQuotientGraph r s L B) col
  buffer : RowQ r s L B
  hbuf_nb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = buffer} → Bool,
    IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) buffer) col
  hfib_conn : ∀ X : RowQ r s L B,
    (fibreGraph (flipGraph r s) (rowProj hB) X).Connected
  hfib_isMH : ∀ X : RowQ r s L B,
    IsMH (fibreGraph (flipGraph r s) (rowProj hB) X)
  hinterface_step :
    ∀ {X Y : RowQ r s L B},
      quotientAdj (flipGraph r s) (rowProj hB) X Y →
        ∀ x : {M : MarginClass r s // rowProj hB M = X},
          ∃ y : {M : MarginClass r s // rowProj hB M = X},
            ∃ z : {M : MarginClass r s // rowProj hB M = Y},
              Nonempty
                {choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x y //
                  (flipGraph r s).Adj y.val z.val}
  hinterface_step_to_buffer_avoid :
    ∀ {X : RowQ r s L B},
      quotientAdj (flipGraph r s) (rowProj hB) X buffer →
        ∀ (x : {M : MarginClass r s // rowProj hB M = X})
          (bad : {M : MarginClass r s // rowProj hB M = buffer}),
          ∃ y : {M : MarginClass r s // rowProj hB M = X},
            ∃ z : {M : MarginClass r s // rowProj hB M = buffer},
              z ≠ bad ∧
                Nonempty
                  {choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x y //
                    (flipGraph r s).Adj y.val z.val}

private abbrev RowFibre {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (X : RowQ r s L B) :=
  {M : MarginClass r s // rowProj hB M = X}

private theorem rowFibre_nonempty {m n : ℕ} {r : Fin (m + 1) → ℕ}
    {s : Fin n → ℕ} {L : Fin (m + 1)} {B : BaseFamily (Fin n)}
    {hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}}
    (X : RowQ r s L B) : Nonempty (RowFibre hB X) := by
  rcases (hB X.val).mp X.property with ⟨M⟩
  exact ⟨⟨M.val, by
    apply Subtype.ext
    exact M.property⟩⟩

/-- The row interface data needed by `PivotBufferData.hinterface_step`. -/
theorem row_hinterface_step {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (hfib_conn : ∀ X : RowQ r s L B,
      (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hfib_isMH : ∀ X : RowQ r s L B,
      IsMH (fibreGraph (flipGraph r s) (rowProj hB) X)) :
    ∀ {X Y : RowQ r s L B},
      quotientAdj (flipGraph r s) (rowProj hB) X Y →
        ∀ x : {M : MarginClass r s // rowProj hB M = X},
          ∃ y : {M : MarginClass r s // rowProj hB M = X},
            ∃ z : {M : MarginClass r s // rowProj hB M = Y},
              Nonempty
                {choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x y //
                  (flipGraph r s).Adj y.val z.val} := by
  classical
  intro X Y hused x
  rcases rowQuotient_singletons_of_quotientAdj r s L B hB hused with
    ⟨i, j, hXY, hYX⟩
  let G := flipGraph r s
  let π := rowProj hB
  have hfinish_ham :
      ∀ {u : MarginClass r s},
        u ∈ interface G π X Y → x.val ≠ u →
          IsHamConnected (fibreGraph G π X) →
            ∃ y : {M : MarginClass r s // π M = X},
              ∃ z : {M : MarginClass r s // π M = Y},
                Nonempty
                  {choice : FibreTerminalChoice G π X x y // G.Adj y.val z.val} := by
    intro u hu hxu hconn
    have huX : u ∈ fibre π X := interface_sub_fibre G π X Y hu
    rcases (mem_interface_iff.mp hu).2 with ⟨v, hvY, huv⟩
    let y : {M : MarginClass r s // π M = X} := ⟨u, by simpa [fibre] using huX⟩
    let z : {M : MarginClass r s // π M = Y} := ⟨v, by simpa [fibre] using hvY⟩
    refine ⟨y, z, ⟨⟨?_, by simpa [G, y, z] using huv⟩⟩⟩
    exact FibreTerminalChoice.hamConnected hconn (by
      intro hxy
      exact hxu (congrArg Subtype.val hxy))
  have hfinish_singleton :
      (∀ v : MarginClass r s, v ∈ fibre π X → v = x.val) →
        ∃ y : {M : MarginClass r s // π M = X},
          ∃ z : {M : MarginClass r s // π M = Y},
            Nonempty
              {choice : FibreTerminalChoice G π X x y // G.Adj y.val z.val} := by
    intro huniq
    rcases hused with ⟨_hneXY, u, huX, v, hvY, huv⟩
    have hux : u = x.val := huniq u huX
    let z : {M : MarginClass r s // π M = Y} := ⟨v, by simpa [fibre] using hvY⟩
    refine ⟨x, z, ⟨⟨?_, ?_⟩⟩⟩
    · exact FibreTerminalChoice.singleton rfl (by
        intro v hv
        exact huniq v hv)
    · simpa [G, π, z, hux] using huv
  rcases hfib_isMH X with hconn | ⟨col, hproper, hsurj, hlace⟩
  · by_cases hnb :
        ¬ ∃ col : {M : MarginClass r s // π M = X} → Bool,
          IsProper2Coloring (fibreGraph G π X) col
    · rcases row_interface_two_of_nonbip r s L B hB hXY hYX hused (hfib_conn X)
          (by simpa [G, π] using hnb) with
        ⟨M₁, hM₁, M₂, hM₂, hM₁M₂⟩
      by_cases hxM₁ : x.val = M₁
      · exact hfinish_ham hM₂ (by
          intro hxM₂
          exact hM₁M₂ (hxM₁.symm.trans hxM₂)) (by simpa [G, π] using hconn)
      · exact hfinish_ham hM₁ hxM₁ (by simpa [G, π] using hconn)
    · have hbip_ex :
          ∃ col : {M : MarginClass r s // π M = X} → Bool,
            IsProper2Coloring (fibreGraph G π X) col :=
        Classical.byContradiction hnb
      rcases hbip_ex with ⟨col, hbip⟩
      have hall :
          ∀ M : {M : MarginClass r s // π M = X},
            M.val ∈ interface G π X Y := by
        simpa [G, π] using
          row_interface_all_of_bip_source r s L B hB hXY hYX hused (hfib_conn X) hbip
      by_cases huniq : ∀ v : MarginClass r s, v ∈ fibre π X → v = x.val
      · exact hfinish_singleton huniq
      · push_neg at huniq
        rcases huniq with ⟨u, huX, hux⟩
        let y : {M : MarginClass r s // π M = X} := ⟨u, by simpa [fibre] using huX⟩
        exact hfinish_ham (hall y) (by
          intro hxu
          exact hux hxu.symm) (by simpa [G, π] using hconn)
  · have hall :
        ∀ M : {M : MarginClass r s // π M = X},
          M.val ∈ interface G π X Y := by
      simpa [G, π] using
        row_interface_all_of_bip_source r s L B hB hXY hYX hused (hfib_conn X) hproper
    rcases hsurj (!(col x)) with ⟨y, hy⟩
    have hxy_col : col x ≠ col y := by
      rw [hy]
      cases col x <;> decide
    rcases (mem_interface_iff.mp (hall y)).2 with ⟨v, hvY, hyv⟩
    let z : {M : MarginClass r s // π M = Y} := ⟨v, by simpa [fibre] using hvY⟩
    refine ⟨y, z, ⟨⟨?_, by simpa [G, π, z] using hyv⟩⟩⟩
    exact FibreTerminalChoice.hamLaceable col hlace hxy_col

/-! ### Lemma 5.8, as printed (2026-07-05, Jeff's call: "follow the paper").

The paper's proof: with `D = s j - s i + 1`, the margin identities pin `b - a = D` on the
source side and `a - b = 2 - D` on the target side; `D = 1` is excluded by the column-swap
isomorphism (a bipartite fiber cannot be isomorphic to a non-bipartite one), `D < 0` by a
triangle among three flips of a common target inside the bipartite source fiber; `D ≥ 2`
gives every source vertex two crossing edges outright, and `D = 0` splits on `|C| = 2`
(both members adjacent to all of `E`) vs `|C| ≥ 4` (a single reached target would make the
color class a clique). The development's original constructive proof is kept below as
`row_bip_source_avoid_direct`. -/

private def colSwapMat {m n : ℕ} (i j : Fin n) (M : ZeroOneMat (m + 1) n) :
    ZeroOneMat (m + 1) n :=
  fun a b => M a (Equiv.swap i j b)

private theorem colSwapMat_invol {m n : ℕ} (i j : Fin n) (M : ZeroOneMat (m + 1) n) :
    colSwapMat i j (colSwapMat i j M) = M := by
  funext a b
  simp [colSwapMat, Equiv.swap_apply_self]

private theorem colSwapMat_interchange {m n : ℕ} {i j : Fin n}
    {M N : ZeroOneMat (m + 1) n} (h : Interchange M N) :
    Interchange (colSwapMat i j M) (colSwapMat i j N) := by
  obtain ⟨r₁, r₂, c₁, c₂, hr, hc, hM11, hM22, hM12, hM21, hN11, hN22, hN12, hN21, hout⟩ := h
  refine ⟨r₁, r₂, Equiv.swap i j c₁, Equiv.swap i j c₂, hr,
    fun hcc => hc ((Equiv.swap i j).injective hcc), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [colSwapMat, Equiv.swap_apply_self] using hM11
  · simpa [colSwapMat, Equiv.swap_apply_self] using hM22
  · simpa [colSwapMat, Equiv.swap_apply_self] using hM12
  · simpa [colSwapMat, Equiv.swap_apply_self] using hM21
  · simpa [colSwapMat, Equiv.swap_apply_self] using hN11
  · simpa [colSwapMat, Equiv.swap_apply_self] using hN22
  · simpa [colSwapMat, Equiv.swap_apply_self] using hN12
  · simpa [colSwapMat, Equiv.swap_apply_self] using hN21
  · intro a b hb
    show N a (Equiv.swap i j b) = M a (Equiv.swap i j b)
    apply hout
    rintro ⟨ha, hbc⟩
    apply hb
    refine ⟨ha, ?_⟩
    rcases hbc with hbc | hbc
    · exact Or.inl (by rw [← hbc, Equiv.swap_apply_self])
    · exact Or.inr (by rw [← hbc, Equiv.swap_apply_self])

private theorem colSwapMat_hasMargins {m n : ℕ} {r : Fin (m + 1) → ℕ} {s : Fin n → ℕ}
    {i j : Fin n} (hsij : s i = s j) {M : ZeroOneMat (m + 1) n} (h : HasMargins r s M) :
    HasMargins r s (colSwapMat i j M) := by
  constructor
  · intro a
    have hre : rowSum (colSwapMat i j M) a = rowSum M a := by
      unfold rowSum colSwapMat
      exact Fintype.sum_equiv (Equiv.swap i j)
        (fun b => (if M a (Equiv.swap i j b) then 1 else 0 : ℕ))
        (fun b => (if M a b then 1 else 0 : ℕ)) (fun b => rfl)
    rw [hre]
    exact h.1 a
  · intro b
    have hcol : colSum (colSwapMat i j M) b = colSum M (Equiv.swap i j b) := rfl
    have hs : s (Equiv.swap i j b) = s b := by
      by_cases hbi : b = i
      · subst b
        rw [Equiv.swap_apply_left]
        exact hsij.symm
      · by_cases hbj : b = j
        · subst b
          rw [Equiv.swap_apply_right]
          exact hsij
        · rw [Equiv.swap_apply_of_ne_of_ne hbi hbj]
    rw [hcol, h.2 (Equiv.swap i j b), hs]

/-- The `D = 1` exclusion of the printed Lemma 5.8: with `s i = s j`, swapping columns
    `i, j` carries the fiber of `E` onto the fiber of `X`, so a proper 2-coloring of `X`'s
    fiber transports to one of `E`'s — impossible when `E`'s fiber is non-bipartite. -/
private theorem row_bip_source_col_eq_contra {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j}) (hsij : s i = s j)
    (hEnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = E} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) E) col)
    {col : {M : MarginClass r s // rowProj hB M = X} → Bool}
    (hproper : IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col) :
    False := by
  classical
  have hiX : i ∈ X.val := (Finset.mem_sdiff.mp (by rw [hXi]; exact Finset.mem_singleton_self i)).1
  have hiE : i ∉ E.val := (Finset.mem_sdiff.mp (by rw [hXi]; exact Finset.mem_singleton_self i)).2
  have hjE : j ∈ E.val := (Finset.mem_sdiff.mp (by rw [hXj]; exact Finset.mem_singleton_self j)).1
  have hjX : j ∉ X.val := (Finset.mem_sdiff.mp (by rw [hXj]; exact Finset.mem_singleton_self j)).2
  have hXE_out : ∀ c, c ≠ i → c ≠ j → (c ∈ X.val ↔ c ∈ E.val) := by
    intro c hci hcj
    constructor
    · intro hcX
      by_contra hcE
      have hmem : c ∈ X.val \ E.val := Finset.mem_sdiff.mpr ⟨hcX, hcE⟩
      rw [hXi] at hmem
      exact hci (Finset.mem_singleton.mp hmem)
    · intro hcE
      by_contra hcX
      have hmem : c ∈ E.val \ X.val := Finset.mem_sdiff.mpr ⟨hcE, hcX⟩
      rw [hXj] at hmem
      exact hcj (Finset.mem_singleton.mp hmem)
  have hswapE_mem : ∀ c, Equiv.swap i j c ∈ E.val ↔ c ∈ X.val := by
    intro c
    by_cases hci : c = i
    · subst c
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => hiX, fun _ => hjE⟩
    · by_cases hcj : c = j
      · subst c
        rw [Equiv.swap_apply_right]
        exact ⟨fun h => absurd h hiE, fun h => absurd h hjX⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hci hcj]
        exact (hXE_out c hci hcj).symm
  -- the swap sends E's fiber into X's fiber
  have hmap : ∀ N : {M : MarginClass r s // rowProj hB M = E},
      ∃ P : {M : MarginClass r s // rowProj hB M = X},
        P.val.val = colSwapMat i j N.val.val := by
    intro N
    have hmarg : HasMargins r s (colSwapMat i j N.val.val) :=
      colSwapMat_hasMargins hsij N.val.property
    have hsupp : rowSupport L ⟨colSwapMat i j N.val.val, hmarg⟩ = X.val := by
      have hNsupp : rowSupport L N.val = E.val := congrArg Subtype.val N.property
      ext b
      simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      show colSwapMat i j N.val.val L b = true ↔ b ∈ X.val
      have : colSwapMat i j N.val.val L b = N.val.val L (Equiv.swap i j b) := rfl
      rw [this]
      have hmem : N.val.val L (Equiv.swap i j b) = true ↔ Equiv.swap i j b ∈ E.val := by
        rw [← hNsupp]
        simp [rowSupport]
      rw [hmem]
      exact hswapE_mem b
    exact ⟨⟨⟨colSwapMat i j N.val.val, hmarg⟩, Subtype.ext hsupp⟩, rfl⟩
  choose φ hφ using hmap
  -- transported coloring
  apply hEnb
  refine ⟨fun N => col (φ N), ?_⟩
  intro N₁ N₂ hadj
  have hadj' := hadj
  rw [fibreGraph, SimpleGraph.induce_adj, flipGraph, SimpleGraph.fromRel_adj] at hadj'
  have hne : N₁.val ≠ N₂.val := fun h => hadj'.1 (by exact_mod_cast h)
  have hint : Interchange N₁.val.val N₂.val.val ∨ Interchange N₂.val.val N₁.val.val := hadj'.2
  have hφne : φ N₁ ≠ φ N₂ := by
    intro h
    apply hne
    have h1 := hφ N₁
    have h2 := hφ N₂
    rw [h] at h1
    have hswap : colSwapMat i j N₁.val.val = colSwapMat i j N₂.val.val := h1.symm.trans h2
    have := congrArg (colSwapMat i j) hswap
    rw [colSwapMat_invol, colSwapMat_invol] at this
    exact Subtype.ext this
  have hadjφ : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj (φ N₁) (φ N₂) := by
    rw [fibreGraph, SimpleGraph.induce_adj, flipGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun h => hφne (Subtype.ext (by exact_mod_cast h)), ?_⟩
    rcases hint with hI | hI
    · left
      have := colSwapMat_interchange (i := i) (j := j) hI
      rwa [← hφ N₁, ← hφ N₂] at this
    · right
      have := colSwapMat_interchange (i := i) (j := j) hI
      rwa [← hφ N₁, ← hφ N₂] at this
  exact hproper (φ N₁) (φ N₂) hadjφ

private theorem exists_three_mem_of_card {α : Type*} [DecidableEq α]
    {S : Finset α} (h : 3 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hbmem : b ∈ S.erase a := Finset.mem_erase.mpr ⟨fun h' => hab h'.symm, hb⟩
  have e1 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
  have e2 : ((S.erase a).erase b).card = (S.erase a).card - 1 :=
    Finset.card_erase_of_mem hbmem
  have hcard : 0 < ((S.erase a).erase b).card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hcard
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  exact ⟨a, ha, b, hb, c, (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2,
    hab, Ne.symm hca, Ne.symm hcb⟩

set_option maxHeartbeats 1600000 in
/-- **Lemma 5.8, as printed** — each color class of the constrained source fiber reaches at
    least two distinct vertices of the non-bipartite target fiber along crossing edges. The
    proof is the paper's: margin identities, the two exclusions (`D = 1` by the column-swap
    isomorphism, `D < 0` by a triangle), then `D ≥ 2` directly and `D = 0` by the
    `|C| = 2` / `|C| ≥ 4` dichotomy. -/
theorem row_bip_source_reach_two {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X E)
    (hXconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hEnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = E} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) E) col)
    {col : {M : MarginClass r s // rowProj hB M = X} → Bool}
    (hproper : IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col)
    (hXIG : IsInterchangeGraph (fibreGraph (flipGraph r s) (rowProj hB) X))
    (κ : Bool)
    (hκne : ∃ w : {M : MarginClass r s // rowProj hB M = X}, col w = κ)
    (hop : ∃ w : {M : MarginClass r s // rowProj hB M = X}, col w ≠ κ) :
    ∃ z₁ z₂ : {M : MarginClass r s // rowProj hB M = E}, z₁ ≠ z₂ ∧
      (∃ y₁, col y₁ = κ ∧ (flipGraph r s).Adj y₁.val z₁.val) ∧
      (∃ y₂, col y₂ = κ ∧ (flipGraph r s).Adj y₂.val z₂.val) := by
  classical
  obtain ⟨y₀, hy₀κ⟩ := hκne
  -- the fiber-side row facts every member carries
  have hXcell : ∀ Y : {M : MarginClass r s // rowProj hB M = X},
      Y.val.val L i = true ∧ Y.val.val L j = false := fun Y =>
    ⟨row_cell_true_of_fibre_left (hB := hB) (j := j) hXi Y,
     row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj Y⟩
  have hEcell : ∀ Z : {M : MarginClass r s // rowProj hB M = E},
      Z.val.val L i = false ∧ Z.val.val L j = true := fun Z =>
    ⟨row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXi Z,
     row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXj Z⟩
  have hsource : ∀ Y : {M : MarginClass r s // rowProj hB M = X},
      bcount L i j Y.val.val + s i = acount L i j Y.val.val + s j + 1 := fun Y =>
    count_identity_source (hXcell Y).1 (hXcell Y).2 (Y.val.property.2 i) (Y.val.property.2 j)
  have htarget : ∀ Z : {M : MarginClass r s // rowProj hB M = E},
      acount L i j Z.val.val + s j = bcount L i j Z.val.val + s i + 1 := fun Z =>
    count_identity_target (hEcell Z).1 (hEcell Z).2 (Z.val.property.2 i) (Z.val.property.2 j)
  have hE3 : 3 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = E} :=
    card_ge_three_of_not_bip_sec5 (G := fibreGraph (flipGraph r s) (rowProj hB) E) hEnb
  -- Exclusion 1: D = 1, i.e. s i = s j.
  by_cases hD1 : s i = s j
  · exact absurd (row_bip_source_col_eq_contra r s L B hB hXi hXj hD1 hEnb hproper) id
  -- Exclusion 2: D < 0, i.e. s i ≥ s j + 2: a triangle in the bipartite source fiber.
  by_cases hDneg : s j + 2 ≤ s i
  · exfalso
    have hEfib : Nonempty {M : MarginClass r s // rowProj hB M = E} :=
      Fintype.card_pos_iff.mp (by omega)
    obtain ⟨Ep⟩ := hEfib
    have hage : 3 ≤ acount L i j Ep.val.val := by
      have h := htarget Ep
      omega
    have hcard := cross_card_eq_acount r s L B hB hXi hXj Ep
    have h3 : 3 ≤ (crossTo (hB := hB) X Ep).card := by omega
    obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, h12, h13, h23⟩ := exists_three_mem_of_card h3
    have hadj1 : (flipGraph r s).Adj Ep.val y₁.val := by simpa [crossTo] using hy₁
    have hadj2 : (flipGraph r s).Adj Ep.val y₂.val := by simpa [crossTo] using hy₂
    have hadj3 : (flipGraph r s).Adj Ep.val y₃.val := by simpa [crossTo] using hy₃
    have hswitch : ∀ (y : {M : MarginClass r s // rowProj hB M = X}),
        (flipGraph r s).Adj Ep.val y.val →
        ∃ a, a ≠ L ∧ Ep.val.val a j = false ∧ Ep.val.val a i = true ∧
          y.val.val = Brualdi.Ryser.switchMat Ep.val.val L a j i := by
      intro y hadj
      have hint : Interchange Ep.val.val y.val.val := by
        have h := hadj
        rw [flipGraph, SimpleGraph.fromRel_adj] at h
        rcases h.2 with hI | hI
        · exact hI
        · exact interchange_symm hI
      exact crossing_eq_switchMat (M := Ep.val.val) (N := y.val.val) (L := L) (i := j) (j := i)
        (hEcell Ep).2 (hEcell Ep).1 (hXcell y).2 (hXcell y).1 hint
    obtain ⟨a₁, ha₁L, ha₁j, ha₁i, he₁⟩ := hswitch y₁ hadj1
    obtain ⟨a₂, ha₂L, ha₂j, ha₂i, he₂⟩ := hswitch y₂ hadj2
    obtain ⟨a₃, ha₃L, ha₃j, ha₃i, he₃⟩ := hswitch y₃ hadj3
    have ha₁A : a₁ ∈ rowsA L i j Ep.val.val := by simp [rowsA, ha₁L, ha₁i, ha₁j]
    have ha₂A : a₂ ∈ rowsA L i j Ep.val.val := by simp [rowsA, ha₂L, ha₂i, ha₂j]
    have ha₃A : a₃ ∈ rowsA L i j Ep.val.val := by simp [rowsA, ha₃L, ha₃i, ha₃j]
    have hrow_ne : ∀ {y y' : {M : MarginClass r s // rowProj hB M = X}}
        {a a' : Fin (m + 1)}, y ≠ y' →
        y.val.val = Brualdi.Ryser.switchMat Ep.val.val L a j i →
        y'.val.val = Brualdi.Ryser.switchMat Ep.val.val L a' j i → a ≠ a' := by
      intro y y' a a' hyy hy hy' haa
      apply hyy
      apply Subtype.ext
      apply Subtype.ext
      rw [hy, hy', haa]
    have h12' := hrow_ne h12 he₁ he₂
    have h13' := hrow_ne h13 he₁ he₃
    have h23' := hrow_ne h23 he₂ he₃
    have hf12 := flips_of_common_adj (hB := hB) (X := X) Ep y₁ y₂ ha₁A ha₂A h12' he₁ he₂
    have hf13 := flips_of_common_adj (hB := hB) (X := X) Ep y₁ y₃ ha₁A ha₃A h13' he₁ he₃
    have hf23 := flips_of_common_adj (hB := hB) (X := X) Ep y₂ y₃ ha₂A ha₃A h23' he₂ he₃
    have hc12 := hproper y₁ y₂ hf12
    have hc13 := hproper y₁ y₃ hf13
    have hc23 := hproper y₂ y₃ hf23
    cases h1 : col y₁ <;> cases h2 : col y₂ <;> cases h3 : col y₃ <;> simp_all
  -- D ≥ 2: s j ≥ s i + 1 gives every source member two crossing edges.
  by_cases hDge2 : s i + 1 ≤ s j
  · have hb2 : 2 ≤ bcount L i j y₀.val.val := by
      have h := hsource y₀
      omega
    have hcard := cross_card_eq_bcount r s L B hB hXi hXj y₀
    obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := Finset.one_lt_card.mp (by omega :
      1 < (crossTo (hB := hB) E y₀).card)
    refine ⟨z₁, z₂, hz12, ⟨y₀, hy₀κ, by simpa [crossTo] using hz₁⟩,
      ⟨y₀, hy₀κ, by simpa [crossTo] using hz₂⟩⟩
  -- D = 0: s i = s j + 1.
  have hD0 : s i = s j + 1 := by omega
  have haE2 : ∀ Z : {M : MarginClass r s // rowProj hB M = E},
      2 ≤ acount L i j Z.val.val := by
    intro Z
    have h := htarget Z
    omega
  -- card ≥ 2 and equitability
  obtain ⟨w₀, hw₀⟩ := hop
  have hyw : y₀ ≠ w₀ := by
    intro h
    rw [h] at hy₀κ
    exact hw₀ hy₀κ
  have hcard2 : 2 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = X} :=
    Fintype.one_lt_card_iff.mpr ⟨y₀, w₀, hyw⟩
  have hEq := interchange_bipartite_equitable hXIG hproper hcard2
  by_cases hC2 : Fintype.card {M : MarginClass r s // rowProj hB M = X} = 2
  · -- |C| = 2: both members are adjacent to every member of E.
    obtain ⟨Z₁, Z₂, hZ12⟩ := Fintype.exists_pair_of_one_lt_card
      (α := {M : MarginClass r s // rowProj hB M = E}) (by omega)
    have hall : ∀ Z : {M : MarginClass r s // rowProj hB M = E},
        (flipGraph r s).Adj y₀.val Z.val := by
      intro Z
      have hcard := cross_card_eq_acount r s L B hB hXi hXj Z
      have h2 : 2 ≤ (crossTo (hB := hB) X Z).card := by
        have := haE2 Z
        omega
      have huniv : crossTo (hB := hB) X Z = Finset.univ := by
        apply Finset.eq_univ_of_card
        have hle : (crossTo (hB := hB) X Z).card ≤ 2 := by
          calc (crossTo (hB := hB) X Z).card
              ≤ (Finset.univ : Finset {M : MarginClass r s // rowProj hB M = X}).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = 2 := by rw [Finset.card_univ, hC2]
        rw [hC2]
        omega
      have hy₀mem : y₀ ∈ crossTo (hB := hB) X Z := by
        rw [huniv]
        exact Finset.mem_univ _
      have h := hy₀mem
      simp only [crossTo, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.symm
    exact ⟨Z₁, Z₂, hZ12, ⟨y₀, hy₀κ, hall Z₁⟩, ⟨y₀, hy₀κ, hall Z₂⟩⟩
  · -- |C| ≥ 4: a single reached target would make the κ-class a clique.
    have heven := equitable_even_card hEq
    have hC4 : 4 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = X} := by
      rcases heven with ⟨t, ht⟩
      omega
    -- the κ class has at least two members
    have hclass2 : 1 < (Finset.univ.filter
        (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = κ)).card := by
      have hft : (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = false)).card =
          (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)).card := by
        have e1 := Fintype.card_subtype
          (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = false)
        have e2 := Fintype.card_subtype
          (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)
        rw [← e1, ← e2]
        exact hEq.2
      have hpart : (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = false)).card +
          (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)).card =
          Fintype.card {M : MarginClass r s // rowProj hB M = X} := by
        rw [← Finset.card_univ]
        have h := Finset.filter_card_add_filter_neg_card_eq_card
          (s := (Finset.univ : Finset {M : MarginClass r s // rowProj hB M = X}))
          (p := fun v => col v = false)
        have hneg : (Finset.univ.filter
              (fun v : {M : MarginClass r s // rowProj hB M = X} => ¬ col v = false)) =
            (Finset.univ.filter
              (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases hv : col v <;> simp
        rw [hneg] at h
        exact h
      cases κ <;> omega
    by_contra hno
    -- the reached set: nonempty and (by hno) a singleton
    have hreach : ∀ M : {M : MarginClass r s // rowProj hB M = X}, col M = κ →
        ∃ Z : {M : MarginClass r s // rowProj hB M = E},
          (flipGraph r s).Adj M.val Z.val := by
      intro M hM
      have hint := row_interface_all_of_bip_source r s L B hB hXi hXj hused hXconn hproper M
      have hW := (row_interface_iff_hasWitness r s L B hB hXi hXj M).mp hint
      obtain ⟨a, haL, hai, haj⟩ := hW
      have hb1 : 1 ≤ bcount L i j M.val.val := by
        have hmem : a ∈ rowsB L i j M.val.val := by simp [rowsB, haL, hai, haj]
        have := Finset.card_pos.mpr ⟨a, hmem⟩
        unfold bcount
        omega
      have hcard := cross_card_eq_bcount r s L B hB hXi hXj M
      have hpos : 0 < (crossTo (hB := hB) E M).card := by omega
      obtain ⟨Z, hZ⟩ := Finset.card_pos.mp hpos
      have h := hZ
      simp only [crossTo, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact ⟨Z, h⟩
    obtain ⟨e₀, he₀⟩ := hreach y₀ hy₀κ
    -- every κ-member reaches only e₀
    have honly : ∀ M : {M : MarginClass r s // rowProj hB M = X}, col M = κ →
        ∀ Z : {M : MarginClass r s // rowProj hB M = E},
          (flipGraph r s).Adj M.val Z.val → Z = e₀ := by
      intro M hM Z hZ
      by_contra hne
      exact hno ⟨Z, e₀, hne, ⟨M, hM, hZ⟩, ⟨y₀, hy₀κ, he₀⟩⟩
    -- two distinct κ-members, both adjacent (only) to e₀
    obtain ⟨M₁, hM₁mem, M₂, hM₂mem, hM12⟩ := Finset.one_lt_card.mp hclass2
    have hM₁κ : col M₁ = κ := (Finset.mem_filter.mp hM₁mem).2
    have hM₂κ : col M₂ = κ := (Finset.mem_filter.mp hM₂mem).2
    obtain ⟨Z₁, hZ₁⟩ := hreach M₁ hM₁κ
    obtain ⟨Z₂, hZ₂⟩ := hreach M₂ hM₂κ
    have hZ₁e : Z₁ = e₀ := honly M₁ hM₁κ Z₁ hZ₁
    have hZ₂e : Z₂ = e₀ := honly M₂ hM₂κ Z₂ hZ₂
    rw [hZ₁e] at hZ₁
    rw [hZ₂e] at hZ₂
    -- both are switches of e₀ at distinct rows, hence adjacent in the fiber
    have hswitch : ∀ (y : {M : MarginClass r s // rowProj hB M = X}),
        (flipGraph r s).Adj y.val e₀.val →
        ∃ a, a ≠ L ∧ e₀.val.val a j = false ∧ e₀.val.val a i = true ∧
          y.val.val = Brualdi.Ryser.switchMat e₀.val.val L a j i := by
      intro y hadj
      have hint : Interchange e₀.val.val y.val.val := by
        have h := hadj.symm
        rw [flipGraph, SimpleGraph.fromRel_adj] at h
        rcases h.2 with hI | hI
        · exact hI
        · exact interchange_symm hI
      exact crossing_eq_switchMat (M := e₀.val.val) (N := y.val.val) (L := L) (i := j) (j := i)
        (hEcell e₀).2 (hEcell e₀).1 (hXcell y).2 (hXcell y).1 hint
    obtain ⟨a₁, ha₁L, ha₁j, ha₁i, he₁⟩ := hswitch M₁ hZ₁
    obtain ⟨a₂, ha₂L, ha₂j, ha₂i, he₂⟩ := hswitch M₂ hZ₂
    have ha₁A : a₁ ∈ rowsA L i j e₀.val.val := by simp [rowsA, ha₁L, ha₁i, ha₁j]
    have ha₂A : a₂ ∈ rowsA L i j e₀.val.val := by simp [rowsA, ha₂L, ha₂i, ha₂j]
    have h12' : a₁ ≠ a₂ := by
      intro h
      apply hM12
      apply Subtype.ext
      apply Subtype.ext
      rw [he₁, he₂, h]
    have hf12 := flips_of_common_adj (hB := hB) (X := X) e₀ M₁ M₂ ha₁A ha₂A h12' he₁ he₂
    have hc := hproper M₁ M₂ hf12
    rw [hM₁κ, hM₂κ] at hc
    exact hc rfl

/-- The avoid form the threading consumes, derived from the printed Lemma 5.8: the color
    class opposite `x` reaches two distinct targets, and one of them dodges `bad`. -/
theorem row_bip_source_avoid {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X E)
    (hXconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hEnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = E} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) E) col)
    {col : {M : MarginClass r s // rowProj hB M = X} → Bool}
    (hproper : IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col)
    (hXIG : IsInterchangeGraph (fibreGraph (flipGraph r s) (rowProj hB) X))
    (x : {M : MarginClass r s // rowProj hB M = X})
    (bad : {M : MarginClass r s // rowProj hB M = E})
    (hopp : ∃ w, col w ≠ col x) :
    ∃ y : {M : MarginClass r s // rowProj hB M = X},
      col y ≠ col x ∧
        ∃ z : {M : MarginClass r s // rowProj hB M = E},
          z ≠ bad ∧ (flipGraph r s).Adj y.val z.val := by
  classical
  obtain ⟨w, hw⟩ := hopp
  have hbne : ∀ a b : Bool, a ≠ b → a = !b := by decide
  have hκne : ∃ v : {M : MarginClass r s // rowProj hB M = X}, col v = !(col x) :=
    ⟨w, hbne _ _ hw⟩
  have hop : ∃ v : {M : MarginClass r s // rowProj hB M = X}, col v ≠ !(col x) :=
    ⟨x, by cases hx : col x <;> simp⟩
  obtain ⟨z₁, z₂, hz12, ⟨y₁, hy₁κ, hadj₁⟩, ⟨y₂, hy₂κ, hadj₂⟩⟩ :=
    row_bip_source_reach_two r s L B hB hXi hXj hused hXconn hEnb hproper hXIG
      (!(col x)) hκne hop
  by_cases hz₁bad : z₁ = bad
  · have hz₂bad : z₂ ≠ bad := fun h => hz12 (hz₁bad.trans h.symm)
    exact ⟨y₂, by rw [hy₂κ]; cases col x <;> simp, z₂, hz₂bad, hadj₂⟩
  · exact ⟨y₁, by rw [hy₁κ]; cases col x <;> simp, z₁, hz₁bad, hadj₁⟩

set_option maxHeartbeats 1000000 in
/-- **ALTERNATE proof of Lemma 5.8's avoid form** (the development's original constructive
    route: the cC-trichotomy handled without the paper's two exclusion arguments). The
    mainline is `row_bip_source_avoid` above, derived from the printed proof
    (`row_bip_source_reach_two`). Kept so both arguments stay machine-checked. -/
theorem row_bip_source_avoid_direct {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X E : RowQ r s L B} {i j : Fin n}
    (hXi : X.val \ E.val = {i}) (hXj : E.val \ X.val = {j})
    (hused : quotientAdj (flipGraph r s) (rowProj hB) X E)
    (hXconn : (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hEnb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = E} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) E) col)
    {col : {M : MarginClass r s // rowProj hB M = X} → Bool}
    (hproper : IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) X) col)
    (hXIG : IsInterchangeGraph (fibreGraph (flipGraph r s) (rowProj hB) X))
    (x : {M : MarginClass r s // rowProj hB M = X})
    (bad : {M : MarginClass r s // rowProj hB M = E})
    (hopp : ∃ w, col w ≠ col x) :
    ∃ y : {M : MarginClass r s // rowProj hB M = X},
      col y ≠ col x ∧
        ∃ z : {M : MarginClass r s // rowProj hB M = E},
          z ≠ bad ∧ (flipGraph r s).Adj y.val z.val := by
  classical
  obtain ⟨w₀, hw₀⟩ := hopp
  have hE3 : 3 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = E} :=
    card_ge_three_of_not_bip_sec5
      (G := fibreGraph (flipGraph r s) (rowProj hB) E) hEnb
  let cC : ℤ := (s j : ℤ) - s i + 1
  have source_count :
      ∀ Y : {M : MarginClass r s // rowProj hB M = X},
        bcount L i j Y.val.val + s i = acount L i j Y.val.val + s j + 1 := by
    intro Y
    have hLi : Y.val.val L i = true :=
      row_cell_true_of_fibre_left (hB := hB) (j := j) hXi Y
    have hLj : Y.val.val L j = false :=
      row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj Y
    exact count_identity_source hLi hLj (Y.val.property.2 i) (Y.val.property.2 j)
  have target_count :
      ∀ Z : {M : MarginClass r s // rowProj hB M = E},
        acount L i j Z.val.val + s j = bcount L i j Z.val.val + s i + 1 := by
    intro Z
    have hLi : Z.val.val L i = false :=
      row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXi Z
    have hLj : Z.val.val L j = true :=
      row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXj Z
    exact count_identity_target hLi hLj (Z.val.property.2 i) (Z.val.property.2 j)
  have hbadLi : bad.val.val L i = false :=
    row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXi bad
  have hbadLj : bad.val.val L j = true :=
    row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXj bad
  by_cases hc2 : (2 : ℤ) ≤ cC
  · have hsrc := source_count w₀
    have hb_ge_two : 2 ≤ bcount L i j w₀.val.val := by
      have hZ : ((bcount L i j w₀.val.val : ℕ) : ℤ) + s i =
              ((acount L i j w₀.val.val : ℕ) : ℤ) + s j + 1 := by
        exact_mod_cast hsrc
      have hac : (0 : ℤ) ≤ (acount L i j w₀.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
      have : (2 : ℤ) ≤ (bcount L i j w₀.val.val : ℤ) := by
        dsimp [cC] at hc2
        omega
      exact_mod_cast this
    have hcard := cross_card_eq_bcount r s L B hB hXi hXj w₀
    have hgt : 1 < (crossTo (hB := hB) E w₀).card := by
      rw [hcard]
      omega
    obtain ⟨z, hz, hz_ne⟩ :=
      exists_mem_ne_of_one_lt_card (S := crossTo (hB := hB) E w₀) (x := bad) hgt
    have hadj : (flipGraph r s).Adj w₀.val z.val := by simpa [crossTo] using hz
    exact ⟨w₀, hw₀, z, hz_ne, hadj⟩
  · by_cases hc0 : cC ≤ 0
    · obtain ⟨Ep, hEp_ne⟩ := exists_ne_of_card_ge_three hE3 bad
      have htgt := target_count Ep
      have ha_ge_two : 2 ≤ acount L i j Ep.val.val := by
        have hZ : ((acount L i j Ep.val.val : ℕ) : ℤ) + s j =
                ((bcount L i j Ep.val.val : ℕ) : ℤ) + s i + 1 := by
          exact_mod_cast htgt
        have hb : (0 : ℤ) ≤ (bcount L i j Ep.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
        have : (2 : ℤ) ≤ (acount L i j Ep.val.val : ℤ) := by
          dsimp [cC] at hc0
          omega
        exact_mod_cast this
      have hcard := cross_card_eq_acount r s L B hB hXi hXj Ep
      have hgt : 1 < (crossTo (hB := hB) X Ep).card := by
        rw [hcard]
        omega
      obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Finset.one_lt_card.mp hgt
      have hadj1 : (flipGraph r s).Adj Ep.val y₁.val := by simpa [crossTo] using hy₁
      have hadj2 : (flipGraph r s).Adj Ep.val y₂.val := by simpa [crossTo] using hy₂
      have hEpLi : Ep.val.val L i = false :=
        row_cell_false_of_fibre_right_missing (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXi Ep
      have hEpLj : Ep.val.val L j = true :=
        row_cell_true_of_fibre_left (hB := hB) (X := E) (Y := X) (i := j) (j := i) hXj Ep
      have hy1Li : y₁.val.val L i = true := row_cell_true_of_fibre_left (hB := hB) (j := j) hXi y₁
      have hy1Lj : y₁.val.val L j = false := row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj y₁
      have hy2Li : y₂.val.val L i = true := row_cell_true_of_fibre_left (hB := hB) (j := j) hXi y₂
      have hy2Lj : y₂.val.val L j = false := row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj y₂
      have hint1 : Interchange Ep.val.val y₁.val.val := by
        rw [flipGraph, SimpleGraph.fromRel_adj] at hadj1
        rcases hadj1 with ⟨_, h | h⟩
        · exact h
        · exact interchange_symm h
      have hint2 : Interchange Ep.val.val y₂.val.val := by
        rw [flipGraph, SimpleGraph.fromRel_adj] at hadj2
        rcases hadj2 with ⟨_, h | h⟩
        · exact h
        · exact interchange_symm h
      obtain ⟨a₁, ha₁L, ha₁j, ha₁i, hy1eq⟩ :=
        crossing_eq_switchMat (M := Ep.val.val) (N := y₁.val.val) (L := L) (i := j) (j := i)
          hEpLj hEpLi hy1Lj hy1Li hint1
      obtain ⟨a₂, ha₂L, ha₂j, ha₂i, hy2eq⟩ :=
        crossing_eq_switchMat (M := Ep.val.val) (N := y₂.val.val) (L := L) (i := j) (j := i)
          hEpLj hEpLi hy2Lj hy2Li hint2
      have ha₁A : a₁ ∈ rowsA L i j Ep.val.val := by simp [rowsA, ha₁L, ha₁i, ha₁j]
      have ha₂A : a₂ ∈ rowsA L i j Ep.val.val := by simp [rowsA, ha₂L, ha₂i, ha₂j]
      have ha12 : a₁ ≠ a₂ := by
        intro h
        apply hy12
        apply Subtype.ext
        apply Subtype.ext
        rw [hy1eq, hy2eq, h]
      have hfib_adj : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj y₁ y₂ :=
        flips_of_common_adj (hB := hB) (X := X) Ep y₁ y₂ ha₁A ha₂A ha12 hy1eq hy2eq
      have hcol_ne : col y₁ ≠ col y₂ := hproper y₁ y₂ hfib_adj
      by_cases hy1x : col y₁ = col x
      · have hy2x : col y₂ ≠ col x := by
          rw [← hy1x]
          exact fun h => hcol_ne h.symm
        exact ⟨y₂, hy2x, Ep, hEp_ne, hadj2.symm⟩
      · exact ⟨y₁, hy1x, Ep, hEp_ne, hadj1.symm⟩
    · have hc_eq_one : cC = 1 := by
        dsimp [cC] at hc2 hc0 ⊢
        omega
      have hsij : s i = s j := by
        have : (s i : ℤ) = s j := by
          dsimp [cC] at hc_eq_one
          omega
        exact_mod_cast this
      by_contra hgoal
      push_neg at hgoal
      have source_b_pos : ∀ Y : {M : MarginClass r s // rowProj hB M = X},
          0 < bcount L i j Y.val.val := by
        intro Y
        have hsrc := source_count Y
        have hZ : ((bcount L i j Y.val.val : ℕ) : ℤ) + s i =
                ((acount L i j Y.val.val : ℕ) : ℤ) + s j + 1 := by
          exact_mod_cast hsrc
        have hac : (0 : ℤ) ≤ (acount L i j Y.val.val : ℤ) := by exact_mod_cast Nat.zero_le _
        have : (1 : ℤ) ≤ (bcount L i j Y.val.val : ℤ) := by
          dsimp [cC] at hc_eq_one
          omega
        exact_mod_cast this
      have kappa_hits_bad : ∀ y : {M : MarginClass r s // rowProj hB M = X},
          col y ≠ col x → (flipGraph r s).Adj y.val bad.val := by
        intro y hy
        have hpos : 0 < (crossTo (hB := hB) E y).card := by
          rw [cross_card_eq_bcount r s L B hB hXi hXj y]
          exact source_b_pos y
        obtain ⟨N, hN⟩ := Finset.card_pos.mp hpos
        have hadj : (flipGraph r s).Adj y.val N.val := by simpa [crossTo] using hN
        have hNbad : N = bad := by
          by_contra hNb
          exact hgoal y hy N hNb hadj
        simpa [hNbad] using hadj
      have hw₀mem : w₀ ∈ Finset.univ.filter
          (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hw₀
      by_cases hκ2 : 2 ≤ (Finset.univ.filter
          (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card
      · have hone : 1 < (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card := by
          omega
        obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Finset.one_lt_card.mp hone
        have hy1c : col y₁ ≠ col x := (Finset.mem_filter.mp hy₁).2
        have hy2c : col y₂ ≠ col x := (Finset.mem_filter.mp hy₂).2
        have hbad1 : (flipGraph r s).Adj y₁.val bad.val := kappa_hits_bad y₁ hy1c
        have hbad2 : (flipGraph r s).Adj y₂.val bad.val := kappa_hits_bad y₂ hy2c
        have hy1Li : y₁.val.val L i = true := row_cell_true_of_fibre_left (hB := hB) (j := j) hXi y₁
        have hy1Lj : y₁.val.val L j = false := row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj y₁
        have hy2Li : y₂.val.val L i = true := row_cell_true_of_fibre_left (hB := hB) (j := j) hXi y₂
        have hy2Lj : y₂.val.val L j = false := row_cell_false_of_fibre_right_missing (hB := hB) (i := i) hXj y₂
        have hint1 : Interchange bad.val.val y₁.val.val := by
          have h := hbad1.symm
          rw [flipGraph, SimpleGraph.fromRel_adj] at h
          rcases h with ⟨_, hh | hh⟩
          · exact hh
          · exact interchange_symm hh
        have hint2 : Interchange bad.val.val y₂.val.val := by
          have h := hbad2.symm
          rw [flipGraph, SimpleGraph.fromRel_adj] at h
          rcases h with ⟨_, hh | hh⟩
          · exact hh
          · exact interchange_symm hh
        obtain ⟨a₁, ha₁L, ha₁j, ha₁i, hy1eq⟩ :=
          crossing_eq_switchMat (M := bad.val.val) (N := y₁.val.val) (L := L) (i := j) (j := i)
            hbadLj hbadLi hy1Lj hy1Li hint1
        obtain ⟨a₂, ha₂L, ha₂j, ha₂i, hy2eq⟩ :=
          crossing_eq_switchMat (M := bad.val.val) (N := y₂.val.val) (L := L) (i := j) (j := i)
            hbadLj hbadLi hy2Lj hy2Li hint2
        have ha₁A : a₁ ∈ rowsA L i j bad.val.val := by simp [rowsA, ha₁L, ha₁i, ha₁j]
        have ha₂A : a₂ ∈ rowsA L i j bad.val.val := by simp [rowsA, ha₂L, ha₂i, ha₂j]
        have ha12 : a₁ ≠ a₂ := by
          intro h
          apply hy12
          apply Subtype.ext
          apply Subtype.ext
          rw [hy1eq, hy2eq, h]
        have hfib_adj : (fibreGraph (flipGraph r s) (rowProj hB) X).Adj y₁ y₂ :=
          flips_of_common_adj (hB := hB) (X := X) bad y₁ y₂ ha₁A ha₂A ha12 hy1eq hy2eq
        have hcol_ne : col y₁ ≠ col y₂ := hproper y₁ y₂ hfib_adj
        have hsame : col y₁ = col y₂ := by
          cases hcx : col x <;> cases h1 : col y₁ <;> cases h2 : col y₂ <;> simp_all
        exact hcol_ne hsame
      · have hκ1 : (Finset.univ.filter
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card = 1 := by
          have hpos : 1 ≤ (Finset.univ.filter
              (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card :=
            Finset.card_pos.mpr ⟨w₀, hw₀mem⟩
          omega
        have hxw₀ : w₀ ≠ x := fun h => (Finset.mem_filter.mp hw₀mem).2 (by rw [h])
        have hcard2 : 2 ≤ Fintype.card {M : MarginClass r s // rowProj hB M = X} :=
          Fintype.one_lt_card_iff.mpr ⟨w₀, x, hxw₀⟩
        have hEq := interchange_bipartite_equitable hXIG hproper hcard2
        have hft :
            (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = false)).card =
              (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)).card := by
          have e1 := Fintype.card_subtype
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = false)
          have e2 := Fintype.card_subtype
            (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = true)
          rw [← e1, ← e2]
          exact hEq.2
        have hother :
            (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = col x)).card =
              (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card := by
          cases hcx : col x
          · -- goal: |{col v = false}| = |{col v ≠ false}|
            have h2 : (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ false)) =
                  (Finset.univ.filter (fun v => col v = true)) := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              cases hv : col v <;> simp
            rw [h2]
            exact hft
          · -- goal: |{col v = true}| = |{col v ≠ true}|
            have h2 : (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ true)) =
                  (Finset.univ.filter (fun v => col v = false)) := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              cases hv : col v <;> simp
            rw [h2]
            exact hft.symm
        have hcard2 : Fintype.card {M : MarginClass r s // rowProj hB M = X} = 2 := by
          have hpart :
              (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v = col x)).card +
                (Finset.univ.filter (fun v : {M : MarginClass r s // rowProj hB M = X} => col v ≠ col x)).card =
                  Fintype.card {M : MarginClass r s // rowProj hB M = X} := by
            rw [← Finset.card_univ]
            exact Finset.filter_card_add_filter_neg_card_eq_card _
          rw [hother, hκ1] at hpart
          omega
        have hXE := fiber_card_eq_of_col_eq r s L B hB hXi hXj hsij
        rw [hcard2] at hXE
        omega

theorem row_hinterface_step_to_buffer_avoid {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (buffer : RowQ r s L B)
    (hbuf_nb : ¬ ∃ col : {M : MarginClass r s // rowProj hB M = buffer} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) buffer) col)
    (hfib_conn : ∀ X : RowQ r s L B,
      (fibreGraph (flipGraph r s) (rowProj hB) X).Connected)
    (hfib_isMH : ∀ X : RowQ r s L B,
      IsMH (fibreGraph (flipGraph r s) (rowProj hB) X)) :
    ∀ {X : RowQ r s L B},
      quotientAdj (flipGraph r s) (rowProj hB) X buffer →
        ∀ (x : {M : MarginClass r s // rowProj hB M = X})
          (bad : {M : MarginClass r s // rowProj hB M = buffer}),
          ∃ y : {M : MarginClass r s // rowProj hB M = X},
            ∃ z : {M : MarginClass r s // rowProj hB M = buffer},
              z ≠ bad ∧
                Nonempty
                  {choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x y //
                    (flipGraph r s).Adj y.val z.val} := by
  classical
  intro X hused x bad
  rcases rowQuotient_singletons_of_quotientAdj r s L B hB hused with
    ⟨i, j, hXi, hXj⟩
  let G := flipGraph r s
  let π := rowProj hB
  have hXIG : IsInterchangeGraph (fibreGraph G π X) := by
    rcases rowProj_fibre_iso_patOfSet r s L B hB X with ⟨e⟩
    refine isInterchangeGraph_of_iso e ?_
    exact fibre_isInterchangeGraph r s L (patOfSet X.val)
      (fibre_nonempty_of_support_nonempty ((hB X.val).mp X.property))
  have hfinish_singleton_avoid :
      (∀ v : MarginClass r s, v ∈ fibre π X → v = x.val) →
        ∃ y : {M : MarginClass r s // π M = X},
          ∃ z : {M : MarginClass r s // π M = buffer},
            z ≠ bad ∧
              Nonempty
                {choice : FibreTerminalChoice G π X x y // G.Adj y.val z.val} := by
    intro huniq
    rcases row_interface_two_of_nonbip r s L B hB (X := buffer) (Y := X)
        (i := j) (j := i) hXj hXi (quotientAdj_symm hused)
        (hfib_conn buffer) hbuf_nb with
      ⟨M₁, hM₁I, M₂, hM₂I, hM₁M₂⟩
    have hfinish (M : MarginClass r s)
        (hMI : M ∈ interface G π buffer X) (hMne : M ≠ bad.val) :
        ∃ y : {M : MarginClass r s // π M = X},
          ∃ z : {M : MarginClass r s // π M = buffer},
            z ≠ bad ∧
              Nonempty
                {choice : FibreTerminalChoice G π X x y // G.Adj y.val z.val} := by
      have hMf : M ∈ fibre π buffer := interface_sub_fibre G π buffer X hMI
      let z : {M : MarginClass r s // π M = buffer} :=
        ⟨M, (Finset.mem_filter.mp hMf).2⟩
      have hz_ne : z ≠ bad := by
        intro hz
        exact hMne (congrArg Subtype.val hz)
      rcases (mem_interface_iff.mp hMI).2 with ⟨v, hvX, hMv⟩
      have hvx : v = x.val := huniq v hvX
      have hxz : G.Adj x.val z.val := by
        have hMx : G.Adj M x.val := by simpa [hvx] using hMv
        simpa [z] using hMx.symm
      refine ⟨x, z, hz_ne, ⟨⟨?_, hxz⟩⟩⟩
      exact FibreTerminalChoice.singleton rfl (by
        intro v hv
        exact huniq v hv)
    by_cases hbad₁ : bad.val = M₁
    · exact hfinish M₂ hM₂I (by
        intro hM₂bad
        exact hM₁M₂ (hbad₁.symm.trans hM₂bad.symm))
    · exact hfinish M₁ hM₁I (by
        intro hM₁bad
        exact hbad₁ hM₁bad.symm)
  rcases hfib_isMH X with hconn | ⟨col, hproper, hsurj, hlace⟩
  · by_cases hnb :
        ¬ ∃ col : {M : MarginClass r s // π M = X} → Bool,
          IsProper2Coloring (fibreGraph G π X) col
    · rcases row_two_of_nonbip_avoid r s L B hB hXi hXj hused
          (by simpa [G, π] using hnb) hbuf_nb (hfib_conn X) x bad with
        ⟨y, z, hyx, hz_ne, hadj⟩
      exact ⟨y, z, hz_ne, ⟨⟨FibreTerminalChoice.hamConnected hconn hyx.symm, hadj⟩⟩⟩
    · have hbip_ex :
          ∃ col : {M : MarginClass r s // π M = X} → Bool,
            IsProper2Coloring (fibreGraph G π X) col :=
        Classical.byContradiction hnb
      rcases hbip_ex with ⟨col, hbip⟩
      by_cases huniq : ∀ v : MarginClass r s, v ∈ fibre π X → v = x.val
      · exact hfinish_singleton_avoid huniq
      · have hnotuniq := huniq
        push_neg at hnotuniq
        rcases hnotuniq with ⟨u, huX, hux⟩
        let uX : {M : MarginClass r s // π M = X} :=
          ⟨u, (Finset.mem_filter.mp huX).2⟩
        let S : Finset {M : MarginClass r s // π M = X} := {x}
        have hSproper : S ≠ Finset.univ := by
          intro hS
          have huS : uX ∈ S := by
            rw [hS]
            simp
          have hu_eq_x : uX = x := by simpa [S] using huS
          exact hux (congrArg Subtype.val hu_eq_x)
        rcases connected_boundary_edge (G := fibreGraph G π X) (hfib_conn X)
            (S := S) (by simp [S]) hSproper with
          ⟨A, hAS, N, _hNS, hAN⟩
        have hAeq : A = x := by simpa [S] using hAS
        subst A
        have hopp : ∃ w : {M : MarginClass r s // π M = X}, col w ≠ col x :=
          ⟨N, (hbip x N hAN).symm⟩
        rcases row_bip_source_avoid r s L B hB hXi hXj hused (hfib_conn X)
            hbuf_nb hbip hXIG x bad hopp with
          ⟨y, hycol, z, hz_ne, hadj⟩
        have hxy : x ≠ y := by
          intro h
          exact hycol (by rw [h])
        exact ⟨y, z, hz_ne, ⟨⟨FibreTerminalChoice.hamConnected hconn hxy, hadj⟩⟩⟩
  · rcases hsurj (!(col x)) with ⟨w, hw⟩
    have hwopp : col w ≠ col x := by
      rw [hw]
      cases col x <;> decide
    rcases row_bip_source_avoid r s L B hB hXi hXj hused (hfib_conn X)
        hbuf_nb hproper hXIG x bad ⟨w, hwopp⟩ with
      ⟨y, hycol, z, hz_ne, hadj⟩
    exact ⟨y, z, hz_ne, ⟨⟨FibreTerminalChoice.hamLaceable col hlace hycol.symm, hadj⟩⟩⟩

/-- A row line supplied by Lemma 5.11 (buffer existence) yields the buffer data, except for the
deferred Lemma-5.8 avoid-richness field. -/
noncomputable def pivotBufferData_of_row_line {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (hact : IsActive r s) (hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card (MarginClass r s) → IsInterchangeGraph H → IsMH H)
    {a b : MarginClass r s} (_hab : a ≠ b) {L : Fin (m + 1)}
    (hsep : rowPat L a ≠ rowPat L b)
    (hline_nb : lineFibreNonbip (r := r) (s := s) (Sum.inl L)) :
    Σ' B : BaseFamily (Fin n),
      Σ' hB : (∀ p : Finset (Fin n),
        B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p}),
        PivotBufferData r s L B hB := by
  classical
  -- data-valued goal: extract from Prop existentials via `choose`, not `rcases`
  let B : BaseFamily (Fin n) := (rowPattern_baseFamily r s L ⟨a⟩).choose
  have hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s //
        (Finset.univ.filter (fun b => M.val L b = true)) = p} :=
    (rowPattern_baseFamily r s L ⟨a⟩).choose_spec
  have hline' : ∃ γ : Fin n → Bool,
      ¬ ∃ col : {M : MarginClass r s // rowPat L M = γ} → Bool,
        IsProper2Coloring (fibreGraph (flipGraph r s) (rowPat L) γ) col := hline_nb
  let γ : Fin n → Bool := hline'.choose
  have hγnb : ¬ ∃ col : {M : MarginClass r s // rowPat L M = γ} → Bool,
      IsProper2Coloring (fibreGraph (flipGraph r s) (rowPat L) γ) col :=
    hline'.choose_spec
  have hγ_nonempty : Nonempty {M : MarginClass r s // rowPat L M = γ} := by
    by_contra hempty
    apply hγnb
    refine ⟨fun M => False.elim (hempty ⟨M⟩), ?_⟩
    intro u _v _huv
    exact False.elim (hempty ⟨u⟩)
  let Mγ : {M : MarginClass r s // rowPat L M = γ} := Classical.choice hγ_nonempty
  let buffer : RowQ r s L B :=
    ⟨rowSupport L Mγ.val, (hB _).mpr ⟨Mγ.val, rfl⟩⟩
  have hbuf_nb :
      ¬ ∃ col : {M : MarginClass r s // rowProj hB M = buffer} → Bool,
        IsProper2Coloring (fibreGraph (flipGraph r s) (rowProj hB) buffer) col := by
    rintro ⟨col, hcol⟩
    apply hγnb
    let toRowProj :
        {M : MarginClass r s // rowPat L M = γ} →
          {M : MarginClass r s // rowProj hB M = buffer} := fun N =>
      ⟨N.val, by
        apply Subtype.ext
        have hpat : rowPat L N.val = rowPat L Mγ.val := N.property.trans Mγ.property.symm
        ext c
        have hc := congrFun hpat c
        simpa [rowProj, rowSupport, rowPat, buffer] using congrArg (fun b => b = true) hc⟩
    refine ⟨fun N => col (toRowProj N), ?_⟩
    intro U V hUV
    exact hcol (toRowProj U) (toRowProj V) hUV
  have hfib_isMH : ∀ X : RowQ r s L B,
      IsMH (fibreGraph (flipGraph r s) (rowProj hB) X) := by
    intro X
    exact rowProj_fibre_isMH hsep IH hB X
  have hfib_conn : ∀ X : RowQ r s L B,
      (fibreGraph (flipGraph r s) (rowProj hB) X).Connected := by
    intro X
    haveI : Nonempty {M : MarginClass r s // rowProj hB M = X} := rowFibre_nonempty X
    exact isMH_connected (hfib_isMH X)
  have hQnb : ¬ ∃ col : RowQ r s L B → Bool,
      IsProper2Coloring (rowQuotientGraph r s L B) col := by
    exact rowQuotient_nonbip r s L B hB hact hn
      (fun j => active_prime_cell_varies r s hact hprime ⟨a⟩ L j)
  refine ⟨B, hB, ?_⟩
  exact
    { hQnb := hQnb
      buffer := buffer
      hbuf_nb := hbuf_nb
      hfib_conn := hfib_conn
      hfib_isMH := hfib_isMH
      hinterface_step := row_hinterface_step r s L B hB hfib_conn hfib_isMH
      hinterface_step_to_buffer_avoid :=
        row_hinterface_step_to_buffer_avoid r s L B hB buffer hbuf_nb hfib_conn hfib_isMH }

private theorem fibrePack_from_entry_exists {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (x : RowFibre hB X) :
    Nonempty {P : FibrePack (flipGraph r s) (rowProj hB) X // P.entry = x} := by
  classical
  rcases bd.hfib_isMH X with hconn | ⟨col, _hproper, hsurj, hlace⟩
  · by_cases hother : ∃ y : RowFibre hB X, x ≠ y
    · rcases hother with ⟨y, hxy⟩
      exact ⟨⟨
        { entry := x
          exit := y
          run := fibre_run_of_terminals x y
            (FibreTerminalChoice.hamConnected hconn hxy) }, rfl⟩⟩
    · have huniq : ∀ v : MarginClass r s, v ∈ fibre (rowProj hB) X → v = x.val := by
        intro v hv
        by_contra hvx
        have hvX : rowProj hB v = X := (Finset.mem_filter.mp hv).2
        exact hother ⟨⟨v, hvX⟩, fun h => hvx (congrArg Subtype.val h.symm)⟩
      exact ⟨⟨
        { entry := x
          exit := x
          run := fibre_run_of_terminals x x
            (FibreTerminalChoice.singleton rfl huniq) }, rfl⟩⟩
  · rcases hsurj (! col x) with ⟨y, hy⟩
    have hxy : col x ≠ col y := by
      rw [hy]
      cases hx : col x <;> simp [hx]
    exact ⟨⟨
      { entry := x
        exit := y
        run := fibre_run_of_terminals x y
          (FibreTerminalChoice.hamLaceable col hlace hxy) }, rfl⟩⟩

private noncomputable def fibrePack_from_entry {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (x : RowFibre hB X) :
    FibrePack (flipGraph r s) (rowProj hB) X :=
  (Classical.choice (fibrePack_from_entry_exists r s L B hB bd X x)).val

private theorem fibrePack_from_entry_entry {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (x : RowFibre hB X) :
    (fibrePack_from_entry r s L B hB bd X x).entry = x :=
  (Classical.choice (fibrePack_from_entry_exists r s L B hB bd X x)).property

private theorem fibrePack_to_exit_exists {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (y : RowFibre hB X) :
    Nonempty {P : FibrePack (flipGraph r s) (rowProj hB) X // P.exit = y} := by
  classical
  rcases bd.hfib_isMH X with hconn | ⟨col, _hproper, hsurj, hlace⟩
  · by_cases hother : ∃ x : RowFibre hB X, x ≠ y
    · rcases hother with ⟨x, hxy⟩
      exact ⟨⟨
        { entry := x
          exit := y
          run := fibre_run_of_terminals x y
            (FibreTerminalChoice.hamConnected hconn hxy) }, rfl⟩⟩
    · have huniq : ∀ v : MarginClass r s, v ∈ fibre (rowProj hB) X → v = y.val := by
        intro v hv
        by_contra hvy
        have hvX : rowProj hB v = X := (Finset.mem_filter.mp hv).2
        exact hother ⟨⟨v, hvX⟩, fun h => hvy (congrArg Subtype.val h)⟩
      exact ⟨⟨
        { entry := y
          exit := y
          run := fibre_run_of_terminals y y
            (FibreTerminalChoice.singleton rfl huniq) }, rfl⟩⟩
  · rcases hsurj (! col y) with ⟨x, hx⟩
    have hxy : col x ≠ col y := by
      rw [hx]
      cases hy : col y <;> simp [hy]
    exact ⟨⟨
      { entry := x
        exit := y
        run := fibre_run_of_terminals x y
          (FibreTerminalChoice.hamLaceable col hlace hxy) }, rfl⟩⟩

private noncomputable def fibrePack_to_exit {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (y : RowFibre hB X) :
    FibrePack (flipGraph r s) (rowProj hB) X :=
  (Classical.choice (fibrePack_to_exit_exists r s L B hB bd X y)).val

private theorem fibrePack_to_exit_exit {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B)
    (y : RowFibre hB X) :
    (fibrePack_to_exit r s L B hB bd X y).exit = y :=
  (Classical.choice (fibrePack_to_exit_exists r s L B hB bd X y)).property

private noncomputable def fibrePack_default {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB) (X : RowQ r s L B) :
    FibrePack (flipGraph r s) (rowProj hB) X :=
  fibrePack_from_entry r s L B hB bd X (Classical.choice (rowFibre_nonempty X))

/-- One forward propagation step across a row quotient edge. -/
structure PivotForwardStep {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B}
    (hXY : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (x : RowFibre hB X) where
  exit : RowFibre hB X
  delivered : RowFibre hB Y
  choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x exit
  adj : (flipGraph r s).Adj exit.val delivered.val

/-- Extract a forward propagation step from the packaged interface richness. -/
noncomputable def pivot_forward_step {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {X Y : RowQ r s L B}
    (hXY : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (x : RowFibre hB X) :
    PivotForwardStep r s L B hB hXY x := by
  classical
  exact Classical.choice (by
    rcases bd.hinterface_step hXY x with ⟨y, z, ⟨choice, hadj⟩⟩
    exact ⟨
      { exit := y
        delivered := z
        choice := choice
        adj := hadj }⟩)

/-- One backward-oriented propagation step across a row quotient edge `X -- Y`. -/
structure PivotBackwardStep {m n : ℕ} (r : Fin (m + 1) → ℕ) (s : Fin n → ℕ)
    (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {X Y : RowQ r s L B}
    (hXY : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (x : RowFibre hB Y) where
  entry : RowFibre hB Y
  delivered : RowFibre hB X
  choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) Y entry x
  adj : (flipGraph r s).Adj delivered.val entry.val

/-- Propagate backward by applying the forward interface step to the symmetric quotient edge. -/
noncomputable def pivot_backward_step {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {X Y : RowQ r s L B}
    (hXY : quotientAdj (flipGraph r s) (rowProj hB) X Y)
    (x : RowFibre hB Y) :
    PivotBackwardStep r s L B hB hXY x := by
  classical
  exact Classical.choice (by
    rcases bd.hinterface_step (quotientAdj_symm hXY) x with ⟨y, z, ⟨choice, hadj⟩⟩
    exact ⟨
      { entry := y
        delivered := z
        choice := choice.symm
        adj := hadj.symm }⟩)

/-- The final backward step into the buffer, with the delivered buffer terminal avoiding `bad`. -/
structure PivotBackwardAvoidStep {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {Y : RowQ r s L B}
    (hYbuf : quotientAdj (flipGraph r s) (rowProj hB) Y bd.buffer)
    (x : RowFibre hB Y) (bad : RowFibre hB bd.buffer) where
  entry : RowFibre hB Y
  delivered : RowFibre hB bd.buffer
  delivered_ne : delivered ≠ bad
  choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) Y entry x
  adj : (flipGraph r s).Adj delivered.val entry.val

/-- Extract the avoid-rich backward step into the buffer. -/
noncomputable def pivot_backward_avoid_step {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {Y : RowQ r s L B}
    (hYbuf : quotientAdj (flipGraph r s) (rowProj hB) Y bd.buffer)
    (x : RowFibre hB Y) (bad : RowFibre hB bd.buffer) :
    PivotBackwardAvoidStep r s L B hB bd hYbuf x bad := by
  classical
  exact Classical.choice (by
    rcases bd.hinterface_step_to_buffer_avoid hYbuf x bad with
      ⟨y, z, hz_ne, ⟨choice, hadj⟩⟩
    exact ⟨
      { entry := y
        delivered := z
        delivered_ne := hz_ne
        choice := choice.symm
        adj := hadj.symm }⟩)

structure PivotForwardAvoidStep {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {X : RowQ r s L B}
    (hXbuf : quotientAdj (flipGraph r s) (rowProj hB) X bd.buffer)
    (x : RowFibre hB X) (bad : RowFibre hB bd.buffer) where
  exit : RowFibre hB X
  delivered : RowFibre hB bd.buffer
  delivered_ne : delivered ≠ bad
  choice : FibreTerminalChoice (flipGraph r s) (rowProj hB) X x exit
  adj : (flipGraph r s).Adj exit.val delivered.val

noncomputable def pivot_forward_avoid_step {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    {X : RowQ r s L B}
    (hXbuf : quotientAdj (flipGraph r s) (rowProj hB) X bd.buffer)
    (x : RowFibre hB X) (bad : RowFibre hB bd.buffer) :
    PivotForwardAvoidStep r s L B hB bd hXbuf x bad := by
  classical
  exact Classical.choice (by
    rcases bd.hinterface_step_to_buffer_avoid hXbuf x bad with
      ⟨y, z, hz_ne, ⟨choice, hadj⟩⟩
    exact ⟨
      { exit := y
        delivered := z
        delivered_ne := hz_ne
        choice := choice
        adj := hadj }⟩)

private theorem qwalk_support_nodup_endpoint_eq {Q : Type u} {R : Q → Q → Prop}
    {q0 qe : Q} (w : QWalk R q0 qe) (hnd : (QWalk.support w).Nodup)
    (heq : q0 = qe) : QWalk.support w = [qe] := by
  cases w with
  | nil q => simp [QWalk.support]
  | cons hstep tail =>
      exfalso
      subst heq
      exact (List.nodup_cons.mp (by
        simpa [QWalk.support] using hnd)).1 (QWalk.end_mem_support tail)

private noncomputable def forward_build {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    (basePk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X) :
    ∀ {q0 qe : RowQ r s L B}
      (w : QWalk (quotientAdj (flipGraph r s) (rowProj hB)) q0 qe),
      qe = bd.buffer →
      (QWalk.support w).Nodup →
      ∀ (x0 : RowFibre hB q0),
      Σ' (pk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X),
      Σ' (bufEntry : RowFibre hB bd.buffer),
      Σ' (visited : List (RowQ r s L B)),
        (∀ X ∈ visited, X ∈ QWalk.support w) ∧
        visited ++ [bd.buffer] = QWalk.support w ∧
        bd.buffer ∉ visited ∧
        (∀ X, X ∉ visited → pk X = basePk X) ∧
        visited.IsChain
          (fun X Y => (flipGraph r s).Adj (pk X).exit.val (pk Y).entry.val) ∧
        (q0 ≠ bd.buffer →
          q0 ∈ visited ∧ (pk q0).entry.val = x0.val ∧ visited.head? = some q0) ∧
        (q0 = bd.buffer → visited = []) ∧
        (visited = [] → bufEntry.val = x0.val) ∧
        (∀ Z, visited.getLast? = some Z →
          (flipGraph r s).Adj (pk Z).exit.val bufEntry.val) := by
  intro q0 qe w
  induction w with
  | nil q =>
      intro hqe _hnd x0
      subst hqe
      refine ⟨basePk, x0, [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro X hX; simp at hX
      · rfl
      · simp
      · intro X _; rfl
      · simp
      · intro hne; exact absurd rfl hne
      · intro _; rfl
      · intro _; rfl
      · intro Z hZ; simp at hZ
  | @cons q0 q' q'' hstep tail ih =>
      intro hqe hnd x0
      subst hqe
      have hnd' : (QWalk.support tail).Nodup :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).2
      have hq0_notin : q0 ∉ QWalk.support tail :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
      have hbuf_in_tail : bd.buffer ∈ QWalk.support tail := QWalk.end_mem_support tail
      have hq0_ne_buf : q0 ≠ bd.buffer := by
        intro h; exact hq0_notin (h ▸ hbuf_in_tail)
      have hq0_ne_q' : q0 ≠ q' := by
        intro h; exact hq0_notin (h ▸ QWalk.head_mem_support tail)
      set step := pivot_forward_step r s L B hB bd hstep x0 with hstepdef
      set q0pack : FibrePack (flipGraph r s) (rowProj hB) q0 :=
        ⟨x0, step.exit, fibre_run_of_terminals x0 step.exit step.choice⟩ with hq0pack
      obtain ⟨pk', bufEntry, visited', hvsub', hsupport', hbuf', hdef', hchain',
        hpin', hstart', hempty', hlast'⟩ := ih rfl hnd' step.delivered
      refine ⟨Function.update pk' q0 q0pack, bufEntry, q0 :: visited',
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · simp [QWalk.support]
        · simp only [QWalk.support]
          exact List.mem_cons_of_mem _ (hvsub' X hX)
      · simp [QWalk.support, hsupport']
      · simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hq0_ne_buf, hbuf'⟩
      · intro X hX
        rw [List.mem_cons, not_or] at hX
        rw [Function.update_of_ne hX.1, hdef' X hX.2]
      · have hpk_eq_on' :
            ∀ X ∈ visited', Function.update pk' q0 q0pack X = pk' X := by
          intro X hX
          exact Function.update_of_ne (by
            rintro rfl
            exact hq0_notin (hvsub' X hX)) _ _
        rw [List.isChain_cons]
        constructor
        · intro y hy
          have hy_mem : y ∈ visited' := List.mem_of_mem_head? hy
          have hvne : visited' ≠ [] := by
            intro h
            rw [h] at hy_mem
            simp at hy_mem
          have hq'_ne_buf : q' ≠ bd.buffer := by
            intro h
            exact hvne (hstart' h)
          have hpin_tail := hpin' hq'_ne_buf
          have hyq' : q' = y := by
            simpa [hpin_tail.2.2] using hy
          subst hyq'
          have hupd_q0 :
              Function.update pk' q0 q0pack q0 = q0pack := Function.update_self _ _ _
          have hupd_y : Function.update pk' q0 q0pack q' = pk' q' :=
            Function.update_of_ne (Ne.symm hq0_ne_q') _ _
          show (flipGraph r s).Adj
            (Function.update pk' q0 q0pack q0).exit.val
            (Function.update pk' q0 q0pack q').entry.val
          rw [hupd_q0, hupd_y, hq0pack]
          rw [hpin_tail.2.1]
          exact step.adj
        · exact List.isChain_mono_on hchain' (fun {X Y} hX hY hadj => by
            rw [hpk_eq_on' X hX, hpk_eq_on' Y hY]
            exact hadj)
      · intro _hne
        refine ⟨List.mem_cons_self, ?_, ?_⟩
        · rw [Function.update_self]
        · rfl
      · intro h
        exact False.elim (hq0_ne_buf h)
      · intro h; simp at h
      · intro Z hZ
        by_cases hv : visited' = []
        · subst hv
          simp only [List.getLast?_singleton, Option.some.injEq] at hZ
          subst hZ
          rw [Function.update_self, hq0pack]
          rw [hempty' rfl]
          exact step.adj
        · have hlast_cons :
              (q0 :: visited').getLast? = visited'.getLast? :=
            List.getLast?_cons_of_ne_nil hv
          rw [hlast_cons] at hZ
          have hZmem : Z ∈ visited' := List.mem_of_mem_getLast? (by simpa [hZ])
          rw [Function.update_of_ne (by
            rintro rfl
            exact hq0_notin (hvsub' Z hZmem))]
          exact hlast' Z hZ

private noncomputable def forward_avoid_build {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    (basePk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X) :
    ∀ {q0 qe : RowQ r s L B}
      (w : QWalk (quotientAdj (flipGraph r s) (rowProj hB)) q0 qe),
      qe = bd.buffer →
      (QWalk.support w).Nodup →
      q0 ≠ bd.buffer →
      ∀ (x0 : RowFibre hB q0) (bad : RowFibre hB bd.buffer),
      Σ' (pk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X),
      Σ' (bufEntry : RowFibre hB bd.buffer),
      Σ' (visited : List (RowQ r s L B)),
        (∀ X ∈ visited, X ∈ QWalk.support w) ∧
        visited ++ [bd.buffer] = QWalk.support w ∧
        bd.buffer ∉ visited ∧
        (∀ X, X ∉ visited → pk X = basePk X) ∧
        visited.IsChain
          (fun X Y => (flipGraph r s).Adj (pk X).exit.val (pk Y).entry.val) ∧
        (q0 ∈ visited ∧ (pk q0).entry.val = x0.val ∧ visited.head? = some q0) ∧
        (∀ Z, visited.getLast? = some Z →
          (flipGraph r s).Adj (pk Z).exit.val bufEntry.val) ∧
        bufEntry ≠ bad := by
  intro q0 qe w
  induction w with
  | nil q =>
      intro hqe _hnd hne _x0 _bad
      exact False.elim (hne hqe)
  | @cons q0 q' q'' hstep tail ih =>
      intro hqe hnd hq0_ne_buf x0 bad
      subst hqe
      have hnd' : (QWalk.support tail).Nodup :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).2
      have hq0_notin : q0 ∉ QWalk.support tail :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
      have hq0_ne_q' : q0 ≠ q' := by
        intro h; exact hq0_notin (h ▸ QWalk.head_mem_support tail)
      by_cases hq'_buf : q' = bd.buffer
      · subst q'
        set step := pivot_forward_avoid_step r s L B hB bd hstep x0 bad with hstepdef
        set q0pack : FibrePack (flipGraph r s) (rowProj hB) q0 :=
          ⟨x0, step.exit, fibre_run_of_terminals x0 step.exit step.choice⟩ with hq0pack
        refine ⟨Function.update basePk q0 q0pack, step.delivered, [q0],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro X hX
          simp only [List.mem_singleton] at hX
          subst hX
          simp [QWalk.support]
        · have htail : QWalk.support tail = [bd.buffer] :=
            qwalk_support_nodup_endpoint_eq tail hnd' rfl
          simp [QWalk.support, htail]
        · simpa using Ne.symm hq0_ne_buf
        · intro X hX
          rw [List.mem_singleton] at hX
          exact Function.update_of_ne hX _ _
        · simp
        · refine ⟨by simp, ?_, by simp⟩
          rw [Function.update_self, hq0pack]
        · intro Z hZ
          simp only [List.getLast?_singleton, Option.some.injEq] at hZ
          subst hZ
          rw [Function.update_self, hq0pack]
          exact step.adj
        · exact step.delivered_ne
      · set step := pivot_forward_step r s L B hB bd hstep x0 with hstepdef
        set q0pack : FibrePack (flipGraph r s) (rowProj hB) q0 :=
          ⟨x0, step.exit, fibre_run_of_terminals x0 step.exit step.choice⟩ with hq0pack
        obtain ⟨pk', bufEntry, visited', hvsub', hsupport', hbuf', hdef', hchain',
          hpin', hlast', hdistinct'⟩ := ih rfl hnd' hq'_buf step.delivered bad
        refine ⟨Function.update pk' q0 q0pack, bufEntry, q0 :: visited',
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro X hX
          rcases List.mem_cons.mp hX with rfl | hX
          · simp [QWalk.support]
          · simp only [QWalk.support]
            exact List.mem_cons_of_mem _ (hvsub' X hX)
        · simp [QWalk.support, hsupport']
        · simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm hq0_ne_buf, hbuf'⟩
        · intro X hX
          rw [List.mem_cons, not_or] at hX
          rw [Function.update_of_ne hX.1, hdef' X hX.2]
        · have hpk_eq_on' :
              ∀ X ∈ visited', Function.update pk' q0 q0pack X = pk' X := by
            intro X hX
            exact Function.update_of_ne (by
              rintro rfl
              exact hq0_notin (hvsub' X hX)) _ _
          rw [List.isChain_cons]
          constructor
          · intro y hy
            have hy_mem : y ∈ visited' := List.mem_of_mem_head? hy
            have hy_ne_buf : y ≠ bd.buffer := by
              rintro rfl
              exact hbuf' hy_mem
            have hpin_tail := hpin'
            have hyq' : q' = y := by
              simpa [hpin_tail.2.2] using hy
            subst hyq'
            rw [Function.update_self,
              Function.update_of_ne (Ne.symm hq0_ne_q'), hq0pack]
            rw [hpin_tail.2.1]
            exact step.adj
          · exact List.isChain_mono_on hchain' (fun {X Y} hX hY hadj => by
              rw [hpk_eq_on' X hX, hpk_eq_on' Y hY]
              exact hadj)
        · refine ⟨List.mem_cons_self, ?_, ?_⟩
          · rw [Function.update_self]
          · rfl
        · intro Z hZ
          by_cases hv : visited' = []
          · subst hv
            simp only [List.getLast?_singleton, Option.some.injEq] at hZ
            subst hZ
            exact False.elim (by simpa using hpin'.1)
          · have hlast_cons :
                (q0 :: visited').getLast? = visited'.getLast? :=
              List.getLast?_cons_of_ne_nil hv
            rw [hlast_cons] at hZ
            have hZmem : Z ∈ visited' := List.mem_of_mem_getLast? (by simpa [hZ])
            rw [Function.update_of_ne (by
              rintro rfl
              exact hq0_notin (hvsub' Z hZmem))]
            exact hlast' Z hZ
        · exact hdistinct'

private noncomputable def backward_build {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (bd : PivotBufferData r s L B hB)
    (basePk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X) :
    ∀ {q0 qe : RowQ r s L B}
      (w : QWalk (quotientAdj (flipGraph r s) (rowProj hB)) q0 qe),
      qe = bd.buffer →
      (QWalk.support w).Nodup →
      q0 ≠ bd.buffer →
      ∀ (x0 : RowFibre hB q0) (bad : RowFibre hB bd.buffer),
      Σ' (pk : ∀ X, FibrePack (flipGraph r s) (rowProj hB) X),
      Σ' (bufExit : RowFibre hB bd.buffer),
      Σ' (visited : List (RowQ r s L B)),
        (∀ X ∈ visited, X ∈ QWalk.support w) ∧
        bd.buffer :: visited = (QWalk.support w).reverse ∧
        bd.buffer ∉ visited ∧
        (∀ X, X ∉ visited → pk X = basePk X) ∧
        visited.IsChain
          (fun X Y => (flipGraph r s).Adj (pk X).exit.val (pk Y).entry.val) ∧
        (q0 ∈ visited ∧ (pk q0).exit.val = x0.val ∧ visited.getLast? = some q0) ∧
        (∀ Z, visited.head? = some Z →
          (flipGraph r s).Adj bufExit.val (pk Z).entry.val) ∧
        bufExit ≠ bad := by
  intro q0 qe w
  induction w with
  | nil q =>
      intro hqe _hnd hne _x0 _bad
      exact False.elim (hne hqe)
  | @cons q0 q' q'' hstep tail ih =>
      intro hqe hnd hq0_ne_buf x0 bad
      subst hqe
      have hnd' : (QWalk.support tail).Nodup :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).2
      have hq0_notin : q0 ∉ QWalk.support tail :=
        (List.nodup_cons.mp (by simpa [QWalk.support] using hnd)).1
      have hq0_ne_q' : q0 ≠ q' := by
        intro h; exact hq0_notin (h ▸ QWalk.head_mem_support tail)
      by_cases hq'_buf : q' = bd.buffer
      · subst q'
        set step := pivot_backward_avoid_step r s L B hB bd hstep x0 bad with hstepdef
        set q0pack : FibrePack (flipGraph r s) (rowProj hB) q0 :=
          ⟨step.entry, x0, fibre_run_of_terminals step.entry x0 step.choice⟩ with hq0pack
        refine ⟨Function.update basePk q0 q0pack, step.delivered, [q0],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro X hX
          simp only [List.mem_singleton] at hX
          subst hX
          simp [QWalk.support]
        · have htail : QWalk.support tail = [bd.buffer] :=
            qwalk_support_nodup_endpoint_eq tail hnd' rfl
          simp [QWalk.support, htail]
        · simpa using Ne.symm hq0_ne_buf
        · intro X hX
          rw [List.mem_singleton] at hX
          exact Function.update_of_ne hX _ _
        · simp
        · refine ⟨by simp, ?_, by simp⟩
          rw [Function.update_self, hq0pack]
        · intro Z hZ
          simp only [List.head?_singleton, Option.some.injEq] at hZ
          subst hZ
          rw [Function.update_self, hq0pack]
          exact step.adj
        · exact step.delivered_ne
      · have hsymm : quotientAdj (flipGraph r s) (rowProj hB) q' q0 :=
          quotientAdj_symm hstep
        set step := pivot_backward_step r s L B hB bd hsymm x0 with hstepdef
        set q0pack : FibrePack (flipGraph r s) (rowProj hB) q0 :=
          ⟨step.entry, x0, fibre_run_of_terminals step.entry x0 step.choice⟩ with hq0pack
        obtain ⟨pk', bufExit, visited', hvsub', hsupport', hbuf', hdef', hchain',
          hpin', hfirst', hdistinct'⟩ := ih rfl hnd' hq'_buf step.delivered bad
        refine ⟨Function.update pk' q0 q0pack, bufExit, visited' ++ [q0],
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro X hX
          rw [List.mem_append, List.mem_singleton] at hX
          rcases hX with hX | rfl
          · simp only [QWalk.support]
            exact List.mem_cons_of_mem _ (hvsub' X hX)
          · simp [QWalk.support]
        · simp [QWalk.support, ← hsupport']
        · rw [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hbuf', Ne.symm hq0_ne_buf⟩
        · intro X hX
          rw [List.mem_append, List.mem_singleton, not_or] at hX
          rw [Function.update_of_ne hX.2, hdef' X hX.1]
        · have hpk_eq_on' :
            ∀ X ∈ visited', Function.update pk' q0 q0pack X = pk' X := by
              intro X hX
              exact Function.update_of_ne (by
                rintro rfl
                exact hq0_notin (hvsub' X hX)) _ _
          rw [List.isChain_append]
          refine ⟨?_, by simp, ?_⟩
          · exact List.isChain_mono_on hchain' (fun {X Y} hX hY hadj => by
              rw [hpk_eq_on' X hX, hpk_eq_on' Y hY]
              exact hadj)
          · intro x hx y hy
            simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
            subst hy
            have hx_mem : x ∈ visited' := List.mem_of_mem_getLast? hx
            have hlast_q' : q' = x := by
              simpa [hpin'.2.2] using hx
            subst hlast_q'
            rw [Function.update_of_ne (by
                rintro rfl
                exact hq0_notin (QWalk.head_mem_support tail)),
              Function.update_self, hq0pack]
            rw [hpin'.2.1]
            exact step.adj
        · refine ⟨by simp, ?_, ?_⟩
          · rw [Function.update_self, hq0pack]
          · simp
        · intro Z hZ
          by_cases hv : visited' = []
          · subst hv
            simp at hpin'
          · have hhead_append :
                (visited' ++ [q0]).head? = visited'.head? := by
              cases visited' with
              | nil => contradiction
              | cons x xs => rfl
            rw [hhead_append] at hZ
            have hZmem : Z ∈ visited' := List.mem_of_mem_head? hZ
            rw [Function.update_of_ne (by
              rintro rfl
              exact hq0_notin (hvsub' Z hZmem))]
            exact hfirst' Z hZ
        · exact hdistinct'

/-- The quotient path selected for buffer-split propagation. -/
def pivot_quotient_path_of_buffer {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    {a b : MarginClass r s} (_hab : a ≠ b) (hsep : rowPat L a ≠ rowPat L b)
    (bd : PivotBufferData r s L B hB) :
    QuotientHamPathList (quotientAdj (flipGraph r s) (rowProj hB))
      (rowProj hB a) (rowProj hB b) :=
  quotient_ham_path_list r s L B hB bd.hQnb (rowProj hB a) (rowProj hB b)
    (rowProj_ne_of_rowPat_ne hsep)

/-- Construct the terminal data for the concrete buffer-split thread. -/
noncomputable def pivot_thread_terminals_of_buffer {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (a b : MarginClass r s) (hab : a ≠ b) (hsep : rowPat L a ≠ rowPat L b)
    (bd : PivotBufferData r s L B hB) :
    ThreadTerminals (flipGraph r s) (rowProj hB)
      (pivot_quotient_path_of_buffer r s L B hB hab hsep bd).qs a b := by
  classical
  let qpath := pivot_quotient_path_of_buffer r s L B hB hab hsep bd
  have _hbuf_conn : IsHamConnected
      (fibreGraph (flipGraph r s) (rowProj hB) bd.buffer) :=
    isMH_hamConnected_of_nonbip (bd.hfib_isMH bd.buffer) bd.hbuf_nb
  have hbuf_mem : bd.buffer ∈ qpath.qs := qpath.hcover bd.buffer
  let left : List (RowQ r s L B) := Classical.choose (List.append_of_mem hbuf_mem)
  let right : List (RowQ r s L B) :=
    Classical.choose (Classical.choose_spec (List.append_of_mem hbuf_mem))
  have hsplit : qpath.qs = left ++ bd.buffer :: right :=
    Classical.choose_spec (Classical.choose_spec (List.append_of_mem hbuf_mem))
  clear_value left right
  let qa : RowQ r s L B := rowProj hB a
  let qb : RowQ r s L B := rowProj hB b
  have hqa_ne_qb : qa ≠ qb := by
    simpa [qa, qb] using rowProj_ne_of_rowPat_ne (hB := hB) hsep
  let R : RowQ r s L B → RowQ r s L B → Prop :=
    quotientAdj (flipGraph r s) (rowProj hB)
  have hchainSplit : (left ++ bd.buffer :: right).IsChain R := by
    simpa [R, hsplit] using qpath.hchain
  have hndSplit : (left ++ bd.buffer :: right).Nodup := by
    simpa [hsplit] using qpath.hnodup
  have hchainL : (left ++ [bd.buffer]).IsChain R := by
    have htmp : ((left ++ [bd.buffer]) ++ right).IsChain R := by
      simpa [List.append_assoc] using hchainSplit
    exact (List.isChain_append.mp htmp).1
  have hchainR : (bd.buffer :: right).IsChain R := by
    exact (List.isChain_append.mp hchainSplit).2.1
  have hheadL : (left ++ [bd.buffer]).head? = some qa := by
    have hheadSplit : (left ++ bd.buffer :: right).head? = some qa := by
      simpa [qa, hsplit] using qpath.hhead
    cases left with
    | nil => simpa using hheadSplit
    | cons x xs => simpa using hheadSplit
  have hlastL : (left ++ [bd.buffer]).getLast? = some bd.buffer := by
    simp
  have hheadR : (bd.buffer :: right).head? = some bd.buffer := by
    simp
  have hlastR : (bd.buffer :: right).getLast? = some qb := by
    have hlastSplit : (left ++ bd.buffer :: right).getLast? = some qb := by
      simpa [qb, hsplit] using qpath.hlast
    simpa [List.getLast?_append_of_ne_nil left (by simp : bd.buffer :: right ≠ [])]
      using hlastSplit
  let wL : QWalk R qa bd.buffer := qwalk_of_isChain hchainL hheadL hlastL
  have hwL_support : QWalk.support wL = left ++ [bd.buffer] := by
    simpa [wL] using qwalk_of_isChain_support hchainL hheadL hlastL
  have ndL : (QWalk.support wL).Nodup := by
    have htmp : ((left ++ [bd.buffer]) ++ right).Nodup := by
      simpa [List.append_assoc] using hndSplit
    simpa [hwL_support] using (List.Nodup.of_append_left htmp)
  let basePk : ∀ X : RowQ r s L B,
      FibrePack (flipGraph r s) (rowProj hB) X :=
    fun X => fibrePack_default r s L B hB bd X
  have hbuf_not_left : bd.buffer ∉ left := by
    intro hb
    have hcross := (List.nodup_append.mp hndSplit).2.2 bd.buffer hb bd.buffer (by simp)
    exact hcross rfl
  have hnot_left_of_right : ∀ {X : RowQ r s L B}, X ∈ right → X ∉ left := by
    intro X hX hleft
    have hcross := (List.nodup_append.mp hndSplit).2.2 X hleft X (by simp [hX])
    exact hcross rfl
  have hnot_buf_of_right : ∀ {X : RowQ r s L B}, X ∈ right → X ≠ bd.buffer := by
    intro X hX h
    have htail_nd : (bd.buffer :: right).Nodup :=
      (List.nodup_append.mp hndSplit).2.1
    exact htail_nd.notMem (h ▸ hX)
  by_cases hright : right = []
  · subst hright
    have hqb_buf : qb = bd.buffer := by
      simpa using hlastR.symm
    have hqa_ne_buf : qa ≠ bd.buffer := by
      intro h
      exact hqa_ne_qb (h.trans hqb_buf.symm)
    let aFibre : RowFibre hB qa := ⟨a, by simp [qa]⟩
    let bFibre : RowFibre hB bd.buffer := ⟨b, by simpa [qb, hqb_buf]⟩
    obtain ⟨pkF, bufEntry, visF, hvsubF, hsupportF, hbufF, hdefF, hchainF,
      hpinF, hlastF, hneF⟩ :=
        forward_avoid_build r s L B hB bd basePk wL rfl ndL hqa_ne_buf aFibre bFibre
    have hvisF : visF = left := by
      have h := hsupportF
      rw [hwL_support] at h
      exact List.append_cancel_right h
    let bufPack : FibrePack (flipGraph r s) (rowProj hB) bd.buffer :=
      ⟨bufEntry, bFibre, FibreRun.of_hasHamPath bufEntry bFibre
        (_hbuf_conn bufEntry bFibre hneF)⟩
    let packOf : ∀ X : RowQ r s L B,
        FibrePack (flipGraph r s) (rowProj hB) X :=
      fun X => if X ∈ left then pkF X else if h : X = bd.buffer then h.symm ▸ bufPack else pkF X
    have hpack_left : ∀ {X : RowQ r s L B}, X ∈ left → packOf X = pkF X := by
      intro X hX
      simp [packOf, hX]
    have hpack_buf : packOf bd.buffer = bufPack := by
      simp [packOf, hbuf_not_left]
    have hqa_left : qa ∈ left := by
      simpa [hvisF] using hpinF.1
    have hpack_qa_entry : (packOf qa).entry.val = a := by
      rw [hpack_left hqa_left]
      exact hpinF.2.1
    have hpack_qb_exit : (packOf qb).exit.val = b := by
      rw [hqb_buf, hpack_buf]
    refine
      { entry := fun X => (packOf X).entry.val
        exit := fun X => (packOf X).exit.val
        hentry_fibre := ?_
        hexit_fibre := ?_
        hrun := fun X => (packOf X).run
        hfirst := ?_
        hlast := ?_
        hcross := ?_ }
    · intro X
      simp [fibre, (packOf X).entry.property]
    · intro X
      simp [fibre, (packOf X).exit.property]
    · have hrun_head : ((packOf qa).run.run).head? = some a := by
        simpa [hpack_qa_entry] using (packOf qa).run.hhead
      simpa [qa] using
        threadedList_head?_of_head qpath.qs
          (fun X => (packOf X).run.run) qpath.hhead hrun_head
    · have hrun_last : ((packOf qb).run.run).getLast? = some b := by
        simpa [hpack_qb_exit] using (packOf qb).run.hlast
      have hrun_ne : ∀ X : RowQ r s L B, X ∈ qpath.qs → (packOf X).run.run ≠ [] := by
        intro X _hX
        exact (packOf X).run.hne
      simpa [qb] using
        threadedList_getLast?_of_getLast qpath.qs
          (fun X => (packOf X).run.run) qpath.hlast hrun_last hrun_ne
    · have hleft_chain :
          left.IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        have hchainLeftPk :
            left.IsChain
              (fun X Y => (flipGraph r s).Adj (pkF X).exit.val (pkF Y).entry.val) := by
          simpa [hvisF] using hchainF
        exact List.isChain_mono_on hchainLeftPk (fun {X Y} hX hY hadj => by
          rw [hpack_left hX, hpack_left hY]
          exact hadj)
      have hedge :
          (left ++ [bd.buffer]).IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        rw [List.isChain_append]
        refine ⟨hleft_chain, by simp, ?_⟩
        intro X hX Y hY
        simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hY
        subst Y
        have hXmem : X ∈ left := List.mem_of_mem_getLast? hX
        rw [hpack_left hXmem, hpack_buf]
        exact hlastF X (by simpa [hvisF] using hX)
      have hedge_qs :
          qpath.qs.IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        simpa [hsplit] using hedge
      exact hedge_qs.imp (fun {X Y} hXY => by
        simpa [runBoundaryAdj] using FibrePack.boundary_of_adj (packOf X) (packOf Y) hXY)
  · have hrevChain : ((bd.buffer :: right).reverse).IsChain R := by
      rw [List.isChain_reverse]
      exact hchainR.imp (fun {X Y} hXY => quotientAdj_symm hXY)
    have hheadRev : ((bd.buffer :: right).reverse).head? = some qb := by
      rw [List.head?_reverse]
      exact hlastR
    have hlastRev : ((bd.buffer :: right).reverse).getLast? = some bd.buffer := by
      simp [List.getLast?_reverse]
    let wR : QWalk R qb bd.buffer := qwalk_of_isChain hrevChain hheadRev hlastRev
    have hwR_support : QWalk.support wR = (bd.buffer :: right).reverse := by
      simpa [wR] using qwalk_of_isChain_support hrevChain hheadRev hlastRev
    have htail_nd : (bd.buffer :: right).Nodup :=
      (List.nodup_append.mp hndSplit).2.1
    have ndR : (QWalk.support wR).Nodup := by
      rw [hwR_support, List.nodup_reverse]
      exact htail_nd
    have hqb_right : qb ∈ right := by
      have hlast_right : right.getLast? = some qb := by
        cases right with
        | nil => exact absurd rfl hright
        | cons y ys => simpa using hlastR
      exact List.mem_of_mem_getLast? (by simp [hlast_right])
    have hqb_ne_buf : qb ≠ bd.buffer := hnot_buf_of_right hqb_right
    let aFibre : RowFibre hB qa := ⟨a, by simp [qa]⟩
    let bFibre : RowFibre hB qb := ⟨b, by simp [qb]⟩
    obtain ⟨pkF, bufEntry, visF, hvsubF, hsupportF, hbufF, hdefF, hchainF,
      hpinF, hstartF, hemptyF, hlastF⟩ :=
        forward_build r s L B hB bd basePk wL rfl ndL aFibre
    have hvisF : visF = left := by
      have h := hsupportF
      rw [hwL_support] at h
      exact List.append_cancel_right h
    obtain ⟨pkB, bufExit, visB, hvsubB, hsupportB, hbufB, hdefB, hchainB,
      hpinB, hfirstB, hneB⟩ :=
        backward_build r s L B hB bd basePk wR rfl ndR hqb_ne_buf bFibre bufEntry
    have hvisB : visB = right := by
      have h := hsupportB
      rw [hwR_support, List.reverse_reverse] at h
      exact (List.cons.inj h).2
    have hbuf_ne : bufEntry ≠ bufExit := by
      exact fun h => hneB h.symm
    let bufPack : FibrePack (flipGraph r s) (rowProj hB) bd.buffer :=
      ⟨bufEntry, bufExit, FibreRun.of_hasHamPath bufEntry bufExit
        (_hbuf_conn bufEntry bufExit hbuf_ne)⟩
    let packOf : ∀ X : RowQ r s L B,
        FibrePack (flipGraph r s) (rowProj hB) X :=
      fun X => if X ∈ left then pkF X else if h : X = bd.buffer then h.symm ▸ bufPack else pkB X
    have hpack_left : ∀ {X : RowQ r s L B}, X ∈ left → packOf X = pkF X := by
      intro X hX
      simp [packOf, hX]
    have hpack_buf : packOf bd.buffer = bufPack := by
      simp [packOf, hbuf_not_left]
    have hpack_right : ∀ {X : RowQ r s L B}, X ∈ right → packOf X = pkB X := by
      intro X hX
      simp [packOf, hnot_left_of_right hX, hnot_buf_of_right hX]
    have hpack_qa_entry : (packOf qa).entry.val = a := by
      by_cases hleft_empty : left = []
      · have hqa_buf : qa = bd.buffer := by
          have h : bd.buffer = qa := by simpa [hleft_empty] using hheadL
          exact h.symm
        have hvis_empty : visF = [] := by simpa [hvisF, hleft_empty]
        rw [hqa_buf, hpack_buf]
        exact hemptyF hvis_empty
      · have hqa_ne_buf : qa ≠ bd.buffer := by
          intro h
          have hqa_left : qa ∈ left := by
            cases left with
            | nil => contradiction
            | cons X xs =>
                simp at hheadL
                simpa [hheadL]
          exact hbuf_not_left (h ▸ hqa_left)
        have hpin := hpinF hqa_ne_buf
        have hqa_left : qa ∈ left := by simpa [hvisF] using hpin.1
        rw [hpack_left hqa_left]
        exact hpin.2.1
    have hpack_qb_exit : (packOf qb).exit.val = b := by
      rw [hpack_right hqb_right]
      exact hpinB.2.1
    refine
      { entry := fun X => (packOf X).entry.val
        exit := fun X => (packOf X).exit.val
        hentry_fibre := ?_
        hexit_fibre := ?_
        hrun := fun X => (packOf X).run
        hfirst := ?_
        hlast := ?_
        hcross := ?_ }
    · intro X
      simp [fibre, (packOf X).entry.property]
    · intro X
      simp [fibre, (packOf X).exit.property]
    · have hrun_head : ((packOf qa).run.run).head? = some a := by
        simpa [hpack_qa_entry] using (packOf qa).run.hhead
      simpa [qa] using
        threadedList_head?_of_head qpath.qs
          (fun X => (packOf X).run.run) qpath.hhead hrun_head
    · have hrun_last : ((packOf qb).run.run).getLast? = some b := by
        simpa [hpack_qb_exit] using (packOf qb).run.hlast
      have hrun_ne : ∀ X : RowQ r s L B, X ∈ qpath.qs → (packOf X).run.run ≠ [] := by
        intro X _hX
        exact (packOf X).run.hne
      simpa [qb] using
        threadedList_getLast?_of_getLast qpath.qs
          (fun X => (packOf X).run.run) qpath.hlast hrun_last hrun_ne
    · have hleft_chain :
          left.IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        have hchainLeftPk :
            left.IsChain
              (fun X Y => (flipGraph r s).Adj (pkF X).exit.val (pkF Y).entry.val) := by
          simpa [hvisF] using hchainF
        exact List.isChain_mono_on hchainLeftPk (fun {X Y} hX hY hadj => by
          rw [hpack_left hX, hpack_left hY]
          exact hadj)
      have hright_chain :
          right.IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        have hchainRightPk :
            right.IsChain
              (fun X Y => (flipGraph r s).Adj (pkB X).exit.val (pkB Y).entry.val) := by
          simpa [hvisB] using hchainB
        exact List.isChain_mono_on hchainRightPk (fun {X Y} hX hY hadj => by
          rw [hpack_right hX, hpack_right hY]
          exact hadj)
      have hleftBuf_chain :
          (left ++ [bd.buffer]).IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        rw [List.isChain_append]
        refine ⟨hleft_chain, by simp, ?_⟩
        intro X hX Y hY
        simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hY
        subst Y
        have hXmem : X ∈ left := List.mem_of_mem_getLast? hX
        rw [hpack_left hXmem, hpack_buf]
        exact hlastF X (by simpa [hvisF] using hX)
      have hedge :
          ((left ++ [bd.buffer]) ++ right).IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        rw [List.isChain_append]
        refine ⟨hleftBuf_chain, hright_chain, ?_⟩
        intro X hX Y hY
        have hXbuf : X = bd.buffer := by
          have h : bd.buffer = X := by simpa using hX
          exact h.symm
        subst X
        have hYmem : Y ∈ right := List.mem_of_mem_head? hY
        rw [hpack_buf, hpack_right hYmem]
        exact hfirstB Y (by simpa [hvisB] using hY)
      have hedge_qs :
          qpath.qs.IsChain
            (fun X Y => (flipGraph r s).Adj (packOf X).exit.val (packOf Y).entry.val) := by
        simpa [hsplit, List.append_assoc] using hedge
      exact hedge_qs.imp (fun {X Y} hXY => by
        simpa [runBoundaryAdj] using FibrePack.boundary_of_adj (packOf X) (packOf Y) hXY)

/-- End-to-end packer: once terminal propagation is supplied, the abstract thread data follows. -/
def pivot_thread_data_of_buffer {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (L : Fin (m + 1)) (B : BaseFamily (Fin n))
    (hB : ∀ p : Finset (Fin n),
      B.Base p ↔ Nonempty {M : MarginClass r s // rowSupport L M = p})
    (a b : MarginClass r s) (hab : a ≠ b) (hsep : rowPat L a ≠ rowPat L b)
    (bd : PivotBufferData r s L B hB) :
    PivotThreadData (flipGraph r s) a b := by
  classical
  let qpath := pivot_quotient_path_of_buffer r s L B hB hab hsep bd
  exact thread_from_terminals qpath.hchain qpath.hnodup qpath.hcover
    (pivot_thread_terminals_of_buffer r s L B hB a b hab hsep bd)

/-! ### Column-line case: concrete transpose transport -/

private theorem stageBTranspose_involutive {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (M : MarginClass r s) :
    stageBTransposeMargin (stageBTransposeMargin M) = M := by
  apply Subtype.ext
  rfl

private def stageBTransposeEquiv {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    MarginClass r s ≃ MarginClass s r where
  toFun := stageBTransposeMargin
  invFun := stageBTransposeMargin
  left_inv := stageBTranspose_involutive
  right_inv := stageBTranspose_involutive

private theorem interchange_stageBTranspose {m n : ℕ} {M N : ZeroOneMat m n}
    (h : Interchange M N) :
    Interchange (stageBTransposeMat M) (stageBTransposeMat N) := by
  rcases h with
    ⟨i, i', j, j', hii, hjj, hM11, hM22, hM12, hM21, hN11, hN22, hN12, hN21, hout⟩
  exact ⟨j, j', i, i', hjj, hii, hM11, hM22, hM21, hM12, hN11, hN22, hN21, hN12,
    fun a b hab => hout b a (fun hcond => hab ⟨hcond.2, hcond.1⟩)⟩

private theorem flipGraph_adj_stageBTranspose {m n : ℕ} {r : Fin m → ℕ}
    {s : Fin n → ℕ} {M N : MarginClass r s} (h : (flipGraph r s).Adj M N) :
    (flipGraph s r).Adj (stageBTransposeMargin M) (stageBTransposeMargin N) := by
  rw [flipGraph, SimpleGraph.fromRel_adj] at h ⊢
  refine ⟨fun heq => h.1 ?_, ?_⟩
  · have h2 := congrArg stageBTransposeMargin heq
    simpa [stageBTranspose_involutive] using h2
  · rcases h.2 with h2 | h2
    · exact Or.inl (interchange_stageBTranspose h2)
    · exact Or.inr (interchange_stageBTranspose h2)

private def stageBTransposeIso {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    flipGraph r s ≃g flipGraph s r where
  toEquiv := stageBTransposeEquiv r s
  map_rel_iff' := by
    intro M N
    constructor
    · intro h
      have h2 := flipGraph_adj_stageBTranspose (r := s) (s := r) h
      simpa [stageBTransposeEquiv, stageBTranspose_involutive] using h2
    · exact fun h => flipGraph_adj_stageBTranspose h

private theorem rowPat_stageBTranspose {m n : ℕ} {r : Fin m → ℕ} {s : Fin n → ℕ}
    (C : Fin n) (M : MarginClass r s) :
    rowPat C (stageBTransposeMargin M) = colPat C M := rfl

theorem flip_hamConnected_of_row_buffer {m n : ℕ} (r : Fin (m + 1) → ℕ)
    (s : Fin n → ℕ) (hact : IsActive r s) (hm : 3 ≤ m + 1) (hn : 3 ≤ n)
    (hprime : ¬ IsDecomposable (flipGraph r s))
    (hnb : ¬ ∃ col, IsProper2Coloring (flipGraph r s) col)
    (IH : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
       Fintype.card W < Fintype.card (MarginClass r s) → IsInterchangeGraph H → IsMH H) :
    IsHamConnected (flipGraph r s) := by
  classical
  intro a b hab
  rcases buffer_line_exists r s hact hm hn hprime hnb a b hab with
    ⟨line, hsepLine, hline_nb⟩
  cases line with
  | inl L =>
      have hsep : rowPat L a ≠ rowPat L b := by
        simpa [lineSeparates] using hsepLine
      rcases pivotBufferData_of_row_line r s hact hn hprime IH hab hsep hline_nb with
        ⟨B, hB, bd⟩
      exact hasHamPath_of_pivotThreadData
        (pivot_thread_data_of_buffer r s L B hB a b hab hsep bd)
  | inr C =>
      -- transpose to the row case for the margins (s, r)
      obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hab' : stageBTransposeMargin a ≠ stageBTransposeMargin b := by
        intro h
        apply hab
        have h2 := congrArg stageBTransposeMargin h
        simpa [stageBTranspose_involutive] using h2
      have hsep' :
          rowPat C (stageBTransposeMargin a) ≠ rowPat C (stageBTransposeMargin b) := by
        have hcp : colPat C a ≠ colPat C b := by
          simpa [lineSeparates] using hsepLine
        simpa [rowPat_stageBTranspose] using hcp
      have hline_nb' : lineFibreNonbip (r := s) (s := r) (Sum.inl C) := by
        rcases hline_nb with ⟨γ, hγnb⟩
        refine ⟨γ, ?_⟩
        rintro ⟨col', hcol'⟩
        apply hγnb
        refine ⟨fun N => col' ⟨stageBTransposeMargin N.val, by
          rw [rowPat_stageBTranspose]
          exact N.property⟩, ?_⟩
        intro u v huv
        exact hcol' _ _ (flipGraph_adj_stageBTranspose huv)
      have hprime' : ¬ IsDecomposable (flipGraph s r) := by
        intro hdec
        exact hprime (stageB_isDecomposable_congr (stageBTransposeIso r s).symm hdec)
      have hnb' : ¬ ∃ col' : MarginClass s r → Bool,
          IsProper2Coloring (flipGraph s r) col' := by
        rintro ⟨col', hcol'⟩
        exact hnb ⟨fun M => col' (stageBTransposeMargin M), fun u v huv =>
          hcol' _ _ (flipGraph_adj_stageBTranspose huv)⟩
      have hcard_eq :
          Fintype.card (MarginClass s r) = Fintype.card (MarginClass r s) :=
        Fintype.card_congr (stageBTransposeEquiv r s).symm
      have IH' : ∀ {W : Type} [DecidableEq W] [Fintype W] (H : SimpleGraph W),
          Fintype.card W < Fintype.card (MarginClass s r) →
            IsInterchangeGraph H → IsMH H := by
        intro W _ _ H hlt hIG'
        rw [hcard_eq] at hlt
        exact IH H hlt hIG'
      rcases pivotBufferData_of_row_line s r ⟨hact.2, hact.1⟩ hm hprime' IH'
          hab' hsep' hline_nb' with ⟨B, hB, bd⟩
      exact hasHamPath_iso (stageBTransposeIso r s)
        (hasHamPath_of_pivotThreadData
          (pivot_thread_data_of_buffer s r C B hB
            (stageBTransposeMargin a) (stageBTransposeMargin b) hab' hsep' bd))

/- Remaining §5 obligations:
   - Lemma-5.8 avoid richness: `PivotBufferData.hinterface_step_to_buffer_avoid`.
   - Column case: transpose the row-line construction.
   The foundational row packaging/wiring is above: buffer existence, row quotient non-bipartiteness,
   row interface stepping, buffer data assembly, and the row branch of the pivot thread. -/




end

end Brualdi.Ledger
