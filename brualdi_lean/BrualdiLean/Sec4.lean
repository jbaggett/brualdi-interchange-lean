/-
  §4 (reduction_decompose): a Cartesian-product interchange graph `G ≃g A □ B` is maximally Hamiltonian,
  given the factors are smaller interchange graphs that are MH (the induction hypothesis).

  Development file. Foundational reusable pieces first:
    • `boxProd_proper_color` — proper 2-colourings of `A`, `B` give one of `A □ B` (the xor colouring);
      the bipartiteness bookkeeping for the "both factors bipartite" case.
    • `boxProd_card_lt`      — nontrivial factors are strictly smaller (so the IH applies).
  The core snake/threading Hamiltonicity (`Walk.ofSupport` over a `List (WA × WB)` route) and the mixed
  bipartite/non-bipartite parity absorber (Prop 4.1) are the harder remaining steps.

  ROADMAP to discharge `reduction_decompose` (mirrors the reduction/CT decompositions):
    [DONE]  boxProd_proper_color, boxProd_card_lt.
    [DONE]  SNAKE (single corner-to-corner Hamilton path): `boxProd_snake_hamPath`.
    [DONE]  IsDecomposable strengthened (Ledger) to carry `IsInterchangeGraph` + instances on both
            factors, so the §4 IH applies. (Superseded the `cartesian_factor_interchange` contract.)
    [DONE]  `boxProd_hamConnected` — the all-pairs case-split ASSEMBLY (verified): reduces the
            non-bipartite branch to the two sub-lemmas below; both-bipartite is impossible (proper_color).
    [TODO]  `boxProd_hamConn_both_nonbip` — both factors Hamilton-connected ⇒ product Hamilton-connected
            (generalised-endpoint snake; reuse the `snakeList` machinery with per-column prescribed ends).
    [TODO]  `boxProd_hamConn_one_bip` — Proposition 4.1 doubled-layer parity absorber (incl. the K₂ prism):
            `A` balanced-bipartite + spanning-2-laceable, `B` non-bip Hamilton-connected ⇒ product
            Hamilton-connected. The hard one (Lemma 4.2 terminals + controlled spanning walks of B).
    [TODO]  wire `reduction_decompose` in Ledger: bipartite branch = `reduction_bipartite`; non-bip branch
            = factor-MH via IH + `boxProd_hamConnected` (spanning-2-lace of the bipartite factor from CORE)
            + `isMH_iso`. Only wire once the two sub-lemmas are complete.
-/
import BrualdiLean.ColemanDefs

namespace Brualdi.Ledger
open SimpleGraph

variable {WA WB : Type*} {A : SimpleGraph WA} {B : SimpleGraph WB}

/-- The xor of proper 2-colourings of the factors is a proper 2-colouring of the box product.
    (So `A □ B` is bipartite when both `A` and `B` are.) -/
theorem boxProd_proper_color {colA : WA → Bool} {colB : WB → Bool}
    (hA : ∀ u v, A.Adj u v → colA u ≠ colA v) (hB : ∀ u v, B.Adj u v → colB u ≠ colB v) :
    ∀ p q : WA × WB, (A □ B).Adj p q →
      (Bool.xor (colA p.1) (colB p.2)) ≠ (Bool.xor (colA q.1) (colB q.2)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hadj h
  rw [SimpleGraph.boxProd_adj] at hadj
  rcases hadj with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact hA a a' ha (by revert h; rw [hb]; cases colA a <;> cases colA a' <;> cases colB b' <;> decide)
  · exact hB b b' hb (by revert h; rw [ha]; cases colB b <;> cases colB b' <;> cases colA a' <;> decide)

/-- Nontrivial Cartesian factors of a finite graph are strictly smaller — so the §4 induction hypothesis
    applies to each factor. -/
theorem boxProd_card_lt {V : Type*} [Fintype V] [Fintype WA] [Fintype WB]
    {G : SimpleGraph V} (e : G ≃g A □ B) [Nontrivial WA] [Nontrivial WB] :
    Fintype.card WA < Fintype.card V ∧ Fintype.card WB < Fintype.card V := by
  have hcard : Fintype.card V = Fintype.card WA * Fintype.card WB := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_prod]
  have hA2 : 2 ≤ Fintype.card WA := Fintype.one_lt_card
  have hB2 : 2 ≤ Fintype.card WB := Fintype.one_lt_card
  refine ⟨?_, ?_⟩ <;> rw [hcard] <;> nlinarith

/-! ### The snake (boustrophedon) Hamilton path of a box product (Codex-drafted, boundary lemma by Claude). -/

/-- One vertical column of the boustrophedon traversal. -/
def snakeColumn (pathB : List WB) (ai : WA × ℕ) : List (WA × WB) :=
  ((if ai.2 % 2 = 0 then pathB else pathB.reverse).map (fun b => (ai.1, b)))

/-- The column-by-column boustrophedon traversal of the Cartesian product. -/
def snakeList (listA : List WA) (pathB : List WB) : List (WA × WB) :=
  (listA.zipIdx).flatMap (fun ai => snakeColumn pathB ai)

/-- Boundary relation used by `List.isChain_flatten`. -/
def listBoundaryAdj {α : Type*} (R : α → α → Prop) (l₁ l₂ : List α) : Prop :=
  ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y

lemma isChain_reverse_of_symmetric {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ {x y : α}, R x y → R y x) {l : List α} (h : l.IsChain R) :
    l.reverse.IsChain R := by
  rw [List.isChain_reverse]
  exact h.imp (fun {x y} hxy => hsymm (x := x) (y := y) hxy)

lemma snakeColumn_ne_nil
    (pathB : List WB) (ai : WA × ℕ) (hBne : pathB ≠ []) :
    snakeColumn pathB ai ≠ [] := by
  unfold snakeColumn
  by_cases h : ai.2 % 2 = 0
  · simpa [h, List.map_eq_nil_iff] using hBne
  · intro hnil
    apply hBne
    have : pathB.reverse = [] := by
      simpa [h, List.map_eq_nil_iff] using hnil
    simpa using congrArg List.reverse this

lemma snakeColumn_nodup [DecidableEq WA] [DecidableEq WB]
    (pathB : List WB) (ai : WA × ℕ) (hBnd : pathB.Nodup) :
    (snakeColumn pathB ai).Nodup := by
  have hinj : Function.Injective (fun b : WB => (ai.1, b)) := by
    intro b c hbc
    exact (Prod.mk.inj hbc).2
  unfold snakeColumn
  by_cases h : ai.2 % 2 = 0
  · simpa [h] using (List.Nodup.map hinj hBnd)
  · simpa [h] using (List.Nodup.map hinj (List.nodup_reverse.mpr hBnd))

lemma mem_snakeColumn_fst
    (pathB : List WB) (ai : WA × ℕ) {x : WA × WB}
    (hx : x ∈ snakeColumn pathB ai) :
    x.1 = ai.1 := by
  unfold snakeColumn at hx
  by_cases h : ai.2 % 2 = 0
  · simp only [h, ↓reduceIte, List.mem_map] at hx
    rcases hx with ⟨b, _hb, rfl⟩
    rfl
  · simp only [h, ↓reduceIte, List.mem_map] at hx
    rcases hx with ⟨b, _hb, rfl⟩
    rfl

lemma zipIdx_pairwise_fst_ne_of_nodup (listA : List WA) (hAnd : listA.Nodup) :
    (listA.zipIdx).Pairwise (fun x y : WA × ℕ => x.1 ≠ y.1) := by
  have hpairMap : (listA.zipIdx.map Prod.fst).Pairwise (fun x y : WA => x ≠ y) := by
    simpa [List.zipIdx_map_fst] using (List.nodup_iff_pairwise_ne.mp hAnd)
  exact List.pairwise_map.mp hpairMap

lemma snakeColumns_pairwise_disjoint [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (pathB : List WB) (hAnd : listA.Nodup) :
    (listA.zipIdx).Pairwise (Function.onFun List.Disjoint (snakeColumn pathB)) := by
  exact (zipIdx_pairwise_fst_ne_of_nodup listA hAnd).imp (fun {ai aj} hfst => by
    intro x hx hy
    exact hfst ((mem_snakeColumn_fst pathB ai hx).symm.trans (mem_snakeColumn_fst pathB aj hy)))

lemma snakeColumn_isChain
    (pathB : List WB) (ai : WA × ℕ) (hBc : pathB.IsChain B.Adj) :
    (snakeColumn (WA := WA) pathB ai).IsChain (A □ B).Adj := by
  unfold snakeColumn
  by_cases h : ai.2 % 2 = 0
  · simp only [h, ↓reduceIte]
    rw [List.isChain_map]
    exact hBc.imp (fun {x y} hxy => by
      rw [SimpleGraph.boxProd_adj]
      exact Or.inr ⟨hxy, rfl⟩)
  · simp only [h, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_reverse_of_symmetric (fun {x y} (hxy : B.Adj x y) => hxy.symm) hBc).imp
      (fun {x y} hxy => by
        rw [SimpleGraph.boxProd_adj]
        exact Or.inr ⟨hxy, rfl⟩)

lemma snakeColumns_no_nil
    (listA : List WA) (pathB : List WB) (hBne : pathB ≠ []) :
    [] ∉ (listA.zipIdx).map (fun ai => snakeColumn pathB ai) := by
  intro hnil
  rcases List.mem_map.mp hnil with ⟨ai, _hai, hcol⟩
  exact snakeColumn_ne_nil pathB ai hBne hcol

lemma zipIdx_isChain_adj_succ_from
    (n : ℕ) : ∀ (listA : List WA), listA.IsChain A.Adj →
    (listA.zipIdx n).IsChain (fun ai aj : WA × ℕ => A.Adj ai.1 aj.1 ∧ aj.2 = ai.2 + 1)
  | [], _ => by simp
  | [a], _ => by simp [List.zipIdx_cons]
  | a :: b :: bs, hAc => by
      have hrel : A.Adj a b := hAc.rel
      have htail : (b :: bs).IsChain A.Adj := hAc.of_cons
      have ihtail := zipIdx_isChain_adj_succ_from (n + 1) (b :: bs) htail
      rw [List.zipIdx_cons]
      exact ihtail.cons (fun y hy => by
        have hy' : y = (b, n + 1) := by
          simpa [List.zipIdx_cons] using hy.symm
        subst y
        exact ⟨hrel, rfl⟩)

lemma zipIdx_isChain_adj_succ
    (listA : List WA) (hAc : listA.IsChain A.Adj) :
    (listA.zipIdx).IsChain (fun ai aj : WA × ℕ => A.Adj ai.1 aj.1 ∧ aj.2 = ai.2 + 1) := by
  simpa using zipIdx_isChain_adj_succ_from (A := A) 0 listA hAc

/-- The turn: consecutive columns meet at a shared B-vertex (`pathB.getLast` for even→odd,
    `pathB.head` for odd→even), so the boundary step is the A-branch of `boxProd_adj`. -/
lemma snakeColumn_boundary_adj
    (pathB : List WB) {ai aj : WA × ℕ}
    (hA : A.Adj ai.1 aj.1) (hidx : aj.2 = ai.2 + 1) (hBne : pathB ≠ []) :
    listBoundaryAdj (A □ B).Adj (snakeColumn pathB ai) (snakeColumn pathB aj) := by
  unfold listBoundaryAdj snakeColumn
  intro x hx y hy
  by_cases hpar : ai.2 % 2 = 0
  · have hajne : ¬ aj.2 % 2 = 0 := by omega
    rw [if_pos hpar, List.getLast?_map] at hx
    rw [if_neg hajne, List.head?_map, List.head?_reverse] at hy
    rw [List.getLast?_eq_getLast_of_ne_nil hBne, Option.map_some, Option.mem_some_iff] at hx hy
    subst hx; subst hy
    rw [SimpleGraph.boxProd_adj]
    exact Or.inl ⟨hA, rfl⟩
  · have hajeq : aj.2 % 2 = 0 := by omega
    rw [if_neg hpar, List.getLast?_map, List.getLast?_reverse] at hx
    rw [if_pos hajeq, List.head?_map] at hy
    rw [List.head?_eq_some_head hBne, Option.map_some, Option.mem_some_iff] at hx hy
    subst hx; subst hy
    rw [SimpleGraph.boxProd_adj]
    exact Or.inl ⟨hA, rfl⟩

lemma snakeColumns_boundary_isChain
    (listA : List WA) (pathB : List WB)
    (hAc : listA.IsChain A.Adj) (hBne : pathB ≠ []) :
    ((listA.zipIdx).map (fun ai => snakeColumn pathB ai)).IsChain
      (listBoundaryAdj (A □ B).Adj) := by
  rw [List.isChain_map]
  exact (zipIdx_isChain_adj_succ (A := A) listA hAc).imp (fun {ai aj} hij =>
    snakeColumn_boundary_adj (A := A) (B := B) pathB hij.1 hij.2 hBne)

lemma snakeList_ne_nil
    (listA : List WA) (pathB : List WB) (hAne : listA ≠ []) (hBne : pathB ≠ []) :
    snakeList listA pathB ≠ [] := by
  cases listA with
  | nil => exact (hAne rfl).elim
  | cons a as =>
      cases pathB with
      | nil => exact (hBne rfl).elim
      | cons b bs =>
          simp [snakeList, snakeColumn]

lemma mem_snakeList_of_mem
    (listA : List WA) (pathB : List WB) {a : WA} {b : WB}
    (ha : a ∈ listA) (hb : b ∈ pathB) :
    (a, b) ∈ snakeList listA pathB := by
  rcases List.getElem_of_mem ha with ⟨i, hi, hia⟩
  rw [snakeList, List.mem_flatMap]
  have hzip0 : (listA[i], i) ∈ listA.zipIdx := by
    have hmem : (listA.zipIdx)[i]'(by simpa [List.length_zipIdx] using hi) ∈ listA.zipIdx :=
      List.getElem_mem (l := listA.zipIdx) (n := i) (by simpa [List.length_zipIdx] using hi)
    simpa [List.getElem_zipIdx] using hmem
  have hzip : (a, i) ∈ listA.zipIdx := by
    simpa [hia] using hzip0
  refine ⟨(a, i), hzip, ?_⟩
  unfold snakeColumn
  by_cases hpar : i % 2 = 0
  · simp [hpar, hb]
  · simp [hpar, hb, List.mem_reverse]

lemma snakeList_cover
    (listA : List WA) (pathB : List WB)
    (hAcov : ∀ a : WA, a ∈ listA) (hBcov : ∀ b : WB, b ∈ pathB) :
    ∀ x : WA × WB, x ∈ snakeList listA pathB := by
  rintro ⟨a, b⟩
  exact mem_snakeList_of_mem listA pathB (hAcov a) (hBcov b)

lemma snakeList_nodup [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (pathB : List WB)
    (hAnd : listA.Nodup) (hBnd : pathB.Nodup) :
    (snakeList listA pathB).Nodup := by
  rw [snakeList, List.nodup_flatMap]
  exact ⟨fun ai _ => snakeColumn_nodup pathB ai hBnd,
    snakeColumns_pairwise_disjoint listA pathB hAnd⟩

lemma snakeList_isChain
    (listA : List WA) (pathB : List WB)
    (hAc : listA.IsChain A.Adj) (hBc : pathB.IsChain B.Adj) (hBne : pathB ≠ []) :
    (snakeList listA pathB).IsChain (A □ B).Adj := by
  let cols : List (List (WA × WB)) := (listA.zipIdx).map (fun ai => snakeColumn pathB ai)
  have hcols_ne : [] ∉ cols := by
    simpa [cols] using snakeColumns_no_nil listA pathB hBne
  have hcols_chain : cols.IsChain (listBoundaryAdj (A □ B).Adj) := by
    simpa [cols] using snakeColumns_boundary_isChain (A := A) (B := B) listA pathB hAc hBne
  have hcols_internal : ∀ c ∈ cols, c.IsChain (A □ B).Adj := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨ai, _hai, rfl⟩
    exact snakeColumn_isChain (A := A) (B := B) pathB ai hBc
  have hcols_boundary : cols.IsChain
      (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), (A □ B).Adj x y) := by
    change cols.IsChain (listBoundaryAdj (A □ B).Adj)
    exact hcols_chain
  have hflat : cols.flatten.IsChain (A □ B).Adj := by
    exact (List.isChain_flatten (R := (A □ B).Adj) hcols_ne).2 ⟨hcols_internal, hcols_boundary⟩
  simpa [snakeList, cols, List.flatMap] using hflat

/-- **The snake Hamilton path.** From spanning paths of the factors (`IsChain`, `Nodup`, covering),
    the box product has a Hamilton path (built as the boustrophedon route via `Walk.ofSupport`). -/
theorem boxProd_snake_hamPath
    [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (pathB : List WB)
    (hAc : listA.IsChain A.Adj) (hAnd : listA.Nodup) (hAcov : ∀ a, a ∈ listA)
    (hBc : pathB.IsChain B.Adj) (hBnd : pathB.Nodup) (hBcov : ∀ b, b ∈ pathB)
    (hAne : listA ≠ []) (hBne : pathB ≠ []) :
    ∃ (s t : WA × WB) (p : (A □ B).Walk s t), p.IsHamiltonian := by
  let l : List (WA × WB) := snakeList listA pathB
  have hl_ne : l ≠ [] := snakeList_ne_nil listA pathB hAne hBne
  have hl_chain : l.IsChain (A □ B).Adj := snakeList_isChain (A := A) (B := B) listA pathB hAc hBc hBne
  let p : (A □ B).Walk (l.head hl_ne) (l.getLast hl_ne) :=
    SimpleGraph.Walk.ofSupport l hl_ne hl_chain
  refine ⟨l.head hl_ne, l.getLast hl_ne, p, ?_⟩
  have hp_support : p.support = l := by simp [p]
  have hp_path : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hp_support]; exact snakeList_nodup listA pathB hAnd hBnd)
  exact hp_path.isHamiltonian_of_mem (fun x => by
    rw [hp_support]; exact snakeList_cover listA pathB hAcov hBcov x)

/-! ### §4 assembly: `A □ B` non-bipartite ⇒ Hamilton-connected (the all-pairs lift). -/

/-- Hamilton-connectedness transports across a graph isomorphism. -/
theorem isHamConnected_iso {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (h : IsHamConnected H) :
    IsHamConnected G := by
  intro u v huv
  exact hasHamPath_iso e (h (e u) (e v) (e.injective.ne huv))

/-- A factor's structural dichotomy for the §4 lift: either **non-bipartite and Hamilton-connected**,
    or **bipartite with the full paired-cover witness** (a proper colour that is surjective, laceable,
    and spanning-2-laceable). Derivable at the Ledger call site from `IsMH` + CORE (spanning-2-lace) and
    `interchange_has_edge` (surjectivity). Casing on this — rather than on the raw `IsMH` disjunct —
    is what avoids the `IsHamConnected`-does-not-imply-non-bipartite trap (`K₂` is both, and
    `K₂ □ K₂ = C₄` is *not* Hamilton-connected). -/
def FactorReady {W : Type*} [DecidableEq W] (G : SimpleGraph W) : Prop :=
  (¬ (∃ col, IsProper2Coloring G col) ∧ IsHamConnected G) ∨
    (∃ col, IsProper2Coloring G col ∧ Function.Surjective col ∧
      IsHamLaceable G col ∧ IsSpanning2DPCOpposite G col)

private theorem head?_eq_head_of_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    l.head? = some (l.head h) := by
  exact List.head?_eq_some_head h

theorem walk_support_head? {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : p.support.head? = some u := by
  rw [head?_eq_head_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.head_support p)

theorem walk_support_getLast? {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : p.support.getLast? = some v := by
  rw [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]
  exact congrArg some (SimpleGraph.Walk.getLast_support p)

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

theorem card_ge_three_of_not_bip [Fintype WA] [DecidableEq WA]
    (hnb : ¬ ∃ col, IsProper2Coloring A col) : 3 ≤ Fintype.card WA := by
  classical
  by_contra hcard
  have hle_two : Fintype.card WA ≤ 2 := by omega
  have hle_bool : Fintype.card WA ≤ Fintype.card Bool := by
    simpa [Fintype.card_bool] using hle_two
  rcases Function.Embedding.nonempty_of_card_le (α := WA) (β := Bool) hle_bool with ⟨e⟩
  apply hnb
  refine ⟨fun w => e w, ?_⟩
  intro u v huv hcol
  have huv_eq : u = v := e.injective hcol
  subst v
  exact A.loopless.irrefl u huv

theorem walk_even_length_iff_color_eq
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) {u v : WA}
    (p : A.Walk u v) :
    Even p.length ↔ colA u = colA v := by
  induction p with
  | nil =>
      simp
  | @cons u v w huv p ih =>
      simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one]
      have huv_col : colA u ≠ colA v := hAbip u v huv
      rw [ih]
      cases hu : colA u <;> cases hv : colA v <;> cases hw : colA w <;>
        simp [hu, hv] at huv_col ⊢

theorem even_card_of_bip_laceable_surj [Fintype WA] [DecidableEq WA]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA) :
    Even (Fintype.card WA) := by
  classical
  rcases hAsurj false with ⟨a0, ha0⟩
  rcases hAsurj true with ⟨a1, ha1⟩
  have hcol : colA a0 ≠ colA a1 := by
    rw [ha0, ha1]
    decide
  rcases hAlace a0 a1 hcol with ⟨p, hp⟩
  have hodd_len : Odd p.length := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hcol ((walk_even_length_iff_color_eq (A := A) hAbip p).mp heven)
  rw [hp.length_eq] at hodd_len
  rcases hodd_len with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  have hpos : 0 < Fintype.card WA := Fintype.card_pos_iff.mpr ⟨a0⟩
  omega

private theorem mem_pair_of_card_two [Fintype WA] [DecidableEq WA]
    (hcard : Fintype.card WA = 2) {x y z : WA} (hxy : x ≠ y) :
    z = x ∨ z = y := by
  classical
  have hpair_univ : ({x, y} : Finset WA) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp
    · rw [Finset.card_univ, hcard]
      exact (Finset.card_pair hxy).ge
  have hz : z ∈ ({x, y} : Finset WA) := by
    rw [hpair_univ]
    simp
  simpa using hz

private theorem adj_of_card_two_laceable [Fintype WA] [DecidableEq WA]
    {colA : WA → Bool} (hcard : Fintype.card WA = 2)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    {x y : WA} (hxy : x ≠ y) : A.Adj x y := by
  classical
  have hcardBool : Fintype.card WA = Fintype.card Bool := by
    simpa [Fintype.card_bool] using hcard
  have hbij : Function.Bijective colA :=
    (Fintype.bijective_iff_surjective_and_card colA).2 ⟨hAsurj, hcardBool⟩
  have hcol : colA x ≠ colA y := hbij.injective.ne hxy
  rcases hAlace x y hcol with ⟨p, hp⟩
  have hlen : p.length = 1 := by
    rw [hp.length_eq, hcard]
  exact SimpleGraph.Walk.adj_of_length_eq_one hlen

private theorem endpoint_chain_exists_of_card_three {W : Type*} [Fintype W]
    (hcard : 3 ≤ Fintype.card W) :
    ∀ n : ℕ, 2 ≤ n → ∀ s t : W,
      ∃ l : List W,
        l.length = n + 1 ∧ l.head? = some s ∧ l.getLast? = some t ∧
          l.IsChain (fun x y => x ≠ y) := by
  classical
  refine Nat.le_induction ?base ?step
  · intro s t
    have hEN : 3 ≤ ENat.card W := by
      simpa [ENat.card, Nat.card_eq_fintype_card] using hcard
    rcases ENat.exists_ne_ne_of_three_le hEN s t with ⟨x, hxs, hxt⟩
    refine ⟨[s, x, t], ?_, ?_, ?_, ?_⟩ <;> simp [hxs.symm, hxt]
  · intro n hn ih s t
    have hone : 1 < Fintype.card W := by omega
    rcases Fintype.exists_ne_of_one_lt_card hone s with ⟨x, hxs⟩
    rcases ih x t with ⟨l, hlen, hhead, hlast, hchain⟩
    refine ⟨s :: l, by simp [hlen], by simp, ?_, ?_⟩
    · cases l with
      | nil => simp at hhead
      | cons y ys =>
          simp at hhead
          subst y
          simpa using hlast
    · rw [List.isChain_cons]
      refine ⟨?_, hchain⟩
      intro y hy
      have hyx : y = x := by
        rw [hhead] at hy
        simpa using hy.symm
      subst y
      exact hxs.symm

private def routedColumn (runs : ℕ → List WB) (ai : WA × ℕ) : List (WA × WB) :=
  (runs ai.2).map (fun b => (ai.1, b))

private def routedList (listA : List WA) (runs : ℕ → List WB) : List (WA × WB) :=
  (listA.zipIdx).flatMap (fun ai => routedColumn runs ai)

private theorem mem_routedColumn_fst
    (runs : ℕ → List WB) (ai : WA × ℕ) {x : WA × WB}
    (hx : x ∈ routedColumn runs ai) :
    x.1 = ai.1 := by
  unfold routedColumn at hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨b, _hb, rfl⟩
  rfl

private theorem routedColumn_nodup [DecidableEq WA] [DecidableEq WB]
    (runs : ℕ → List WB) (ai : WA × ℕ) (hnd : (runs ai.2).Nodup) :
    (routedColumn runs ai).Nodup := by
  have hinj : Function.Injective (fun b : WB => (ai.1, b)) := by
    intro b c hbc
    exact (Prod.mk.inj hbc).2
  exact List.Nodup.map hinj hnd

private theorem routedColumn_isChain
    (runs : ℕ → List WB) (ai : WA × ℕ) (hc : (runs ai.2).IsChain B.Adj) :
    (routedColumn (WA := WA) runs ai).IsChain (A □ B).Adj := by
  unfold routedColumn
  rw [List.isChain_map]
  exact hc.imp (fun {x y} hxy => by
    rw [SimpleGraph.boxProd_adj]
    exact Or.inr ⟨hxy, rfl⟩)

private theorem routedColumns_pairwise_disjoint [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (runs : ℕ → List WB) (hAnd : listA.Nodup) :
    (listA.zipIdx).Pairwise (Function.onFun List.Disjoint (routedColumn runs)) := by
  exact (zipIdx_pairwise_fst_ne_of_nodup listA hAnd).imp (fun {ai aj} hfst => by
    intro x hx hy
    exact hfst ((mem_routedColumn_fst runs ai hx).symm.trans (mem_routedColumn_fst runs aj hy)))

private theorem routedColumn_boundary_adj
    (runs : ℕ → List WB) {ai aj : WA × ℕ}
    (hA : A.Adj ai.1 aj.1)
    (hmatch : (runs ai.2).getLast? = (runs aj.2).head?) :
    listBoundaryAdj (A □ B).Adj (routedColumn runs ai) (routedColumn runs aj) := by
  unfold listBoundaryAdj routedColumn
  intro x hx y hy
  rw [List.getLast?_map] at hx
  rw [List.head?_map] at hy
  cases hlast : (runs ai.2).getLast? with
  | none => simp [hlast] at hx
  | some b =>
      cases hhead : (runs aj.2).head? with
      | none => simp [hhead] at hy
      | some c =>
          simp [hlast] at hx
          simp [hhead] at hy
          subst x
          subst y
          have hbc : b = c := by
            have hs : some b = some c := by simpa [hlast, hhead] using hmatch
            exact Option.some.inj hs
          subst c
          rw [SimpleGraph.boxProd_adj]
          exact Or.inl ⟨hA, rfl⟩

private theorem routedColumns_no_nil
    (listA : List WA) (runs : ℕ → List WB)
    (hrun_ne : ∀ i, i < listA.length → runs i ≠ []) :
    [] ∉ (listA.zipIdx).map (fun ai => routedColumn runs ai) := by
  intro hnil
  rcases List.mem_map.mp hnil with ⟨ai, hai, hcol⟩
  have hi : ai.2 < listA.length := by
    simpa using (List.snd_lt_of_mem_zipIdx (l := listA) (k := 0) hai)
  unfold routedColumn at hcol
  exact hrun_ne ai.2 hi (List.map_eq_nil_iff.mp hcol)

private theorem routedColumns_boundary_isChain
    (listA : List WA) (runs : ℕ → List WB)
    (hAc : listA.IsChain A.Adj)
    (hmatch : ∀ i, i + 1 < listA.length → (runs i).getLast? = (runs (i + 1)).head?) :
    ((listA.zipIdx).map (fun ai => routedColumn runs ai)).IsChain
      (listBoundaryAdj (A □ B).Adj) := by
  rw [List.isChain_map]
  exact (zipIdx_isChain_adj_succ (A := A) listA hAc).imp_of_mem_imp
    (fun ai aj hai haj hij => by
      have hjlt : aj.2 < listA.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := listA) (k := 0) haj)
      have hi1 : ai.2 + 1 < listA.length := by
        simpa [hij.2] using hjlt
      exact routedColumn_boundary_adj (A := A) (B := B) runs hij.1 (by
        simpa [hij.2] using hmatch ai.2 hi1))

private theorem routedList_isChain
    (listA : List WA) (runs : ℕ → List WB)
    (hAc : listA.IsChain A.Adj)
    (hrun_chain : ∀ i, i < listA.length → (runs i).IsChain B.Adj)
    (hrun_ne : ∀ i, i < listA.length → runs i ≠ [])
    (hmatch : ∀ i, i + 1 < listA.length → (runs i).getLast? = (runs (i + 1)).head?) :
    (routedList listA runs).IsChain (A □ B).Adj := by
  let cols : List (List (WA × WB)) := (listA.zipIdx).map (fun ai => routedColumn runs ai)
  have hcols_ne : [] ∉ cols := by
    simpa [cols] using routedColumns_no_nil listA runs hrun_ne
  have hcols_chain : cols.IsChain (listBoundaryAdj (A □ B).Adj) := by
    simpa [cols] using routedColumns_boundary_isChain (A := A) (B := B) listA runs hAc hmatch
  have hcols_internal : ∀ c ∈ cols, c.IsChain (A □ B).Adj := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨ai, hai, rfl⟩
    have hi : ai.2 < listA.length := by
      simpa using (List.snd_lt_of_mem_zipIdx (l := listA) (k := 0) hai)
    exact routedColumn_isChain (A := A) (B := B) runs ai (hrun_chain ai.2 hi)
  have hcols_boundary : cols.IsChain
      (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), (A □ B).Adj x y) := by
    change cols.IsChain (listBoundaryAdj (A □ B).Adj)
    exact hcols_chain
  have hflat : cols.flatten.IsChain (A □ B).Adj := by
    exact (List.isChain_flatten (R := (A □ B).Adj) hcols_ne).2 ⟨hcols_internal, hcols_boundary⟩
  simpa [routedList, cols, List.flatMap] using hflat

private theorem routedList_nodup [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (runs : ℕ → List WB)
    (hAnd : listA.Nodup)
    (hrun_nodup : ∀ i, i < listA.length → (runs i).Nodup) :
    (routedList listA runs).Nodup := by
  rw [routedList, List.nodup_flatMap]
  exact ⟨fun ai hai => by
      have hi : ai.2 < listA.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := listA) (k := 0) hai)
      exact routedColumn_nodup runs ai (hrun_nodup ai.2 hi),
    routedColumns_pairwise_disjoint listA runs hAnd⟩

private theorem mem_routedList_of_mem
    (listA : List WA) (runs : ℕ → List WB) {a : WA} {b : WB}
    (ha : a ∈ listA)
    (hrun_cover : ∀ i, i < listA.length → ∀ b, b ∈ runs i) :
    (a, b) ∈ routedList listA runs := by
  rcases List.getElem_of_mem ha with ⟨i, hi, hia⟩
  rw [routedList, List.mem_flatMap]
  have hzip0 : (listA[i], i) ∈ listA.zipIdx := by
    have hmem : (listA.zipIdx)[i]'(by simpa [List.length_zipIdx] using hi) ∈ listA.zipIdx :=
      List.getElem_mem (l := listA.zipIdx) (n := i) (by simpa [List.length_zipIdx] using hi)
    simpa [List.getElem_zipIdx] using hmem
  have hzip : (a, i) ∈ listA.zipIdx := by
    simpa [hia] using hzip0
  refine ⟨(a, i), hzip, ?_⟩
  unfold routedColumn
  exact List.mem_map.mpr ⟨b, hrun_cover i hi b, rfl⟩

private theorem routedList_cover
    (listA : List WA) (runs : ℕ → List WB)
    (hAcov : ∀ a : WA, a ∈ listA)
    (hrun_cover : ∀ i, i < listA.length → ∀ b, b ∈ runs i) :
    ∀ x : WA × WB, x ∈ routedList listA runs := by
  rintro ⟨a, b⟩
  exact mem_routedList_of_mem listA runs (hAcov a) hrun_cover

private theorem flatMap_head?_eq {α β : Type*} (l : List α) (f : α → List β)
    {a : α} {b : β} (hhead : l.head? = some a) (hfhead : (f a).head? = some b) :
    (l.flatMap f).head? = some b := by
  cases l with
  | nil => simp at hhead
  | cons x xs =>
      simp at hhead
      subst x
      have hfa_ne : f a ≠ [] := by
        intro hnil
        rw [hnil] at hfhead
        simp at hfhead
      rw [List.flatMap_cons, List.head?_append_of_ne_nil _ hfa_ne]
      exact hfhead

private theorem flatMap_getLast?_eq {α β : Type*} (l : List α) (f : α → List β)
    {a : α} {b : β} (hlast : l.getLast? = some a)
    (hne : ∀ x ∈ l, f x ≠ []) (hflast : (f a).getLast? = some b) :
    (l.flatMap f).getLast? = some b := by
  induction l with
  | nil => simp at hlast
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp at hlast
          subst x
          simpa using hflast
      | cons y ys =>
          have htail_last : (y :: ys).getLast? = some a := by
            simpa using hlast
          have htail_ne : ∀ z ∈ y :: ys, f z ≠ [] := by
            intro z hz
            exact hne z (by simp [hz])
          have ih' := ih htail_last htail_ne
          have htail_flat_ne : (List.flatMap f (y :: ys)) ≠ [] := by
            have hfy : f y ≠ [] := hne y (by simp)
            rw [List.flatMap_cons]
            exact List.append_ne_nil_of_left_ne_nil hfy (List.flatMap f ys)
          rw [List.flatMap_cons, List.getLast?_append_of_ne_nil (f x) htail_flat_ne]
          exact ih'

private theorem zipIdx_head?_eq {α : Type*} (listA : List α) {a : α}
    (hhead : listA.head? = some a) :
    listA.zipIdx.head? = some (a, 0) := by
  cases listA with
  | nil => simp at hhead
  | cons x xs =>
      simp at hhead
      subst x
      simp [List.zipIdx_cons]

private theorem zipIdx_getLast?_eq {α : Type*} (listA : List α) {a : α}
    (hlast : listA.getLast? = some a) :
    listA.zipIdx.getLast? = some (a, listA.length - 1) := by
  have hne : listA ≠ [] := by
    intro hnil
    simp [hnil] at hlast
  have hpos : 0 < listA.length := List.length_pos_iff.mpr hne
  have hidx : listA.length - 1 < listA.length := Nat.sub_lt hpos Nat.zero_lt_one
  have hget : listA[listA.length - 1] = a := by
    have h := hlast
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx] at h
    exact Option.some.inj h
  rw [List.getLast?_eq_getElem?]
  have hzidx : (listA.zipIdx).length - 1 < (listA.zipIdx).length := by
    simpa [List.length_zipIdx] using hidx
  rw [List.getElem?_eq_getElem hzidx]
  simp [List.getElem_zipIdx, List.length_zipIdx, hget]

private theorem routedList_head?_eq
    (listA : List WA) (runs : ℕ → List WB) {a : WA} {b : WB}
    (hAhead : listA.head? = some a) (hrun_head : (runs 0).head? = some b) :
    (routedList listA runs).head? = some (a, b) := by
  exact flatMap_head?_eq (listA.zipIdx) (fun ai => routedColumn runs ai)
    (zipIdx_head?_eq listA hAhead) (by
      simp [routedColumn, List.head?_map, hrun_head])

private theorem routedList_getLast?_eq
    (listA : List WA) (runs : ℕ → List WB) {a : WA} {b : WB}
    (hAlast : listA.getLast? = some a)
    (hrun_ne : ∀ i, i < listA.length → runs i ≠ [])
    (hrun_last : (runs (listA.length - 1)).getLast? = some b) :
    (routedList listA runs).getLast? = some (a, b) := by
  exact flatMap_getLast?_eq (listA.zipIdx) (fun ai => routedColumn runs ai)
    (zipIdx_getLast?_eq listA hAlast)
    (fun ai hai => by
      have hi : ai.2 < listA.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := listA) (k := 0) hai)
      unfold routedColumn
      exact fun hmap => hrun_ne ai.2 hi (List.map_eq_nil_iff.mp hmap))
    (by
      simp [routedColumn, List.getLast?_map, hrun_last])

private theorem boxProd_routed_hamPath
    [DecidableEq WA] [DecidableEq WB]
    (listA : List WA) (runs : ℕ → List WB) (a0 a1 : WA) (b0 b1 : WB)
    (hAc : listA.IsChain A.Adj) (hAnd : listA.Nodup) (hAcov : ∀ a, a ∈ listA)
    (hAhead : listA.head? = some a0) (hAlast : listA.getLast? = some a1)
    (hrun_chain : ∀ i, i < listA.length → (runs i).IsChain B.Adj)
    (hrun_nodup : ∀ i, i < listA.length → (runs i).Nodup)
    (hrun_cover : ∀ i, i < listA.length → ∀ b, b ∈ runs i)
    (hrun_ne : ∀ i, i < listA.length → runs i ≠ [])
    (hrun_head0 : (runs 0).head? = some b0)
    (hrun_last : (runs (listA.length - 1)).getLast? = some b1)
    (hmatch : ∀ i, i + 1 < listA.length → (runs i).getLast? = (runs (i + 1)).head?) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  let l : List (WA × WB) := routedList listA runs
  have hl_head : l.head? = some (a0, b0) := by
    simpa [l] using routedList_head?_eq listA runs hAhead hrun_head0
  have hl_last : l.getLast? = some (a1, b1) := by
    simpa [l] using routedList_getLast?_eq listA runs hAlast hrun_ne hrun_last
  have hl_ne : l ≠ [] := by
    intro hnil
    rw [hnil] at hl_head
    simp at hl_head
  have hl_chain : l.IsChain (A □ B).Adj := by
    simpa [l] using routedList_isChain (A := A) (B := B) listA runs hAc hrun_chain hrun_ne hmatch
  let p₀ : (A □ B).Walk (l.head hl_ne) (l.getLast hl_ne) :=
    SimpleGraph.Walk.ofSupport l hl_ne hl_chain
  have hstart : l.head hl_ne = (a0, b0) := by
    have hsome : some (l.head hl_ne) = some (a0, b0) :=
      (head?_eq_head_of_ne_nil hl_ne).symm.trans hl_head
    exact Option.some.inj hsome
  have hend : l.getLast hl_ne = (a1, b1) := by
    have hsome : some (l.getLast hl_ne) = some (a1, b1) :=
      (List.getLast?_eq_getLast_of_ne_nil hl_ne).symm.trans hl_last
    exact Option.some.inj hsome
  let p : (A □ B).Walk (a0, b0) (a1, b1) := p₀.copy hstart hend
  refine ⟨p, ?_⟩
  have hp₀_support : p₀.support = l := by simp [p₀]
  have hp₀_path : p₀.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hp₀_support]
    exact routedList_nodup listA runs hAnd hrun_nodup)
  have hp₀_ham : p₀.IsHamiltonian := hp₀_path.isHamiltonian_of_mem (fun x => by
    rw [hp₀_support]
    exact routedList_cover listA runs hAcov hrun_cover x)
  intro x
  simpa [p, SimpleGraph.Walk.support_copy] using hp₀_ham x

private theorem boxProd_hamPath_of_A_hamPath
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hAcard : 3 ≤ Fintype.card WA) (hBcard : 3 ≤ Fintype.card WB)
    (hB : IsHamConnected B) {a0 a1 : WA} {b0 b1 : WB}
    (pA : A.Walk a0 a1) (hpA : pA.IsHamiltonian) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  let listA : List WA := pA.support
  have hAc : listA.IsChain A.Adj := by
    simpa [listA] using pA.isChain_adj_support
  have hAnd : listA.Nodup := by
    simpa [listA] using hpA.isPath.support_nodup
  have hAcov : ∀ a : WA, a ∈ listA := by
    intro a
    simpa [listA] using hpA.mem_support a
  have hAhead : listA.head? = some a0 := by
    simpa [listA] using walk_support_head? pA
  have hAlast : listA.getLast? = some a1 := by
    simpa [listA] using walk_support_getLast? pA
  have hAlen : listA.length = Fintype.card WA := by
    simpa [listA] using hpA.length_support
  have hncols : 2 ≤ listA.length := by
    rw [hAlen]
    omega
  rcases endpoint_chain_exists_of_card_three hBcard listA.length hncols b0 b1 with
    ⟨ends, hends_len, hends_head, hends_last, hends_chain⟩
  have hends_adj : ∀ i, (hi : i + 1 < ends.length) → ends[i] ≠ ends[i + 1] := by
    exact (List.isChain_iff_getElem.mp hends_chain)
  have hends0 : ends[0] = b0 := by
    have h0 : 0 < ends.length := by
      rw [hends_len]
      omega
    have h := hends_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at h
    exact Option.some.inj h
  have hendsLast : ends[listA.length] = b1 := by
    have hpos : 0 < ends.length := by
      rw [hends_len]
      omega
    have hidx : ends.length - 1 < ends.length := Nat.sub_lt hpos Nat.zero_lt_one
    have hget : ends[ends.length - 1] = b1 := by
      have h := hends_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx] at h
      exact Option.some.inj h
    have hidx_eq : ends.length - 1 = listA.length := by
      rw [hends_len]
      omega
    simpa [hidx_eq] using hget
  let runs : ℕ → List WB := fun i =>
    if hi : i + 1 < ends.length then
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hi))).support
    else [b0]
  have hrun_chain : ∀ i, i < listA.length → (runs i).IsChain B.Adj := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    simpa [runs, hlt] using
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).isChain_adj_support
  have hrun_nodup : ∀ i, i < listA.length → (runs i).Nodup := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hp : (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).IsHamiltonian :=
      Classical.choose_spec (hB ends[i] ends[i + 1] (hends_adj i hlt))
    simpa [runs, hlt] using hp.isPath.support_nodup
  have hrun_cover : ∀ i, i < listA.length → ∀ b, b ∈ runs i := by
    intro i hi b
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hp : (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).IsHamiltonian :=
      Classical.choose_spec (hB ends[i] ends[i + 1] (hends_adj i hlt))
    simpa [runs, hlt] using hp.mem_support b
  have hrun_ne : ∀ i, i < listA.length → runs i ≠ [] := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    simpa [runs, hlt] using
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).support_ne_nil
  have hrun_head0 : (runs 0).head? = some b0 := by
    have hlt : 0 + 1 < ends.length := by
      rw [hends_len]
      omega
    have hphead := walk_support_head?
      (Classical.choose (hB ends[0] ends[0 + 1] (hends_adj 0 hlt)))
    simpa [runs, hlt, hends0] using hphead
  have hrun_last : (runs (listA.length - 1)).getLast? = some b1 := by
    have hlt : (listA.length - 1) + 1 < ends.length := by
      rw [hends_len]
      omega
    have hend : ends[(listA.length - 1) + 1] = b1 := by
      have hidx : (listA.length - 1) + 1 = listA.length := by omega
      simpa [hidx] using hendsLast
    have hplast := walk_support_getLast?
      (Classical.choose
        (hB ends[listA.length - 1] ends[(listA.length - 1) + 1]
          (hends_adj (listA.length - 1) hlt)))
    simpa [runs, hlt, hend] using hplast
  have hmatch : ∀ i, i + 1 < listA.length → (runs i).getLast? = (runs (i + 1)).head? := by
    intro i hi
    have hlt_i : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hlt_next : (i + 1) + 1 < ends.length := by
      rw [hends_len]
      omega
    have hlast_i := walk_support_getLast?
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt_i)))
    have hhead_next := walk_support_head?
      (Classical.choose (hB ends[i + 1] ends[(i + 1) + 1] (hends_adj (i + 1) hlt_next)))
    simp [runs, hlt_i, hlt_next, hlast_i, hhead_next]
  exact boxProd_routed_hamPath (A := A) (B := B) listA runs a0 a1 b0 b1
    hAc hAnd hAcov hAhead hAlast hrun_chain hrun_nodup hrun_cover hrun_ne
    hrun_head0 hrun_last hmatch

private theorem boxProd_hamPath_of_A_hamPath_card_two
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hAcard : 2 ≤ Fintype.card WA) (hBcard : 3 ≤ Fintype.card WB)
    (hB : IsHamConnected B) {a0 a1 : WA} {b0 b1 : WB}
    (pA : A.Walk a0 a1) (hpA : pA.IsHamiltonian) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  let listA : List WA := pA.support
  have hAc : listA.IsChain A.Adj := by
    simpa [listA] using pA.isChain_adj_support
  have hAnd : listA.Nodup := by
    simpa [listA] using hpA.isPath.support_nodup
  have hAcov : ∀ a : WA, a ∈ listA := by
    intro a
    simpa [listA] using hpA.mem_support a
  have hAhead : listA.head? = some a0 := by
    simpa [listA] using walk_support_head? pA
  have hAlast : listA.getLast? = some a1 := by
    simpa [listA] using walk_support_getLast? pA
  have hAlen : listA.length = Fintype.card WA := by
    simpa [listA] using hpA.length_support
  have hncols : 2 ≤ listA.length := by
    rw [hAlen]
    omega
  rcases endpoint_chain_exists_of_card_three hBcard listA.length hncols b0 b1 with
    ⟨ends, hends_len, hends_head, hends_last, hends_chain⟩
  have hends_adj : ∀ i, (hi : i + 1 < ends.length) → ends[i] ≠ ends[i + 1] := by
    exact (List.isChain_iff_getElem.mp hends_chain)
  have hends0 : ends[0] = b0 := by
    have h0 : 0 < ends.length := by
      rw [hends_len]
      omega
    have h := hends_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at h
    exact Option.some.inj h
  have hendsLast : ends[listA.length] = b1 := by
    have hpos : 0 < ends.length := by
      rw [hends_len]
      omega
    have hidx : ends.length - 1 < ends.length := Nat.sub_lt hpos Nat.zero_lt_one
    have hget : ends[ends.length - 1] = b1 := by
      have h := hends_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx] at h
      exact Option.some.inj h
    have hidx_eq : ends.length - 1 = listA.length := by
      rw [hends_len]
      omega
    simpa [hidx_eq] using hget
  let runs : ℕ → List WB := fun i =>
    if hi : i + 1 < ends.length then
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hi))).support
    else [b0]
  have hrun_chain : ∀ i, i < listA.length → (runs i).IsChain B.Adj := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    simpa [runs, hlt] using
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).isChain_adj_support
  have hrun_nodup : ∀ i, i < listA.length → (runs i).Nodup := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hp : (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).IsHamiltonian :=
      Classical.choose_spec (hB ends[i] ends[i + 1] (hends_adj i hlt))
    simpa [runs, hlt] using hp.isPath.support_nodup
  have hrun_cover : ∀ i, i < listA.length → ∀ b, b ∈ runs i := by
    intro i hi b
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hp : (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).IsHamiltonian :=
      Classical.choose_spec (hB ends[i] ends[i + 1] (hends_adj i hlt))
    simpa [runs, hlt] using hp.mem_support b
  have hrun_ne : ∀ i, i < listA.length → runs i ≠ [] := by
    intro i hi
    have hlt : i + 1 < ends.length := by
      rw [hends_len]
      omega
    simpa [runs, hlt] using
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt))).support_ne_nil
  have hrun_head0 : (runs 0).head? = some b0 := by
    have hlt : 0 + 1 < ends.length := by
      rw [hends_len]
      omega
    have hphead := walk_support_head?
      (Classical.choose (hB ends[0] ends[0 + 1] (hends_adj 0 hlt)))
    simpa [runs, hlt, hends0] using hphead
  have hrun_last : (runs (listA.length - 1)).getLast? = some b1 := by
    have hlt : (listA.length - 1) + 1 < ends.length := by
      rw [hends_len]
      omega
    have hend : ends[(listA.length - 1) + 1] = b1 := by
      have hidx : (listA.length - 1) + 1 = listA.length := by omega
      simpa [hidx] using hendsLast
    have hplast := walk_support_getLast?
      (Classical.choose
        (hB ends[listA.length - 1] ends[(listA.length - 1) + 1]
          (hends_adj (listA.length - 1) hlt)))
    simpa [runs, hlt, hend] using hplast
  have hmatch : ∀ i, i + 1 < listA.length → (runs i).getLast? = (runs (i + 1)).head? := by
    intro i hi
    have hlt_i : i + 1 < ends.length := by
      rw [hends_len]
      omega
    have hlt_next : (i + 1) + 1 < ends.length := by
      rw [hends_len]
      omega
    have hlast_i := walk_support_getLast?
      (Classical.choose (hB ends[i] ends[i + 1] (hends_adj i hlt_i)))
    have hhead_next := walk_support_head?
      (Classical.choose (hB ends[i + 1] ends[(i + 1) + 1] (hends_adj (i + 1) hlt_next)))
    simp [runs, hlt_i, hlt_next, hlast_i, hhead_next]
  exact boxProd_routed_hamPath (A := A) (B := B) listA runs a0 a1 b0 b1
    hAc hAnd hAcov hAhead hAlast hrun_chain hrun_nodup hrun_cover hrun_ne
    hrun_head0 hrun_last hmatch

theorem boxProd_hamConn_both_nonbip_fst_ne
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hAcard : 3 ≤ Fintype.card WA) (hBcard : 3 ≤ Fintype.card WB)
    (hA : IsHamConnected A) (hB : IsHamConnected B)
    {a0 a1 : WA} {b0 b1 : WB} (ha : a0 ≠ a1) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  rcases hA a0 a1 ha with ⟨pA, hpA⟩
  exact boxProd_hamPath_of_A_hamPath (A := A) (B := B) hAcard hBcard hB pA hpA

theorem boxProd_hamConn_one_bip_color_ne
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hBnb : ¬ ∃ col, IsProper2Coloring B col)
    (hB : IsHamConnected B) {a0 a1 : WA} {b0 b1 : WB}
    (hcol : colA a0 ≠ colA a1) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  have hAcard : 2 ≤ Fintype.card WA := by
    have h := Fintype.card_le_of_surjective colA hAsurj
    simpa [Fintype.card_bool] using h
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  rcases hAlace a0 a1 hcol with ⟨pA, hpA⟩
  exact boxProd_hamPath_of_A_hamPath_card_two (A := A) (B := B) hAcard hBcard hB pA hpA

private theorem boxProd_prism_card_two_same_copy
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hcard : Fintype.card WA = 2)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    {a : WA} {b0 b1 : WB} (hb : b0 ≠ b1) :
    HasHamPath (A □ B) (a, b0) (a, b1) := by
  classical
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  rcases Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card WA) a with ⟨a', ha'⟩
  have hAedge : A.Adj a a' := adj_of_card_two_laceable (A := A) hcard hAsurj hAlace ha'.symm
  rcases hB b0 b1 hb with ⟨p, hp⟩
  have hp_len : p.length = Fintype.card WB - 1 := hp.length_eq
  have hp_len_gt_one : 1 < p.length := by
    rw [hp_len]
    omega
  let bNext : WB := p.getVert 1
  have hb0_bNext : B.Adj b0 bNext := by
    simpa [bNext] using p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
  have hb0_ne_bNext : b0 ≠ bNext := hb0_bNext.ne
  rcases hB b0 bNext hb0_ne_bNext with ⟨q, hq⟩
  let qList : List (WA × WB) := q.support.map fun b => (a', b)
  let pTail : List (WA × WB) := p.support.tail.map fun b => (a, b)
  let l : List (WA × WB) := ([(a, b0)] ++ qList) ++ pTail
  have htail_head : p.support.tail.head? = some bNext := by
    have hget := p.getVert_eq_support_getElem? (n := 1) (by omega : 1 ≤ p.length)
    simpa [bNext] using hget.symm
  have hb1_tail : b1 ∈ p.support.tail := by
    simpa using SimpleGraph.Walk.end_mem_tail_support_of_ne hb p
  have hp_tail_ne : p.support.tail ≠ [] := List.ne_nil_of_mem hb1_tail
  have htail_last : p.support.tail.getLast? = some b1 := by
    cases htail : p.support.tail with
    | nil => exact (hp_tail_ne htail).elim
    | cons c cs =>
        have hsupport : p.support = b0 :: c :: cs := by
          rw [← SimpleGraph.Walk.cons_tail_support p, htail]
        have hlast := walk_support_getLast? p
        rw [hsupport] at hlast
        simpa [htail] using hlast
  have htail_map :
      (p.support.map (fun b => (a, b))).tail =
        p.support.tail.map (fun b => (a, b)) := by
    cases p.support <;> rfl
  have hhead : l.head? = some (a, b0) := by
    simp [l]
  have hlast : l.getLast? = some (a, b1) := by
    have hb1_pTail : (a, b1) ∈ pTail := by
      unfold pTail
      exact List.mem_map.mpr ⟨b1, hb1_tail, rfl⟩
    have hpTail_ne : pTail ≠ [] := by
      exact List.ne_nil_of_mem hb1_pTail
    change ((([(a, b0)] ++ qList) ++ pTail).getLast? = some (a, b1))
    rw [List.getLast?_append_of_ne_nil _ hpTail_ne]
    have hlast_pTail : pTail.getLast? = some (a, b1) := by
      unfold pTail
      change (p.support.tail.map (fun b => (a, b))).getLast? = some (a, b1)
      rw [List.getLast?_map, htail_last]
      rfl
    exact hlast_pTail
  have hq_chain : qList.IsChain (A □ B).Adj := by
    change (q.support.map fun b => (a', b)).IsChain (A □ B).Adj
    rw [List.isChain_map]
    exact q.isChain_adj_support.imp (fun {x y} hxy => by
      rw [SimpleGraph.boxProd_adj]
      exact Or.inr ⟨hxy, rfl⟩)
  have hp_tail_chain : pTail.IsChain (A □ B).Adj := by
    change (p.support.tail.map fun b => (a, b)).IsChain (A □ B).Adj
    rw [List.isChain_map]
    exact p.isChain_adj_support.tail.imp (fun {x y} hxy => by
      rw [SimpleGraph.boxProd_adj]
      exact Or.inr ⟨hxy, rfl⟩)
  have hfirst_chain : ([(a, b0)] ++ qList).IsChain (A □ B).Adj := by
    exact (List.IsChain.singleton (R := (A □ B).Adj) (a, b0)).append hq_chain (by
      intro x hx y hy
      simp at hx
      subst x
      change y ∈ (q.support.map fun b => (a', b)).head? at hy
      rw [List.head?_map, walk_support_head? q] at hy
      simp at hy
      subst y
      rw [SimpleGraph.boxProd_adj]
      exact Or.inl ⟨hAedge, rfl⟩)
  have hchain : l.IsChain (A □ B).Adj := by
    exact hfirst_chain.append hp_tail_chain (by
      intro x hx y hy
      rw [List.getLast?_append_of_ne_nil] at hx
      · change x ∈ (q.support.map fun b => (a', b)).getLast? at hx
        change y ∈ (p.support.tail.map fun b => (a, b)).head? at hy
        rw [List.getLast?_map, walk_support_getLast? q] at hx
        rw [List.head?_map, htail_head] at hy
        simp at hx hy
        subst x
        subst y
        rw [SimpleGraph.boxProd_adj]
        exact Or.inl ⟨hAedge.symm, rfl⟩
      · unfold qList
        simpa [List.map_eq_nil_iff] using q.support_ne_nil)
  have hp_support_cons_nd : (b0 :: p.support.tail).Nodup := by
    simpa [SimpleGraph.Walk.cons_tail_support p] using hp.isPath.support_nodup
  have hb0_not_tail : b0 ∉ p.support.tail := (List.nodup_cons.mp hp_support_cons_nd).1
  have hq_nodup : qList.Nodup := by
    have hinj : Function.Injective (fun b : WB => (a', b)) := by
      intro x y hxy
      exact (Prod.mk.inj hxy).2
    exact List.Nodup.map hinj hq.isPath.support_nodup
  have hp_tail_nodup : pTail.Nodup := by
    have hinj : Function.Injective (fun b : WB => (a, b)) := by
      intro x y hxy
      exact (Prod.mk.inj hxy).2
    exact List.Nodup.map hinj hp.isPath.support_nodup.tail
  have hsingle_disj_q : List.Disjoint [(a, b0)] qList := by
    intro x hx hy
    simp at hx
    subst x
    change (a, b0) ∈ q.support.map (fun b => (a', b)) at hy
    rcases List.mem_map.mp hy with ⟨b, _hb, hpair⟩
    exact ha' (Prod.mk.inj hpair).1
  have hsingle_disj_tail : List.Disjoint [(a, b0)] pTail := by
    intro x hx hy
    simp at hx
    subst x
    change (a, b0) ∈ p.support.tail.map (fun b => (a, b)) at hy
    rcases List.mem_map.mp hy with ⟨b, hbmem, hpair⟩
    have hb_eq : b = b0 := (Prod.mk.inj hpair).2
    exact hb0_not_tail (by simpa [hb_eq] using hbmem)
  have hq_disj_tail : List.Disjoint qList pTail := by
    intro x hx hy
    change x ∈ q.support.map (fun b => (a', b)) at hx
    change x ∈ p.support.tail.map (fun b => (a, b)) at hy
    rcases List.mem_map.mp hx with ⟨b, _hb, hxb⟩
    rcases List.mem_map.mp hy with ⟨c, _hc, hxc⟩
    have hfirst : a' = a := (Prod.mk.inj (hxb.trans hxc.symm)).1
    exact ha' hfirst
  have hfirst_tail_disj : List.Disjoint ([(a, b0)] ++ qList) pTail := by
    intro x hx hy
    rcases List.mem_append.mp hx with hx | hx
    · exact hsingle_disj_tail hx hy
    · exact hq_disj_tail hx hy
  have hnodup : l.Nodup := by
    have hsingle_nd : [(a, b0)].Nodup := by simp
    have hfirst_nd : ([(a, b0)] ++ qList).Nodup :=
      hsingle_nd.append hq_nodup hsingle_disj_q
    exact hfirst_nd.append hp_tail_nodup hfirst_tail_disj
  have hcover : ∀ x : WA × WB, x ∈ l := by
    rintro ⟨aa, b⟩
    rcases mem_pair_of_card_two hcard ha'.symm (z := aa) with haa | haa
    · subst aa
      by_cases hb0eq : b = b0
      · subst b
        change (a, b0) ∈ ([(a, b0)] ++ qList) ++ pTail
        exact List.mem_append_left _ (by simp)
      · have hbmem : b ∈ p.support := hp.mem_support b
        have hbtail : b ∈ p.support.tail := by
          rcases (SimpleGraph.Walk.mem_support_iff p).mp hbmem with hbstart | htail
          · exact (hb0eq hbstart).elim
          · exact htail
        have hpMem : (a, b) ∈ pTail := by
          change (a, b) ∈ p.support.tail.map (fun b => (a, b))
          exact List.mem_map.mpr ⟨b, hbtail, rfl⟩
        change (a, b) ∈ ([(a, b0)] ++ qList) ++ pTail
        exact List.mem_append_right _ hpMem
    · subst aa
      have hbmem : b ∈ q.support := hq.mem_support b
      have hqMem : (a', b) ∈ qList := by
        change (a', b) ∈ q.support.map (fun b => (a', b))
        exact List.mem_map.mpr ⟨b, hbmem, rfl⟩
      change (a', b) ∈ ([(a, b0)] ++ qList) ++ pTail
      exact List.mem_append_left _ (List.mem_append_right _ hqMem)
  exact hasHamPath_of_list l hhead hlast hchain hnodup hcover

theorem boxProd_prism_card_two
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hcard : Fintype.card WA = 2)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B) :
    IsHamConnected (A □ B) := by
  classical
  rintro ⟨a0, b0⟩ ⟨a1, b1⟩ huv
  by_cases ha : a0 = a1
  · subst a1
    have hb : b0 ≠ b1 := by
      intro hb_eq
      exact huv (by simp [hb_eq])
    exact boxProd_prism_card_two_same_copy (A := A) (B := B) hcard hAsurj hAlace hBnb hB hb
  · have hcardBool : Fintype.card WA = Fintype.card Bool := by
      simpa [Fintype.card_bool] using hcard
    have hbij : Function.Bijective colA :=
      (Fintype.bijective_iff_surjective_and_card colA).2 ⟨hAsurj, hcardBool⟩
    have hcol : colA a0 ≠ colA a1 := hbij.injective.ne ha
    exact boxProd_hamConn_one_bip_color_ne (A := A) (B := B) hAsurj hAlace hBnb hB hcol

private def layeredColumn (walkB : List WB) (pieces : ℕ → List WA) (bi : WB × ℕ) :
    List (WA × WB) :=
  (pieces bi.2).map (fun a => (a, bi.1))

private def layeredList (walkB : List WB) (pieces : ℕ → List WA) : List (WA × WB) :=
  (walkB.zipIdx).flatMap (fun bi => layeredColumn walkB pieces bi)

private theorem mem_layeredColumn_snd
    (walkB : List WB) (pieces : ℕ → List WA) (bi : WB × ℕ) {x : WA × WB}
    (hx : x ∈ layeredColumn walkB pieces bi) :
    x.2 = bi.1 := by
  unfold layeredColumn at hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨a, _ha, rfl⟩
  rfl

private theorem mem_layeredColumn_fst
    (walkB : List WB) (pieces : ℕ → List WA) (bi : WB × ℕ) {x : WA × WB}
    (hx : x ∈ layeredColumn walkB pieces bi) :
    x.1 ∈ pieces bi.2 := by
  unfold layeredColumn at hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨a, ha, rfl⟩
  exact ha

private theorem layeredColumn_nodup [DecidableEq WA] [DecidableEq WB]
    (walkB : List WB) (pieces : ℕ → List WA) (bi : WB × ℕ)
    (hnd : (pieces bi.2).Nodup) :
    (layeredColumn walkB pieces bi).Nodup := by
  have hinj : Function.Injective (fun a : WA => (a, bi.1)) := by
    intro a c hac
    exact (Prod.mk.inj hac).1
  exact List.Nodup.map hinj hnd

private theorem layeredColumn_isChain
    (walkB : List WB) (pieces : ℕ → List WA) (bi : WB × ℕ)
    (hc : (pieces bi.2).IsChain A.Adj) :
    (layeredColumn (WA := WA) walkB pieces bi).IsChain (A □ B).Adj := by
  unfold layeredColumn
  rw [List.isChain_map]
  exact hc.imp (fun {x y} hxy => by
    rw [SimpleGraph.boxProd_adj]
    exact Or.inl ⟨hxy, rfl⟩)

private theorem layeredColumns_pairwise_disjoint [DecidableEq WA] [DecidableEq WB]
    (walkB : List WB) (pieces : ℕ → List WA)
    (hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2))) :
    (walkB.zipIdx).Pairwise (Function.onFun List.Disjoint (layeredColumn walkB pieces)) := by
  exact hdisj.imp (fun {bi bj} hbij => by
    intro x hx hy
    rcases hbij with hbne | hpdisj
    · exact hbne ((mem_layeredColumn_snd walkB pieces bi hx).symm.trans
        (mem_layeredColumn_snd walkB pieces bj hy))
    · exact hpdisj (mem_layeredColumn_fst walkB pieces bi hx)
        (mem_layeredColumn_fst walkB pieces bj hy))

private theorem layeredColumn_boundary_adj
    (walkB : List WB) (pieces : ℕ → List WA) {bi bj : WB × ℕ}
    (hB : B.Adj bi.1 bj.1)
    (hmatch : (pieces bi.2).getLast? = (pieces bj.2).head?) :
    listBoundaryAdj (A □ B).Adj
      (layeredColumn walkB pieces bi) (layeredColumn walkB pieces bj) := by
  unfold listBoundaryAdj layeredColumn
  intro x hx y hy
  rw [List.getLast?_map] at hx
  rw [List.head?_map] at hy
  cases hlast : (pieces bi.2).getLast? with
  | none => simp [hlast] at hx
  | some a =>
      cases hhead : (pieces bj.2).head? with
      | none => simp [hhead] at hy
      | some c =>
          simp [hlast] at hx
          simp [hhead] at hy
          subst x
          subst y
          have hac : a = c := by
            have hs : some a = some c := by simpa [hlast, hhead] using hmatch
            exact Option.some.inj hs
          subst c
          rw [SimpleGraph.boxProd_adj]
          exact Or.inr ⟨hB, rfl⟩

private theorem layeredColumns_no_nil
    (walkB : List WB) (pieces : ℕ → List WA)
    (hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ []) :
    [] ∉ (walkB.zipIdx).map (fun bi => layeredColumn walkB pieces bi) := by
  intro hnil
  rcases List.mem_map.mp hnil with ⟨bi, hbi, hcol⟩
  have hi : bi.2 < walkB.length := by
    simpa using (List.snd_lt_of_mem_zipIdx (l := walkB) (k := 0) hbi)
  unfold layeredColumn at hcol
  exact hpiece_ne bi.2 hi (List.map_eq_nil_iff.mp hcol)

private theorem layeredColumns_boundary_isChain
    (walkB : List WB) (pieces : ℕ → List WA)
    (hBc : walkB.IsChain B.Adj)
    (hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head?) :
    ((walkB.zipIdx).map (fun bi => layeredColumn walkB pieces bi)).IsChain
      (listBoundaryAdj (A □ B).Adj) := by
  rw [List.isChain_map]
  exact (zipIdx_isChain_adj_succ (A := B) walkB hBc).imp_of_mem_imp
    (fun bi bj hbi hbj hij => by
      have hjlt : bj.2 < walkB.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := walkB) (k := 0) hbj)
      have hi1 : bi.2 + 1 < walkB.length := by
        simpa [hij.2] using hjlt
      exact layeredColumn_boundary_adj (A := A) (B := B) walkB pieces hij.1 (by
        simpa [hij.2] using hmatch bi.2 hi1))

private theorem layeredList_isChain
    (walkB : List WB) (pieces : ℕ → List WA)
    (hBc : walkB.IsChain B.Adj)
    (hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj)
    (hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [])
    (hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head?) :
    (layeredList (WA := WA) (WB := WB) walkB pieces).IsChain (A □ B).Adj := by
  let cols : List (List (WA × WB)) :=
    (walkB.zipIdx).map (fun bi => layeredColumn walkB pieces bi)
  have hcols_ne : [] ∉ cols := by
    simpa [cols] using layeredColumns_no_nil walkB pieces hpiece_ne
  have hcols_chain : cols.IsChain (listBoundaryAdj (A □ B).Adj) := by
    simpa [cols] using
      layeredColumns_boundary_isChain (A := A) (B := B) walkB pieces hBc hmatch
  have hcols_internal : ∀ c ∈ cols, c.IsChain (A □ B).Adj := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨bi, hbi, rfl⟩
    have hi : bi.2 < walkB.length := by
      simpa using (List.snd_lt_of_mem_zipIdx (l := walkB) (k := 0) hbi)
    exact layeredColumn_isChain (A := A) (B := B) walkB pieces bi (hpiece_chain bi.2 hi)
  have hcols_boundary : cols.IsChain
      (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), (A □ B).Adj x y) := by
    change cols.IsChain (listBoundaryAdj (A □ B).Adj)
    exact hcols_chain
  have hflat : cols.flatten.IsChain (A □ B).Adj := by
    exact (List.isChain_flatten (R := (A □ B).Adj) hcols_ne).2
      ⟨hcols_internal, hcols_boundary⟩
  simpa [layeredList, cols, List.flatMap] using hflat

private theorem layeredList_nodup [DecidableEq WA] [DecidableEq WB]
    (walkB : List WB) (pieces : ℕ → List WA)
    (hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup)
    (hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2))) :
    (layeredList walkB pieces).Nodup := by
  rw [layeredList, List.nodup_flatMap]
  exact ⟨fun bi hbi => by
      have hi : bi.2 < walkB.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := walkB) (k := 0) hbi)
      exact layeredColumn_nodup walkB pieces bi (hpiece_nodup bi.2 hi),
    layeredColumns_pairwise_disjoint walkB pieces hdisj⟩

private theorem mem_layeredList_of_get
    (walkB : List WB) (pieces : ℕ → List WA) {i : ℕ}
    (hi : i < walkB.length) {a : WA} (ha : a ∈ pieces i) :
    (a, walkB[i]'hi) ∈ layeredList walkB pieces := by
  rw [layeredList, List.mem_flatMap]
  have hzip0 : (walkB[i]'hi, i) ∈ walkB.zipIdx := by
    have hmem : (walkB.zipIdx)[i]'(by simpa [List.length_zipIdx] using hi) ∈ walkB.zipIdx :=
      List.getElem_mem (l := walkB.zipIdx) (n := i) (by simpa [List.length_zipIdx] using hi)
    simpa [List.getElem_zipIdx] using hmem
  refine ⟨(walkB[i]'hi, i), hzip0, ?_⟩
  unfold layeredColumn
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

private theorem layeredList_cover
    (walkB : List WB) (pieces : ℕ → List WA)
    (hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i) :
    ∀ x : WA × WB, x ∈ layeredList walkB pieces := by
  rintro ⟨a, b⟩
  rcases hcover a b with ⟨i, hi, hib, ha⟩
  simpa [hib] using mem_layeredList_of_get walkB pieces hi ha

private theorem layeredList_head?_eq
    (walkB : List WB) (pieces : ℕ → List WA) {a : WA} {b : WB}
    (hBhead : walkB.head? = some b) (hpiece_head : (pieces 0).head? = some a) :
    (layeredList walkB pieces).head? = some (a, b) := by
  exact flatMap_head?_eq (walkB.zipIdx) (fun bi => layeredColumn walkB pieces bi)
    (zipIdx_head?_eq walkB hBhead) (by
      simp [layeredColumn, List.head?_map, hpiece_head])

private theorem layeredList_getLast?_eq
    (walkB : List WB) (pieces : ℕ → List WA) {a : WA} {b : WB}
    (hBlast : walkB.getLast? = some b)
    (hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [])
    (hpiece_last : (pieces (walkB.length - 1)).getLast? = some a) :
    (layeredList walkB pieces).getLast? = some (a, b) := by
  exact flatMap_getLast?_eq (walkB.zipIdx) (fun bi => layeredColumn walkB pieces bi)
    (zipIdx_getLast?_eq walkB hBlast)
    (fun bi hbi => by
      have hi : bi.2 < walkB.length := by
        simpa using (List.snd_lt_of_mem_zipIdx (l := walkB) (k := 0) hbi)
      unfold layeredColumn
      exact fun hmap => hpiece_ne bi.2 hi (List.map_eq_nil_iff.mp hmap))
    (by
      simp [layeredColumn, List.getLast?_map, hpiece_last])

theorem boxProd_layered_hamPath
    [DecidableEq WA] [DecidableEq WB]
    (walkB : List WB) (pieces : ℕ → List WA) (a0 a1 : WA) (b0 b1 : WB)
    (hBc : walkB.IsChain B.Adj)
    (hBhead : walkB.head? = some b0) (hBlast : walkB.getLast? = some b1)
    (hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj)
    (hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup)
    (hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [])
    (hpiece_head : (pieces 0).head? = some a0)
    (hpiece_last : (pieces (walkB.length - 1)).getLast? = some a1)
    (hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head?)
    (hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2)))
    (hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  let l : List (WA × WB) := layeredList walkB pieces
  have hl_head : l.head? = some (a0, b0) := by
    simpa [l] using layeredList_head?_eq walkB pieces hBhead hpiece_head
  have hl_last : l.getLast? = some (a1, b1) := by
    simpa [l] using layeredList_getLast?_eq walkB pieces hBlast hpiece_ne hpiece_last
  have hl_chain : l.IsChain (A □ B).Adj := by
    simpa [l] using
      layeredList_isChain (A := A) (B := B) walkB pieces hBc hpiece_chain hpiece_ne hmatch
  have hl_nodup : l.Nodup := by
    simpa [l] using layeredList_nodup walkB pieces hpiece_nodup hdisj
  have hl_cover : ∀ x : WA × WB, x ∈ l := by
    simpa [l] using layeredList_cover walkB pieces hcover
  exact hasHamPath_of_list l hl_head hl_last hl_chain hl_nodup hl_cover

private theorem boxProd_same_color_over_B_hamPath_even
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (a0 a1 : WA) {b0 b1 : WB} (pB : B.Walk b0 b1) (hpB : pB.IsHamiltonian)
    (hcol : colA a0 = colA a1) (hEven : Even pB.support.length) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  let walkB : List WB := pB.support
  let N : ℕ := walkB.length
  have hNpos : 0 < N := by
    simp [N, walkB]
  let c0 : Bool := colA a0
  rcases hAsurj (!c0) with ⟨aOpp, haOpp⟩
  have ha0_opp : colA a0 ≠ colA aOpp := by
    have hopp : colA aOpp = !colA a0 := by simpa [c0] using haOpp
    rw [hopp]
    cases h : colA a0 <;> simp [h]
  have hopp_a0 : colA aOpp ≠ colA a0 := ha0_opp.symm
  have hopp_a1 : colA aOpp ≠ colA a1 := by
    have hopp : colA aOpp = !colA a0 := by simpa [c0] using haOpp
    rw [hopp, ← hcol]
    cases h : colA a0 <;> simp [h]
  let boundary : ℕ → WA := fun i =>
    if i = N then a1 else if i % 2 = 0 then a0 else aOpp
  have hboundary0 : boundary 0 = a0 := by
    have h0N : 0 ≠ N := by omega
    simp [boundary, h0N]
  have hboundaryN : boundary N = a1 := by
    simp [boundary]
  have hboundary_col :
      ∀ i, i < N → colA (boundary i) ≠ colA (boundary (i + 1)) := by
    intro i hi
    have hi_ne_N : i ≠ N := by omega
    by_cases hlast : i + 1 = N
    · have hiodd : ¬ i % 2 = 0 := by
        intro hmod
        rcases hEven with ⟨k, hk⟩
        have hN_eq : N = k + k := by simpa [N, walkB] using hk
        have h2dvd_i : 2 ∣ i := (Nat.dvd_iff_mod_eq_zero).2 hmod
        rcases h2dvd_i with ⟨m, hm⟩
        omega
      simp [boundary, hi_ne_N, hlast, hiodd, hopp_a1]
    · have hsucc_ne_N : i + 1 ≠ N := hlast
      by_cases hpar : i % 2 = 0
      · have hsucc_odd : ¬ (i + 1) % 2 = 0 := by omega
        simp [boundary, hi_ne_N, hsucc_ne_N, hpar, hsucc_odd, ha0_opp]
      · have hsucc_even : (i + 1) % 2 = 0 := by omega
        simp [boundary, hi_ne_N, hsucc_ne_N, hpar, hsucc_even, hopp_a0]
  let piece : ∀ i : ℕ, i < N → A.Walk (boundary i) (boundary (i + 1)) :=
    fun i hi => Classical.choose (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  have hpiece_ham : ∀ i (hi : i < N), (piece i hi).IsHamiltonian := by
    intro i hi
    exact Classical.choose_spec
      (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  let pieces : ℕ → List WA := fun i =>
    if hi : i < N then (piece i hi).support else [a0]
  have hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    simpa [pieces, hiN] using (piece i hiN).isChain_adj_support
  have hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    simpa [pieces, hiN] using (hpiece_ham i hiN).isPath.support_nodup
  have hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [] := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    simpa [pieces, hiN] using (piece i hiN).support_ne_nil
  have hpiece_head : (pieces 0).head? = some a0 := by
    have h0N : 0 < N := hNpos
    have hhead := walk_support_head? (piece 0 h0N)
    simpa [pieces, h0N, hboundary0] using hhead
  have hpiece_last : (pieces (walkB.length - 1)).getLast? = some a1 := by
    have hlast_lt : walkB.length - 1 < N := by
      simp [N]
      omega
    have hidx : walkB.length - 1 + 1 = N := by
      simp [N]
      omega
    have hlast := walk_support_getLast? (piece (walkB.length - 1) hlast_lt)
    simpa [pieces, hlast_lt, hidx, hboundaryN] using hlast
  have hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head? := by
    intro i hi
    have hiN : i < N := by
      simp [N] at hi ⊢
      omega
    have hnextN : i + 1 < N := by simpa [N] using hi
    have hlast := walk_support_getLast? (piece i hiN)
    have hhead := walk_support_head? (piece (i + 1) hnextN)
    simpa [pieces, hiN, hnextN] using hlast.trans hhead.symm
  have hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2)) := by
    have hBnd : walkB.Nodup := by
      simpa [walkB] using hpB.isPath.support_nodup
    exact (zipIdx_pairwise_fst_ne_of_nodup walkB hBnd).imp (fun {bi bj} hne => Or.inl hne)
  have hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i := by
    intro a b
    have hbmem : b ∈ walkB := by
      simpa [walkB] using hpB.mem_support b
    rcases List.getElem_of_mem hbmem with ⟨i, hi, hib⟩
    refine ⟨i, hi, hib, ?_⟩
    have hiN : i < N := by simpa [N] using hi
    simpa [pieces, hiN] using (hpiece_ham i hiN).mem_support a
  exact boxProd_layered_hamPath (A := A) (B := B) walkB pieces a0 a1 b0 b1
    (by simpa [walkB] using pB.isChain_adj_support)
    (by simpa [walkB] using walk_support_head? pB)
    (by simpa [walkB] using walk_support_getLast? pB)
    hpiece_chain hpiece_nodup hpiece_ne hpiece_head hpiece_last hmatch hdisj hcover

theorem exists_same_color_ne_of_card_ge_four
    [Fintype WA] [DecidableEq WA]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (hAcard_ge_four : 4 ≤ Fintype.card WA) (a : WA) :
    ∃ a' : WA, a' ≠ a ∧ colA a' = colA a := by
  classical
  rcases hAsurj (!colA a) with ⟨b, hb⟩
  have hab_col : colA a ≠ colA b := by
    rw [hb]
    cases h : colA a <;> simp [h]
  rcases hAlace a b hab_col with ⟨p, hp⟩
  have hlen_ge : 2 ≤ p.length := by
    rw [hp.length_eq]
    omega
  refine ⟨p.getVert 2, ?_, ?_⟩
  · intro hsame
    have hget : p.getVert 2 = p.getVert 0 := by
      simpa [hsame] using (show p.getVert 2 = a from hsame)
    have hidx := hp.isPath.getVert_injOn
      (by rw [Set.mem_setOf_eq]; exact hlen_ge)
      (by rw [Set.mem_setOf_eq]; omega)
      hget
    omega
  · have htake_len : (p.take 2).length = 2 := by
      rw [SimpleGraph.Walk.take_length]
      omega
    have htake_even : Even (p.take 2).length := by
      rw [htake_len]
      exact even_two
    have hcol := (walk_even_length_iff_color_eq (A := A) hAbip (p.take 2)).mp htake_even
    simpa [SimpleGraph.Walk.take_getVert] using hcol.symm

theorem exists_adj_ne_of_hamConnected
    [Fintype WB] [DecidableEq WB]
    (hBcard : 3 ≤ Fintype.card WB) (hB : IsHamConnected B)
    (v avoid : WB) : ∃ w : WB, B.Adj v w ∧ w ≠ avoid := by
  classical
  have hone_lt : 1 < Fintype.card WB := by omega
  rcases Fintype.exists_ne_of_one_lt_card hone_lt v with ⟨x, hxv⟩
  have hEN : 3 ≤ ENat.card WB := by
    simpa [ENat.card, Nat.card_eq_fintype_card] using hBcard
  rcases ENat.exists_ne_ne_of_three_le hEN v x with ⟨y, hyv, hyx⟩
  have hxy : x ≠ y := by exact hyx.symm
  rcases hB x y hxy with ⟨p, hp⟩
  have hv_mem : v ∈ p.support := hp.mem_support v
  let k : ℕ := p.support.idxOf v
  have hk_support : p.getVert k = v := by
    simpa [k] using p.getVert_support_idxOf hv_mem
  have hk_lt_support : k < p.support.length := by
    simpa [k] using List.idxOf_lt_length_of_mem hv_mem
  have hk_le_len : k ≤ p.length := by
    rw [p.length_support] at hk_lt_support
    omega
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hvx : v = x := by
      have h0 : p.getVert 0 = x := by simp
      simpa [hk0, h0] using hk_support.symm
    exact hxv hvx.symm
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  have hk_ne_len : k ≠ p.length := by
    intro hklen
    have hvy : v = y := by
      have hlast : p.getVert p.length = y := SimpleGraph.Walk.getVert_length p
      simpa [hklen, hlast] using hk_support.symm
    exact hyv hvy.symm
  have hk_lt_len : k < p.length := lt_of_le_of_ne hk_le_len hk_ne_len
  let wPrev : WB := p.getVert (k - 1)
  let wNext : WB := p.getVert (k + 1)
  have hprev_adj : B.Adj v wPrev := by
    have hadj := p.adj_getVert_succ (i := k - 1) (by omega : k - 1 < p.length)
    have hsucc : k - 1 + 1 = k := by omega
    simpa [wPrev, hsucc, hk_support] using hadj.symm
  have hnext_adj : B.Adj v wNext := by
    have hadj := p.adj_getVert_succ (i := k) hk_lt_len
    simpa [wNext, hk_support] using hadj
  have hprev_ne_next : wPrev ≠ wNext := by
    intro hsame
    have hidx := hp.isPath.getVert_injOn
      (by omega : k - 1 ≤ p.length)
      (by omega : k + 1 ≤ p.length)
      (by simpa [wPrev, wNext] using hsame)
    omega
  by_cases hprev : wPrev = avoid
  · refine ⟨wNext, hnext_adj, ?_⟩
    intro hnext
    exact hprev_ne_next (hprev.trans hnext.symm)
  · exact ⟨wPrev, hprev_adj, hprev⟩

private theorem boxProd_absorber_doubled_layer_open_odd
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    (a0 a1 : WA) {b0 b1 : WB} (hb : b0 ≠ b1)
    (hcol : colA a0 = colA a1) (hAcard_ge_four : 4 ≤ Fintype.card WA)
    (hBodd : ¬ Even (Fintype.card WB)) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  rcases exists_same_color_ne_of_card_ge_four (A := A) hAbip hAsurj hAlace hAcard_ge_four a1 with
    ⟨aSame, haSame_ne_a1, haSame_col_a1⟩
  let c0 : Bool := colA a0
  rcases hAsurj (!c0) with ⟨o0, ho0⟩
  rcases exists_same_color_ne_of_card_ge_four (A := A) hAbip hAsurj hAlace hAcard_ge_four o0 with
    ⟨o1, ho1_ne_o0, ho1_col_o0⟩
  have haSame_col_a0 : colA aSame = colA a0 := haSame_col_a1.trans hcol.symm
  have ho0_opp_a0 : colA o0 ≠ colA a0 := by
    have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
    rw [ho0c]
    cases h : colA a0 <;> simp [h]
  have ho1_opp_a0 : colA o1 ≠ colA a0 := by
    rw [ho1_col_o0]
    exact ho0_opp_a0
  have haSame_ne_o0 : aSame ≠ o0 := by
    intro h
    exact ho0_opp_a0 (by rw [← h, haSame_col_a0])
  have haSame_ne_o1 : aSame ≠ o1 := by
    intro h
    exact ho1_opp_a0 (by rw [← h, haSame_col_a0])
  have ho0_ne_a1 : o0 ≠ a1 := by
    intro h
    exact ho0_opp_a0 (by rw [h, ← hcol])
  have ho1_ne_a1 : o1 ≠ a1 := by
    intro h
    exact ho1_opp_a0 (by rw [h, ← hcol])
  rcases exists_adj_ne_of_hamConnected (B := B) hBcard hB b1 b0 with ⟨w, hwb1, hwb0⟩
  have hbw : b0 ≠ w := hwb0.symm
  have hwb1_ne : w ≠ b1 := hwb1.ne.symm
  rcases hB b0 w hbw with ⟨pB, hpB⟩
  let base : List WB := pB.support
  let r : ℕ := base.idxOf b1
  let walkB : List WB := base ++ [b1]
  let N : ℕ := walkB.length
  have hb1_mem_base : b1 ∈ base := by
    simpa [base] using hpB.mem_support b1
  have hbase_nodup : base.Nodup := by
    simpa [base] using hpB.isPath.support_nodup
  have hbase_len : base.length = Fintype.card WB := by
    simpa [base] using hpB.length_support
  have hN_eq : N = Fintype.card WB + 1 := by
    simp [N, walkB, base, hbase_len]
  have hN_even : Even N := by
    have hodd : Odd (Fintype.card WB) := Nat.not_even_iff_odd.mp hBodd
    rcases hodd with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  have hN_pos : 0 < N := by
    rw [hN_eq]
    omega
  have hN_ge_four : 4 ≤ N := by
    rw [hN_eq]
    omega
  have hr_lt_base : r < base.length := by
    simpa [r] using List.idxOf_lt_length_of_mem hb1_mem_base
  have hbase_r : base[r] = b1 := by
    simpa [r] using List.getElem_idxOf (l := base) (x := b1) hr_lt_base
  have hbase_r_get? : base[r]? = some b1 := by
    rw [List.getElem?_eq_getElem hr_lt_base]
    exact congrArg some hbase_r
  have hbase_last : base.getLast? = some w := by
    simpa [base] using walk_support_getLast? pB
  have hbase_last_get : base[base.length - 1]'(by
      have hpos : 0 < base.length := by
        rw [hbase_len]
        omega
      exact Nat.sub_lt hpos Nat.zero_lt_one) = w := by
    have hpos : 0 < base.length := by
      rw [hbase_len]
      omega
    have hidx : base.length - 1 < base.length := Nat.sub_lt hpos Nat.zero_lt_one
    have h := hbase_last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx] at h
    exact Option.some.inj h
  have hbase_last_get? : base[base.length - 1]? = some w := by
    have hpos : 0 < base.length := by
      rw [hbase_len]
      omega
    have hidx : base.length - 1 < base.length := Nat.sub_lt hpos Nat.zero_lt_one
    rw [List.getElem?_eq_getElem hidx]
    exact congrArg some hbase_last_get
  have hr_ne_last : r ≠ base.length - 1 := by
    intro hr_last
    have : b1 = w := by
      have h₁ := hbase_r_get?
      rw [hr_last] at h₁
      exact Option.some.inj (h₁.symm.trans hbase_last_get?)
    exact hwb1_ne this.symm
  have hr_succ_lt_base : r + 1 < base.length := by
    omega
  have hr_pos : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    have hhead : base.head? = some b0 := by
      simpa [base] using walk_support_head? pB
    have hbase0 : base[0]'(by omega) = b0 := by
      have h := hhead
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < base.length)] at h
      exact Option.some.inj h
    have hbase0_get? : base[0]? = some b0 := by
      rw [List.getElem?_eq_getElem (by omega : 0 < base.length)]
      exact congrArg some hbase0
    have hb10 : b1 = b0 := by
      have h₁ := hbase_r_get?
      rw [hr0] at h₁
      exact Option.some.inj (h₁.symm.trans hbase0_get?)
    exact hb hb10.symm
  have hr_lt_N : r < N := by
    simp [N, walkB]
    omega
  have hr_succ_lt_N : r + 1 < N := by
    simp [N, walkB]
    omega
  have hs_lt_N : N - 1 < N := Nat.sub_lt hN_pos Nat.zero_lt_one
  have hs_eq_base_len : N - 1 = base.length := by
    simp [N, walkB]
  have hr_ne_s : r ≠ N - 1 := by
    rw [hs_eq_base_len]
    omega
  have hr_succ_ne_s : r + 1 ≠ N - 1 := by
    rw [hs_eq_base_len]
    omega
  let boundary : ℕ → WA := fun i =>
    if i = N then a1
    else if i = N - 1 then o0
    else if i = r then (if r % 2 = 0 then aSame else o1)
    else if i = r + 1 then (if r % 2 = 0 then o1 else aSame)
    else if i % 2 = 0 then a0 else o0
  have hboundary0 : boundary 0 = a0 := by
    have h0N : 0 ≠ N := by omega
    have h0s : 0 ≠ N - 1 := by omega
    have h0r : 0 ≠ r := by omega
    have h0r1 : 0 ≠ r + 1 := by omega
    simp [boundary, h0N, h0s, h0r, h0r1]
  have hboundaryN : boundary N = a1 := by
    simp [boundary]
  have hboundary_s : boundary (N - 1) = o0 := by
    have hsN : N - 1 ≠ N := by omega
    simp [boundary, hsN]
  have hboundary_succ_s : boundary ((N - 1) + 1) = a1 := by
    have hsN : N - 1 + 1 = N := by omega
    simp [hsN, boundary]
  have hboundary_r :
      boundary r = (if r % 2 = 0 then aSame else o1) := by
    have hrN : r ≠ N := by omega
    have hrs : r ≠ N - 1 := hr_ne_s
    simp [boundary, hrN, hrs]
  have hboundary_r1 :
      boundary (r + 1) = (if r % 2 = 0 then o1 else aSame) := by
    have hr1N : r + 1 ≠ N := by omega
    have hr1s : r + 1 ≠ N - 1 := hr_succ_ne_s
    have hr1r : r + 1 ≠ r := by omega
    simp [boundary, hr1N, hr1s, hr1r]
  have hboundary_color : ∀ i, i ≤ N →
      colA (boundary i) = if i % 2 = 0 then colA a0 else !colA a0 := by
    intro i hi
    by_cases hiN : i = N
    · subst i
      have hNeven : N % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 (by
        rcases hN_even with ⟨k, hk⟩
        exact ⟨k, by omega⟩)
      simp [boundary, hNeven, hcol]
    · by_cases his : i = N - 1
      · subst i
        have hsodd : ¬ (N - 1) % 2 = 0 := by
          intro hsmod
          rcases hN_even with ⟨k, hk⟩
          omega
        have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
        simp [boundary, hiN, hsodd, ho0c]
      · by_cases hir : i = r
        · subst i
          by_cases hrpar : r % 2 = 0
          · simp [boundary, hiN, his, hrpar, haSame_col_a0]
          · have ho1c : colA o1 = !colA a0 := by
              have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
              rw [ho1_col_o0, ho0c]
            simp [boundary, hiN, his, hrpar, ho1c]
        · by_cases hir1 : i = r + 1
          · subst i
            by_cases hrpar : r % 2 = 0
            · have hsucc_odd : ¬ (r + 1) % 2 = 0 := by omega
              have ho1c : colA o1 = !colA a0 := by
                have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
                rw [ho1_col_o0, ho0c]
              simp [boundary, hiN, his, hir, hrpar, hsucc_odd, ho1c]
            · have hsucc_even : (r + 1) % 2 = 0 := by omega
              simp [boundary, hiN, his, hir, hrpar, hsucc_even, haSame_col_a0]
          · by_cases hipar : i % 2 = 0
            · simp [boundary, hiN, his, hir, hir1, hipar]
            · have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
              simp [boundary, hiN, his, hir, hir1, hipar, ho0c]
  have hboundary_col : ∀ i, i < N → colA (boundary i) ≠ colA (boundary (i + 1)) := by
    intro i hi
    have hci := hboundary_color i (by omega)
    have hcj := hboundary_color (i + 1) (by omega)
    rw [hci, hcj]
    by_cases hipar : i % 2 = 0
    · have hsucc_odd : ¬ (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_odd]
    · have hsucc_even : (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_even]
  have hD_col₁ : colA (boundary r) ≠ colA (boundary (r + 1)) :=
    hboundary_col r (by omega)
  have hD_col₂ : colA (boundary (N - 1)) ≠ colA (boundary ((N - 1) + 1)) :=
    hboundary_col (N - 1) hs_lt_N
  have hD_ne₁ : boundary r ≠ boundary (N - 1) := by
    rw [hboundary_s, hboundary_r]
    by_cases hrpar : r % 2 = 0
    · simp [hrpar, haSame_ne_o0]
    · simpa [hrpar] using ho1_ne_o0
  have hD_ne₂ : boundary r ≠ boundary ((N - 1) + 1) := by
    rw [hboundary_succ_s, hboundary_r]
    by_cases hrpar : r % 2 = 0
    · simp [hrpar, haSame_ne_a1]
    · simpa [hrpar] using ho1_ne_a1
  have hD_ne₃ : boundary (r + 1) ≠ boundary (N - 1) := by
    rw [hboundary_s, hboundary_r1]
    by_cases hrpar : r % 2 = 0
    · simp [hrpar, ho1_ne_o0]
    · simpa [hrpar] using haSame_ne_o0
  have hD_ne₄ : boundary (r + 1) ≠ boundary ((N - 1) + 1) := by
    rw [hboundary_succ_s, hboundary_r1]
    by_cases hrpar : r % 2 = 0
    · simp [hrpar, ho1_ne_a1]
    · simpa [hrpar] using haSame_ne_a1
  have hD_ne₅ : boundary r ≠ boundary (r + 1) := by
    exact fun h => hD_col₁ (congrArg colA h)
  have hD_ne₆ : boundary (N - 1) ≠ boundary ((N - 1) + 1) := by
    exact fun h => hD_col₂ (congrArg colA h)
  rcases hAspan (boundary r) (boundary (r + 1))
      (boundary (N - 1)) (boundary ((N - 1) + 1))
      hD_col₁ hD_col₂ hD_ne₁ hD_ne₂ hD_ne₃ hD_ne₄ hD_ne₅ hD_ne₆ with
    ⟨pD, qD, hpD_path, hqD_path, hD_cover, hD_disj⟩
  let single : ∀ i : ℕ, i < N → i ≠ r → i ≠ N - 1 →
      A.Walk (boundary i) (boundary (i + 1)) :=
    fun i hi hir his => Classical.choose (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  have hsingle_ham : ∀ i (hi : i < N) (hir : i ≠ r) (his : i ≠ N - 1),
      (single i hi hir his).IsHamiltonian := by
    intro i hi hir his
    exact Classical.choose_spec (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  let pieces : ℕ → List WA := fun i =>
    if hir : i = r then pD.support
    else if his : i = N - 1 then qD.support
    else if hi : i < N then (single i hi hir his).support
    else [a0]
  have hpieces_head : ∀ i, i < N → (pieces i).head? = some (boundary i) := by
    intro i hi
    by_cases hir : i = r
    · simpa [pieces, hir] using walk_support_head? pD
    · by_cases his : i = N - 1
      · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hir, his, hsr] using walk_support_head? qD
      · simpa [pieces, hir, his, hi] using walk_support_head? (single i hi hir his)
  have hpieces_last : ∀ i, i < N → (pieces i).getLast? = some (boundary (i + 1)) := by
    intro i hi
    by_cases hir : i = r
    · simpa [pieces, hir] using walk_support_getLast? pD
    · by_cases his : i = N - 1
      · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hir, his, hsr] using walk_support_getLast? qD
      · simpa [pieces, hir, his, hi] using walk_support_getLast? (single i hi hir his)
  have hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hir : i = r
    · simpa [pieces, hir] using pD.isChain_adj_support
    · by_cases his : i = N - 1
      · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hir, his, hsr] using qD.isChain_adj_support
      · simpa [pieces, hir, his, hiN] using (single i hiN hir his).isChain_adj_support
  have hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hir : i = r
    · simpa [pieces, hir] using hpD_path.support_nodup
    · by_cases his : i = N - 1
      · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hir, his, hsr] using hqD_path.support_nodup
      · simpa [pieces, hir, his, hiN] using (hsingle_ham i hiN hir his).isPath.support_nodup
  have hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [] := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hir : i = r
    · simpa [pieces, hir] using pD.support_ne_nil
    · by_cases his : i = N - 1
      · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hir, his, hsr] using qD.support_ne_nil
      · simpa [pieces, hir, his, hiN] using (single i hiN hir his).support_ne_nil
  have hpiece_head : (pieces 0).head? = some a0 := by
    have h0N : 0 < N := hN_pos
    have h := hpieces_head 0 h0N
    simpa [hboundary0] using h
  have hpiece_last : (pieces (walkB.length - 1)).getLast? = some a1 := by
    have hidx : walkB.length - 1 = N - 1 := by simp [N]
    have h := hpieces_last (N - 1) hs_lt_N
    simpa [hidx, hboundary_succ_s] using h
  have hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head? := by
    intro i hi
    have hiN : i < N := by
      omega
    have hnextN : i + 1 < N := by simpa [N] using hi
    rw [hpieces_last i hiN, hpieces_head (i + 1) hnextN]
  have hD_disjoint : List.Disjoint pD.support qD.support := by
    intro x hx hy
    exact hD_disj x ⟨hx, hy⟩
  have hwalk_get_r : walkB[r]'hr_lt_N = b1 := by
    have hrb : r < base.length := hr_lt_base
    simpa [walkB, List.getElem_append_left hrb] using hbase_r
  have hwalk_get_s : walkB[N - 1]'hs_lt_N = b1 := by
    have hsopt : walkB[N - 1]? = some b1 := by
      rw [hs_eq_base_len]
      simp [walkB]
    rw [List.getElem?_eq_getElem hs_lt_N] at hsopt
    exact Option.some.inj hsopt
  have hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_zipIdx] at hi hj
    simp only [List.getElem_zipIdx]
    by_cases hbij : walkB[i] = walkB[j]
    · right
      have hi_ne_s : i ≠ N - 1 := by omega
      by_cases hjs : j = N - 1
      · subst j
        have hi_base : i < base.length := by
          rw [← hs_eq_base_len]
          omega
        have hwi : walkB[i]'hi = b1 := by
          exact hbij.trans hwalk_get_s
        have hbase_i : base[i]'hi_base = b1 := by
          simpa [walkB, List.getElem_append_left hi_base] using hwi
        have hir : i = r := by
          have heq : base[i]'hi_base = base[r]'hr_lt_base := by
            simpa [hbase_r] using hbase_i
          exact (hbase_nodup.getElem_inj_iff).mp heq
        subst i
        have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
        simpa [pieces, hr_ne_s, hsr] using hD_disjoint
      · have hi_base : i < base.length := by
          rw [← hs_eq_base_len]
          omega
        have hj_base : j < base.length := by
          rw [← hs_eq_base_len]
          omega
        have hbase_eq : base[i]'hi_base = base[j]'hj_base := by
          simpa [walkB, List.getElem_append_left hi_base, List.getElem_append_left hj_base] using hbij
        have hij_eq : i = j := (hbase_nodup.getElem_inj_iff).mp hbase_eq
        omega
    · exact Or.inl hbij
  have hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i := by
    intro a b
    by_cases hb1 : b = b1
    · subst b
      rcases hD_cover a with ha | ha
      · refine ⟨r, by simpa [N] using hr_lt_N, ?_, ?_⟩
        · exact hwalk_get_r
        · simpa [pieces] using ha
      · refine ⟨N - 1, by simpa [N] using hs_lt_N, ?_, ?_⟩
        · exact hwalk_get_s
        · have hsr : N - 1 ≠ r := fun h => hr_ne_s h.symm
          simpa [pieces, hr_ne_s, hsr] using ha
    · have hbmem : b ∈ base := by
        simpa [base] using hpB.mem_support b
      rcases List.getElem_of_mem hbmem with ⟨i, hi, hib⟩
      have hiN : i < N := by
        simp [N, walkB]
        omega
      have hir : i ≠ r := by
        intro hir
        subst i
        exact hb1 (by simpa [hbase_r] using hib.symm)
      have his : i ≠ N - 1 := by
        rw [hs_eq_base_len]
        omega
      refine ⟨i, by simpa [N] using hiN, ?_, ?_⟩
      · simpa [walkB, List.getElem_append_left hi] using hib
      · simpa [pieces, hir, his, hiN] using (hsingle_ham i hiN hir his).mem_support a
  have hBc : walkB.IsChain B.Adj := by
    exact pB.isChain_adj_support.append (by simp) (by
      intro x hx y hy
      rw [hbase_last] at hx
      simp at hx hy
      subst x
      subst y
      exact hwb1.symm)
  have hBhead : walkB.head? = some b0 := by
    have hhead : base.head? = some b0 := by
      simpa [base] using walk_support_head? pB
    simpa [walkB, List.head?_append, hhead]
  have hBlast : walkB.getLast? = some b1 := by
    simp [walkB]
  exact boxProd_layered_hamPath (A := A) (B := B) walkB pieces a0 a1 b0 b1
    hBc hBhead hBlast hpiece_chain hpiece_nodup hpiece_ne hpiece_head hpiece_last
    hmatch hdisj hcover

private theorem boxProd_absorber_same_layer_odd
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 : WB) (ha : a0 ≠ a1)
    (hcol : colA a0 = colA a1) (hAcard_ge_four : 4 ≤ Fintype.card WA)
    (hBodd : ¬ Even (Fintype.card WB)) :
    HasHamPath (A □ B) (a0, b0) (a1, b0) := by
  classical
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  let c0 : Bool := colA a0
  rcases hAsurj (!c0) with ⟨o0, ho0⟩
  rcases exists_same_color_ne_of_card_ge_four (A := A) hAbip hAsurj hAlace hAcard_ge_four o0 with
    ⟨o1, ho1_ne_o0, ho1_col_o0⟩
  have ho0_opp_a0 : colA o0 ≠ colA a0 := by
    have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
    rw [ho0c]
    cases h : colA a0 <;> simp [h]
  have ho1_opp_a0 : colA o1 ≠ colA a0 := by
    rw [ho1_col_o0]
    exact ho0_opp_a0
  have ho0_ne_a0 : o0 ≠ a0 := fun h => ho0_opp_a0 (by rw [h])
  have ho1_ne_a0 : o1 ≠ a0 := fun h => ho1_opp_a0 (by rw [h])
  have ho0_ne_a1 : o0 ≠ a1 := by
    intro h
    exact ho0_opp_a0 (by rw [h, ← hcol])
  have ho1_ne_a1 : o1 ≠ a1 := by
    intro h
    exact ho1_opp_a0 (by rw [h, ← hcol])
  rcases exists_adj_ne_of_hamConnected (B := B) hBcard hB b0 b0 with ⟨m, hmb0, hmb0_ne⟩
  have hb0m : b0 ≠ m := hmb0_ne.symm
  rcases hB b0 m hb0m with ⟨pB, hpB⟩
  let base : List WB := pB.support
  let walkB : List WB := base ++ [b0]
  let N : ℕ := walkB.length
  have hbase_nodup : base.Nodup := by
    simpa [base] using hpB.isPath.support_nodup
  have hbase_len : base.length = Fintype.card WB := by
    simpa [base] using hpB.length_support
  have hN_eq : N = Fintype.card WB + 1 := by
    simp [N, walkB, base, hbase_len]
  have hN_even : Even N := by
    have hodd : Odd (Fintype.card WB) := Nat.not_even_iff_odd.mp hBodd
    rcases hodd with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  have hN_pos : 0 < N := by
    rw [hN_eq]
    omega
  have hN_ge_four : 4 ≤ N := by
    rw [hN_eq]
    omega
  have hs_lt_N : N - 1 < N := Nat.sub_lt hN_pos Nat.zero_lt_one
  have hs_eq_base_len : N - 1 = base.length := by
    simp [N, walkB]
  have hbase_head : base.head? = some b0 := by
    simpa [base] using walk_support_head? pB
  have hbase_last : base.getLast? = some m := by
    simpa [base] using walk_support_getLast? pB
  let boundary : ℕ → WA := fun i =>
    if i = N then a1
    else if i = N - 1 then o1
    else if i % 2 = 0 then a0 else o0
  have hboundary0 : boundary 0 = a0 := by
    have h0N : 0 ≠ N := by omega
    have h0s : 0 ≠ N - 1 := by omega
    simp [boundary, h0N, h0s]
  have hboundary1 : boundary 1 = o0 := by
    have h1N : 1 ≠ N := by omega
    have h1s : 1 ≠ N - 1 := by omega
    simp [boundary, h1N, h1s]
  have hboundaryN : boundary N = a1 := by
    simp [boundary]
  have hboundary_s : boundary (N - 1) = o1 := by
    have hsN : N - 1 ≠ N := by omega
    simp [boundary, hsN]
  have hboundary_succ_s : boundary ((N - 1) + 1) = a1 := by
    have hsN : N - 1 + 1 = N := by omega
    simp [hsN, boundary]
  have hboundary_color : ∀ i, i ≤ N →
      colA (boundary i) = if i % 2 = 0 then colA a0 else !colA a0 := by
    intro i hi
    by_cases hiN : i = N
    · subst i
      have hNeven : N % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 (by
        rcases hN_even with ⟨k, hk⟩
        exact ⟨k, by omega⟩)
      simp [boundary, hNeven, hcol]
    · by_cases his : i = N - 1
      · subst i
        have hsodd : ¬ (N - 1) % 2 = 0 := by
          intro hsmod
          rcases hN_even with ⟨k, hk⟩
          omega
        have ho1c : colA o1 = !colA a0 := by
          have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
          rw [ho1_col_o0, ho0c]
        simp [boundary, hiN, hsodd, ho1c]
      · by_cases hipar : i % 2 = 0
        · simp [boundary, hiN, his, hipar]
        · have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
          simp [boundary, hiN, his, hipar, ho0c]
  have hboundary_col : ∀ i, i < N → colA (boundary i) ≠ colA (boundary (i + 1)) := by
    intro i hi
    have hci := hboundary_color i (by omega)
    have hcj := hboundary_color (i + 1) (by omega)
    rw [hci, hcj]
    by_cases hipar : i % 2 = 0
    · have hsucc_odd : ¬ (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_odd]
    · have hsucc_even : (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_even]
  have hD_col₁ : colA (boundary 0) ≠ colA (boundary 1) := hboundary_col 0 (by omega)
  have hD_col₂ : colA (boundary (N - 1)) ≠ colA (boundary ((N - 1) + 1)) :=
    hboundary_col (N - 1) hs_lt_N
  have hD_ne₁ : boundary 0 ≠ boundary (N - 1) := by
    rw [hboundary0, hboundary_s]
    exact ho1_ne_a0.symm
  have hD_ne₂ : boundary 0 ≠ boundary ((N - 1) + 1) := by
    rw [hboundary0, hboundary_succ_s]
    exact ha
  have hD_ne₃ : boundary 1 ≠ boundary (N - 1) := by
    rw [hboundary1, hboundary_s]
    exact ho1_ne_o0.symm
  have hD_ne₄ : boundary 1 ≠ boundary ((N - 1) + 1) := by
    rw [hboundary1, hboundary_succ_s]
    exact ho0_ne_a1
  have hD_ne₅ : boundary 0 ≠ boundary 1 := fun h => hD_col₁ (congrArg colA h)
  have hD_ne₆ : boundary (N - 1) ≠ boundary ((N - 1) + 1) := fun h => hD_col₂ (congrArg colA h)
  rcases hAspan (boundary 0) (boundary 1)
      (boundary (N - 1)) (boundary ((N - 1) + 1))
      hD_col₁ hD_col₂ hD_ne₁ hD_ne₂ hD_ne₃ hD_ne₄ hD_ne₅ hD_ne₆ with
    ⟨pD, qD, hpD_path, hqD_path, hD_cover, hD_disj⟩
  let single : ∀ i : ℕ, i < N → i ≠ 0 → i ≠ N - 1 →
      A.Walk (boundary i) (boundary (i + 1)) :=
    fun i hi hi0 his => Classical.choose (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  have hsingle_ham : ∀ i (hi : i < N) (hi0 : i ≠ 0) (his : i ≠ N - 1),
      (single i hi hi0 his).IsHamiltonian := by
    intro i hi hi0 his
    exact Classical.choose_spec (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  let pieces : ℕ → List WA := fun i =>
    if hi0 : i = 0 then pD.support
    else if his : i = N - 1 then qD.support
    else if hi : i < N then (single i hi hi0 his).support
    else [a0]
  have hpieces_head : ∀ i, i < N → (pieces i).head? = some (boundary i) := by
    intro i hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using walk_support_head? pD
    · by_cases his : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his, hs0] using walk_support_head? qD
      · simpa [pieces, hi0, his, hi] using walk_support_head? (single i hi hi0 his)
  have hpieces_last : ∀ i, i < N → (pieces i).getLast? = some (boundary (i + 1)) := by
    intro i hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using walk_support_getLast? pD
    · by_cases his : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his, hs0] using walk_support_getLast? qD
      · simpa [pieces, hi0, his, hi] using walk_support_getLast? (single i hi hi0 his)
  have hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using pD.isChain_adj_support
    · by_cases his : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his, hs0] using qD.isChain_adj_support
      · simpa [pieces, hi0, his, hiN] using (single i hiN hi0 his).isChain_adj_support
  have hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using hpD_path.support_nodup
    · by_cases his : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his, hs0] using hqD_path.support_nodup
      · simpa [pieces, hi0, his, hiN] using (hsingle_ham i hiN hi0 his).isPath.support_nodup
  have hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [] := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using pD.support_ne_nil
    · by_cases his : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his, hs0] using qD.support_ne_nil
      · simpa [pieces, hi0, his, hiN] using (single i hiN hi0 his).support_ne_nil
  have hpiece_head : (pieces 0).head? = some a0 := by
    have h := hpieces_head 0 hN_pos
    simpa [hboundary0] using h
  have hpiece_last : (pieces (walkB.length - 1)).getLast? = some a1 := by
    have hidx : walkB.length - 1 = N - 1 := by simp [N]
    have h := hpieces_last (N - 1) hs_lt_N
    simpa [hidx, hboundary_succ_s] using h
  have hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head? := by
    intro i hi
    have hiN : i < N := by omega
    have hnextN : i + 1 < N := by simpa [N] using hi
    rw [hpieces_last i hiN, hpieces_head (i + 1) hnextN]
  have hD_disjoint : List.Disjoint pD.support qD.support := by
    intro x hx hy
    exact hD_disj x ⟨hx, hy⟩
  have hwalk_get_0 : walkB[0]'(by simpa [N] using hN_pos) = b0 := by
    have hbase0_lt : 0 < base.length := by
      rw [hbase_len]
      omega
    have hbase0_get : base[0]'hbase0_lt = b0 := by
      have h := hbase_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hbase0_lt] at h
      exact Option.some.inj h
    simpa [walkB, List.getElem_append_left hbase0_lt] using hbase0_get
  have hwalk_get_s : walkB[N - 1]'hs_lt_N = b0 := by
    have hsopt : walkB[N - 1]? = some b0 := by
      rw [hs_eq_base_len]
      simp [walkB]
    rw [List.getElem?_eq_getElem hs_lt_N] at hsopt
    exact Option.some.inj hsopt
  have hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_zipIdx] at hi hj
    simp only [List.getElem_zipIdx]
    by_cases hbij : walkB[i] = walkB[j]
    · right
      have hi_ne_s : i ≠ N - 1 := by omega
      by_cases hi0 : i = 0
      · subst i
        by_cases hjs : j = N - 1
        · subst j
          have hs0 : N - 1 ≠ 0 := by omega
          simpa [pieces, hs0] using hD_disjoint
        · have hj_base : j < base.length := by
            rw [← hs_eq_base_len]
            omega
          have hbj : base[j]'hj_base = b0 := by
            have hwj : walkB[j]'hj = b0 := by
              simpa [hwalk_get_0] using hbij.symm
            simpa [walkB, List.getElem_append_left hj_base] using hwj
          have hbase0_get : base[0]'(by
              rw [hbase_len]
              omega) = b0 := by
            have h := hbase_head
            rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
              rw [hbase_len]
              omega : 0 < base.length)] at h
            exact Option.some.inj h
          have hj0 : j = 0 := by
            have heq : base[j]'hj_base = base[0]'(by rw [hbase_len]; omega) := by
              simpa [hbase0_get] using hbj
            exact (hbase_nodup.getElem_inj_iff).mp heq
          omega
      · have hi_base : i < base.length := by
          rw [← hs_eq_base_len]
          omega
        have hj_base : j < base.length := by
          by_cases hjs : j = N - 1
          · subst j
            have hwi : walkB[i]'hi = b0 := hbij.trans hwalk_get_s
            have hbi : base[i]'hi_base = b0 := by
              simpa [walkB, List.getElem_append_left hi_base] using hwi
            have hbase0_get : base[0]'(by rw [hbase_len]; omega) = b0 := by
              have h := hbase_head
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
                rw [hbase_len]
                omega : 0 < base.length)] at h
              exact Option.some.inj h
            have hi_eq0 : i = 0 := by
              have heq : base[i]'hi_base = base[0]'(by rw [hbase_len]; omega) := by
                simpa [hbase0_get] using hbi
              exact (hbase_nodup.getElem_inj_iff).mp heq
            exact (hi0 hi_eq0).elim
          · rw [← hs_eq_base_len]
            omega
        have hbase_eq : base[i]'hi_base = base[j]'hj_base := by
          simpa [walkB, List.getElem_append_left hi_base, List.getElem_append_left hj_base] using hbij
        have hij_eq : i = j := (hbase_nodup.getElem_inj_iff).mp hbase_eq
        omega
    · exact Or.inl hbij
  have hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i := by
    intro a b
    by_cases hb0 : b = b0
    · subst b
      rcases hD_cover a with ha | ha
      · refine ⟨0, by simpa [N] using hN_pos, ?_, ?_⟩
        · exact hwalk_get_0
        · simpa [pieces] using ha
      · refine ⟨N - 1, by simpa [N] using hs_lt_N, ?_, ?_⟩
        · exact hwalk_get_s
        · have hs0 : N - 1 ≠ 0 := by omega
          simpa [pieces, hs0] using ha
    · have hbmem : b ∈ base := by
        simpa [base] using hpB.mem_support b
      rcases List.getElem_of_mem hbmem with ⟨i, hi, hib⟩
      have hiN : i < N := by
        simp [N, walkB]
        omega
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        have hbase0 : base[0]'hi = b0 := by
          have h := hbase_head
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at h
          exact Option.some.inj h
        exact hb0 (hib.symm.trans hbase0)
      have his : i ≠ N - 1 := by
        rw [hs_eq_base_len]
        omega
      refine ⟨i, by simpa [N] using hiN, ?_, ?_⟩
      · simpa [walkB, List.getElem_append_left hi] using hib
      · simpa [pieces, hi0, his, hiN] using (hsingle_ham i hiN hi0 his).mem_support a
  have hBc : walkB.IsChain B.Adj := by
    exact pB.isChain_adj_support.append (by simp) (by
      intro x hx y hy
      rw [hbase_last] at hx
      simp at hx hy
      subst x
      subst y
      exact hmb0.symm)
  have hBhead : walkB.head? = some b0 := by
    simpa [walkB, List.head?_append, hbase_head]
  have hBlast : walkB.getLast? = some b0 := by
    simp [walkB]
  exact boxProd_layered_hamPath (A := A) (B := B) walkB pieces a0 a1 b0 b0
    hBc hBhead hBlast hpiece_chain hpiece_nodup hpiece_ne hpiece_head hpiece_last
    hmatch hdisj hcover

private theorem boxProd_absorber_same_layer_even
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 : WB) (ha : a0 ≠ a1)
    (hcol : colA a0 = colA a1) (hAcard_ge_four : 4 ≤ Fintype.card WA)
    (hBeven : Even (Fintype.card WB)) :
    HasHamPath (A □ B) (a0, b0) (a1, b0) := by
  classical
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  let c0 : Bool := colA a0
  rcases hAsurj (!c0) with ⟨o0, ho0⟩
  rcases exists_same_color_ne_of_card_ge_four (A := A) hAbip hAsurj hAlace hAcard_ge_four o0 with
    ⟨o1, ho1_ne_o0, ho1_col_o0⟩
  have ho0_opp_a0 : colA o0 ≠ colA a0 := by
    have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
    rw [ho0c]
    cases h : colA a0 <;> simp [h]
  have ho1_opp_a0 : colA o1 ≠ colA a0 := by
    rw [ho1_col_o0]
    exact ho0_opp_a0
  have ho0_ne_a0 : o0 ≠ a0 := fun h => ho0_opp_a0 (by rw [h])
  have ho1_ne_a0 : o1 ≠ a0 := fun h => ho1_opp_a0 (by rw [h])
  have ho0_ne_a1 : o0 ≠ a1 := by
    intro h
    exact ho0_opp_a0 (by rw [h, ← hcol])
  have ho1_ne_a1 : o1 ≠ a1 := by
    intro h
    exact ho1_opp_a0 (by rw [h, ← hcol])
  rcases exists_adj_ne_of_hamConnected (B := B) hBcard hB b0 b0 with ⟨m, hmb0, hmb0_ne⟩
  rcases exists_adj_ne_of_hamConnected (B := B) hBcard hB m b0 with ⟨u, hum, hub0⟩
  have hm_ne_b0 : m ≠ b0 := hmb0_ne
  have hb0_ne_u : b0 ≠ u := hub0.symm
  have hu_ne_m : u ≠ m := hum.ne.symm
  rcases hB b0 u hb0_ne_u with ⟨pB, hpB⟩
  let base : List WB := pB.support
  let r : ℕ := base.idxOf m
  let walkB : List WB := base ++ [m, b0]
  let N : ℕ := walkB.length
  have hm_mem_base : m ∈ base := by
    simpa [base] using hpB.mem_support m
  have hbase_nodup : base.Nodup := by
    simpa [base] using hpB.isPath.support_nodup
  have hbase_len : base.length = Fintype.card WB := by
    simpa [base] using hpB.length_support
  have hN_eq : N = Fintype.card WB + 2 := by
    simp [N, walkB, base, hbase_len]
  have hN_even : Even N := by
    rcases hBeven with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  have hN_pos : 0 < N := by
    rw [hN_eq]
    omega
  have hN_ge_six : 6 ≤ N := by
    rw [hN_eq]
    rcases hBeven with ⟨k, hk⟩
    omega
  have hr_lt_base : r < base.length := by
    simpa [r] using List.idxOf_lt_length_of_mem hm_mem_base
  have hbase_r : base[r] = m := by
    simpa [r] using List.getElem_idxOf (l := base) (x := m) hr_lt_base
  have hbase_r_get? : base[r]? = some m := by
    rw [List.getElem?_eq_getElem hr_lt_base]
    exact congrArg some hbase_r
  have hbase_head : base.head? = some b0 := by
    simpa [base] using walk_support_head? pB
  have hbase_last : base.getLast? = some u := by
    simpa [base] using walk_support_getLast? pB
  have hbase0_lt : 0 < base.length := by
    rw [hbase_len]
    omega
  have hbase0_get : base[0]'hbase0_lt = b0 := by
    have h := hbase_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hbase0_lt] at h
    exact Option.some.inj h
  have hbase0_get? : base[0]? = some b0 := by
    rw [List.getElem?_eq_getElem hbase0_lt]
    exact congrArg some hbase0_get
  have hbase_last_get : base[base.length - 1]'(by
      have hpos : 0 < base.length := by
        rw [hbase_len]
        omega
      exact Nat.sub_lt hpos Nat.zero_lt_one) = u := by
    have hpos : 0 < base.length := by
      rw [hbase_len]
      omega
    have hidx : base.length - 1 < base.length := Nat.sub_lt hpos Nat.zero_lt_one
    have h := hbase_last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx] at h
    exact Option.some.inj h
  have hbase_last_get? : base[base.length - 1]? = some u := by
    have hpos : 0 < base.length := by
      rw [hbase_len]
      omega
    have hidx : base.length - 1 < base.length := Nat.sub_lt hpos Nat.zero_lt_one
    rw [List.getElem?_eq_getElem hidx]
    exact congrArg some hbase_last_get
  have hr_pos : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    have h₁ := hbase_r_get?
    rw [hr0] at h₁
    have hmb : m = b0 := Option.some.inj (h₁.symm.trans hbase0_get?)
    exact hm_ne_b0 hmb
  have hr_ne_last : r ≠ base.length - 1 := by
    intro hr_last
    have h₁ := hbase_r_get?
    rw [hr_last] at h₁
    have hmu : m = u := Option.some.inj (h₁.symm.trans hbase_last_get?)
    exact hu_ne_m hmu.symm
  have hr_succ_lt_base : r + 1 < base.length := by omega
  have hsM_eq_base_len : N - 2 = base.length := by
    simp [N, walkB]
  have hs0_eq_base_len_succ : N - 1 = base.length + 1 := by
    simp [N, walkB]
  have hsM_lt_N : N - 2 < N := by omega
  have hs0_lt_N : N - 1 < N := Nat.sub_lt hN_pos Nat.zero_lt_one
  have hr_lt_N : r < N := by
    simp [N, walkB]
    omega
  have hr_succ_lt_N : r + 1 < N := by
    simp [N, walkB]
    omega
  have hr_ne_sM : r ≠ N - 2 := by
    rw [hsM_eq_base_len]
    omega
  have hr_ne_s0 : r ≠ N - 1 := by
    rw [hs0_eq_base_len_succ]
    omega
  have hr_succ_ne_sM : r + 1 ≠ N - 2 := by
    rw [hsM_eq_base_len]
    omega
  have h0_ne_sM : 0 ≠ N - 2 := by omega
  have h0_ne_s0 : 0 ≠ N - 1 := by omega
  have hsM_ne_s0 : N - 2 ≠ N - 1 := by omega
  let boundary : ℕ → WA := fun i =>
    if i = N then a1
    else if i = N - 1 then o1
    else if i = N - 2 then a1
    else if i = r then (if r % 2 = 0 then a0 else o0)
    else if i = r + 1 then (if r % 2 = 0 then o0 else a0)
    else if i % 2 = 0 then a0 else o0
  have hboundary0 : boundary 0 = a0 := by
    have h0N : 0 ≠ N := by omega
    have h0s0 : 0 ≠ N - 1 := by omega
    have h0sM : 0 ≠ N - 2 := by omega
    have h0r : 0 ≠ r := by omega
    simp [boundary, h0N, h0s0, h0sM, h0r]
  have hboundary1 : boundary 1 = o0 := by
    have h1N : 1 ≠ N := by omega
    have h1s0 : 1 ≠ N - 1 := by omega
    have h1sM : 1 ≠ N - 2 := by omega
    by_cases hr1 : r = 1
    · have hrodd : ¬ r % 2 = 0 := by omega
      simp [boundary, h1N, h1s0, h1sM, hr1, hrodd]
    · have h1r : 1 ≠ r := by exact fun h => hr1 h.symm
      have h1r1 : 1 ≠ r + 1 := by omega
      have hr0ne : r ≠ 0 := by omega
      simp [boundary, h1N, h1s0, h1sM, h1r, h1r1, hr0ne]
  have hboundaryN : boundary N = a1 := by
    simp [boundary]
  have hboundary_s0 : boundary (N - 1) = o1 := by
    have hsN : N - 1 ≠ N := by omega
    simp [boundary, hsN]
  have hboundary_s0_succ : boundary ((N - 1) + 1) = a1 := by
    have hsN : N - 1 + 1 = N := by omega
    simp [boundary, hsN]
  have hboundary_sM : boundary (N - 2) = a1 := by
    have hMN : N - 2 ≠ N := by omega
    have hMs0 : N - 2 ≠ N - 1 := by omega
    simp [boundary, hMN, hMs0]
  have hboundary_sM_succ : boundary ((N - 2) + 1) = o1 := by
    have hsucc : N - 2 + 1 = N - 1 := by omega
    simp [hsucc, hboundary_s0]
  have hboundary_r : boundary r = (if r % 2 = 0 then a0 else o0) := by
    have hrN : r ≠ N := by omega
    have hrs0 : r ≠ N - 1 := hr_ne_s0
    have hrsM : r ≠ N - 2 := hr_ne_sM
    simp [boundary, hrN, hrs0, hrsM]
  have hboundary_r1 : boundary (r + 1) = (if r % 2 = 0 then o0 else a0) := by
    have hr1N : r + 1 ≠ N := by omega
    have hr1s0 : r + 1 ≠ N - 1 := by
      rw [hs0_eq_base_len_succ]
      omega
    have hr1sM : r + 1 ≠ N - 2 := hr_succ_ne_sM
    have hr1r : r + 1 ≠ r := by omega
    simp [boundary, hr1N, hr1s0, hr1sM, hr1r]
  have hboundary_color : ∀ i, i ≤ N →
      colA (boundary i) = if i % 2 = 0 then colA a0 else !colA a0 := by
    intro i hi
    by_cases hiN : i = N
    · subst i
      have hNeven : N % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 (by
        rcases hN_even with ⟨k, hk⟩
        exact ⟨k, by omega⟩)
      simp [boundary, hNeven, hcol]
    · by_cases his0 : i = N - 1
      · subst i
        have hsodd : ¬ (N - 1) % 2 = 0 := by
          intro hsmod
          rcases hN_even with ⟨k, hk⟩
          omega
        have ho1c : colA o1 = !colA a0 := by
          have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
          rw [ho1_col_o0, ho0c]
        simp [boundary, hiN, hsodd, ho1c]
      · by_cases hisM : i = N - 2
        · subst i
          have hMeven : (N - 2) % 2 = 0 := by
            rcases hN_even with ⟨k, hk⟩
            omega
          simp [boundary, hiN, his0, hMeven, hcol]
        · by_cases hir : i = r
          · subst i
            by_cases hrpar : r % 2 = 0
            · simp [boundary, hiN, his0, hisM, hrpar]
            · have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
              simp [boundary, hiN, his0, hisM, hrpar, ho0c]
          · by_cases hir1 : i = r + 1
            · subst i
              by_cases hrpar : r % 2 = 0
              · have hsucc_odd : ¬ (r + 1) % 2 = 0 := by omega
                have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
                simp [boundary, hiN, his0, hisM, hir, hrpar, hsucc_odd, ho0c]
              · have hsucc_even : (r + 1) % 2 = 0 := by omega
                simp [boundary, hiN, his0, hisM, hir, hrpar, hsucc_even]
            · by_cases hipar : i % 2 = 0
              · simp [boundary, hiN, his0, hisM, hir, hir1, hipar]
              · have ho0c : colA o0 = !colA a0 := by simpa [c0] using ho0
                simp [boundary, hiN, his0, hisM, hir, hir1, hipar, ho0c]
  have hboundary_col : ∀ i, i < N → colA (boundary i) ≠ colA (boundary (i + 1)) := by
    intro i hi
    have hci := hboundary_color i (by omega)
    have hcj := hboundary_color (i + 1) (by omega)
    rw [hci, hcj]
    by_cases hipar : i % 2 = 0
    · have hsucc_odd : ¬ (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_odd]
    · have hsucc_even : (i + 1) % 2 = 0 := by omega
      simp [hipar, hsucc_even]
  have h0_col₁ : colA (boundary 0) ≠ colA (boundary 1) := hboundary_col 0 (by omega)
  have h0_col₂ : colA (boundary (N - 1)) ≠ colA (boundary ((N - 1) + 1)) :=
    hboundary_col (N - 1) hs0_lt_N
  have hm_col₁ : colA (boundary r) ≠ colA (boundary (r + 1)) := hboundary_col r (by omega)
  have hm_col₂ : colA (boundary (N - 2)) ≠ colA (boundary ((N - 2) + 1)) :=
    hboundary_col (N - 2) hsM_lt_N
  have h0_ne₁ : boundary 0 ≠ boundary (N - 1) := by
    rw [hboundary0, hboundary_s0]
    exact ho1_ne_a0.symm
  have h0_ne₂ : boundary 0 ≠ boundary ((N - 1) + 1) := by
    rw [hboundary0, hboundary_s0_succ]
    exact ha
  have h0_ne₃ : boundary 1 ≠ boundary (N - 1) := by
    rw [hboundary1, hboundary_s0]
    exact ho1_ne_o0.symm
  have h0_ne₄ : boundary 1 ≠ boundary ((N - 1) + 1) := by
    rw [hboundary1, hboundary_s0_succ]
    exact ho0_ne_a1
  have h0_ne₅ : boundary 0 ≠ boundary 1 := fun h => h0_col₁ (congrArg colA h)
  have h0_ne₆ : boundary (N - 1) ≠ boundary ((N - 1) + 1) := fun h => h0_col₂ (congrArg colA h)
  rcases hAspan (boundary 0) (boundary 1)
      (boundary (N - 1)) (boundary ((N - 1) + 1))
      h0_col₁ h0_col₂ h0_ne₁ h0_ne₂ h0_ne₃ h0_ne₄ h0_ne₅ h0_ne₆ with
    ⟨p0, q0, hp0_path, hq0_path, h0_cover, h0_disj⟩
  have hm_ne₁ : boundary r ≠ boundary (N - 2) := by
    rw [hboundary_r, hboundary_sM]
    by_cases hrpar : r % 2 = 0
    · simpa [hrpar] using ha
    · simpa [hrpar] using ho0_ne_a1
  have hm_ne₂ : boundary r ≠ boundary ((N - 2) + 1) := by
    rw [hboundary_r, hboundary_sM_succ]
    by_cases hrpar : r % 2 = 0
    · simpa [hrpar] using ho1_ne_a0.symm
    · simpa [hrpar] using ho1_ne_o0.symm
  have hm_ne₃ : boundary (r + 1) ≠ boundary (N - 2) := by
    rw [hboundary_r1, hboundary_sM]
    by_cases hrpar : r % 2 = 0
    · simpa [hrpar] using ho0_ne_a1
    · simpa [hrpar] using ha
  have hm_ne₄ : boundary (r + 1) ≠ boundary ((N - 2) + 1) := by
    rw [hboundary_r1, hboundary_sM_succ]
    by_cases hrpar : r % 2 = 0
    · simpa [hrpar] using ho1_ne_o0.symm
    · simpa [hrpar] using ho1_ne_a0.symm
  have hm_ne₅ : boundary r ≠ boundary (r + 1) := fun h => hm_col₁ (congrArg colA h)
  have hm_ne₆ : boundary (N - 2) ≠ boundary ((N - 2) + 1) := fun h => hm_col₂ (congrArg colA h)
  rcases hAspan (boundary r) (boundary (r + 1))
      (boundary (N - 2)) (boundary ((N - 2) + 1))
      hm_col₁ hm_col₂ hm_ne₁ hm_ne₂ hm_ne₃ hm_ne₄ hm_ne₅ hm_ne₆ with
    ⟨pM, qM, hpM_path, hqM_path, hM_cover, hM_disj⟩
  let single : ∀ i : ℕ, i < N → i ≠ 0 → i ≠ N - 1 → i ≠ r → i ≠ N - 2 →
      A.Walk (boundary i) (boundary (i + 1)) :=
    fun i hi hi0 his0 hir hisM =>
      Classical.choose (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  have hsingle_ham : ∀ i (hi : i < N) (hi0 : i ≠ 0) (his0 : i ≠ N - 1)
      (hir : i ≠ r) (hisM : i ≠ N - 2),
      (single i hi hi0 his0 hir hisM).IsHamiltonian := by
    intro i hi hi0 his0 hir hisM
    exact Classical.choose_spec (hAlace (boundary i) (boundary (i + 1)) (hboundary_col i hi))
  let pieces : ℕ → List WA := fun i =>
    if hi0 : i = 0 then p0.support
    else if his0 : i = N - 1 then q0.support
    else if hir : i = r then pM.support
    else if hisM : i = N - 2 then qM.support
    else if hi : i < N then (single i hi hi0 his0 hir hisM).support
    else [a0]
  have hpieces_head : ∀ i, i < N → (pieces i).head? = some (boundary i) := by
    intro i hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using walk_support_head? p0
    · by_cases his0 : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his0, hs0] using walk_support_head? q0
      · by_cases hir : i = r
        · have hr0 : r ≠ 0 := by omega
          have hrs0 : r ≠ N - 1 := hr_ne_s0
          simpa [pieces, hi0, his0, hir, hr0, hrs0] using walk_support_head? pM
        · by_cases hisM : i = N - 2
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hi0, his0, hir, hisM, hM0, hMs0, hMr] using walk_support_head? qM
          · simpa [pieces, hi0, his0, hir, hisM, hi] using
              walk_support_head? (single i hi hi0 his0 hir hisM)
  have hpieces_last : ∀ i, i < N → (pieces i).getLast? = some (boundary (i + 1)) := by
    intro i hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using walk_support_getLast? p0
    · by_cases his0 : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his0, hs0] using walk_support_getLast? q0
      · by_cases hir : i = r
        · have hr0 : r ≠ 0 := by omega
          have hrs0 : r ≠ N - 1 := hr_ne_s0
          simpa [pieces, hi0, his0, hir, hr0, hrs0] using walk_support_getLast? pM
        · by_cases hisM : i = N - 2
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hi0, his0, hir, hisM, hM0, hMs0, hMr] using walk_support_getLast? qM
          · simpa [pieces, hi0, his0, hir, hisM, hi] using
              walk_support_getLast? (single i hi hi0 his0 hir hisM)
  have hpiece_chain : ∀ i, i < walkB.length → (pieces i).IsChain A.Adj := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using p0.isChain_adj_support
    · by_cases his0 : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his0, hs0] using q0.isChain_adj_support
      · by_cases hir : i = r
        · have hr0 : r ≠ 0 := by omega
          have hrs0 : r ≠ N - 1 := hr_ne_s0
          simpa [pieces, hi0, his0, hir, hr0, hrs0] using pM.isChain_adj_support
        · by_cases hisM : i = N - 2
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hi0, his0, hir, hisM, hM0, hMs0, hMr] using qM.isChain_adj_support
          · simpa [pieces, hi0, his0, hir, hisM, hiN] using
              (single i hiN hi0 his0 hir hisM).isChain_adj_support
  have hpiece_nodup : ∀ i, i < walkB.length → (pieces i).Nodup := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using hp0_path.support_nodup
    · by_cases his0 : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his0, hs0] using hq0_path.support_nodup
      · by_cases hir : i = r
        · have hr0 : r ≠ 0 := by omega
          have hrs0 : r ≠ N - 1 := hr_ne_s0
          simpa [pieces, hi0, his0, hir, hr0, hrs0] using hpM_path.support_nodup
        · by_cases hisM : i = N - 2
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hi0, his0, hir, hisM, hM0, hMs0, hMr] using hqM_path.support_nodup
          · simpa [pieces, hi0, his0, hir, hisM, hiN] using
              (hsingle_ham i hiN hi0 his0 hir hisM).isPath.support_nodup
  have hpiece_ne : ∀ i, i < walkB.length → pieces i ≠ [] := by
    intro i hi
    have hiN : i < N := by simpa [N] using hi
    by_cases hi0 : i = 0
    · simpa [pieces, hi0] using p0.support_ne_nil
    · by_cases his0 : i = N - 1
      · have hs0 : N - 1 ≠ 0 := by omega
        simpa [pieces, hi0, his0, hs0] using q0.support_ne_nil
      · by_cases hir : i = r
        · have hr0 : r ≠ 0 := by omega
          have hrs0 : r ≠ N - 1 := hr_ne_s0
          simpa [pieces, hi0, his0, hir, hr0, hrs0] using pM.support_ne_nil
        · by_cases hisM : i = N - 2
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hi0, his0, hir, hisM, hM0, hMs0, hMr] using qM.support_ne_nil
          · simpa [pieces, hi0, his0, hir, hisM, hiN] using
              (single i hiN hi0 his0 hir hisM).support_ne_nil
  have hpiece_head : (pieces 0).head? = some a0 := by
    have h := hpieces_head 0 hN_pos
    simpa [hboundary0] using h
  have hpiece_last : (pieces (walkB.length - 1)).getLast? = some a1 := by
    have hidx : walkB.length - 1 = N - 1 := by simp [N]
    have h := hpieces_last (N - 1) hs0_lt_N
    simpa [hidx, hboundary_s0_succ] using h
  have hmatch : ∀ i, i + 1 < walkB.length →
      (pieces i).getLast? = (pieces (i + 1)).head? := by
    intro i hi
    have hiN : i < N := by omega
    have hnextN : i + 1 < N := by simpa [N] using hi
    rw [hpieces_last i hiN, hpieces_head (i + 1) hnextN]
  have h0_disjoint : List.Disjoint p0.support q0.support := by
    intro x hx hy
    exact h0_disj x ⟨hx, hy⟩
  have hM_disjoint : List.Disjoint pM.support qM.support := by
    intro x hx hy
    exact hM_disj x ⟨hx, hy⟩
  have hwalk_get_0 : walkB[0]'(by simpa [N] using hN_pos) = b0 := by
    simpa [walkB, List.getElem_append_left hbase0_lt] using hbase0_get
  have hwalk_get_r : walkB[r]'hr_lt_N = m := by
    simpa [walkB, List.getElem_append_left hr_lt_base] using hbase_r
  have hwalk_get_sM : walkB[N - 2]'hsM_lt_N = m := by
    have hsopt : walkB[N - 2]? = some m := by
      rw [hsM_eq_base_len]
      simp [walkB]
    rw [List.getElem?_eq_getElem hsM_lt_N] at hsopt
    exact Option.some.inj hsopt
  have hwalk_get_s0 : walkB[N - 1]'hs0_lt_N = b0 := by
    have hsopt : walkB[N - 1]? = some b0 := by
      rw [hs0_eq_base_len_succ]
      simp [walkB]
    rw [List.getElem?_eq_getElem hs0_lt_N] at hsopt
    exact Option.some.inj hsopt
  have hdisj : (walkB.zipIdx).Pairwise (fun bi bj : WB × ℕ =>
      bi.1 ≠ bj.1 ∨ List.Disjoint (pieces bi.2) (pieces bj.2)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_zipIdx] at hi hj
    simp only [List.getElem_zipIdx]
    by_cases hbij : walkB[i] = walkB[j]
    · right
      by_cases hjs0 : j = N - 1
      · subst j
        have hwi : walkB[i]'hi = b0 := hbij.trans hwalk_get_s0
        by_cases hi0 : i = 0
        · subst i
          have hs0 : N - 1 ≠ 0 := by omega
          simpa [pieces, hs0] using h0_disjoint
        · by_cases hiM : i = N - 2
          · subst i
            have hmb : m = b0 := hwalk_get_sM.symm.trans hwi
            exact (hm_ne_b0 hmb).elim
          · have hi_base : i < base.length := by
              rw [← hsM_eq_base_len]
              omega
            have hbi : base[i]'hi_base = b0 := by
              simpa [walkB, List.getElem_append_left hi_base] using hwi
            have hi_eq0 : i = 0 := by
              have heq : base[i]'hi_base = base[0]'hbase0_lt := by
                simpa [hbase0_get] using hbi
              exact (hbase_nodup.getElem_inj_iff).mp heq
            exact (hi0 hi_eq0).elim
      · by_cases hjsM : j = N - 2
        · subst j
          have hwi : walkB[i]'hi = m := hbij.trans hwalk_get_sM
          by_cases hir : i = r
          · subst i
            have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            have hr0 : r ≠ 0 := by omega
            have hrs0 : r ≠ N - 1 := hr_ne_s0
            simpa [pieces, hr_ne_sM, hM0, hMs0, hMr, hr0, hrs0] using hM_disjoint
          · have hi_base : i < base.length := by
              rw [← hsM_eq_base_len]
              omega
            have hbi : base[i]'hi_base = m := by
              simpa [walkB, List.getElem_append_left hi_base] using hwi
            have hi_eqr : i = r := by
              have heq : base[i]'hi_base = base[r]'hr_lt_base := by
                simpa [hbase_r] using hbi
              exact (hbase_nodup.getElem_inj_iff).mp heq
            exact (hir hi_eqr).elim
        · have hi_base : i < base.length := by
            rw [← hsM_eq_base_len]
            omega
          have hj_base : j < base.length := by
            rw [← hsM_eq_base_len]
            omega
          have hbase_eq : base[i]'hi_base = base[j]'hj_base := by
            simpa [walkB, List.getElem_append_left hi_base, List.getElem_append_left hj_base] using hbij
          have hij_eq : i = j := (hbase_nodup.getElem_inj_iff).mp hbase_eq
          omega
    · exact Or.inl hbij
  have hcover : ∀ a b, ∃ i, ∃ hi : i < walkB.length,
      walkB[i]'hi = b ∧ a ∈ pieces i := by
    intro a b
    by_cases hb0 : b = b0
    · subst b
      rcases h0_cover a with ha0 | ha0
      · refine ⟨0, by simpa [N] using hN_pos, ?_, ?_⟩
        · exact hwalk_get_0
        · simpa [pieces] using ha0
      · refine ⟨N - 1, by simpa [N] using hs0_lt_N, ?_, ?_⟩
        · exact hwalk_get_s0
        · have hs0 : N - 1 ≠ 0 := by omega
          simpa [pieces, hs0] using ha0
    · by_cases hbm : b = m
      · subst b
        rcases hM_cover a with haM | haM
        · refine ⟨r, by simpa [N] using hr_lt_N, ?_, ?_⟩
          · exact hwalk_get_r
          · have hr0 : r ≠ 0 := by omega
            have hrs0 : r ≠ N - 1 := hr_ne_s0
            simpa [pieces, hr0, hrs0] using haM
        · refine ⟨N - 2, by simpa [N] using hsM_lt_N, ?_, ?_⟩
          · exact hwalk_get_sM
          · have hM0 : N - 2 ≠ 0 := by omega
            have hMs0 : N - 2 ≠ N - 1 := by omega
            have hMr : N - 2 ≠ r := fun h => hr_ne_sM h.symm
            simpa [pieces, hM0, hMs0, hMr] using haM
      · have hbmem : b ∈ base := by
          simpa [base] using hpB.mem_support b
        rcases List.getElem_of_mem hbmem with ⟨i, hi, hib⟩
        have hiN : i < N := by
          simp [N, walkB]
          omega
        have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          exact hb0 (hib.symm.trans hbase0_get)
        have hir : i ≠ r := by
          intro hir
          subst i
          exact hbm (hib.symm.trans hbase_r)
        have hisM : i ≠ N - 2 := by
          rw [hsM_eq_base_len]
          omega
        have his0 : i ≠ N - 1 := by
          rw [hs0_eq_base_len_succ]
          omega
        refine ⟨i, by simpa [N] using hiN, ?_, ?_⟩
        · simpa [walkB, List.getElem_append_left hi] using hib
        · simpa [pieces, hi0, his0, hir, hisM, hiN] using
            (hsingle_ham i hiN hi0 his0 hir hisM).mem_support a
  have hBc : walkB.IsChain B.Adj := by
    have hbase_append_m : (base ++ [m]).IsChain B.Adj := by
      exact pB.isChain_adj_support.append (by simp) (by
        intro x hx y hy
        rw [hbase_last] at hx
        simp at hx hy
        subst x
        subst y
        exact hum.symm)
    simpa [List.append_assoc] using hbase_append_m.append (by simp) (by
      intro x hx y hy
      change x ∈ (base ++ [m]).getLast? at hx
      change y ∈ ([b0] : List WB).head? at hy
      have hlast : (base ++ [m]).getLast? = some m := by
        simp
      rw [hlast] at hx
      simp at hx hy
      subst x
      subst y
      exact hmb0.symm)
  have hBhead : walkB.head? = some b0 := by
    simpa [walkB, List.head?_append, hbase_head]
  have hBlast : walkB.getLast? = some b0 := by
    simp [walkB]
  exact boxProd_layered_hamPath (A := A) (B := B) walkB pieces a0 a1 b0 b0
    hBc hBhead hBlast hpiece_chain hpiece_nodup hpiece_ne hpiece_head hpiece_last
    hmatch hdisj hcover

/-- **§4 sub-lemma A (TODO — both factors non-bipartite).** If `A` and `B` are non-bipartite and
    Hamilton-connected, so is `A □ B`. (Non-bipartite ⇒ `≥ 3` vertices and product non-bipartite, so
    the generalised-endpoint snake with per-column crossing vertices applies — no `K₂` degeneracy.)
    The non-bipartiteness hypotheses are ESSENTIAL: without them `A = B = K₂` is a counterexample
    (`K₂ □ K₂ = C₄`). -/
theorem boxProd_hamConn_both_nonbip [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hAnb : ¬ ∃ col, IsProper2Coloring A col) (hBnb : ¬ ∃ col, IsProper2Coloring B col)
    (hA : IsHamConnected A) (hB : IsHamConnected B) : IsHamConnected (A □ B) := by
  classical
  have hAcard : 3 ≤ Fintype.card WA := card_ge_three_of_not_bip (A := A) hAnb
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  rintro ⟨a0, b0⟩ ⟨a1, b1⟩ huv
  by_cases ha : a0 = a1
  · have hb : b0 ≠ b1 := by
      intro hb
      exact huv (by simp [ha, hb])
    exact hasHamPath_iso (SimpleGraph.boxProdComm A B)
      (boxProd_hamConn_both_nonbip_fst_ne (A := B) (B := A)
        hBcard hAcard hB hA (a0 := b0) (a1 := b1) (b0 := a0) (b1 := a1) hb)
  · exact boxProd_hamConn_both_nonbip_fst_ne (A := A) (B := B)
      hAcard hBcard hA hB (a0 := a0) (a1 := a1) (b0 := b0) (b1 := b1) ha

/-- **THE last open §4 core — the doubled-layer device (TODO).** The subcase of the same-colour
    absorber that genuinely needs a *doubled* layer: `b0 = b1` (same `B`-layer) or `|V(B)|` odd (no
    even-length Hamilton path of `B`). Manuscript §4 Proposition 4.1: route a controlled spanning walk
    of `B` (visiting each vertex `≤ 2×`, of the parity absorbing the colour discrepancy — the Claim on
    controlled spanning walks), cover the `≤ 2` doubled layers by a paired-2-cover of `A` (`hAspan`)
    with four distinct terminals in two opposite-colour pairs (Lemma 4.2), single layers by
    Hamilton-laceable paths, and flatten via `boxProd_layered_hamPath`. -/
private theorem boxProd_absorber_doubled_layer
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 b1 : WB) (huv : (a0, b0) ≠ (a1, b1))
    (hcol : colA a0 = colA a1) (hAcard_ge_four : 4 ≤ Fintype.card WA)
    (hneed : b0 = b1 ∨ ¬ Even (Fintype.card WB)) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  rcases hneed with hb_eq | hBodd
  · subst b1
    have ha : a0 ≠ a1 := by
      intro haeq
      exact huv (by simp [haeq])
    by_cases hBeven : Even (Fintype.card WB)
    · exact boxProd_absorber_same_layer_even hAbip hAsurj hAlace hAspan hBnb hB
        a0 a1 b0 ha hcol hAcard_ge_four hBeven
    · exact boxProd_absorber_same_layer_odd hAbip hAsurj hAlace hAspan hBnb hB
        a0 a1 b0 ha hcol hAcard_ge_four hBeven
  · by_cases hb : b0 = b1
    · subst b1
      have ha : a0 ≠ a1 := by
        intro haeq
        exact huv (by simp [haeq])
      by_cases hBeven : Even (Fintype.card WB)
      · exact boxProd_absorber_same_layer_even hAbip hAsurj hAlace hAspan hBnb hB
          a0 a1 b0 ha hcol hAcard_ge_four hBeven
      · exact boxProd_absorber_same_layer_odd hAbip hAsurj hAlace hAspan hBnb hB
          a0 a1 b0 ha hcol hAcard_ge_four hBeven
    · exact boxProd_absorber_doubled_layer_open_odd hAbip hAsurj hAlace hAspan hBnb hB
        a0 a1 (b0 := b0) (b1 := b1) hb hcol hAcard_ge_four hBodd

/-- **§4 same-colour, `|V(A)| ≥ 4` absorber.** Proved modulo the single remaining core
    `boxProd_absorber_doubled_layer`: when `b0 ≠ b1` and `|V(B)|` is even, a Hamilton path of `B` has
    even occurrence count, so the coloured snake (`boxProd_same_color_over_B_hamPath_even`, no doubled
    layer) already works; otherwise a layer must be doubled. -/
private theorem boxProd_absorber_same_color
    [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 b1 : WB) (huv : (a0, b0) ≠ (a1, b1))
    (hcol : colA a0 = colA a1) (hAcard_ge_four : 4 ≤ Fintype.card WA) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  by_cases hb : b0 = b1
  · exact boxProd_absorber_doubled_layer hAbip hAsurj hAlace hAspan hBnb hB a0 a1 b0 b1 huv hcol
      hAcard_ge_four (Or.inl hb)
  · by_cases hn : Even (Fintype.card WB)
    · obtain ⟨pB, hpB⟩ := hB b0 b1 hb
      have hlen : pB.support.length = Fintype.card WB := by
        have hnd : pB.support.Nodup := hpB.isPath.support_nodup
        have huniv : pB.support.toFinset = Finset.univ := by
          ext x
          simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
          exact hpB.mem_support x
        rw [← List.toFinset_card_of_nodup hnd, huniv, Finset.card_univ]
      exact boxProd_same_color_over_B_hamPath_even hAbip hAsurj hAlace a0 a1 pB hpB hcol
        (by rw [hlen]; exact hn)
    · exact boxProd_absorber_doubled_layer hAbip hAsurj hAlace hAspan hBnb hB a0 a1 b0 b1 huv hcol
        hAcard_ge_four (Or.inr hn)

/-- **§4 sub-lemma B (one factor bipartite; Proposition 4.1 + the `K₂` prism).** If `A` is
    bipartite with the full paired-cover witness (proper `colA`, surjective, Hamilton-laceable,
    spanning-2-laceable) and `B` is **non-bipartite** Hamilton-connected, then `A □ B` is
    Hamilton-connected. (`B` non-bipartite ⇒ `A □ B` non-bipartite; laceable+surjective ⇒ `|V(A)|` even
    and balanced, so `|V(A)| = 2` is the prism and `|V(A)| ≥ 4` the doubled-layer absorber.) Proved
    modulo the single isolated core `boxProd_absorber_same_color` (same-colour, `|V(A)| ≥ 4`). -/
theorem boxProd_hamConn_one_bip [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B) : IsHamConnected (A □ B) := by
  classical
  rintro ⟨a0, b0⟩ ⟨a1, b1⟩ huv
  by_cases hcard : (Fintype.card WA = 2)
  · exact (boxProd_prism_card_two (A := A) (B := B) hcard hAsurj hAlace hBnb hB)
      (a0, b0) (a1, b1) huv
  · by_cases hcol : colA a0 ≠ colA a1
    · exact boxProd_hamConn_one_bip_color_ne (A := A) (B := B) hAsurj hAlace hBnb hB hcol
    · have hAeven : Even (Fintype.card WA) :=
        even_card_of_bip_laceable_surj (A := A) hAbip hAsurj hAlace
      have hAcard_ge_two : 2 ≤ Fintype.card WA := by
        have h := Fintype.card_le_of_surjective colA hAsurj
        simpa [Fintype.card_bool] using h
      have hAcard_ge_four : 4 ≤ Fintype.card WA := by
        rcases hAeven with ⟨k, hk⟩
        omega
      exact boxProd_absorber_same_color hAbip hAsurj hAlace hAspan hBnb hB a0 a1 b0 b1 huv
        (not_not.mp hcol) hAcard_ge_four

/-- **§4 core — reduces `reduction_decompose`'s non-bipartite branch to the two sub-lemmas.**
    Each factor is `FactorReady`; `A □ B` is non-bipartite. Cases on the per-factor dichotomy: both
    non-bipartite → sub-lemma A; exactly one bipartite → sub-lemma B (via `boxProdComm` for the mirror
    order); both bipartite → impossible, since `boxProd_proper_color` would 2-colour `A □ B`. -/
theorem boxProd_hamConnected [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hA : FactorReady A) (hB : FactorReady B)
    (hnb : ¬ ∃ col, IsProper2Coloring (A □ B) col) :
    IsHamConnected (A □ B) := by
  rcases hA with ⟨hAnb, hAconn⟩ | ⟨cA, hAbip, hAsurj, hAlace, hAspan⟩
  · rcases hB with ⟨hBnb, hBconn⟩ | ⟨cB, hBbip, hBsurj, hBlace, hBspan⟩
    · exact boxProd_hamConn_both_nonbip hAnb hBnb hAconn hBconn
    · -- `A` non-bipartite, `B` bipartite: sub-lemma B on `B □ A`, transported by `boxProdComm`
      exact isHamConnected_iso (SimpleGraph.boxProdComm A B)
        (boxProd_hamConn_one_bip hBbip hBsurj hBlace hBspan hAnb hAconn)
  · rcases hB with ⟨hBnb, hBconn⟩ | ⟨cB, hBbip, hBsurj, hBlace, hBspan⟩
    · exact boxProd_hamConn_one_bip hAbip hAsurj hAlace hAspan hBnb hBconn
    · -- both bipartite ⇒ `A □ B` bipartite, contradicting `hnb`
      exact absurd ⟨fun p => Bool.xor (cA p.1) (cB p.2), boxProd_proper_color hAbip hBbip⟩ hnb

/-! ### §4 anti-vacuity sentinels (guarding that `IsHamConnected` is a genuine, discriminating
    predicate — not vacuously true — and that the non-bipartiteness hypotheses are load-bearing). -/

/-- In a properly 2-coloured graph, a walk joins equal-colour endpoints iff it has even length. -/
theorem walk_color_parity {V : Type*} {G : SimpleGraph V} {col : V → Bool}
    (hcol : ∀ u v, G.Adj u v → col u ≠ col v) :
    ∀ {u v : V} (p : G.Walk u v), (col u = col v ↔ Even p.length) := by
  intro u v p
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    have hne : col u ≠ col w := hcol u w h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases hu : col u <;> cases hw : col w <;> cases hv : col v <;> simp_all

/-- **§4 anti-vacuity sentinel.** `C₄ = K₂ □ K₂` is NOT Hamilton-connected: no Hamilton path joins the
    antipodal same-colour vertices `(0,0)` and `(1,1)`. So `IsHamConnected` genuinely discriminates
    (it is provably false here), and the non-bipartiteness hypotheses of `boxProd_hamConn_both_nonbip`
    are essential — without them the lemma would claim exactly this false statement. -/
theorem C4_not_hamConnected :
    ¬ IsHamConnected ((⊤ : SimpleGraph (Fin 2)) □ (⊤ : SimpleGraph (Fin 2))) := by
  intro hHC
  let cK : Fin 2 → Bool := fun i => decide (i = 1)
  have hcK : ∀ u v : Fin 2, (⊤ : SimpleGraph (Fin 2)).Adj u v → cK u ≠ cK v := by
    intro u v huv; fin_cases u <;> fin_cases v <;> simp_all [cK]
  have hcol := boxProd_proper_color (A := (⊤ : SimpleGraph (Fin 2))) (B := (⊤ : SimpleGraph (Fin 2)))
    hcK hcK
  obtain ⟨p, hp⟩ := hHC (0, 0) (1, 1) (by decide)
  have hcolEq : Bool.xor (cK (0, 0).1) (cK (0, 0).2) = Bool.xor (cK (1, 1).1) (cK (1, 1).2) := by decide
  have heven : Even p.length := (walk_color_parity hcol p).mp hcolEq
  have hlen : p.length = 3 := by simpa using hp.length_eq
  rw [hlen] at heven
  exact (by decide : ¬ Even 3) heven

end Brualdi.Ledger
