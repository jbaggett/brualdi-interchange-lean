/-
# §4 as printed — Proposition 4.1 by the paper's walk device

This file re-proves the one-bipartite-factor case of §4 (the paper's Proposition 4.1)
following the PRINTED proof: thread the layers of `A □ B` along a spanning walk of `B`
obtained from the Claim (controlled spanning walks), selected by the color-telescoping
parity `N ≡ χ(a₀) ⊕ χ(a₁)`; assign the boundary vertices along the walk in the telescoping
colors (the paper's global boundary pass, with the four terminals of every doubled layer
pairwise distinct); traverse single layers by Hamilton paths of `A` (laceability) and
doubled layers by a paired 2-cover (spanning-2-laceability); splice with the verified
layered-assembly lemma `boxProd_layered_hamPath`.

The walks used are the Claim's four shapes — a Hamilton path of `B`; a Hamilton path plus a
closing edge (one doubled layer); a Hamilton cycle (one doubled layer at the base); a cycle
with a two-edge detour (two doubled layers, the paper's same-layer case, including its
shared-boundary refinement). The Claim as printed is `controlled_spanning_walks`
(AltProofs.lean); here its constructions are used in list form, with the occurrence
structure the boundary pass needs made explicit.

`boxProd_hamConnected_paper` at the end proves the same statement as `Sec4.lean`'s
`boxProd_hamConnected` with the one-bipartite branch carried by this development; the
absorber route remains in `Sec4.lean` as the independent alternate. Everything here is
foundations-only.
-/
import BrualdiLean.Sec4

namespace Brualdi.Ledger
open SimpleGraph

variable {WA WB : Type*} {A : SimpleGraph WA} {B : SimpleGraph WB}

/-! ## The assembly core: boundaries + per-position pieces ⟹ Hamilton path

A thin translation layer onto the verified splice `boxProd_layered_hamPath`: given the walk
`walkB`, a boundary assignment `β` pinned at the endpoints, and per-position pieces running
`β i → β (i+1)` that are disjoint on repeated layers and jointly cover, the product has the
Hamilton path. This is the interface the paper's boundary pass feeds. -/

theorem walk_assembly_core [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (a0 a1 : WA) (b0 b1 : WB) (walkB : List WB) (β : ℕ → WA) (pieces : ℕ → List WA)
    (hBc : walkB.IsChain B.Adj)
    (hBhead : walkB.head? = some b0) (hBlast : walkB.getLast? = some b1)
    (hβ0 : β 0 = a0) (hβN : β walkB.length = a1)
    (hpc : ∀ i, i < walkB.length →
        (pieces i).IsChain A.Adj ∧ (pieces i).Nodup ∧ pieces i ≠ [] ∧
        (pieces i).head? = some (β i) ∧ (pieces i).getLast? = some (β (i + 1)))
    (hdisjP : ∀ i j, i < j → ∀ (hi : i < walkB.length) (hj : j < walkB.length),
        walkB[i]'hi = walkB[j]'hj → List.Disjoint (pieces i) (pieces j))
    (hcovP : ∀ a b, ∃ i, ∃ hi : i < walkB.length, walkB[i]'hi = b ∧ a ∈ pieces i) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  have hNpos : 0 < walkB.length := by
    cases walkB with
    | nil => simp at hBhead
    | cons x l => simp
  refine boxProd_layered_hamPath (A := A) (B := B) walkB pieces a0 a1 b0 b1 hBc hBhead hBlast
    (fun i hi => (hpc i hi).1) (fun i hi => (hpc i hi).2.1) (fun i hi => (hpc i hi).2.2.1)
    ?_ ?_ ?_ ?_ hcovP
  · rw [← hβ0]
    exact (hpc 0 hNpos).2.2.2.1
  · have hlt : walkB.length - 1 < walkB.length := Nat.sub_lt hNpos Nat.zero_lt_one
    have h := (hpc _ hlt).2.2.2.2
    have harith : walkB.length - 1 + 1 = walkB.length := by omega
    rw [harith] at h
    rw [← hβN]
    exact h
  · intro i hi
    have h1 := (hpc i (by omega)).2.2.2.2
    have h2 := (hpc (i + 1) hi).2.2.2.1
    rw [h1, h2]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < walkB.length := by simpa [List.length_zipIdx] using hi
    have hj' : j < walkB.length := by simpa [List.length_zipIdx] using hj
    rw [List.getElem_zipIdx, List.getElem_zipIdx]
    by_cases heq : walkB[i]'hi' = walkB[j]'hj'
    · exact Or.inr (by simpa using hdisjP i j hij hi' hj' heq)
    · exact Or.inl (by simpa using heq)

/-! ## Boundary and piece helpers -/

/-- Pick a vertex of a prescribed color. -/
theorem walk_pick_color {colA : WA → Bool} (hAsurj : Function.Surjective colA) (c : Bool) :
    ∃ v, colA v = c :=
  hAsurj c

/-- Pick a vertex of a prescribed color avoiding one vertex (each color class has at least
    two vertices; this is the paper's "a valid distinct choice is available"). -/
theorem walk_pick_color_ne [Fintype WA] [DecidableEq WA]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (hAcard : 4 ≤ Fintype.card WA) (c : Bool) (x : WA) :
    ∃ v, colA v = c ∧ v ≠ x := by
  by_cases hx : colA x = c
  · obtain ⟨v, hv_ne, hv_col⟩ :=
      exists_same_color_ne_of_card_ge_four (A := A) hAbip hAsurj hAlace hAcard x
    exact ⟨v, hv_col.trans hx, hv_ne⟩
  · obtain ⟨v, hv⟩ := hAsurj c
    exact ⟨v, hv, fun h => hx (h ▸ hv)⟩

/-- The telescoping color at step `i`. -/
def walkColor (c0 : Bool) (i : ℕ) : Bool := if i % 2 = 0 then c0 else !c0

theorem walkColor_succ_ne (c0 : Bool) (i : ℕ) : walkColor c0 (i + 1) ≠ walkColor c0 i := by
  unfold walkColor
  rcases Nat.even_or_odd i with he | ho
  · have h1 : i % 2 = 0 := Nat.even_iff.mp he
    have h2 : ¬((i + 1) % 2 = 0) := by omega
    simp [h1, h2]
  · have h1 : ¬(i % 2 = 0) := by
      have := Nat.odd_iff.mp ho
      omega
    have h2 : (i + 1) % 2 = 0 := by
      have := Nat.odd_iff.mp ho
      omega
    simp [h1, h2]

/-! ## Shape 1: a Hamilton path of `B` (no doubled layer)

Applies when `N = |V(B)|` already has the parity the telescoping demands
(`χ(a₁) = walkColor (χ(a₀)) N`). Every layer is traversed once, by a Hamilton path of `A`
between opposite-colored boundaries. -/

theorem walk_pass_hamPath [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (a0 a1 : WA) {b0 b1 : WB} (pB : B.Walk b0 b1) (hpB : pB.IsHamiltonian)
    (hpar : colA a1 = walkColor (colA a0) pB.support.length) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  set walkB : List WB := pB.support with hwalkBdef
  set N : ℕ := walkB.length with hNdef
  have hNpos : 0 < N := by
    simp [N, walkB]
  -- boundaries: pins at the ends, any vertex of the telescoping color inside
  obtain ⟨dT, hdT⟩ := hAsurj true
  obtain ⟨dF, hdF⟩ := hAsurj false
  set d : Bool → WA := fun c => if c then dT else dF with hddef
  have hdcol : ∀ c, colA (d c) = c := by
    intro c
    cases c <;> simp [d, hdT, hdF]
  set β : ℕ → WA := fun i => if i = 0 then a0 else if i = N then a1 else
    d (walkColor (colA a0) i) with hβdef
  have hβ0 : β 0 = a0 := by simp [β]
  have hβN : β N = a1 := by
    have h0 : ¬(N = 0) := by omega
    simp [β, h0]
  have hβcol : ∀ i, colA (β i) = walkColor (colA a0) i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      simp [β, walkColor]
    · by_cases hN : i = N
      · subst hN
        rw [hβN]
        simpa [N, walkB] using hpar
      · simp [β, h0, hN, hdcol]
  have hβconsec : ∀ i, colA (β i) ≠ colA (β (i + 1)) := by
    intro i
    rw [hβcol, hβcol]
    exact (walkColor_succ_ne (colA a0) i).symm
  -- per-position Hamilton paths of A
  have hham : ∀ i, ∃ w : A.Walk (β i) (β (i + 1)), w.IsHamiltonian := fun i =>
    hAlace (β i) (β (i + 1)) (hβconsec i)
  choose ham hhamP using hham
  set pieces : ℕ → List WA := fun i => (ham i).support with hpiecesdef
  -- walk facts
  have hBc : walkB.IsChain B.Adj := by simpa [walkB] using pB.isChain_adj_support
  have hBhead : walkB.head? = some b0 := by simpa [walkB] using walk_support_head? pB
  have hBlast : walkB.getLast? = some b1 := by simpa [walkB] using walk_support_getLast? pB
  have hnodup : walkB.Nodup := by simpa [walkB] using hpB.isPath.support_nodup
  refine walk_assembly_core a0 a1 b0 b1 walkB β pieces hBc hBhead hBlast hβ0 hβN ?_ ?_ ?_
  · intro i _
    exact ⟨(ham i).isChain_adj_support, (hhamP i).isPath.support_nodup,
      (ham i).support_ne_nil, walk_support_head? (ham i), walk_support_getLast? (ham i)⟩
  · intro i j hij hi hj heq
    exact absurd (hnodup.getElem_inj_iff.mp heq) (by omega)
  · intro a b
    have hb : b ∈ walkB := by simpa [walkB] using hpB.mem_support b
    obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hb
    exact ⟨i, hi, hib, by simpa [pieces] using (hhamP i).mem_support a⟩

theorem walkColor_succ (c0 : Bool) (i : ℕ) : walkColor c0 (i + 1) = !(walkColor c0 i) := by
  unfold walkColor
  rcases Nat.even_or_odd i with he | ho
  · have h1 : i % 2 = 0 := Nat.even_iff.mp he
    have h2 : ¬((i + 1) % 2 = 0) := by omega
    cases c0 <;> simp [h1, h2]
  · have h1 : ¬(i % 2 = 0) := by
      have := Nat.odd_iff.mp ho
      omega
    have h2 : (i + 1) % 2 = 0 := by
      have := Nat.odd_iff.mp ho
      omega
    cases c0 <;> simp [h1, h2]

/-- A Hamiltonian walk in a graph on at least three vertices is not nil. -/
private theorem walkHam_not_nil {V : Type u} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {s t : V} {P : G.Walk s t} (hP : P.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) : ¬ P.Nil := by
  intro hnil
  have hlen : P.length = Fintype.card V - 1 := hP.length_eq
  have := SimpleGraph.Walk.nil_iff_length_eq.mp hnil
  omega

/-- The penultimate vertex of a Hamilton path avoids the start (three or more vertices).
    (The paper's degree facts come from exactly this observation.) -/
private theorem walkHam_penultimate_ne {V : Type u} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} {s t : V} {P : G.Walk s t} (hP : P.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) : P.penultimate ≠ s := by
  intro heq
  have hlen : P.length = Fintype.card V - 1 := hP.length_eq
  have heq' : P.getVert (P.length - 1) = P.getVert 0 := by
    rw [SimpleGraph.Walk.getVert_zero]
    exact heq
  have hij := hP.isPath.getVert_injOn
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) heq'
  omega

/-- Choose the two free terminals of a doubled layer: a `c`-colored and a `!c`-colored vertex,
    distinct from each other and from the two given opposite-colored vertices. This is the
    paper's "a valid distinct choice is available at every step" (each color class of `A` has
    at least two vertices). -/
theorem walk_pick_terminals [Fintype WA] [DecidableEq WA]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA)
    (hAsurj : Function.Surjective colA) (hAlace : IsHamLaceable A colA)
    (hAcard : 4 ≤ Fintype.card WA) (c : Bool) (x y : WA) (hxy : colA x ≠ colA y) :
    ∃ v w, colA v = c ∧ colA w = !c ∧ v ≠ w ∧ v ≠ x ∧ v ≠ y ∧ w ≠ x ∧ w ≠ y := by
  have hboolne : ∀ b : Bool, b ≠ !b := by decide
  by_cases hx : colA x = c
  · have hy : colA y = !c := by
      have h1 : colA y ≠ c := fun h => hxy (hx.trans h.symm)
      cases hcy : colA y <;> cases hc : c <;> simp [hcy, hc] at h1 ⊢
    obtain ⟨v, hvc, hvx⟩ := walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard c x
    obtain ⟨w, hwc, hwy⟩ := walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (!c) y
    refine ⟨v, w, hvc, hwc, ?_, hvx, ?_, ?_, hwy⟩
    · intro h
      exact absurd ((h ▸ hvc : colA w = c).symm.trans hwc) (hboolne c)
    · intro h
      exact absurd ((h ▸ hvc : colA y = c).symm.trans hy) (hboolne c)
    · intro h
      exact absurd (hx.symm.trans (h ▸ hwc : colA x = !c)) (hboolne c)
  · have hx' : colA x = !c := by
      cases hcx : colA x <;> cases hc : c <;> simp [hcx, hc] at hx ⊢
    have hy : colA y = c := by
      have h1 : colA y ≠ !c := fun h => hxy (hx'.trans h.symm)
      cases hcy : colA y <;> cases hc : c <;> simp [hcy, hc] at h1 ⊢
    obtain ⟨v, hvc, hvy⟩ := walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard c y
    obtain ⟨w, hwc, hwx⟩ := walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (!c) x
    refine ⟨v, w, hvc, hwc, ?_, ?_, hvy, hwx, ?_⟩
    · intro h
      exact absurd ((h ▸ hvc : colA w = c).symm.trans hwc) (hboolne c)
    · intro h
      exact absurd ((h ▸ hvc : colA x = c).symm.trans hx') (hboolne c)
    · intro h
      exact absurd (hy.symm.trans (h ▸ hwc : colA y = !c)) (hboolne c)

/-! ## Shape 2: a Hamilton path plus a closing edge (one doubled layer)

The Claim's `N = n + 1` open walk: a Hamilton path `b₀ → w` for a neighbor `w ≠ b₀` of `b₁`,
closed by the edge `w b₁`. The layer of `b₁` is traversed twice — once inside the path, once
at the end — and receives a paired 2-cover; the four terminals are chosen distinct by the
boundary pass. -/

theorem walk_pass_plus_edge [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hAcard : 4 ≤ Fintype.card WA)
    (hBcard : 3 ≤ Fintype.card WB) (hB : IsHamConnected B)
    (a0 a1 : WA) {b0 b1 : WB} (hb : b0 ≠ b1)
    (hpar : colA a1 = walkColor (colA a0) (Fintype.card WB + 1)) :
    HasHamPath (A □ B) (a0, b0) (a1, b1) := by
  classical
  set n : ℕ := Fintype.card WB with hndef
  -- a neighbor w ≠ b0 of b1, and a Hamilton path b0 → w
  obtain ⟨w, hwb1, hwb0⟩ := exists_adj_ne_of_hamConnected (B := B) hBcard hB b1 b0
  obtain ⟨Q, hQ⟩ := hB b0 w (Ne.symm hwb0)
  set base : List WB := Q.support with hbasedef
  have hbase_nodup : base.Nodup := by simpa [base] using hQ.isPath.support_nodup
  have hbase_len : base.length = n := by simpa [base, n] using hQ.length_support
  have hbase_head : base.head? = some b0 := by simpa [base] using walk_support_head? Q
  have hbase_last : base.getLast? = some w := by simpa [base] using walk_support_getLast? Q
  have hnpos : 3 ≤ n := hBcard
  set walkB : List WB := base ++ [b1] with hwalkBdef
  have hlen : walkB.length = n + 1 := by simp [walkB, hbase_len]
  -- the interior occurrence of b1
  have hb1_mem : b1 ∈ base := by simpa [base] using hQ.mem_support b1
  set k : ℕ := base.idxOf b1 with hkdef
  have hk_lt : k < base.length := by simpa [k] using List.idxOf_lt_length_of_mem hb1_mem
  have hbase_k : base[k]'hk_lt = b1 := by
    simpa [k] using List.getElem_idxOf (l := base) (x := b1) hk_lt
  have hbase_len_pos : 0 < base.length := by omega
  have hbase_k? : base[k]? = some b1 := by
    rw [List.getElem?_eq_getElem hk_lt]
    exact congrArg some hbase_k
  have hbase_zero? : base[0]? = some b0 := by
    have h := hbase_head
    rwa [List.head?_eq_getElem?] at h
  have hbase_last? : base[base.length - 1]? = some w := by
    have h := hbase_last
    rwa [List.getLast?_eq_getElem?] at h
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      apply hb
      have h1 : base[0]? = some b1 := by
        rw [← h0]
        exact hbase_k?
      exact Option.some.inj (hbase_zero?.symm.trans h1)
    · exact h
  have hk_ne_last : k ≠ base.length - 1 := by
    intro h
    apply hwb1.ne'
    have h1 : base[base.length - 1]? = some b1 := by
      rw [← h]
      exact hbase_k?
    exact Option.some.inj (hbase_last?.symm.trans h1)
  have hk_le : k + 1 ≤ n - 1 := by
    have h1 := hk_lt
    have h2 := hk_ne_last
    rw [hbase_len] at h1 h2
    omega
  -- walk facts
  have hBc : walkB.IsChain B.Adj := by
    exact Q.isChain_adj_support.append (by simp) (by
      intro x hx y hy
      rw [hbase_last] at hx
      simp at hx hy
      subst x
      subst y
      exact hwb1.symm)
  have hBhead : walkB.head? = some b0 := by
    simpa [walkB, List.head?_append, hbase_head]
  have hBlast : walkB.getLast? = some b1 := by
    simp [walkB]
  have hgetElem_lt : ∀ i (hi : i < base.length) (hi' : i < walkB.length),
      walkB[i]'hi' = base[i]'hi := by
    intro i hi hi'
    exact List.getElem_append_left hi
  have hgetElem_n? : walkB[n]? = some b1 := by
    have h : (base ++ [b1])[base.length]? = some b1 := by simp
    rw [hbase_len] at h
    exact h
  have hgetElem_n : ∀ (hn : n < walkB.length), walkB[n]'hn = b1 := by
    intro hn
    have h := hgetElem_n?
    rw [List.getElem?_eq_getElem hn] at h
    exact Option.some.inj h
  -- boundary pass
  set c0 : Bool := colA a0 with hc0def
  obtain ⟨dT, hdT⟩ := hAsurj true
  obtain ⟨dF, hdF⟩ := hAsurj false
  set d : Bool → WA := fun c => if c then dT else dF with hddef
  have hdcol : ∀ c, colA (d c) = c := by
    intro c
    cases c <;> simp [d, hdT, hdF]
  set vn : WA := d (walkColor c0 n) with hvndef
  have hvn_col : colA vn = walkColor c0 n := hdcol _
  have hvn_a1 : colA vn ≠ colA a1 := by
    rw [hvn_col, hpar, walkColor_succ]
    cases walkColor c0 n <;> simp
  obtain ⟨vk, vk1, hvk_col, hvk1_col, hvv, hvkvn, hvka1, hvk1vn, hvk1a1⟩ :=
    walk_pick_terminals (A := A) hAbip hAsurj hAlace hAcard (walkColor c0 k) vn a1 hvn_a1
  set N : ℕ := walkB.length with hNdef
  have hNval : N = n + 1 := hlen
  have hlen2 : walkB.length = n + 1 := hNdef.symm.trans hlen
  have hkn : k < n := by
    have h := hk_lt
    rwa [hbase_len] at h
  set β : ℕ → WA := fun i => if i = 0 then a0 else if i = N then a1 else
    if i = k then vk else if i = k + 1 then vk1 else if i = n then vn else
    d (walkColor c0 i) with hβdef
  have hβ0 : β 0 = a0 := by simp [β]
  have hβN : β N = a1 := by
    have h0 : ¬(N = 0) := by omega
    simp [β, h0]
  have hβk : β k = vk := by
    have h0 : ¬(k = 0) := by omega
    have hN : ¬(k = N) := by omega
    simp [β, h0, hN]
  have hβk1 : β (k + 1) = vk1 := by
    have h0 : ¬(k + 1 = 0) := by omega
    have hN : ¬(k + 1 = N) := by omega
    have hk' : ¬(k + 1 = k) := by omega
    simp [β, h0, hN, hk']
  have hβn : β n = vn := by
    have h0 : ¬(n = 0) := by omega
    have hN : ¬(n = N) := by omega
    have hk' : ¬(n = k) := by rw [hbase_len] at hk_lt; omega
    have hk1' : ¬(n = k + 1) := by omega
    simp [β, h0, hN, hk', hk1']
  have hβcol : ∀ i, colA (β i) = walkColor c0 i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [hβ0]
      simp [walkColor, c0]
    · by_cases hN : i = N
      · subst hN
        rw [hβN, hNval]
        exact hpar
      · by_cases hk' : i = k
        · subst hk'
          rw [hβk]
          exact hvk_col
        · by_cases hk1' : i = k + 1
          · subst hk1'
            rw [hβk1, hvk1_col, walkColor_succ]
          · by_cases hn' : i = n
            · subst hn'
              rw [hβn]
              exact hvn_col
            · have : β i = d (walkColor c0 i) := by
                simp [β, h0, hN, hk', hk1', hn']
              rw [this]
              exact hdcol _
  have hβconsec : ∀ i, colA (β i) ≠ colA (β (i + 1)) := by
    intro i
    rw [hβcol, hβcol, walkColor_succ]
    cases walkColor c0 i <;> simp
  -- the paired 2-cover of the doubled layer
  have h8 : vn ≠ a1 := fun h => hvn_a1 (h ▸ rfl)
  have h1 : colA vk ≠ colA vk1 := by
    rw [hvk_col, hvk1_col]
    cases walkColor c0 k <;> simp
  obtain ⟨pw, qw, hpw_path, hqw_path, hcov_all, hcov_disj⟩ :=
    hAspan vk vk1 vn a1 h1 hvn_a1 hvkvn hvka1 hvk1vn hvk1a1 hvv h8
  -- Hamilton paths for the single layers
  have hham : ∀ i, ∃ wk : A.Walk (β i) (β (i + 1)), wk.IsHamiltonian := fun i =>
    hAlace (β i) (β (i + 1)) (hβconsec i)
  choose ham hhamP using hham
  set pieces : ℕ → List WA := fun i =>
    if i = k then pw.support else if i = n then qw.support else (ham i).support
    with hpiecesdef
  have hpk : pieces k = pw.support := by simp [pieces]
  have hpn : pieces n = qw.support := by
    have hk' : ¬(n = k) := by rw [hbase_len] at hk_lt; omega
    simp [pieces, hk']
  have hpother : ∀ i, i ≠ k → i ≠ n → pieces i = (ham i).support := by
    intro i h1' h2'
    simp [pieces, h1', h2']
  -- uniqueness of the interior b1-occurrence
  have huniq : ∀ i (hi : i < base.length), base[i]'hi = b1 → i = k := by
    intro i hi hib
    exact hbase_nodup.getElem_inj_iff.mp (hib.trans hbase_k.symm)
  refine walk_assembly_core a0 a1 b0 b1 walkB β pieces hBc hBhead hBlast hβ0 hβN ?_ ?_ ?_
  · intro i hi
    by_cases hik : i = k
    · subst hik
      rw [hpk]
      refine ⟨pw.isChain_adj_support, hpw_path.support_nodup, pw.support_ne_nil, ?_, ?_⟩
      · rw [walk_support_head? pw, hβk]
      · rw [walk_support_getLast? pw, hβk1]
    · by_cases hin : i = n
      · subst hin
        rw [hpn]
        refine ⟨qw.isChain_adj_support, hqw_path.support_nodup, qw.support_ne_nil, ?_, ?_⟩
        · rw [walk_support_head? qw, hβn]
        · rw [walk_support_getLast? qw]
          have : n + 1 = N := hNval.symm
          rw [this, hβN]
      · rw [hpother i hik hin]
        exact ⟨(ham i).isChain_adj_support, (hhamP i).isPath.support_nodup,
          (ham i).support_ne_nil, walk_support_head? (ham i), walk_support_getLast? (ham i)⟩
  · intro i j hij hi hj heq
    have hjn : j ≤ n := by
      rw [hlen2] at hj
      omega
    rcases Nat.lt_or_ge j n with hjlt | hjge
    · -- both inside the nodup base: impossible
      exfalso
      have hib : i < base.length := by rw [hbase_len]; omega
      have hjb : j < base.length := by rw [hbase_len]; omega
      rw [hgetElem_lt i hib hi, hgetElem_lt j hjb hj] at heq
      have heqij := hbase_nodup.getElem_inj_iff.mp heq
      omega
    · -- j = n: the doubled layer; i must be its interior occurrence k
      have hjn' : j = n := by omega
      subst hjn'
      have hib : i < base.length := by rw [hbase_len]; omega
      rw [hgetElem_lt i hib hi, hgetElem_n hj] at heq
      have hik : i = k := huniq i hib heq
      subst hik
      rw [hpk, hpn]
      intro x hx hy
      exact hcov_disj x ⟨hx, hy⟩
  · intro a b
    by_cases hbb : b = b1
    · subst hbb
      rcases hcov_all a with hca | hca
      · refine ⟨k, by rw [hlen2]; omega, ?_, ?_⟩
        · rw [hgetElem_lt k hk_lt (by rw [hlen2]; omega)]
          exact hbase_k
        · rw [hpk]
          exact hca
      · refine ⟨n, by rw [hlen2]; omega, hgetElem_n _, by rw [hpn]; exact hca⟩
    · have hbmem : b ∈ base := by simpa [base] using hQ.mem_support b
      obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hbmem
      have hib? : base[i]? = some b := by
        rw [List.getElem?_eq_getElem hi]
        exact congrArg some hib
      have hik : i ≠ k := by
        intro h
        apply hbb
        have h2 := hib?
        rw [h] at h2
        exact Option.some.inj (h2.symm.trans hbase_k?)
      have hin : i ≠ n := by
        have h := hi
        rw [hbase_len] at h
        omega
      have hi' : i < walkB.length := by
        have h := hi
        rw [hbase_len] at h
        rw [hlen2]
        omega
      refine ⟨i, hi', ?_, ?_⟩
      · rw [hgetElem_lt i hi hi']
        exact hib
      · rw [hpother i hik hin]
        exact (hhamP i).mem_support a

/-- Two Booleans that differ: the other is the negation. -/
private theorem walkBool_ne_iff : ∀ a b : Bool, a ≠ b → a = !b := by decide

/-! ## Shape 3: a Hamilton cycle (same-layer endpoints, one doubled layer)

The Claim's `N = n + 1` closed walk based at `b₀`: a Hamilton path `b₀ → u` along a neighbor
`u` of `b₀`, closed by the edge `u b₀`. The layer of `b₀` is doubled (first and last), and
carries both pinned endpoints. -/

theorem walk_pass_cycle [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hAcard : 4 ≤ Fintype.card WA)
    (hBcard : 3 ≤ Fintype.card WB) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 : WB) (ha : a0 ≠ a1)
    (hpar : colA a1 = walkColor (colA a0) (Fintype.card WB + 1)) :
    HasHamPath (A □ B) (a0, b0) (a1, b0) := by
  classical
  set n : ℕ := Fintype.card WB with hndef
  have hnpos : 3 ≤ n := hBcard
  obtain ⟨u, hb0u, _⟩ := exists_adj_ne_of_hamConnected (B := B) hBcard hB b0 b0
  obtain ⟨P1, hP1⟩ := hB b0 u (B.ne_of_adj hb0u)
  set base : List WB := P1.support with hbasedef
  have hbase_nodup : base.Nodup := by simpa [base] using hP1.isPath.support_nodup
  have hbase_len : base.length = n := by simpa [base, n] using hP1.length_support
  have hbase_head : base.head? = some b0 := by simpa [base] using walk_support_head? P1
  have hbase_last : base.getLast? = some u := by simpa [base] using walk_support_getLast? P1
  set walkB : List WB := base ++ [b0] with hwalkBdef
  have hlen : walkB.length = n + 1 := by simp [walkB, hbase_len]
  have hbase_zero? : base[0]? = some b0 := by
    have h := hbase_head
    rwa [List.head?_eq_getElem?] at h
  have hbase_zero : base[0]'(by omega) = b0 := by
    have h := hbase_zero?
    rw [List.getElem?_eq_getElem (by omega : 0 < base.length)] at h
    exact Option.some.inj h
  have hBc : walkB.IsChain B.Adj := by
    exact P1.isChain_adj_support.append (by simp) (by
      intro x hx y hy
      rw [hbase_last] at hx
      simp at hx hy
      subst x
      subst y
      exact hb0u.symm)
  have hBhead : walkB.head? = some b0 := by
    simpa [walkB, List.head?_append, hbase_head]
  have hBlast : walkB.getLast? = some b0 := by
    simp [walkB]
  have hgetElem_lt : ∀ i (hi : i < base.length) (hi' : i < walkB.length),
      walkB[i]'hi' = base[i]'hi := by
    intro i hi hi'
    exact List.getElem_append_left hi
  have hgetElem_n? : walkB[n]? = some b0 := by
    have h : (base ++ [b0])[base.length]? = some b0 := by simp
    rw [hbase_len] at h
    exact h
  have hgetElem_n : ∀ (hn : n < walkB.length), walkB[n]'hn = b0 := by
    intro hn
    have h := hgetElem_n?
    rw [List.getElem?_eq_getElem hn] at h
    exact Option.some.inj h
  set c0 : Bool := colA a0 with hc0def
  obtain ⟨dT, hdT⟩ := hAsurj true
  obtain ⟨dF, hdF⟩ := hAsurj false
  set d : Bool → WA := fun c => if c then dT else dF with hddef
  have hdcol : ∀ c, colA (d c) = c := by
    intro c
    cases c <;> simp [d, hdT, hdF]
  obtain ⟨v1, hv1_col, hv1_a1⟩ :=
    walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (!c0) a1
  set tgt : WA := if colA a0 = walkColor c0 n then a0 else v1 with htgtdef
  obtain ⟨vn, hvn_col, hvn_tgt⟩ :=
    walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (walkColor c0 n) tgt
  have hvn_a1col : colA vn ≠ colA a1 := by
    rw [hvn_col, hpar, walkColor_succ]
    cases walkColor c0 n <;> simp
  have ha0_vn : a0 ≠ vn := by
    by_cases hc : colA a0 = walkColor c0 n
    · intro h
      apply hvn_tgt
      rw [← h]
      simp [tgt, hc]
    · intro h
      apply hc
      rw [h]
      exact hvn_col
  have hv1_vn : v1 ≠ vn := by
    by_cases hc : walkColor c0 n = !c0
    · intro h
      apply hvn_tgt
      rw [← h]
      have hc' : ¬(colA a0 = walkColor c0 n) := by
        rw [hc, hc0def]
        cases colA a0 <;> simp
      simp [tgt, hc']
    · intro h
      apply hc
      rw [← hvn_col, ← h, hv1_col]
  have h1 : colA a0 ≠ colA v1 := by
    rw [hv1_col, hc0def]
    cases colA a0 <;> simp
  have h7 : a0 ≠ v1 := fun h => h1 (h ▸ rfl)
  have h8 : vn ≠ a1 := fun h => hvn_a1col (h ▸ rfl)
  obtain ⟨pw, qw, hpw_path, hqw_path, hcov_all, hcov_disj⟩ :=
    hAspan a0 v1 vn a1 h1 hvn_a1col ha0_vn ha hv1_vn hv1_a1 h7 h8
  set N : ℕ := walkB.length with hNdef
  have hNval : N = n + 1 := hlen
  have hlen2 : walkB.length = n + 1 := hNdef.symm.trans hNval
  set β : ℕ → WA := fun i => if i = 0 then a0 else if i = N then a1 else
    if i = 1 then v1 else if i = n then vn else d (walkColor c0 i) with hβdef
  have hβ0 : β 0 = a0 := by simp [β]
  have hβN : β N = a1 := by
    have h0 : ¬(N = 0) := by omega
    simp [β, h0]
  have hβ1 : β 1 = v1 := by
    have h0 : ¬((1 : ℕ) = 0) := by omega
    have hN : ¬((1 : ℕ) = N) := by omega
    simp [β, h0, hN]
  have hβn : β n = vn := by
    have h0 : ¬(n = 0) := by omega
    have hN : ¬(n = N) := by omega
    have h1' : ¬(n = 1) := by omega
    simp [β, h0, hN, h1']
  have hβcol : ∀ i, colA (β i) = walkColor c0 i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [hβ0]
      simp [walkColor, c0]
    · by_cases hN : i = N
      · subst hN
        rw [hβN, hNval]
        exact hpar
      · by_cases h1' : i = 1
        · subst h1'
          rw [hβ1, hv1_col]
          simp [walkColor]
        · by_cases hn' : i = n
          · subst hn'
            rw [hβn]
            exact hvn_col
          · have hd' : β i = d (walkColor c0 i) := by
              simp [β, h0, hN, h1', hn']
            rw [hd']
            exact hdcol _
  have hβconsec : ∀ i, colA (β i) ≠ colA (β (i + 1)) := by
    intro i
    rw [hβcol, hβcol, walkColor_succ]
    cases walkColor c0 i <;> simp
  have hham : ∀ i, ∃ wk : A.Walk (β i) (β (i + 1)), wk.IsHamiltonian := fun i =>
    hAlace (β i) (β (i + 1)) (hβconsec i)
  choose ham hhamP using hham
  set pieces : ℕ → List WA := fun i =>
    if i = 0 then pw.support else if i = n then qw.support else (ham i).support
    with hpiecesdef
  have hpz : pieces 0 = pw.support := by simp [pieces]
  have hpn : pieces n = qw.support := by
    have h0 : ¬(n = 0) := by omega
    simp [pieces, h0]
  have hpother : ∀ i, i ≠ 0 → i ≠ n → pieces i = (ham i).support := by
    intro i ha' hb'
    simp [pieces, ha', hb']
  refine walk_assembly_core a0 a1 b0 b0 walkB β pieces hBc hBhead hBlast hβ0 hβN ?_ ?_ ?_
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [hpz]
      refine ⟨pw.isChain_adj_support, hpw_path.support_nodup, pw.support_ne_nil, ?_, ?_⟩
      · rw [walk_support_head? pw, hβ0]
      · rw [walk_support_getLast? pw, hβ1]
    · by_cases hin : i = n
      · subst hin
        rw [hpn]
        refine ⟨qw.isChain_adj_support, hqw_path.support_nodup, qw.support_ne_nil, ?_, ?_⟩
        · rw [walk_support_head? qw, hβn]
        · rw [walk_support_getLast? qw]
          have harith : n + 1 = N := hNval.symm
          rw [harith, hβN]
      · rw [hpother i hi0 hin]
        exact ⟨(ham i).isChain_adj_support, (hhamP i).isPath.support_nodup,
          (ham i).support_ne_nil, walk_support_head? (ham i), walk_support_getLast? (ham i)⟩
  · intro i j hij hi hj heq
    have hjn : j ≤ n := by
      rw [hlen2] at hj
      omega
    rcases Nat.lt_or_ge j n with hjlt | hjge
    · exfalso
      have hib : i < base.length := by rw [hbase_len]; omega
      have hjb : j < base.length := by rw [hbase_len]; omega
      rw [hgetElem_lt i hib hi, hgetElem_lt j hjb hj] at heq
      have heqij := hbase_nodup.getElem_inj_iff.mp heq
      omega
    · have hjn' : j = n := by omega
      subst hjn'
      have hib : i < base.length := by rw [hbase_len]; omega
      rw [hgetElem_lt i hib hi, hgetElem_n hj] at heq
      have hi0 : i = 0 := by
        have h := heq.trans hbase_zero.symm
        exact hbase_nodup.getElem_inj_iff.mp h
      subst hi0
      rw [hpz, hpn]
      intro x hx hy
      exact hcov_disj x ⟨hx, hy⟩
  · intro a b
    by_cases hbb : b = b0
    · subst hbb
      rcases hcov_all a with hca | hca
      · refine ⟨0, by omega, ?_, ?_⟩
        · rw [hgetElem_lt 0 (by omega) (by omega)]
          exact hbase_zero
        · rw [hpz]
          exact hca
      · refine ⟨n, by rw [hlen2]; omega, hgetElem_n _, by rw [hpn]; exact hca⟩
    · have hbmem : b ∈ base := by simpa [base] using hP1.mem_support b
      obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hbmem
      have hi0 : i ≠ 0 := by
        intro h
        apply hbb
        rw [← hib]
        subst h
        exact hbase_zero
      have hin : i ≠ n := by
        have h := hi
        rw [hbase_len] at h
        omega
      have hi' : i < walkB.length := by
        have h := hi
        rw [hbase_len] at h
        rw [hlen2]
        omega
      refine ⟨i, hi', ?_, ?_⟩
      · rw [hgetElem_lt i hi hi']
        exact hib
      · rw [hpother i hi0 hin]
        exact (hhamP i).mem_support a

/-! ## Shape 4: a Hamilton cycle with a two-edge detour (two doubled layers)

The Claim's `N = n + 2` closed walk based at `b₀`: a Hamilton path `b₀ → u'` where `u'` is a
neighbor of a neighbor `m` of `b₀`, closed by the edges `u' m` and `m b₀`. Both the layer of
`b₀` (first and last) and the layer of `m` (interior and second-to-last) are doubled; the
boundary between the two final pieces is the paper's SHARED boundary, and the choice order
below (`vsh` before `v1` before `vn` before the `m`-pair) is the refinement that keeps every
choice to a single same-color exclusion. -/

theorem walk_pass_cycle_detour [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hAcard : 4 ≤ Fintype.card WA)
    (hBcard : 3 ≤ Fintype.card WB) (hB : IsHamConnected B)
    (a0 a1 : WA) (b0 : WB) (ha : a0 ≠ a1)
    (hpar : colA a1 = walkColor (colA a0) (Fintype.card WB + 2)) :
    HasHamPath (A □ B) (a0, b0) (a1, b0) := by
  classical
  set n : ℕ := Fintype.card WB with hndef
  have hnpos : 3 ≤ n := hBcard
  obtain ⟨m, hb0m, _⟩ := exists_adj_ne_of_hamConnected (B := B) hBcard hB b0 b0
  have hmb0 : m ≠ b0 := (B.ne_of_adj hb0m).symm
  obtain ⟨R, hR⟩ := hB b0 m (B.ne_of_adj hb0m)
  have hRnil : ¬ R.Nil := walkHam_not_nil hR hBcard
  set u' : WB := R.penultimate with hu'def
  have hu'm : B.Adj u' m := R.adj_penultimate hRnil
  have hu'b0 : u' ≠ b0 := walkHam_penultimate_ne hR hBcard
  have hu'ne_m : u' ≠ m := B.ne_of_adj hu'm
  obtain ⟨P2, hP2⟩ := hB b0 u' (Ne.symm hu'b0)
  set base : List WB := P2.support with hbasedef
  have hbase_nodup : base.Nodup := by simpa [base] using hP2.isPath.support_nodup
  have hbase_len : base.length = n := by simpa [base, n] using hP2.length_support
  have hbase_head : base.head? = some b0 := by simpa [base] using walk_support_head? P2
  have hbase_last : base.getLast? = some u' := by simpa [base] using walk_support_getLast? P2
  set walkB : List WB := base ++ [m, b0] with hwalkBdef
  have hlen : walkB.length = n + 2 := by simp [walkB, hbase_len]
  have hbase_zero? : base[0]? = some b0 := by
    have h := hbase_head
    rwa [List.head?_eq_getElem?] at h
  have hbase_zero : base[0]'(by omega) = b0 := by
    have h := hbase_zero?
    rw [List.getElem?_eq_getElem (by omega : 0 < base.length)] at h
    exact Option.some.inj h
  have hbase_last? : base[base.length - 1]? = some u' := by
    have h := hbase_last
    rwa [List.getLast?_eq_getElem?] at h
  -- the interior occurrence of m
  have hm_mem : m ∈ base := by simpa [base] using hP2.mem_support m
  set k : ℕ := base.idxOf m with hkdef
  have hk_lt : k < base.length := by simpa [k] using List.idxOf_lt_length_of_mem hm_mem
  have hbase_k : base[k]'hk_lt = m := by
    simpa [k] using List.getElem_idxOf (l := base) (x := m) hk_lt
  have hbase_k? : base[k]? = some m := by
    rw [List.getElem?_eq_getElem hk_lt]
    exact congrArg some hbase_k
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      apply hmb0
      have h1 : base[0]? = some m := by
        rw [← h0]
        exact hbase_k?
      exact (Option.some.inj (hbase_zero?.symm.trans h1)).symm
    · exact h
  have hk_ne_last : k ≠ base.length - 1 := by
    intro h
    apply hu'ne_m
    have h1 : base[base.length - 1]? = some m := by
      rw [← h]
      exact hbase_k?
    exact Option.some.inj (hbase_last?.symm.trans h1)
  have hkn : k < n := by
    have h := hk_lt
    rwa [hbase_len] at h
  have hk_le : k + 1 ≤ n - 1 := by
    have h1 := hk_lt
    have h2 := hk_ne_last
    rw [hbase_len] at h1 h2
    omega
  -- walk facts
  have hBc : walkB.IsChain B.Adj := by
    exact P2.isChain_adj_support.append (by simpa using hb0m.symm) (by
      intro x hx y hy
      rw [hbase_last] at hx
      simp at hx hy
      subst x
      subst y
      exact hu'm)
  have hBhead : walkB.head? = some b0 := by
    simpa [walkB, List.head?_append, hbase_head]
  have hBlast : walkB.getLast? = some b0 := by
    simp [walkB]
  have hgetElem_lt : ∀ i (hi : i < base.length) (hi' : i < walkB.length),
      walkB[i]'hi' = base[i]'hi := by
    intro i hi hi'
    exact List.getElem_append_left hi
  have hgetElem_n? : walkB[n]? = some m := by
    have h : (base ++ [m, b0])[base.length]? = some m := by
      rw [List.getElem?_append_right (le_refl base.length)]
      simp
    rw [hbase_len] at h
    exact h
  have hgetElem_n : ∀ (hn : n < walkB.length), walkB[n]'hn = m := by
    intro hn
    have h := hgetElem_n?
    rw [List.getElem?_eq_getElem hn] at h
    exact Option.some.inj h
  have hgetElem_n1? : walkB[n + 1]? = some b0 := by
    have h : (base ++ [m, b0])[base.length + 1]? = some b0 := by
      rw [List.getElem?_append_right (by omega)]
      simp
    rw [hbase_len] at h
    exact h
  have hgetElem_n1 : ∀ (hn : n + 1 < walkB.length), walkB[n + 1]'hn = b0 := by
    intro hn
    have h := hgetElem_n1?
    rw [List.getElem?_eq_getElem hn] at h
    exact Option.some.inj h
  -- boundary pass (the paper's choice order: shared boundary first)
  set c0 : Bool := colA a0 with hc0def
  obtain ⟨dT, hdT⟩ := hAsurj true
  obtain ⟨dF, hdF⟩ := hAsurj false
  set d : Bool → WA := fun c => if c then dT else dF with hddef
  have hdcol : ∀ c, colA (d c) = c := by
    intro c
    cases c <;> simp [d, hdT, hdF]
  have hcol_n2 : walkColor c0 (n + 2) = colA a1 := hpar.symm
  have hcol_n1 : walkColor c0 (n + 1) = !(colA a1) := by
    have h := walkColor_succ c0 (n + 1)
    rw [hcol_n2] at h
    cases hca : colA a1 <;> cases hwc : walkColor c0 (n + 1) <;> simp_all
  obtain ⟨vsh, hvsh_col, hvsh_a0⟩ :=
    walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (walkColor c0 (n + 1)) a0
  set tgt1 : WA := if colA a1 = !c0 then a1 else vsh with htgt1def
  obtain ⟨v1, hv1_col, hv1_tgt1⟩ :=
    walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (!c0) tgt1
  obtain ⟨vn, hvn_col, hvn_v1⟩ :=
    walk_pick_color_ne (A := A) hAbip hAsurj hAlace hAcard (walkColor c0 n) v1
  have hvn_vsh_col : colA vn ≠ colA vsh := by
    rw [hvn_col, hvsh_col, walkColor_succ]
    cases walkColor c0 n <;> simp
  obtain ⟨vk, vk1, hvk_col, hvk1_col, hvkk1, hvk_vn, hvk_vsh, hvk1_vn, hvk1_vsh⟩ :=
    walk_pick_terminals (A := A) hAbip hAsurj hAlace hAcard (walkColor c0 k) vn vsh hvn_vsh_col
  -- the b0-layer disequalities
  have hbne : ∀ b : Bool, b ≠ !b := by decide
  have hv1_vsh : v1 ≠ vsh := by
    by_cases hc : colA a1 = !c0
    · intro h
      have h1 : colA vsh = c0 := by
        rw [hvsh_col, hcol_n1, hc]
        exact Bool.not_not c0
      rw [← h] at h1
      exact hbne c0 (h1.symm.trans hv1_col)
    · intro h
      apply hv1_tgt1
      rw [h]
      simp [tgt1, hc]
  have hv1_a1 : v1 ≠ a1 := by
    by_cases hc : colA a1 = !c0
    · intro h
      apply hv1_tgt1
      rw [h]
      simp [tgt1, hc]
    · intro h
      apply hc
      rw [← h]
      exact hv1_col
  have ha0_vsh : a0 ≠ vsh := Ne.symm hvsh_a0
  -- the m-layer values: ak is what β k evaluates to
  set ak : WA := if k = 1 then v1 else vk with hakdef
  have hak_col : colA ak = walkColor c0 k := by
    by_cases hk1 : k = 1
    · rw [hakdef, if_pos hk1, hv1_col, hk1]
      simp [walkColor]
    · rw [hakdef, if_neg hk1]
      exact hvk_col
  have hak_vn : ak ≠ vn := by
    by_cases hk1 : k = 1
    · rw [hakdef, if_pos hk1]
      exact Ne.symm hvn_v1
    · rw [hakdef, if_neg hk1]
      exact hvk_vn
  have hak_vsh : ak ≠ vsh := by
    by_cases hk1 : k = 1
    · rw [hakdef, if_pos hk1]
      exact hv1_vsh
    · rw [hakdef, if_neg hk1]
      exact hvk_vsh
  -- the two paired 2-covers
  have hb01 : colA a0 ≠ colA v1 := by
    rw [hv1_col, hc0def]
    cases colA a0 <;> simp
  have hb02 : colA vsh ≠ colA a1 := by
    rw [hvsh_col, hcol_n1]
    cases colA a1 <;> simp
  have hb07 : a0 ≠ v1 := fun h => hb01 (h ▸ rfl)
  have hb08 : vsh ≠ a1 := fun h => hb02 (h ▸ rfl)
  obtain ⟨p0, q0, hp0_path, hq0_path, hcov0_all, hcov0_disj⟩ :=
    hAspan a0 v1 vsh a1 hb01 hb02 ha0_vsh ha hv1_vsh hv1_a1 hb07 hb08
  have hm1 : colA ak ≠ colA vk1 := by
    rw [hak_col, hvk1_col]
    cases walkColor c0 k <;> simp
  have hm7 : ak ≠ vk1 := fun h => hm1 (h ▸ rfl)
  have hm8 : vn ≠ vsh := fun h => hvn_vsh_col (h ▸ rfl)
  obtain ⟨p1, q1, hp1_path, hq1_path, hcov1_all, hcov1_disj⟩ :=
    hAspan ak vk1 vn vsh hm1 hvn_vsh_col hak_vn hak_vsh hvk1_vn hvk1_vsh hm7 hm8
  -- the boundary assignment
  set N : ℕ := walkB.length with hNdef
  have hNval : N = n + 2 := hlen
  have hlen2 : walkB.length = n + 2 := hNdef.symm.trans hNval
  set β : ℕ → WA := fun i => if i = 0 then a0 else if i = N then a1 else
    if i = 1 then v1 else if i = n + 1 then vsh else if i = n then vn else
    if i = k then vk else if i = k + 1 then vk1 else d (walkColor c0 i) with hβdef
  have hβ0 : β 0 = a0 := by simp [β]
  have hβN : β N = a1 := by
    have h0 : ¬(N = 0) := by omega
    simp [β, h0]
  have hβ1 : β 1 = v1 := by
    have h0 : ¬((1 : ℕ) = 0) := by omega
    have hN : ¬((1 : ℕ) = N) := by omega
    simp [β, h0, hN]
  have hβn1 : β (n + 1) = vsh := by
    have h0 : ¬(n + 1 = 0) := by omega
    have hN : ¬(n + 1 = N) := by omega
    have h1' : ¬(n = 0) := by omega
    simp [β, h0, hN, h1']
  have hβn : β n = vn := by
    have h0 : ¬(n = 0) := by omega
    have hN : ¬(n = N) := by omega
    have h1' : ¬(n = 1) := by omega
    have hn1' : ¬(n = n + 1) := by omega
    simp [β, h0, hN, h1', hn1']
  have hβk : β k = ak := by
    by_cases hk1 : k = 1
    · rw [hakdef, if_pos hk1, hk1]
      exact hβ1
    · have h0 : ¬(k = 0) := by omega
      have hN : ¬(k = N) := by omega
      have hn1' : ¬(k = n + 1) := by omega
      have hn' : ¬(k = n) := by omega
      rw [hakdef, if_neg hk1]
      simp [β, h0, hN, hk1, hn1', hn']
  have hβk1 : β (k + 1) = vk1 := by
    have h0 : ¬(k + 1 = 0) := by omega
    have hN : ¬(k + 1 = N) := by omega
    have h1' : ¬(k = 0) := by omega
    have hn1' : ¬(k = n) := by omega
    have hn' : ¬(k + 1 = n) := by
      have := hk_le
      omega
    have hk' : ¬(k + 1 = k) := by omega
    simp [β, h0, hN, h1', hn1', hn', hk']
  have hβcol : ∀ i, colA (β i) = walkColor c0 i := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [hβ0]
      simp [walkColor, c0]
    · by_cases hN : i = N
      · subst hN
        rw [hβN, hNval]
        exact hpar
      · by_cases h1' : i = 1
        · subst h1'
          rw [hβ1, hv1_col]
          simp [walkColor]
        · by_cases hn1' : i = n + 1
          · subst hn1'
            rw [hβn1]
            exact hvsh_col
          · by_cases hn' : i = n
            · subst hn'
              rw [hβn]
              exact hvn_col
            · by_cases hk' : i = k
              · subst hk'
                rw [hβk]
                exact hak_col
              · by_cases hk1' : i = k + 1
                · subst hk1'
                  rw [hβk1, hvk1_col, walkColor_succ]
                · have hd' : β i = d (walkColor c0 i) := by
                    simp [β, h0, hN, h1', hn1', hn', hk', hk1']
                  rw [hd']
                  exact hdcol _
  have hβconsec : ∀ i, colA (β i) ≠ colA (β (i + 1)) := by
    intro i
    rw [hβcol, hβcol, walkColor_succ]
    cases walkColor c0 i <;> simp
  have hham : ∀ i, ∃ wk : A.Walk (β i) (β (i + 1)), wk.IsHamiltonian := fun i =>
    hAlace (β i) (β (i + 1)) (hβconsec i)
  choose ham hhamP using hham
  set pieces : ℕ → List WA := fun i =>
    if i = 0 then p0.support else if i = n + 1 then q0.support else
    if i = k then p1.support else if i = n then q1.support else (ham i).support
    with hpiecesdef
  have hpz : pieces 0 = p0.support := by simp [pieces]
  have hpn1 : pieces (n + 1) = q0.support := by
    have h0 : ¬(n + 1 = 0) := by omega
    simp [pieces, h0]
  have hpk : pieces k = p1.support := by
    have h0 : ¬(k = 0) := by omega
    have h1' : ¬(k = n + 1) := by omega
    simp [pieces, h0, h1']
  have hpn : pieces n = q1.support := by
    have h0 : ¬(n = 0) := by omega
    have h1' : ¬(n = n + 1) := by omega
    have hk' : ¬(n = k) := by omega
    simp [pieces, h0, h1', hk']
  have hpother : ∀ i, i ≠ 0 → i ≠ n + 1 → i ≠ k → i ≠ n → pieces i = (ham i).support := by
    intro i h1' h2' h3' h4'
    simp [pieces, h1', h2', h3', h4']
  -- occurrence uniqueness in the base
  have huniq_b0 : ∀ i (hi : i < base.length), base[i]'hi = b0 → i = 0 := by
    intro i hi hib
    exact hbase_nodup.getElem_inj_iff.mp (hib.trans hbase_zero.symm)
  have huniq_m : ∀ i (hi : i < base.length), base[i]'hi = m → i = k := by
    intro i hi hib
    exact hbase_nodup.getElem_inj_iff.mp (hib.trans hbase_k.symm)
  refine walk_assembly_core a0 a1 b0 b0 walkB β pieces hBc hBhead hBlast hβ0 hβN ?_ ?_ ?_
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [hpz]
      refine ⟨p0.isChain_adj_support, hp0_path.support_nodup, p0.support_ne_nil, ?_, ?_⟩
      · rw [walk_support_head? p0, hβ0]
      · rw [walk_support_getLast? p0, hβ1]
    · by_cases hin1 : i = n + 1
      · subst hin1
        rw [hpn1]
        refine ⟨q0.isChain_adj_support, hq0_path.support_nodup, q0.support_ne_nil, ?_, ?_⟩
        · rw [walk_support_head? q0, hβn1]
        · rw [walk_support_getLast? q0]
          have harith : n + 1 + 1 = N := by omega
          rw [harith, hβN]
      · by_cases hik : i = k
        · subst hik
          rw [hpk]
          refine ⟨p1.isChain_adj_support, hp1_path.support_nodup, p1.support_ne_nil, ?_, ?_⟩
          · rw [walk_support_head? p1, hβk]
          · rw [walk_support_getLast? p1, hβk1]
        · by_cases hin : i = n
          · subst hin
            rw [hpn]
            refine ⟨q1.isChain_adj_support, hq1_path.support_nodup, q1.support_ne_nil, ?_, ?_⟩
            · rw [walk_support_head? q1, hβn]
            · rw [walk_support_getLast? q1, hβn1]
          · rw [hpother i hi0 hin1 hik hin]
            exact ⟨(ham i).isChain_adj_support, (hhamP i).isPath.support_nodup,
              (ham i).support_ne_nil, walk_support_head? (ham i), walk_support_getLast? (ham i)⟩
  · intro i j hij hi hj heq
    have hjn : j ≤ n + 1 := by
      rw [hlen2] at hj
      omega
    rcases Nat.lt_or_ge j n with hjlt | hjge
    · exfalso
      have hib : i < base.length := by rw [hbase_len]; omega
      have hjb : j < base.length := by rw [hbase_len]; omega
      rw [hgetElem_lt i hib hi, hgetElem_lt j hjb hj] at heq
      have heqij := hbase_nodup.getElem_inj_iff.mp heq
      omega
    · rcases Nat.eq_or_lt_of_le hjge with hjn' | hjgt
      · -- j = n: the m layer
        have hjn'' : j = n := hjn'.symm
        subst hjn''
        have hib : i < base.length := by rw [hbase_len]; omega
        rw [hgetElem_lt i hib hi, hgetElem_n hj] at heq
        have hik : i = k := huniq_m i hib heq
        subst hik
        rw [hpk, hpn]
        intro x hx hy
        exact hcov1_disj x ⟨hx, hy⟩
      · -- j = n + 1: the b0 layer
        have hjn'' : j = n + 1 := by omega
        subst hjn''
        rcases Nat.lt_or_ge i n with hilt | hige
        · have hib : i < base.length := by rw [hbase_len]; omega
          rw [hgetElem_lt i hib hi, hgetElem_n1 hj] at heq
          have hi0 : i = 0 := huniq_b0 i hib heq
          subst hi0
          rw [hpz, hpn1]
          intro x hx hy
          exact hcov0_disj x ⟨hx, hy⟩
        · -- i = n: layers m and b0 differ
          exfalso
          have hin : i = n := by omega
          subst hin
          rw [hgetElem_n hi, hgetElem_n1 hj] at heq
          exact hmb0 heq
  · intro a b
    by_cases hbm : b = m
    · subst hbm
      rcases hcov1_all a with hca | hca
      · refine ⟨k, by rw [hlen2]; omega, ?_, ?_⟩
        · rw [hgetElem_lt k hk_lt (by rw [hlen2]; omega)]
          exact hbase_k
        · rw [hpk]
          exact hca
      · refine ⟨n, by rw [hlen2]; omega, hgetElem_n _, by rw [hpn]; exact hca⟩
    · by_cases hbb : b = b0
      · subst hbb
        rcases hcov0_all a with hca | hca
        · refine ⟨0, by rw [hlen2]; omega, ?_, ?_⟩
          · rw [hgetElem_lt 0 (by omega) (by rw [hlen2]; omega)]
            exact hbase_zero
          · rw [hpz]
            exact hca
        · refine ⟨n + 1, by rw [hlen2]; omega, hgetElem_n1 _, by rw [hpn1]; exact hca⟩
      · have hbmem : b ∈ base := by simpa [base] using hP2.mem_support b
        obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hbmem
        have hi0 : i ≠ 0 := by
          intro h
          apply hbb
          rw [← hib]
          subst h
          exact hbase_zero
        have hik : i ≠ k := by
          intro h
          apply hbm
          rw [← hib]
          subst h
          exact hbase_k
        have hin : i ≠ n := by
          have h := hi
          rw [hbase_len] at h
          omega
        have hin1 : i ≠ n + 1 := by
          have h := hi
          rw [hbase_len] at h
          omega
        have hi' : i < walkB.length := by
          have h := hi
          rw [hbase_len] at h
          rw [hlen2]
          omega
        refine ⟨i, hi', ?_, ?_⟩
        · rw [hgetElem_lt i hi hi']
          exact hib
        · rw [hpother i hi0 hin1 hik hin]
          exact (hhamP i).mem_support a

/-! ## Proposition 4.1, as printed

The Claim supplies walks of both parities of the occurrence count `N`; the telescoping
constraint `χ(a₁) = walkColor (χ(a₀)) N` selects one. Distinct layers use `N = n` (a Hamilton
path) or `N = n + 1` (path plus closing edge); coinciding layers use `N = n + 1` (cycle) or
`N = n + 2` (cycle with detour). -/

theorem boxProd_hamConn_one_bip_walk [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hAcard : 4 ≤ Fintype.card WA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B) :
    IsHamConnected (A □ B) := by
  classical
  have hBcard : 3 ≤ Fintype.card WB := card_ge_three_of_not_bip (A := B) hBnb
  rintro ⟨a0, b0⟩ ⟨a1, b1⟩ huv
  by_cases hbb : b0 = b1
  · subst hbb
    have ha : a0 ≠ a1 := fun h => huv (by rw [h])
    by_cases hpar : colA a1 = walkColor (colA a0) (Fintype.card WB + 1)
    · exact walk_pass_cycle hAbip hAsurj hAlace hAspan hAcard hBcard hB a0 a1 b0 ha hpar
    · have hpar2 : colA a1 = walkColor (colA a0) (Fintype.card WB + 2) := by
        have h := walkBool_ne_iff _ _ hpar
        rw [h, ← walkColor_succ]
      exact walk_pass_cycle_detour hAbip hAsurj hAlace hAspan hAcard hBcard hB a0 a1 b0 ha hpar2
  · by_cases hpar : colA a1 = walkColor (colA a0) (Fintype.card WB)
    · obtain ⟨P, hP⟩ := hB b0 b1 hbb
      refine walk_pass_hamPath hAsurj hAlace a0 a1 P hP ?_
      have hslen : P.support.length = Fintype.card WB := by
        rw [SimpleGraph.Walk.length_support, hP.length_eq]
        omega
      rw [hslen]
      exact hpar
    · have hpar2 : colA a1 = walkColor (colA a0) (Fintype.card WB + 1) := by
        have h := walkBool_ne_iff _ _ hpar
        rw [h, ← walkColor_succ]
      exact walk_pass_plus_edge hAbip hAsurj hAlace hAspan hAcard hBcard hB a0 a1 hbb hpar2

/-- The one-bipartite-factor branch, the paper's way: the `K₂` prism case is handled
    separately (as in the paper), and everything else is Proposition 4.1 via the walk device. -/
theorem boxProd_hamConn_one_bip_paper [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    {colA : WA → Bool} (hAbip : IsProper2Coloring A colA) (hAsurj : Function.Surjective colA)
    (hAlace : IsHamLaceable A colA) (hAspan : IsSpanning2DPCOpposite A colA)
    (hBnb : ¬ ∃ col, IsProper2Coloring B col) (hB : IsHamConnected B) :
    IsHamConnected (A □ B) := by
  classical
  by_cases hcard : Fintype.card WA = 2
  · intro u v huv
    exact (boxProd_prism_card_two (A := A) (B := B) hcard hAsurj hAlace hBnb hB) u v huv
  · have hAeven : Even (Fintype.card WA) :=
      even_card_of_bip_laceable_surj (A := A) hAbip hAsurj hAlace
    have hge2 : 2 ≤ Fintype.card WA := by
      have h := Fintype.card_le_of_surjective colA hAsurj
      simpa [Fintype.card_bool] using h
    have hge4 : 4 ≤ Fintype.card WA := by
      rcases hAeven with ⟨k, hk⟩
      omega
    exact boxProd_hamConn_one_bip_walk hAbip hAsurj hAlace hAspan hge4 hBnb hB

/-- **§4 as printed** — the same statement as `boxProd_hamConnected`, with the mixed branch
    carried by the paper's walk-device proof of Proposition 4.1. The mainline absorber route
    (`boxProd_hamConn_one_bip`) remains in `Sec4.lean` as the independent alternate. -/
theorem boxProd_hamConnected_paper [Fintype WA] [Fintype WB] [DecidableEq WA] [DecidableEq WB]
    (hA : FactorReady A) (hB : FactorReady B)
    (hnb : ¬ ∃ col, IsProper2Coloring (A □ B) col) :
    IsHamConnected (A □ B) := by
  rcases hA with ⟨hAnb, hAconn⟩ | ⟨cA, hAbip, hAsurj, hAlace, hAspan⟩
  · rcases hB with ⟨hBnb, hBconn⟩ | ⟨cB, hBbip, hBsurj, hBlace, hBspan⟩
    · exact boxProd_hamConn_both_nonbip hAnb hBnb hAconn hBconn
    · exact isHamConnected_iso (SimpleGraph.boxProdComm A B)
        (boxProd_hamConn_one_bip_paper hBbip hBsurj hBlace hBspan hAnb hAconn)
  · rcases hB with ⟨hBnb, hBconn⟩ | ⟨cB, hBbip, hBsurj, hBlace, hBspan⟩
    · exact boxProd_hamConn_one_bip_paper hAbip hAsurj hAlace hAspan hBnb hBconn
    · exact absurd ⟨fun p => Bool.xor (cA p.1) (cB p.2), boxProd_proper_color hAbip hBbip⟩ hnb

end Brualdi.Ledger
