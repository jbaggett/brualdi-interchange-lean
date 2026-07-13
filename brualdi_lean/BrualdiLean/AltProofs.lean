/-
# AltProofs — the §4 Claim, machine-checked as printed

ARCHITECTURE NOTE (2026-07-05, Jeff's call): the MAINLINE proofs now follow the paper's
printed arguments wherever both exist — `rowPattern_baseFamily` (Lemma 5.3) is proved in
`Sec5.lean` by the paper's Gale-Ryser/deficient-set argument (on top of the self-contained
`GaleRyser.lean`), and `rowQuotient_nonbip` (Lemma 5.12) by the paper's lexicographic
compression walk. The development's original independent arguments are KEPT as named
alternates in `Sec5.lean` (`rowPattern_baseFamily_minpair`, `rowQuotient_nonbip_rankmin`),
so both proofs of each lemma stay machine-checked (deliberate two-proof redundancy).

This file carries what remains outside the mainline: the paper's §4 **Claim (controlled
spanning walks)**, machine-checked exactly as printed. Proposition 4.1 itself is
machine-checked by the mainline absorber construction (Sec4), whose walks are the very
shapes this Claim produces; only §4's boundary-assignment/splice presentation remains
prose-only. Nothing in this file enters `brualdi_MH`'s trace, and everything here is
foundations-only (`#print axioms`).
-/
import BrualdiLean.Sec5

namespace Brualdi.Ledger

/-! ## The §4 Claim (controlled spanning walks), the paper's walk device

The paper proves Proposition 4.1 by threading layers along a spanning walk of `B` whose
occurrence count has a prescribed parity; the mainline Lean proves the same proposition by
the absorber construction instead, so the walk presentation is prose-only. The self-contained
graph-theoretic heart of that presentation is the Claim below: a Hamilton-connected graph on
at least three vertices has spanning walks between any two prescribed endpoints that visit
every vertex at most twice and realize BOTH parities of the occurrence count — `n` and `n+1`
for distinct endpoints, `n+1` and `n+2` for coinciding ones. This mechanizes the Claim exactly
as printed (the degree facts the paper gets from 2-connectedness come here from the
penultimate vertex of a Hamilton path, which is the paper's own construction one line later).
-/

/-- The penultimate vertex of a Hamilton path avoids the start (three or more vertices). -/
private theorem alt_ham_penultimate_ne {V : Type u} [DecidableEq V] [Fintype V]
    {B : SimpleGraph V} {s t : V} {P : B.Walk s t} (hP : P.IsHamiltonian)
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

/-- A Hamiltonian walk is not nil when the graph has at least three vertices. -/
private theorem alt_ham_not_nil {V : Type u} [DecidableEq V] [Fintype V]
    {B : SimpleGraph V} {s t : V} {P : B.Walk s t} (hP : P.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) : ¬ P.Nil := by
  intro hnil
  have hlen : P.length = Fintype.card V - 1 := hP.length_eq
  have := SimpleGraph.Walk.nil_iff_length_eq.mp hnil
  omega

/-- Support facts for a Hamiltonian walk extended by one edge. -/
private theorem alt_concat_facts {V : Type u} [DecidableEq V] [Fintype V]
    {B : SimpleGraph V} {s w x : V} {P : B.Walk s w} (hP : P.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) (h : B.Adj w x) :
    (∀ v, v ∈ (P.concat h).support) ∧ (∀ v, (P.concat h).support.count v ≤ 2) ∧
      (P.concat h).support.length = Fintype.card V + 1 := by
  have hsupp : (P.concat h).support = P.support ++ [x] :=
    SimpleGraph.Walk.support_concat P h
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [hsupp, List.mem_append]
    exact Or.inl (hP.mem_support v)
  · intro v
    rw [hsupp, List.count_append]
    have h1 : P.support.count v = 1 := hP v
    have h2 : List.count v [x] ≤ 1 := by
      calc List.count v [x] ≤ [x].length := List.count_le_length
        _ = 1 := rfl
    omega
  · have h1 : P.support.length = Fintype.card V := by
      rw [SimpleGraph.Walk.length_support, hP.length_eq]
      omega
    rw [hsupp, List.length_append, h1]
    rfl

/-- **The paper's §4 Claim (controlled spanning walks), machine-checked as printed.**
    A Hamilton-connected graph on `n ≥ 3` vertices has, for every `s, t`, spanning walks
    from `s` to `t` visiting every vertex at most twice and realizing both parities of the
    occurrence count: `N = n, n+1` when `s ≠ t`, and `N = n+1, n+2` when `s = t`. -/
theorem controlled_spanning_walks {V : Type u} [DecidableEq V] [Fintype V]
    {B : SimpleGraph V} (hHC : IsHamConnected B) (hcard : 3 ≤ Fintype.card V)
    (s t : V) :
    ∃ W₁ W₂ : B.Walk s t,
      (∀ v, v ∈ W₁.support) ∧ (∀ v, W₁.support.count v ≤ 2) ∧
      (∀ v, v ∈ W₂.support) ∧ (∀ v, W₂.support.count v ≤ 2) ∧
      W₂.support.length = W₁.support.length + 1 ∧
      W₁.support.length = (if s = t then Fintype.card V + 1 else Fintype.card V) := by
  classical
  by_cases hst : s = t
  · -- closed walks: a Hamilton cycle through s (N = n+1), then with one extra detour (N = n+2)
    subst hst
    -- a neighbor u of s, from the second vertex of any Hamilton path out of s
    obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
    obtain ⟨P₀, hP₀⟩ := hHC s x (Ne.symm hx)
    have hP₀nil : ¬ P₀.Nil := alt_ham_not_nil hP₀ hcard
    have hAdj_su : B.Adj s P₀.snd := P₀.adj_snd hP₀nil
    set u := P₀.snd with hudef
    have hsu : s ≠ u := B.ne_of_adj hAdj_su
    -- W₁: Hamilton path s → u closed by the edge u–s
    obtain ⟨P₁, hP₁⟩ := hHC s u hsu
    have hW₁ := alt_concat_facts hP₁ hcard hAdj_su.symm
    -- a neighbor u' ≠ s of u, from the penultimate vertex of a Hamilton path s → u
    have hu'Adj : B.Adj P₁.penultimate u := P₁.adj_penultimate (alt_ham_not_nil hP₁ hcard)
    set u' := P₁.penultimate with hu'def
    have hu's : u' ≠ s := alt_ham_penultimate_ne hP₁ hcard
    -- W₂: Hamilton path s → u' closed by the edges u'–u and u–s
    obtain ⟨P₂, hP₂⟩ := hHC s u' (Ne.symm hu's)
    have hmid := alt_concat_facts hP₂ hcard hu'Adj
    have hsupp₂ : ((P₂.concat hu'Adj).concat hAdj_su.symm).support =
        (P₂.concat hu'Adj).support ++ [s] :=
      SimpleGraph.Walk.support_concat _ _
    refine ⟨P₁.concat hAdj_su.symm, (P₂.concat hu'Adj).concat hAdj_su.symm,
      hW₁.1, hW₁.2.1, ?_, ?_, ?_, ?_⟩
    · intro v
      rw [hsupp₂, List.mem_append]
      exact Or.inl (hmid.1 v)
    · intro v
      rw [hsupp₂, List.count_append]
      have h1 : (P₂.concat hu'Adj).support.count v ≤ 2 := hmid.2.1 v
      have h1' : (P₂.concat hu'Adj).support = P₂.support ++ [u] :=
        SimpleGraph.Walk.support_concat P₂ hu'Adj
      have h2 : List.count v [s] ≤ 1 := by
        calc List.count v [s] ≤ [s].length := List.count_le_length
          _ = 1 := rfl
      by_cases hv : v = s
      · -- s occurs once in P₂ and not as the appended u (u ≠ s)
        have hcount : (P₂.concat hu'Adj).support.count v = 1 := by
          rw [h1', List.count_append]
          have hs1 : P₂.support.count v = 1 := by rw [hv]; exact hP₂ s
          have hs2 : List.count v [u] = 0 := by
            refine List.count_eq_zero_of_not_mem ?_
            simp only [List.mem_singleton, hv]
            exact hsu
          omega
        omega
      · have : List.count v [s] = 0 :=
          List.count_eq_zero_of_not_mem (by simp [hv])
        omega
    · rw [hsupp₂, List.length_append, hmid.2.2, hW₁.2.2]
      rfl
    · rw [hW₁.2.2]
      simp
  · -- open walks: a Hamilton path (N = n), then one with a detour through t (N = n+1)
    obtain ⟨P, hP⟩ := hHC s t hst
    have hlen₁ : P.support.length = Fintype.card V := by
      rw [SimpleGraph.Walk.length_support, hP.length_eq]
      omega
    -- the penultimate vertex w of P: a neighbor of t distinct from s and t
    have hwAdj : B.Adj P.penultimate t := P.adj_penultimate (alt_ham_not_nil hP hcard)
    set w := P.penultimate with hwdef
    have hws : w ≠ s := alt_ham_penultimate_ne hP hcard
    -- W₂: Hamilton path s → w followed by the edge w–t
    obtain ⟨Q, hQ⟩ := hHC s w (Ne.symm hws)
    have hW₂ := alt_concat_facts hQ hcard hwAdj
    refine ⟨P, Q.concat hwAdj, ?_, ?_, hW₂.1, hW₂.2.1, ?_, ?_⟩
    · intro v
      exact hP.mem_support v
    · intro v
      have := hP v
      omega
    · rw [hW₂.2.2, hlen₁]
    · rw [if_neg hst]
      exact hlen₁

end Brualdi.Ledger
