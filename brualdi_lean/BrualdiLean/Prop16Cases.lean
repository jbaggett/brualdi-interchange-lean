/-
Prop16Cases.lean — Tier 3: the case analysis of Coleman et al. 2025, Proposition 1.6.

Case 1 (`prop16_case1`): every copy meets at most `n − 1` pairs. Within-copy pairs are
covered inside their copy; split pairs route source copy → matching edge → target copy
through greedily chosen connectors (`weld_greedy`); every touched copy is exactly
partitioned by one inner `w_j`-PDPC (`inner_family`); Lemma 2.1 (`weld_lemma21`) absorbs
the untouched copies.

Case 2 (`prop16_case2`): all terminals in one copy — subcases (i)/(ii) reroute around the
extra terminals through Hamilton bridges of one or two fresh copies.

Case 3 (`prop16_case3`): all sources in copy `j1`, all targets in copy `j2 ≠ j1` — split
the source-carrier at the last source and the target-carrier at the last target; rejoin
the freed cut ends through a Hamilton bridge of a fresh copy `j3`, and route the last
pair through a Hamilton bridge of a second fresh copy `j4`. The two special carrier
indices are handled independently (the paper's double WLOG conflates them).

Case 4 (`prop16_case4`): all sources in copy `j0`, some target elsewhere, all other
copies meeting ≤ n − 1 pairs. The paper's "WLOG tn ∉ V(G_{j0})" is a machine-checked
demand permutation (`dpc_perm`). Per-target-copy inner families (`case4_family`) route
every split pair; the carrier of the last source splits at it, with subcase (i) renaming
exits when the carrier is a split pair and subcase (ii) rerouting a within-carrier
through a Hamilton bridge of a fresh copy no target touches.

Case 5 (`prop16_case5`): one copy `j0` meets every pair but holds neither all sources
nor all targets. Two machine-checked reductions (role swap via `MonoDemand.swap` +
`dpc_swap`; pair permutation via `dpc_perm`) arrange ≥ 2 targets in `j0` and the last
pair split with source there. The greedy connectors (`weld_greedy`) discharge Coleman's
Case 5 count — over ℕ the count needs the set-nonemptiness facts the paper's ℤ-prose
hides. The carrier of the last source is cut twice (`sn` keeps its predecessor `y`);
subcase (α) (an untouched copy exists) reroutes both cut ends through a 2-cover of that
copy, the last connector avoiding the pullback of `u₀*` (the paper's `N(u₀*)` exclusion);
subcase (β) (every copy touched) forces `ℓ = n + 1` with singleton copies
by a counting argument, and threads the carrier through 2-covers of a source-singleton
copy and the last target's copy — here Coleman's `u₀* ≠ v₂` argument silently uses
matching coherence, which the setting now carries (`hM`, supplied by `IsColemanTree`).

Case 6 (`prop16_case6`): two copies meet every pair (so every pair splits across them,
which is machine-derived). The greedy count runs as in Case 5. Shape I (the carrier's
`j1` segment is source-type) hands the carrier's connector pair to the last pair and
reroutes the carrier through a `j3` Hamilton bridge into its target's freed successor,
rejoining the second cut through a `j4` Hamilton bridge. Shape II (connector-type) cuts
both full copies and stitches the four freed ends through 2-covers of `j3` and `j4`
joined by a fresh matching edge; Coleman's `yn ∉ N(yι*)` exclusion works here exactly
because the setting carries matching coherence. All WLOGs are demand permutations.

The dispatcher (`prop16`/`coleman_prop16`) assembles the six cases into Proposition 1.6
itself: at most two copies can meet every pair, and every demand configuration lands in
exactly one case. All of it checks with `[propext, Classical.choice, Quot.sound]` only.

Nothing here is wired into the mainline; the remaining step toward discharging axiom A1
(`coleman_thm15`) is the Theorem 1.5 rank induction over `IsColemanTree` with its base
cases, consuming `coleman_prop16` at each weld.
-/
import BrualdiLean.Prop16

set_option linter.unusedSectionVars false

namespace Brualdi.Ledger

universe u

variable {W : Type u} [DecidableEq W] [Fintype W]

set_option maxHeartbeats 1600000 in
/-- **Case 1 of Coleman et al. 2025, Proposition 1.6**: if every copy meets at most
    `n − 1` of the demanded pairs, the weld admits the demanded `n`-PDPC. -/
theorem prop16_case1 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool} (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    (hw : ∀ j, (weldWSet s t j).card ≤ n - 1) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
  -- the split indices
  set D : Finset (Fin n) := Finset.univ.filter (fun i => (s i).1 ≠ (t i).1) with hD
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
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card < 2 * n - 1 := by
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
  obtain ⟨v, u, hvcol, hucol, hpart, hvT, huS, hvv, huu⟩ := weld_greedy S b s t D hsplit hcount
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
    apply S.inner_family (b := b) j (weldWSet s t j) ((hJmem j).mp hjJ) (hw j)
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
  have hpaths : ∀ i : Fin n, ∃ P : (weldGraph ell Gs M).Walk (s i) (t i), P.IsPath ∧
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
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0) J P hPpath ?_ ?_ ?_
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

set_option maxHeartbeats 3200000 in
private theorem prop16_case2_one_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
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
  have hn := S.hn
  have hEll := S.hEll
  -- a fresh copy for the detour
  obtain ⟨j2, -, hj2, -, -⟩ := fin_exists_two_ne (by omega) j0
  have hj02 : j0 ≠ j2 := fun h => hj2 h.symm
  -- the detour endpoints and the Hamilton bridge
  have hadj_in : (weldGraph ell Gs M).Adj (j0, y) (j2, M j0 j2 y) := weld_cross_adj hj02 y
  have hadj_out : (weldGraph ell Gs M).Adj (j2, M j0 j2 z) (j0, z) :=
    (weld_cross_adj hj02 z).symm
  have hcolbridge : col (j2, M j0 j2 y) ≠ col (j2, M j0 j2 z) := by
    have h1 := S.hproper _ _ hadj_in
    have h2 := S.hproper _ _ hadj_out
    cases hcy : col (j0, y) <;> cases hcz : col (j0, z) <;>
      cases hys : col (j2, M j0 j2 y) <;> cases hzs : col (j2, M j0 j2 z) <;> simp_all
  obtain ⟨hw, hham⟩ := S.copy_lace j2 _ _ hcolbridge
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
  refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0) ({j0, j2} : Finset (Fin ell))
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
private theorem prop16_case2_one {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
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
  have hbal := (S.hcopy_eq j0).1
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
    refine prop16_case2_one_core S hmono hS hT q hqcov hqdis a A Bmid C hA hB hC hyz
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
    refine prop16_case2_one_core S hmono hS hT q hqcov hqdis a A Bmid.reverse C hA
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
private theorem prop16_case2_two {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
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
  have hn := S.hn
  have hEll := S.hEll
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
  have hbal := (S.hcopy_eq j0).1
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
    have h := S.hproper _ _ (weld_cross_adj hj02 w)
    cases h1 : col (j0, w) <;> cases h2 : col (j2, M j0 j2 w) <;> simp_all
  have hstar3 : ∀ w : W, col (j3, M j0 j3 w) = !(col (j0, w)) := by
    intro w
    have h := S.hproper _ _ (weld_cross_adj hj03 w)
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
    S.inner_cover j2 (by omega) (by omega) _ _ hd2
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
  obtain ⟨hw3, hham3⟩ := S.copy_lace j3 _ _ hcolham
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
  refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
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
/-- **Case 2 of Coleman et al. 2025, Proposition 1.6**: all terminals lie in one copy
    `j0`. Cover the first `n − 1` pairs inside `j0`; the path carrying the extra pair's
    terminals is rearranged through one or two fresh copies (subcases (i)/(ii)). -/
theorem prop16_case2 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool} (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT : ∀ i, (t i).1 = j0) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
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
  obtain ⟨q, hqp, hqcov, hqdis⟩ := S.inner_cover j0 (by omega) (by omega) _ _ hd
  obtain ⟨a, ha⟩ := hqcov (s (Fin.last m)).2
  obtain ⟨c, hc⟩ := hqcov (t (Fin.last m)).2
  by_cases hac : a = c
  · subst hac
    exact prop16_case2_one S hmono hS hT q hqp hqcov hqdis a ha hc
  · exact prop16_case2_two S hmono hS hT q hqp hqcov hqdis a c hac ha hc

#print axioms prop16_case2

/-! ## Case 3: sources in one copy, targets in another

`prop16_case3`: all sources in copy `j1`, all targets in copy `j2 ≠ j1`. An inner
`m`-cover of `j1` pairs the first `m` sources with `m` chosen fresh `!b`-exits; the
path carrying the last source is split there, freeing a new exit `y` just before it and
keeping the tail as the last pair's `j1`-segment. The exits' matching partners in `j2`
are demanded against the first `m` targets; the path carrying the last target is split
there, its two cut ends are rejoined through a Hamilton bridge of a fresh copy `j3`
(Coleman's `G₃`), and the last pair reaches its target through a Hamilton bridge of a
second fresh copy `j4` (Coleman's `G₄`), entering via the target's freed path-neighbor.
Unlike the paper's presentation, the two special inner indices (the source-carrier `a`
and the target-carrier `k`) are handled independently — including `a = k`, which the
paper's double WLOG silently conflates. -/

private theorem fin_exists_two_avoid {ell : ℕ} (h : 4 ≤ ell) (a b : Fin ell) :
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
private theorem exists_injective_colored {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) (c : Bool) (m : ℕ)
    (hm : m ≤ 2 * n - 1) :
    ∃ v : Fin m → W, Function.Injective v ∧ ∀ i, col (j, v i) = c := by
  classical
  have hcard : m ≤ (Finset.univ.filter (fun w => col (j, w) = c)).card :=
    le_trans hm (S.class_card j c)
  obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨fun i => (u.equivFin.symm (finCongr hucard.symm i)).1, ?_, ?_⟩
  · intro i i' h
    have h2 := u.equivFin.symm.injective (Subtype.ext h)
    exact (finCongr hucard.symm).injective h2
  · intro i
    have h2 := husub (u.equivFin.symm (finCongr hucard.symm i)).2
    rw [Finset.mem_filter] at h2
    exact h2.2

private theorem bool_eq_of_ne_not {x c : Bool} (h : x ≠ !c) : x = c := by
  cases x <;> cases c <;> simp_all

private theorem bool_eq_not_of_ne {x c : Bool} (h : x ≠ c) : x = !c := by
  cases x <;> cases c <;> simp_all

set_option maxHeartbeats 6400000 in
/-- **Case 3 of Coleman et al. 2025, Proposition 1.6**: all sources in copy `j1`, all
    targets in copy `j2 ≠ j1`. -/
theorem prop16_case3 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool} (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2) (hS : ∀ i, (s i).1 = j1) (hT : ∀ i, (t i).1 = j2) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
  have hEll := S.hEll
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
  obtain ⟨v, hvinj, hvcol⟩ := exists_injective_colored S j1 (!b) m (by omega)
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
  obtain ⟨q, hqp, hqcov, hqdis⟩ := S.inner_cover j1 (by omega) (by omega) _ _ hd1
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
    have h := S.hproper _ _ hadj
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
    have h := S.hproper _ _ hadj
    rw [hcolex] at h
    exact bool_eq_of_ne_not (Ne.symm h)
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
  obtain ⟨qh, hqhp, hqhcov, hqhdis⟩ := S.inner_cover j2 (by omega) (by omega) _ _ hd2
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
    have h := S.hproper _ _ hadj
    have h2 := hcolT (Fin.last m)
    rw [h2] at h
    exact bool_eq_of_ne_not h
  have hcolun : col (j2, un) = b := by
    have hadj : (weldGraph ell Gs M).Adj (j2, (t (Fin.last m)).2) (j2, un) :=
      (weldLift Gs M j2).map_adj hadj_tn_un
    have h := S.hproper _ _ hadj
    have h2 := hcolT (Fin.last m)
    rw [h2] at h
    exact bool_eq_of_ne_not (Ne.symm h)
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
    have h := S.hproper _ _ hadj
    rw [hcolun] at h
    exact bool_eq_not_of_ne (Ne.symm h)
  -- two fresh bridge copies
  obtain ⟨j3, j4, hj31, hj32, hj41, hj42, hj34⟩ := fin_exists_two_avoid (by omega) j1 j2
  -- the `j3` bridge rejoins the two cut ends of the target-carrier
  have hbr3 : col (j3, M j2 j3 u0) ≠ col (j3, M j2 j3 v0) := by
    have h1 := S.hproper _ _ (weld_cross_adj (M := M) hj32.symm u0)
    have h2 := S.hproper _ _ (weld_cross_adj (M := M) hj32.symm v0)
    rw [hcolu0] at h1
    rw [hcolv0] at h2
    rw [bool_eq_not_of_ne (Ne.symm h1), bool_eq_of_ne_not (Ne.symm h2)]
    cases b <;> simp
  obtain ⟨h3, hham3⟩ := S.copy_lace j3 _ _ hbr3
  -- the `j4` bridge carries the last pair from `j1` to the freed neighbor `un`
  have hbr4 : col (j4, M j1 j4 (v a)) ≠ col (j4, M j2 j4 un) := by
    have h1 := S.hproper _ _ (weld_cross_adj (M := M) hj41.symm (v a))
    have h2 := S.hproper _ _ (weld_cross_adj (M := M) hj42.symm un)
    rw [hvcol a] at h1
    rw [hcolun] at h2
    rw [bool_eq_of_ne_not (Ne.symm h1), bool_eq_not_of_ne (Ne.symm h2)]
    cases b <;> simp
  obtain ⟨h4, hham4⟩ := S.copy_lace j4 _ _ hbr4
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
  refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
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



#print axioms prop16_case3

/-! ## Case 4: all sources in one copy, targets not all there

Infrastructure: demand permutation transport (the paper's "WLOG `tn ∉ V(G_{j0})`"),
an avoid-list version of the fresh-vertex chooser, and a fresh copy avoiding every
target (the paper's `|T \ T₁| < n ≤ ℓ − 1` observation). -/

/-- Permuting a demand transports covers (reindex the paths). -/
theorem dpc_perm {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {s t : Fin k → V} (σ : Equiv.Perm (Fin k))
    (h : IsPairedDPC G k (fun i => s (σ i)) (fun i => t (σ i))) :
    IsPairedDPC G k s t := by
  obtain ⟨p, hpath, hcov, hdisj⟩ := h
  refine ⟨fun i => (p (σ.symm i)).copy (by simp) (by simp), ?_, ?_, ?_⟩
  · intro i
    rw [SimpleGraph.Walk.isPath_copy]
    exact hpath _
  · intro x
    obtain ⟨j, hj⟩ := hcov x
    refine ⟨σ j, ?_⟩
    rw [SimpleGraph.Walk.support_copy]
    have he : σ.symm (σ j) = j := σ.symm_apply_apply j
    rw [he]
    exact hj
  · intro i j hij x hx
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hx
    exact hdisj (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h)) x hx

/-- `m` pairwise-distinct vertices of a prescribed color in copy `j`, avoiding a given
    finite set (room: `m + |avoid| ≤ 2n − 1`). -/
private theorem exists_injective_colored_avoid {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) (j : Fin ell) (c : Bool) (m : ℕ)
    (avoid : Finset W) (hm : m + avoid.card ≤ 2 * n - 1) :
    ∃ v : Fin m → W, Function.Injective v ∧ (∀ i, col (j, v i) = c) ∧ ∀ i, v i ∉ avoid := by
  classical
  have h1 := S.class_card j c
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

/-- A copy that no target touches, provided some target lies in `j0` (so the targets
    occupy at most `n` copies including `j0`, and `n < ℓ`). -/
private theorem exists_copy_avoiding_targets {ell n : ℕ} {t : Fin n → Fin ell × W}
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
private theorem case4_family {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ n - 1)
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
  apply S.inner_family (b := b) j (weldWSet s t j) hjne (hw j hj0)
  · intro i _
    have hadj := weld_cross_adj (Gs := Gs) (M := M) hj0.symm (exit i)
    have h := S.hproper _ _ hadj
    rw [hexcol i] at h
    exact bool_eq_of_ne_not (Ne.symm h)
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
private theorem prop16_case4_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0)
    (hlast : (t (Fin.last m)).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ m + 1 - 1) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn := S.hn
  have hEll := S.hEll
  have hcolS : ∀ i, col (j0, (s i).2) = b := by
    intro i
    rw [← hS i]
    exact hmono.1 i
  have hcolT : ∀ i, (t i).1 = j0 → col (j0, (t i).2) = !b := by
    intro i hi
    rw [← hi]
    exact hmono.2.1 i
  -- fresh `!b` exits avoiding the in-copy targets
  obtain ⟨v, hvinj, hvcol, hvavoid⟩ := exists_injective_colored_avoid S j0 (!b) m
    ((Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).image (fun i => (t i).2))
    (by
      have h1 : (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).card ≤ m := by
        have hsub : (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0))
            ⊆ Finset.univ.erase (Fin.last m) := by
          intro i hi
          rw [Finset.mem_filter] at hi
          rw [Finset.mem_erase]
          exact ⟨fun h => hlast (h ▸ hi.2), Finset.mem_univ i⟩
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin] at h2
        omega
      have h3 := Finset.card_image_le (s := Finset.univ.filter
        (fun i : Fin (m + 1) => (t i).1 = j0)) (f := fun i => (t i).2)
      omega)
  have hvt : ∀ i, ∀ r : Fin (m + 1), (t r).1 = j0 → v i ≠ (t r).2 := by
    intro i r hr he
    apply hvavoid i
    rw [Finset.mem_image]
    exact ⟨r, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ r, hr⟩, he.symm⟩
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
        exact absurd he.symm (hvt k i.castSucc hti)
      · rw [if_neg hti, if_pos htk] at he
        exact absurd he (hvt i k.castSucc htk)
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
  obtain ⟨q, hqp, hqcov, hqdis⟩ := S.inner_cover j0 (by omega) (by omega) _ _ hd0
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
    have h := S.hproper _ _ hadj
    have h2 := hcolS (Fin.last m)
    rw [h2] at h
    exact bool_eq_not_of_ne h
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
      have h := S.hproper _ _ hadj
      rw [hcoly] at h
      exact bool_eq_of_ne_not h
    have hcolz : col (j0, z) = !b := by
      have hadj : (weldGraph ell Gs M).Adj (j0, (s (Fin.last m)).2) (j0, z) :=
        (weldLift Gs M j0).map_adj hadj_sn_z
      have h := S.hproper _ _ hadj
      rw [hcolS (Fin.last m)] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    -- the fresh bridge copy
    obtain ⟨jf, hjf⟩ := exists_copy_avoiding_targets (t := t) hEll
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
      have h1 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjf0) u0)
      have h2 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjf0) z)
      rw [hcolu0] at h1
      rw [hcolz] at h2
      rw [bool_eq_not_of_ne (Ne.symm h1), bool_eq_of_ne_not (Ne.symm h2)]
      cases b <;> simp
    obtain ⟨hf, hhamf⟩ := S.copy_lace jf _ _ hbrf
    -- the per-target-copy families
    have hfam := fun j hj => case4_family S hmono hS hw exit hexcol hexinjS j
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
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
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
    have hfam := fun j hj => case4_family S hmono hS hw exit hexcol hexinjS j
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
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0) (insert j0 Jt) P hPp ?_ ?_ ?_
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
theorem prop16_case4 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W} {M : Fin ell → Fin ell → (W ≃ W)}
    {col : Fin ell × W → Bool} (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hS : ∀ i, (s i).1 = j0) (hT0 : ∃ i, (t i).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ n - 1) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
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
  exact prop16_case4_core S hmono' hS' hlast' hw'

#print axioms prop16_case4


/-! ## Case 5: one copy meets every pair but holds neither all sources nor all targets

Reductions: swapping the roles of sources and targets (`MonoDemand.swap` + `dpc_swap`)
arranges at least two targets in the full copy, and a demand permutation (`dpc_perm`)
arranges the last pair as a split pair with source in the full copy. The connectors come
from `weld_greedy` with Coleman's Case 5 count. -/

theorem MonoDemand.swap {V : Type u} [DecidableEq V] [Fintype V] {col : V → Bool} {b : Bool}
    {k : ℕ} {s t : Fin k → V} (h : MonoDemand col b s t) : MonoDemand col (!b) t s :=
  ⟨h.2.1, fun i => by rw [Bool.not_not]; exact h.1 i, h.2.2.2, h.2.2.1⟩

theorem weldWSet_swap {ell n : ℕ} (s t : Fin n → Fin ell × W) (j : Fin ell) :
    weldWSet t s j = weldWSet s t j := by
  ext i
  rw [mem_weldWSet, mem_weldWSet]
  exact or_comm

theorem weldWSet_card_perm {ell n : ℕ} (s t : Fin n → Fin ell × W)
    (σ : Equiv.Perm (Fin n)) (j : Fin ell) :
    (weldWSet (fun i => s (σ i)) (fun i => t (σ i)) j).card = (weldWSet s t j).card := by
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    rw [mem_weldWSet] at hi ⊢
    exact hi
  · intro i _ i' _ he
    exact σ.injective he
  · intro i hi
    refine ⟨σ.symm i, ?_, ?_⟩
    · rw [mem_weldWSet] at hi ⊢
      simpa using hi
    · exact σ.apply_symm_apply i

/-- Every pair touches a copy whose `w`-set is full. -/
theorem weldWSet_full_touch {ell n : ℕ} {s t : Fin n → Fin ell × W} {j0 : Fin ell}
    (hw0 : (weldWSet s t j0).card = n) (i : Fin n) : (s i).1 = j0 ∨ (t i).1 = j0 :=
  weldWSet_touch_of_card hw0 i


/-- Filtering on `P ∧ ¬Q` is the difference of the filters. -/
private theorem filter_and_not_eq_sdiff {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P]
    [DecidablePred Q] :
    Finset.univ.filter (fun k => P k ∧ ¬ Q k)
      = Finset.univ.filter P \ Finset.univ.filter Q := by
  ext k
  rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
  simp

set_option maxHeartbeats 12800000 in
/-- **Case 5 core**: copy `j0` meets every pair, at least two targets lie in it, the last
    pair is split with source in `j0`, and every other copy meets at most `n − 1` pairs. -/
private theorem prop16_case5_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hw0 : (weldWSet s t j0).card = m + 1)
    (hT2 : 2 ≤ (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).card)
    (hlastT : (t (Fin.last m)).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ m + 1 - 1) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn := S.hn
  have hEll := S.hEll
  have htouch : ∀ i, (s i).1 = j0 ∨ (t i).1 = j0 := weldWSet_full_touch hw0
  have hlastS : (s (Fin.last m)).1 = j0 := (htouch _).resolve_right hlastT
  -- the split pairs among the first `m`
  obtain ⟨D, hDmem⟩ : ∃ D : Finset (Fin (m + 1)),
      ∀ i, i ∈ D ↔ (i ≠ Fin.last m ∧ (s i).1 ≠ (t i).1) :=
    ⟨Finset.univ.filter (fun i => i ≠ Fin.last m ∧ (s i).1 ≠ (t i).1), fun i => by
      rw [Finset.mem_filter]
      simp⟩
  have hsplitD : ∀ i ∈ D, (s i).1 ≠ (t i).1 := fun i hi => ((hDmem i).mp hi).2
  -- Coleman's Case 5 count
  have hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < 2 * (m + 1) - 1 := by
    intro i hiD
    obtain ⟨hine, hisplit⟩ := (hDmem i).mp hiD
    by_cases hsj : (s i).1 = j0
    · -- the source side sits in the full copy
      have hitj : (t i).1 ≠ j0 := fun h => hisplit (hsj.trans h.symm)
      have hlastmem : Fin.last m ∈ Finset.univ.filter
          (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlastS, hlastT⟩
      have himem : i ∈ (Finset.univ.filter
          (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0)).erase (Fin.last m) := by
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨hine, Finset.mem_univ _, hsj, hitj⟩
      have h2 : (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0)).card - 2 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)
            ⊆ ((Finset.univ.filter (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0)).erase
                (Fin.last m)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hks, -⟩ := hk
          obtain ⟨hkne, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, hkne, Finset.mem_univ _, hks.trans hsj,
            fun h => hksplit ((hks.trans hsj).trans h.symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem himem, Finset.card_erase_of_mem hlastmem] at hle
      have hi4 : i ∈ Finset.univ.filter
          (fun k => (t k).1 = (t i).1 ∧ ¬ (s k).1 = (t i).1) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl, fun h => hisplit (h.trans rfl)⟩
      have h4 : (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
          ≤ (Finset.univ.filter
              (fun k => (t k).1 = (t i).1 ∧ ¬ (s k).1 = (t i).1)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)
            ⊆ (Finset.univ.filter
                (fun k => (t k).1 = (t i).1 ∧ ¬ (s k).1 = (t i).1)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hkt⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨hki, Finset.mem_univ _, hkt, ?_⟩
          intro h
          have hks : (s k).1 = j0 := (htouch k).resolve_right
            (fun hh => hitj (hkt.symm.trans hh))
          exact hitj (hks.symm.trans h).symm
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem hi4] at hle
      have hI1 : (Finset.univ.filter (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0)).card
          + (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j0)).card
          = (weldWSet s t j0).card := by
        rw [filter_and_not_eq_sdiff]
        exact weldWSet_card_split_t s t j0
      have hI2 : (Finset.univ.filter
            (fun k => (t k).1 = (t i).1 ∧ ¬ (s k).1 = (t i).1)).card
          + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
          = (weldWSet s t (t i).1).card := by
        rw [filter_and_not_eq_sdiff]
        exact weldWSet_card_split_s s t (t i).1
      have hwti := hw (t i).1 hitj
      have hS2 : 2 ≤ (Finset.univ.filter
          (fun k => (s k).1 = j0 ∧ ¬ (t k).1 = j0)).card := by
        rw [Nat.succ_le_iff]
        exact Finset.one_lt_card.mpr ⟨Fin.last m, hlastmem, i,
          Finset.mem_of_mem_erase himem, fun h => hine h.symm⟩
      have hT1 : 1 ≤ (Finset.univ.filter
          (fun k => (t k).1 = (t i).1 ∧ ¬ (s k).1 = (t i).1)).card :=
        Finset.card_pos.mpr ⟨i, hi4⟩
      have hTceq : (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j0)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hsj]
      omega
    · -- the target side sits in the full copy
      have hitj : (t i).1 = j0 := (htouch i).resolve_left hsj
      have hisj : (s i).1 ≠ (t i).1 := hisplit
      have himem2 : i ∈ Finset.univ.filter
          (fun k => (s k).1 = (s i).1 ∧ ¬ (t k).1 = (s i).1) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl, fun h => hisplit h.symm⟩
      have h2 : (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
          ≤ (Finset.univ.filter
              (fun k => (s k).1 = (s i).1 ∧ ¬ (t k).1 = (s i).1)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)
            ⊆ (Finset.univ.filter
                (fun k => (s k).1 = (s i).1 ∧ ¬ (t k).1 = (s i).1)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hks, -⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, Finset.mem_univ _, hks, fun h => hksplit (hks.trans h.symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem himem2] at hle
      have hlastmem4 : Fin.last m ∉ Finset.univ.filter
          (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0) := by
        rw [Finset.mem_filter]
        push_neg
        intro _ h
        exact absurd h hlastT
      have hi4 : i ∈ Finset.univ.filter
          (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hitj, hsj⟩
      have h4 : (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)
            ⊆ (Finset.univ.filter (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hkt⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, Finset.mem_univ _, hkt.trans hitj,
            fun h => hksplit (h.trans (hkt.trans hitj).symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem hi4] at hle
      have hI1 : (Finset.univ.filter
            (fun k => (s k).1 = (s i).1 ∧ ¬ (t k).1 = (s i).1)).card
          + (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
          = (weldWSet s t (s i).1).card := by
        rw [filter_and_not_eq_sdiff]
        exact weldWSet_card_split_t s t (s i).1
      have hI2 : (Finset.univ.filter (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0)).card
          + (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j0)).card
          = (weldWSet s t j0).card := by
        rw [filter_and_not_eq_sdiff]
        exact weldWSet_card_split_s s t j0
      have hwsi := hw (s i).1 hsj
      have hS1 : 1 ≤ (Finset.univ.filter
          (fun k => (s k).1 = (s i).1 ∧ ¬ (t k).1 = (s i).1)).card :=
        Finset.card_pos.mpr ⟨i, himem2⟩
      have hT1 : 1 ≤ (Finset.univ.filter
          (fun k => (t k).1 = j0 ∧ ¬ (s k).1 = j0)).card :=
        Finset.card_pos.mpr ⟨i, hi4⟩
      have hTceq : (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j0)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hitj]
      omega
  -- the greedy connectors for the split non-last pairs
  obtain ⟨v, u, hvcol, hucol, hpart, hvT, huS, hvv, huu⟩ := weld_greedy S b s t D hsplitD hcount
  -- the `j0` inner family over the first `m` pairs (the last pair is excluded; its
  -- source is the split point)
  have hA0ne : (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hA0card : (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))).card ≤ m + 1 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hDofA0 : ∀ i ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))),
      (s i).1 ≠ (t i).1 → i ∈ D := by
    intro i hi hsplit
    exact (hDmem i).mpr ⟨Finset.ne_of_mem_erase hi, hsplit⟩
  have hfam0 : ∃ Q0 : ∀ i ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))),
      (Gs j0).Walk (wInnerS s u j0 i) (wInnerT t v j0 i),
      (∀ i (hi : i ∈ _), (Q0 i hi).IsPath) ∧
      (∀ x : W, ∃ i, ∃ hi : i ∈ _, x ∈ (Q0 i hi).support) ∧
      (∀ i (hi : i ∈ _), ∀ k (hk : k ∈ _), i ≠ k →
        ∀ x, ¬ (x ∈ (Q0 i hi).support ∧ x ∈ (Q0 k hk).support)) := by
    apply S.inner_family (b := b) j0 _ hA0ne hA0card
    · intro i hi
      by_cases hsij : (s i).1 = j0
      · rw [wInnerS_src hsij, ← hsij]
        exact hmono.1 i
      · have htij : (t i).1 = j0 := (htouch i).resolve_left hsij
        have hiD : i ∈ D := hDofA0 i hi (fun h => hsij (h.trans htij))
        rw [wInnerS_conn hsij, ← htij]
        exact hucol i hiD
    · intro i hi
      by_cases htij : (t i).1 = j0
      · rw [wInnerT_tgt htij, ← htij]
        exact hmono.2.1 i
      · have hsij : (s i).1 = j0 := (htouch i).resolve_right htij
        have hiD : i ∈ D := hDofA0 i hi (fun h => htij (h.symm.trans hsij))
        rw [wInnerT_conn htij, ← hsij]
        exact hvcol i hiD
    · intro i hi k hk hik
      by_cases hsij : (s i).1 = j0 <;> by_cases hskj : (s k).1 = j0
      · rw [wInnerS_src hsij, wInnerS_src hskj]
        intro he
        exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
      · have htkj : (t k).1 = j0 := (htouch k).resolve_left hskj
        have hkD : k ∈ D := hDofA0 k hk (fun h => hskj (h.trans htkj))
        rw [wInnerS_src hsij, wInnerS_conn hskj]
        exact fun he => huS k hkD i (hsij.trans htkj.symm) he.symm
      · have htij : (t i).1 = j0 := (htouch i).resolve_left hsij
        have hiD : i ∈ D := hDofA0 i hi (fun h => hsij (h.trans htij))
        rw [wInnerS_conn hsij, wInnerS_src hskj]
        exact huS i hiD k (hskj.trans htij.symm)
      · have htij : (t i).1 = j0 := (htouch i).resolve_left hsij
        have htkj : (t k).1 = j0 := (htouch k).resolve_left hskj
        have hiD : i ∈ D := hDofA0 i hi (fun h => hsij (h.trans htij))
        have hkD : k ∈ D := hDofA0 k hk (fun h => hskj (h.trans htkj))
        rw [wInnerS_conn hsij, wInnerS_conn hskj]
        exact huu k hkD i hiD hik (htij.trans htkj.symm)
    · intro i hi k hk hik
      by_cases htij : (t i).1 = j0 <;> by_cases htkj : (t k).1 = j0
      · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
        intro he
        exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
      · have hskj : (s k).1 = j0 := (htouch k).resolve_right htkj
        have hkD : k ∈ D := hDofA0 k hk (fun h => htkj (h.symm.trans hskj))
        rw [wInnerT_tgt htij, wInnerT_conn htkj]
        exact fun he => hvT k hkD i (htij.trans hskj.symm) he.symm
      · have hsij : (s i).1 = j0 := (htouch i).resolve_right htij
        have hiD : i ∈ D := hDofA0 i hi (fun h => htij (h.symm.trans hsij))
        rw [wInnerT_conn htij, wInnerT_tgt htkj]
        exact hvT i hiD k (htkj.trans hsij.symm)
      · have hsij : (s i).1 = j0 := (htouch i).resolve_right htij
        have hskj : (s k).1 = j0 := (htouch k).resolve_right htkj
        have hiD : i ∈ D := hDofA0 i hi (fun h => htij (h.symm.trans hsij))
        have hkD : k ∈ D := hDofA0 k hk (fun h => htkj (h.symm.trans hskj))
        rw [wInnerT_conn htij, wInnerT_conn htkj]
        exact hvv k hkD i hiD hik (hsij.trans hskj.symm)
  obtain ⟨Q0, hQ0path, hQ0cov, hQ0disj⟩ := hfam0
  -- locate the carrier of the last source and split it there
  obtain ⟨a, ha0, ha⟩ := hQ0cov (s (Fin.last m)).2
  have halast : a ≠ Fin.last m := Finset.ne_of_mem_erase ha0
  -- the last source is interior to its carrier
  have hsnS : (s (Fin.last m)).2 ≠ wInnerS s u j0 a := by
    by_cases hsij : (s a).1 = j0
    · rw [wInnerS_src hsij]
      intro h
      have h2 := hmono.2.2.1 (Prod.ext (hlastS.trans hsij.symm) h)
      exact halast h2.symm
    · have htij : (t a).1 = j0 := (htouch a).resolve_left hsij
      have hiD : a ∈ D := (hDmem a).mpr ⟨halast, fun h => hsij (h.trans htij)⟩
      rw [wInnerS_conn hsij]
      intro h
      exact huS a hiD (Fin.last m) (hlastS.trans htij.symm) h.symm
  have hpairlast : s (Fin.last m) = (j0, (s (Fin.last m)).2) := Prod.ext hlastS rfl
  have hsnT : (s (Fin.last m)).2 ≠ wInnerT t v j0 a := by
    by_cases htij : (t a).1 = j0
    · rw [wInnerT_tgt htij]
      intro h
      have h1 := hmono.1 (Fin.last m)
      rw [hpairlast] at h1
      have h2 := hmono.2.1 a
      rw [show t a = (j0, (t a).2) from Prod.ext htij rfl] at h2
      rw [h] at h1
      rw [h1] at h2
      cases b <;> simp at h2
    · have hsij : (s a).1 = j0 := (htouch a).resolve_right htij
      have hiD : a ∈ D := (hDmem a).mpr ⟨halast, fun h => htij (h.symm.trans hsij)⟩
      rw [wInnerT_conn htij]
      intro h
      have h1 := hmono.1 (Fin.last m)
      rw [hpairlast] at h1
      have h2 := hvcol a hiD
      rw [hsij] at h2
      rw [h] at h1
      rw [h1] at h2
      cases b <;> simp at h2
  -- split the carrier at the last source, keep its predecessor with the last pair,
  -- and peel one more vertex off the prefix
  obtain ⟨y, z, Apre, B, hApre, hB, hadj_y_sn, hadj_sn_z, hsuppA⟩ :=
    path_split_interior (Q0 a ha0) (hQ0path a ha0) ha hsnS hsnT
  have hndA := (hQ0path a ha0).support_nodup
  rw [hsuppA] at hndA
  obtain ⟨hndA1, hndA2, hdisjA⟩ := List.nodup_append.mp hndA
  have hsn_notB : (s (Fin.last m)).2 ∉ B.support := (List.nodup_cons.mp hndA2).1
  have hcoly : col (j0, y) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j0, y) (j0, (s (Fin.last m)).2) :=
      (weldLift Gs M j0).map_adj hadj_y_sn
    have h := S.hproper _ _ hadj
    have h2 := hmono.1 (Fin.last m)
    rw [hpairlast] at h2
    rw [h2] at h
    exact bool_eq_not_of_ne h
  have hcolz : col (j0, z) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j0, (s (Fin.last m)).2) (j0, z) :=
      (weldLift Gs M j0).map_adj hadj_sn_z
    have h := S.hproper _ _ hadj
    have h2 := hmono.1 (Fin.last m)
    rw [hpairlast] at h2
    rw [h2] at h
    exact bool_eq_not_of_ne (Ne.symm h)
  have hyApre : y ≠ wInnerS s u j0 a := by
    intro h
    have h1 := hcoly
    by_cases hsij : (s a).1 = j0
    · rw [wInnerS_src hsij] at h
      have h2 := hmono.1 a
      rw [show s a = (j0, (s a).2) from Prod.ext hsij rfl] at h2
      rw [← h] at h2
      rw [h1] at h2
      cases b <;> simp at h2
    · have htij : (t a).1 = j0 := (htouch a).resolve_left hsij
      have hiD : a ∈ D := (hDmem a).mpr ⟨halast, fun hh => hsij (hh.trans htij)⟩
      rw [wInnerS_conn hsij] at h
      have h2 := hucol a hiD
      rw [htij] at h2
      rw [← h] at h2
      rw [h1] at h2
      cases b <;> simp at h2
  obtain ⟨u0, A', hA', hadj_u0_y, hsuppA', hy_notA'⟩ := path_peel_last Apre hApre hyApre
  have hcolu0 : col (j0, u0) = b := by
    have hadj : (weldGraph ell Gs M).Adj (j0, u0) (j0, y) :=
      (weldLift Gs M j0).map_adj hadj_u0_y
    have h := S.hproper _ _ hadj
    rw [hcoly] at h
    exact bool_eq_of_ne_not h
  -- the touched non-`j0` copies
  have hJtmem0 : ∀ j : Fin ell, j ≠ j0 → (weldWSet s t j).Nonempty →
      ∀ i ∈ weldWSet s t j, (t i).1 = j ∨ (s i).1 = j := by
    intro j _ _ i hi
    rcases mem_weldWSet.mp hi with h | h
    · exact Or.inr h
    · exact Or.inl h
  by_cases hE : ∃ jE : Fin ell, weldWSet s t jE = ∅
  · -- SUBCASE (α): an untouched copy exists; bridge both surgical gaps through it
    obtain ⟨jE, hwE⟩ := hE
    have hjE0 : jE ≠ j0 := by
      intro h
      rw [h] at hwE
      rw [hwE] at hw0
      simp at hw0
    have hjEnone : ∀ i : Fin (m + 1), (s i).1 ≠ jE ∧ (t i).1 ≠ jE := by
      intro i
      constructor <;> intro h
      · have : i ∈ weldWSet s t jE := mem_weldWSet.mpr (Or.inl h)
        rw [hwE] at this
        exact absurd this (Finset.notMem_empty i)
      · have : i ∈ weldWSet s t jE := mem_weldWSet.mpr (Or.inr h)
        rw [hwE] at this
        exact absurd this (Finset.notMem_empty i)
    -- the connector of the last pair in its target copy, avoiding the copy's sources,
    -- the other connectors, and the pullback of the first bridge endpoint
    have hunavoid : ((Finset.univ.filter
          (fun k : Fin (m + 1) => (s k).1 = (t (Fin.last m)).1)).image (fun k => (s k).2)
        ∪ (D.filter (fun k => (t k).1 = (t (Fin.last m)).1)).image u
        ∪ {(M (t (Fin.last m)).1 jE).symm (M j0 jE u0)}).card < 2 * (m + 1) - 1 := by
      have h1 := Finset.card_union_le
        ((Finset.univ.filter
          (fun k : Fin (m + 1) => (s k).1 = (t (Fin.last m)).1)).image (fun k => (s k).2)
          ∪ (D.filter (fun k => (t k).1 = (t (Fin.last m)).1)).image u)
        ({(M (t (Fin.last m)).1 jE).symm (M j0 jE u0)} : Finset W)
      have h2 := Finset.card_union_le
        ((Finset.univ.filter
          (fun k : Fin (m + 1) => (s k).1 = (t (Fin.last m)).1)).image (fun k => (s k).2))
        ((D.filter (fun k => (t k).1 = (t (Fin.last m)).1)).image u)
      have h3 := Finset.card_image_le (s := Finset.univ.filter
        (fun k : Fin (m + 1) => (s k).1 = (t (Fin.last m)).1)) (f := fun k => (s k).2)
      have h4 := Finset.card_image_le
        (s := D.filter (fun k => (t k).1 = (t (Fin.last m)).1)) (f := u)
      have h5 : (D.filter (fun k => (t k).1 = (t (Fin.last m)).1)).card
          ≤ (Finset.univ.filter (fun k : Fin (m + 1) =>
              (t k).1 = (t (Fin.last m)).1 ∧ ¬ (s k).1 = (t (Fin.last m)).1)).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter] at hk
        obtain ⟨hkD, hkt⟩ := hk
        obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hkt, ?_⟩
        intro h
        exact hksplit (h.trans hkt.symm)
      have hI : (Finset.univ.filter (fun k : Fin (m + 1) =>
            (t k).1 = (t (Fin.last m)).1 ∧ ¬ (s k).1 = (t (Fin.last m)).1)).card
          + (Finset.univ.filter
            (fun k : Fin (m + 1) => (s k).1 = (t (Fin.last m)).1)).card
          = (weldWSet s t (t (Fin.last m)).1).card := by
        rw [filter_and_not_eq_sdiff]
        exact weldWSet_card_split_s s t (t (Fin.last m)).1
      have hwjn := hw (t (Fin.last m)).1 hlastT
      have h6 : ({(M (t (Fin.last m)).1 jE).symm (M j0 jE u0)} : Finset W).card = 1 :=
        Finset.card_singleton _
      omega
    obtain ⟨un, hcolun, hunavoids⟩ := S.exists_avoid (t (Fin.last m)).1 b _ hunavoid
    have hun_notS : ∀ k : Fin (m + 1), (s k).1 = (t (Fin.last m)).1 → un ≠ (s k).2 := by
      intro k hk he
      apply hunavoids
      rw [Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hk⟩, he.symm⟩))
    have hun_notu : ∀ k ∈ D, (t k).1 = (t (Fin.last m)).1 → un ≠ u k := by
      intro k hkD hk he
      apply hunavoids
      rw [Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, by
        rw [Finset.mem_filter]; exact ⟨hkD, hk⟩, he.symm⟩))
    have hun_notpull : un ≠ (M (t (Fin.last m)).1 jE).symm (M j0 jE u0) := by
      intro he
      apply hunavoids
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_singleton.mpr he)
    -- extend the connectors with the last pair's
    obtain ⟨u', hu'val⟩ : ∃ u' : Fin (m + 1) → W,
        (∀ i, i ≠ Fin.last m → u' i = u i) ∧ u' (Fin.last m) = un := by
      refine ⟨Function.update u (Fin.last m) un, ?_, Function.update_self ..⟩
      intro i hi
      exact Function.update_of_ne hi ..
    have hu'D : ∀ i ∈ D, u' i = u i := fun i hi => hu'val.1 i ((hDmem i).mp hi).1
    -- the two cut vertices differ
    have hyz : y ≠ z := by
      intro h
      exact hdisjA y (SimpleGraph.Walk.end_mem_support Apre) z
        (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support B)) h
    -- colors across the bridge
    have hcu0E : col (jE, M j0 jE u0) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjE0) u0)
      rw [hcolu0] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    have hcyE : col (jE, M j0 jE y) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjE0) y)
      rw [hcoly] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hczE : col (jE, M j0 jE z) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hjE0) z)
      rw [hcolz] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcunE : col (jE, M (t (Fin.last m)).1 jE un) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M)
        ((hjEnone (Fin.last m)).2) un)
      rw [hcolun] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    -- the bridge 2-cover
    have hdE : OppositeDemand (fun w' => col (jE, w'))
        ![M j0 jE u0, M j0 jE y] ![M j0 jE z, M (t (Fin.last m)).1 jE un] := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · show col (jE, M j0 jE u0) ≠ col (jE, M j0 jE z)
          rw [hcu0E, hczE]
          cases b <;> simp
        · show col (jE, M j0 jE y) ≠ col (jE, M (t (Fin.last m)).1 jE un)
          rw [hcyE, hcunE]
          cases b <;> simp
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exfalso
          have h2 : M j0 jE u0 = M j0 jE y := h
          rw [h2] at hcu0E
          rw [hcyE] at hcu0E
          cases b <;> simp at hcu0E
        · exfalso
          have h2 : M j0 jE y = M j0 jE u0 := h
          rw [h2] at hcyE
          rw [hcu0E] at hcyE
          cases b <;> simp at hcyE
        · rfl
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exfalso
          have h2 : M j0 jE z = M (t (Fin.last m)).1 jE un := h
          rw [h2] at hczE
          rw [hcunE] at hczE
          cases b <;> simp at hczE
        · exfalso
          have h2 : M (t (Fin.last m)).1 jE un = M j0 jE z := h
          rw [← h2] at hczE
          rw [hcunE] at hczE
          cases b <;> simp at hczE
        · rfl
      · intro i k
        fin_cases i <;> fin_cases k
        · intro h
          have h2 : M j0 jE u0 = M j0 jE z := h
          rw [h2] at hcu0E
          rw [hczE] at hcu0E
          cases b <;> simp at hcu0E
        · intro h
          have h2 : M j0 jE u0 = M (t (Fin.last m)).1 jE un := h
          apply hun_notpull
          rw [eq_comm, Equiv.symm_apply_eq]
          exact h2
        · intro h
          have h2 : M j0 jE y = M j0 jE z := h
          exact hyz ((M j0 jE).injective h2)
        · intro h
          have h2 : M j0 jE y = M (t (Fin.last m)).1 jE un := h
          rw [h2] at hcyE
          rw [hcunE] at hcyE
          cases b <;> simp at hcyE
    have hm2 : 2 ≤ m := by omega
    obtain ⟨qE, hqEp, hqEcov, hqEdis⟩ := S.inner_cover jE (by omega) (by omega) _ _ hdE
    -- the touched non-`j0` copies and their families (with the extended connectors)
    set Jt : Finset (Fin ell) := Finset.univ.filter
      (fun j => j ≠ j0 ∧ (weldWSet s t j).Nonempty) with hJt
    have hJtmem : ∀ j, j ∈ Jt ↔ (j ≠ j0 ∧ (weldWSet s t j).Nonempty) := by
      intro j
      rw [hJt, Finset.mem_filter]
      simp
    have hfamJ : ∀ j ∈ Jt, ∃ Q : ∀ i ∈ weldWSet s t j,
        (Gs j).Walk (wInnerS s u' j i) (wInnerT t v j i),
        (∀ i (hi : i ∈ weldWSet s t j), (Q i hi).IsPath) ∧
        (∀ x : W, ∃ i, ∃ hi : i ∈ weldWSet s t j, x ∈ (Q i hi).support) ∧
        (∀ i (hi : i ∈ weldWSet s t j), ∀ k (hk : k ∈ weldWSet s t j), i ≠ k →
          ∀ x, ¬ (x ∈ (Q i hi).support ∧ x ∈ (Q k hk).support)) := by
      intro j hjJt
      obtain ⟨hj0ne, hjne⟩ := (hJtmem j).mp hjJt
      have hmemD : ∀ i ∈ weldWSet s t j, i ≠ Fin.last m → i ∈ D := by
        intro i hi hilast
        refine (hDmem i).mpr ⟨hilast, ?_⟩
        intro hh
        have hc : (s i).1 = j := by
          rcases mem_weldWSet.mp hi with h | h
          · exact h
          · exact hh.trans h
        have hc0 : (s i).1 = j0 := by
          rcases htouch i with h | h
          · exact h
          · exact hh.trans h
        exact hj0ne (hc.symm.trans hc0)
      apply S.inner_family (b := b) j _ hjne (hw j hj0ne)
      · intro i hi
        by_cases hsij : (s i).1 = j
        · rw [wInnerS_src hsij, ← hsij]
          exact hmono.1 i
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          rw [wInnerS_conn hsij]
          by_cases hilast : i = Fin.last m
          · subst hilast
            rw [hu'val.2, ← htij]
            exact hcolun
          · have hiD := hmemD i hi hilast
            rw [hu'val.1 i hilast, ← htij]
            exact hucol i hiD
      · intro i hi
        by_cases htij : (t i).1 = j
        · rw [wInnerT_tgt htij, ← htij]
          exact hmono.2.1 i
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          have hilast : i ≠ Fin.last m := fun h => hj0ne ((h ▸ hsij).symm.trans hlastS)
          have hiD := hmemD i hi hilast
          rw [wInnerT_conn htij, ← hsij]
          exact hvcol i hiD
      · intro i hi k hk hik
        by_cases hsij : (s i).1 = j <;> by_cases hskj : (s k).1 = j
        · rw [wInnerS_src hsij, wInnerS_src hskj]
          intro he
          exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
        · have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
          rw [wInnerS_src hsij, wInnerS_conn hskj]
          by_cases hklast : k = Fin.last m
          · subst hklast
            rw [hu'val.2]
            exact fun he => hun_notS i (hsij.trans htkj.symm) he.symm
          · have hkD := hmemD k hk hklast
            rw [hu'val.1 k hklast]
            exact fun he => huS k hkD i (hsij.trans htkj.symm) he.symm
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          rw [wInnerS_conn hsij, wInnerS_src hskj]
          by_cases hilast : i = Fin.last m
          · subst hilast
            rw [hu'val.2]
            exact hun_notS k (hskj.trans htij.symm)
          · have hiD := hmemD i hi hilast
            rw [hu'val.1 i hilast]
            exact huS i hiD k (hskj.trans htij.symm)
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
          rw [wInnerS_conn hsij, wInnerS_conn hskj]
          by_cases hilast : i = Fin.last m <;> by_cases hklast : k = Fin.last m
          · exact absurd (hilast.trans hklast.symm) hik
          · subst hilast
            have hkD := hmemD k hk hklast
            rw [hu'val.2, hu'val.1 k hklast]
            exact fun he => hun_notu k hkD (htkj.trans htij.symm) he
          · subst hklast
            have hiD := hmemD i hi hilast
            rw [hu'val.1 i hilast, hu'val.2]
            exact fun he => hun_notu i hiD (htij.trans htkj.symm) he.symm
          · have hiD := hmemD i hi hilast
            have hkD := hmemD k hk hklast
            rw [hu'val.1 i hilast, hu'val.1 k hklast]
            exact huu k hkD i hiD hik (htij.trans htkj.symm)
      · intro i hi k hk hik
        by_cases htij : (t i).1 = j <;> by_cases htkj : (t k).1 = j
        · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
          intro he
          exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
        · have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
          have hklast : k ≠ Fin.last m := fun h => hj0ne ((h ▸ hskj).symm.trans hlastS)
          have hkD := hmemD k hk hklast
          rw [wInnerT_tgt htij, wInnerT_conn htkj]
          exact fun he => hvT k hkD i (htij.trans hskj.symm) he.symm
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          have hilast : i ≠ Fin.last m := fun h => hj0ne ((h ▸ hsij).symm.trans hlastS)
          have hiD := hmemD i hi hilast
          rw [wInnerT_conn htij, wInnerT_tgt htkj]
          exact hvT i hiD k (htkj.trans hsij.symm)
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
          have hilast : i ≠ Fin.last m := fun h => hj0ne ((h ▸ hsij).symm.trans hlastS)
          have hklast : k ≠ Fin.last m := fun h => hj0ne ((h ▸ hskj).symm.trans hlastS)
          have hiD := hmemD i hi hilast
          have hkD := hmemD k hk hklast
          rw [wInnerT_conn htij, wInnerT_conn htkj]
          exact hvv k hkD i hiD hik (hsij.trans hskj.symm)
    choose QJ hQJp hQJcov hQJdis using hfamJ
    have hQtrans : ∀ (j j' : Fin ell) (he : j = j') (hj : j ∈ Jt) (hj' : j' ∈ Jt)
        (r : Fin (m + 1)) (hi : r ∈ weldWSet s t j) (hi' : r ∈ weldWSet s t j') (x2 : W),
        x2 ∈ (QJ j hj r hi).support → x2 ∈ (QJ j' hj' r hi').support := by
      intro j j' he
      subst he
      intro hj hj' r hi hi' x2 h
      exact h
    -- the `j0`-side segment lists
    set g0 : Fin (m + 1) → List W := fun r =>
      if hr : r = Fin.last m then ((s (Fin.last m)).2 :: [y])
      else if r = a then A'.support ++ B.support
      else (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support with hg0
    have hg0last : g0 (Fin.last m) = ((s (Fin.last m)).2 :: [y]) := by
      rw [hg0]
      exact dif_pos rfl
    have hg0a : g0 a = A'.support ++ B.support := by
      simp [hg0, halast]
    have hg0other : ∀ r, ∀ hr : r ≠ Fin.last m, r ≠ a →
        g0 r = (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
      intro r hr hra
      simp only [hg0]
      rw [dif_neg hr, if_neg hra]
    have hsubA' : ∀ x2 : W, x2 ∈ A'.support → x2 ∈ Apre.support := by
      intro x2 h
      rw [hsuppA']
      exact List.mem_append_left _ h
    have hsub_qa : ∀ x2 : W, x2 ∈ g0 a → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg0a] at h
      rw [hsuppA]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (hsubA' x2 h)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hsub_last : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg0last] at h
      rcases List.mem_cons.mp h with h | h
      · rw [h, hsuppA]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · rw [List.mem_singleton] at h
        rw [h, hsuppA]
        exact List.mem_append_left _ (by
          rw [hsuppA']
          exact List.mem_append_right _ (List.mem_singleton_self _))
    have hlast_va : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ g0 a → False := by
      intro x2 h h'
      rw [hg0last] at h
      rw [hg0a] at h'
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
      intro r r' hrr' x2 h h'
      by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
      · exact hrr' (hr.trans hr'.symm)
      · rw [hr] at h
        by_cases hra : r' = a
        · rw [hra] at h'
          exact hlast_va x2 h h'
        · rw [hg0other r' hr' hra] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra x2 ⟨h', hsub_last x2 h⟩
      · rw [hr'] at h'
        by_cases hra : r = a
        · rw [hra] at h
          exact hlast_va x2 h' h
        · rw [hg0other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_last x2 h'⟩
      · by_cases hra : r = a <;> by_cases hra' : r' = a
        · exact hrr' (hra.trans hra'.symm)
        · rw [hra] at h
          rw [hg0other r' hr' hra'] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra' x2 ⟨h', hsub_qa x2 h⟩
        · rw [hra'] at h'
          rw [hg0other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_qa x2 h'⟩
        · rw [hg0other r hr hra] at h
          rw [hg0other r' hr' hra'] at h'
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    have hjEJt : jE ∉ Jt := by
      intro h
      obtain ⟨i0', hi0'⟩ := ((hJtmem jE).mp h).2
      rw [hwE] at hi0'
      exact absurd hi0' (Finset.notMem_empty i0')
    -- the bridge segments with clean endpoints
    have hqE0' : ∃ q : (Gs jE).Walk (M j0 jE u0) (M j0 jE z), q.IsPath ∧
        q.support = (qE 0).support :=
      ⟨(qE 0).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hqEp 0, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨qE0, hqE0p, hqE0s⟩ := hqE0'
    have hqE1' : ∃ q : (Gs jE).Walk (M j0 jE y) (M (t (Fin.last m)).1 jE un), q.IsPath ∧
        q.support = (qE 1).support :=
      ⟨(qE 1).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hqEp 1, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨qE1, hqE1p, hqE1s⟩ := hqE1'
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j0 ∧ x.2 ∈ g0 r) ∨
            (∃ (hj : x.1 ∈ Jt) (hi : r ∈ weldWSet s t x.1), x.2 ∈ (QJ x.1 hj r hi).support) ∨
            (x.1 = jE ∧ ((r = a ∧ x.2 ∈ (qE 0).support) ∨
              (r = Fin.last m ∧ x.2 ∈ (qE 1).support)))) := by
      intro r
      by_cases hr : r = Fin.last m
      · -- the last pair: `sn, y` in `j0`, the second bridge path, then its target segment
        subst hr
        have hjnJt : (t (Fin.last m)).1 ∈ Jt :=
          (hJtmem _).mpr ⟨hlastT, ⟨_, mem_weldWSet.mpr (Or.inr rfl)⟩⟩
        have hlastW : Fin.last m ∈ weldWSet s t (t (Fin.last m)).1 :=
          mem_weldWSet.mpr (Or.inr rfl)
        have hsnwp : (SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil :
            (Gs j0).Walk (s (Fin.last m)).2 y).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcoly
          rw [← h] at h1
          have h2 := hmono.1 (Fin.last m)
          rw [hpairlast] at h2
          rw [h2] at h1
          cases b <;> simp at h1
        have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j0, y), R.IsPath ∧
            R.support = [(s (Fin.last m)).2, y].map (fun w' => (j0, w')) := by
          refine ⟨((SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil).map
            (weldLift Gs M j0)).copy (Prod.ext hlastS.symm rfl) rfl, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsnwp
          · rw [SimpleGraph.Walk.support_copy, weldLift_support,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
        obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
        obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ qE1 hR₀p hqE1p
          (weld_cross_adj (Ne.symm hjE0) y)
          (by
            intro w' _ hmem
            rw [hR₀s, mem_map_pair] at hmem
            exact hjE0 hmem.1)
        have hseg : ∃ q : (Gs (t (Fin.last m)).1).Walk un (t (Fin.last m)).2, q.IsPath ∧
            q.support = (QJ _ hjnJt (Fin.last m) hlastW).support := by
          refine ⟨(QJ _ hjnJt (Fin.last m) hlastW).copy ?_ (wInnerT_tgt rfl), ?_, ?_⟩
          · rw [wInnerS_conn (fun h => hlastT ((hlastS.symm.trans h).symm))]
            exact hu'val.2
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hQJp _ hjnJt _ hlastW
          · rw [SimpleGraph.Walk.support_copy]
        obtain ⟨seg, hsegp, hsegs⟩ := hseg
        obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ seg hR₁p hsegp
          ((weld_cross_adj ((hjEnone (Fin.last m)).2) un).symm)
          (by
            intro w' _ hmem
            rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
            rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hlastT h1
            · exact (hjEnone (Fin.last m)).2 h1)
        refine ⟨R₂.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₂p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s, List.mem_append,
            hR₀s, mem_map_pair, mem_map_pair, mem_map_pair]
          constructor
          · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · refine Or.inl ⟨h1, ?_⟩
              rw [hg0last]
              simpa using h2
            · exact Or.inr (Or.inr ⟨h1, Or.inr ⟨rfl, by rw [← hqE1s]; exact h2⟩⟩)
            · refine Or.inr (Or.inl ?_)
              have hj' : x.1 ∈ Jt := by rw [h1]; exact hjnJt
              have hi' : Fin.last m ∈ weldWSet s t x.1 := by rw [h1]; exact hlastW
              rw [hsegs] at h2
              exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjnJt hj' _ hlastW hi' x.2 h2⟩
          · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hra, -⟩ | ⟨-, h2⟩⟩)
            · refine Or.inl (Or.inl ⟨h1, ?_⟩)
              rw [hg0last] at h2
              simpa using h2
            · have hx1 : x.1 = (t (Fin.last m)).1 := by
                rcases mem_weldWSet.mp hi with h | h
                · exact absurd ((hlastS.symm.trans h).symm) ((hJtmem x.1).mp hj).1
                · exact h.symm
              refine Or.inr ?_
              rw [hsegs]
              exact ⟨hx1, hQtrans x.1 _ hx1 hj hjnJt _ hi hlastW x.2 h2⟩
            · exact absurd hra.symm (Finset.ne_of_mem_erase ha0)
            · exact Or.inl (Or.inr ⟨h1, by rw [hqE1s]; exact h2⟩)
      · have hrmem : r ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))) :=
          Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
        by_cases hra : r = a
        · -- the carrier pair: reroute the cut through the first bridge path
          subst hra
          by_cases hsaj : (s r).1 = j0
          · have hA'c : ∃ q : (Gs j0).Walk (s r).2 u0, q.IsPath ∧ q.support = A'.support :=
              ⟨A'.copy (wInnerS_src hsaj) rfl, by
                rw [SimpleGraph.Walk.isPath_copy]; exact hA', SimpleGraph.Walk.support_copy ..⟩
            obtain ⟨A'c, hA'cp, hA'cs⟩ := hA'c
            have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j0, u0), R.IsPath ∧
                R.support = A'.support.map (fun w' => (j0, w')) := by
              refine ⟨(A'c.map (weldLift Gs M j0)).copy (Prod.ext hsaj.symm rfl) rfl, ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA'cp
              · rw [SimpleGraph.Walk.support_copy, weldLift_support, hA'cs]
            obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ qE0 hR₀p hqE0p
              (weld_cross_adj (Ne.symm hjE0) u0)
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hjE0 hmem.1)
            by_cases htaj : (t r).1 = j0
            · -- within: come back to `j0` and finish inside it
              have hBc : ∃ q : (Gs j0).Walk z (t r).2, q.IsPath ∧ q.support = B.support :=
                ⟨B.copy rfl (wInnerT_tgt htaj), by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hB, SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨Bc, hBcp, hBcs⟩ := hBc
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ Bc hR₁p hBcp
                ((weld_cross_adj (Ne.symm hjE0) z).symm)
                (by
                  intro w' hw' hmem
                  rw [hBcs] at hw'
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
                  · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                  · exact hjE0 h1.symm)
              refine ⟨R₂.copy rfl (Prod.ext htaj.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₂p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s,
                  List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair, hBcs]
                constructor
                · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_left _ h2⟩
                  · exact Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, by rw [← hqE0s]; exact h2⟩⟩)
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_right _ h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hrl, -⟩⟩)
                  · rw [hg0a] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl ⟨h1, h2⟩)
                    · exact Or.inr ⟨h1, h2⟩
                  · exfalso
                    have hne := ((hJtmem x.1).mp hj).1
                    rcases mem_weldWSet.mp hi with h | h
                    · exact hne ((hsaj.symm.trans h).symm)
                    · exact hne ((htaj.symm.trans h).symm)
                  · exact Or.inl (Or.inr ⟨h1, by rw [hqE0s]; exact h2⟩)
                  · exact absurd hrl hr
            · -- split with source in `j0`: exit to the target copy after the cut
              have haD : r ∈ D := (hDmem r).mpr ⟨hr, fun h => htaj (h.symm.trans hsaj)⟩
              have hBc : ∃ q : (Gs j0).Walk z (v r), q.IsPath ∧ q.support = B.support :=
                ⟨B.copy rfl (wInnerT_conn htaj), by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hB, SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨Bc, hBcp, hBcs⟩ := hBc
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ Bc hR₁p hBcp
                ((weld_cross_adj (Ne.symm hjE0) z).symm)
                (by
                  intro w' hw' hmem
                  rw [hBcs] at hw'
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
                  · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                  · exact hjE0 h1.symm)
              have hjc : (t r).1 ∈ Jt :=
                (hJtmem _).mpr ⟨htaj, ⟨r, mem_weldWSet.mpr (Or.inr rfl)⟩⟩
              have hic : r ∈ weldWSet s t (t r).1 := mem_weldWSet.mpr (Or.inr rfl)
              have hseg : ∃ q : (Gs (t r).1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (QJ _ hjc r hic).support := by
                refine ⟨(QJ _ hjc r hic).copy ?_ (wInnerT_tgt rfl), ?_, ?_⟩
                · rw [wInnerS_conn (fun h => htaj ((hsaj.symm.trans h).symm))]
                  exact hu'val.1 r hr
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQJp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ seg hR₂p hsegp
                (by
                  have h := weld_cross_adj (Gs := Gs) (M := M)
                    (show j0 ≠ (t r).1 from fun h => htaj h.symm) (v r)
                  rwa [show M j0 (t r).1 (v r) = u r from by
                    rw [hpart r haD, hsaj]] at h)
                (by
                  intro w' _ hmem
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact htaj h1
                  · exact (hjEnone r).2 h1
                  · exact htaj h1)
              refine ⟨R₃.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₃p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                  List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair, hBcs, hsegs]
                constructor
                · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_left _ h2⟩
                  · exact Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, by rw [← hqE0s]; exact h2⟩⟩)
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_right _ h2⟩
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hrl, -⟩⟩)
                  · rw [hg0a] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
                    · exact Or.inl (Or.inr ⟨h1, h2⟩)
                  · have hx1 : x.1 = (t r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact absurd ((hsaj.symm.trans h).symm) ((hJtmem x.1).mp hj).1
                      · exact h.symm
                    exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, by rw [hqE0s]; exact h2⟩))
                  · exact absurd hrl hr
          · -- split with target in `j0`: enter from the source copy, then the cut
            have htaj0 : (t r).1 = j0 := (htouch r).resolve_left hsaj
            have haD : r ∈ D := (hDmem r).mpr ⟨hr, fun h => hsaj (h.trans htaj0)⟩
            have hjc : (s r).1 ∈ Jt :=
              (hJtmem _).mpr ⟨hsaj, ⟨r, mem_weldWSet.mpr (Or.inl rfl)⟩⟩
            have hic : r ∈ weldWSet s t (s r).1 := mem_weldWSet.mpr (Or.inl rfl)
            have hseg : ∃ q : (Gs (s r).1).Walk (s r).2 (v r), q.IsPath ∧
                q.support = (QJ _ hjc r hic).support := by
              refine ⟨(QJ _ hjc r hic).copy (wInnerS_src rfl)
                (wInnerT_conn (fun h => hsaj (h.symm.trans htaj0))) , ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hQJp _ hjc _ hic
              · rw [SimpleGraph.Walk.support_copy]
            obtain ⟨seg, hsegp, hsegs⟩ := hseg
            have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) ((s r).1, v r), R.IsPath ∧
                R.support = (QJ _ hjc r hic).support.map (fun w' => ((s r).1, w')) := by
              refine ⟨(seg.map (weldLift Gs M (s r).1)).copy (Prod.ext rfl rfl) rfl, ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsegp
              · rw [SimpleGraph.Walk.support_copy, weldLift_support, hsegs]
            obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
            have hA'c : ∃ q : (Gs j0).Walk (u r) u0, q.IsPath ∧ q.support = A'.support :=
              ⟨A'.copy (wInnerS_conn hsaj) rfl, by
                rw [SimpleGraph.Walk.isPath_copy]; exact hA', SimpleGraph.Walk.support_copy ..⟩
            obtain ⟨A'c, hA'cp, hA'cs⟩ := hA'c
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ A'c hR₀p hA'cp
              (by
                have h := weld_cross_adj (Gs := Gs) (M := M)
                  (show (s r).1 ≠ j0 from hsaj) (v r)
                rwa [show M (s r).1 j0 (v r) = u r from by
                  rw [hpart r haD, htaj0]] at h)
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hsaj hmem.1.symm)
            rw [hA'cs] at hR₁s
            obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ qE0 hR₁p hqE0p
              (weld_cross_adj (Ne.symm hjE0) u0)
              (by
                intro w' _ hmem
                rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                · exact (hjEnone r).1 (h1.symm)
                · exact hjE0 h1)
            have hBc : ∃ q : (Gs j0).Walk z (t r).2, q.IsPath ∧ q.support = B.support :=
              ⟨B.copy rfl (wInnerT_tgt htaj0), by
                rw [SimpleGraph.Walk.isPath_copy]; exact hB, SimpleGraph.Walk.support_copy ..⟩
            obtain ⟨Bc, hBcp, hBcs⟩ := hBc
            obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ Bc hR₂p hBcp
              ((weld_cross_adj (Ne.symm hjE0) z).symm)
              (by
                intro w' hw' hmem
                rw [hBcs] at hw'
                rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
                · exact hsaj (h1.symm)
                · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                · exact hjE0 h1.symm)
            refine ⟨R₃.copy rfl (Prod.ext htaj0.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hR₃p
            · intro x
              rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                mem_map_pair, mem_map_pair, hBcs]
              constructor
              · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                · refine Or.inr (Or.inl ?_)
                  have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                  have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                  exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_left _ h2⟩
                · exact Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, by rw [← hqE0s]; exact h2⟩⟩)
                · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_right _ h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hrl, -⟩⟩)
                · rw [hg0a] at h2
                  rcases List.mem_append.mp h2 with h2 | h2
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                  · exact Or.inr ⟨h1, h2⟩
                · have hx1 : x.1 = (s r).1 := by
                    rcases mem_weldWSet.mp hi with h | h
                    · exact h.symm
                    · exact absurd ((htaj0.symm.trans h).symm) ((hJtmem x.1).mp hj).1
                  exact Or.inl (Or.inl (Or.inl ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩))
                · exact Or.inl (Or.inr ⟨h1, by rw [hqE0s]; exact h2⟩)
                · exact absurd hrl hr
        · -- an ordinary pair
          by_cases hsplit : (s r).1 = (t r).1
          · -- within `j0`
            have hsrj : (s r).1 = j0 := by
              rcases htouch r with h | h
              · exact h
              · exact hsplit.trans h
            have htrj : (t r).1 = j0 := hsplit.symm.trans hsrj
            refine ⟨((Q0 r hrmem).copy (wInnerS_src hsrj) (wInnerT_tgt htrj)).map
              (weldLift Gs M j0) |>.copy (Prod.ext hsrj.symm rfl) (Prod.ext htrj.symm rfl),
              ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              refine SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) ?_
              rw [SimpleGraph.Walk.isPath_copy]
              exact hQ0path r hrmem
            · intro x
              rw [SimpleGraph.Walk.support_copy, weldLift_support,
                SimpleGraph.Walk.support_copy, mem_map_pair]
              constructor
              · rintro ⟨h1, h2⟩
                exact Or.inl ⟨h1, by rw [hg0other r hr hra]; exact h2⟩
              · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hra', -⟩ | ⟨hrl, -⟩⟩)
                · exact ⟨h1, by rw [hg0other r hr hra] at h2; exact h2⟩
                · exfalso
                  have hne := ((hJtmem x.1).mp hj).1
                  rcases mem_weldWSet.mp hi with h | h
                  · exact hne ((hsrj.symm.trans h).symm)
                  · exact hne ((htrj.symm.trans h).symm)
                · exact absurd hra' hra
                · exact absurd hrl hr
          · -- split
            have hrD : r ∈ D := (hDmem r).mpr ⟨hr, hsplit⟩
            by_cases hsrj : (s r).1 = j0
            · have htrj : (t r).1 ≠ j0 := fun h => hsplit (hsrj.trans h.symm)
              have hjc : (t r).1 ∈ Jt :=
                (hJtmem _).mpr ⟨htrj, ⟨r, mem_weldWSet.mpr (Or.inr rfl)⟩⟩
              have hic : r ∈ weldWSet s t (t r).1 := mem_weldWSet.mpr (Or.inr rfl)
              have hseg : ∃ q : (Gs (t r).1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (QJ _ hjc r hic).support := by
                refine ⟨(QJ _ hjc r hic).copy ?_ (wInnerT_tgt rfl), ?_, ?_⟩
                · rw [wInnerS_conn (fun h => htrj ((hsrj.symm.trans h).symm))]
                  exact hu'val.1 r hr
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQJp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R, hRp, hRs⟩ := weld_splice
                (show j0 ≠ (t r).1 from fun h => htrj h.symm)
                ((Q0 r hrmem).copy (wInnerS_src hsrj) (wInnerT_conn htrj)) seg
                (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem) hsegp
                (by rw [hpart r hrD, hsrj])
              refine ⟨R.copy (Prod.ext hsrj.symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hsegs]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra]; exact h2⟩
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hra', -⟩ | ⟨hrl, -⟩⟩)
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra] at h2; exact h2⟩
                  · have hx1 : x.1 = (t r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact absurd ((hsrj.symm.trans h).symm) ((hJtmem x.1).mp hj).1
                      · exact h.symm
                    exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact absurd hra' hra
                  · exact absurd hrl hr
            · have htrj : (t r).1 = j0 := (htouch r).resolve_left hsrj
              have hjc : (s r).1 ∈ Jt :=
                (hJtmem _).mpr ⟨hsrj, ⟨r, mem_weldWSet.mpr (Or.inl rfl)⟩⟩
              have hic : r ∈ weldWSet s t (s r).1 := mem_weldWSet.mpr (Or.inl rfl)
              have hseg : ∃ q : (Gs (s r).1).Walk (s r).2 (v r), q.IsPath ∧
                  q.support = (QJ _ hjc r hic).support := by
                refine ⟨(QJ _ hjc r hic).copy (wInnerS_src rfl)
                  (wInnerT_conn (fun h => hsrj (h.symm.trans htrj))), ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQJp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R, hRp, hRs⟩ := weld_splice
                (show (s r).1 ≠ j0 from hsrj) seg
                ((Q0 r hrmem).copy (wInnerS_conn hsrj) (wInnerT_tgt htrj))
                hsegp (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem)
                (by rw [hpart r hrD, htrj])
              refine ⟨R.copy (Prod.ext rfl rfl) (Prod.ext htrj.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hsegs]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hra', -⟩ | ⟨hrl, -⟩⟩)
                  · exact Or.inr ⟨h1, by rw [hg0other r hr hra] at h2; exact h2⟩
                  · have hx1 : x.1 = (s r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact h.symm
                      · exact absurd ((htrj.symm.trans h).symm) ((hJtmem x.1).mp hj).1
                    exact Or.inl ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact absurd hra' hra
                  · exact absurd hrl hr
    choose P hPp hPchar using hpaths
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
      (insert j0 (insert jE Jt)) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨hj, -, -⟩ | ⟨h1, -⟩
      · rw [h1]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)
      · rw [h1]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rintro ⟨xj, xw⟩ hxJ
      rw [Finset.mem_insert, Finset.mem_insert] at hxJ
      rcases hxJ with rfl | rfl | hxJt
      · obtain ⟨i, hi, hmem⟩ := hQ0cov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · rw [hsuppA'] at hmem
            rcases List.mem_append.mp hmem with hmem2 | hmem2
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0a]; exact List.mem_append_left _ hmem2⟩)⟩
            · rw [List.mem_singleton] at hmem2
              exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0last, hmem2]
                exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0last, hmem2]
                exact List.mem_cons_self ..⟩)⟩
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0a]; exact List.mem_append_right _ hmem2⟩)⟩
        · have hilast : i ≠ Fin.last m := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
            rw [hg0other i hilast hia]; exact hmem⟩)⟩
      · obtain ⟨iE, hiE⟩ := hqEcov xw
        fin_cases iE
        · exact ⟨a, (hPchar a (xj, xw)).mpr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, hiE⟩⟩))⟩
        · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
            (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, hiE⟩⟩))⟩
      · obtain ⟨i, hi, hmem⟩ := hQJcov xj hxJt xw
        exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨hxJt, hi, hmem⟩))⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, hE1⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨hj', hi', h2'⟩ | ⟨h1', hE1'⟩
      · exact hg0disj r r' hrr' x.2 h2 h2'
      · exact ((hJtmem x.1).mp hj').1 h1
      · exact hjE0 (h1'.symm.trans h1)
      · exact ((hJtmem x.1).mp hj).1 h1'
      · exact hQJdis x.1 hj r hi r' hi' hrr' x.2 ⟨h2, h2'⟩
      · exact hjEJt (h1' ▸ hj)
      · exact hjE0 (h1.symm.trans h1')
      · exact hjEJt (h1 ▸ hj')
      · rcases hE1 with ⟨hra, hm0⟩ | ⟨hrl, hm1⟩ <;> rcases hE1' with ⟨hra', hm0'⟩ | ⟨hrl', hm1'⟩
        · exact hrr' (hra.trans hra'.symm)
        · exact hqEdis 0 1 (by decide) x.2 ⟨hm0, hm1'⟩
        · exact hqEdis 0 1 (by decide) x.2 ⟨hm0', hm1⟩
        · exact hrr' (hrl.trans hrl'.symm)

  · -- SUBCASE (β): every copy is touched
    have hall : ∀ j : Fin ell, (weldWSet s t j).Nonempty :=
      fun j => Finset.nonempty_iff_ne_empty.mpr (fun h => hE ⟨j, h⟩)
    -- the non-`j0` w-sets are pairwise disjoint and consist of split pairs
    have hWdisj : ∀ j ∈ Finset.univ.erase j0, ∀ j' ∈ Finset.univ.erase j0, j ≠ j' →
        Disjoint (weldWSet s t j) (weldWSet s t j') := by
      intro j hj j' hj' hjj'
      rw [Finset.disjoint_left]
      intro i hij hij'
      rcases mem_weldWSet.mp hij with h1 | h1 <;> rcases mem_weldWSet.mp hij' with h2 | h2
      · exact hjj' (h1.symm.trans h2)
      · rcases htouch i with h3 | h3
        · exact Finset.ne_of_mem_erase hj (h1.symm.trans h3)
        · exact Finset.ne_of_mem_erase hj' (h2.symm.trans h3)
      · rcases htouch i with h3 | h3
        · exact Finset.ne_of_mem_erase hj' (h2.symm.trans h3)
        · exact Finset.ne_of_mem_erase hj (h1.symm.trans h3)
      · exact hjj' (h1.symm.trans h2)
    have hbisub : (Finset.univ.erase j0).biUnion (fun j => weldWSet s t j) ⊆
        Finset.univ.filter (fun i => (s i).1 ≠ (t i).1) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨j, hj, hij⟩ := hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hh
      have hc : (s i).1 = j := by
        rcases mem_weldWSet.mp hij with h | h
        · exact h
        · exact hh.trans h
      have hc0 : (s i).1 = j0 := by
        rcases htouch i with h | h
        · exact h
        · exact hh.trans h
      exact Finset.ne_of_mem_erase hj (hc.symm.trans hc0)
    have hsum : ∑ j ∈ Finset.univ.erase j0, (weldWSet s t j).card
        = ((Finset.univ.erase j0).biUnion (fun j => weldWSet s t j)).card :=
      (Finset.card_biUnion hWdisj).symm
    have hsumub : ∑ j ∈ Finset.univ.erase j0, (weldWSet s t j).card ≤ m + 1 := by
      rw [hsum]
      exact le_trans (Finset.card_le_card hbisub) (le_trans (Finset.card_filter_le _ _)
        (by rw [Finset.card_univ, Fintype.card_fin]))
    have hsumlb : (Finset.univ.erase j0).card • 1
        ≤ ∑ j ∈ Finset.univ.erase j0, (weldWSet s t j).card :=
      Finset.card_nsmul_le_sum _ _ _ (fun j _ => Finset.card_pos.mpr (hall j))
    have hellcard : (Finset.univ.erase j0 : Finset (Fin ell)).card = ell - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hellm : ell = m + 2 := by
      rw [hellcard] at hsumlb
      simp only [smul_eq_mul, mul_one] at hsumlb
      omega
    -- every non-`j0` copy meets exactly one pair
    have hone : ∀ j : Fin ell, j ≠ j0 → (weldWSet s t j).card = 1 := by
      intro j hj
      have hjmem : j ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      have hsplit2 := Finset.add_sum_erase _ (fun j' => (weldWSet s t j').card) hjmem
      have hlb2 : ((Finset.univ.erase j0).erase j).card • 1
          ≤ ∑ j' ∈ (Finset.univ.erase j0).erase j, (weldWSet s t j').card :=
        Finset.card_nsmul_le_sum _ _ _ (fun j' _ => Finset.card_pos.mpr (hall j'))
      have hcard2 : ((Finset.univ.erase j0).erase j).card = ell - 2 := by
        rw [Finset.card_erase_of_mem hjmem, hellcard]
        omega
      have hpos := Finset.card_pos.mpr (hall j)
      rw [hcard2] at hlb2
      simp only [smul_eq_mul, mul_one] at hlb2
      omega
    -- every pair is split
    have hallsplit : ∀ i : Fin (m + 1), (s i).1 ≠ (t i).1 := by
      intro i
      have hcards : (Finset.univ.filter
          (fun i : Fin (m + 1) => (s i).1 ≠ (t i).1)).card = m + 1 := by
        have h1 := Finset.card_le_card hbisub
        rw [← hsum] at h1
        have h2 : ∑ j ∈ Finset.univ.erase j0, (weldWSet s t j).card = ell - 1 := by
          rw [Finset.sum_congr rfl (fun j hj => hone j (Finset.ne_of_mem_erase hj))]
          rw [Finset.sum_const, smul_eq_mul, mul_one, hellcard]
        rw [h2] at h1
        have h3 := Finset.card_filter_le Finset.univ
          (fun i : Fin (m + 1) => (s i).1 ≠ (t i).1)
        rw [Finset.card_univ, Fintype.card_fin] at h3
        omega
      have huniv : Finset.univ.filter (fun i : Fin (m + 1) => (s i).1 ≠ (t i).1)
          = Finset.univ := Finset.eq_univ_of_card _ (by
            rw [hcards, Fintype.card_fin])
      have := huniv ▸ Finset.mem_univ i
      rw [Finset.mem_filter] at this
      exact this.2
    -- a target-in-`j0` pair other than the carrier
    obtain ⟨ks, hksmem, hksa⟩ : ∃ ks, (t ks).1 = j0 ∧ ks ≠ a := by
      obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp hT2
      rw [Finset.mem_filter] at hi1 hi2
      by_cases h : i1 = a
      · exact ⟨i2, hi2.2, fun hh => hne (h.trans hh.symm)⟩
      · exact ⟨i1, hi1.2, h⟩
    have hsks : (s ks).1 ≠ j0 := fun h => hallsplit ks (h.trans hksmem.symm)
    have hkslast : ks ≠ Fin.last m := by
      intro h
      rw [h] at hksmem
      exact hlastT hksmem
    have hksD : ks ∈ D := (hDmem ks).mpr ⟨hkslast, hallsplit ks⟩
    -- the singleton-copy facts
    have hsingleton : ∀ j : Fin ell, j ≠ j0 → ∀ i ∈ weldWSet s t j, ∀ i' ∈ weldWSet s t j,
        i = i' := by
      intro j hj i hi i' hi'
      have h1 := hone j hj
      have h2 := Finset.card_le_one.mp (le_of_eq h1)
      exact h2 i hi i' hi'
    have hksW : ks ∈ weldWSet s t (s ks).1 := mem_weldWSet.mpr (Or.inl rfl)
    have hlastW : Fin.last m ∈ weldWSet s t (t (Fin.last m)).1 :=
      mem_weldWSet.mpr (Or.inr rfl)
    have hjsjn : (s ks).1 ≠ (t (Fin.last m)).1 := by
      intro h
      have := hsingleton (s ks).1 hsks ks hksW (Fin.last m) (by rw [h]; exact hlastW)
      exact hkslast this
    have hyz : y ≠ z := by
      intro h
      exact hdisjA y (SimpleGraph.Walk.end_mem_support Apre) z
        (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support B)) h
    -- the fresh entry vertex in the source copy of `ks`
    have hx0avoid : ({(s ks).2} ∪ {(M (s ks).1 (t (Fin.last m)).1).symm (t (Fin.last m)).2}
        : Finset W).card < 2 * (m + 1) - 1 := by
      have h1 := Finset.card_union_le ({(s ks).2} : Finset W)
        ({(M (s ks).1 (t (Fin.last m)).1).symm (t (Fin.last m)).2} : Finset W)
      rw [Finset.card_singleton, Finset.card_singleton] at h1
      omega
    obtain ⟨x0, hcolx0, hx0avoids⟩ := S.exists_avoid (s ks).1 b _ hx0avoid
    have hx0s : x0 ≠ (s ks).2 := by
      intro h
      exact hx0avoids (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr h)))
    have hy0tn : M (s ks).1 (t (Fin.last m)).1 x0 ≠ (t (Fin.last m)).2 := by
      intro h
      refine hx0avoids (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr ?_)))
      rw [← h, Equiv.symm_apply_apply]
    -- the first cut vertex is not the `ks`-connector (this is where matching coherence
    -- enters: Coleman's "u₀* ≠ v₂ since u₂ ≠ u₀")
    have hvks_u0 : v ks ≠ M j0 (s ks).1 u0 := by
      intro h
      have h2 : M (s ks).1 j0 (v ks) = u0 := by
        rw [h, S.hM]
        exact Equiv.symm_apply_apply ..
      have h3 : u ks = u0 := by
        rw [hpart ks hksD, hksmem]
        exact h2
      have h4 : u ks ∈ (Q0 ks (Finset.mem_erase.mpr ⟨hkslast, Finset.mem_univ ks⟩)).support := by
        have h5 := SimpleGraph.Walk.start_mem_support
          ((Q0 ks (Finset.mem_erase.mpr ⟨hkslast, Finset.mem_univ ks⟩)).copy
            (wInnerS_conn hsks) rfl)
        rwa [SimpleGraph.Walk.support_copy] at h5
      have h6 : u0 ∈ (Q0 a ha0).support := by
        rw [hsuppA]
        refine List.mem_append_left _ ?_
        rw [hsuppA']
        exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support A')
      rw [h3] at h4
      exact hQ0disj ks (Finset.mem_erase.mpr ⟨hkslast, Finset.mem_univ ks⟩) a ha0 hksa u0
        ⟨h4, h6⟩
    -- colors across the two auxiliary copies
    have hcu0js : col ((s ks).1, M j0 (s ks).1 u0) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M)
        (Ne.symm hsks) u0)
      rw [hcolu0] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    have hczjn : col ((t (Fin.last m)).1, M j0 (t (Fin.last m)).1 z) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M)
        (fun hh => hlastT hh.symm) z)
      rw [hcolz] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcyjn : col ((t (Fin.last m)).1, M j0 (t (Fin.last m)).1 y) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M)
        (fun hh => hlastT hh.symm) y)
      rw [hcoly] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcy0jn : col ((t (Fin.last m)).1, M (s ks).1 (t (Fin.last m)).1 x0) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hjsjn x0)
      rw [hcolx0] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    -- the `js` 2-cover: the `ks`-pair's source segment and the bridge entry
    have hd2c : OppositeDemand (fun w' => col ((s ks).1, w'))
        ![(s ks).2, x0] ![v ks, M j0 (s ks).1 u0] := by
      have hcs : col ((s ks).1, (s ks).2) = b := hmono.1 ks
      have hcv := hvcol ks hksD
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · show col ((s ks).1, (s ks).2) ≠ col ((s ks).1, v ks)
          rw [hcs, hcv]
          cases b <;> simp
        · show col ((s ks).1, x0) ≠ col ((s ks).1, M j0 (s ks).1 u0)
          rw [hcolx0, hcu0js]
          cases b <;> simp
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd (h : (s ks).2 = x0).symm hx0s
        · exact absurd (h : x0 = (s ks).2) hx0s
        · rfl
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd (h : v ks = M j0 (s ks).1 u0) hvks_u0
        · exact absurd (h : M j0 (s ks).1 u0 = v ks).symm hvks_u0
        · rfl
      · intro i k
        fin_cases i <;> fin_cases k
        · intro h
          have hcast : (s ks).2 = v ks := h
          rw [hcast] at hcs
          rw [hcv] at hcs
          cases b <;> simp at hcs
        · intro h
          have hcast : (s ks).2 = M j0 (s ks).1 u0 := h
          rw [hcast] at hcs
          rw [hcu0js] at hcs
          cases b <;> simp at hcs
        · intro h
          have hcast : x0 = v ks := h
          rw [hcast] at hcolx0
          rw [hcv] at hcolx0
          cases b <;> simp at hcolx0
        · intro h
          have hcast : x0 = M j0 (s ks).1 u0 := h
          rw [hcast] at hcolx0
          rw [hcu0js] at hcolx0
          cases b <;> simp at hcolx0
    obtain ⟨q2, hq2p, hq2cov, hq2dis⟩ := S.inner_cover (s ks).1 (by omega) (by omega) _ _ hd2c
    -- the `jn` 2-cover: the rerouted cut and the last pair's finish
    have hd3c : OppositeDemand (fun w' => col ((t (Fin.last m)).1, w'))
        ![M j0 (t (Fin.last m)).1 z, M j0 (t (Fin.last m)).1 y]
        ![M (s ks).1 (t (Fin.last m)).1 x0, (t (Fin.last m)).2] := by
      have hct : col ((t (Fin.last m)).1, (t (Fin.last m)).2) = !b := hmono.2.1 (Fin.last m)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · show col ((t (Fin.last m)).1, M j0 (t (Fin.last m)).1 z)
              ≠ col ((t (Fin.last m)).1, M (s ks).1 (t (Fin.last m)).1 x0)
          rw [hczjn, hcy0jn]
          cases b <;> simp
        · show col ((t (Fin.last m)).1, M j0 (t (Fin.last m)).1 y)
              ≠ col ((t (Fin.last m)).1, (t (Fin.last m)).2)
          rw [hcyjn, hct]
          cases b <;> simp
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd ((M j0 (t (Fin.last m)).1).injective
            (h : M j0 (t (Fin.last m)).1 z = M j0 (t (Fin.last m)).1 y)) (Ne.symm hyz)
        · exact absurd ((M j0 (t (Fin.last m)).1).injective
            (h : M j0 (t (Fin.last m)).1 y = M j0 (t (Fin.last m)).1 z)) hyz
        · rfl
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd (h : M (s ks).1 (t (Fin.last m)).1 x0 = (t (Fin.last m)).2) hy0tn
        · exact absurd (h : (t (Fin.last m)).2 = M (s ks).1 (t (Fin.last m)).1 x0).symm hy0tn
        · rfl
      · intro i k
        fin_cases i <;> fin_cases k
        · intro h
          have hcast : M j0 (t (Fin.last m)).1 z = M (s ks).1 (t (Fin.last m)).1 x0 := h
          rw [hcast] at hczjn
          rw [hcy0jn] at hczjn
          cases b <;> simp at hczjn
        · intro h
          have hcast : M j0 (t (Fin.last m)).1 z = (t (Fin.last m)).2 := h
          rw [hcast] at hczjn
          rw [hct] at hczjn
          cases b <;> simp at hczjn
        · intro h
          have hcast : M j0 (t (Fin.last m)).1 y = M (s ks).1 (t (Fin.last m)).1 x0 := h
          rw [hcast] at hcyjn
          rw [hcy0jn] at hcyjn
          cases b <;> simp at hcyjn
        · intro h
          have hcast : M j0 (t (Fin.last m)).1 y = (t (Fin.last m)).2 := h
          rw [hcast] at hcyjn
          rw [hct] at hcyjn
          cases b <;> simp at hcyjn
    obtain ⟨q3, hq3p, hq3cov, hq3dis⟩ := S.inner_cover (t (Fin.last m)).1
      (by omega) (by omega) _ _ hd3c
    -- the remaining copies and their singleton families
    set Jt : Finset (Fin ell) := ((Finset.univ.erase j0).erase (s ks).1).erase
      (t (Fin.last m)).1 with hJt
    have hJtmem : ∀ j, j ∈ Jt ↔
        (j ≠ (t (Fin.last m)).1 ∧ j ≠ (s ks).1 ∧ j ≠ j0) := by
      intro j
      rw [hJt, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
      simp
    have hfamJ : ∀ j ∈ Jt, ∃ Q : ∀ i ∈ weldWSet s t j,
        (Gs j).Walk (wInnerS s u j i) (wInnerT t v j i),
        (∀ i (hi : i ∈ weldWSet s t j), (Q i hi).IsPath) ∧
        (∀ x : W, ∃ i, ∃ hi : i ∈ weldWSet s t j, x ∈ (Q i hi).support) ∧
        (∀ i (hi : i ∈ weldWSet s t j), ∀ k (hk : k ∈ weldWSet s t j), i ≠ k →
          ∀ x, ¬ (x ∈ (Q i hi).support ∧ x ∈ (Q k hk).support)) := by
      intro j hjJt
      obtain ⟨hjn, hjs, hj0ne⟩ := (hJtmem j).mp hjJt
      have hmemD : ∀ i ∈ weldWSet s t j, i ∈ D := by
        intro i hi
        refine (hDmem i).mpr ⟨?_, hallsplit i⟩
        intro hilast
        subst hilast
        rcases mem_weldWSet.mp hi with h | h
        · exact hj0ne (h.symm.trans hlastS)
        · exact hjn h.symm
      apply S.inner_family (b := b) j _ (hall j) (hw j hj0ne)
      · intro i hi
        by_cases hsij : (s i).1 = j
        · rw [wInnerS_src hsij, ← hsij]
          exact hmono.1 i
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          rw [wInnerS_conn hsij, ← htij]
          exact hucol i (hmemD i hi)
      · intro i hi
        by_cases htij : (t i).1 = j
        · rw [wInnerT_tgt htij, ← htij]
          exact hmono.2.1 i
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          rw [wInnerT_conn htij, ← hsij]
          exact hvcol i (hmemD i hi)
      · intro i hi k hk hik
        by_cases hsij : (s i).1 = j <;> by_cases hskj : (s k).1 = j
        · rw [wInnerS_src hsij, wInnerS_src hskj]
          intro he
          exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
        · have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
          rw [wInnerS_src hsij, wInnerS_conn hskj]
          exact fun he => huS k (hmemD k hk) i (hsij.trans htkj.symm) he.symm
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          rw [wInnerS_conn hsij, wInnerS_src hskj]
          exact huS i (hmemD i hi) k (hskj.trans htij.symm)
        · have htij : (t i).1 = j := (mem_weldWSet.mp hi).resolve_left hsij
          have htkj : (t k).1 = j := (mem_weldWSet.mp hk).resolve_left hskj
          rw [wInnerS_conn hsij, wInnerS_conn hskj]
          exact huu k (hmemD k hk) i (hmemD i hi) hik (htij.trans htkj.symm)
      · intro i hi k hk hik
        by_cases htij : (t i).1 = j <;> by_cases htkj : (t k).1 = j
        · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
          intro he
          exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
        · have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
          rw [wInnerT_tgt htij, wInnerT_conn htkj]
          exact fun he => hvT k (hmemD k hk) i (htij.trans hskj.symm) he.symm
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          rw [wInnerT_conn htij, wInnerT_tgt htkj]
          exact hvT i (hmemD i hi) k (htkj.trans hsij.symm)
        · have hsij : (s i).1 = j := (mem_weldWSet.mp hi).resolve_right htij
          have hskj : (s k).1 = j := (mem_weldWSet.mp hk).resolve_right htkj
          rw [wInnerT_conn htij, wInnerT_conn htkj]
          exact hvv k (hmemD k hk) i (hmemD i hi) hik (hsij.trans hskj.symm)
    choose QF hQFp hQFcov hQFdis using hfamJ
    have hQtrans : ∀ (j j' : Fin ell) (he : j = j') (hj : j ∈ Jt) (hj' : j' ∈ Jt)
        (r : Fin (m + 1)) (hi : r ∈ weldWSet s t j) (hi' : r ∈ weldWSet s t j') (x2 : W),
        x2 ∈ (QF j hj r hi).support → x2 ∈ (QF j' hj' r hi').support := by
      intro j j' he
      subst he
      intro hj hj' r hi hi' x2 h
      exact h
    -- the `j0`-side segment lists
    set g0 : Fin (m + 1) → List W := fun r =>
      if hr : r = Fin.last m then ((s (Fin.last m)).2 :: [y])
      else if r = a then A'.support ++ B.support
      else (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support with hg0
    have hg0last : g0 (Fin.last m) = ((s (Fin.last m)).2 :: [y]) := by
      rw [hg0]
      exact dif_pos rfl
    have hg0a : g0 a = A'.support ++ B.support := by
      simp [hg0, halast]
    have hg0other : ∀ r, ∀ hr : r ≠ Fin.last m, r ≠ a →
        g0 r = (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
      intro r hr hra
      simp only [hg0]
      rw [dif_neg hr, if_neg hra]
    have hsubA' : ∀ x2 : W, x2 ∈ A'.support → x2 ∈ Apre.support := by
      intro x2 h
      rw [hsuppA']
      exact List.mem_append_left _ h
    have hsub_qa : ∀ x2 : W, x2 ∈ g0 a → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg0a] at h
      rw [hsuppA]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (hsubA' x2 h)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hsub_last : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg0last] at h
      rcases List.mem_cons.mp h with h | h
      · rw [h, hsuppA]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · rw [List.mem_singleton] at h
        rw [h, hsuppA]
        exact List.mem_append_left _ (by
          rw [hsuppA']
          exact List.mem_append_right _ (List.mem_singleton_self _))
    have hlast_va : ∀ x2 : W, x2 ∈ g0 (Fin.last m) → x2 ∈ g0 a → False := by
      intro x2 h h'
      rw [hg0last] at h
      rw [hg0a] at h'
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
      intro r r' hrr' x2 h h'
      by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
      · exact hrr' (hr.trans hr'.symm)
      · rw [hr] at h
        by_cases hra : r' = a
        · rw [hra] at h'
          exact hlast_va x2 h h'
        · rw [hg0other r' hr' hra] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra x2 ⟨h', hsub_last x2 h⟩
      · rw [hr'] at h'
        by_cases hra : r = a
        · rw [hra] at h
          exact hlast_va x2 h' h
        · rw [hg0other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_last x2 h'⟩
      · by_cases hra : r = a <;> by_cases hra' : r' = a
        · exact hrr' (hra.trans hra'.symm)
        · rw [hra] at h
          rw [hg0other r' hr' hra'] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra' x2 ⟨h', hsub_qa x2 h⟩
        · rw [hra'] at h'
          rw [hg0other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_qa x2 h'⟩
        · rw [hg0other r hr hra] at h
          rw [hg0other r' hr' hra'] at h'
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    -- the auxiliary segments with clean endpoints
    have hq20' : ∃ q : (Gs (s ks).1).Walk (s ks).2 (v ks), q.IsPath ∧
        q.support = (q2 0).support :=
      ⟨(q2 0).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hq2p 0, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨q20c, hq20p, hq20s⟩ := hq20'
    have hq21' : ∃ q : (Gs (s ks).1).Walk (M j0 (s ks).1 u0) x0, q.IsPath ∧
        ∀ x2 : W, x2 ∈ q.support ↔ x2 ∈ (q2 1).support := by
      refine ⟨(q2 1).reverse.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (hq2p 1).reverse
      · intro x2
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse]
    obtain ⟨q21c, hq21p, hq21m⟩ := hq21'
    have hq30' : ∃ q : (Gs (t (Fin.last m)).1).Walk (M (s ks).1 (t (Fin.last m)).1 x0)
        (M j0 (t (Fin.last m)).1 z), q.IsPath ∧
        ∀ x2 : W, x2 ∈ q.support ↔ x2 ∈ (q3 0).support := by
      refine ⟨(q3 0).reverse.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (hq3p 0).reverse
      · intro x2
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse]
    obtain ⟨q30c, hq30p, hq30m⟩ := hq30'
    have hq31' : ∃ q : (Gs (t (Fin.last m)).1).Walk (M j0 (t (Fin.last m)).1 y)
        (t (Fin.last m)).2, q.IsPath ∧ q.support = (q3 1).support :=
      ⟨(q3 1).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hq3p 1, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨q31c, hq31p, hq31s⟩ := hq31'
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j0 ∧ x.2 ∈ g0 r) ∨
            (∃ (hj : x.1 ∈ Jt) (hi : r ∈ weldWSet s t x.1), x.2 ∈ (QF x.1 hj r hi).support) ∨
            (x.1 = (s ks).1 ∧ ((r = ks ∧ x.2 ∈ (q2 0).support) ∨
              (r = a ∧ x.2 ∈ (q2 1).support))) ∨
            (x.1 = (t (Fin.last m)).1 ∧ ((r = a ∧ x.2 ∈ (q3 0).support) ∨
              (r = Fin.last m ∧ x.2 ∈ (q3 1).support)))) := by
      intro r
      by_cases hr : r = Fin.last m
      · -- the last pair
        subst hr
        have hsnwp : (SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil :
            (Gs j0).Walk (s (Fin.last m)).2 y).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcoly
          rw [← h] at h1
          have h2 := hmono.1 (Fin.last m)
          rw [hpairlast] at h2
          rw [h2] at h1
          cases b <;> simp at h1
        have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j0, y), R.IsPath ∧
            R.support = [(s (Fin.last m)).2, y].map (fun w' => (j0, w')) := by
          refine ⟨((SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil).map
            (weldLift Gs M j0)).copy (Prod.ext hlastS.symm rfl) rfl, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsnwp
          · rw [SimpleGraph.Walk.support_copy, weldLift_support,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
        obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
        obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q31c hR₀p hq31p
          (weld_cross_adj (fun hh => hlastT hh.symm) y)
          (by
            intro w' _ hmem
            rw [hR₀s, mem_map_pair] at hmem
            exact hlastT hmem.1)
        refine ⟨R₁.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₁p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s, mem_map_pair,
            mem_map_pair, hq31s]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · refine Or.inl ⟨h1, ?_⟩
              rw [hg0last]
              simpa using h2
            · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inr ⟨rfl, h2⟩⟩))
          · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hrk, -⟩ | ⟨hra, -⟩⟩ |
              ⟨h1, ⟨hra, -⟩ | ⟨-, h2⟩⟩)
            · refine Or.inl ⟨h1, ?_⟩
              rw [hg0last] at h2
              simpa using h2
            · exfalso
              rcases mem_weldWSet.mp hi with h | h
              · exact ((hJtmem x.1).mp hj).2.2 (h.symm.trans hlastS)
              · exact ((hJtmem x.1).mp hj).1 h.symm
            · exact absurd hrk.symm hkslast
            · exact absurd hra.symm halast
            · exact absurd hra.symm halast
            · exact Or.inr ⟨h1, h2⟩
      · have hrmem : r ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))) :=
          Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
        by_cases hrk : r = ks
        · -- the `ks` pair: its source-copy segment from the 2-cover, then its `j0` segment
          subst hrk
          have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) ((s r).1, v r), R.IsPath ∧
              R.support = (q2 0).support.map (fun w' => ((s r).1, w')) := by
            refine ⟨(q20c.map (weldLift Gs M (s r).1)).copy (Prod.ext rfl rfl) rfl, ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hq20p
            · rw [SimpleGraph.Walk.support_copy, weldLift_support, hq20s]
          obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
          have hQ0c : ∃ q : (Gs j0).Walk (u r) (t r).2, q.IsPath ∧
              q.support = (Q0 r hrmem).support := by
            refine ⟨(Q0 r hrmem).copy (wInnerS_conn hsks) (wInnerT_tgt hksmem), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hQ0path r hrmem
            · rw [SimpleGraph.Walk.support_copy]
          obtain ⟨Q0c, hQ0cp, hQ0cs⟩ := hQ0c
          obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Q0c hR₀p hQ0cp
            (by
              have h := weld_cross_adj (Gs := Gs) (M := M) hsks (v r)
              rwa [show M (s r).1 j0 (v r) = u r from by
                rw [hpart r hksD, hksmem]] at h)
            (by
              intro w' _ hmem
              rw [hR₀s, mem_map_pair] at hmem
              exact hsks hmem.1.symm)
          refine ⟨R₁.copy rfl (Prod.ext hksmem.symm rfl), ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact hR₁p
          · intro x
            rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s, mem_map_pair,
              mem_map_pair, hQ0cs]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩))
              · exact Or.inl ⟨h1, by rw [hg0other r hkslast hksa]; exact h2⟩
            · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hra, -⟩⟩ |
                ⟨h1, ⟨hra, -⟩ | ⟨hrl, -⟩⟩)
              · exact Or.inr ⟨h1, by rw [hg0other r hkslast hksa] at h2; exact h2⟩
              · exfalso
                have hin : r ∈ weldWSet s t x.1 := hi
                rcases mem_weldWSet.mp hin with h | h
                · exact ((hJtmem x.1).mp hj).2.1 h.symm
                · exact ((hJtmem x.1).mp hj).2.2 (h.symm.trans hksmem)
              · exact Or.inl ⟨h1, h2⟩
              · exact absurd hra hksa
              · exact absurd hra hksa
              · exact absurd hrl hkslast
        · by_cases hra : r = a
          · -- the carrier pair: thread the cut through both auxiliary copies
            subst hra
            have hjsJt' : ∀ c : Fin ell, r ∈ weldWSet s t c → c ≠ j0 → c ∈ Jt := by
              intro c hc hc0
              refine (hJtmem c).mpr ⟨?_, ?_, hc0⟩
              · intro h
                exact halast (hsingleton c hc0 r hc (Fin.last m) (by rw [h]; exact hlastW))
              · intro h
                exact hksa (hsingleton c hc0 r hc ks (by rw [h]; exact hksW)).symm
            by_cases hsaj : (s r).1 = j0
            · have hta : (t r).1 ≠ j0 := fun h => hallsplit r (hsaj.trans h.symm)
              have hjc : (t r).1 ∈ Jt :=
                hjsJt' (t r).1 (mem_weldWSet.mpr (Or.inr rfl)) hta
              have hic : r ∈ weldWSet s t (t r).1 := mem_weldWSet.mpr (Or.inr rfl)
              have hA'c : ∃ q : (Gs j0).Walk (s r).2 u0, q.IsPath ∧ q.support = A'.support :=
                ⟨A'.copy (wInnerS_src hsaj) rfl, by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hA',
                  SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨A'c, hA'cp, hA'cs⟩ := hA'c
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j0, u0), R.IsPath ∧
                  R.support = A'.support.map (fun w' => (j0, w')) := by
                refine ⟨(A'c.map (weldLift Gs M j0)).copy (Prod.ext hsaj.symm rfl) rfl, ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hA'cp
                · rw [SimpleGraph.Walk.support_copy, weldLift_support, hA'cs]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q21c hR₀p hq21p
                (weld_cross_adj (Ne.symm hsks) u0)
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hsks hmem.1)
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ q30c hR₁p hq30p
                (weld_cross_adj hjsjn x0)
                (by
                  intro w' _ hmem
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                  · exact hlastT h1
                  · exact hjsjn (h1.symm)
                )
              have hBc : ∃ q : (Gs j0).Walk z (v r), q.IsPath ∧ q.support = B.support :=
                ⟨B.copy rfl (wInnerT_conn hta), by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hB,
                  SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨Bc, hBcp, hBcs⟩ := hBc
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ Bc hR₂p hBcp
                ((weld_cross_adj (fun hh => hlastT hh.symm) z).symm)
                (by
                  intro w' hw' hmem
                  rw [hBcs] at hw'
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨-, h2⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                  · exact hsks h1.symm
                  · exact hlastT h1.symm)
              have hseg : ∃ q : (Gs (t r).1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (QF _ hjc r hic).support := by
                refine ⟨(QF _ hjc r hic).copy ?_ (wInnerT_tgt rfl), ?_, ?_⟩
                · rw [wInnerS_conn (fun h => hta ((hsaj.symm.trans h).symm))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQFp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R₄, hR₄p, hR₄s⟩ := weld_splice_snoc R₃ seg hR₃p hsegp
                (by
                  have h := weld_cross_adj (Gs := Gs) (M := M)
                    (show j0 ≠ (t r).1 from fun h => hta h.symm) (v r)
                  rwa [show M j0 (t r).1 (v r) = u r from by
                    rw [hpart r ((hDmem r).mpr ⟨hr, hallsplit r⟩), hsaj]] at h)
                (by
                  intro w' _ hmem
                  rw [hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append,
                    hR₀s, mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ((⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact hta h1
                  · exact ((hJtmem (t r).1).mp hjc).2.1 h1
                  · exact ((hJtmem (t r).1).mp hjc).1 h1
                  · exact hta h1)
              refine ⟨R₄.copy rfl (Prod.ext rfl rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₄p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₄s, List.mem_append, hR₃s,
                  List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair,
                  hBcs, hsegs]
                constructor
                · rintro ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_left _ h2⟩
                  · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, (hq21m x.2).mp h2⟩⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, (hq30m x.2).mp h2⟩⟩))
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_right _ h2⟩
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hrk, -⟩ | ⟨-, h2⟩⟩ |
                    ⟨h1, ⟨-, h2⟩ | ⟨hrl, -⟩⟩)
                  · rw [hg0a] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, h2⟩)))
                    · exact Or.inl (Or.inr ⟨h1, h2⟩)
                  · have hx1 : x.1 = (t r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact absurd ((hsaj.symm.trans h).symm) ((hJtmem x.1).mp hj).2.2
                      · exact h.symm
                    exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact absurd hrk.symm hksa
                  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, (hq21m x.2).mpr h2⟩)))
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, (hq30m x.2).mpr h2⟩))
                  · exact absurd hrl hr
            · -- target in `j0`
              have htaj0 : (t r).1 = j0 := (htouch r).resolve_left hsaj
              have hjc : (s r).1 ∈ Jt :=
                hjsJt' (s r).1 (mem_weldWSet.mpr (Or.inl rfl)) hsaj
              have hic : r ∈ weldWSet s t (s r).1 := mem_weldWSet.mpr (Or.inl rfl)
              have hseg : ∃ q : (Gs (s r).1).Walk (s r).2 (v r), q.IsPath ∧
                  q.support = (QF _ hjc r hic).support := by
                refine ⟨(QF _ hjc r hic).copy (wInnerS_src rfl)
                  (wInnerT_conn (fun h => hsaj (h.symm.trans htaj0))), ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQFp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) ((s r).1, v r), R.IsPath ∧
                  R.support = (QF _ hjc r hic).support.map (fun w' => ((s r).1, w')) := by
                refine ⟨(seg.map (weldLift Gs M (s r).1)).copy (Prod.ext rfl rfl) rfl, ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsegp
                · rw [SimpleGraph.Walk.support_copy, weldLift_support, hsegs]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              have hA'c : ∃ q : (Gs j0).Walk (u r) u0, q.IsPath ∧ q.support = A'.support :=
                ⟨A'.copy (wInnerS_conn hsaj) rfl, by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hA',
                  SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨A'c, hA'cp, hA'cs⟩ := hA'c
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ A'c hR₀p hA'cp
                (by
                  have h := weld_cross_adj (Gs := Gs) (M := M)
                    (show (s r).1 ≠ j0 from hsaj) (v r)
                  rwa [show M (s r).1 j0 (v r) = u r from by
                    rw [hpart r ((hDmem r).mpr ⟨hr, hallsplit r⟩), htaj0]] at h)
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hsaj hmem.1.symm)
              rw [hA'cs] at hR₁s
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ q21c hR₁p hq21p
                (weld_cross_adj (Ne.symm hsks) u0)
                (by
                  intro w' _ hmem
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                  · exact ((hJtmem (s r).1).mp hjc).2.1 h1.symm
                  · exact hsks h1)
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ q30c hR₂p hq30p
                (weld_cross_adj hjsjn x0)
                (by
                  intro w' _ hmem
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact ((hJtmem (s r).1).mp hjc).1 h1.symm
                  · exact hlastT h1
                  · exact hjsjn h1.symm)
              have hBc : ∃ q : (Gs j0).Walk z (t r).2, q.IsPath ∧ q.support = B.support :=
                ⟨B.copy rfl (wInnerT_tgt htaj0), by
                  rw [SimpleGraph.Walk.isPath_copy]; exact hB,
                  SimpleGraph.Walk.support_copy ..⟩
              obtain ⟨Bc, hBcp, hBcs⟩ := hBc
              obtain ⟨R₄, hR₄p, hR₄s⟩ := weld_splice_snoc R₃ Bc hR₃p hBcp
                ((weld_cross_adj (fun hh => hlastT hh.symm) z).symm)
                (by
                  intro w' hw' hmem
                  rw [hBcs] at hw'
                  rw [hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append,
                    hR₀s, mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ((⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact hsaj h1.symm
                  · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                  · exact hsks h1.symm
                  · exact hlastT h1.symm)
              refine ⟨R₄.copy rfl (Prod.ext htaj0.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₄p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₄s, List.mem_append, hR₃s,
                  List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair,
                  hBcs]
                constructor
                · rintro ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_left _ h2⟩
                  · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, (hq21m x.2).mp h2⟩⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, (hq30m x.2).mp h2⟩⟩))
                  · exact Or.inl ⟨h1, by rw [hg0a]; exact List.mem_append_right _ h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hrk, -⟩ | ⟨-, h2⟩⟩ |
                    ⟨h1, ⟨-, h2⟩ | ⟨hrl, -⟩⟩)
                  · rw [hg0a] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, h2⟩)))
                    · exact Or.inr ⟨h1, h2⟩
                  · have hx1 : x.1 = (s r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact h.symm
                      · exact absurd ((htaj0.symm.trans h).symm) ((hJtmem x.1).mp hj).2.2
                    exact Or.inl (Or.inl (Or.inl (Or.inl
                      ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩)))
                  · exact absurd hrk.symm hksa
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, (hq21m x.2).mpr h2⟩))
                  · exact Or.inl (Or.inr ⟨h1, (hq30m x.2).mpr h2⟩)
                  · exact absurd hrl hr
          · -- an ordinary pair
            have hrD : r ∈ D := (hDmem r).mpr ⟨hr, hallsplit r⟩
            have hjcJ : ∀ c : Fin ell, r ∈ weldWSet s t c → c ≠ j0 → c ∈ Jt := by
              intro c hc hc0
              refine (hJtmem c).mpr ⟨?_, ?_, hc0⟩
              · intro h
                exact hr (hsingleton c hc0 r hc (Fin.last m) (by rw [h]; exact hlastW))
              · intro h
                exact hrk (hsingleton c hc0 r hc ks (by rw [h]; exact hksW))
            by_cases hsrj : (s r).1 = j0
            · have htrj : (t r).1 ≠ j0 := fun h => hallsplit r (hsrj.trans h.symm)
              have hjc : (t r).1 ∈ Jt := hjcJ (t r).1 (mem_weldWSet.mpr (Or.inr rfl)) htrj
              have hic : r ∈ weldWSet s t (t r).1 := mem_weldWSet.mpr (Or.inr rfl)
              have hseg : ∃ q : (Gs (t r).1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (QF _ hjc r hic).support := by
                refine ⟨(QF _ hjc r hic).copy ?_ (wInnerT_tgt rfl), ?_, ?_⟩
                · rw [wInnerS_conn (fun h => htrj ((hsrj.symm.trans h).symm))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQFp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R, hRp, hRs⟩ := weld_splice
                (show j0 ≠ (t r).1 from fun h => htrj h.symm)
                ((Q0 r hrmem).copy (wInnerS_src hsrj) (wInnerT_conn htrj)) seg
                (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem) hsegp
                (by rw [hpart r hrD, hsrj])
              refine ⟨R.copy (Prod.ext hsrj.symm rfl) (Prod.ext rfl rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hsegs]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra]; exact h2⟩
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hrk', -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hra', -⟩ | ⟨hrl, -⟩⟩)
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra] at h2; exact h2⟩
                  · have hx1 : x.1 = (t r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact absurd ((hsrj.symm.trans h).symm) ((hJtmem x.1).mp hj).2.2
                      · exact h.symm
                    exact Or.inr ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact absurd hrk' hrk
                  · exact absurd hra' hra
                  · exact absurd hra' hra
                  · exact absurd hrl hr
            · have htrj0 : (t r).1 = j0 := (htouch r).resolve_left hsrj
              have hjc : (s r).1 ∈ Jt := hjcJ (s r).1 (mem_weldWSet.mpr (Or.inl rfl)) hsrj
              have hic : r ∈ weldWSet s t (s r).1 := mem_weldWSet.mpr (Or.inl rfl)
              have hseg : ∃ q : (Gs (s r).1).Walk (s r).2 (v r), q.IsPath ∧
                  q.support = (QF _ hjc r hic).support := by
                refine ⟨(QF _ hjc r hic).copy (wInnerS_src rfl)
                  (wInnerT_conn (fun h => hsrj (h.symm.trans htrj0))), ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQFp _ hjc _ hic
                · rw [SimpleGraph.Walk.support_copy]
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R, hRp, hRs⟩ := weld_splice
                (show (s r).1 ≠ j0 from hsrj) seg
                ((Q0 r hrmem).copy (wInnerS_conn hsrj) (wInnerT_tgt htrj0))
                hsegp (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem)
                (by rw [hpart r hrD, htrj0])
              refine ⟨R.copy (Prod.ext rfl rfl) (Prod.ext htrj0.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hsegs]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · refine Or.inr (Or.inl ?_)
                    have hj' : x.1 ∈ Jt := by rw [h1]; exact hjc
                    have hi' : r ∈ weldWSet s t x.1 := by rw [h1]; exact hic
                    exact ⟨hj', hi', hQtrans _ x.1 h1.symm hjc hj' _ hic hi' x.2 h2⟩
                  · exact Or.inl ⟨h1, by rw [hg0other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, ⟨hrk', -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hra', -⟩ | ⟨hrl, -⟩⟩)
                  · exact Or.inr ⟨h1, by rw [hg0other r hr hra] at h2; exact h2⟩
                  · have hx1 : x.1 = (s r).1 := by
                      rcases mem_weldWSet.mp hi with h | h
                      · exact h.symm
                      · exact absurd ((htrj0.symm.trans h).symm) ((hJtmem x.1).mp hj).2.2
                    exact Or.inl ⟨hx1, hQtrans x.1 _ hx1 hj hjc _ hi hic x.2 h2⟩
                  · exact absurd hrk' hrk
                  · exact absurd hra' hra
                  · exact absurd hra' hra
                  · exact absurd hrl hr
    choose P hPp hPchar using hpaths
    have hjsJt : (s ks).1 ∉ Jt := fun h => ((hJtmem _).mp h).2.1 rfl
    have hjnJt : (t (Fin.last m)).1 ∉ Jt := fun h => ((hJtmem _).mp h).1 rfl
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
      (insert j0 (insert (s ks).1 (insert (t (Fin.last m)).1 Jt))) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨hj, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem hj))
      · rw [h1]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [h1]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))
    · rintro ⟨xj, xw⟩ hxJ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert] at hxJ
      rcases hxJ with rfl | rfl | rfl | hxJt
      · obtain ⟨i, hi, hmem⟩ := hQ0cov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · rw [hsuppA'] at hmem
            rcases List.mem_append.mp hmem with hmem2 | hmem2
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0a]; exact List.mem_append_left _ hmem2⟩)⟩
            · rw [List.mem_singleton] at hmem2
              exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0last, hmem2]
                exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0last, hmem2]
                exact List.mem_cons_self ..⟩)⟩
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg0a]; exact List.mem_append_right _ hmem2⟩)⟩
        · have hilast : i ≠ Fin.last m := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
            rw [hg0other i hilast hia]; exact hmem⟩)⟩
      · obtain ⟨iE, hiE⟩ := hq2cov xw
        fin_cases iE
        · exact ⟨ks, (hPchar ks ((s ks).1, xw)).mpr
            (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, hiE⟩⟩)))⟩
        · exact ⟨a, (hPchar a ((s ks).1, xw)).mpr
            (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, hiE⟩⟩)))⟩
      · obtain ⟨iE, hiE⟩ := hq3cov xw
        fin_cases iE
        · exact ⟨a, (hPchar a ((t (Fin.last m)).1, xw)).mpr
            (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, hiE⟩⟩)))⟩
        · exact ⟨Fin.last m, (hPchar (Fin.last m) ((t (Fin.last m)).1, xw)).mpr
            (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, hiE⟩⟩)))⟩
      · obtain ⟨i, hi, hmem⟩ := hQFcov xj hxJt xw
        exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨hxJt, hi, hmem⟩))⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨hj, hi, h2⟩ | ⟨h1, hE1⟩ | ⟨h1, hE1⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨hj', hi', h2'⟩ | ⟨h1', hE1'⟩ |
          ⟨h1', hE1'⟩
      · exact hg0disj r r' hrr' x.2 h2 h2'
      · exact ((hJtmem x.1).mp hj').2.2 h1
      · exact hsks (h1'.symm.trans h1)
      · exact hlastT (h1'.symm.trans h1)
      · exact ((hJtmem x.1).mp hj).2.2 h1'
      · exact hQFdis x.1 hj r hi r' hi' hrr' x.2 ⟨h2, h2'⟩
      · exact hjsJt (h1' ▸ hj)
      · exact hjnJt (h1' ▸ hj)
      · exact hsks (h1.symm.trans h1')
      · exact hjsJt (h1 ▸ hj')
      · rcases hE1 with ⟨hrk, hm0⟩ | ⟨hra, hm1⟩ <;>
          rcases hE1' with ⟨hrk', hm0'⟩ | ⟨hra', hm1'⟩
        · exact hrr' (hrk.trans hrk'.symm)
        · exact hq2dis 0 1 (by decide) x.2 ⟨hm0, hm1'⟩
        · exact hq2dis 0 1 (by decide) x.2 ⟨hm0', hm1⟩
        · exact hrr' (hra.trans hra'.symm)
      · exact hjsjn (h1.symm.trans h1')
      · exact hlastT (h1.symm.trans h1')
      · exact hjnJt (h1 ▸ hj')
      · exact hjsjn (h1'.symm.trans h1)
      · rcases hE1 with ⟨hra, hm0⟩ | ⟨hrl, hm1⟩ <;>
          rcases hE1' with ⟨hra', hm0'⟩ | ⟨hrl', hm1'⟩
        · exact hrr' (hra.trans hra'.symm)
        · exact hq3dis 0 1 (by decide) x.2 ⟨hm0, hm1'⟩
        · exact hq3dis 0 1 (by decide) x.2 ⟨hm0', hm1⟩
        · exact hrr' (hrl.trans hrl'.symm)










private theorem filter_comp_perm_card {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun i => P (σ i))).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2⟩
  · intro i _ i' _ he
    exact σ.injective he
  · intro i hi
    rw [Finset.mem_filter] at hi
    refine ⟨σ.symm i, ?_, σ.apply_symm_apply i⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [σ.apply_symm_apply]
    exact hi.2

/-- Case 5 with at least two targets in the full copy: permute the offending pair last. -/
private theorem prop16_case5_sorted {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hw0 : (weldWSet s t j0).card = m + 1)
    (hT2 : 2 ≤ (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).card)
    (hT0 : ∃ i, (t i).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ m + 1 - 1) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  obtain ⟨i₀, hi₀⟩ := hT0
  apply dpc_perm (Equiv.swap i₀ (Fin.last m))
  have hmono' : MonoDemand col b (fun i => s (Equiv.swap i₀ (Fin.last m) i))
      (fun i => t (Equiv.swap i₀ (Fin.last m) i)) :=
    ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
      hmono.2.2.1.comp (Equiv.swap i₀ (Fin.last m)).injective,
      hmono.2.2.2.comp (Equiv.swap i₀ (Fin.last m)).injective⟩
  refine prop16_case5_core S hmono' (j0 := j0) ?_ ?_ ?_ ?_
  · rw [weldWSet_card_perm]
    exact hw0
  · have h := filter_comp_perm_card (fun i : Fin (m + 1) => (t i).1 = j0)
      (Equiv.swap i₀ (Fin.last m))
    rw [h]
    exact hT2
  · show (t (Equiv.swap i₀ (Fin.last m) (Fin.last m))).1 ≠ j0
    rw [Equiv.swap_apply_right]
    exact hi₀
  · intro j hj
    rw [weldWSet_card_perm]
    exact hw j hj

/-- **Case 5 of Coleman et al. 2025, Proposition 1.6**: one copy meets every pair but
    holds neither all sources nor all targets; every other copy meets at most `n − 1`. -/
theorem prop16_case5 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j0 : Fin ell} (hw0 : (weldWSet s t j0).card = n)
    (hS0 : ∃ i, (s i).1 ≠ j0) (hT0 : ∃ i, (t i).1 ≠ j0)
    (hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ n - 1) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hT2 : 2 ≤ (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0)).card
  · exact prop16_case5_sorted S hmono hw0 hT2 hT0 hw
  · -- swap the roles of sources and targets
    have hsub : weldWSet s t j0 ⊆
        Finset.univ.filter (fun i : Fin (m + 1) => (s i).1 = j0)
        ∪ Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0) := by
      intro i hi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases mem_weldWSet.mp hi with h | h
      · exact Or.inl ⟨Finset.mem_univ _, h⟩
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
    have hS2 : 2 ≤ (Finset.univ.filter (fun i : Fin (m + 1) => (s i).1 = j0)).card := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        (Finset.univ.filter (fun i : Fin (m + 1) => (s i).1 = j0))
        (Finset.univ.filter (fun i : Fin (m + 1) => (t i).1 = j0))
      omega
    apply dpc_swap
    have hw0' : (weldWSet t s j0).card = m + 1 := by
      rw [weldWSet_swap]
      exact hw0
    have hw' : ∀ j, j ≠ j0 → (weldWSet t s j).card ≤ m + 1 - 1 := by
      intro j hj
      rw [weldWSet_swap]
      exact hw j hj
    exact prop16_case5_sorted S hmono.swap hw0' hS2 hS0 hw'

#print axioms prop16_case5


/-! ## Case 6: two copies meet every pair

Every pair has exactly one endpoint in each of the two full copies `j1, j2`. A demand
permutation puts a `j1`-source pair last. The greedy connectors run as in Case 5; the
`j1` inner family excludes the last pair, whose source is the split point. Shape I (the
carrier exits by a `v`-endpoint) reassigns the carrier's connector pair to the last pair
and reroutes the carrier through a Hamilton bridge into its target's freed path-neighbor;
shape II (the carrier exits by a `t`-endpoint) cuts both full copies and stitches the
four freed ends through 2-covers of two fresh copies joined by a fresh matching edge. -/

set_option maxHeartbeats 12800000 in
private theorem prop16_case6_core {ell m : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell (m + 1) Gs M col) {b : Bool}
    {s t : Fin (m + 1) → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hsplit6 : ∀ i, ((s i).1 = j1 ∧ (t i).1 = j2) ∨ ((s i).1 = j2 ∧ (t i).1 = j1))
    (hlastS : (s (Fin.last m)).1 = j1) :
    IsPairedDPC (weldGraph ell Gs M) (m + 1) s t := by
  classical
  have hn := S.hn
  have hEll := S.hEll
  have hlastT : (t (Fin.last m)).1 = j2 := by
    rcases hsplit6 (Fin.last m) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (hlastS.symm.trans h) hj12
  -- the split pairs among the first `m` (all pairs are split)
  obtain ⟨D, hDmem⟩ : ∃ D : Finset (Fin (m + 1)),
      ∀ i, i ∈ D ↔ (i ≠ Fin.last m ∧ (s i).1 ≠ (t i).1) :=
    ⟨Finset.univ.filter (fun i => i ≠ Fin.last m ∧ (s i).1 ≠ (t i).1), fun i => by
      rw [Finset.mem_filter]
      simp⟩
  have hallsplit : ∀ i : Fin (m + 1), (s i).1 ≠ (t i).1 := by
    intro i
    rcases hsplit6 i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hj12
    · rw [h1, h2]
      exact Ne.symm hj12
  have hDmem' : ∀ i, i ∈ D ↔ i ≠ Fin.last m := by
    intro i
    rw [hDmem]
    exact ⟨fun h => h.1, fun h => ⟨h, hallsplit i⟩⟩
  have hsplitD : ∀ i ∈ D, (s i).1 ≠ (t i).1 := fun i hi => ((hDmem i).mp hi).2
  -- the split identities at the two full copies
  have hid1 : (Finset.univ.filter (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)).card
      + (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j1)).card = m + 1 := by
    have h1 : Finset.univ.filter (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)
        = Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j1) := by
      ext k
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
      intro hh
      exact hallsplit k (h.2.trans hh.symm)
    rw [h1]
    have h2 : Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j1)
        = Finset.univ.filter (fun k : Fin (m + 1) => ¬ (s k).1 = j1) := by
      ext k
      rw [Finset.mem_filter, Finset.mem_filter]
      rcases hsplit6 k with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> simp [h1', h2', hj12.symm]
    rw [h2, Finset.filter_not, Finset.card_sdiff]
    have h4 : Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j1) ∩ Finset.univ
        = Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j1) :=
      Finset.inter_univ _
    rw [h4]
    have h3 := Finset.card_filter_le Finset.univ (fun k : Fin (m + 1) => (s k).1 = j1)
    rw [Finset.card_univ, Fintype.card_fin] at h3 ⊢
    omega
  have hid2 : (Finset.univ.filter (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2)).card
      + (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j2)).card = m + 1 := by
    have h1 : Finset.univ.filter (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2)
        = Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j2) := by
      ext k
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
      intro hh
      exact hallsplit k (h.2.trans hh.symm)
    rw [h1]
    have h2 : Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j2)
        = Finset.univ.filter (fun k : Fin (m + 1) => ¬ (s k).1 = j2) := by
      ext k
      rw [Finset.mem_filter, Finset.mem_filter]
      rcases hsplit6 k with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> simp [h1', h2', hj12]
    rw [h2, Finset.filter_not, Finset.card_sdiff]
    have h4 : Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j2) ∩ Finset.univ
        = Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j2) :=
      Finset.inter_univ _
    rw [h4]
    have h3 := Finset.card_filter_le Finset.univ (fun k : Fin (m + 1) => (s k).1 = j2)
    rw [Finset.card_univ, Fintype.card_fin] at h3 ⊢
    omega
  have hw1card : (weldWSet s t j1).card = m + 1 := by
    have huniv : weldWSet s t j1 = Finset.univ := by
      ext i
      simp only [mem_weldWSet, Finset.mem_univ, iff_true]
      rcases hsplit6 i with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hw2card : (weldWSet s t j2).card = m + 1 := by
    have huniv : weldWSet s t j2 = Finset.univ := by
      ext i
      simp only [mem_weldWSet, Finset.mem_univ, iff_true]
      rcases hsplit6 i with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hIA2 : (Finset.univ.filter (fun k => (t k).1 = j2 ∧ ¬ (s k).1 = j2)).card
      + (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j2)).card = m + 1 := by
    have h := weldWSet_card_split_s s t j2
    rw [filter_and_not_eq_sdiff]
    omega
  have hIB2 : (Finset.univ.filter (fun k => (t k).1 = j1 ∧ ¬ (s k).1 = j1)).card
      + (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j1)).card = m + 1 := by
    have h := weldWSet_card_split_s s t j1
    rw [filter_and_not_eq_sdiff]
    omega
  -- Coleman's Case 6 count
  have hcount : ∀ i ∈ D,
      (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
      + (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
      + (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
      < 2 * (m + 1) - 1 := by
    intro i hiD
    obtain ⟨hine, hisplit⟩ := (hDmem i).mp hiD
    have hTceq1 : (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
        = (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = (s i).1)).card := rfl
    rcases hsplit6 i with ⟨hsi, hti⟩ | ⟨hsi, hti⟩
    · -- source in `j1`
      have hlastmem : Fin.last m ∈ Finset.univ.filter
          (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hlastS, ?_⟩
        rw [hlastT]
        exact Ne.symm hj12
      have himem : i ∈ (Finset.univ.filter
          (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)).erase (Fin.last m) := by
        rw [Finset.mem_erase, Finset.mem_filter]
        refine ⟨hine, Finset.mem_univ _, hsi, ?_⟩
        rw [hti]
        exact Ne.symm hj12
      have h2 : (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)).card - 2 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)
            ⊆ ((Finset.univ.filter (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)).erase
                (Fin.last m)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hks, -⟩ := hk
          obtain ⟨hkne, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, hkne, Finset.mem_univ _, hks.trans hsi,
            fun h => hksplit ((hks.trans hsi).trans h.symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem himem, Finset.card_erase_of_mem hlastmem] at hle
      have hi4 : i ∈ Finset.univ.filter
          (fun k => (t k).1 = j2 ∧ ¬ (s k).1 = j2) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hti, ?_⟩
        rw [hsi]
        exact hj12
      have h4 : (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (t k).1 = j2 ∧ ¬ (s k).1 = j2)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)
            ⊆ (Finset.univ.filter (fun k => (t k).1 = j2 ∧ ¬ (s k).1 = j2)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hkt⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, Finset.mem_univ _, hkt.trans hti,
            fun h => hksplit (h.trans (hkt.trans hti).symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem hi4] at hle
      have hS'2 : 2 ≤ (Finset.univ.filter
          (fun k => (s k).1 = j1 ∧ ¬ (t k).1 = j1)).card := by
        rw [Nat.succ_le_iff]
        exact Finset.one_lt_card.mpr ⟨Fin.last m, hlastmem, i,
          Finset.mem_of_mem_erase himem, fun h => hine h.symm⟩
      have hT'1 : 1 ≤ (Finset.univ.filter
          (fun k => (t k).1 = j2 ∧ ¬ (s k).1 = j2)).card :=
        Finset.card_pos.mpr ⟨i, hi4⟩
      have hTA : (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j1)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hsi]
      have hTB : (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j2)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hti]
      omega
    · -- source in `j2`
      have himem : i ∈ Finset.univ.filter
          (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hsi, ?_⟩
        rw [hti]
        exact hj12.symm ∘ Eq.symm
      have h2 : (D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (s k).1 = (s i).1 ∧ (t k).1 ≠ (t i).1)
            ⊆ (Finset.univ.filter (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hks, -⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, Finset.mem_univ _, hks.trans hsi,
            fun h => hksplit ((hks.trans hsi).trans h.symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem himem] at hle
      have hi4 : i ∈ Finset.univ.filter
          (fun k => (t k).1 = j1 ∧ ¬ (s k).1 = j1) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hti, ?_⟩
        rw [hsi]
        exact hj12.symm
      have h4 : (D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)).card
          ≤ (Finset.univ.filter (fun k => (t k).1 = j1 ∧ ¬ (s k).1 = j1)).card - 1 := by
        have hsub : D.filter (fun k => k ≠ i ∧ (t k).1 = (t i).1)
            ⊆ (Finset.univ.filter (fun k => (t k).1 = j1 ∧ ¬ (s k).1 = j1)).erase i := by
          intro k hk
          rw [Finset.mem_filter] at hk
          obtain ⟨hkD, hki, hkt⟩ := hk
          obtain ⟨-, hksplit⟩ := (hDmem k).mp hkD
          rw [Finset.mem_erase, Finset.mem_filter]
          exact ⟨hki, Finset.mem_univ _, hkt.trans hti,
            fun h => hksplit (h.trans (hkt.trans hti).symm)⟩
        have hle := Finset.card_le_card hsub
        rwa [Finset.card_erase_of_mem hi4] at hle
      have hS'2 : 1 ≤ (Finset.univ.filter
          (fun k => (s k).1 = j2 ∧ ¬ (t k).1 = j2)).card :=
        Finset.card_pos.mpr ⟨i, himem⟩
      have hT'1 : 1 ≤ (Finset.univ.filter
          (fun k => (t k).1 = j1 ∧ ¬ (s k).1 = j1)).card :=
        Finset.card_pos.mpr ⟨i, hi4⟩
      have hTA : (Finset.univ.filter (fun k => (t k).1 = (s i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (t k).1 = j2)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hsi]
      have hTB : (Finset.univ.filter (fun k => (s k).1 = (t i).1)).card
          = (Finset.univ.filter (fun k : Fin (m + 1) => (s k).1 = j1)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        rw [hti]
      omega
  -- the greedy connectors
  obtain ⟨v, u, hvcol, hucol, hpart, hvT, huS, hvv, huu⟩ := weld_greedy S b s t D hsplitD hcount
  -- the `j1` inner family over the first `m` pairs
  have hA0ne : (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hA0card : (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))).card ≤ m + 1 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hDofA0 : ∀ i ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))), i ∈ D :=
    fun i hi => (hDmem' i).mpr (Finset.ne_of_mem_erase hi)
  have htouch1 : ∀ i : Fin (m + 1), (s i).1 = j1 ∨ (t i).1 = j1 := by
    intro i
    rcases hsplit6 i with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hfam0 : ∃ Q0 : ∀ i ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))),
      (Gs j1).Walk (wInnerS s u j1 i) (wInnerT t v j1 i),
      (∀ i (hi : i ∈ _), (Q0 i hi).IsPath) ∧
      (∀ x : W, ∃ i, ∃ hi : i ∈ _, x ∈ (Q0 i hi).support) ∧
      (∀ i (hi : i ∈ _), ∀ k (hk : k ∈ _), i ≠ k →
        ∀ x, ¬ (x ∈ (Q0 i hi).support ∧ x ∈ (Q0 k hk).support)) := by
    apply S.inner_family (b := b) j1 _ hA0ne hA0card
    · intro i hi
      by_cases hsij : (s i).1 = j1
      · rw [wInnerS_src hsij, ← hsij]
        exact hmono.1 i
      · have htij : (t i).1 = j1 := (htouch1 i).resolve_left hsij
        rw [wInnerS_conn hsij, ← htij]
        exact hucol i (hDofA0 i hi)
    · intro i hi
      by_cases htij : (t i).1 = j1
      · rw [wInnerT_tgt htij, ← htij]
        exact hmono.2.1 i
      · have hsij : (s i).1 = j1 := (htouch1 i).resolve_right htij
        rw [wInnerT_conn htij, ← hsij]
        exact hvcol i (hDofA0 i hi)
    · intro i hi k hk hik
      by_cases hsij : (s i).1 = j1 <;> by_cases hskj : (s k).1 = j1
      · rw [wInnerS_src hsij, wInnerS_src hskj]
        intro he
        exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
      · have htkj : (t k).1 = j1 := (htouch1 k).resolve_left hskj
        rw [wInnerS_src hsij, wInnerS_conn hskj]
        exact fun he => huS k (hDofA0 k hk) i (hsij.trans htkj.symm) he.symm
      · have htij : (t i).1 = j1 := (htouch1 i).resolve_left hsij
        rw [wInnerS_conn hsij, wInnerS_src hskj]
        exact huS i (hDofA0 i hi) k (hskj.trans htij.symm)
      · have htij : (t i).1 = j1 := (htouch1 i).resolve_left hsij
        have htkj : (t k).1 = j1 := (htouch1 k).resolve_left hskj
        rw [wInnerS_conn hsij, wInnerS_conn hskj]
        exact huu k (hDofA0 k hk) i (hDofA0 i hi) hik (htij.trans htkj.symm)
    · intro i hi k hk hik
      by_cases htij : (t i).1 = j1 <;> by_cases htkj : (t k).1 = j1
      · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
        intro he
        exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
      · have hskj : (s k).1 = j1 := (htouch1 k).resolve_right htkj
        rw [wInnerT_tgt htij, wInnerT_conn htkj]
        exact fun he => hvT k (hDofA0 k hk) i (htij.trans hskj.symm) he.symm
      · have hsij : (s i).1 = j1 := (htouch1 i).resolve_right htij
        rw [wInnerT_conn htij, wInnerT_tgt htkj]
        exact hvT i (hDofA0 i hi) k (htkj.trans hsij.symm)
      · have hsij : (s i).1 = j1 := (htouch1 i).resolve_right htij
        have hskj : (s k).1 = j1 := (htouch1 k).resolve_right htkj
        rw [wInnerT_conn htij, wInnerT_conn htkj]
        exact hvv k (hDofA0 k hk) i (hDofA0 i hi) hik (hsij.trans hskj.symm)
  obtain ⟨Q0, hQ0path, hQ0cov, hQ0disj⟩ := hfam0
  -- locate the carrier of the last source and split it there
  obtain ⟨a, ha0, ha⟩ := hQ0cov (s (Fin.last m)).2
  have halast : a ≠ Fin.last m := Finset.ne_of_mem_erase ha0
  have haD : a ∈ D := (hDmem' a).mpr halast
  have hpairlast : s (Fin.last m) = (j1, (s (Fin.last m)).2) := Prod.ext hlastS rfl
  have hsnS : (s (Fin.last m)).2 ≠ wInnerS s u j1 a := by
    by_cases hsij : (s a).1 = j1
    · rw [wInnerS_src hsij]
      intro h
      have h2 := hmono.2.2.1 (Prod.ext (hlastS.trans hsij.symm) h)
      exact halast h2.symm
    · have htij : (t a).1 = j1 := (htouch1 a).resolve_left hsij
      rw [wInnerS_conn hsij]
      intro h
      exact huS a haD (Fin.last m) (hlastS.trans htij.symm) h.symm
  have hsnT : (s (Fin.last m)).2 ≠ wInnerT t v j1 a := by
    by_cases htij : (t a).1 = j1
    · rw [wInnerT_tgt htij]
      intro h
      have h1 := hmono.1 (Fin.last m)
      rw [hpairlast] at h1
      have h2 := hmono.2.1 a
      rw [show t a = (j1, (t a).2) from Prod.ext htij rfl] at h2
      rw [h] at h1
      rw [h1] at h2
      cases b <;> simp at h2
    · rw [wInnerT_conn htij]
      intro h
      have h1 := hmono.1 (Fin.last m)
      rw [hpairlast] at h1
      have hsij : (s a).1 = j1 := (htouch1 a).resolve_right htij
      have h2 := hvcol a haD
      rw [hsij] at h2
      rw [h] at h1
      rw [h1] at h2
      cases b <;> simp at h2
  obtain ⟨y, z, Apre, B, hApre, hB, hadj_y_sn, hadj_sn_z, hsuppA⟩ :=
    path_split_interior (Q0 a ha0) (hQ0path a ha0) ha hsnS hsnT
  have hndA := (hQ0path a ha0).support_nodup
  rw [hsuppA] at hndA
  obtain ⟨hndA1, hndA2, hdisjA⟩ := List.nodup_append.mp hndA
  have hsn_notB : (s (Fin.last m)).2 ∉ B.support := (List.nodup_cons.mp hndA2).1
  have hcoly : col (j1, y) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j1, y) (j1, (s (Fin.last m)).2) :=
      (weldLift Gs M j1).map_adj hadj_y_sn
    have h := S.hproper _ _ hadj
    have h2 := hmono.1 (Fin.last m)
    rw [hpairlast] at h2
    rw [h2] at h
    exact bool_eq_not_of_ne h
  have hcolz : col (j1, z) = !b := by
    have hadj : (weldGraph ell Gs M).Adj (j1, (s (Fin.last m)).2) (j1, z) :=
      (weldLift Gs M j1).map_adj hadj_sn_z
    have h := S.hproper _ _ hadj
    have h2 := hmono.1 (Fin.last m)
    rw [hpairlast] at h2
    rw [h2] at h
    exact bool_eq_not_of_ne (Ne.symm h)
  -- two fresh bridge copies
  obtain ⟨j3, j4, hj31, hj32, hj41, hj42, hj34⟩ := fin_exists_two_avoid (by omega) j1 j2
  by_cases hshape : (s a).1 = j1
  · -- SHAPE I: the carrier's `j1` segment is source-type; the last pair inherits its
    -- connector pair, and the carrier reroutes through `j3` into its target's freed
    -- path-neighbor
    have htaj2 : (t a).1 = j2 := by
      rcases hsplit6 a with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (hshape.symm.trans h) hj12
    -- the carrier's `j1` pieces have concrete endpoints
    have hBva : ∃ q : (Gs j1).Walk z (v a), q.IsPath ∧ q.support = B.support :=
      ⟨B.copy rfl (wInnerT_conn (fun h => hj12 (h.symm.trans htaj2))), by
        rw [SimpleGraph.Walk.isPath_copy]; exact hB, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨Bva, hBvap, hBvas⟩ := hBva
    have hApre' : ∃ q : (Gs j1).Walk (s a).2 y, q.IsPath ∧ q.support = Apre.support :=
      ⟨Apre.copy (wInnerS_src hshape) rfl, by
        rw [SimpleGraph.Walk.isPath_copy]; exact hApre, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨Aprec, hAprecp, hAprecs⟩ := hApre'
    -- the extended connectors: the last pair inherits the carrier's
    obtain ⟨u'', hu''⟩ : ∃ u'' : Fin (m + 1) → W,
        (∀ i, i ≠ Fin.last m → u'' i = u i) ∧ u'' (Fin.last m) = u a := by
      refine ⟨Function.update u (Fin.last m) (u a), ?_, Function.update_self ..⟩
      intro i hi
      exact Function.update_of_ne hi ..
    -- the `j2` inner family over all pairs but the carrier
    have htouch2 : ∀ i : Fin (m + 1), (s i).1 = j2 ∨ (t i).1 = j2 := by
      intro i
      rcases hsplit6 i with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
    have hA2ne : (Finset.univ.erase a : Finset (Fin (m + 1))).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hA2card : (Finset.univ.erase a : Finset (Fin (m + 1))).card ≤ m + 1 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hDof : ∀ i : Fin (m + 1), i ≠ Fin.last m → i ∈ D := fun i hi => (hDmem' i).mpr hi
    have hfam2 : ∃ Q2 : ∀ i ∈ (Finset.univ.erase a : Finset (Fin (m + 1))),
        (Gs j2).Walk (wInnerS s u'' j2 i) (wInnerT t v j2 i),
        (∀ i (hi : i ∈ _), (Q2 i hi).IsPath) ∧
        (∀ x : W, ∃ i, ∃ hi : i ∈ _, x ∈ (Q2 i hi).support) ∧
        (∀ i (hi : i ∈ _), ∀ k (hk : k ∈ _), i ≠ k →
          ∀ x, ¬ (x ∈ (Q2 i hi).support ∧ x ∈ (Q2 k hk).support)) := by
      apply S.inner_family (b := b) j2 _ hA2ne hA2card
      · intro i _
        by_cases hsij : (s i).1 = j2
        · rw [wInnerS_src hsij, ← hsij]
          exact hmono.1 i
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          rw [wInnerS_conn hsij]
          by_cases hilast : i = Fin.last m
          · subst hilast
            rw [hu''.2, ← htaj2]
            exact hucol a haD
          · rw [hu''.1 i hilast, ← htij]
            exact hucol i (hDof i hilast)
      · intro i _
        by_cases htij : (t i).1 = j2
        · rw [wInnerT_tgt htij, ← htij]
          exact hmono.2.1 i
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          have hilast : i ≠ Fin.last m := by
            intro h
            rw [h] at hsij
            exact hj12 (hlastS.symm.trans hsij)
          rw [wInnerT_conn htij, ← hsij]
          exact hvcol i (hDof i hilast)
      · intro i hi k hk hik
        by_cases hsij : (s i).1 = j2 <;> by_cases hskj : (s k).1 = j2
        · rw [wInnerS_src hsij, wInnerS_src hskj]
          intro he
          exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
        · have htkj : (t k).1 = j2 := (htouch2 k).resolve_left hskj
          rw [wInnerS_src hsij, wInnerS_conn hskj]
          by_cases hklast : k = Fin.last m
          · subst hklast
            rw [hu''.2]
            exact fun he => huS a haD i (hsij.trans htaj2.symm) he.symm
          · rw [hu''.1 k hklast]
            exact fun he => huS k (hDof k hklast) i (hsij.trans htkj.symm) he.symm
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          rw [wInnerS_conn hsij, wInnerS_src hskj]
          by_cases hilast : i = Fin.last m
          · subst hilast
            rw [hu''.2]
            exact huS a haD k (hskj.trans htaj2.symm)
          · rw [hu''.1 i hilast]
            exact huS i (hDof i hilast) k (hskj.trans htij.symm)
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          have htkj : (t k).1 = j2 := (htouch2 k).resolve_left hskj
          rw [wInnerS_conn hsij, wInnerS_conn hskj]
          by_cases hilast : i = Fin.last m <;> by_cases hklast : k = Fin.last m
          · exact absurd (hilast.trans hklast.symm) hik
          · subst hilast
            rw [hu''.2, hu''.1 k hklast]
            have hka : k ≠ a := Finset.ne_of_mem_erase hk
            exact fun he => huu k (hDof k hklast) a haD (Ne.symm hka)
              (htaj2.trans htkj.symm) he
          · subst hklast
            rw [hu''.1 i hilast, hu''.2]
            have hia : i ≠ a := Finset.ne_of_mem_erase hi
            exact fun he => huu i (hDof i hilast) a haD (Ne.symm hia)
              (htaj2.trans htij.symm) he.symm
          · rw [hu''.1 i hilast, hu''.1 k hklast]
            exact huu k (hDof k hklast) i (hDof i hilast) hik (htij.trans htkj.symm)
      · intro i hi k hk hik
        by_cases htij : (t i).1 = j2 <;> by_cases htkj : (t k).1 = j2
        · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
          intro he
          exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
        · have hskj : (s k).1 = j2 := (htouch2 k).resolve_right htkj
          have hklast : k ≠ Fin.last m := by
            intro h
            rw [h] at hskj
            exact hj12 (hlastS.symm.trans hskj)
          rw [wInnerT_tgt htij, wInnerT_conn htkj]
          exact fun he => hvT k (hDof k hklast) i (htij.trans hskj.symm) he.symm
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          have hilast : i ≠ Fin.last m := by
            intro h
            rw [h] at hsij
            exact hj12 (hlastS.symm.trans hsij)
          rw [wInnerT_conn htij, wInnerT_tgt htkj]
          exact hvT i (hDof i hilast) k (htkj.trans hsij.symm)
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          have hskj : (s k).1 = j2 := (htouch2 k).resolve_right htkj
          have hilast : i ≠ Fin.last m := by
            intro h
            rw [h] at hsij
            exact hj12 (hlastS.symm.trans hsij)
          have hklast : k ≠ Fin.last m := by
            intro h
            rw [h] at hskj
            exact hj12 (hlastS.symm.trans hskj)
          rw [wInnerT_conn htij, wInnerT_conn htkj]
          exact hvv k (hDof k hklast) i (hDof i hilast) hik (hsij.trans hskj.symm)
    obtain ⟨Q2, hQ2p, hQ2cov, hQ2dis⟩ := hfam2
    -- locate the carrier's target inside the `j2` family and split there
    obtain ⟨ι, hι0, hιmem⟩ := hQ2cov (t a).2
    have hιa : ι ≠ a := Finset.ne_of_mem_erase hι0
    have hta_ne_S : (t a).2 ≠ wInnerS s u'' j2 ι := by
      intro h
      have h1 := hmono.2.1 a
      rw [show t a = (j2, (t a).2) from Prod.ext htaj2 rfl] at h1
      by_cases hsij : (s ι).1 = j2
      · rw [wInnerS_src hsij] at h
        have h2 := hmono.1 ι
        rw [show s ι = (j2, (s ι).2) from Prod.ext hsij rfl] at h2
        rw [← h] at h2
        rw [h1] at h2
        cases b <;> simp at h2
      · have htij : (t ι).1 = j2 := (htouch2 ι).resolve_left hsij
        rw [wInnerS_conn hsij] at h
        by_cases hιlast : ι = Fin.last m
        · subst hιlast
          rw [hu''.2] at h
          have h2 := hucol a haD
          rw [htaj2] at h2
          rw [← h] at h2
          rw [h1] at h2
          cases b <;> simp at h2
        · rw [hu''.1 ι hιlast] at h
          have h2 := hucol ι (hDof ι hιlast)
          rw [htij] at h2
          rw [← h] at h2
          rw [h1] at h2
          cases b <;> simp at h2
    have hta_ne_T : (t a).2 ≠ wInnerT t v j2 ι := by
      by_cases htij : (t ι).1 = j2
      · rw [wInnerT_tgt htij]
        intro h
        exact hιa (hmono.2.2.2 (Prod.ext (htij.trans htaj2.symm) h.symm))
      · have hsij : (s ι).1 = j2 := (htouch2 ι).resolve_right htij
        have hιlast : ι ≠ Fin.last m := by
          intro h
          rw [h] at hsij
          exact hj12 (hlastS.symm.trans hsij)
        rw [wInnerT_conn htij]
        intro h
        exact hvT ι (hDof ι hιlast) a (htaj2.trans hsij.symm) h.symm
    obtain ⟨x₂, u1s, C, D₂, hC, hD₂, hadj_x2_ta, hadj_ta_u1s, hsuppC⟩ :=
      path_split_interior (Q2 ι hι0) (hQ2p ι hι0) hιmem hta_ne_S hta_ne_T
    have hndC := (hQ2p ι hι0).support_nodup
    rw [hsuppC] at hndC
    obtain ⟨hndC1, hndC2, hdisjC⟩ := List.nodup_append.mp hndC
    have hta_notD₂ : (t a).2 ∉ D₂.support := (List.nodup_cons.mp hndC2).1
    have hcolu1s : col (j2, u1s) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, (t a).2) (j2, u1s) :=
        (weldLift Gs M j2).map_adj hadj_ta_u1s
      have h := S.hproper _ _ hadj
      have h2 := hmono.2.1 a
      rw [show t a = (j2, (t a).2) from Prod.ext htaj2 rfl] at h2
      rw [h2] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hu1s_ne : u1s ≠ wInnerT t v j2 ι := by
      by_cases htij : (t ι).1 = j2
      · rw [wInnerT_tgt htij]
        intro h
        have h2 := hmono.2.1 ι
        rw [show t ι = (j2, (t ι).2) from Prod.ext htij rfl] at h2
        rw [← h] at h2
        rw [hcolu1s] at h2
        cases b <;> simp at h2
      · have hsij : (s ι).1 = j2 := (htouch2 ι).resolve_right htij
        have hιlast : ι ≠ Fin.last m := by
          intro h
          rw [h] at hsij
          exact hj12 (hlastS.symm.trans hsij)
        rw [wInnerT_conn htij]
        intro h
        have h2 := hvcol ι (hDof ι hιlast)
        rw [hsij] at h2
        rw [← h] at h2
        rw [hcolu1s] at h2
        cases b <;> simp at h2
    obtain ⟨y₂, D₂', hD₂', hadj_u1s_y2, hsuppD₂, hu1s_notD₂'⟩ := path_peel_head D₂ hD₂ hu1s_ne
    have hcoly2 : col (j2, y₂) = !b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, u1s) (j2, y₂) :=
        (weldLift Gs M j2).map_adj hadj_u1s_y2
      have h := S.hproper _ _ hadj
      rw [hcolu1s] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    have hcolx2 : col (j2, x₂) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, x₂) (j2, (t a).2) :=
        (weldLift Gs M j2).map_adj hadj_x2_ta
      have h := S.hproper _ _ hadj
      have h2 := hmono.2.1 a
      rw [show t a = (j2, (t a).2) from Prod.ext htaj2 rfl] at h2
      rw [h2] at h
      exact bool_eq_of_ne_not h
    -- the two Hamilton bridges
    have hbr3 : col (j3, M j1 j3 y) ≠ col (j3, M j2 j3 u1s) := by
      have h1 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) y)
      have h2 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj32) u1s)
      rw [hcoly] at h1
      rw [hcolu1s] at h2
      rw [bool_eq_of_ne_not (Ne.symm h1), bool_eq_not_of_ne (Ne.symm h2)]
      cases b <;> simp
    obtain ⟨h3, hham3⟩ := S.copy_lace j3 _ _ hbr3
    have hbr4 : col (j4, M j2 j4 x₂) ≠ col (j4, M j2 j4 y₂) := by
      have h1 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) x₂)
      have h2 := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) y₂)
      rw [hcolx2] at h1
      rw [hcoly2] at h2
      rw [bool_eq_not_of_ne (Ne.symm h1), bool_eq_of_ne_not (Ne.symm h2)]
      cases b <;> simp
    obtain ⟨h4, hham4⟩ := S.copy_lace j4 _ _ hbr4
    -- the per-copy segment lists
    set g1 : Fin (m + 1) → List W := fun r =>
      if hr : r = Fin.last m then ((s (Fin.last m)).2 :: B.support)
      else if r = a then Apre.support
      else (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support with hg1
    have hg1last : g1 (Fin.last m) = ((s (Fin.last m)).2 :: B.support) := by
      rw [hg1]
      exact dif_pos rfl
    have hg1a : g1 a = Apre.support := by
      simp [hg1, halast]
    have hg1other : ∀ r, ∀ hr : r ≠ Fin.last m, r ≠ a →
        g1 r = (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
      intro r hr hra
      simp only [hg1]
      rw [dif_neg hr, if_neg hra]
    set g2 : Fin (m + 1) → List W := fun r =>
      if hra : r = a then [u1s, (t a).2]
      else if r = ι then C.support ++ D₂'.support
      else (Q2 r (Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩)).support with hg2
    have hg2a : g2 a = [u1s, (t a).2] := by
      rw [hg2]
      exact dif_pos rfl
    have hg2ι : g2 ι = C.support ++ D₂'.support := by
      simp [hg2, hιa]
    have hg2other : ∀ r, ∀ hra : r ≠ a, r ≠ ι →
        g2 r = (Q2 r (Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩)).support := by
      intro r hra hrι
      simp only [hg2]
      rw [dif_neg hra, if_neg hrι]
    -- coverage decompositions of the two surgical paths
    have hsub_g1a : ∀ x2 : W, x2 ∈ g1 a → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg1a] at h
      rw [hsuppA]
      exact List.mem_append_left _ h
    have hsub_g1last : ∀ x2 : W, x2 ∈ g1 (Fin.last m) → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg1last] at h
      rw [hsuppA]
      exact List.mem_append_right _ h
    have hg1_lastva : ∀ x2 : W, x2 ∈ g1 (Fin.last m) → x2 ∈ g1 a → False := by
      intro x2 h h'
      rw [hg1last] at h
      rw [hg1a] at h'
      exact hdisjA x2 h' x2 h rfl
    have hg1disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g1 r → x2 ∉ g1 r' := by
      intro r r' hrr' x2 h h'
      by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
      · exact hrr' (hr.trans hr'.symm)
      · rw [hr] at h
        by_cases hra : r' = a
        · rw [hra] at h'
          exact hg1_lastva x2 h h'
        · rw [hg1other r' hr' hra] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra x2 ⟨h', hsub_g1last x2 h⟩
      · rw [hr'] at h'
        by_cases hra : r = a
        · rw [hra] at h
          exact hg1_lastva x2 h' h
        · rw [hg1other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_g1last x2 h'⟩
      · by_cases hra : r = a <;> by_cases hra' : r' = a
        · exact hrr' (hra.trans hra'.symm)
        · rw [hra] at h
          rw [hg1other r' hr' hra'] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra' x2 ⟨h', hsub_g1a x2 h⟩
        · rw [hra'] at h'
          rw [hg1other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_g1a x2 h'⟩
        · rw [hg1other r hr hra] at h
          rw [hg1other r' hr' hra'] at h'
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    have hsub_g2a : ∀ x2 : W, x2 ∈ g2 a → x2 ∈ (Q2 ι hι0).support := by
      intro x2 h
      rw [hg2a] at h
      rw [hsuppC]
      have hmem2 : x2 ∈ ((t a).2 :: D₂.support) := by
        rw [hsuppD₂]
        rcases List.mem_cons.mp h with h | h
        · rw [h]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rw [List.mem_singleton] at h
          rw [h]
          exact List.mem_cons_self ..
      exact List.mem_append_right _ hmem2
    have hsub_g2ι : ∀ x2 : W, x2 ∈ g2 ι → x2 ∈ (Q2 ι hι0).support := by
      intro x2 h
      rw [hg2ι] at h
      rw [hsuppC]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (by
          rw [hsuppD₂]
          exact List.mem_cons_of_mem _ h))
    have hg2_aι : ∀ x2 : W, x2 ∈ g2 a → x2 ∈ g2 ι → False := by
      intro x2 h h'
      rw [hg2a] at h
      rw [hg2ι] at h'
      rcases List.mem_cons.mp h with h | h
      · rcases List.mem_append.mp h' with h'' | h''
        · refine hdisjC x2 h'' x2 ?_ rfl
          rw [h, hsuppD₂]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · exact hu1s_notD₂' (h ▸ h'')
      · rw [List.mem_singleton] at h
        rcases List.mem_append.mp h' with h'' | h''
        · exact hdisjC x2 h'' x2 (h ▸ List.mem_cons_self ..) rfl
        · exact hta_notD₂ (h ▸ (by rw [hsuppD₂]; exact List.mem_cons_of_mem _ h''))
    have hg2disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g2 r → x2 ∉ g2 r' := by
      intro r r' hrr' x2 h h'
      by_cases hra : r = a <;> by_cases hra' : r' = a
      · exact hrr' (hra.trans hra'.symm)
      · rw [hra] at h
        by_cases hrι : r' = ι
        · rw [hrι] at h'
          exact hg2_aι x2 h h'
        · rw [hg2other r' hra' hrι] at h'
          exact hQ2dis r' (Finset.mem_erase.mpr ⟨hra', Finset.mem_univ r'⟩) ι hι0
            hrι x2 ⟨h', hsub_g2a x2 h⟩
      · rw [hra'] at h'
        by_cases hrι : r = ι
        · rw [hrι] at h
          exact hg2_aι x2 h' h
        · rw [hg2other r hra hrι] at h
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩) ι hι0
            hrι x2 ⟨h, hsub_g2a x2 h'⟩
      · by_cases hrι : r = ι <;> by_cases hrι' : r' = ι
        · exact hrr' (hrι.trans hrι'.symm)
        · rw [hrι] at h
          rw [hg2other r' hra' hrι'] at h'
          exact hQ2dis r' (Finset.mem_erase.mpr ⟨hra', Finset.mem_univ r'⟩) ι hι0
            hrι' x2 ⟨h', hsub_g2ι x2 h⟩
        · rw [hrι'] at h'
          rw [hg2other r hra hrι] at h
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩) ι hι0
            hrι x2 ⟨h, hsub_g2ι x2 h'⟩
        · rw [hg2other r hra hrι] at h
          rw [hg2other r' hra' hrι'] at h'
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hra', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j1 ∧ x.2 ∈ g1 r) ∨ (x.1 = j2 ∧ x.2 ∈ g2 r) ∨
            (r = a ∧ x.1 = j3 ∧ x.2 ∈ h3.support) ∨
            (r = ι ∧ x.1 = j4 ∧ x.2 ∈ h4.support)) := by
      intro r
      by_cases hra : r = a
      · -- the carrier: its `j1` prefix, the `j3` bridge, and its target's freed neighbor
        subst hra
        have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j1, y), R.IsPath ∧
            R.support = Apre.support.map (fun w' => (j1, w')) := by
          refine ⟨(Aprec.map (weldLift Gs M j1)).copy (Prod.ext hshape.symm rfl) rfl, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hAprecp
          · rw [SimpleGraph.Walk.support_copy, weldLift_support, hAprecs]
        obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
        obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ h3 hR₀p hham3.isPath
          (weld_cross_adj (Ne.symm hj31) y)
          (by
            intro w' _ hmem
            rw [hR₀s, mem_map_pair] at hmem
            exact hj31 hmem.1)
        have hW2p : (SimpleGraph.Walk.cons hadj_ta_u1s.symm SimpleGraph.Walk.nil :
            (Gs j2).Walk u1s (t r).2).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcolu1s
          rw [h] at h1
          have h2 := hmono.2.1 r
          rw [show t r = (j2, (t r).2) from Prod.ext htaj2 rfl] at h2
          rw [h2] at h1
          cases b <;> simp at h1
        obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁
          (SimpleGraph.Walk.cons hadj_ta_u1s.symm SimpleGraph.Walk.nil) hR₁p hW2p
          ((weld_cross_adj (Ne.symm hj32) u1s).symm)
          (by
            intro w' _ hmem
            rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
            rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hj12 h1.symm
            · exact hj32 h1.symm)
        refine ⟨R₂.copy rfl (Prod.ext htaj2.symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₂p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₂s, List.mem_append, hR₁s, List.mem_append,
            hR₀s, mem_map_pair, mem_map_pair, mem_map_pair]
          constructor
          · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · exact Or.inl ⟨h1, by rw [hg1a]; exact h2⟩
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2⟩))
            · refine Or.inr (Or.inl ⟨h1, ?_⟩)
              rw [hg2a]
              simpa using h2
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨hrι, -, -⟩)
            · exact Or.inl (Or.inl ⟨h1, by rw [hg1a] at h2; exact h2⟩)
            · refine Or.inr ⟨h1, ?_⟩
              rw [hg2a] at h2
              simpa using h2
            · exact Or.inl (Or.inr ⟨h1, h2⟩)
            · exact absurd hrι.symm hιa
      · by_cases hr : r = Fin.last m
        · -- the last pair: `sn ⇝ v a`, the inherited connector edge, then its family path
          subst hr
          have hsnBp : (SimpleGraph.Walk.cons hadj_sn_z Bva).IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]
            refine ⟨hBvap, ?_⟩
            rw [hBvas]
            exact hsn_notB
          have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j1, v a), R.IsPath ∧
              R.support = ((s (Fin.last m)).2 :: B.support).map (fun w' => (j1, w')) := by
            refine ⟨((SimpleGraph.Walk.cons hadj_sn_z Bva).map (weldLift Gs M j1)).copy
              (Prod.ext hlastS.symm rfl) rfl, ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hsnBp
            · rw [SimpleGraph.Walk.support_copy, weldLift_support,
                SimpleGraph.Walk.support_cons, hBvas]
          obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
          have hadjva : (weldGraph ell Gs M).Adj (j1, v a) (j2, u a) := by
            have h := weld_cross_adj (Gs := Gs) (M := M) hj12 (v a)
            rwa [show M j1 j2 (v a) = u a from by rw [hpart a haD, hshape, htaj2]] at h
          by_cases hlι : Fin.last m = ι
          · -- the inherited family path is itself the rerouted carrier of `t a`
            have hCc : ∃ q : (Gs j2).Walk (u a) x₂, q.IsPath ∧ q.support = C.support := by
              refine ⟨C.copy ?_ rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
              · rw [← hlι, wInnerS_conn (fun h => hj12 (hlastS.symm.trans h)), hu''.2]
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hC
            obtain ⟨Cc, hCcp, hCcs⟩ := hCc
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Cc hR₀p hCcp hadjva
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hj12 hmem.1.symm)
            rw [hCcs] at hR₁s
            obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ h4 hR₁p hham4.isPath
              (weld_cross_adj (Ne.symm hj42) x₂)
              (by
                intro w' _ hmem
                rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                · exact hj41 h1
                · exact hj42 h1)
            have hD₂c : ∃ q : (Gs j2).Walk y₂ (t (Fin.last m)).2, q.IsPath ∧
                q.support = D₂'.support := by
              refine ⟨D₂'.copy rfl ?_, ?_, SimpleGraph.Walk.support_copy ..⟩
              · rw [← hlι, wInnerT_tgt hlastT]
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hD₂'
            obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
            obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ D₂c hR₂p hD₂cp
              ((weld_cross_adj (Ne.symm hj42) y₂).symm)
              (by
                intro w' hw' hmem
                rw [hD₂cs] at hw'
                rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
                · exact hj12 h1.symm
                · refine hdisjC w' h2 w' ?_ rfl
                  rw [hsuppD₂]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                · exact hj42 h1.symm)
            refine ⟨R₃.copy rfl (Prod.ext hlastT.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hR₃p
            · intro x
              rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                mem_map_pair, mem_map_pair, hD₂cs]
              constructor
              · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, by rw [hg1last]; exact h2⟩
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hlι, hg2ι]
                    exact List.mem_append_left _ h2⟩)
                · exact Or.inr (Or.inr (Or.inr ⟨hlι, h1, h2⟩))
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hlι, hg2ι]
                    exact List.mem_append_right _ h2⟩)
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨-, h1, h2⟩)
                · exact Or.inl (Or.inl (Or.inl ⟨h1, by rw [hg1last] at h2; exact h2⟩))
                · rw [hlι, hg2ι] at h2
                  rcases List.mem_append.mp h2 with h2 | h2
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                  · exact Or.inr ⟨h1, h2⟩
                · exact absurd hra'.symm halast
                · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · -- the inherited family path is untouched
            have hseg : ∃ q : (Gs j2).Walk (u a) (t (Fin.last m)).2, q.IsPath ∧
                q.support = (Q2 (Fin.last m) (Finset.mem_erase.mpr
                  ⟨fun h => halast h.symm, Finset.mem_univ _⟩)).support := by
              refine ⟨(Q2 _ _).copy ?_ (wInnerT_tgt hlastT), ?_,
                SimpleGraph.Walk.support_copy ..⟩
              · rw [wInnerS_conn (fun h => hj12 (hlastS.symm.trans h)), hu''.2]
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hQ2p _ _
            obtain ⟨seg, hsegp, hsegs⟩ := hseg
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ seg hR₀p hsegp hadjva
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hj12 hmem.1.symm)
            refine ⟨R₁.copy rfl (Prod.ext hlastT.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hR₁p
            · intro x
              rw [SimpleGraph.Walk.support_copy, hR₁s, List.mem_append, hR₀s, mem_map_pair,
                mem_map_pair, hsegs]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                · exact Or.inl ⟨h1, by rw [hg1last]; exact h2⟩
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hg2other (Fin.last m) (fun h => halast h.symm) (fun h => hlι h)]
                    exact h2⟩)
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨hrι, -, -⟩)
                · exact Or.inl ⟨h1, by rw [hg1last] at h2; exact h2⟩
                · exact Or.inr ⟨h1, by
                    rw [hg2other (Fin.last m) (fun h => halast h.symm) (fun h => hlι h)] at h2
                    exact h2⟩
                · exact absurd hra'.symm halast
                · exact absurd hrι hlι
        · have hrmem1 : r ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))) :=
            Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
          have hrmem2 : r ∈ (Finset.univ.erase a : Finset (Fin (m + 1))) :=
            Finset.mem_erase.mpr ⟨hra, Finset.mem_univ r⟩
          have hu''r : u'' r = u r := hu''.1 r hr
          by_cases hrι : r = ι
          · -- the pair whose `j2` segment is rerouted around the carrier's target
            subst hrι
            by_cases hsrj : (s r).1 = j1
            · have htrj : (t r).1 = j2 := by
                rcases hsplit6 r with ⟨-, h⟩ | ⟨h, -⟩
                · exact h
                · exact absurd (hsrj.symm.trans h) hj12
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j1, v r), R.IsPath ∧
                  R.support = (Q0 r hrmem1).support.map (fun w' => (j1, w')) := by
                refine ⟨(((Q0 r hrmem1).copy (wInnerS_src hsrj)
                  (wInnerT_conn (fun h => hj12 (h.symm.trans htrj)))).map
                  (weldLift Gs M j1)).copy (Prod.ext hsrj.symm rfl) rfl, ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  refine SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) ?_
                  rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem1
                · rw [SimpleGraph.Walk.support_copy, weldLift_support,
                    SimpleGraph.Walk.support_copy]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              have hadjvu : (weldGraph ell Gs M).Adj (j1, v r) (j2, u r) := by
                have h := weld_cross_adj (Gs := Gs) (M := M) hj12 (v r)
                rwa [show M j1 j2 (v r) = u r from by
                  rw [hpart r ((hDmem' r).mpr hr), hsrj, htrj]] at h
              have hCc : ∃ q : (Gs j2).Walk (u r) x₂, q.IsPath ∧ q.support = C.support := by
                refine ⟨C.copy ?_ rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj.symm.trans h)), hu''r]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hC
              obtain ⟨Cc, hCcp, hCcs⟩ := hCc
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Cc hR₀p hCcp hadjvu
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hj12 hmem.1.symm)
              rw [hCcs] at hR₁s
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ h4 hR₁p hham4.isPath
                (weld_cross_adj (Ne.symm hj42) x₂)
                (by
                  intro w' _ hmem
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                  · exact hj41 h1
                  · exact hj42 h1)
              have hD₂c : ∃ q : (Gs j2).Walk y₂ (t r).2, q.IsPath ∧
                  q.support = D₂'.support := by
                refine ⟨D₂'.copy rfl (wInnerT_tgt htrj), ?_, SimpleGraph.Walk.support_copy ..⟩
                rw [SimpleGraph.Walk.isPath_copy]
                exact hD₂'
              obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ D₂c hR₂p hD₂cp
                ((weld_cross_adj (Ne.symm hj42) y₂).symm)
                (by
                  intro w' hw' hmem
                  rw [hD₂cs] at hw'
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
                  · exact hj12 h1.symm
                  · refine hdisjC w' h2 w' ?_ rfl
                    rw [hsuppD₂]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                  · exact hj42 h1.symm)
              refine ⟨R₃.copy rfl (Prod.ext htrj.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₃p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                  List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair, hD₂cs]
                constructor
                · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_left _ h2⟩)
                  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2⟩))
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_right _ h2⟩)
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨-, h1, h2⟩)
                  · exact Or.inl (Or.inl (Or.inl ⟨h1, by
                      rw [hg1other r hr hra] at h2
                      exact h2⟩))
                  · rw [hg2ι] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                    · exact Or.inr ⟨h1, h2⟩
                  · exact absurd hra' hra
                  · exact Or.inl (Or.inr ⟨h1, h2⟩)
            · have hsrj2 : (s r).1 = j2 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨h, -⟩
                · exact absurd h hsrj
                · exact h
              have htrj1 : (t r).1 = j1 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨-, h⟩
                · exact absurd h hsrj
                · exact h
              have hCc : ∃ q : (Gs j2).Walk (s r).2 x₂, q.IsPath ∧
                  q.support = C.support := by
                refine ⟨C.copy ?_ rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_src hsrj2]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hC
              obtain ⟨Cc, hCcp, hCcs⟩ := hCc
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j2, x₂), R.IsPath ∧
                  R.support = C.support.map (fun w' => (j2, w')) := by
                refine ⟨(Cc.map (weldLift Gs M j2)).copy (Prod.ext hsrj2.symm rfl) rfl,
                  ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hCcp
                · rw [SimpleGraph.Walk.support_copy, weldLift_support, hCcs]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ h4 hR₀p hham4.isPath
                (weld_cross_adj (Ne.symm hj42) x₂)
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hj42 hmem.1)
              have hD₂c : ∃ q : (Gs j2).Walk y₂ (v r), q.IsPath ∧
                  q.support = D₂'.support := by
                refine ⟨D₂'.copy rfl ?_, ?_, SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerT_conn (fun h => hj12 (htrj1.symm.trans h))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hD₂'
              obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ D₂c hR₁p hD₂cp
                ((weld_cross_adj (Ne.symm hj42) y₂).symm)
                (by
                  intro w' hw' hmem
                  rw [hD₂cs] at hw'
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
                  · refine hdisjC w' h2 w' ?_ rfl
                    rw [hsuppD₂]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                  · exact hj42 h1.symm)
              have hadjvu : (weldGraph ell Gs M).Adj (j2, v r) (j1, u r) := by
                have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (v r)
                rwa [show M j2 j1 (v r) = u r from by
                  rw [hpart r ((hDmem' r).mpr hr), hsrj2, htrj1]] at h
              have hseg : ∃ q : (Gs j1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q0 r hrmem1).support := by
                refine ⟨(Q0 r hrmem1).copy ?_ (wInnerT_tgt htrj1), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj2.symm.trans h).symm)]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem1
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ seg hR₂p hsegp hadjvu
                (by
                  intro w' _ hmem
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact hj12 h1
                  · exact hj41 h1.symm
                  · exact hj12 h1)
              refine ⟨R₃.copy rfl (Prod.ext htrj1.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₃p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                  List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair, hD₂cs, hsegs]
                constructor
                · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_left _ h2⟩)
                  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2⟩))
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_right _ h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨-, h1, h2⟩)
                  · exact Or.inr ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · rw [hg2ι] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
                    · exact Or.inl (Or.inr ⟨h1, h2⟩)
                  · exact absurd hra' hra
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
          · -- an ordinary pair: its two family segments spliced at its connector edge
            by_cases hsrj : (s r).1 = j1
            · have htrj : (t r).1 = j2 := by
                rcases hsplit6 r with ⟨-, h⟩ | ⟨h, -⟩
                · exact h
                · exact absurd (hsrj.symm.trans h) hj12
              have hseg2 : ∃ q : (Gs j2).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q2 r hrmem2).support := by
                refine ⟨(Q2 r hrmem2).copy ?_ (wInnerT_tgt htrj), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj.symm.trans h)), hu''r]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ2p r hrmem2
              obtain ⟨seg2, hseg2p, hseg2s⟩ := hseg2
              obtain ⟨R, hRp, hRs⟩ := weld_splice hj12
                ((Q0 r hrmem1).copy (wInnerS_src hsrj)
                  (wInnerT_conn (fun h => hj12 (h.symm.trans htrj)))) seg2
                (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem1) hseg2p
                (by rw [hpart r ((hDmem' r).mpr hr), hsrj, htrj])
              refine ⟨R.copy (Prod.ext hsrj.symm rfl) (Prod.ext htrj.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hseg2s]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                  · exact Or.inr (Or.inl ⟨h1, by rw [hg2other r hra hrι]; exact h2⟩)
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨hrι', -, -⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · exact Or.inr ⟨h1, by rw [hg2other r hra hrι] at h2; exact h2⟩
                  · exact absurd hra' hra
                  · exact absurd hrι' hrι
            · have hsrj2 : (s r).1 = j2 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨h, -⟩
                · exact absurd h hsrj
                · exact h
              have htrj1 : (t r).1 = j1 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨-, h⟩
                · exact absurd h hsrj
                · exact h
              have hseg2 : ∃ q : (Gs j2).Walk (s r).2 (v r), q.IsPath ∧
                  q.support = (Q2 r hrmem2).support := by
                refine ⟨(Q2 r hrmem2).copy (wInnerS_src hsrj2)
                  (wInnerT_conn (fun h => hj12 (htrj1.symm.trans h))), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                rw [SimpleGraph.Walk.isPath_copy]
                exact hQ2p r hrmem2
              obtain ⟨seg2, hseg2p, hseg2s⟩ := hseg2
              have hseg1 : ∃ q : (Gs j1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q0 r hrmem1).support := by
                refine ⟨(Q0 r hrmem1).copy ?_ (wInnerT_tgt htrj1), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj2.symm.trans h).symm)]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem1
              obtain ⟨seg1, hseg1p, hseg1s⟩ := hseg1
              obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hj12) seg2 seg1
                hseg2p hseg1p
                (by rw [hpart r ((hDmem' r).mpr hr), hsrj2, htrj1])
              refine ⟨R.copy (Prod.ext hsrj2.symm rfl) (Prod.ext htrj1.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, hseg2s, hseg1s]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inl ⟨h1, by rw [hg2other r hra hrι]; exact h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hra', -, -⟩ | ⟨hrι', -, -⟩)
                  · exact Or.inr ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · exact Or.inl ⟨h1, by rw [hg2other r hra hrι] at h2; exact h2⟩
                  · exact absurd hra' hra
                  · exact absurd hrι' hrι
    choose P hPp hPchar using hpaths
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
      ({j1, j2, j3, j4} : Finset (Fin ell)) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;>
        simp [h1]
    · rintro ⟨xj, xw⟩ hxJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
      rcases hxJ with rfl | rfl | rfl | rfl
      · obtain ⟨i, hi, hmem⟩ := hQ0cov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by rw [hg1a]; exact hmem⟩)⟩
          · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
              (Or.inl ⟨rfl, by rw [hg1last]; exact hmem⟩)⟩
        · have hilast : i ≠ Fin.last m := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
            rw [hg1other i hilast hia]; exact hmem⟩)⟩
      · obtain ⟨i, hi, hmem⟩ := hQ2cov xw
        by_cases hiι : i = ι
        · subst hiι
          rw [hsuppC] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
              rw [hg2ι]; exact List.mem_append_left _ hmem⟩))⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨a, (hPchar a (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
                rw [hg2a, hmem2]
                exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))⟩
            · rw [hsuppD₂] at hmem2
              rcases List.mem_cons.mp hmem2 with hmem3 | hmem3
              · exact ⟨a, (hPchar a (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
                  rw [hg2a, hmem3]
                  exact List.mem_cons_self ..⟩))⟩
              · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
                  rw [hg2ι]; exact List.mem_append_right _ hmem3⟩))⟩
        · have hia : i ≠ a := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
            rw [hg2other i hia hiι]; exact hmem⟩))⟩
      · exact ⟨a, (hPchar a (xj, xw)).mpr (Or.inr (Or.inr (Or.inl
          ⟨rfl, rfl, hham3.mem_support xw⟩)))⟩
      · exact ⟨ι, (hPchar ι (xj, xw)).mpr (Or.inr (Or.inr (Or.inr
          ⟨rfl, rfl, hham4.mem_support xw⟩)))⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hE1, h1, h2⟩ | ⟨hE1, h1, h2⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨hE1', h1', h2'⟩ |
          ⟨hE1', h1', h2'⟩
      · exact hg1disj r r' hrr' x.2 h2 h2'
      · exact hj12 (h1.symm.trans h1')
      · exact hj31 (h1'.symm.trans h1)
      · exact hj41 (h1'.symm.trans h1)
      · exact hj12 (h1'.symm.trans h1)
      · exact hg2disj r r' hrr' x.2 h2 h2'
      · exact hj32 (h1'.symm.trans h1)
      · exact hj42 (h1'.symm.trans h1)
      · exact hj31 (h1.symm.trans h1')
      · exact hj32 (h1.symm.trans h1')
      · exact hrr' (hE1.trans hE1'.symm)
      · exact hj34 (h1.symm.trans h1')
      · exact hj41 (h1.symm.trans h1')
      · exact hj42 (h1.symm.trans h1')
      · exact hj34 (h1'.symm.trans h1)
      · exact hrr' (hE1.trans hE1'.symm)



  ·    -- SHAPE II: the carrier's `j1` segment is connector-type
    have htouch2 : ∀ i : Fin (m + 1), (s i).1 = j2 ∨ (t i).1 = j2 := by
      intro i
      rcases hsplit6 i with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
    have hsaj2 : (s a).1 = j2 := by
      rcases hsplit6 a with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hshape
      · exact h
    have htaj1 : (t a).1 = j1 := by
      rcases hsplit6 a with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hshape
      · exact h
    -- peel the prefix once more: `y` stays with the last pair
    have hyApre : y ≠ wInnerS s u j1 a := by
      rw [wInnerS_conn hshape]
      intro h
      have h1 := hcoly
      rw [h] at h1
      have h2 := hucol a haD
      rw [htaj1] at h2
      rw [h1] at h2
      cases b <;> simp at h2
    obtain ⟨x0, A', hA', hadj_x0_y, hsuppA', hy_notA'⟩ := path_peel_last Apre hApre hyApre
    have hcolx0 : col (j1, x0) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j1, x0) (j1, y) :=
        (weldLift Gs M j1).map_adj hadj_x0_y
      have h := S.hproper _ _ hadj
      rw [hcoly] at h
      exact bool_eq_of_ne_not h
    -- the `j2` inner family over the first `m` pairs (the last pair's target is the
    -- second split point)
    have hfam2 : ∃ Q2 : ∀ i ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))),
        (Gs j2).Walk (wInnerS s u j2 i) (wInnerT t v j2 i),
        (∀ i (hi : i ∈ _), (Q2 i hi).IsPath) ∧
        (∀ x : W, ∃ i, ∃ hi : i ∈ _, x ∈ (Q2 i hi).support) ∧
        (∀ i (hi : i ∈ _), ∀ k (hk : k ∈ _), i ≠ k →
          ∀ x, ¬ (x ∈ (Q2 i hi).support ∧ x ∈ (Q2 k hk).support)) := by
      apply S.inner_family (b := b) j2 _ hA0ne hA0card
      · intro i hi
        by_cases hsij : (s i).1 = j2
        · rw [wInnerS_src hsij, ← hsij]
          exact hmono.1 i
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          rw [wInnerS_conn hsij, ← htij]
          exact hucol i (hDofA0 i hi)
      · intro i hi
        by_cases htij : (t i).1 = j2
        · rw [wInnerT_tgt htij, ← htij]
          exact hmono.2.1 i
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          rw [wInnerT_conn htij, ← hsij]
          exact hvcol i (hDofA0 i hi)
      · intro i hi k hk hik
        by_cases hsij : (s i).1 = j2 <;> by_cases hskj : (s k).1 = j2
        · rw [wInnerS_src hsij, wInnerS_src hskj]
          intro he
          exact hik (hmono.2.2.1 (Prod.ext (hsij.trans hskj.symm) he))
        · have htkj : (t k).1 = j2 := (htouch2 k).resolve_left hskj
          rw [wInnerS_src hsij, wInnerS_conn hskj]
          exact fun he => huS k (hDofA0 k hk) i (hsij.trans htkj.symm) he.symm
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          rw [wInnerS_conn hsij, wInnerS_src hskj]
          exact huS i (hDofA0 i hi) k (hskj.trans htij.symm)
        · have htij : (t i).1 = j2 := (htouch2 i).resolve_left hsij
          have htkj : (t k).1 = j2 := (htouch2 k).resolve_left hskj
          rw [wInnerS_conn hsij, wInnerS_conn hskj]
          exact huu k (hDofA0 k hk) i (hDofA0 i hi) hik (htij.trans htkj.symm)
      · intro i hi k hk hik
        by_cases htij : (t i).1 = j2 <;> by_cases htkj : (t k).1 = j2
        · rw [wInnerT_tgt htij, wInnerT_tgt htkj]
          intro he
          exact hik (hmono.2.2.2 (Prod.ext (htij.trans htkj.symm) he))
        · have hskj : (s k).1 = j2 := (htouch2 k).resolve_right htkj
          rw [wInnerT_tgt htij, wInnerT_conn htkj]
          exact fun he => hvT k (hDofA0 k hk) i (htij.trans hskj.symm) he.symm
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          rw [wInnerT_conn htij, wInnerT_tgt htkj]
          exact hvT i (hDofA0 i hi) k (htkj.trans hsij.symm)
        · have hsij : (s i).1 = j2 := (htouch2 i).resolve_right htij
          have hskj : (s k).1 = j2 := (htouch2 k).resolve_right htkj
          rw [wInnerT_conn htij, wInnerT_conn htkj]
          exact hvv k (hDofA0 k hk) i (hDofA0 i hi) hik (hsij.trans hskj.symm)
    obtain ⟨Q2, hQ2p, hQ2cov, hQ2dis⟩ := hfam2
    -- locate the last target inside the `j2` family and split there
    obtain ⟨ι, hι0, hιmem⟩ := hQ2cov (t (Fin.last m)).2
    have hιlast : ι ≠ Fin.last m := Finset.ne_of_mem_erase hι0
    have hpairtlast : t (Fin.last m) = (j2, (t (Fin.last m)).2) := Prod.ext hlastT rfl
    have htn_ne_S : (t (Fin.last m)).2 ≠ wInnerS s u j2 ι := by
      intro h
      have h1 := hmono.2.1 (Fin.last m)
      rw [hpairtlast] at h1
      by_cases hsij : (s ι).1 = j2
      · rw [wInnerS_src hsij] at h
        have h2 := hmono.1 ι
        rw [show s ι = (j2, (s ι).2) from Prod.ext hsij rfl] at h2
        rw [← h] at h2
        rw [h1] at h2
        cases b <;> simp at h2
      · have htij : (t ι).1 = j2 := (htouch2 ι).resolve_left hsij
        rw [wInnerS_conn hsij] at h
        have h2 := hucol ι (hDofA0 ι hι0)
        rw [htij] at h2
        rw [← h] at h2
        rw [h1] at h2
        cases b <;> simp at h2
    have htn_ne_T : (t (Fin.last m)).2 ≠ wInnerT t v j2 ι := by
      by_cases htij : (t ι).1 = j2
      · rw [wInnerT_tgt htij]
        intro h
        exact hιlast (hmono.2.2.2 (Prod.ext (htij.trans hlastT.symm) h.symm))
      · have hsij : (s ι).1 = j2 := (htouch2 ι).resolve_right htij
        rw [wInnerT_conn htij]
        intro h
        exact hvT ι (hDofA0 ι hι0) (Fin.last m) (hlastT.trans hsij.symm) h.symm
    obtain ⟨xι, un, C, D₂, hC, hD₂, hadj_xι_tn, hadj_tn_un, hsuppC⟩ :=
      path_split_interior (Q2 ι hι0) (hQ2p ι hι0) hιmem htn_ne_S htn_ne_T
    have hndC := (hQ2p ι hι0).support_nodup
    rw [hsuppC] at hndC
    obtain ⟨hndC1, hndC2, hdisjC⟩ := List.nodup_append.mp hndC
    have htn_notD₂ : (t (Fin.last m)).2 ∉ D₂.support := (List.nodup_cons.mp hndC2).1
    have hcolun : col (j2, un) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, (t (Fin.last m)).2) (j2, un) :=
        (weldLift Gs M j2).map_adj hadj_tn_un
      have h := S.hproper _ _ hadj
      have h2 := hmono.2.1 (Fin.last m)
      rw [hpairtlast] at h2
      rw [h2] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcolxι : col (j2, xι) = b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, xι) (j2, (t (Fin.last m)).2) :=
        (weldLift Gs M j2).map_adj hadj_xι_tn
      have h := S.hproper _ _ hadj
      have h2 := hmono.2.1 (Fin.last m)
      rw [hpairtlast] at h2
      rw [h2] at h
      exact bool_eq_of_ne_not h
    have hun_ne : un ≠ wInnerT t v j2 ι := by
      by_cases htij : (t ι).1 = j2
      · rw [wInnerT_tgt htij]
        intro h
        have h2 := hmono.2.1 ι
        rw [show t ι = (j2, (t ι).2) from Prod.ext htij rfl] at h2
        rw [← h] at h2
        rw [hcolun] at h2
        cases b <;> simp at h2
      · have hsij : (s ι).1 = j2 := (htouch2 ι).resolve_right htij
        rw [wInnerT_conn htij]
        intro h
        have h2 := hvcol ι (hDofA0 ι hι0)
        rw [hsij] at h2
        rw [← h] at h2
        rw [hcolun] at h2
        cases b <;> simp at h2
    obtain ⟨yι, D₂', hD₂', hadj_un_yι, hsuppD₂, hun_notD₂'⟩ := path_peel_head D₂ hD₂ hun_ne
    have hcolyι : col (j2, yι) = !b := by
      have hadj : (weldGraph ell Gs M).Adj (j2, un) (j2, yι) :=
        (weldLift Gs M j2).map_adj hadj_un_yι
      have h := S.hproper _ _ hadj
      rw [hcolun] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    -- the fresh vertex in `j3` and its `j4` partner
    have hyz : y ≠ z := by
      intro h
      exact hdisjA y (SimpleGraph.Walk.end_mem_support Apre) z
        (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support B)) h
    have hynavoid : ({M j1 j3 x0} ∪ {M j4 j3 (M j2 j4 yι)} : Finset W).card
        < 2 * (m + 1) - 1 := by
      have h1 := Finset.card_union_le ({M j1 j3 x0} : Finset W)
        ({M j4 j3 (M j2 j4 yι)} : Finset W)
      rw [Finset.card_singleton, Finset.card_singleton] at h1
      omega
    obtain ⟨yn, hcolyn, hynavoids⟩ := S.exists_avoid j3 (!b) _ hynavoid
    have hyn_x0 : yn ≠ M j1 j3 x0 := by
      intro h
      exact hynavoids (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr h)))
    have hxn_yι : M j3 j4 yn ≠ M j2 j4 yι := by
      intro h
      refine hynavoids (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr ?_)))
      rw [S.hM j3 j4, ← h]
      exact (Equiv.symm_apply_apply ..).symm
    -- colors across the bridges
    have hcyE : col (j3, M j1 j3 y) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) y)
      rw [hcoly] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hczE : col (j3, M j1 j3 z) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) z)
      rw [hcolz] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcx0E : col (j3, M j1 j3 x0) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj31) x0)
      rw [hcolx0] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    have hcxnE : col (j4, M j3 j4 yn) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) hj34 yn)
      rw [hcolyn] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcyιE : col (j4, M j2 j4 yι) = b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) yι)
      rw [hcolyι] at h
      exact bool_eq_of_ne_not (Ne.symm h)
    have hcunE : col (j4, M j2 j4 un) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) un)
      rw [hcolun] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    have hcxιE : col (j4, M j2 j4 xι) = !b := by
      have h := S.hproper _ _ (weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj42) xι)
      rw [hcolxι] at h
      exact bool_eq_not_of_ne (Ne.symm h)
    -- the `j3` 2-cover
    have hd3 : OppositeDemand (fun w' => col (j3, w'))
        ![M j1 j3 y, M j1 j3 z] ![yn, M j1 j3 x0] := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · show col (j3, M j1 j3 y) ≠ col (j3, yn)
          rw [hcyE, hcolyn]
          cases b <;> simp
        · show col (j3, M j1 j3 z) ≠ col (j3, M j1 j3 x0)
          rw [hczE, hcx0E]
          cases b <;> simp
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd ((M j1 j3).injective (h : M j1 j3 y = M j1 j3 z)) hyz
        · exact absurd ((M j1 j3).injective (h : M j1 j3 z = M j1 j3 y)) (Ne.symm hyz)
        · rfl
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd (h : yn = M j1 j3 x0) hyn_x0
        · exact absurd (h : M j1 j3 x0 = yn).symm hyn_x0
        · rfl
      · intro i k
        fin_cases i <;> fin_cases k
        · intro h
          have h2 : M j1 j3 y = yn := h
          rw [h2] at hcyE
          rw [hcolyn] at hcyE
          cases b <;> simp at hcyE
        · intro h
          have h2 : M j1 j3 y = M j1 j3 x0 := h
          have h3 := (M j1 j3).injective h2
          exact hy_notA' (h3 ▸ SimpleGraph.Walk.end_mem_support A')
        · intro h
          have h2 : M j1 j3 z = yn := h
          rw [h2] at hczE
          rw [hcolyn] at hczE
          cases b <;> simp at hczE
        · intro h
          have h2 : M j1 j3 z = M j1 j3 x0 := h
          rw [h2] at hczE
          rw [hcx0E] at hczE
          cases b <;> simp at hczE
    obtain ⟨q3, hq3p, hq3cov, hq3dis⟩ := S.inner_cover j3 (by omega) (by omega) _ _ hd3
    -- the `j4` 2-cover
    have hd4 : OppositeDemand (fun w' => col (j4, w'))
        ![M j3 j4 yn, M j2 j4 yι] ![M j2 j4 un, M j2 j4 xι] := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · show col (j4, M j3 j4 yn) ≠ col (j4, M j2 j4 un)
          rw [hcxnE, hcunE]
          cases b <;> simp
        · show col (j4, M j2 j4 yι) ≠ col (j4, M j2 j4 xι)
          rw [hcyιE, hcxιE]
          cases b <;> simp
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · exact absurd (h : M j3 j4 yn = M j2 j4 yι) hxn_yι
        · exact absurd (h : M j2 j4 yι = M j3 j4 yn).symm hxn_yι
        · rfl
      · intro i k h
        fin_cases i <;> fin_cases k
        · rfl
        · refine absurd ((M j2 j4).injective (h : M j2 j4 un = M j2 j4 xι)) ?_
          intro hh
          refine hdisjC xι (SimpleGraph.Walk.end_mem_support C) un ?_ hh.symm
          rw [hsuppD₂]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · refine absurd ((M j2 j4).injective (h : M j2 j4 xι = M j2 j4 un)) ?_
          intro hh
          refine hdisjC xι (SimpleGraph.Walk.end_mem_support C) un ?_ hh
          rw [hsuppD₂]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rfl
      · intro i k
        fin_cases i <;> fin_cases k
        · intro h
          have h2 : M j3 j4 yn = M j2 j4 un := h
          rw [h2] at hcxnE
          rw [hcunE] at hcxnE
          cases b <;> simp at hcxnE
        · intro h
          have h2 : M j3 j4 yn = M j2 j4 xι := h
          rw [h2] at hcxnE
          rw [hcxιE] at hcxnE
          cases b <;> simp at hcxnE
        · intro h
          have h2 : M j2 j4 yι = M j2 j4 un := h
          rw [h2] at hcyιE
          rw [hcunE] at hcyιE
          cases b <;> simp at hcyιE
        · intro h
          have h2 : M j2 j4 yι = M j2 j4 xι := h
          rw [h2] at hcyιE
          rw [hcxιE] at hcyιE
          cases b <;> simp at hcyιE
    obtain ⟨q4, hq4p, hq4cov, hq4dis⟩ := S.inner_cover j4 (by omega) (by omega) _ _ hd4
    -- clean-endpoint segments
    have hq30' : ∃ q : (Gs j3).Walk (M j1 j3 y) yn, q.IsPath ∧ q.support = (q3 0).support :=
      ⟨(q3 0).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hq3p 0, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨q30c, hq30p, hq30s⟩ := hq30'
    have hq31' : ∃ q : (Gs j3).Walk (M j1 j3 x0) (M j1 j3 z), q.IsPath ∧
        ∀ x2 : W, x2 ∈ q.support ↔ x2 ∈ (q3 1).support := by
      refine ⟨(q3 1).reverse.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (hq3p 1).reverse
      · intro x2
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse]
    obtain ⟨q31c, hq31p, hq31m⟩ := hq31'
    have hq40' : ∃ q : (Gs j4).Walk (M j3 j4 yn) (M j2 j4 un), q.IsPath ∧
        q.support = (q4 0).support :=
      ⟨(q4 0).copy rfl rfl, by
        rw [SimpleGraph.Walk.isPath_copy]
        exact hq4p 0, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨q40c, hq40p, hq40s⟩ := hq40'
    have hq41' : ∃ q : (Gs j4).Walk (M j2 j4 xι) (M j2 j4 yι), q.IsPath ∧
        ∀ x2 : W, x2 ∈ q.support ↔ x2 ∈ (q4 1).support := by
      refine ⟨(q4 1).reverse.copy rfl rfl, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (hq4p 1).reverse
      · intro x2
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse, List.mem_reverse]
    obtain ⟨q41c, hq41p, hq41m⟩ := hq41'
    have hA'c : ∃ q : (Gs j1).Walk (u a) x0, q.IsPath ∧ q.support = A'.support :=
      ⟨A'.copy (wInnerS_conn hshape) rfl, by
        rw [SimpleGraph.Walk.isPath_copy]; exact hA', SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨A'c, hA'cp, hA'cs⟩ := hA'c
    have hBc : ∃ q : (Gs j1).Walk z (t a).2, q.IsPath ∧ q.support = B.support :=
      ⟨B.copy rfl (wInnerT_tgt htaj1), by
        rw [SimpleGraph.Walk.isPath_copy]; exact hB, SimpleGraph.Walk.support_copy ..⟩
    obtain ⟨Bc, hBcp, hBcs⟩ := hBc
    -- the per-copy segment lists
    set g1 : Fin (m + 1) → List W := fun r =>
      if r = Fin.last m then ((s (Fin.last m)).2 :: [y])
      else if hra : r = a then A'.support ++ B.support
      else if hr : r = Fin.last m then []
      else (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support with hg1
    have hg1last : g1 (Fin.last m) = ((s (Fin.last m)).2 :: [y]) := by
      simp [hg1]
    have hg1a : g1 a = A'.support ++ B.support := by
      simp [hg1, halast]
    have hg1other : ∀ r, ∀ hr : r ≠ Fin.last m, r ≠ a →
        g1 r = (Q0 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
      intro r hr hra
      simp only [hg1]
      rw [if_neg hr, dif_neg hra, dif_neg hr]
    set g2 : Fin (m + 1) → List W := fun r =>
      if r = Fin.last m then (un :: [(t (Fin.last m)).2])
      else if r = ι then C.support ++ D₂'.support
      else if hr : r = Fin.last m then []
      else (Q2 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support with hg2
    have hg2last : g2 (Fin.last m) = (un :: [(t (Fin.last m)).2]) := by
      simp [hg2]
    have hg2ι : g2 ι = C.support ++ D₂'.support := by
      simp [hg2, hιlast]
    have hg2other : ∀ r, ∀ hr : r ≠ Fin.last m, r ≠ ι →
        g2 r = (Q2 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
      intro r hr hrι
      simp only [hg2]
      rw [if_neg hr, if_neg hrι, dif_neg hr]
    -- coverage decompositions and pairwise disjointness of the segment lists
    have hsubA' : ∀ x2 : W, x2 ∈ A'.support → x2 ∈ Apre.support := by
      intro x2 h
      rw [hsuppA']
      exact List.mem_append_left _ h
    have hsub_g1a : ∀ x2 : W, x2 ∈ g1 a → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg1a] at h
      rw [hsuppA]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (hsubA' x2 h)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hsub_g1last : ∀ x2 : W, x2 ∈ g1 (Fin.last m) → x2 ∈ (Q0 a ha0).support := by
      intro x2 h
      rw [hg1last] at h
      rcases List.mem_cons.mp h with h | h
      · rw [h, hsuppA]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · rw [List.mem_singleton] at h
        rw [h, hsuppA]
        exact List.mem_append_left _ (by
          rw [hsuppA']
          exact List.mem_append_right _ (List.mem_singleton_self _))
    have hg1_lastva : ∀ x2 : W, x2 ∈ g1 (Fin.last m) → x2 ∈ g1 a → False := by
      intro x2 h h'
      rw [hg1last] at h
      rw [hg1a] at h'
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
    have hg1disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g1 r → x2 ∉ g1 r' := by
      intro r r' hrr' x2 h h'
      by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
      · exact hrr' (hr.trans hr'.symm)
      · rw [hr] at h
        by_cases hra : r' = a
        · rw [hra] at h'
          exact hg1_lastva x2 h h'
        · rw [hg1other r' hr' hra] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra x2 ⟨h', hsub_g1last x2 h⟩
      · rw [hr'] at h'
        by_cases hra : r = a
        · rw [hra] at h
          exact hg1_lastva x2 h' h
        · rw [hg1other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_g1last x2 h'⟩
      · by_cases hra : r = a <;> by_cases hra' : r' = a
        · exact hrr' (hra.trans hra'.symm)
        · rw [hra] at h
          rw [hg1other r' hr' hra'] at h'
          exact hQ0disj r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) a ha0
            hra' x2 ⟨h', hsub_g1a x2 h⟩
        · rw [hra'] at h'
          rw [hg1other r hr hra] at h
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) a ha0
            hra x2 ⟨h, hsub_g1a x2 h'⟩
        · rw [hg1other r hr hra] at h
          rw [hg1other r' hr' hra'] at h'
          exact hQ0disj r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    have hsub_g2ι : ∀ x2 : W, x2 ∈ g2 ι → x2 ∈ (Q2 ι hι0).support := by
      intro x2 h
      rw [hg2ι] at h
      rw [hsuppC]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (by
          rw [hsuppD₂]
          exact List.mem_cons_of_mem _ h))
    have hsub_g2last : ∀ x2 : W, x2 ∈ g2 (Fin.last m) → x2 ∈ (Q2 ι hι0).support := by
      intro x2 h
      rw [hg2last] at h
      rw [hsuppC]
      have hmem2 : x2 ∈ ((t (Fin.last m)).2 :: D₂.support) := by
        rw [hsuppD₂]
        rcases List.mem_cons.mp h with h | h
        · rw [h]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rw [List.mem_singleton] at h
          rw [h]
          exact List.mem_cons_self ..
      exact List.mem_append_right _ hmem2
    have hg2_lastι : ∀ x2 : W, x2 ∈ g2 (Fin.last m) → x2 ∈ g2 ι → False := by
      intro x2 h h'
      rw [hg2last] at h
      rw [hg2ι] at h'
      rcases List.mem_cons.mp h with h | h
      · rcases List.mem_append.mp h' with h'' | h''
        · refine hdisjC x2 h'' x2 ?_ rfl
          rw [h, hsuppD₂]
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · exact hun_notD₂' (h ▸ h'')
      · rw [List.mem_singleton] at h
        rcases List.mem_append.mp h' with h'' | h''
        · exact hdisjC x2 h'' x2 (h ▸ List.mem_cons_self ..) rfl
        · exact htn_notD₂ (h ▸ (by rw [hsuppD₂]; exact List.mem_cons_of_mem _ h''))
    have hg2disj : ∀ r r' : Fin (m + 1), r ≠ r' → ∀ x2 : W, x2 ∈ g2 r → x2 ∉ g2 r' := by
      intro r r' hrr' x2 h h'
      by_cases hr : r = Fin.last m <;> by_cases hr' : r' = Fin.last m
      · exact hrr' (hr.trans hr'.symm)
      · rw [hr] at h
        by_cases hrι : r' = ι
        · rw [hrι] at h'
          exact hg2_lastι x2 h h'
        · rw [hg2other r' hr' hrι] at h'
          exact hQ2dis r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) ι hι0
            hrι x2 ⟨h', hsub_g2last x2 h⟩
      · rw [hr'] at h'
        by_cases hrι : r = ι
        · rw [hrι] at h
          exact hg2_lastι x2 h' h
        · rw [hg2other r hr hrι] at h
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) ι hι0
            hrι x2 ⟨h, hsub_g2last x2 h'⟩
      · by_cases hrι : r = ι <;> by_cases hrι' : r' = ι
        · exact hrr' (hrι.trans hrι'.symm)
        · rw [hrι] at h
          rw [hg2other r' hr' hrι'] at h'
          exact hQ2dis r' (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) ι hι0
            hrι' x2 ⟨h', hsub_g2ι x2 h⟩
        · rw [hrι'] at h'
          rw [hg2other r hr hrι] at h
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) ι hι0
            hrι x2 ⟨h, hsub_g2ι x2 h'⟩
        · rw [hg2other r hr hrι] at h
          rw [hg2other r' hr' hrι'] at h'
          exact hQ2dis r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) r'
            (Finset.mem_erase.mpr ⟨hr', Finset.mem_univ r'⟩) hrr' x2 ⟨h, h'⟩
    -- the per-pair weld paths
    have hpaths : ∀ r : Fin (m + 1), ∃ P : (weldGraph ell Gs M).Walk (s r) (t r), P.IsPath ∧
        ∀ x : Fin ell × W, x ∈ P.support ↔
          ((x.1 = j1 ∧ x.2 ∈ g1 r) ∨ (x.1 = j2 ∧ x.2 ∈ g2 r) ∨
            (x.1 = j3 ∧ ((r = Fin.last m ∧ x.2 ∈ (q3 0).support) ∨
              (r = a ∧ x.2 ∈ (q3 1).support))) ∨
            (x.1 = j4 ∧ ((r = Fin.last m ∧ x.2 ∈ (q4 0).support) ∨
              (r = ι ∧ x.2 ∈ (q4 1).support)))) := by
      intro r
      by_cases hr : r = Fin.last m
      · -- the last pair threads both bridge copies
        subst hr
        have hW1p : (SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil :
            (Gs j1).Walk (s (Fin.last m)).2 y).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcoly
          rw [← h] at h1
          have h2 := hmono.1 (Fin.last m)
          rw [hpairlast] at h2
          rw [h2] at h1
          cases b <;> simp at h1
        have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s (Fin.last m)) (j1, y), R.IsPath ∧
            R.support = [(s (Fin.last m)).2, y].map (fun w' => (j1, w')) := by
          refine ⟨((SimpleGraph.Walk.cons hadj_y_sn.symm SimpleGraph.Walk.nil).map
            (weldLift Gs M j1)).copy (Prod.ext hlastS.symm rfl) rfl, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_copy]
            exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hW1p
          · rw [SimpleGraph.Walk.support_copy, weldLift_support,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
        obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
        obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q30c hR₀p hq30p
          (weld_cross_adj (Ne.symm hj31) y)
          (by
            intro w' _ hmem
            rw [hR₀s, mem_map_pair] at hmem
            exact hj31 hmem.1)
        obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ q40c hR₁p hq40p
          (weld_cross_adj hj34 yn)
          (by
            intro w' _ hmem
            rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
            rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hj41 h1
            · exact hj34 h1.symm)
        have hW2p : (SimpleGraph.Walk.cons hadj_tn_un.symm SimpleGraph.Walk.nil :
            (Gs j2).Walk un (t (Fin.last m)).2).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
          intro h
          have h1 := hcolun
          rw [h] at h1
          have h2 := hmono.2.1 (Fin.last m)
          rw [hpairtlast] at h2
          rw [h2] at h1
          cases b <;> simp at h1
        obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂
          (SimpleGraph.Walk.cons hadj_tn_un.symm SimpleGraph.Walk.nil) hR₂p hW2p
          ((weld_cross_adj (Ne.symm hj42) un).symm)
          (by
            intro w' _ hmem
            rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
              mem_map_pair, mem_map_pair, mem_map_pair] at hmem
            rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
            · exact hj12 h1.symm
            · exact hj32 h1.symm
            · exact hj42 h1.symm)
        refine ⟨R₃.copy rfl (Prod.ext hlastT.symm rfl), ?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_copy]
          exact hR₃p
        · intro x
          rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s, List.mem_append,
            hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair,
            mem_map_pair, hq30s, hq40s]
          constructor
          · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · refine Or.inl ⟨h1, ?_⟩
              rw [hg1last]
              simpa using h2
            · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inl ⟨rfl, h2⟩⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inl ⟨rfl, h2⟩⟩))
            · refine Or.inr (Or.inl ⟨h1, ?_⟩)
              rw [hg2last]
              simpa using h2
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hra, -⟩⟩ | ⟨h1, ⟨-, h2⟩ | ⟨hrι, -⟩⟩)
            · refine Or.inl (Or.inl (Or.inl ⟨h1, ?_⟩))
              rw [hg1last] at h2
              simpa using h2
            · refine Or.inr ⟨h1, ?_⟩
              rw [hg2last] at h2
              simpa using h2
            · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
            · exact absurd hra.symm halast
            · exact Or.inl (Or.inr ⟨h1, h2⟩)
            · exact absurd hrι.symm hιlast
      · by_cases hra : r = a
        · -- the carrier: its `j2` segment, the freed prefix, the `j3` detour, the suffix
          subst hra
          by_cases hιa : ι = r
          · -- its `j2` segment is itself the second carrier: reroute it through `j4` too
            subst hιa
            have hCa : ∃ q : (Gs j2).Walk (s ι).2 xι, q.IsPath ∧ q.support = C.support := by
              refine ⟨C.copy (wInnerS_src hsaj2) rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
              rw [SimpleGraph.Walk.isPath_copy]
              exact hC
            obtain ⟨Ca, hCap, hCas⟩ := hCa
            have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s ι) (j2, xι), R.IsPath ∧
                R.support = C.support.map (fun w' => (j2, w')) := by
              refine ⟨(Ca.map (weldLift Gs M j2)).copy (Prod.ext hsaj2.symm rfl) rfl, ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hCap
              · rw [SimpleGraph.Walk.support_copy, weldLift_support, hCas]
            obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q41c hR₀p hq41p
              (weld_cross_adj (Ne.symm hj42) xι)
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hj42 hmem.1)
            have hD₂c : ∃ q : (Gs j2).Walk yι (v ι), q.IsPath ∧
                q.support = D₂'.support := by
              refine ⟨D₂'.copy rfl ?_, ?_, SimpleGraph.Walk.support_copy ..⟩
              · rw [wInnerT_conn (fun h => hj12 (htaj1.symm.trans h))]
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hD₂'
            obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
            obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ D₂c hR₁p hD₂cp
              ((weld_cross_adj (Ne.symm hj42) yι).symm)
              (by
                intro w' hw' hmem
                rw [hD₂cs] at hw'
                rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
                · refine hdisjC w' h2 w' ?_ rfl
                  rw [hsuppD₂]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                · exact hj42 h1.symm)
            have hadjvu : (weldGraph ell Gs M).Adj (j2, v ι) (j1, u ι) := by
              have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (v ι)
              rwa [show M j2 j1 (v ι) = u ι from by
                rw [hpart ι haD, hsaj2, htaj1]] at h
            obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ A'c hR₂p hA'cp hadjvu
              (by
                intro w' _ hmem
                rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                · exact hj12 h1
                · exact hj41 h1.symm
                · exact hj12 h1)
            rw [hA'cs] at hR₃s
            obtain ⟨R₄, hR₄p, hR₄s⟩ := weld_splice_snoc R₃ q31c hR₃p hq31p
              (weld_cross_adj (Ne.symm hj31) x0)
              (by
                intro w' _ hmem
                rw [hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s, List.mem_append,
                  hR₀s, mem_map_pair, mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with ((⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩) | ⟨h1, -⟩
                · exact hj32 h1
                · exact hj34 h1
                · exact hj32 h1
                · exact hj31 h1)
            obtain ⟨R₅, hR₅p, hR₅s⟩ := weld_splice_snoc R₄ Bc hR₄p hBcp
              ((weld_cross_adj (Ne.symm hj31) z).symm)
              (by
                intro w' hw' hmem
                rw [hBcs] at hw'
                rw [hR₄s, List.mem_append, hR₃s, List.mem_append, hR₂s, List.mem_append,
                  hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair] at hmem
                rcases hmem with (((⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩) | ⟨-, h2⟩) | ⟨h1, -⟩
                · exact hj12 h1
                · exact hj41 h1.symm
                · exact hj12 h1
                · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                · exact hj31 h1.symm)
            refine ⟨R₅.copy rfl (Prod.ext htaj1.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hR₅p
            · intro x
              rw [SimpleGraph.Walk.support_copy, hR₅s, List.mem_append, hR₄s,
                List.mem_append, hR₃s, List.mem_append, hR₂s, List.mem_append, hR₁s,
                List.mem_append, hR₀s, mem_map_pair, mem_map_pair, mem_map_pair,
                mem_map_pair, mem_map_pair, mem_map_pair, hD₂cs, hBcs]
              constructor
              · rintro (((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
                  ⟨h1, h2⟩)
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hg2ι]
                    exact List.mem_append_left _ h2⟩)
                · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inr ⟨rfl, (hq41m x.2).mp h2⟩⟩))
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hg2ι]
                    exact List.mem_append_right _ h2⟩)
                · exact Or.inl ⟨h1, by rw [hg1a]; exact List.mem_append_left _ h2⟩
                · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, (hq31m x.2).mp h2⟩⟩))
                · exact Or.inl ⟨h1, by rw [hg1a]; exact List.mem_append_right _ h2⟩
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨-, h2⟩⟩ |
                  ⟨h1, ⟨hrl, -⟩ | ⟨-, h2⟩⟩)
                · rw [hg1a] at h2
                  rcases List.mem_append.mp h2 with h2 | h2
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                  · exact Or.inr ⟨h1, h2⟩
                · rw [hg2ι] at h2
                  rcases List.mem_append.mp h2 with h2 | h2
                  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))))
                  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, h2⟩)))
                · exact absurd hrl halast
                · exact Or.inl (Or.inr ⟨h1, (hq31m x.2).mpr h2⟩)
                · exact absurd hrl halast
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
                    ⟨h1, (hq41m x.2).mpr h2⟩))))
          · -- its `j2` segment is an untouched family path
            have hfamA : ∃ q : (Gs j2).Walk (s r).2 (v r), q.IsPath ∧
                q.support = (Q2 r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)).support := by
              refine ⟨(Q2 r _).copy (wInnerS_src hsaj2)
                (wInnerT_conn (fun h => hj12 (htaj1.symm.trans h))), ?_,
                SimpleGraph.Walk.support_copy ..⟩
              rw [SimpleGraph.Walk.isPath_copy]
              exact hQ2p _ _
            obtain ⟨famA, hfamAp, hfamAs⟩ := hfamA
            have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j2, v r), R.IsPath ∧
                R.support = (Q2 r (Finset.mem_erase.mpr
                  ⟨hr, Finset.mem_univ r⟩)).support.map (fun w' => (j2, w')) := by
              refine ⟨(famA.map (weldLift Gs M j2)).copy (Prod.ext hsaj2.symm rfl) rfl,
                ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hfamAp
              · rw [SimpleGraph.Walk.support_copy, weldLift_support, hfamAs]
            obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
            have hadjvu : (weldGraph ell Gs M).Adj (j2, v r) (j1, u r) := by
              have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (v r)
              rwa [show M j2 j1 (v r) = u r from by
                rw [hpart r haD, hsaj2, htaj1]] at h
            obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ A'c hR₀p hA'cp hadjvu
              (by
                intro w' _ hmem
                rw [hR₀s, mem_map_pair] at hmem
                exact hj12 hmem.1)
            rw [hA'cs] at hR₁s
            obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ q31c hR₁p hq31p
              (weld_cross_adj (Ne.symm hj31) x0)
              (by
                intro w' _ hmem
                rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                · exact hj32 h1
                · exact hj31 h1)
            obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ Bc hR₂p hBcp
              ((weld_cross_adj (Ne.symm hj31) z).symm)
              (by
                intro w' hw' hmem
                rw [hBcs] at hw'
                rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                  mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
                · exact hj12 h1
                · exact hdisjA w' (hsubA' w' h2) w' (List.mem_cons_of_mem _ hw') rfl
                · exact hj31 h1.symm)
            refine ⟨R₃.copy rfl (Prod.ext htaj1.symm rfl), ?_, ?_⟩
            · rw [SimpleGraph.Walk.isPath_copy]
              exact hR₃p
            · intro x
              rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                mem_map_pair, mem_map_pair, hBcs]
              constructor
              · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                · exact Or.inr (Or.inl ⟨h1, by
                    rw [hg2other r hr (fun h => hιa h.symm)]
                    exact h2⟩)
                · exact Or.inl ⟨h1, by rw [hg1a]; exact List.mem_append_left _ h2⟩
                · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr ⟨rfl, (hq31m x.2).mp h2⟩⟩))
                · exact Or.inl ⟨h1, by rw [hg1a]; exact List.mem_append_right _ h2⟩
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨-, h2⟩⟩ |
                  ⟨h1, ⟨hrl, -⟩ | ⟨hrι, -⟩⟩)
                · rw [hg1a] at h2
                  rcases List.mem_append.mp h2 with h2 | h2
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                  · exact Or.inr ⟨h1, h2⟩
                · exact Or.inl (Or.inl (Or.inl ⟨h1, by
                    rw [hg2other r hr (fun h => hιa h.symm)] at h2
                    exact h2⟩))
                · exact absurd hrl halast
                · exact Or.inl (Or.inr ⟨h1, (hq31m x.2).mpr h2⟩)
                · exact absurd hrl halast
                · exact absurd hrι.symm hιa
        · have hrmem : r ∈ (Finset.univ.erase (Fin.last m) : Finset (Fin (m + 1))) :=
            Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
          have hrD : r ∈ D := (hDmem' r).mpr hr
          by_cases hrι : r = ι
          · -- the second carrier: its `j2` segment reroutes through `j4`
            subst hrι
            by_cases hsrj : (s r).1 = j2
            · have htrj1 : (t r).1 = j1 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨-, h⟩
                · exact absurd (h.symm.trans hsrj) hj12
                · exact h
              have hCc : ∃ q : (Gs j2).Walk (s r).2 xι, q.IsPath ∧
                  q.support = C.support := by
                refine ⟨C.copy (wInnerS_src hsrj) rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
                rw [SimpleGraph.Walk.isPath_copy]
                exact hC
              obtain ⟨Cc, hCcp, hCcs⟩ := hCc
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j2, xι), R.IsPath ∧
                  R.support = C.support.map (fun w' => (j2, w')) := by
                refine ⟨(Cc.map (weldLift Gs M j2)).copy (Prod.ext hsrj.symm rfl) rfl,
                  ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) hCcp
                · rw [SimpleGraph.Walk.support_copy, weldLift_support, hCcs]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ q41c hR₀p hq41p
                (weld_cross_adj (Ne.symm hj42) xι)
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hj42 hmem.1)
              have hD₂c : ∃ q : (Gs j2).Walk yι (v r), q.IsPath ∧
                  q.support = D₂'.support := by
                refine ⟨D₂'.copy rfl ?_, ?_, SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerT_conn (fun h => hj12 (htrj1.symm.trans h))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hD₂'
              obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ D₂c hR₁p hD₂cp
                ((weld_cross_adj (Ne.symm hj42) yι).symm)
                (by
                  intro w' hw' hmem
                  rw [hD₂cs] at hw'
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨-, h2⟩ | ⟨h1, -⟩
                  · refine hdisjC w' h2 w' ?_ rfl
                    rw [hsuppD₂]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                  · exact hj42 h1.symm)
              have hadjvu : (weldGraph ell Gs M).Adj (j2, v r) (j1, u r) := by
                have h := weld_cross_adj (Gs := Gs) (M := M) (Ne.symm hj12) (v r)
                rwa [show M j2 j1 (v r) = u r from by
                  rw [hpart r hrD, hsrj, htrj1]] at h
              have hseg : ∃ q : (Gs j1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q0 r hrmem).support := by
                refine ⟨(Q0 r hrmem).copy ?_ (wInnerT_tgt htrj1), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj.symm.trans h).symm)]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem
              obtain ⟨seg, hsegp, hsegs⟩ := hseg
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ seg hR₂p hsegp hadjvu
                (by
                  intro w' _ hmem
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨h1, -⟩
                  · exact hj12 h1
                  · exact hj41 h1.symm
                  · exact hj12 h1)
              refine ⟨R₃.copy rfl (Prod.ext htrj1.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₃p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                  List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair, hD₂cs, hsegs]
                constructor
                · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_left _ h2⟩)
                  · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inr ⟨rfl, (hq41m x.2).mp h2⟩⟩))
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_right _ h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hrl, -⟩ | ⟨-, h2⟩⟩)
                  · exact Or.inr ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · rw [hg2ι] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
                    · exact Or.inl (Or.inr ⟨h1, h2⟩)
                  · exact absurd hrl hr
                  · exact absurd hra' hra
                  · exact absurd hrl hr
                  · exact Or.inl (Or.inl (Or.inr ⟨h1, (hq41m x.2).mpr h2⟩))
            · have hsrj1 : (s r).1 = j1 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨h, -⟩
                · exact h
                · exact absurd h hsrj
              have htrj2 : (t r).1 = j2 := by
                rcases hsplit6 r with ⟨-, h⟩ | ⟨h, -⟩
                · exact h
                · exact absurd h hsrj
              have hR0 : ∃ R : (weldGraph ell Gs M).Walk (s r) (j1, v r), R.IsPath ∧
                  R.support = (Q0 r hrmem).support.map (fun w' => (j1, w')) := by
                refine ⟨(((Q0 r hrmem).copy (wInnerS_src hsrj1)
                  (wInnerT_conn (fun h => hj12 ((htrj2.symm.trans h).symm)))).map
                  (weldLift Gs M j1)).copy (Prod.ext hsrj1.symm rfl) rfl, ?_, ?_⟩
                · rw [SimpleGraph.Walk.isPath_copy]
                  refine SimpleGraph.Walk.map_isPath_of_injective (weldLift_inj _) ?_
                  rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem
                · rw [SimpleGraph.Walk.support_copy, weldLift_support,
                    SimpleGraph.Walk.support_copy]
              obtain ⟨R₀, hR₀p, hR₀s⟩ := hR0
              have hadjvu : (weldGraph ell Gs M).Adj (j1, v r) (j2, u r) := by
                have h := weld_cross_adj (Gs := Gs) (M := M) hj12 (v r)
                rwa [show M j1 j2 (v r) = u r from by
                  rw [hpart r hrD, hsrj1, htrj2]] at h
              have hCc : ∃ q : (Gs j2).Walk (u r) xι, q.IsPath ∧
                  q.support = C.support := by
                refine ⟨C.copy ?_ rfl, ?_, SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj1.symm.trans h))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hC
              obtain ⟨Cc, hCcp, hCcs⟩ := hCc
              obtain ⟨R₁, hR₁p, hR₁s⟩ := weld_splice_snoc R₀ Cc hR₀p hCcp hadjvu
                (by
                  intro w' _ hmem
                  rw [hR₀s, mem_map_pair] at hmem
                  exact hj12 hmem.1.symm)
              rw [hCcs] at hR₁s
              obtain ⟨R₂, hR₂p, hR₂s⟩ := weld_splice_snoc R₁ q41c hR₁p hq41p
                (weld_cross_adj (Ne.symm hj42) xι)
                (by
                  intro w' _ hmem
                  rw [hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
                  · exact hj41 h1
                  · exact hj42 h1)
              have hD₂c : ∃ q : (Gs j2).Walk yι (t r).2, q.IsPath ∧
                  q.support = D₂'.support := by
                refine ⟨D₂'.copy rfl (wInnerT_tgt htrj2), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                rw [SimpleGraph.Walk.isPath_copy]
                exact hD₂'
              obtain ⟨D₂c, hD₂cp, hD₂cs⟩ := hD₂c
              obtain ⟨R₃, hR₃p, hR₃s⟩ := weld_splice_snoc R₂ D₂c hR₂p hD₂cp
                ((weld_cross_adj (Ne.symm hj42) yι).symm)
                (by
                  intro w' hw' hmem
                  rw [hD₂cs] at hw'
                  rw [hR₂s, List.mem_append, hR₁s, List.mem_append, hR₀s,
                    mem_map_pair, mem_map_pair, mem_map_pair] at hmem
                  rcases hmem with (⟨h1, -⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
                  · exact hj12 h1.symm
                  · refine hdisjC w' h2 w' ?_ rfl
                    rw [hsuppD₂]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw')
                  · exact hj42 h1.symm)
              refine ⟨R₃.copy rfl (Prod.ext htrj2.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hR₃p
              · intro x
                rw [SimpleGraph.Walk.support_copy, hR₃s, List.mem_append, hR₂s,
                  List.mem_append, hR₁s, List.mem_append, hR₀s, mem_map_pair, mem_map_pair,
                  mem_map_pair, mem_map_pair, hD₂cs]
                constructor
                · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_left _ h2⟩)
                  · exact Or.inr (Or.inr (Or.inr ⟨h1, Or.inr ⟨rfl, (hq41m x.2).mp h2⟩⟩))
                  · exact Or.inr (Or.inl ⟨h1, by
                      rw [hg2ι]
                      exact List.mem_append_right _ h2⟩)
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hrl, -⟩ | ⟨-, h2⟩⟩)
                  · exact Or.inl (Or.inl (Or.inl ⟨h1, by
                      rw [hg1other r hr hra] at h2
                      exact h2⟩))
                  · rw [hg2ι] at h2
                    rcases List.mem_append.mp h2 with h2 | h2
                    · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
                    · exact Or.inr ⟨h1, h2⟩
                  · exact absurd hrl hr
                  · exact absurd hra' hra
                  · exact absurd hrl hr
                  · exact Or.inl (Or.inr ⟨h1, (hq41m x.2).mpr h2⟩)
          · -- an ordinary pair
            by_cases hsrj : (s r).1 = j1
            · have htrj : (t r).1 = j2 := by
                rcases hsplit6 r with ⟨-, h⟩ | ⟨h, -⟩
                · exact h
                · exact absurd (hsrj.symm.trans h) hj12
              have hseg2 : ∃ q : (Gs j2).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q2 r hrmem).support := by
                refine ⟨(Q2 r hrmem).copy ?_ (wInnerT_tgt htrj), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj.symm.trans h))]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ2p r hrmem
              obtain ⟨seg2, hseg2p, hseg2s⟩ := hseg2
              obtain ⟨R, hRp, hRs⟩ := weld_splice hj12
                ((Q0 r hrmem).copy (wInnerS_src hsrj)
                  (wInnerT_conn (fun h => hj12 (h.symm.trans htrj)))) seg2
                (by rw [SimpleGraph.Walk.isPath_copy]; exact hQ0path r hrmem) hseg2p
                (by rw [hpart r hrD, hsrj, htrj])
              refine ⟨R.copy (Prod.ext hsrj.symm rfl) (Prod.ext htrj.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, SimpleGraph.Walk.support_copy, hseg2s]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                  · exact Or.inr (Or.inl ⟨h1, by rw [hg2other r hr hrι]; exact h2⟩)
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hrl, -⟩ | ⟨hrι', -⟩⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · exact Or.inr ⟨h1, by rw [hg2other r hr hrι] at h2; exact h2⟩
                  · exact absurd hrl hr
                  · exact absurd hra' hra
                  · exact absurd hrl hr
                  · exact absurd hrι' hrι
            · have hsrj2 : (s r).1 = j2 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨h, -⟩
                · exact absurd h hsrj
                · exact h
              have htrj1 : (t r).1 = j1 := by
                rcases hsplit6 r with ⟨h, -⟩ | ⟨-, h⟩
                · exact absurd h hsrj
                · exact h
              have hseg2 : ∃ q : (Gs j2).Walk (s r).2 (v r), q.IsPath ∧
                  q.support = (Q2 r hrmem).support := by
                refine ⟨(Q2 r hrmem).copy (wInnerS_src hsrj2)
                  (wInnerT_conn (fun h => hj12 (htrj1.symm.trans h))), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                rw [SimpleGraph.Walk.isPath_copy]
                exact hQ2p r hrmem
              obtain ⟨seg2, hseg2p, hseg2s⟩ := hseg2
              have hseg1 : ∃ q : (Gs j1).Walk (u r) (t r).2, q.IsPath ∧
                  q.support = (Q0 r hrmem).support := by
                refine ⟨(Q0 r hrmem).copy ?_ (wInnerT_tgt htrj1), ?_,
                  SimpleGraph.Walk.support_copy ..⟩
                · rw [wInnerS_conn (fun h => hj12 (hsrj2.symm.trans h).symm)]
                · rw [SimpleGraph.Walk.isPath_copy]
                  exact hQ0path r hrmem
              obtain ⟨seg1, hseg1p, hseg1s⟩ := hseg1
              obtain ⟨R, hRp, hRs⟩ := weld_splice (Ne.symm hj12) seg2 seg1
                hseg2p hseg1p
                (by rw [hpart r hrD, hsrj2, htrj1])
              refine ⟨R.copy (Prod.ext hsrj2.symm rfl) (Prod.ext htrj1.symm rfl), ?_, ?_⟩
              · rw [SimpleGraph.Walk.isPath_copy]
                exact hRp
              · intro x
                rw [SimpleGraph.Walk.support_copy, hRs, List.mem_append, mem_map_pair,
                  mem_map_pair, hseg2s, hseg1s]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact Or.inr (Or.inl ⟨h1, by rw [hg2other r hr hrι]; exact h2⟩)
                  · exact Or.inl ⟨h1, by rw [hg1other r hr hra]; exact h2⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, ⟨hrl, -⟩ | ⟨hra', -⟩⟩ |
                    ⟨h1, ⟨hrl, -⟩ | ⟨hrι', -⟩⟩)
                  · exact Or.inr ⟨h1, by rw [hg1other r hr hra] at h2; exact h2⟩
                  · exact Or.inl ⟨h1, by rw [hg2other r hr hrι] at h2; exact h2⟩
                  · exact absurd hrl hr
                  · exact absurd hra' hra
                  · exact absurd hrl hr
                  · exact absurd hrι' hrι
    choose P hPp hPchar using hpaths
    refine weld_lemma21 S.hproper S.copy_lace (hmono.st_ne 0 0)
      ({j1, j2, j3, j4} : Finset (Fin ell)) P hPp ?_ ?_ ?_
    · intro r x hx
      rcases (hPchar r x).mp hx with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        simp [h1]
    · rintro ⟨xj, xw⟩ hxJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
      rcases hxJ with rfl | rfl | rfl | rfl
      · obtain ⟨i, hi, hmem⟩ := hQ0cov xw
        by_cases hia : i = a
        · subst hia
          rw [hsuppA] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · rw [hsuppA'] at hmem
            rcases List.mem_append.mp hmem with hmem2 | hmem2
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg1a]; exact List.mem_append_left _ hmem2⟩)⟩
            · rw [List.mem_singleton] at hmem2
              exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg1last, hmem2]
                exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg1last, hmem2]
                exact List.mem_cons_self ..⟩)⟩
            · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
                rw [hg1a]; exact List.mem_append_right _ hmem2⟩)⟩
        · have hilast : i ≠ Fin.last m := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inl ⟨rfl, by
            rw [hg1other i hilast hia]; exact hmem⟩)⟩
      · obtain ⟨i, hi, hmem⟩ := hQ2cov xw
        by_cases hiι : i = ι
        · subst hiι
          rw [hsuppC] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
              rw [hg2ι]; exact List.mem_append_left _ hmem⟩))⟩
          · rcases List.mem_cons.mp hmem with hmem2 | hmem2
            · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
                (Or.inr (Or.inl ⟨rfl, by
                  rw [hg2last, hmem2]
                  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))⟩
            · rw [hsuppD₂] at hmem2
              rcases List.mem_cons.mp hmem2 with hmem3 | hmem3
              · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
                  (Or.inr (Or.inl ⟨rfl, by
                    rw [hg2last, hmem3]
                    exact List.mem_cons_self ..⟩))⟩
              · exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
                  rw [hg2ι]; exact List.mem_append_right _ hmem3⟩))⟩
        · have hilast : i ≠ Fin.last m := Finset.ne_of_mem_erase hi
          exact ⟨i, (hPchar i (xj, xw)).mpr (Or.inr (Or.inl ⟨rfl, by
            rw [hg2other i hilast hiι]; exact hmem⟩))⟩
      · obtain ⟨iE, hiE⟩ := hq3cov xw
        fin_cases iE
        · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
            (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, hiE⟩⟩)))⟩
        · exact ⟨a, (hPchar a (xj, xw)).mpr
            (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, hiE⟩⟩)))⟩
      · obtain ⟨iE, hiE⟩ := hq4cov xw
        fin_cases iE
        · exact ⟨Fin.last m, (hPchar (Fin.last m) (xj, xw)).mpr
            (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, hiE⟩⟩)))⟩
        · exact ⟨ι, (hPchar ι (xj, xw)).mpr
            (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, hiE⟩⟩)))⟩
    · intro r r' hrr' x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases (hPchar r x).mp hx1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, hE⟩ | ⟨h1, hE⟩ <;>
        rcases (hPchar r' x).mp hx2 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', hE'⟩ | ⟨h1', hE'⟩
      · exact hg1disj r r' hrr' x.2 h2 h2'
      · exact hj12 (h1.symm.trans h1')
      · exact hj31 (h1'.symm.trans h1)
      · exact hj41 (h1'.symm.trans h1)
      · exact hj12 (h1'.symm.trans h1)
      · exact hg2disj r r' hrr' x.2 h2 h2'
      · exact hj32 (h1'.symm.trans h1)
      · exact hj42 (h1'.symm.trans h1)
      · exact hj31 (h1.symm.trans h1')
      · exact hj32 (h1.symm.trans h1')
      · rcases hE with ⟨hrl, hm⟩ | ⟨hra, hm⟩ <;> rcases hE' with ⟨hrl', hm'⟩ | ⟨hra', hm'⟩
        · exact hrr' (hrl.trans hrl'.symm)
        · exact hq3dis 0 1 (by decide) x.2 ⟨hm, hm'⟩
        · exact hq3dis 0 1 (by decide) x.2 ⟨hm', hm⟩
        · exact hrr' (hra.trans hra'.symm)
      · exact hj34 (h1.symm.trans h1')
      · exact hj41 (h1.symm.trans h1')
      · exact hj42 (h1.symm.trans h1')
      · exact hj34 (h1'.symm.trans h1)
      · rcases hE with ⟨hrl, hm⟩ | ⟨hrι, hm⟩ <;> rcases hE' with ⟨hrl', hm'⟩ | ⟨hrι', hm'⟩
        · exact hrr' (hrl.trans hrl'.symm)
        · exact hq4dis 0 1 (by decide) x.2 ⟨hm, hm'⟩
        · exact hq4dis 0 1 (by decide) x.2 ⟨hm', hm⟩
        · exact hrr' (hrι.trans hrι'.symm)









/-- **Case 6 of Coleman et al. 2025, Proposition 1.6**: two copies meet every pair, and
    a source lies in the first. -/
theorem prop16_case6 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) {b : Bool}
    {s t : Fin n → Fin ell × W} (hmono : MonoDemand col b s t)
    {j1 j2 : Fin ell} (hj12 : j1 ≠ j2)
    (hw1 : (weldWSet s t j1).card = n) (hw2 : (weldWSet s t j2).card = n)
    (hS1 : ∃ i, (s i).1 = j1) :
    IsPairedDPC (weldGraph ell Gs M) n s t := by
  classical
  have hn := S.hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit6 : ∀ i, ((s i).1 = j1 ∧ (t i).1 = j2) ∨ ((s i).1 = j2 ∧ (t i).1 = j1) := by
    intro i
    have h1 := weldWSet_full_touch hw1 i
    have h2 := weldWSet_full_touch hw2 i
    rcases h1 with hs1 | ht1 <;> rcases h2 with hs2 | ht2
    · exact absurd (hs1.symm.trans hs2) hj12
    · exact Or.inl ⟨hs1, ht2⟩
    · exact Or.inr ⟨hs2, ht1⟩
    · exact absurd (ht1.symm.trans ht2) hj12
  obtain ⟨i₀, hi₀⟩ := hS1
  apply dpc_perm (Equiv.swap i₀ (Fin.last m))
  have hmono' : MonoDemand col b (fun i => s (Equiv.swap i₀ (Fin.last m) i))
      (fun i => t (Equiv.swap i₀ (Fin.last m) i)) :=
    ⟨fun i => hmono.1 _, fun i => hmono.2.1 _,
      hmono.2.2.1.comp (Equiv.swap i₀ (Fin.last m)).injective,
      hmono.2.2.2.comp (Equiv.swap i₀ (Fin.last m)).injective⟩
  refine prop16_case6_core S hmono' hj12 (fun i => hsplit6 _) ?_
  show (s (Equiv.swap i₀ (Fin.last m) (Fin.last m))).1 = j1
  rw [Equiv.swap_apply_right]
  exact hi₀

#print axioms prop16_case6


/-- **Proposition 1.6 of Coleman et al. 2025** (the weld induction step): under the
    setting, the weld admits paired `n`-DPCs for every legal demand. The six-way case
    dispatch is machine-checked: at most two copies can meet every pair, and every
    configuration lands in one of the six proved cases. -/
theorem prop16 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool}
    (S : ColemanProp16Setting ell n Gs M col) :
    IsPairedKDPCForOpposite (weldGraph ell Gs M) col n := by
  classical
  apply pairedKDPC_of_mono
  intro b s t hmono
  by_cases hfull : ∃ j0, (weldWSet s t j0).card = n
  · obtain ⟨j0, hw0⟩ := hfull
    by_cases hfull2 : ∃ j2, j2 ≠ j0 ∧ (weldWSet s t j2).card = n
    · -- two full copies: Case 6, or Case 3 when no source lies in the first
      obtain ⟨j2, hj2, hw2⟩ := hfull2
      by_cases hS1 : ∃ i, (s i).1 = j0
      · exact prop16_case6 S hmono (Ne.symm hj2) hw0 hw2 hS1
      · have hT : ∀ i, (t i).1 = j0 := fun i =>
          (weldWSet_full_touch hw0 i).resolve_left (fun h => hS1 ⟨i, h⟩)
        have hS : ∀ i, (s i).1 = j2 := by
          intro i
          rcases weldWSet_full_touch hw2 i with h | h
          · exact h
          · exact absurd ((hT i).symm.trans h).symm hj2
        exact prop16_case3 S hmono hj2 hS hT
    · -- exactly one full copy: Cases 2, 4, or 5
      have hw : ∀ j, j ≠ j0 → (weldWSet s t j).card ≤ n - 1 := by
        intro j hj
        have h1 := weldWSet_card_le s t j
        have h2 : (weldWSet s t j).card ≠ n := fun h => hfull2 ⟨j, hj, h⟩
        omega
      by_cases hSin : ∀ i, (s i).1 = j0
      · by_cases hTin : ∀ i, (t i).1 = j0
        · exact prop16_case2 S hmono hSin hTin
        · have hT0 : ∃ i, (t i).1 ≠ j0 := by
            by_contra h
            exact hTin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
          exact prop16_case4 S hmono hSin hT0 hw
      · have hS0 : ∃ i, (s i).1 ≠ j0 := by
          by_contra h
          exact hSin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
        by_cases hTin : ∀ i, (t i).1 = j0
        · apply dpc_swap
          have hw' : ∀ j, j ≠ j0 → (weldWSet t s j).card ≤ n - 1 := by
            intro j hj
            rw [weldWSet_swap]
            exact hw j hj
          exact prop16_case4 S hmono.swap hTin hS0 hw'
        · have hT0 : ∃ i, (t i).1 ≠ j0 := by
            by_contra h
            exact hTin (fun i => Classical.byContradiction fun hh => h ⟨i, hh⟩)
          exact prop16_case5 S hmono hw0 hS0 hT0 hw
  · -- no full copy: Case 1
    have hw : ∀ j, (weldWSet s t j).card ≤ n - 1 := by
      intro j
      have h1 := weldWSet_card_le s t j
      have h2 : (weldWSet s t j).card ≠ n := fun h => hfull ⟨j, h⟩
      omega
    exact prop16_case1 S hmono hw

/-- The Tier 3 target, discharged: Proposition 1.6 in its packaged form. -/
theorem coleman_prop16 {ell n : ℕ} {Gs : Fin ell → SimpleGraph W}
    {M : Fin ell → Fin ell → (W ≃ W)} {col : Fin ell × W → Bool} :
    ColemanProp16Statement ell n Gs M col :=
  fun S => prop16 S

#print axioms coleman_prop16

end Brualdi.Ledger
