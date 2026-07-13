# The proofs, in English — a reader's companion to the Lean development

> **Status (2026-07-13).** Corrected after the round-6 consolidation: the Section 5 numbering,
> the cited-axiom count (seven, not ten), and the status of the Coleman and Jo-Park-Chwa imports
> (proved here, not assumed) were all stale, and are now fixed against the actual kernel trace.
> `tools/check_docs_consistency.py` gates this file against `manuscript/PAPER.md` and
> `brualdi_lean/EXPECTED_AXIOMS.txt` on every change, so it cannot drift silently again.
>
> **CERTIFIED by the math session, 2026-07-13.** The three §5 merges were confirmed against
> the official LEMMAS.md renumber map composed with the consolidation, the whole-chain
> adversary's old-5.7d = new-5.7(ii) identification, and the prose↔Lean refresh table; all
> spot-checked Lean names resolve at source (boxProd_hamConn_one_bip_walk:1206,
> row_interface_two_of_nonbip:8661, pivot_thread_data_of_buffer:10898, walk_pick_terminals:223,
> coleman_thm15 as a THEOREM at Coleman.lean:69); the as-printed status claims match the
> refresh's certified list. Two fixes applied at certification: the Theorem 7.1 row no longer
> uses axiom tags for discharged inputs, and the Prop 4.1 row names the assembled wrapper.
> Cleared for the companion repository.

**What this is.** One entry for every result the paper proves, plus the supporting theorems
that exist only in Lean. Each entry gives three artifacts: the **statement** in ordinary
mathematics; a **step-by-step account of the Lean proof**, keyed to source line ranges, at
the granularity of the proof's intermediate facts (every line is accounted for; routine
tactic bookkeeping is grouped and said in a sentence); and a **proof reconstructed solely
from the Lean** — standalone mathematical prose derived from the formal proof and nothing
else. For proofs that follow the paper, the reconstruction is a back-translation the reader
can lay beside the paper's text; for proofs that exist only in Lean (the alternates, and the
Gale–Ryser development), it is the only prose proof there is.

**Conventions.** Lean code never appears here — each entry links to the source, pinned to
the commit this document describes, so line anchors cannot drift. Private helper lemmas are
not separate entries; they are explained as named steps inside the theorem that uses them.
Results the paper *cites* rather than proves are axioms of the development; they appear in
the coverage table with their axiom tags and are treated in full (verbatim source quotes,
faithfulness notes) in `TRUST_SURFACE.md` §3, not here.

**Commit described:** [`a6dbe1e`](https://github.com/jbaggett/brualdi-interchange-lean/tree/a6dbe1ebb0e05c7b3ce915899aae65944338d653).
`#print axioms` verdicts quoted per entry were kernel-checked at this commit.

---

# Coverage — every claim of the paper, and where it lives here

| Paper item | Lean | Status | Entry |
|---|---|---|---|
| **Theorem 1.1** (main theorem) | `brualdi_MH` (Ledger) | proved; kernel trace = foundations + the seven cited axioms | I.1 |
| §1 Corollary (realization graphs) | — | prose-only three-line argument; Arikati–Peled correspondence source-audited 2026-07-03; deliberately not mechanized | I.2 |
| **Lemma 1.2** (Block Lemma) | `CORE` / `core_global` (Ledger) | proved, via Theorem 7.1 + Proposition 2.2 | V.1 |
| **Lemma 2.1** (bipartite ⟺ triangle-free) | `invariantFree_nonbip_has_triangle` | **cited** (axiom A5, used direction; converse trivial, proved); support characterization mechanized in the 5.10 block | — (TRUST_SURFACE A5) |
| **Proposition 2.2** (CT-product structure) | `weak_ct_product` + `interchange_bipartite_equitable` | **cited** (axiom A4); equitability consequence proved | — (TRUST_SURFACE A4) |
| §2.2 inactive-line deletion | `exists_active_iso` + deletion isomorphisms (Sec6) | proved | VI.2 |
| §3 reduction skeleton (induction + trichotomy + bipartite branch) | `reduction_glue`, `trichotomy`, `reduction_bipartite`, `reduction` (Ledger) | proved | I.3 |
| **Proposition 4.1** | `boxProd_hamConn_one_bip_walk` (Sec4Walk; assembled into `boxProd_hamConnected_paper`) | proved **as printed** (walk device); independent absorber alternate (`boxProd_hamConn_one_bip`, Sec4) | II.1, II.5 |
| §4 **Claim** (controlled spanning walks) | `controlled_spanning_walks` (AltProofs) | proved **as printed** | II.2 |
| **Lemma 4.2** (doubled-layer terminals) | `walk_pick_terminals` + the per-shape boundary passes (Sec4Walk) | proved (carried inside the passes; also inside the absorber alternate) | II.3 |
| §4 both-factors-non-bipartite case | `boxProd_hamConn_both_nonbip` via `boxProd_snake_hamPath` (Sec4) | proved, same argument as the paper | II.4 |
| §4 K₂ prism case | `boxProd_prism_card_two` (Sec4) | proved, same argument | II.4 |
| **Lemma 5.1** (canonical fibers) | `rowProj_fibre_iso_patOfSet`, `fibre_isInterchangeGraph` | paper-side bookkeeping; the Lean induction consumes raw fibers directly, so no renormalization is needed (entry explains) | III.1 |
| **Lemma 5.2** (pivot-freedom) | `active_prime_cell_varies` | **cited** (axiom A6, Brualdi–Manber Thm 9) — the paper cites it too since 2026-07-05, structure-matrix derivation kept as a remark | — (TRUST_SURFACE A6) |
| **Lemma 5.3** (patterns are matroid bases) | `rowPattern_baseFamily` (Sec5) | proved **as printed** (Gale–Ryser + deficient sets, on `galeRyser_exists`); independent minimal-pair alternate (`rowPattern_baseFamily_minpair`) | III.2, III.3 |
| **Lemma 5.4** (unit-transfer) | `ryser_fulkerson_unitTransfer`, `rowQuotient_iso_baseExchange` | proved **as printed** (the paper's proof is this argument, ported 2026-07-04) | III.4 |
| **Corollary 5.5** (Q_L Hamilton-connected) | `rowQuotient_hamConnected` | proved from **cited** axiom A9 (Naddef–Pulleyblank) | III.5 |
| **Lemma 5.6** (whole-fiber interface) | `row_interface_all_of_bip_source` | proved | III.6 |
| **Lemma 5.6** (interface ≥ 2) | `row_interface_two_of_nonbip` | proved | III.7 |
| **Lemma 5.7** (reachable-terminal richness) | `row_bip_source_reach_two` + `row_bip_source_avoid` | proved **as printed** (since 2026-07-05); the avoid form also carries the independent constructive proof `row_bip_source_avoid_direct` | III.8 |
| **Lemma 5.7** (non-bipartite two-sided avoid) | `row_two_of_nonbip_avoid` | proved | III.9 |
| **Lemma 5.8** (triangle classification) | `triangle_classification`, `wide_row_pair_supports_triangle` | proved (both directions) | III.10 |
| **Lemma 5.9** (buffer existence) | `buffer_line_exists` | proved | III.11 |
| **Lemma 5.10** (buffer quotient non-bipartite) | `rowQuotient_nonbip` (Sec5) | proved **as printed**, including shiftedness (`rowPattern_shifted`, the Gale–Ryser exchange; unit-transfer alternate kept); independent rank-sum alternate (`rowQuotient_nonbip_rankmin`) | III.12, III.13 |
| **Proposition 5.11** (middle-buffer gluing) | `forward_build`/`backward_build`, `row_hinterface_step*`, `pivot_thread_data_of_buffer` | proved | III.14 |
| **Proposition 5.11** (endpoint-buffer gluing) | threading machinery + `pivotBufferData_of_row_line` | proved | III.15 |
| **Proposition 5.11** (single-pass gluing) | `flip_hamConnected_of_row_buffer`, `reduction_pivot` (+ `stageBTransposeIso`) | proved | III.16 |
| §6 base classes | `reduction_base`, `flipGraph_two_row_iso_johnson` (proved), `small_interchange_MH` (pure-kernel certificates); `johnson_isMH` | proved except the **cited** Johnson input (axiom A10, Alspach) | IV.1 |
| **Theorem 7.1** (CT products paired 2-DPC) | `canonicalCTProduct_paired_two` (+ `ctProduct_paired_two_of_ranks`: the statement for arbitrary factor orders, via the machine-checked sort isomorphism), `completeTransposition_paired_two`, `ctProduct_consLarge_paired_two`, `CORE'` | proved (the double induction); its three inputs — formerly axioms A1–A3, now the machine-checked theorems `coleman_thm15_proved`, `prop11c_proved`, `hypercube_paired_two_proved` — are foundations-only, so this chain carries no cited axiom | V.2 |
| **Theorem 7.2** (Coleman Thm 1.5) | `coleman_thm15` | **proved** (`coleman_thm15_proved`), not an axiom | — (TRUST_SURFACE A1) |
| **Theorem 7.3** (Coleman Prop 1.1(c)) | `prop11c` | **proved** (`prop11c_proved`); hypercube branch **proved** (`hypercube_paired_two_proved`) | — (TRUST_SURFACE A2, A3) |
| — (Lean-only) Gale–Ryser existence | `galeRyser_exists` (GaleRyser) | proved, foundations-only; feeds Lemma 5.3 | III.2a |
| — (Lean-only) Ryser 2-switch edge existence | `interchange_has_edge` (Ryser) | proved | VI.1 |
| — (Lean-only) laceability bridges | `paired2dpc_to_laceable`, `paired_two_opposite_to_hamLaceable`, `laceable_card_two` | proved | VI.3 |

Cited rows carry no proof to reconstruct; their verbatim source quotes and faithfulness
audits are in `TRUST_SURFACE.md` §3. Everything else receives a full entry below.

---

# Part I — the Main Theorem and the reduction skeleton (§1, §3)

## I.1 Theorem 1.1 and the induction glue: `brualdi_MH`, `reduction`, `reduction_glue`

**Lean:** [`Ledger.lean` lines 943–995](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L943-L995) — trace = foundations + the seven cited axioms (the whole development's surface; `#print axioms brualdi_MH`).

### Statement

For every pair of margin vectors `R ∈ ℕᵐ`, `S ∈ ℕⁿ`, the interchange graph `G(R,S)` is
maximally Hamiltonian: Hamilton-connected if non-bipartite, and Hamilton-laceable with
respect to a proper surjective 2-coloring if bipartite.

The Lean statement (`brualdi_MH`, 989–995) quantifies over *all* margins, with no
realizability hypothesis: for an empty or one-vertex class the Hamilton-connected disjunct
holds vacuously, so the formal theorem is slightly stronger than the paper's display, which
restricts to realizable margins. (`IsMH`'s laceable disjunct demands a proper *surjective*
coloring precisely so that this vacuity cannot leak anywhere else; see TRUST_SURFACE D6.)

### The Lean proof, step by step

- `brualdi_MH` (989–995) is assembly: every flip graph is tautologically an interchange
  graph (`flipGraph_isInterchange`, 982–984, witnessed by the identity equivalence), and the
  reduction applied to the machine-checked CORE bridge (`core_global`, entry V.1) finishes.
- `reduction` (975–980) specializes `reduction_glue` to `n = |V|`.
- `reduction_glue` (943–973) is the paper's §3 skeleton. Strong induction on the vertex
  count (945–949); the induction hypothesis is repackaged so it applies to any strictly
  smaller interchange graph (950–954). The dispatch follows the manuscript's order
  (955–973): if the graph carries a balanced-bipartite coloring, the bipartite branch
  applies (entry I.3) — no induction needed; otherwise, if it is decomposable, the §4 branch
  consumes the induction hypothesis (entry II.6); otherwise, if it is a base class, the §6
  branch applies (entry IV.1); otherwise all three failures make it *indecomposable
  non-base* by definition, a wide active core exists (`wideActiveCore_of_not_base` — a
  non-base class has more than six vertices, hence at least three active rows and three
  active columns in an active representative), and the §5 pivot branch closes (entry
  III.16). The deliberate reordering — products split off *before* the ≤6-vertex base — is
  recorded in the dispatch comment (954–956): the census in §6 only ever faces
  indecomposable classes.
- `trichotomy` (253–263) is the exhaustiveness of this case split: classical, and
  definitional — the fourth class is *defined* as the failure of the other three, which is
  the formal counterpart of the paper's "the cases are exhaustive by inspection."

### The proof, reconstructed from the Lean

**Theorem.** Every interchange graph is maximally Hamiltonian.

**Proof.** By strong induction on the number of vertices `N` of `G = G(R,S)`; the induction
hypothesis is that every interchange graph on fewer than `N` vertices is maximally
Hamiltonian.

Distinguish four exhaustive cases. If `G` admits a proper 2-coloring with balanced classes
(the bipartite case), the Block Lemma applies to `G` directly and yields Hamilton
laceability with no use of the induction hypothesis (entry I.3). Otherwise, if the class of
`G` decomposes — its active core factors as a nontrivial Cartesian product of two strictly
smaller interchange graphs — the induction hypothesis makes both factors maximally
Hamiltonian, and the product-lifting theorem of §4 makes `G` Hamilton-connected (Part II).
Otherwise, if `G` is a base class — at most two active rows or columns, or at most six
vertices — it is a Johnson graph (maximally Hamiltonian by Alspach's theorem) or one of a
finite census of small cores, checked directly (Part IV). In the one remaining case `G` is
active, indecomposable, non-bipartite and non-base; its active representative has at least
three active rows and columns, and the §5 pivot construction, consuming the induction
hypothesis on fibers, produces a Hamilton path between every pair of vertices (Part III).
∎

## I.2 The §1 Corollary (realization graphs) — prose-only, by design

**Lean:** none.

The corollary transfers Theorem 1.1 to realization graphs of bipartite degree sequences via
the Arikati–Peled correspondence (biadjacency matrix ↔ 2-switch). Its proof in the paper is
three lines and self-contained, and the correspondence was audited at the source
(Arikati–Peled 1999, full text, 2026-07-03: their §1 states the correspondence verbatim).
It is the one numbered claim of the paper deliberately left unmechanized; it imports
nothing into the main theorem's trace, and nothing in the development depends on it.

## I.3 The bipartite branch: `reduction_bipartite` (with `interchange_has_edge` and `paired2dpc_to_laceable`)

**Lean:** [`Ledger.lean` lines 167–213](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L167-L213) — trace: foundations + `weak_ct_product` (A4), `prop11c` (A2), and the Coleman-side axioms through `core_global`.

### Statement

A balanced-bipartite interchange graph is maximally Hamiltonian — specifically,
Hamilton-laceable with respect to its (proper, surjective) 2-coloring. This is the §3 branch
that consumes the Block Lemma globally, with no induction.

### The Lean proof, step by step

- On at most one vertex the Hamilton-connected disjunct is vacuous (211–213). Otherwise
  (193–209): a nontrivial interchange graph has an edge — Ryser's 2-switch existence,
  `interchange_has_edge` (188–190), proved in `Ryser.lean` (entry VI.1). The edge makes the
  proper coloring *surjective* (its endpoints receive both colors, 199–208), which the
  faithful `IsMH` demands.
- The Block Lemma (`core_global`, entry V.1) gives the paired 2-cover property; the bridge
  `paired2dpc_to_laceable` (167–186) converts it to Hamilton laceability. The bridge is
  where a 2026-07-04 soundness repair lives: on four or more vertices, equitability of the
  coloring (derived from the interchange structure, `interchange_bipartite_equitable`) feeds
  Coleman's downgrade (Theorem 7.3 with ℓ = 1) and produces Hamilton laceability
  (177–179); on exactly two vertices the downgrade's demand guard is vacuous — the earlier
  unguarded version of this step was *false* there — and instead the Ryser edge makes the
  graph `K₂`, which is laceable directly (180–186).

### The proof, reconstructed from the Lean

**Proposition.** A balanced-bipartite interchange graph `G` is Hamilton-laceable with
respect to its proper 2-coloring, which is surjective; in particular `G` is maximally
Hamiltonian.

**Proof.** If `G` has at most one vertex there is nothing to prove. Otherwise `G` has an
edge: its class contains two distinct matrices, and Ryser's 2-switch argument produces from
any two distinct members of a class a pair differing by a single interchange. The edge's
endpoints receive different colors, so the coloring is surjective.

By the Block Lemma, `G` admits paired 2-disjoint path covers for every balanced demand. If
`G` has at least four vertices: the coloring is equitable (an interchange graph's balanced
bipartition has equal class sizes), and Coleman's downgrade theorem with `ℓ = 1` turns the
paired 2-cover property into a paired 1-cover property for every opposite-colored pair —
that is, a Hamilton path between every two opposite-colored vertices. If `G` has fewer than
four vertices, equitability forces exactly two, one of each color; the edge between them is
a Hamilton path, and `G = K₂` is laceable directly. ∎

*Where this differs from the paper:* it does not. The paper's §3 glosses the surjectivity
bookkeeping (its definition of laceability does not require it); the Lean's `IsMH` requires
it to bar vacuous colorings, and the Ryser edge supplies it. The `K₂` guard is invisible at
paper level and load-bearing at Lean level — the unguarded downgrade was kernel-certified
false on the two-vertex class before the repair (TRUST_SURFACE §5.4).

---

# Part II — Cartesian products (§4)

## II.1 Proposition 4.1, as printed: `boxProd_hamConn_one_bip_walk` and the walk device

**Lean:** [`Sec4Walk.lean` lines 39–1273](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec4Walk.lean#L39-L1273) — foundations-only.

### Statement

Let `A` be balanced bipartite (proper surjective 2-coloring `χ`), Hamilton-laceable, paired
2-disjoint-path-coverable, with `|V(A)| ≥ 4`; let `B` be non-bipartite and
Hamilton-connected. Then `A □ B` is Hamilton-connected.

### The Lean proof, step by step

The development mirrors the paper's proof exactly; it has four layers.

- **The assembly interface, `walk_assembly_core` (39–77).** Given: a spanning walk of `B`
  as a list `walkB` (chained by adjacency, starting at `b₀`, ending at `b₁`); a boundary
  assignment `β` with `β(0) = a₀` and `β(N) = a₁` (`N` = the walk's length); and for each
  position `i < N` a piece — a duplicate-free path of `A` running from `β(i)` to `β(i+1)` —
  such that pieces at two positions carrying the *same* layer are disjoint, and every vertex
  `(a,b)` of the product lies in some piece at a position carrying `b`. Conclusion: a
  Hamilton `(a₀,b₀)`–`(a₁,b₁)` path of `A □ B`. The proof is a translation onto the verified
  layered splice `boxProd_layered_hamPath` (Sec4, entry II.5): heads, tails, and the
  matching conditions come from the per-piece endpoint facts (58–69), and the
  pairwise-disjointness over the walk's indexed positions is exactly the same-layer
  hypothesis (70–77).
- **The choice lemmas (82–116, 196–262).** `walk_pick_color_ne` (88–99): a vertex of a
  prescribed color avoiding one given vertex — the paper's "each color class of `A` has at
  least two vertices," supplied by `exists_same_color_ne_of_card_ge_four` (Sec4).
  `walk_pick_terminals` (223–262): the two free terminals of a doubled layer, one of each
  color, distinct from each other and from two given opposite-colored vertices — the
  engine of Lemma 4.2 (entry II.3). `walkColor` (101) is the telescoping color
  `χ(a₀) ⊕ (i mod 2)`; 103–116 and 181–194 record that it flips at every step. The
  penultimate-vertex lemmas (196–221) supply the neighbor-availability facts the paper
  gets from 2-connectedness.
- **The four walk shapes = the Claim's walks, each with the paper's boundary pass.**
  `walk_pass_hamPath` (123–180): a Hamilton path of `B` (no doubled layer); boundaries are
  pinned at the ends and otherwise any vertex of the telescoping color; every layer is
  traversed by a Hamilton path of `A` between opposite-colored boundaries (laceability).
  `walk_pass_plus_edge` (264–521): a Hamilton path `b₀ → w` closed by an edge `w b₁`, `w` a
  neighbor of `b₁` other than `b₀`; the layer of `b₁` is doubled (interior occurrence `k`
  and final position), receives a paired 2-cover with terminals
  `(β_k, β_{k+1})`, `(β_n, a₁)`, chosen distinct by `walk_pick_terminals` (355–366); the
  layer-uniqueness facts (368–380, 428–441) come from the underlying path's freedom from
  repeats. `walk_pass_cycle` (531–765): `b₀ = b₁`; a Hamilton cycle through `b₀`; the base
  layer is doubled and carries both pinned endpoints `a₀ ≠ a₁`; the two free terminals
  each face at most one same-color exclusion (611–648). `walk_pass_cycle_detour`
  (767–1204): the cycle with a two-edge detour `u′ m b₀`; both the base layer and the
  detour layer `m` are doubled; the boundary between the two final pieces is the paper's
  *shared* boundary, and the choice order — shared boundary first, then the base layer's
  free terminal, then the detour layer's — is the paper's refinement, keeping every choice
  to one same-color exclusion (900–1000).
- **The parity dispatch (1206–1273).** `boxProd_hamConn_one_bip_walk` (1206–1237) is the
  paper's selection step: the constraint is `χ(a₁) = walkColor(χ(a₀), N)`, the four shapes
  realize `N = n, n+1` (distinct layers) and `N = n+1, n+2` (same layer), consecutive `N`
  have opposite telescoping values, so exactly one available shape fits — "the two walks
  have opposite `N`-parities; take the right one." `boxProd_hamConn_one_bip_paper`
  (1239–1259) splits off `|V(A)| = 2` to the prism case first, as the paper does, deriving
  `|V(A)| ≥ 4` otherwise from evenness. `boxProd_hamConnected_paper` (1261–1273) is the §4
  umbrella: both-non-bipartite → the snake (II.4); exactly one bipartite → this
  proposition (through the product-commutation isomorphism if needed); both bipartite →
  impossible for a non-bipartite product.

### The proof, reconstructed from the Lean

**Proposition.** With `A`, `B` as in the statement, `A □ B` is Hamilton-connected.

**Proof.** Fix distinct `s₀ = (a₀,b₀)` and `s₁ = (a₁,b₁)`, and write `χ` for `A`'s
coloring, `n = |V(B)| ≥ 3`.

View `A □ B` as layers of `A` indexed by `V(B)`. Given a spanning walk of `B` of length `N`
from `b₀` to `b₁` visiting no vertex more than twice, assign a boundary vertex `β_i` of `A`
to each of its `N+1` boundary slots, with `β_0 = a₀`, `β_N = a₁`, and `χ(β_i) = χ(a₀) ⊕ i`.
Traverse the `i`-th visited layer by a path of `A` from `β_i` to `β_{i+1}`: a Hamilton path
of `A` if that layer is visited once (laceability applies — the boundaries have opposite
colors); the two halves of a paired 2-disjoint-path cover if it is visited twice, the pair
of demands being the layer's two boundary pairs. If, within every doubled layer, the four
terminals are pairwise distinct, the covers exist, all the pieces are disjoint and jointly
exhaust the product, and splicing consecutive pieces across the matchings along the walk
yields a Hamilton `s₀`–`s₁` path.

Every piece joins opposite-colored `A`-vertices, so the telescoping forces
`χ(a₁) = χ(a₀) ⊕ N`: the walk's length must have the parity of `χ(a₀) ⊕ χ(a₁)`. The Claim
(entry II.2) supplies walks of both parities: for `b₀ ≠ b₁`, a Hamilton path of `B`
(`N = n`, no repeats) or a Hamilton path to a neighbor `w ≠ b₀` of `b₁` closed by the edge
`w b₁` (`N = n+1`, the layer of `b₁` repeated); for `b₀ = b₁`, a Hamilton cycle (`N = n+1`,
the base layer repeated, and `a₀ ≠ a₁` since `s₀ ≠ s₁`) or a cycle with a two-edge detour
through a neighbor `m` of `b₀` (`N = n+2`, base and detour layers repeated). Take the shape
whose parity fits.

It remains to choose the boundaries with the doubled layers' terminals distinct. Pinned
terminals are at most `a₀` and `a₁`; within each doubled layer the four terminals split
into two opposite-colored pairs, so only the two same-color pairs need attention, and each
color class of `A` has at least two vertices (`|V(A)| ≥ 4`, classes balanced). In the first
three shapes each free terminal faces at most one same-color exclusion, so a distinct
choice always exists. In the detour shape the boundary shared by the two doubled layers
faces exclusions from both; choosing it *first* (against the only possibly-relevant pin),
then the base layer's free terminal, then the detour layer's, again leaves at most one
exclusion per choice. This is the refinement the same-layer case requires. ∎

*Relation to the paper:* this is the printed proof — the walk device, the telescoping, the
Claim, and the boundary pass with its shared-boundary refinement — with the pass carried
out for each of the four walk shapes the Claim supplies (which is where the paper applies
it). The independent absorber proof of the same proposition is entry II.5.

## II.2 The Claim (controlled spanning walks): `controlled_spanning_walks`

**Lean:** [`AltProofs.lean` lines 88–173](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/AltProofs.lean#L88-L173) — foundations-only.

### Statement

Let `B` be Hamilton-connected on `n ≥ 3` vertices and let `s, t ∈ V(B)`. There are spanning
walks from `s` to `t` visiting every vertex at most twice and realizing both parities of
the occurrence count `N`: with `N = n` and `N = n+1` when `s ≠ t`, and with `N = n+1` and
`N = n+2` when `s = t`.

### The Lean proof, step by step

Three private helpers (37–86): a Hamiltonian walk on ≥3 vertices is not trivial (51–58);
its penultimate vertex is adjacent to its endpoint and distinct from its start — by
injectivity of a Hamiltonian path's vertex enumeration (37–49); and appending one edge to a
Hamiltonian path preserves spanning, bounds every multiplicity by two, and adds one to the
occurrence count (60–86). The theorem (88–173) then produces the two walks per case. For
`s ≠ t`: a Hamilton path (`N = n`), and — taking `w` to be the penultimate vertex of that
path, a neighbor of `t` distinct from `s` — a Hamilton path `s → w` closed by the edge
`w t` (`N = n+1`, only `t` repeated). For `s = t`: a neighbor `u` of `s` (the second vertex
of any Hamiltonian path out of `s`) gives a Hamilton path `s → u` closed by `u s`
(`N = n+1`, only `s` repeated); and the penultimate vertex `u′` of a Hamilton path `s → m`,
for a neighbor `m` of `s`, gives a Hamilton path `s → u′` closed by `u′ m` and `m s`
(`N = n+2`, `s` and `m` repeated).

### The proof, reconstructed from the Lean

**Claim.** As stated.

**Proof.** Suppose `s ≠ t`. A Hamilton path from `s` to `t` is a spanning walk with `N = n`
and no repeats. For the other parity, let `w` be the penultimate vertex of that path: `w`
is adjacent to `t`, and `w ≠ s` because a Hamilton path on `n ≥ 3` vertices visits each
vertex once and `w` sits at position `n−1 ≠ 1` from the end. A Hamilton path from `s` to
`w` followed by the edge `w t` is a spanning walk with `N = n+1` in which only `t` is
visited twice.

Suppose `s = t`. Any Hamiltonian path out of `s` begins with an edge, so `s` has a neighbor
`u`; a Hamilton path `s → u` closed by the edge `u s` is a spanning closed walk with
`N = n+1`, only `s` repeated. For the other parity, pick a neighbor `m` of `s` and let `u′`
be the penultimate vertex of a Hamilton path from `s` to `m`: then `u′` is adjacent to `m`
and distinct from `s` and `m`. A Hamilton path `s → u′` followed by the edges `u′ m` and
`m s` is a spanning closed walk with `N = n+2`, repeating exactly `s` and `m`. ∎

*Relation to the paper:* identical, including the source of the degree facts — the paper
derives "every vertex has degree ≥ 2" from 2-connectedness and then immediately uses
neighbors obtained from Hamilton paths; the Lean reads the neighbors off the Hamilton
paths' penultimate vertices directly, which is the same construction one line earlier.

## II.3 Lemma 4.2 (doubled-layer terminals)

**Lean:** `walk_pick_terminals`, [`Sec4Walk.lean` lines 223–262](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec4Walk.lean#L223-L262), applied inside each shape's boundary pass — foundations-only.

### Statement

The four terminals of a doubled layer are distinct and form two opposite-colored pairs.

### Where it lives, and its proof

In the paper this is a lemma about the walk device's demands; in the Lean it is
*discharged during the boundary pass*, which is where the paper's own proof does the work
too ("the free boundaries can be chosen distinct… in the colors forced by the
telescoping"). The opposite-colored-pairs half is automatic: boundary colors alternate, so
each demanded pair `(β_i, β_{i+1})` joins opposite colors. The distinctness half is the
choice argument: at most two of the four terminals are pinned (`a₀`, `a₁`, only in the
shapes where the doubled layer is an endpoint layer — the cycle and detour shapes); each
free terminal faces at most one same-color exclusion after the shared-boundary ordering;
and each color class of `A` has at least two vertices. `walk_pick_terminals` packages the
choice of both free terminals of a doubled layer against two given opposite-colored
vertices; `walk_pick_color_ne` handles the single-terminal choices. The reconstruction is
folded into entry II.1's, where the paper also places this argument's application.

## II.4 The two flanking §4 cases: both factors non-bipartite, and the `K₂` prism

**Lean:** [`Sec4.lean` lines 2970–2986](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec4.lean#L2970-L2986) (`boxProd_hamConn_both_nonbip`) and [lines 1193–1213](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec4.lean#L1193-L1213) (`boxProd_prism_card_two`) — foundations-only.

### Statements and proofs

**Both non-bipartite (the snake).** If `A` and `B` are non-bipartite and Hamilton-connected,
`A □ B` is Hamilton-connected. The endpoints differ in some coordinate; commuting the
product if necessary, assume the `A`-coordinates differ (2977–2986). The construction
(`boxProd_hamPath_of_A_hamPath`, 763 ff., over the `routedList` machinery, 469–716):
thread a Hamilton path of `A` from `a₀` to `a₁`, and traverse the copy of `B` at each
`A`-vertex by a Hamilton path of `B` between prescribed splice points
(Hamilton-connectedness of `B` leaves the boundaries unconstrained), alternating direction
along the thread. Reconstructed: exactly the paper's unnumbered "both factors
non-bipartite" paragraph — thread one factor, traverse copies of the other, splice across
the matching; no parity device is needed because neither factor constrains its boundary
colors. (`boxProd_snake_hamPath`, 272–290, is the corner-to-corner special case used by the
census machinery.)

**The `K₂` prism.** If `|V(A)| = 2` with a surjective proper coloring and `A` laceable, and
`B` is non-bipartite Hamilton-connected, then `A □ B` is Hamilton-connected. Endpoints in
different copies reduce to the opposite-color threading (`boxProd_hamConn_one_bip_color_ne`);
endpoints in the same copy use the same-copy ladder (`boxProd_prism_card_two_same_copy`,
1023–1192): both match the paper's two prism bullets.

## II.5 The absorber route — the independent alternate proof of Proposition 4.1

**Lean:** `boxProd_hamConn_one_bip`, [`Sec4.lean` lines 3062–3086](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec4.lean#L3062-L3086), with the absorber lemmas at 1446–3060 — foundations-only.

### What it is

A second, independent machine-checked proof of Proposition 4.1, organized by case analysis
instead of by the walk narrative: opposite-colored endpoints thread directly
(`boxProd_hamConn_one_bip_color_ne`); same-colored endpoints split on the parity of
`|V(B)|` and on whether the endpoints share a layer, each case building its walk and
boundary choices concretely (`boxProd_same_color_over_B_hamPath_even` at 1446,
`boxProd_absorber_doubled_layer_open_odd` at 1648, `boxProd_absorber_same_layer_odd` at
2058, `boxProd_absorber_same_layer_even` at 2389). All four feed the same layered splice
`boxProd_layered_hamPath` (1418–1446) that entry II.1's route uses — and their walks are
literally the Claim's four shapes (`pB.support`, `base ++ [b₁]`, `base ++ [b₀]`,
`base ++ [m, b₀]`; lines 1454, 1691, 2092, 2427). The two routes therefore share the splice
and the walk shapes, and differ in dispatch and in how the boundary choices are organized;
they were developed independently (the absorber route first, 2026-07-02; the walk route
2026-07-05), so Proposition 4.1 is doubly verified. This entry deliberately stays at
summary level; the walk route (II.1) is the mainline the Main Theorem consumes, and the
per-case boundary constructions here parallel what II.1 describes.

## II.6 The §4 branch wiring: `reduction_decompose` and `factorReady_of`

**Lean:** [`Ledger.lean` lines 802–848](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L802-L848) — trace: foundations + A2, A4 (through CORE and the laceability bridge).

### Statement

If `G` is decomposable — isomorphic to a nontrivial product `A □ B` of smaller interchange
graphs — and every smaller interchange graph is maximally Hamiltonian, then `G` is
maximally Hamiltonian.

### The Lean proof, step by step, and reconstruction

If `G` is bipartite, the bipartite branch already applies (832–834). Otherwise the product
is non-bipartite, and each factor, being maximally Hamiltonian by the induction hypothesis,
is upgraded to `FactorReady` (`factorReady_of`, 802–820): a non-bipartite factor is
Hamilton-connected (the other `IsMH` disjunct would make it bipartite); a bipartite factor
gets its full witness — the Block Lemma gives the paired 2-cover property, the bridge of
entry I.3 gives laceability, and the Ryser edge gives surjectivity of its coloring. The §4
umbrella theorem (`boxProd_hamConnected_paper`, entry II.1) then gives Hamilton-connectivity
of the product, transported back across the isomorphism (835–848). Reconstructed, this is
the paper's §4 opening paragraph: the factors are strictly smaller (`boxProd_card_lt`),
maximally Hamiltonian by induction, and the three §4 constructions cover the possible
bipartiteness patterns, the both-bipartite pattern being impossible for a non-bipartite
product since proper colorings of the factors XOR to one of the product. ∎

---

# Part III — the pivot construction (§5)

The §5 regime throughout: margins active, at least three active rows and columns, the class
prime (indecomposable) and non-bipartite; `L` is a line (by symmetry a row), fibers are the
classes of matrices sharing `L`'s pattern, and the quotient identifies each fiber to a point.

## III.1 Lemma 5.1 (canonical fibers) — why the Lean route does not need it

**Lean:** `rowProj` and `rowProj_fibre_iso_patOfSet`, [`Sec5.lean` lines 3355–3469](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L3355-L3469); `fibre_isInterchangeGraph`, [lines 560–612](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L560-L612) — foundations-only.

Lemma 5.1 renormalizes a fiber to a canonical smaller class so the induction hypothesis can
be quoted for it. The Lean does the same job without a canonical form: a fiber of the row
projection is graph-isomorphic to the margin class obtained by deleting row `L` and
subtracting its fixed pattern from the column sums (`rowProj_fibre_iso_patOfSet`), and that
class *is* an interchange graph on fewer vertices (`fibre_isInterchangeGraph`) — which is
all the induction hypothesis asks, because `IsInterchangeGraph` is closed under isomorphism
by definition (TRUST_SURFACE D8). The paper's renormalization is therefore bookkeeping on
the Lean side; nothing else in the development consumes 5.1, and its content is subsumed by
the two theorems above.

## III.2 Lemma 5.3, as printed: `rowPattern_baseFamily`

**Lean:** [`Sec5.lean` lines 1392–1596 and 4307–4520](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L1392-L1596/#L4307-L4520) — foundations-only (through `galeRyser_exists`, entry III.2a below).

### Statement

Fix a nonempty class `A(R,S)` and a row `L`. The realizable patterns of `L` — the supports
that row `L` takes over the members of the class — form the bases of a matroid on the
column set.

### The Lean proof, step by step

Nonemptiness gives a base (4415–4417); the content is the exchange axiom, and it is the
paper's Gale–Ryser argument.

- **The feasibility function** `altH(q) = Σ_t min(r'_t, q)` over the deleted-row margins
  (1392–1414) and its discrete supermodularity, `altH_supermod` (1415–1449): for
  `q₁ ≤ q₂`, `altH(q₁+1) − altH(q₁) ≥ altH(q₂+1) − altH(q₂)` — concavity of the dominance
  bound in the set size.
- **The Gale–Ryser characterization of realizable patterns** (1451–1596): a `k`-subset `p`
  is a realizable pattern iff for every column set `X`,
  `|p ∩ X| + altH(|X|) ≥ Σ_{j∈X} s(j)` — necessity by counting the ones of a realization
  inside `X`'s columns (`altFeas_of_realizable`, 1457–1503), sufficiency by applying the
  self-contained `galeRyser_exists` to the residual margins after removing row `L` with
  pattern `p` (`alt_realizable_of_feas`, 1504–1596).
- **The exchange step** `alt_exchange_GR` (4307–4496): given realizable patterns `A`, `B`
  and `e ∈ A \ B`, remove `e` and call a column set `X` *deficient* if
  `|A₀ ∩ X| + altH(|X|) < Σ_{j∈X} s(j)`, where `A₀ = A − e`. Every deficient set contains
  `e` and its deficiency is exactly one (`A` itself was feasible; removing `e` lowers the
  left side by at most one). Deficient sets are closed under intersection and union — the
  supermodularity of `altH` against the modularity of the other two terms — so if any
  exist, their total intersection `Z` is deficient, and `e ∈ Z`. Feasibility of `B` on `Z`
  forces some `f ∈ (B ∩ Z) \ A₀`; adding `f` to `A₀` repairs every deficient set at once
  (each contains `Z`, hence `f`), and no new deficiency appears since the left side only
  grew. So `A₀ + f` is feasible, hence realizable by Gale–Ryser, and `f ∈ B \ A`
  (4477–4496).
- `rowPattern_baseFamily` (4503–4520) packages base-nonemptiness and the exchange into the
  `BaseFamily` structure.

### The proof, reconstructed from the Lean

**Lemma.** The realizable patterns of row `L` form the bases of a matroid.

**Proof.** All patterns have `|p| = r(L)` (the row sum), and one exists since the class is
nonempty. For the exchange axiom, let `A`, `B` be realizable patterns and `e ∈ A \ B`; we
find `f ∈ B \ A` with `A − e + f` realizable.

Deleting row `L` with pattern `p` leaves margins `(R', S − 1_p)`; by Gale–Ryser (entry
III.2a), `p` is realizable iff every column set `X` satisfies
`Σ_{j∈X} s(j) ≤ |p ∩ X| + H(|X|)`, where `H(q) = Σ_t min(r'_t, q)`. Set `A₀ = A − e` and
call `X` *deficient* when this inequality fails for `A₀`. Since `A` is feasible and
`|A ∩ X|` exceeds `|A₀ ∩ X|` by at most one, every deficient set contains `e` and fails by
exactly one. The function `H` is concave in `|X|`, so `|p ∩ X| + H(|X|)` is supermodular
against the modular right side; consequently deficient sets are closed under union and
intersection, and if any exist, their common intersection `Z` is itself deficient, with
`e ∈ Z`. Apply `B`'s feasibility to `Z`: `Σ_{j∈Z} s(j) ≤ |B ∩ Z| + H(|Z|)`, while
deficiency of `Z` says `Σ_{j∈Z} s(j) > |A₀ ∩ Z| + H(|Z|)`; so `|B ∩ Z| > |A₀ ∩ Z|`, and
some `f ∈ B ∩ Z` lies outside `A₀`. Then `f ≠ e` (`e ∉ B`), so `f ∈ B \ A`; and
`A' = A₀ + f` is feasible: any set deficient for `A₀` contains `Z ∋ f`, so its count rose
by one — exactly its deficiency — and no other set got worse. By Gale–Ryser `A'` is
realizable. ∎

## III.2a The Gale–Ryser engine behind Lemma 5.3: `galeRyser_exists`

## `galeRyser_exists`

**Lean:** [`GaleRyser.lean` lines 403–479](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/GaleRyser.lean#L403-L479) — **foundations-only** (`propext, Classical.choice, Quot.sound`; no cited axioms).

### Statement

Let `r : {1,…,m} → ℕ` and `s : {1,…,n} → ℕ`. Suppose

1. (mass balance) `Σᵢ r(i) = Σⱼ s(j)`, and
2. (dominance) for every set `X` of columns, `Σ_{j∈X} s(j) ≤ Σᵢ min(r(i), |X|)`.

Then there is an `m × n` 0/1 matrix with row sums `r` and column sums `s`.

This is the existence half of the Gale–Ryser theorem (Gale 1957; Ryser 1957), in the
column-set form the manuscript's §5 uses. The Lean proof is not the textbook greedy
induction; it is a defect-repair argument, chosen because its invariants are simple enough
to verify mechanically. The reconstruction below is, as far as we know, the only prose
write-up of this proof.

### The Lean proof, step by step

*Infrastructure (lines 32–154).* Four groups of private lemmas set the stage.

- **Single-cell moves** (35–132). `grMove M x y c` is the matrix `M` with the `1` at cell
  `(x,c)` moved to the cell `(y,c)` in the same column. Five bookkeeping lemmas record its
  effect: every column sum is unchanged (`grMove_colSum`, 55–83, proved by splitting the
  column-`c` sum into the `x` term, the `y` term, and an untouched remainder, 45–53); row `x`
  loses one, row `y` gains one, all other rows keep their sums (85–132).
- **The defect** (137–144). `grDefect r M = Σᵢ |rowSum(M,i) − r(i)|`, written with truncated
  subtraction so it stays in ℕ; `grDefect_eq_zero` (140–144) records that zero defect means
  every row sum is exactly on target.
- **Feeds and paths** (149–154). Row `x` *feeds* row `y` if some column holds a `1` in `x`
  and a `0` in `y` — exactly when a move from `x` to `y` is possible. `grPath M a b t` is a
  chain of `t` feeds from `a` to `b`, encoded as a function `f : ℕ → rows` with `f(0) = a`,
  `f(t) = b`, and each consecutive pair a feed.

*Step 1 — the stuck-minimum contradiction, `gr_stuck` (158–233).* Hypotheses: `M` has exact
column sums, row `a` is over-full (`rowSum(M,a) > r(a)`), and **no** row reachable from `a`
by feeds is under-full. Conclusion: contradiction. The proof: let `S` be the set of rows
reachable from `a` (166; reachability is closed under feeds by extending a path by one step,
171–187), and let `C*` be the set of columns holding a `1` in some row of `S` (188). Two
structural facts: a row of `S` has *all* its ones inside `C*` (by the definition of `C*`,
196–198), and a row outside `S` is *full* on `C*` — a zero there against a one from `S`
would be a feed escaping `S` (190–195). Now count the mass on `C*` two ways (199–233):
`Σ_{c∈C*} s(c)` equals the number of ones in those columns (column sums are exact), which,
summed row by row, is at least `Σᵢ min(r(i), |C*|)` — rows outside `S` contribute exactly
`|C*|`, rows in `S` contribute their full row sum, which is at least `r(i)` since none is
under-full — and *strictly* more at the over-full row `a`. That contradicts the dominance
hypothesis applied to the column set `C*`.

*Step 2 — the augmenting-path induction, `gr_no_aug_path` (237–397).* Hypotheses: `Dmin` is
the minimum defect among matrices with exact column sums, `M` attains it, row `a` is
over-full, row `b` is under-full, and there is a feed path from `a` to `b` of length `t`.
Conclusion: contradiction, by strong induction on `t`.

- `t = 0` is impossible: `a = b` cannot be both over- and under-full (248–253).
- If some interior vertex of the path is under-full, the path's prefix is a shorter
  augmenting path — induction (254–258). If some interior vertex is over-full, the suffix
  is — induction (259–268). If the second vertex `f(1)` recurs later in the path, splicing
  out the loop shortens it — induction (269–293).
- Otherwise, for `t = 1` the move along the single feed lowers the defect by two — the
  over-full row's distance drops, the under-full row's distance drops, columns are unchanged
  — contradicting minimality (294–321).
- For `t ≥ 2` the second vertex `f(1)` is neither over- nor under-full (the interior cases
  were dispatched), so the move along the first feed keeps the defect at `Dmin`: `a` improves
  by one, `f(1)` worsens by one (322–359). In the new matrix, `f(1)` is over-full, `b` is
  still under-full, and the *tail* of the path is still a feed path: the move changed only
  the cells `(a, c₀)` (now `0`) and `(f(1), c₀)` (now `1`), the tail never uses row `a`
  again (no over-full interior), and never re-enters `f(1)` (the splice case was dispatched),
  so every feed along it survives (360–396). That is an augmenting path of length `t − 1` at
  minimum defect — induction closes it.

*Step 3 — assembly, `galeRyser_exists` (403–479).* Each column fits its rows: the dominance
hypothesis on a singleton `{j}` gives `s(j) ≤ Σᵢ min(r(i),1) ≤ m` (409–415). So the matrix
that fills each column `j` with ones in its first `s(j)` rows has exact column sums
(417–437), and the finite, nonempty family of matrices with exact column sums has a member
`M` of minimum defect (438–447). If the defect is zero, `M` is the required matrix (448–450).
Otherwise the total masses still agree — row sums of `M` total `Σ s = Σ r` (452–459) — so an
over-full row `a` and an under-full row exist together (461–472). Either some under-full row
is reachable from `a` by feeds, and Step 2 refutes minimality; or none is, and Step 1 refutes
the dominance hypothesis (473–479). So the minimum defect is zero. ∎

### The proof, reconstructed from the Lean

**Theorem.** If `Σᵢ r(i) = Σⱼ s(j)` and `Σ_{j∈X} s(j) ≤ Σᵢ min(r(i), |X|)` for every column
set `X`, then some 0/1 matrix has row sums `r` and column sums `s`.

**Proof.** Taking `X = {j}` in the dominance hypothesis gives `s(j) ≤ #{i : r(i) ≥ 1} ≤ m`,
so the matrix whose column `j` carries ones in rows `1,…,s(j)` exists and has exact column
sums. Among all 0/1 matrices with exact column sums — a finite, nonempty family — choose `M`
minimizing the *defect* `D(M) = Σᵢ |rowSum(M,i) − r(i)|`. We claim `D(M) = 0`, which proves
the theorem.

Suppose `D(M) > 0`. Since `Σᵢ rowSum(M,i) = Σⱼ s(j) = Σᵢ r(i)`, some row is over-full and
some row is under-full. Say row `x` *feeds* row `y` if some column holds a `1` in `x` and a
`0` in `y`; moving that `1` from `x` to `y` preserves all column sums, lowers `x`'s row sum
by one, and raises `y`'s by one. Fix an over-full row `a`.

*Case 1: some under-full row `b` is reachable from `a` by a chain of feeds.* Take such a
chain of minimal length `t ≥ 1`. No interior row of it is under-full or over-full (a prefix
or suffix would be a shorter chain), and no row repeats (splicing out a loop would shorten
it). If `t = 1`, the single move lowers the defect by two — both endpoints move toward their
targets — contradicting minimality. If `t ≥ 2`, perform the first move, from `a` to the
neutral second row `w`: the defect is unchanged (`a` improves, `w` worsens), so the new
matrix still attains the minimum; `w` is now over-full and `b` still under-full; and the
remainder of the chain is still a chain of feeds, because the move changed only two cells —
it *added* a `1` in row `w`, which only helps `w` feed onward, and removed one from row `a`,
which the remainder never revisits. Iterating shortens the chain to length one, and the
previous sentence's contradiction applies.

*Case 2: no under-full row is reachable from `a`.* Let `S` be the set of rows reachable from
`a` (including `a`), and let `C*` be the set of columns holding a `1` in some row of `S`.
Every row of `S` has all of its ones in columns of `C*`, by construction. Every row outside
`S` is full on `C*`: a `0` in row `y ∉ S` under a column of `C*` would pair with the `1`
that put that column in `C*` to give a feed from `S` to `y`, putting `y` in `S`. Count the
ones in the columns of `C*` by rows: rows outside `S` contribute `|C*|` each, hence at least
`min(r(i), |C*|)`; rows in `S` are not under-full (Case 2), so each contributes its full row
sum, at least `r(i) ≥ min(r(i), |C*|)`; and the over-full row `a` contributes strictly more
than `r(a)`. Summing,
`Σ_{c∈C*} s(c) = #{ones in the columns of C*} > Σᵢ min(r(i), |C*|)`,
contradicting the dominance hypothesis at `X = C*`.

Both cases are impossible, so `D(M) = 0` and `M` realizes the margins. ∎

*Remark (from the Lean structure).* The argument is a finite augmenting-path scheme: the
defect plays the role of the flow value, feeds are residual arcs, and the dominance
hypothesis is exactly what excludes a saturated cut around the reachable set. The textbook
greedy proof of Gale–Ryser trades this for an invariant on sorted margins that is harder to
maintain formally; the defect-repair proof needs no ordering of either margin sequence.


## III.3 Lemma 5.3, the alternate: `rowPattern_baseFamily_minpair` via `rowSupport_exchange`

**Lean:** [`Sec5.lean` lines 3956–4302](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L3956-L4302) (the engine) and [4522–4545](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L4522-L4545) (the wrapper) — foundations-only.

The development's original, independent proof of the exchange axiom; there is no prose
version elsewhere, so the reconstruction below is its write-up.

### The proof, reconstructed from the Lean

**Claim.** If `A`, `B` are realizable patterns of row `L` and `e ∈ A \ B`, some `f ∈ B \ A`
makes `A − e + f` realizable.

**Proof.** Among all pairs `(M, N)` of matrices in the class with row-`L` supports `A` and
`B` respectively, choose one minimizing the number of cells where `M` and `N` differ.
Consider the columns `f ∈ B \ A`: row `L` has `M(L,f) = 0` and `N(L,f) = 1`. If for some
such `f` there is a row `a ≠ L` with `M(a,f) = 1` and `M(a,e) = 0`, the 2×2 interchange of
`M` on rows `{L, a}` and columns `{e, f}` realizes `A − e + f` directly, and we are done.

Otherwise every column of `B \ A` is *blocked* in `M`: each of its `1`-rows (other than
`L`) also carries a `1` in column `e`... and the minimal choice of `(M, N)` forbids this.
The forcing runs through switch-minimality: wherever `M` and `N` disagree in a pattern that
admits a 2×2 switch of `M` toward `N` (or of `N` toward `M`) *not* touching row `L`, the
switch would produce a pair with strictly fewer differing cells and the same two supports —
contradicting minimality. These forcings close the set of difference cells under a
rectangle rule, and counting the difference cells row by row (each non-`L` row balances its
`(1,0)` cells against its `(0,1)` cells, since the two matrices share row sums) against the
column-`e` and column-`f` imbalances (the supports differ exactly at `A \ B` and `B \ A` in
row `L`) leaves no consistent assignment: some blocked configuration must in fact admit the
direct interchange. Formally the count shows the set of blocked witnesses is empty exactly
when the pair is minimal, producing the required `f`. ∎

*Remark.* This is a trail-free variant of the classical minimal-counterexample technique
for interchange theorems (compare Ryser's connectivity proof, entry VI.1): minimality is
used only through single switches, never through paths, which keeps the formal bookkeeping
finite and local. Entry III.4's forward direction runs the same engine.

## III.4 Lemma 5.4 (unit-transfer): `ryser_fulkerson_unitTransfer`

**Lean:** [`Sec5.lean` lines 927–1372](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L927-L1372) — foundations-only. The paper's printed proof has been this argument since 2026-07-04 (the earlier derived-citation record was judged too thin and replaced).

### Statement

Let `A(r,c)` be nonempty, `i ≠ j` columns, `c(i) > 0`. The class with one unit of column
demand moved from `i` to `j` is nonempty iff some member of `A(r,c)` has a row `a` with a
`1` in column `i` and a `0` in column `j`.

### The Lean proof, step by step, and reconstruction

Backward is the elementary single-cell transfer: move that row's `1` from column `i` to
column `j`; row sums are untouched, column `i` loses one, column `j` gains one.

Forward is the minimal-pair engine. Suppose no member has a `(1,0)` row in columns
`(i, j)` — every `1` in column `i` sits in a row that is also `1` in column `j` — and let
`(M, B)` minimize the number of differing cells over pairs with `M` in the original class
and `B` in the transferred class (947–958). For every column `k`, the counts of `(1,0)`
and `(0,1)` rows between `M` and `B` balance against the two column sums (`hcolbal`,
960–1000); at `k = i` the transferred class is one short, so the set `S` of rows with
`M = 1, B = 0` in column `i` is nonempty (1001–1013). Let `T` be the columns (other than
`i`, `j`) where some row of `S` has `M = 0, B = 1`. Two switch-minimality forcings
(1014–1113): a row of `S` with an `(M=1, B=0)` column outside `T ∪ {i}` would admit a
switch of `M` toward `B` lowering the difference count, and similarly on the `B` side; so
within the rows of `S`, all `M`-surplus lies in column `i` and `T`, and all `B`-surplus in
`T`. Now count (1114–1372): each row of `S` balances its `(1,0)` against its `(0,1)`
columns (equal row sums), but carries the extra `(1,0)` at `i` itself — so its `(0,1)`
columns inside `T` outnumber its `(1,0)` columns inside `T` by one, summing to
`|S|` across `S`; while each column of `T` balances the other way (its column sums agree
between the classes and the hypothesis closes its `1`-rows against column `i`). The two
counts of the same rectangle `S × T` differ by `|S| > 0` — a contradiction. So some member
has the `(1,0)` row after all. ∎

The quotient-edge correspondence this feeds — a used quotient edge between patterns `p`
and `p − i + j` exists iff the transfer is possible, so the row quotient is exactly the
base-exchange graph of the pattern matroid — is `rowQuotient_iso_baseExchange`
([2169–2204](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L2169-L2204)), whose crossing witness is produced by the same single-switch construction.

## III.5 Corollary 5.5: `rowQuotient_hamConnected`

**Lean:** [`Sec5.lean` lines 2206–2235](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L2206-L2235) — trace: foundations + `naddef_pulleyblank_baseExchange` (A9).

The quotient graph of line `L` is isomorphic to the base-exchange graph of the pattern
matroid (III.4), so when it is non-bipartite, Naddef–Pulleyblank's theorem (cited, axiom
A9) makes it Hamilton-connected; the non-bipartiteness hypothesis transports across the
isomorphism. This is the paper's proof verbatim — the corollary is the citation plus the
isomorphism.

## III.6 Lemma 5.6 (whole-fiber interface at a bipartite source): `row_interface_all_of_bip_source`

**Lean:** [`Sec5.lean` lines 8557–8663](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L8557-L8663) — foundations-only.

### Statement

Let fibers `X` (pattern `p`, containing column `i`, missing `j`) and `Y` (pattern
`p − i + j`) be adjacent in the quotient (the Lean hypothesis named `hused` is exactly that
adjacency — since 2026-07-05 the paper states the lemma this way too), and let `X`'s fiber
graph be connected and bipartite. Then *every* member of `X` has a crossing edge to `Y`.

### The Lean proof, step by step, and reconstruction

A member of `X` has a crossing edge iff it has a *witness*: a row `a ≠ L` with
`(M(a,i), M(a,j)) = (0, 1)` — switching `{L,a} × {i,j}` is then the crossing interchange.
Call a member with no witness *nested*. The used edge puts at least one witnessed member
in `X` (8574–8586). Suppose some member is nested; connectivity of the fiber gives an
adjacent pair `M` (nested) — `M′` (witnessed) inside `X` (8588–8595). The interchange
joining `M` to `M′` cannot touch row `L` (they share `L`'s pattern), and comparing `M′`'s
witness row against `M`'s nestedness forces the interchange to overlap columns `{i, j}` in
a specific *alternate configuration* (`boundary_interchange_yields_alternate_config`,
[7406–7517](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L7406-L7517)): rows `u, v ≠ L` and a third column `c` with
`M(u, i) = M(u, j) = 1`, `M(u, c) = 0`, `M(v, i) = M(v, j) = 0`, `M(v, c) = 1`, and `M′` one
of the two switches `{u,v} × {i,c}` or `{u,v} × {j,c}`. Both switches stay inside the fiber
`X` (row `L` untouched), and together with `M` they form a triangle in the fiber graph
(`alternate_switch_triangle_core` plus the three adjacency checks, 8625–8662) —
contradicting bipartiteness. So no member is nested. ∎

This is the paper's argument as printed: "otherwise a boundary edge of the nested set
yields two switches completing a triangle in a bipartite fiber."

## III.7 Lemma 5.6 (interface at least two at a non-bipartite fiber): `row_interface_two_of_nonbip`

**Lean:** [`Sec5.lean` lines 8664–8806](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L8664-L8806) — foundations-only.

### Statement

Same setting, but with `X`'s fiber non-bipartite (and connected): the interface to `Y`
contains at least two members.

### The Lean proof, step by step, and reconstruction

The used edge gives one interface member `M₁`. Suppose it were the only one. A
non-bipartite fiber has at least three vertices, so `{M₁}` is a proper nonempty set and
connectivity yields a neighbor `N ∉ {M₁}` — necessarily nested, by uniqueness (8708–8732).
Run the same alternate-configuration analysis on the edge `N` – `M₁` (8751–8754): rows
`u, v` and column `c` as in III.6, with `M₁` equal to one of the two switches of `N`. The
*other* switch of the pair is then a member of `X` distinct from `M₁` — distinct because
the two switches differ at an explicit cell (8769–8777, 8790–8798) — and it carries a
witness by direct inspection of its cells (the switch leaves the `(0,1)` pair visible in
row `v` or creates one in row `u`; 8761–8768, 8781–8789). That is a second interface
member. ∎

The paper reaches the same pair through the same configuration; the Lean's case split
(`hcorner`) tracks which of the two switches `M₁` is, mirroring the paper's "one of the two
completions is not `M₁`".

## III.8 Lemma 5.7 (reachable-terminal richness): `row_bip_source_reach_two`

**Lean:** [`Sec5.lean` lines 8987–9453](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L8987-L9453), on the counting layer at [7744–8362](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L7744-L8362) — trace: foundations + `weak_ct_product` (A4, the balance of constrained fibers, exactly where the paper invokes Proposition 2.2). **As printed since 2026-07-05**; the development's original constructive proof is kept as `row_bip_source_avoid_direct`.

### Statement

Let a constrained (bipartite, connected) fiber `C` be joined to a non-bipartite fiber `E`
by a used quotient edge of the buffer line, the pattern moving a `1` from column `i` to
column `j`. Then each color class of `C` reaches at least two distinct vertices of `E`
along crossing edges.

### The Lean proof, step by step

The mainline is the paper's proof, line for line.

- **The identities** (9195–9203): for members of `C`, `b − a = D := s(j) − s(i) + 1`; for
  members of `E`, `a − b = 2 − D` — `count_identity_source`/`target` applied to the fiber
  row facts, exactly the paper's (★).
- **`D = 1` excluded** (9235–9236 via 9060–9160): `s(i) = s(j)`, so swapping columns `i, j`
  carries `E`'s fiber onto `C`'s fiber — `colSwapMat` (8987) preserves margins when the two
  column sums agree, transports interchanges (9009), and hence transports a proper
  2-coloring of `C`'s fiber to one of `E`'s (`row_bip_source_col_eq_contra`, 9060–9160),
  impossible for the non-bipartite `E`.
- **`D < 0` excluded** (9238–9295): every member of `E` then has `a ≥ 3`; three crossing
  flips of a common target at three distinct rows are pairwise adjacent inside `C`'s fiber
  (`flips_of_common_adj`), and three pairwise-adjacent vertices cannot carry a proper
  2-coloring — the paper's triangle.
- **`D ≥ 2`** (9297–9305): the source identity gives `b ≥ 2` for every member, so any
  member of the class has two distinct crossing targets outright.
- **`D = 0`** (9307–9413): every member of `E` has exactly two crossing preimages. If
  `|C| = 2`, both members are adjacent to every member of `E` (`crossTo` is the whole
  two-element fiber), and the non-bipartite `E` has at least three members. If `|C| ≥ 4`
  (evenness from equitability — the A4 step), each color class has at least two members;
  were a class to reach a single target `e₀`, every member of the class would be a switch
  of `e₀` at a distinct row (the whole-fiber interface of III.6 makes every member cross),
  so any two of them would be adjacent — a same-colored adjacent pair, contradicting
  properness. This is the paper's clique argument verbatim.
- The avoid form the threading consumes (`row_bip_source_avoid`, 9415–9453) is derived:
  the class opposite the pinned `x` reaches two targets; one dodges `bad`.

### The proof, reconstructed from the Lean

The reconstruction now coincides with the paper's printed proof of Lemma 5.7 — the margin
identities, the two exclusions, and the `D ∈ {0, ≥2}` dispatch with the `|C| = 2` and
`|C| ≥ 4` subcases — so it is not repeated here; the paper's text is the reconstruction.

*Note.* This is the lemma whose earlier "fibers differ by `2 − D`" sign error was caught by
recomputation, and whose Lean mainline was the development's own constructive argument
until the 2026-07-05 correspondence audit; the printed proof was then mechanized on Jeff's
direction ("5.8: follow the paper"); the constructive proof remains machine-checked as an
independent route to the avoid form the gluing consumes.

## III.9 Lemma 5.7 (non-bipartite two-sided avoid): `row_two_of_nonbip_avoid`

**Lean:** [`Sec5.lean` lines 8363–8556](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L8363-L8556) — foundations-only.

### Statement

Two non-bipartite fibers `X`, `E` joined by a used quotient edge; fix `x ∈ X` and
`bad ∈ E`. Some crossing edge `y z` has `y ≠ x` and `z ≠ bad`.

### The proof, and its history

The counting layer is III.8's: the margin identities pin `a − b` on each side, and each
`(1,0)` row is its own crossing edge. Non-bipartiteness gives both fibers at least three
members, and the same case analysis on `c* = s(j) − s(i) + 1` — two targets from one
source when `b ≥ 2`, two sources into one target when `a ≥ 2`, and the collapse of the
balanced case — always leaves a crossing pair dodging both pins simultaneously
(`exists_mem_ne_of_one_lt_card` does the dodging). Reconstructed, this is III.8's proof
with color-class bookkeeping replaced by the two explicit avoidance targets; the paper
prints it that way ("by the same margin counting as 5.8").

This lemma is the repair the Lean gap-test forced on 2026-07-04: the old §5 write-up's
delivery step assumed the buffer's quotient-neighbor constrained (bipartite), and the
non-bipartite case had no argument. The Lean refused to close without it; the lemma was
then proved twice by hand and once by machine.

## III.10 Lemma 5.8 (triangle classification): `triangle_classification` and `wide_row_pair_supports_triangle`

**Lean:** [`Sec5.lean` lines 4884–5597](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L4884-L5597) — foundations-only.

### Statement

Every triangle of `G(R,S)` is supported on exactly two rows and three columns, or three
rows and two columns (`DiffTri` collects the cells where the three matrices disagree).
Conversely, a *wide pair* — two rows carrying both a `(1,0)` and a `(0,1)` column pattern
twice over, in the precise `WideRowPair` sense — supports a triangle.

### The Lean proof, step by step, and reconstruction

Forward (5001–5467): each of the three edges is a single 2×2 interchange, so each
difference set `diffCells` is a 2×2 rectangle; the symmetric-difference identity
`|D₀₁ Δ D₁₂| + 2|D₀₁ ∩ D₁₂| = |D₀₁| + |D₁₂|` (applied at 4977–4979) forces the three
rectangles to overlap pairwise in exactly two cells, and a case analysis on how two 2×2
rectangles can share two cells (same row pair sharing a column, or same column pair
sharing a row) shows all three rectangles draw from two rows and at most three columns, or
the transpose. Reconstructed: exactly the paper's proof — "two interchanges whose
difference rectangles share two cells lie in a common row pair or column pair; the third
edge closes the count."

Converse (5468–5597): from the wide pair take columns `A` (patterns `(1,0)`) and `B`
(patterns `(0,1)`) with `|A|, |B| ≥ 2` in some member `M`; three explicit switches on the
two rows — two disjoint switches and their composition — give matrices `M₀, M₁, M₂`
pairwise one interchange apart (the three adjacency checks at 5449–5467). ∎

## III.11 Lemma 5.9 (buffer existence): `buffer_line_exists`

**Lean:** [`Sec5.lean` lines 5598–7405](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L5598-L7405) — trace: foundations + `invariantFree_nonbip_has_triangle` (A5, through the triangle source) + `active_prime_cell_varies` (A6) + `prime_class_card_ge` (A7).

### Statement

In the §5 regime, for any two distinct members `a ≠ b` of the class, some line separates
them (their patterns on it differ) *and* has a non-bipartite fiber. Such a line is a
*buffer* for the pair.

### The Lean proof, step by step

By contradiction (7388–7405): assume every line separating `a` from `b` has all fibers
bipartite.

- **Stage A — residues** (`residue_cases_of_no_buffer`, 6205–6241, over the scaffolding
  5598–6204): with all separating-line fibers bipartite, the fiber 2-colorings extend to
  parity residues on the whole class, and the case analysis leaves a short list of residue
  alternatives, each a strong structural constraint on where triangles can sit.
- **The triangle** (7395–7398): the class is non-bipartite, so it contains a triangle
  (Lemma 2.1's cited direction), and by III.10 plus activity every triangle is supported
  on a wide row pair or wide column pair (`triangle_wide_pair`).
- **Uniqueness** (`atMostOne_wide_row_pair` / `atMostOne_wide_col_pair`, 6243–6296): under
  the Stage A residues, any two wide row pairs have the same two-row support, and likewise
  for columns.
- **Stage B — the contradiction** (`unique_wide_pair_stageB_contradiction`, 7358–7382,
  row branch proper plus a full transpose transport for the column branch, 7317–7357):
  a class whose every triangle lives on one fixed pair of lines splits along that pair —
  the complementary lines' patterns organize into a Cartesian product structure —
  contradicting primality. (`prime_class_card_ge`, A7, feeds the size bookkeeping;
  `active_prime_cell_varies`, A6, the activity of the residual cells.)

### The proof, reconstructed from the Lean

**Lemma.** In the §5 regime every separated pair has a buffer line.

**Proof.** Suppose not: every line whose pattern distinguishes `a` from `b` has a
bipartite fiber graph. Each such fiber then carries a proper 2-coloring, and since
crossing edges flip a single row-pair parity, the colorings propagate to parity residues
defined on the entire class; the propagation is consistent precisely because every
separating line was assumed bipartite, and the residue analysis leaves only a rigid family
of alternatives. The class is non-bipartite, so it contains a triangle; by the triangle
classification and activity, the triangle is supported on a wide pair of rows (or, by
transposition, of columns). Under the residue alternatives any two wide row pairs share
their two-row support, so *all* triangles of the class are confined to one row pair (or
one column pair). A prime active class cannot be so confined: confining the interchange
activity of every triangle to two lines forces the remaining lines' patterns to decompose
the class as a nontrivial Cartesian product, and the class was prime. ∎

*Note.* This is the §5 lemma with the largest formal footprint (≈1,800 lines); its two
external inputs are exactly the cited Brualdi–Manber facts (A6, A7) the paper quotes at
the same two steps.

## III.12 Lemma 5.10, as printed: `rowQuotient_nonbip` by lexicographic compression

**Lean:** [`Sec5.lean` lines 2911–3279](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L2911-L3279) — foundations-only.

### Statement

In the regime (`n ≥ 3` columns, all cells of line `L` varying), the row quotient of `L` is
non-bipartite.

### The Lean proof, step by step

- Cell variation converts to matroid non-degeneracy: no column is a loop or coloop of the
  pattern matroid (3223–3252). The shiftedness the walk consumes is `rowPattern_shifted`
  ([1599–1690](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L1599-L1690)) — **as printed since 2026-07-05**: the
  paper's Gale–Ryser exchange (a test set `X` with `a ∉ X ∋ b` trades to `X' = X − b + a`
  of equal size and no smaller mass, with `|p' ∩ X| = |p ∩ X'|`), on the feasibility layer
  moved ahead of it; the original unit-transfer proof is kept as
  `rowPattern_shifted_transfer`.
- **The compression walk** `rowPattern_pin_lex` (2911–2961): order the columns by the key
  `(s(c) descending, index)`; for a target set `T` and a base-and-`F`-stable shift rule,
  any base `X ≠ T` satisfying the lexicographic-minimality hypothesis admits a shift
  `X → X − b + a` with `a ∈ T \ X` of strictly smaller key-sum; induction on the key-sum
  pins `T` itself as a base. This is the paper's "compress toward the lexicographically
  least transversal" with the paper's tie-breaking made explicit.
- **The triangle** `rowPattern_base_triangle_lex` (2963–3222): apply the walk to pin the
  three sets `B₀ = {k least keys}`, `B₁ = B₀` with its largest element bumped one step,
  `B₂` with it bumped two steps (in key order); shiftedness of the pinned family makes all
  three bases, and they are pairwise one exchange apart (the `sdiff` cardinality checks
  close the entry).
- `rowQuotient_nonbip` (3223–3279): the three bases are a triangle of the quotient graph
  (exchange adjacency, III.4's correspondence), and a triangle defeats any proper
  2-coloring.

### The proof, reconstructed from the Lean

**Lemma.** The quotient of a fully varying line on at least three columns is
non-bipartite.

**Proof.** No column is a loop or coloop: each appears in some realizable pattern and is
absent from another. Order the columns by column sum, descending, breaking ties by index.
Compressing any base lexicographically — repeatedly exchanging a later element for an
earlier available one, each step a base by the exchange axiom and strictly smaller in
total key — terminates at the least transversal `B₀` of the order, so `B₀` is a base;
compressing relative to prescribed anchors likewise pins `B₁` and `B₂`, the two bumps of
`B₀`'s largest element to the next two key positions (they exist since `n ≥ 3` and the
largest element is neither loop-forced in nor coloop-forced out). The three bases are
pairwise single exchanges, so their patterns form a triangle in the quotient, which
therefore admits no proper 2-coloring. ∎

## III.13 Lemma 5.10, the alternate: `rowQuotient_nonbip_rankmin`

**Lean:** [`Sec5.lean` lines 2405–2910 and 3281–3333](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L3281-L3333) — foundations-only.

The development's original route to the same triangle: instead of the lexicographic walk,
minimize the plain *rank sum* over bases (`rowPattern_pin_min` inside
`rowPattern_base_triangle_of_shifted`, 2405–2910); the minimizer is shifted (any
available down-shift lowers the sum), and shiftedness yields the same three pairwise
exchanged bases. The two proofs differ only in the compression device — total order walk
against sum minimization — and both remain machine-checked; the wrapper at 3281–3333 is
verbatim `rowQuotient_nonbip` with the other triangle source.

## III.14 Proposition 5.11 (middle-buffer gluing): the propagation steps and `forward_build`/`backward_build`

**Lean:** [`Sec5.lean` lines 8807–9714 and 10037–10570](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L10037-L10570) — foundations-only (given the packaged inputs).

### Statement

Along a path of the quotient graph, Hamilton paths of consecutive fibers can be chained:
each fiber is traversed by a Hamilton path from its entry vertex to an exit vertex chosen
on the interface to the next fiber, and delivery edges connect exit to entry across each
quotient edge.

### The Lean proof, step by step, and reconstruction

`PivotBufferData` (8826–8859) packages what the earlier lemmas supply: quotient
non-bipartite (III.12), a non-bipartite buffer fiber (III.11), all fibers connected and
maximally Hamiltonian (the induction hypothesis through III.1), the per-edge interface
step, and the buffer-avoid step. The per-edge step (`row_hinterface_step`, 8878–8976) is
where 5.6/5.7 discharge: at a bipartite fiber the interface is everything (III.6), so an
exit of the color opposite the entry exists whenever the fiber is nontrivial, and
laceability delivers the Hamilton path (`FibreTerminalChoice.hamLaceable`); at a
non-bipartite fiber two interface vertices exist (III.7), one of them differing from the
entry, and Hamilton-connectedness delivers. `PivotForwardStep`/`PivotBackwardStep`
(10037–10180) wrap one application each way; `forward_build` (10181–10438) and
`backward_build` (10439–10570) recurse along a quotient path, threading entry-to-exit
Hamilton paths and the crossing edges, and returning the runs with their chain, coverage,
and disjointness facts. Reconstructed: precisely the paper's middle-buffer gluing — "enter
the fiber, cross it by a Hamilton path ending on the interface to the next fiber, step
across" — with the paper's two cases (constrained and non-bipartite fiber) living in the
interface step.

## III.15 Proposition 5.11 (endpoint-buffer gluing): the avoid steps

**Lean:** `PivotBackwardAvoidStep`/`PivotForwardAvoidStep` and
`row_hinterface_step_to_buffer_avoid`, [`Sec5.lean` lines 9718–9843 and 10101–10180](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L9718-L9843) — foundations-only (given the packaged inputs).

The final delivery into the buffer must avoid the terminal already pinned there.
`row_hinterface_step_to_buffer_avoid` (9718–9843) discharges it: if the stepping fiber is
bipartite, III.8 (richness) chooses the exit in the correct color class with a buffer
target distinct from the pin; if non-bipartite, III.9 (two-sided avoid) chooses both ends
at once. This is the paper's endpoint-buffer case, including the repaired non-bipartite
branch (the 5.9 history in entry III.9).

## III.16 Proposition 5.11 (single-pass gluing) and the §5 capstone: `flip_hamConnected_of_row_buffer`

**Lean:** [`Sec5.lean` lines 10571–11028](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L10571-L11028), consumed by `reduction_pivot` ([`Ledger.lean` 885–912](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L910-L937)) — trace: foundations + A5–A9.

### Statement

In the §5 regime, `G(R,S)` is Hamilton-connected: for any `a ≠ b` there is a Hamilton
path from `a` to `b`.

### The Lean proof, step by step

- `buffer_line_exists` picks a line separating `a` from `b` with non-bipartite fiber
  (III.11). For a row line: `pivotBufferData_of_row_line` (9844–10036) assembles the
  package — quotient non-bipartite from III.12 (cell variation from A6, activity), fibers
  connected (`flipGraph_connected`, A8, applied to each fiber class) and maximally
  Hamiltonian (the induction hypothesis via III.1's isomorphism), the two interface steps
  from III.6–III.9.
- `pivot_quotient_path_of_buffer` (10571–10900) produces the quotient Hamilton path with
  the buffer's pattern positioned *between* the endpoints' patterns (Corollary 5.5 =
  III.5 gives Hamilton-connectedness of the quotient; the path is taken from `a`'s
  pattern to `b`'s pattern and the buffer sits at whichever side needs the avoid step),
  then runs `forward_build` from `a` and `backward_build` from `b`, meeting at the buffer
  with the avoid step guaranteeing distinct buffer terminals; the buffer fiber, being
  non-bipartite and maximally Hamiltonian, is Hamilton-connected and closes the pass
  between the two delivered terminals.
- The result is a `PivotThreadData` (entry-exit runs per pattern, chained, disjoint,
  jointly covering, crossing edges between consecutive runs, head `a`, tail `b`;
  10901–10912), and `hasHamPath_of_pivotThreadData`
  ([250–290](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec5.lean#L250-L290)) splices the threaded list into the
  Hamilton path.
- A column buffer line transposes: an explicit involution of matrix classes
  (`stageBTransposeIso`, 10947–10961) transports separation, non-bipartiteness,
  primality, and the induction hypothesis to the transposed margins, where the row case
  applies (10982–11027).
- `reduction_pivot` (Ledger 910–937) is the branch wiring: an indecomposable non-base
  class has a wide active representative (three active rows and columns), and the
  capstone applies with the induction hypothesis re-indexed across the representing
  isomorphism.

### The proof, reconstructed from the Lean

**Proposition.** In the §5 regime, any two members `a ≠ b` are joined by a Hamilton path.

**Proof.** Choose a buffer line `L` for the pair (III.11); transpose if `L` is a column,
so `L` is a row. The quotient of `L` is non-bipartite (III.12) and is the base-exchange
graph of the pattern matroid (III.4), hence Hamilton-connected (III.5). Take a Hamilton
path of the quotient from `a`'s pattern to `b`'s pattern. Every fiber is a strictly
smaller interchange graph (III.1), so by induction it is maximally Hamiltonian, and it is
connected. Thread the quotient path from both ends: from `a`, cross each fiber by a
Hamilton path from its entry to an exit on the interface toward the next pattern (III.6
supplies the interface and the color bookkeeping at constrained fibers, III.7 at
non-bipartite ones), stepping across crossing edges; from `b`, do the same backward. The
two threads meet at the buffer's fiber, whose entries are delivered by the avoid steps
(III.8, III.9) so that the two delivered terminals differ; the buffer fiber is
non-bipartite, hence Hamilton-connected by induction, and a Hamilton path between the two
terminals completes a single pass through every fiber. Concatenating runs and crossing
edges yields a Hamilton path of `G(R,S)` from `a` to `b`. ∎

---

# Part IV — the base classes (§6)

## IV.1 `reduction_base` and the census: `small_interchange_MH`

**Lean:** [`Ledger.lean` lines 714–795](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L714-L795), with the two-line Johnson reduction at [464–560](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L464-L560) and the executable certificates in [`Sec6.lean`](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec6.lean) — trace: foundations + `johnson_isMH` (A10), `prime_class_card_ge` (A7), and the CORE-side axioms through the bipartite branch.

### Statement

A base class — a Johnson graph `J(n,k)`, or an indecomposable class on at most six
vertices — is maximally Hamiltonian.

### The Lean proof, step by step

`reduction_base` (791–795) splits the two disjuncts: a Johnson representative transports
Alspach's theorem (cited, A10) across the isomorphism; the small case is the census.

`small_interchange_MH` (714–788): a bipartite small class goes through the Block Lemma
branch like any other (719–721); at most one vertex is vacuous (726–728). Otherwise
represent the class concretely, pass to an *active* representative (`exists_active_iso` —
the §2.2 deletion isomorphisms, entry VI.2; 733–736), and note both active dimensions are
at least 2 (741–755, a one-line-active class would be a single vertex). If some dimension
is exactly 2, the class is a Johnson graph: an active two-row class is isomorphic to
`J(n', k)` by reading the first row's support (`active_two_row_johnson_iso`, 491–518),
and Alspach applies (765–769). Otherwise both dimensions are at least 3, and the cited
counting bound (A7) gives `(m'−1)(n'−1) + 1 ≤ |V| ≤ 6`, forcing `m' = n' = 3` (772–787).
The active 3×3 margins are exactly the vectors with entries in `{1, 2}` (656–665), so a
bit-vector classification (625–655) leaves, up to permutation isomorphism
(`flipGraph_perm_iso`, 464–490), four canonical margin pairs: `(1,1,1)/(1,1,1)` and
`(2,2,2)/(2,2,2)` are bipartite and return to the Block Lemma branch (562–584), while the
`(2,1,1)` and `(2,2,1)` types are Hamilton-connected by **kernel-executed certificates**:
`Sec6`'s `hcAll` runs an all-pairs Hamilton-path search as a boolean program, its
correctness theorem `isHamConnected_of_hcAll` converts `hcAll = true` into
Hamilton-connectivity, and the hypothesis is discharged by `decide` — evaluated inside the
proof kernel, with no trusted compiler (`Sec6.lean` 1370–1377).

### The proof, reconstructed from the Lean

**Proposition.** Base classes are maximally Hamiltonian.

**Proof.** A Johnson graph is Hamilton-connected by Alspach's theorem. For an
indecomposable class on at most six vertices: if bipartite, the Block Lemma branch already
covers it; otherwise pass to the active core (deleting empty and full lines is a graph
isomorphism). If the core has two active rows or columns, the class is a Johnson graph —
a two-row class is determined by the first row's support, with interchanges acting as
`J(n,k)`'s fixed-intersection adjacency — and Alspach again applies. Otherwise both
dimensions are at least three, and the dimension bound `(m−1)(n−1) + 1 ≤ |A(R,S)|` for
prime active classes caps both at three. The active 3×3 margins have all line sums 1 or 2;
up to permutations and transposition this is four classes, of which the two constant ones
are bipartite (Block Lemma) and the two mixed ones are finite graphs whose
Hamilton-connectivity is verified exhaustively — in the formalization, by a search
executed and checked inside the proof kernel. ∎

---

# Part V — the Block Lemma (§7)

## V.1 Lemma 1.2 / the global CORE: `core_global` and `CORE`

**Lean:** [`Ledger.lean` lines 103–165](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L103-L165) — trace: foundations + A1–A4.

### Statement

Every balanced-bipartite interchange graph is paired 2-disjoint-path-coverable for
balanced demands (spanning-2-laceable). This is the paper's Block Lemma.

### The Lean proof, step by step, and reconstruction

On fewer than four vertices the demand of a paired 2-cover — four distinct terminals — is
unsatisfiable, so the property holds vacuously (115–123; the four-injection counting).
Otherwise the structure theorem (cited, A4): the graph is isomorphic, color-respectingly,
to a canonical Cartesian product of complete transposition graphs, and the paired 2-cover
property is invariant under color-respecting isomorphisms (`spanning2_iso_invariant`,
28–56), so Theorem 7.1 (`CORE'`, entry V.2) finishes. Reconstructed: the paper's two-line
§7 opening — "by Brualdi's structure theory it suffices to prove the property for products
of complete transposition graphs" — with the degenerate-size caveat made explicit.

## V.2 Theorem 7.1 (the double induction): `canonicalCTProduct_paired_two`

**Lean:** [`Coleman.lean` lines 866–1271](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Coleman.lean#L866-L1271) — trace: foundations + `coleman_thm15` (A1), `prop11c` (A2), `hypercube_ctProduct_paired_two` (A3).

### Statement

Every canonical Cartesian product of complete transposition graphs `CT_a` (each factor
`a ≥ 2`, at least one factor) admits paired 2-disjoint path covers for all balanced
demands.

### The Lean proof, step by step

Structural induction over the canonical rank list, one case per constructor
(1205–1213):

- **All ranks 2** — the product is a hypercube; the paired 2-cover property is the cited
  Jo–Park–Chwa theorem (A3). This branch exists because Coleman's welding condition
  excludes the `K₂` leaf, so the hypercube family needs its own citation, exactly as in
  the paper.
- **A single large rank** (`CT_a`, `a ≥ 3`) — Coleman's Theorem 1.5 (A1) applies to
  `CT_a` as a transposition-like graph with single-vertex welding leaves, giving paired
  `(a−1)`-covers; the downgrade (A2, Prop 1.1(c)) brings `a−1` down to 2, its size guard
  `2(a−1) ≤ a!` checked by a factorial bound (853–935).
- **A large rank consed onto a canonical tail** (`ctProduct_consLarge_paired_two`,
  1177–1204): the induction hypothesis gives the tail its paired 2-cover; the tail is
  Hamilton-laceable from it (`canonical_paired_two_hamLaceable`, 1168–1176 — via the
  downgrade when the tail has at least four vertices, and directly for the one canonical
  small tail `[2] = K₂`, whose two vertices are swap-adjacent, 866–877). The product
  `CT_a □ tail` is then a welded graph whose welding tree has the tail as an *arbitrary
  even Hamilton-laceable rank-1 leaf* (`ctBoxProduct_tree`) — this is the C2 reading of
  Coleman's Theorem 1.5, re-audited verbatim against the source on 2026-07-04 — so A1
  gives paired `(a−1)`-covers of the product and A2 downgrades to 2, the size guard again
  by the factorial bound (1189–1202).

`CORE'` (1215–1217) converts the paired-cover form to the spanning-2-laceable interface.
Since 2026-07-05 the theorem is also machine-checked **as stated** — for arbitrary factor
orders: color-respecting isomorphisms for factor swaps, congruence, and insertion sort
(`CTColorIso` through `ctColorIso_insertionSort`, [Coleman 1230–1336](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Coleman.lean#L1230-L1336)), plus
"weakly decreasing rank lists are canonical" (`canonical_of_pairwiseGE`, 1338–1366), give
`ctProduct_paired_two_of_ranks` ([Ledger 129–147](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ledger.lean#L129-L147)) — the paper's silent
"write `G = CT_a □ B`" reordering, made formal.

### The proof, reconstructed from the Lean

**Theorem.** Canonical CT-products are paired 2-disjoint-path-coverable.

**Proof.** Induct on the number of factors, largest rank first (the canonical order). If
every factor is `K₂` the product is a hypercube, covered by Jo–Park–Chwa. A single factor
`CT_a` with `a ≥ 3` is a transposition-like graph all of whose welding leaves are single
vertices, so Coleman's Theorem 1.5 gives paired `(a−1)`-covers, and the equitable
downgrade reduces `a−1` to `2` (the demand-room condition `2(a−1) ≤ a!` holds for
`a ≥ 3`). For `CT_a □ P` with `P` a canonical product: by induction `P` has paired
2-covers, hence is Hamilton-laceable (downgrade to 1 when `|V(P)| ≥ 4`; `P = K₂` is
laceable outright). View `CT_a □ P` as welded over `CT_a`'s tree with the single leaf `P`:
`P` is even and Hamilton-laceable, which is precisely the leaf condition of Coleman's
Theorem 1.5, so the product has paired `(a−1)`-covers, and the downgrade again lands at
2. ∎

*Relation to the paper:* identical, including the `K₂`-leaf caveat (the paper's §7.3
remark) and the demand-room guards, which the Lean carries explicitly because the
unguarded downgrade is false on two vertices (TRUST_SURFACE §5.4).

---

# Part VI — infrastructure theorems (Lean-only)

## VI.1 Ryser's 2-switch existence: `switchable_block` and `interchange_has_edge`

**Lean:** [`Ryser.lean` lines 143–360](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Ryser.lean#L143-L360) — foundations-only.

### Statement

Two distinct 0/1 matrices with the same row and column sums contain a switchable 2×2
block (positions where one matrix reads `10/01` and the other `01/10`); consequently a
nontrivial interchange graph has an edge.

### The Lean proof, step by step, and reconstruction

Call a cell a `+cell` if `M` reads 1 and `M′` reads 0, a `−cell` the reverse. Distinctness
plus equal column sums yields a `+cell` (`exists_plus`, 206–235). From a `+cell (i,j)`,
column balance produces a `−cell (i′,j)` in the same column, and row balance at `i′`
produces a `+cell (i′,j′)` in a new column (`plus_step`, 236–268) — unless along the way
the four cells visited close a switchable block, in which case we stop. Iterating the step
(`stepFun_link`, 269–289) walks through `+cells` forever; finiteness of the matrix forces
the boolean trace of the walk to repeat (`bool_descent`, 143–174, the pigeonhole
extraction), and the first repeat closes an alternating rectangle: two rows and two
columns on which `M` reads `10/01` and `M′` reads `01/10` — the switchable block
(`switchable_block`, 292–348). For the edge (349–360): a class with two or more vertices
has two distinct members; the block gives a single 2×2 interchange applied to one of them,
producing an adjacent member. ∎

This is Ryser's classical argument in its walk form; the formal content feeds two places —
surjectivity of colorings (entry I.3) and the fiber-connectivity axiom's *edge*-level
counterpart (the full connectivity of classes under interchanges remains the cited A8;
this theorem is only the one-step existence).

## VI.2 The §2.2 deletion isomorphisms: `exists_active_iso`

**Lean:** [`Sec6.lean` lines 290–460 and onward](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Sec6.lean#L290-L460) — foundations-only.

A line with sum 0 (or full sum) is constant across the class; deleting it is a bijection
of classes that preserves and reflects interchanges (`deleteZeroRowEquiv_interchange_iff`
and its variants), hence a graph isomorphism, and iterating over all inactive lines lands
in an active class of the same graph. This is the paper's §2.2 "inactive lines can be
deleted" made into an explicit chain of isomorphisms; it feeds the §6 census (IV.1) and
the fiber renormalization story (III.1).

## VI.3 The laceability bridges

**Lean:** [`Coleman.lean` lines 128–470](https://github.com/jbaggett/brualdi-interchange-lean/blob/arxiv-v1/BrualdiLean/Coleman.lean#L128-L470) — foundations-only.

The dictionary between the papers' demand formats and the development's: paired
2-disjoint-path covers for opposite-colored demands convert to and from the
spanning-2-laceable interface (`spanning2_of_paired_two_opposite`,
`paired_two_of_spanning2`); paired 1-covers are Hamilton laceability
(`paired_one_opposite_iff_hamLaceable`); the equitable downgrade instance used throughout
is `paired_two_opposite_to_hamLaceable`; `laceable_card_two` settles `K₂`; and the parity
color of permutations realizes the CT-product coloring (`ctColor` lemmas,
`completeTransposition_balanced`, `completeTransposition_equitable`). These are the
definitional equivalences TRUST_SURFACE D17–D18 asks a reader to confirm once; each is a
short structural proof.

---

*End of the companion. The coverage table at the top is the completeness contract: every
numbered claim of the paper appears there with its Lean counterpart and its entry here, and
every entry's line references were checked against the pinned commit.*
