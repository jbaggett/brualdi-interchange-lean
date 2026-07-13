# Trust surface for `brualdi_MH`

This document gives a public verification guide for the main theorem in the Brualdi-MH Lean repository. We state the theorem, explain the definitions through which it factors, identify every cited axiom on its kernel trace, and quote the corresponding literature statements. The reader can use Part I as a guided tour and Part II as a definition-by-definition and axiom-by-axiom reference.

**Claim.** For all nonnegative-integer margin vectors (R) and (S), the interchange graph (G(R,S)) is maximally Hamiltonian: Hamilton-laceable when bipartite and Hamilton-connected when not.

**Repository build.** From the repository root, run `cd brualdi_lean && lake build`. The command must exit with code 0, and `.lake/build/lib/lean/BrualdiLean/Sec5.olean` must exist after the build. To inspect the trust boundary, run `lake env lean` on a file that imports `BrualdiLean.Ledger` and contains `#print axioms Brualdi.Ledger.brualdi_MH`.

---

# Part I: The tour

## I.1 What Lean verifies

The Lean development is a computer-checked derivation with three layers.

The bottom layer contains seven statements cited from published papers and books. We entered these statements as Lean axioms, which play the formal role of citations. Part II gives the complete Lean statement, mathematical reading, source quotation, and full citation for each axiom.

The top layer contains one statement: every interchange graph `G(R,S)` is maximally Hamiltonian.

The middle layer contains the definitions and machine-checked arguments for the reduction, product, pivot, base-case, and complete-transposition-product branches. The Lean kernel checks every deduction from the seven cited axioms to the main theorem.

The kernel checks formal deduction, but it does not interpret English mathematical terminology or compare a formal statement with a source. Three questions therefore remain for human verification:

1. Do the definitions match the mathematical definitions in the preprint?
2. Do the seven axioms claim no more than their cited sources prove?
3. Are the cited results correct?

The first two questions define the trust surface documented here. The third is the ordinary trust that mathematical writing extends to its bibliography.

Three further results taken from the literature were fully formalized and therefore do not appear among the cited axioms.

## I.2 The claim in one sentence

> For all nonnegative-integer margin vectors R and S (Lean: `r : Fin m → ℕ`, `s : Fin n → ℕ`), the interchange graph `G(R,S)` is maximally Hamiltonian: Hamilton-laceable when bipartite and Hamilton-connected when not.

The Lean statement has no realizability or size hypothesis. It includes infeasible margins and the resulting empty graph. The paper corollary restores the paper's standing realizability hypothesis:

> **Lean theorem** (`brualdi_MH`): for all nonnegative-integer margins `r` and `s`, including infeasible margins, `IsMH (flipGraph r s)`.
>
> **Paper corollary** (`brualdi_MH_paper`): if `𝔄(R,S)` is nonempty, then `G(R,S)` is maximally Hamiltonian in the paper's sense.

The one-vertex class is vacuously maximally Hamiltonian. The empty class is also covered vacuously by the stronger Lean statement.

## I.3 The verification checklist

Each row asks whether the formal statement says what the mathematics requires. Part II supplies the complete entry.

| No. | Confirm that | Entry |
|---:|---|---|
| 1 | The main theorem states that every `G(R,S)` is maximally Hamiltonian, without an added hypothesis. | §1 |
| 2 | `flipGraph` is the interchange graph: its vertices are the 0/1 matrices with margins R and S, and its edges are single 2×2 interchanges. | D1–D4 |
| 3 | `IsMH` means Hamilton-connected or properly and surjectively 2-colored Hamilton-laceable. | D6 |
| 4 | `IsSpanning2DPCOpposite` means paired 2-disjoint-path-coverability for balanced demands. | D7 |
| 5 | `IsInterchangeGraph` means isomorphic to some `G(R,S)`. | D8 |
| 6 | `IsProper2Coloring` asserts proper 2-coloring only; balance is expressed by `IsEquitableBipartite`. | D9–D10 |
| 7 | The pairwise opposite-colored demand encoding is equivalent to the sources' `S ⊆ V₁, T ⊆ V₂` formulation. | D17–D18 |
| 8 | `IsColemanTree` describes a transposition-like graph over one welding tree whose leaves are single vertices or have even order. | D22–D23 |
| 9 | Brualdi §6.3 supports the classification of a balanced-bipartite interchange graph with at least two vertices as a nonempty product of complete-transposition factors of order at least 2. | A4 |
| 10 | Brualdi Theorem 6.3.4 implies that an invariant-free non-bipartite interchange graph contains a triangle. | A5 |
| 11 | Brualdi–Manber Theorem 9 implies that every cell varies in an active, prime, nonempty class. | A6 |
| 12 | Brualdi §9.13, footnote 26, gives at least `(m−1)(n−1)+1` matrices in an active, invariant-free, nonempty class. | A7 |
| 13 | Ryser's theorem gives connectivity of every nonempty class under interchanges. | A8 |
| 14 | Naddef–Pulleyblank gives Hamilton-connectedness of every non-bipartite matroid base-exchange graph. | A9 |
| 15 | Alspach gives maximal Hamiltonicity of Johnson graphs; his stronger conclusion is Hamilton-connectedness. | A10 |

## I.4 How to read an entry

### Worked definition example

Entry D6 defines `IsMH`. The Lean code is the exact audit object. A reader who does not use Lean can begin with the **Mathematics** paragraph:

> *G is maximally Hamiltonian if either (i) G is Hamilton-connected, or (ii) G admits a proper 2-coloring with both color classes nonempty with respect to which it is Hamilton-laceable.*

The preprint describes maximal Hamiltonicity conditionally: laceable when bipartite and connected when not. The Lean definition uses a disjunction. The faithfulness notes explain why the formulations agree. They also explain the properness and surjectivity guards. Without properness, a constant coloring would make every graph vacuously MH. Without surjectivity, the edgeless graph on two vertices would be vacuously laceable.

### Worked axiom example

Entry A5 gives Brualdi's triangle result. The Lean block states the axiom exactly. The **Mathematics** paragraph translates it, and the **Source (verbatim)** paragraph reproduces the published statement. A referee should ask whether the mathematical translation claims more than the source quotation. Stronger hypotheses or a weaker conclusion are safe; weaker hypotheses or a stronger conclusion would enlarge the trust assumption.

This comparison procedure applies to all fifteen checklist rows.

## I.5 Questions about the trust boundary

**Why trust the kernel?** Lean's kernel is a small independent checker used throughout mathlib. The build and axiom-trace commands make the present claim reproducible.

**What are `propext`, `Classical.choice`, and `Quot.sound`?** These are Lean's foundations for ordinary classical mathematics: propositional extensionality, choice, and quotients.

**Why are seven axioms present?** Each axiom formalizes a citation. The axiom trace closes the list of external assumptions used by the theorem. It contains no hidden repository lemma and no unfinished proof.

**What do the guards accomplish?** Explicit properness, surjectivity, nonemptiness, and cardinality hypotheses prevent vacuous hypotheses on degenerate instances. Part II explains each guard where it enters. The sentinel lemmas test representative boundary cases.

**What do “no `sorryAx`” and “no `native_decide`” mean?** `sorryAx` would mark an unfinished proof. `native_decide` would add the compiler to the trusted base. Neither appears in the main theorem's axiom trace.

## I.6 Re-running the verification

Run the full build:

```sh
cd brualdi_lean
lake build
test -f .lake/build/lib/lean/BrualdiLean/Sec5.olean
```

Then create a temporary file such as `CheckAxioms.lean` in `brualdi_lean`:

```lean
import BrualdiLean.Ledger
#print axioms Brualdi.Ledger.brualdi_MH
```

Run:

```sh
lake env lean CheckAxioms.lean
```

The output must list exactly `propext`, `Classical.choice`, `Quot.sound`, and the seven cited axioms reproduced in Part II §0.

---

# Part II: The reference layer

Every definition and cited axiom appears below in full. Each entry begins with verbatim Lean. Readers interested only in the mathematical meaning can read the **Mathematics** paragraph and source quotation.

## 0. The claim, and how to check it yourself

```
Brualdi.Ledger.brualdi_MH :
  ∀ {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ), IsMH (flipGraph r s)
```
(`Ledger.lean:989`.) In words: **every interchange graph `G(R,S)` of a class of 0/1 matrices with
prescribed row-sum vector R and column-sum vector S is maximally Hamiltonian**, with no
realizability, activity, or size hypothesis at all (the empty and one-vertex classes are vacuously
MH; see the `IsMH` entry).

Verification is two commands, both of which must succeed:

1. **The build gate.** `cd brualdi_lean && lake build` must **exit 0**, and
   `.lake/build/lib/lean/BrualdiLean/Sec5.olean` must exist afterwards. (The root module imports
   `Sec5`; the explicit `.olean` check confirms that the module compiled. A module-only build
   `lake build BrualdiLean.Sec5` can emit a spurious lint error; only the full build is
   authoritative.)
2. **The axiom trace.** Run `lake env lean` on a file containing
   `import BrualdiLean.Ledger` + `#print axioms Brualdi.Ledger.brualdi_MH`. The output must be:

```
'Brualdi.Ledger.brualdi_MH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Brualdi.Ledger.active_prime_cell_varies,
 Brualdi.Ledger.flipGraph_connected,
 Brualdi.Ledger.invariantFree_card_ge,
 Brualdi.Ledger.invariantFree_nonbip_has_triangle,
 Brualdi.Ledger.johnson_isMH,
 Brualdi.Ledger.naddef_pulleyblank_baseExchange,
 Brualdi.Ledger.weak_ct_product_raw]
```

`propext`, `Classical.choice`, `Quot.sound` are Lean/mathlib's three classical foundations. The
other **seven** are the cited external theorems documented in §3. The trace contains no
`sorryAx` and no `Lean.ofReduceBool`, so it uses neither unfinished proofs nor `native_decide`.

---

## 1. The main theorem and its immediate frame

### `brualdi_MH`: `Ledger.lean:989`

```lean
theorem brualdi_MH {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) :
    IsMH (flipGraph r s) := by
  classical
  exact reduction (flipGraph r s) (flipGraph_isInterchange r s) core_global
```

It is the composition of three machine-checked pieces: `reduction` (the §§3–6 strong induction and
trichotomy, `Ledger.lean:975`), the tautological `flipGraph_isInterchange`, and `core_global` (the
CORE bridge, `Ledger.lean:109`). Section 3 lists every assumption used underneath.

---

## 2. The definition chain

Every notion `brualdi_MH` factors through, in dependency order. **The kernel does not check that
these definitions capture the paper's notions; that is exactly what this section is for.**

> **How to read the Lean vocabulary (one box, used by every entry below).**
> - `Fin n` is the finite index set `{0, 1, …, n−1}`. A function `Fin k → V` is just a list of
>   `k` vertices `v₀, …, v_{k−1}` (possibly with repeats unless injectivity is stated).
> - `{x // P x}` is the subtype "the elements `x` satisfying `P`" — e.g. `MarginClass r s` is
>   "the 0/1 matrices with margins `(r, s)`". An element carries its membership proof; `.val`
>   strips it.
> - `SimpleGraph.fromRel R` builds a simple graph from ANY binary relation `R`: vertices `u ≠ v`
>   are adjacent iff `R u v` **or** `R v u`. So `fromRel` symmetrizes the relation and discards
>   loops; when an entry says "the relation is oriented, the graph symmetrizes it," this is what
>   is meant.
> - `G.Walk u v` is a walk from `u` to `v` (a sequence of consecutive edges); `p.support` is the
>   list of vertices it visits; `p.IsPath` says no vertex repeats; `p.IsHamiltonian` says it
>   visits **every** vertex of the graph exactly once. "`x ∈ p.support`" reads "the walk `p`
>   passes through `x`."
> - `Equiv.Perm (Fin a)` is the symmetric group `S_a`: all permutations of `{0, …, a−1}`, with
>   `*` composition, `⁻¹` inverse, `Equiv.swap x y` the transposition `(x y)`, and
>   `Equiv.Perm.sign` the usual even/odd sign.
> - `W ≃ W` is a bijection of `W` with itself packaged with its inverse (`.symm`); `G ≃g H` is a
>   graph isomorphism; `A □ B` is the Cartesian (box) product of graphs — copies of `B` indexed
>   by `A`'s vertices, with edges inside each copy and matching edges between copies whose
>   indices are adjacent in `A`.
>
> Nothing else in this section needs Lean knowledge beyond this box.

**Source definitions.** Where a formal definition transcribes a notion *defined in a cited
source*, the entry quotes the source's own definition verbatim for side-by-side comparison
(same convention as the axiom quotes in §3; OCR artifacts in the older scans, including ligatures
and the class symbol `𝔄`, are silently repaired; nothing else is touched). Definitions with no single
source (our packaging, e.g. D13, D15, D25) say so.

### 2.1 Core combinatorial objects (`Basic.lean`)

#### D1: `ZeroOneMat`, `rowSum`, `colSum` (`Basic.lean:20,23,26`)

```lean
abbrev ZeroOneMat (m n : ℕ) := Fin m → Fin n → Bool

def rowSum (M : ZeroOneMat m n) (i : Fin m) : ℕ := ∑ j, (if M i j then 1 else 0)
def colSum (M : ZeroOneMat m n) (j : Fin n) : ℕ := ∑ i, (if M i j then 1 else 0)
```

**Mathematics.** An `m×n` 0/1 matrix, and its `i`-th row sum / `j`-th column sum.
**Paper anchor.** §1/§2 (the class `𝔄(R,S)`).

#### D2: `HasMargins`, `MarginClass` (`Basic.lean:29,33`)

```lean
def HasMargins (r : Fin m → ℕ) (s : Fin n → ℕ) (M : ZeroOneMat m n) : Prop :=
  (∀ i, rowSum M i = r i) ∧ (∀ j, colSum M j = s j)

abbrev MarginClass (r : Fin m → ℕ) (s : Fin n → ℕ) : Type :=
  {M : ZeroOneMat m n // HasMargins r s M}
```

**Mathematics.** `MarginClass r s` **is** the matrix class `𝔄(R,S)`: all 0/1 matrices with row sums
`r` and column sums `s`.
**Source definition (verbatim).** Brualdi–Manber 1983, abstract, p. 156:
> "Let R = (r₁,…,r_m) and S = (s₁,…,s_n) be nonnegative integral vectors, and let 𝔄(R,S) denote
> the class of all m × n matrices of 0's and 1's having row sum vector R and column sum vector S."
**Faithfulness notes.** (i) The margins are **arbitrary functions** `Fin m → ℕ`; no monotone
(nonincreasing) normalization, no realizability assumption. Infeasible margins give the *empty*
class; see the permutation-equivariance and nonemptiness notes in §5. (ii) `m` or `n` may be `0`. If `m = 0` there is exactly one underlying `0×n` Boolean matrix, but
its column sums are all `0`: the margin class is a *singleton* exactly when every required column
margin is `0`, and *empty* otherwise (both sum equations in `HasMargins` must hold); similarly for
`m×0`.

#### D3: `Interchange` (`Basic.lean:41`)

```lean
def Interchange (M M' : ZeroOneMat m n) : Prop :=
  ∃ (i i' : Fin m) (j j' : Fin n), i ≠ i' ∧ j ≠ j' ∧
    M i j = true ∧ M i' j' = true ∧ M i j' = false ∧ M i' j = false ∧
    M' i j = false ∧ M' i' j' = false ∧ M' i j' = true ∧ M' i' j = true ∧
    (∀ a b, ¬ ((a = i ∨ a = i') ∧ (b = j ∨ b = j')) → M' a b = M a b)
```

**Mathematics.** One oriented 2×2 interchange: in rows `i ≠ i'` and columns `j ≠ j'`, the submatrix
`[[1,0],[0,1]]` becomes `[[0,1],[1,0]]`, all other entries unchanged. Brualdi's "interchange"
(= 2-switch / swap).
**Source definition (verbatim).** Brualdi 2006, §3.2, p. 52:
> "Then A₁ is obtained from A₂ by replacing a submatrix A₂[{p,q},{k,l}] = [[1,0],[0,1]] of A₂ of
> order 2 with [[0,1],[1,0]], or vice versa. We say that A₁ is obtained from A₂ by an interchange
> or, more precisely, by a (p,q;k,l)-interchange."
**Faithfulness note.** The relation is oriented (one diagonal to the other); the graph below
symmetrizes it, which recovers the standard unoriented interchange.

#### D4: `flipGraph` (`Basic.lean:54`)

```lean
def flipGraph (r : Fin m → ℕ) (s : Fin n → ℕ) : SimpleGraph (MarginClass r s) :=
  SimpleGraph.fromRel (fun M M' => Interchange M.val M'.val)
```

**Mathematics.** **The interchange graph `G(R,S)`**: vertices = the matrices of `𝔄(R,S)`, edges =
pairs that differ by a single interchange. `SimpleGraph.fromRel` makes the relation symmetric and
irreflexive: `Adj M M' ↔ M ≠ M' ∧ (Interchange M M' ∨ Interchange M' M)`.
**Source definition (verbatim).** Brualdi 2006, §3.2, pp. 52–53 (introducing `G(R,S)`, credited there to
Brualdi 1980):
> "The vertices of G(R,S) are the matrices in A(R,S). Two matrices A and B in A(R,S) are joined
> by an edge provided A differs from B by an interchange, equivalently, A − B is an interchange
> matrix."

Brualdi–Manber 1983 use the same definition ("two matrices are joined by an edge provided they
differ by an interchange").
**Paper anchor.** §1 (Brualdi 1980's object; Mütze P60).
**Sentinel.** `isInterchangeGraph_flipGraph` (`Sentinel.lean:17`); the hypothesis class of the
whole development is inhabited by the real thing.

### 2.2 Target properties (`Coleman.lean`)

#### D5: `HasHamPath`, `IsHamConnected`, `IsHamLaceable` (`ColemanDefs.lean:29,33,37`)

```lean
def HasHamPath (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, p.IsHamiltonian

def IsHamConnected (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → HasHamPath G u v

def IsHamLaceable (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ u v : V, col u ≠ col v → HasHamPath G u v
```

**Mathematics.** `HasHamPath G u v` says: there is a walk from `u` to `v` that visits every
vertex of the graph exactly once; a Hamilton path with prescribed endpoints. `IsHamConnected`
asks for such a path between **every** pair of distinct vertices; `IsHamLaceable` (relative to a
2-coloring `col`) asks for one between every pair of **oppositely colored** vertices, and asks
nothing about same-colored pairs.

**In plain terms.** On the complete graph `K₅`, any two distinct vertices are joined by a
Hamilton path (visit the other three in any order), so `K₅` is Hamilton-connected. On the 4-cycle
`C₄` with the alternating black/white coloring, every opposite-colored pair is adjacent, and
deleting the edge between them leaves a Hamilton path; so `C₄` is Hamilton-laceable; its two
same-colored (antipodal) pairs are joined by no Hamilton path, because in a bipartite graph with
equally many black and white vertices a Hamilton path must end in opposite colors; so `C₄` is
not Hamilton-connected. That parity obstruction is the entire reason the bipartite case of the
conjecture is stated with laceability. (Longer cycles witness neither property: a Hamilton path
of a cycle is the cycle minus one edge, so its endpoints must be *adjacent*; `C₅` is not
Hamilton-connected and `C₆` is not Hamilton-laceable.)

**The mathlib layer this rests on (verbatim).** `Walk.IsHamiltonian` is mathlib's, not ours:
```lean
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1
```
, every vertex appears in the walk's support exactly once. Its two consequences that D5's gloss
uses (such a walk is a path, and it covers every vertex) are machine-checked, not prose: sentinel
`hamPath_isPath` (`Sentinel.lean`) proves `HasHamPath G u v → ∃ p, p.IsPath ∧ ∀ x, x ∈ p.support`.

**Source definitions (verbatim).** Alspach 2013, §1, p. 1:
> "A graph is Hamilton-connected if for any pair of distinct vertices u, v there is a Hamilton
> path whose terminal vertices are u and v. The graph with a single vertex is trivially
> Hamilton-connected."

(The last sentence is the source's own version of our vacuous small-case convention.) For
laceability, Coleman et al. 2025, §1, define it through path covers:
> "a paired 1-to-1 disjoint path coverable graph is also said to be Hamiltonian-connected" …
> "Another name for a balanced paired 1-to-1 disjoint path coverable graph is
> Hamiltonian-laceable."

**What to confirm.** That "Hamilton path" here means visits-every-vertex-exactly-once (it does:
mathlib's `IsHamiltonian` is `∀ x, walk visits x exactly once`, and a Hamiltonian walk is
automatically a path), and that laceability quantifies over exactly the opposite-colored pairs.

#### D6: `IsMH` (maximal Hamiltonicity: the target): `ColemanDefs.lean:44`

```lean
def IsMH (G : SimpleGraph V) : Prop :=
  IsHamConnected G ∨ ∃ col : V → Bool,
    (∀ u v, G.Adj u v → col u ≠ col v) ∧ Function.Surjective col ∧ IsHamLaceable G col
```

**Mathematics.** *G is maximally Hamiltonian if either (i) G is Hamilton-connected, or (ii) G
admits a proper 2-coloring with both color classes nonempty with respect to which it is
Hamilton-laceable.*
**Paper anchor.** §1: "maximally Hamiltonian if it is Hamilton-laceable when bipartite and
Hamilton-connected when not."
**Faithfulness notes.**
1. *Disjunction vs. the paper's conditional.* The two agree on every graph: a non-bipartite graph
   has no proper 2-coloring, so for it `IsMH` ⟺ Hamilton-connected exactly; a bipartite graph on
   ≥ 3 vertices is never Hamilton-connected (part-size parity kills one of the required pairs), so
   for it `IsMH` ⟺ laceable w.r.t. a proper surjective coloring; and a laceable coloring forces
   connectivity, where the proper 2-coloring is unique up to swapping the colors, i.e. it is *the*
   bipartition. (K₁ and K₂ satisfy both readings.)
2. *The properness and surjectivity guards are load-bearing.* Without properness, a constant
   coloring makes `IsHamLaceable` vacuous (every graph would be "MH"); without surjectivity, the
   edgeless 2-vertex graph is vacuously "laceable".
3. *Connectivity is implied, not assumed*: for |V| ≥ 2 either disjunct produces a spanning path.
   The one-vertex and empty graphs are vacuously Hamilton-connected, which is the intended reading
   of the theorem for |𝔄(R,S)| ≤ 1 (paper §1 remark).

**Sentinels** (`Sentinel.lean:25,41`): the edgeless graph on 2 vertices is **not** `IsMH`; the
constant coloring is blocked on any edge. (`Sec4.lean` adds: C₄ is not Hamilton-connected.)

#### D7: `IsSpanning2DPCOpposite` (`ColemanDefs.lean:49`)

```lean
def IsSpanning2DPCOpposite (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : V,
    col a₁ ≠ col b₁ → col a₂ ≠ col b₂ →
    a₁ ≠ a₂ → a₁ ≠ b₂ → b₁ ≠ a₂ → b₁ ≠ b₂ → a₁ ≠ b₁ → a₂ ≠ b₂ →
    ∃ (p : G.Walk a₁ b₁) (q : G.Walk a₂ b₂),
      p.IsPath ∧ q.IsPath ∧
      (∀ x, x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ x, ¬ (x ∈ p.support ∧ x ∈ q.support))
```

**Mathematics.** Paired 2-disjoint-path-coverable for opposite-colored demands: for any four
distinct vertices grouped into two oppositely-colored pairs, two vertex-disjoint paths join the
pairs and together cover every vertex. This is the CORE property (paper §2.4/§3).
**Faithfulness note.** For |V| < 4 the property is vacuous (no four distinct vertices); this
convention matters and is discussed in §4.4. The bridge lemmas `paired_two_of_spanning2` and
`spanning2_of_paired_two_opposite` prove equivalence with
`IsPairedKDPCForOpposite G col 2` in both directions.

#### D8: `IsInterchangeGraph` (`ColemanDefs.lean:60`)

```lean
def IsInterchangeGraph (G : SimpleGraph V) : Prop :=
  ∃ (m n : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ) (φ : V ≃ MarginClass r s),
    ∀ a b, G.Adj a b ↔ (flipGraph r s).Adj (φ a) (φ b)
```

**Mathematics.** `G` *is* (isomorphic to) an interchange graph, for some dimensions and margins.
This is the hypothesis under which every abstract lemma of the development operates; a genuine
predicate, not satisfied by all graphs, which is what keeps graph-level axioms falsifiable.

#### D9: `IsProper2Coloring` (`ColemanDefs.lean:69`)

```lean
def IsProper2Coloring (G : SimpleGraph V) (col : V → Bool) : Prop :=
  ∀ u v, G.Adj u v → col u ≠ col v
```

**Mathematics.** `col` is a proper 2-coloring of `G`. This predicate asserts bipartiteness with the given witness and imposes no condition on color-class sizes. Entry D10 gives the separate equitability condition.

#### D10: `IsEquitableBipartite` (`ColemanDefs.lean:223`)

```lean
def IsEquitableBipartite [Fintype V] (G : SimpleGraph V) (col : V → Bool) : Prop :=
  IsProper2Coloring G col ∧
    Fintype.card {v : V // col v = false} = Fintype.card {v : V // col v = true}
```

**Mathematics.** Proper 2-coloring **and** equal color classes (the papers' "equitable").
Consequences proved in Lean: surjectivity on nonempty graphs
(`surjective_of_equitable_nonempty`, `:393`) and even order (`equitable_even_card`, `:422`).
**Source definition (verbatim).** Coleman et al. 2025, §1, p. 2:
> "if G is an equitable bipartite graph, i.e., |V₁| = |V₂|"

### 2.3 Trichotomy predicates

#### D11: `IsBaseClass` (`ColemanDefs.lean:74`) and the Johnson graph (`Johnson.lean:15–22`)

```lean
def IsBaseClass {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  IsInterchangeGraph G ∧
    ((∃ (n k : ℕ), 0 < k ∧ k < n ∧ Nonempty (G ≃g Brualdi.Johnson.Jgraph n k)) ∨
      Fintype.card V ≤ 6)

-- Johnson.lean:
abbrev JV (n k : ℕ) := {s : Finset (Fin n) // s.card = k}
def Jgraph (n k : ℕ) : SimpleGraph (JV n k) :=
  SimpleGraph.fromRel (fun s t => (s.1 ∩ t.1).card = k - 1)
```

**Mathematics.** A base class is an interchange graph that is either a Johnson graph `J(n,k)` or
a graph on at most 6 vertices. The Johnson-graph vertices are the k-subsets of an n-set, with an
edge when two subsets intersect in k−1 elements. These are the interchange graphs with at most
two active lines in paper §6. The finite census includes six-vertex classes. A7's bound exceeds
6 when `min(m,n) ≥ 3` and `(m,n) ≠ (3,3)`; the order-5 and order-6 census cores cover the 3×3
case.

**Scope guard.** `IsInterchangeGraph G` is a conjunct of the definition. The small-cardinality
disjunct therefore applies only to interchange graphs. The sentinel
`edgeless_two_not_baseClass` confirms that the edgeless graph on two vertices cannot enter this
branch.

**Source definition (verbatim).** Alspach 2013, §1, p. 1:
> "The Johnson graph J(n, k), 0 ≤ k ≤ n, is defined by letting the vertices correspond to the
> k-subsets of an n-set, where two vertices are adjacent if and only if the corresponding
> k-subsets have exactly k − 1 elements in common."

#### D12: `IsDecomposable` (`ColemanDefs.lean:83`)

```lean
def IsDecomposable {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (W₁ W₂ : Type) (_ : DecidableEq W₁) (_ : DecidableEq W₂) (_ : Fintype W₁) (_ : Fintype W₂)
      (A : SimpleGraph W₁) (B : SimpleGraph W₂),
    Nontrivial W₁ ∧ Nontrivial W₂ ∧ IsInterchangeGraph A ∧ IsInterchangeGraph B ∧
      Nonempty (G ≃g A □ B)
```

**Mathematics.** `G` is a nontrivial Cartesian (box) product of two smaller **interchange** graphs
(`□` is mathlib's `SimpleGraph.boxProd`). The factors being interchange graphs is what the paper's
§2.2 invariant-position decomposition guarantees, and exactly what lets the induction hypothesis
apply to each factor in §4.
**Faithfulness note.** Requiring interchange factors makes `IsDecomposable` *harder* to satisfy
than bare product-ness, hence `¬IsDecomposable` (the hypothesis used in §5/§6 via "prime") *easier*
, but Brualdi–Manber's primeness is exactly product-of-interchange-blocks (their Thm 1 + Sabidussi
unique factorization), so the notions coincide on interchange graphs; see the
`active_prime_cell_varies` entry (A6).
**Source definition (verbatim).** Brualdi–Manber 1983, §2, p. 159 (OCR repaired):
> "Then the Cartesian product G₁ × G₂ is the graph with vertex set V₁ × V₂ and with an edge
> joining (x₁, x₂) and (y₁, y₂) if and only if x₁ = y₁ and [x₂, y₂] ∈ E₂ or x₂ = y₂ and
> [x₁, y₁] ∈ E₁. Following Sabidussi [6], we say that a graph G is prime if whenever G is
> isomorphic to G₁ × G₂, G₁ or G₂ consists of a single vertex."

Our `IsDecomposable` is the negation of their primeness, restricted to interchange factors
(the faithfulness note above).

#### D13: `IsIndecomposableNonBase` (`ColemanDefs.lean:92`)

```lean
def IsIndecomposableNonBase {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬(∃ col, IsProper2Coloring G col) ∧ ¬IsBaseClass G ∧ ¬IsDecomposable G
```

**Mathematics.** The fourth case of the paper's §3 case split, *defined as the complement of the
other three*: not bipartite, not a base class, not decomposable.

**In plain terms.** The paper argues "every class is bipartite, decomposable, base, or else lands
in the §5 pivot regime." In the Lean, "or else" is made literal: this predicate IS the
conjunction of the three negations, so the trichotomy theorem (`Ledger.lean:253`) is true by
classical logic alone and carries no combinatorial content. That is deliberate, and it is the
honest reading of the paper's "the cases are exhaustive": exhaustiveness is free; everything
substantive lives in (i) the three positive definitions D9/D11/D12 saying what the named cases
*mean*, and (ii) the four branch theorems doing real work in each case. In particular the §5
regime's working hypotheses, at least three active rows and columns, are *derived* from this
definition (via D15's bridge `wideActiveCore_of_not_base`: a non-base class has more than six
vertices and cannot have ≤ 2 active lines, else it would BE a Johnson base class), never assumed.

**What to confirm.** Only that the three positive predicates it negates are the right ones,
this entry adds nothing new to check beyond D9, D11, D12.

#### D14: `IsActive` (`Sec6.lean:855`) and `CellVaries` (`Sec5.lean:178`)

```lean
def IsActive {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) : Prop :=
  (∀ i, 0 < r i ∧ r i < n) ∧ (∀ j, 0 < s j ∧ s j < m)

def CellVaries {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ) (i : Fin m) (j : Fin n) : Prop :=
  ∃ M N : MarginClass r s, M.val i j ≠ N.val i j
```

**Mathematics.** *Active*: every row sum strictly between 0 and n, every column sum strictly
between 0 and m (Brualdi–Manber's `1 ≤ rᵢ ≤ n−1, 1 ≤ sⱼ ≤ m−1`). *Cell (i,j) varies*: the class
has two matrices differing there; "(i,j) is not an invariant position".

**In plain terms.** A row sum of `0` forces a whole row of zeros in every member (that row is
frozen, hence inactive); a row sum of `n` forces a row of ones. "Active" says no line is
frozen for that trivial reason. A *cell* can still be frozen for subtler reasons even when its
lines are active; "the cell varies" rules that out for one cell. The Brualdi–Manber theorem (A6)
says: in an active *prime* nonempty class, every cell varies.

**Nonemptiness guard.** `IsActive` is a condition on the margin *numbers* only; it does **not** imply the class is
nonempty (`active_empty_class_exists`, `Sentinel.lean:56`: active margins with an empty class
exist). This is why the B–M axioms carry explicit `Nonempty` guards (§3 and §4.4).

**Source definitions (verbatim).** Brualdi–Manber 1983, abstract (p. 156) and §1 (OCR repaired):
> "An invariant position of 𝔄(R,S) is a position whose entry is the same for all matrices in
> 𝔄(R,S)." … "We prove that when 1 ≤ rᵢ ≤ n − 1 (i = 1,…,m) and 1 ≤ sⱼ ≤ m − 1 (j = 1,…,n),
> G(R,S) is prime if and only if 𝔄(R,S) has no invariant positions."

The displayed inequalities are exactly our `IsActive`; "the cell varies" is exactly the negation
of "invariant position."

**What to confirm.** That "active" matches the paper's/B–M's inequalities and that "varies" is
the negation of "invariant position." Both are one-line definitions; the content is the guard
note above.

#### D15: `HasWideActiveCore` (`Ledger.lean:850`)

```lean
def HasWideActiveCore {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (m n : ℕ) (r : Fin m → ℕ) (s : Fin n → ℕ),
    3 ≤ m ∧ 3 ≤ n ∧ IsActive r s ∧ Nonempty (G ≃g Brualdi.flipGraph r s)
```

**Mathematics.** `G` has an active representative with ≥3 rows and ≥3 columns; the §5 pivot
regime. In the glue it is *derived* from `¬IsBaseClass` via the mechanized "≤2 active lines ⇒
Johnson" bridge (`wideActiveCore_of_not_base`), never assumed.

### 2.4 Disjoint-path-cover machinery (`Coleman.lean`)

#### D16: `IsPairedDPC` (`ColemanDefs.lean:97`)

```lean
def IsPairedDPC (G : SimpleGraph V) (k : Nat) (s t : Fin k → V) : Prop :=
  ∃ p : ∀ i : Fin k, G.Walk (s i) (t i),
    (∀ i : Fin k, (p i).IsPath) ∧
    (∀ x : V, ∃ i : Fin k, x ∈ (p i).support) ∧
    (∀ i j : Fin k, i ≠ j → ∀ x : V,
      ¬ (x ∈ (p i).support ∧ x ∈ (p j).support))
```

**Mathematics.** A *paired k-disjoint path cover* for the demand `(s, t)`. The demand is `k`
prescribed source–target pairs `(s₀, t₀), …, (s_{k−1}, t_{k−1})`. The cover is `k` walks, the
`i`-th from `s i` to `t i`, such that: each walk is a *path* (no repeated vertex); every vertex
of the graph lies on at least one of the paths (the cover clause); and no vertex lies on two
different paths (the disjointness clause). Together the last two say the vertex sets of the `k`
paths **partition** `V(G)`.

**In plain terms.** Imagine `k` pins-and-strings puzzles solved at once: string `i` runs from
pin `s i` to pin `t i`, no two strings touch, and every vertex is threaded by exactly one
string. A Hamilton path is exactly the case `k = 1`. A worked `k = 2` example on the 6-cycle
`1–2–3–4–5–6–1`: the demand `(1,4), (2,3)` is covered by `p₁ = 1–6–5–4` and `p₂ = 2–3`; disjoint,
and together they hit all six vertices. The demand `(1,2), (4,5)` has NO cover: a `1→2` path is
either the edge `1–2` (and then a single `4→5` path would have to cover `3, 4, 5, 6`, but `3` and
`6` are dead ends off the path `4–5`) or the whole cycle minus an edge (leaving nothing for the
second path). Working one such example by hand is the fastest way to internalize the three
clauses; and it shows the property is a genuine demand on the graph, not a formality.

**Source definitions (verbatim).** Coleman et al. 2025, §1, p. 2:
> "Given a graph G, let S = {s₁, s₂, …, s_k} and T = {t₁, t₂, …, t_k} be two disjoint k-subsets
> of V(G). A paired k-to-k disjoint path cover (sometimes abbreviated as k-PDPC) of G is a
> collection of path subgraphs P₁, P₂, …, P_k of G such that V(P₁), V(P₂), …, V(P_k) form a
> partition of V(G) and P_i has s_i and t_i as its endpoints for each i ∈ [k]."

Jo–Park–Chwa 2013, abstract:
> "A paired many-to-many k-disjoint path cover (paired k-DPC for short) of a graph is a set of k
> vertex-disjoint paths joining k distinct source-sink pairs that altogether cover every vertex
> of the graph."

Both say: paths, prescribed endpoints per pair, vertex sets partitioning `V(G)`; the three
conjuncts of the Lean definition.

**What to confirm.** Three clauses: paths (not mere walks), joint coverage, pairwise
disjointness. The formal statement has exactly these three conjuncts.

#### D17: `OppositeDemand` (`ColemanDefs.lean:112`): **encoding note**

```lean
def OppositeDemand (col : V → Bool) {k : Nat} (s t : Fin k → V) : Prop :=
  (∀ i : Fin k, col (s i) ≠ col (t i)) ∧
  Function.Injective s ∧
  Function.Injective t ∧
  (∀ i j : Fin k, s i ≠ t j)
```

**Mathematics.** What counts as a *legal* demand for the covers of D16, in this development:
`k` source–target pairs in which (i) the two endpoints of each pair have opposite colors, (ii)
no source repeats and no target repeats (`s`, `t` injective), and (iii) no source equals any
target; together: all `2k` endpoints are distinct, and each pair straddles the bipartition.
**Source definition (verbatim).** Coleman et al. 2025, §1, p. 2 (the demand class their results run
over):
> "A bipartite graph G is said to be balanced paired k-to-k disjoint path coverable if there is
> a k-PDPC whenever S ∪ T is balanced."

with balanced meaning, for equitable G, `|(S ∪ T) ∩ V₁| = |(S ∪ T) ∩ V₂|`. Our pairwise-opposite encoding is equivalent to the sources' `S ⊆ V₁,
T ⊆ V₂` demand form, which is the class Theorem 1.5 and the CORE property quantify over. The
*general* balanced class (Coleman's Prop 1.1 context) is strictly larger for k ≥ 2 (two same-part
pairs may balance each other); we neither claim nor need that larger class. The S/T-form
equivalence is the faithfulness note below.
**Faithfulness note.** The DPC sources (Jo–Park–Chwa,
Coleman) phrase paired k-DPC over **sets** `S ⊆ V₁`, `T ⊆ V₂` (each side inside one color class).
The pairwise-opposite encoding is *equivalent* to that form for a bipartite graph: within each
pair, exactly one endpoint lies in each part, so swapping `s i ↔ t i` where needed (with walk
reversal) relabels any pairwise-opposite demand into an `S ⊆ V₁, T ⊆ V₂` demand and vice versa.
The relabelling affects no conclusion and is left implicit throughout.

#### D18: `IsPairedKDPCForOpposite` (`ColemanDefs.lean:118`)

```lean
def IsPairedKDPCForOpposite (G : SimpleGraph V) (col : V → Bool) (k : Nat) : Prop :=
  ∀ s t : Fin k → V, OppositeDemand col s t → IsPairedDPC G k s t
```

**Mathematics.** "`G` is paired `k`-disjoint-path coverable for opposite demands": every legal
demand in the sense of D17 admits a cover in the sense of D16. This is the property the whole §7
induction manipulates, at `k = n−1` (from Coleman's theorem) and `k = 2` (the Block Lemma's
form) and `k = 1` (Hamilton laceability).

**In plain terms and what to confirm.** Two conversions are proved, not assumed, and they are
what lets the development move between the papers' languages: at `k = 2` this property is
exactly D7's `IsSpanning2DPCOpposite` (`paired_two_of_spanning2` / `spanning2_of_paired_two_opposite`),
and at `k = 1` it is exactly Hamilton laceability (`paired_one_opposite_iff_hamLaceable`; one
path covering all vertices between an opposite-colored pair IS a Hamilton path).
**Cardinality convention.** When `|V| < 2k`, no legal demand exists because a demand needs `2k` distinct vertices. The property then holds vacuously.

### 2.5 Complete-transposition products and welds (`Coleman.lean`)

#### D19: `CompleteTranspositionGraph`, `CompleteTranspositionColor` (`ColemanDefs.lean:272,275`)

```lean
def CompleteTranspositionGraph (a : Nat) : SimpleGraph (Equiv.Perm (Fin a)) :=
  SimpleGraph.fromRel fun σ τ => Equiv.Perm.IsSwap (σ⁻¹ * τ)

def CompleteTranspositionColor (a : Nat) (σ : Equiv.Perm (Fin a)) : Bool :=
  if Equiv.Perm.sign σ = 1 then false else true
```

**Mathematics.** The *complete transposition graph* `CT_a`, and its parity 2-coloring.

**In plain terms: the graph.** Vertices are all `a!` permutations of `{1, …, a}`. Two
permutations `σ, τ` are adjacent when `σ⁻¹ τ` is a transposition; equivalently, when
`τ = σ · (x y)` for some transposition `(x y)`: you get from `σ` to `τ` by composing with one
swap. (The `fromRel` symmetrization is harmless here: `(σ⁻¹τ)⁻¹ = τ⁻¹σ`, and the inverse of a
transposition is itself, so the relation is already symmetric.) This is the Cayley graph of the
symmetric group with respect to ALL transpositions; every vertex has degree `a(a−1)/2`.
Smallest cases: `CT₂ = K₂` (two permutations, one swap); `CT₃ = K_{3,3}` (six permutations, each
even one adjacent to all three odd ones).

**In plain terms: the coloring.** `CompleteTranspositionColor` colors a permutation by its
sign: even permutations `false`, odd ones `true`. Multiplying by a transposition flips the sign,
so adjacent vertices always get opposite colors; the coloring is proper, and it is exactly the
bipartition of `CT_a` into even and odd permutations. Both facts are *proved*, not assumed:
`ctColor_false_iff`/`ctColor_true_iff` (the color is the sign) and
`completeTransposition_equitable` (for `a ≥ 2` the two classes have equal size `a!/2`).

**Source definition (verbatim).** Coleman et al. 2025, §1, p. 3:
> "If G = S_n and T_n = {(i, j) : 1 ≤ i < j ≤ n}, then the Cayley graph Γ(S_n, T_n) is called
> the transposition graph of rank n. Note that for n ≥ 2, the transposition graph Γ(S_n, T_n)
> has a structural property that it is composed of n subgraphs Γ₁, Γ₂, …, Γ_n, each Γ_i is an
> isomorphic copy of Γ(S_{n−1}, T_{n−1}), and there is a perfect matching between Γ_i and Γ_j
> for all 1 ≤ i < j ≤ n."

(The quoted structural property is exactly the weld decomposition our `ct_weld_iso` proves.)

**What to confirm.** That this is the same `CT_a` as the paper's §7 and Brualdi §6.3 (Cayley
graph of `S_a` on all transpositions) and that "even = `false`" is a labeling convention with no
mathematical content (only *opposite* colors ever matter).

#### D20: `CTProductVertex/Graph/Color` (`ColemanDefs.lean:278,313,318`)

```lean
def CTProductVertex : List Nat → Type
  | [] => PUnit
  | [a] => Equiv.Perm (Fin a)
  | a :: b :: ranks => Equiv.Perm (Fin a) × CTProductVertex (b :: ranks)

def CTProductGraph : (ranks : List Nat) → SimpleGraph (CTProductVertex ranks)
  | [] => ⊥
  | [a] => CompleteTranspositionGraph a
  | a :: b :: ranks => CompleteTranspositionGraph a □ CTProductGraph (b :: ranks)

def CTProductColor : (ranks : List Nat) → CTProductVertex ranks → Bool
  | [], _ => false
  | [a], σ => CompleteTranspositionColor a σ
  | a :: b :: ranks, x => Bool.xor (CompleteTranspositionColor a x.1) (CTProductColor (b :: ranks) x.2)
```

**Mathematics.** The Cartesian product `CT_{a₁} □ ⋯ □ CT_{a_k}`, built by recursion on the list
of ranks, with the xor-of-signs coloring.

**In plain terms.** A vertex is a tuple of permutations, one per factor; a step in the product
changes exactly ONE coordinate by one transposition (that is what the box product's edges are).
The color of a tuple is the parity of the *total* number of inversions across coordinates,
`xor` of the factor signs. One step flips exactly one factor's sign and therefore flips the total.
The coloring is proper, and it is the product's bipartition. The base case of the recursion, the
empty list, is the one-vertex graph colored `false`; canonical rank lists (D21) exclude it.
Sanity example: `CT₂ □ CT₂ = K₂ □ K₂ = C₄`, colored alternately, classes of size 2.
Equitability for nonempty products is proved (`ctProduct_equitable :989`).

**What to confirm.** That the recursion really is "the graphs the paper multiplies, with the
bipartition coloring"; Prop 2.2's canonical form (A4) hands the reduction exactly these
objects.

#### D21: `CanonicalCTRanks` (`ColemanDefs.lean:818`)

```lean
inductive CanonicalCTRanks : List Nat → Prop where
  | allTwos {ranks : List Nat} (hne : ranks ≠ []) (hall : ∀ a : Nat, a ∈ ranks → a = 2) :
      CanonicalCTRanks ranks
  | singleLarge (a : Nat) (ha : 3 ≤ a) : CanonicalCTRanks [a]
  | consLarge (a : Nat) {ranks : List Nat} (ha : 3 ≤ a) (htail : CanonicalCTRanks ranks) :
      CanonicalCTRanks (a :: ranks)
```

**Mathematics.** Which rank lists the §7 induction ranges over. Three constructors, mirroring
the induction's three cases: a nonempty all-2s list (the product is then a hypercube; `CT₂ = K₂`
in every factor); a single rank `a ≥ 3` (a bare `CT_a`); or a head `a ≥ 3` on a canonical tail
(the inductive step `CT_a □ tail`).

**In plain terms.** "Canonical" does two jobs. It normalizes the structure theorem's output,
Prop 2.2 (A4) delivers every balanced-bipartite interchange graph as such a product, with ranks
that can be taken ≥ 2 and, when some rank exceeds 2, ordered so a large rank leads. It also names
the induction's case split. The all-2s case is where Coleman's welding condition cannot be used
because a `K₂` leaf has one vertex. The formalized hypercube result takes over. Every canonical
product has at least 2 vertices, and `[2]` (= `K₂`) is the only one with
fewer than 4 (`canonical_card_ge_four_or_eq_two`); the two smallness facts the downgrade guards
feed on.
**Nonemptiness guard.** The **empty** list (product = one vertex) is deliberately excluded; that is why
`weak_ct_product` carries its `2 ≤ card` guard (§3 A4).

**What to confirm.** That these three cases exhaust the products Prop 2.2 can deliver (they do:
any multiset of ranks ≥ 2 either is all 2s or contains some `a ≥ 3` to lead with), and that each
constructor's side conditions match the case the induction actually handles.

#### D22: `weldGraph` (`ColemanDefs.lean:328`)

```lean
def weldGraph {W : Type*} (ell : ℕ) (Gs : Fin ell → SimpleGraph W) (M : Fin ell → Fin ell → (W ≃ W)) :
    SimpleGraph (Fin ell × W) :=
  SimpleGraph.fromRel (fun p q =>
    (p.1 = q.1 ∧ (Gs p.1).Adj p.2 q.2) ∨ (p.1 ≠ q.1 ∧ q.2 = M p.1 q.1 p.2))
```

**Mathematics.** Coleman's **weld**. Take `ell` graphs `G₀, …, G_{ell−1}`, all on the same vertex
set `W` (so all have the same order). The weld lives on pairs `(i, u)`, meaning "vertex `u` in
copy `i`," with two kinds of edges: internal edges between `(i,u)` and `(i,v)` whenever `G_i`
has the edge `u v`, and cross edges between `(i,u)` and `(j, M i j u)` for `i ≠ j`. Copy `i` is
joined to copy `j` by the
perfect matching that the bijection `M i j` prescribes. Arbitrary matchings are allowed (Coleman's
definition allows any perfect matching between each pair of copies, not just "identify equal
labels"); `CT_a`'s coset matchings genuinely need that generality.

**Coherence condition.** `SimpleGraph.fromRel` symmetrizes the relation, so the cross edges from `M i j` and `M j i` must describe the same matching. Entry D23 requires `M j i = (M i j).symm`. This condition gives exactly one perfect matching between each pair of copies, as Coleman's definition requires.

**Source definition (verbatim).** Coleman et al. 2025, Definition 1.2, p. 3:
> "If G₁, G₂, …, G_n are n graphs with the same number of vertices, then G is said to be a weld
> of G₁, G₂, …, G_n if G is composed of G₁, G₂, …, G_n and there is a perfect matching between
> G_i and G_j for all 1 ≤ i < j ≤ n."

**What to confirm.** That "ell copies + a perfect matching between each pair" is Coleman's Def
1.2/1.3 weld, and that the coherence condition is what "a perfect matching between each pair"
means once each matching is written as a function with a direction.

#### D23: `IsColemanTree` (`ColemanDefs.lean:345`)

```lean
inductive IsColemanTree : {V : Type} → SimpleGraph V → ℕ → Prop where
  | base {V : Type} [DecidableEq V] {G : SimpleGraph V}
      (hham : IsHamConnected G ∨
        ∃ col : V → Bool, IsProper2Coloring G col ∧ Function.Surjective col ∧
          IsHamLaceable G col)
      (hcard : Nat.card V = 1 ∨ Even (Nat.card V)) :
      IsColemanTree G 1
  | weld {V W : Type} {G : SimpleGraph V} {ell r : ℕ} {Gs : Fin ell → SimpleGraph W}
      {M : Fin ell → Fin ell → (W ≃ W)}
      (hr : 2 ≤ r) (hEll : r ≤ ell) (htl : ∀ i, IsColemanTree (Gs i) (r - 1))
      (hM : ∀ i j, M j i = (M i j).symm)
      (e : G ≃g weldGraph ell Gs M) :
      IsColemanTree G r
```

**Mathematics.** Coleman's Def 1.2/1.3 welding tree **combined with** Thm 1.5's leaf condition,
over one tree. The `hM` field requires the pairwise matchings to be mutually inverse; see D22.

**`Nat.card` note.** The `base` constructor uses `Nat.card V`
without a `[Fintype V]` hypothesis, and `Nat.card` of an *infinite* type is the junk value `0`
(which is even); so one might worry that infinite leaves slip in vacuously. They cannot: the
`hham` field is unsatisfiable on an infinite vertex type (a Hamiltonian walk has finite support
yet must cover every vertex, and a demanded endpoint pair always exists; any two distinct
vertices for Hamilton-connectedness, one from each class of the *surjective* coloring for
laceability). Sentinel `colemanTree_finite` (`Sentinel.lean`) proves
`IsColemanTree G n → Finite V` outright, by induction up the welding tree; so `Nat.card` is
always the ordinary finite cardinality wherever the predicate holds. The `[Fintype V]` context
of Coleman's formalized theorem is therefore consistent with every layer of the tree.

**Source definition (verbatim).** Coleman et al. 2025, Definition 1.3, p. 3:
> "A transposition-like graph of rank 1 is a Hamiltonian-connected or Hamiltonian-laceable
> graph. For each integer n ≥ 2, a transposition-like graph of rank n is a weld of
> G₁, G₂, …, G_ell, where ell ≥ n and each G_i is a transposition-like graph of rank n − 1 with the
> same number of vertices."

The source's "Hamiltonian-laceable" presupposes a bipartite graph and *its* bipartition; our
rank-1 base makes that explicit as "laceable with respect to a proper surjective coloring",
the properness and surjectivity conditions express "the bipartition of a bipartite graph" when
the coloring is a free variable.

**In plain terms.** The predicate `IsColemanTree G r` says "`G` is a rank-`r` transposition-like
graph, and every rank-1 leaf of its build tree is a single vertex or even." It is defined the way
the source builds the class, by recursion on the rank. *Rank 1* (the leaves): any graph that is
Hamilton-connected, or Hamilton-laceable with respect to a proper and surjective 2-coloring,
subject to Thm 1.5's side condition that the leaf be a single vertex or of even order. *Rank
`r ≥ 2`*: `G` is (isomorphic to) a weld of `ell ≥ r` graphs, each itself carrying a rank-`(r−1)`
tree, with coherent matchings. The motivating instance: `CT_a` has rank `a`; it is the weld of
`a` copies of `CT_{a−1}` along the cosets "where does the symbol at position 0 go," recursing
down to `CT₁` = a single vertex. The §7 induction's other instance welds copies of
`CT_{a−1} □ B`, whose leaves are the single tree's rank-1 graphs `1 □ B ≅ B`. This is why
Thm 1.5's leaf condition ("even order") lands on `B` and drives the whole C2 reading.
**Faithfulness.** The leaf property and the even-order condition refer to the same welding tree, as required by the source phrase "during the welding process to form G." Properness and surjectivity make the source's bipartition explicit and prevent a vacuous Hamilton-laceability witness.

### 2.6 §5/§6 objects### 2.6 §5/§6 objects

#### D24: `BaseFamily`, `baseExchangeGraph` (`Sec5.lean:846,853`)

```lean
structure BaseFamily (α : Type u) [Fintype α] [DecidableEq α] where
  Base : Finset α → Prop
  exists_base : ∃ B, Base B
  exchange : ∀ {A B : Finset α} {e : α}, Base A → Base B → e ∈ A → e ∉ B →
      ∃ f ∈ B, f ∉ A ∧ Base (insert f (A.erase e))

def baseExchangeGraph {α : Type u} [Fintype α] [DecidableEq α] (B : BaseFamily α) :
    SimpleGraph {X : Finset α // B.Base X} :=
  SimpleGraph.fromRel (fun X Y => (X.val \ Y.val).card = 1 ∧ (Y.val \ X.val).card = 1)
```

**Mathematics.** A finite set system packaged by exactly the two **classical matroid basis
axioms**; (B1) some base exists, and (B2) one-sided exchange: if `A`, `B` are bases and
`e ∈ A \ B`, then some `f ∈ B \ A` makes `A − e + f` a base (Oxley, *Matroid Theory*, §1.2),
together with the *base-exchange graph*: vertices the bases, two bases adjacent when each has
exactly one element the other lacks.

**In plain terms.** No rank function, no independence axioms; just "bases" and the swap rule.
Small example: on the ground set `{1, 2, 3}`, let the bases be all singletons; exchange holds
trivially, and the base-exchange graph is a triangle. In §5 the ground set is the columns and the
bases are the realizable patterns of one row (Lemma 5.3); the swap rule is what Lemma 5.4's unit
transfer provides, and the base-exchange graph is then literally the row's quotient graph
(`rowQuotient_iso_baseExchange`). Packaging it this way makes A9 (Naddef–Pulleyblank) applicable
off the shelf: their theorem is about base-exchange graphs of matroids, and (B1)+(B2) is all a
matroid's bases satisfy; and all their proof uses.

**Source definition (verbatim).** Naddef–Pulleyblank 1981, §1, p. 297:
> "The graph G(P) of a polyhedron P is the graph whose nodes are the vertices of the polyhedron
> and which has an edge joining each pair of nodes for which the corresponding vertices of the
> polyhedron are adjacent, that is, joined by an edge of the polyhedron." … "the graph of a
> matroid basis polytope (the convex hull of the incidence vectors of the bases of a matroid)"

Two incidence vectors of bases are polytope-adjacent exactly when the bases differ by a single
exchange. Entry A9 documents the correspondence; our `baseExchangeGraph` is that graph
stated combinatorially.

**What to confirm.** That (B1)+(B2) is the standard basis axiomatization (it is; B2 here is the
one-sided exchange, which for finite systems of equicardinal sets is equivalent to the symmetric
version), and that the adjacency is the papers' "differ by a single exchange." The §5 row-pattern
family is proved to satisfy the structure by `rowPattern_baseFamily`.

#### D25: `CORE_global` (`Ledger.lean:103`)

```lean
def CORE_global : Prop :=
  ∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V) (col : V → Bool),
    IsInterchangeGraph G → IsProper2Coloring G col → IsSpanning2DPCOpposite G col
```

**Mathematics.** The CORE statement: every finite balanced-bipartite interchange graph is paired
2-disjoint-path-coverable for opposite demands. **Proved** (`core_global`, `Ledger.lean:110`) from `weak_ct_product` +
the §7 double induction; the reduction consumes it as a single proposition.

---

## 3. The seven cited axioms

These seven statements are the complete external mathematical trust surface beyond Lean's classical foundations. Each entry gives the verbatim Lean statement, a mathematical translation, the source quotation, its role in the proof, and a direction-of-error check.

Several statements carry explicit nonemptiness or cardinality guards because their sources use standing nondegeneracy conventions. The guards strengthen the hypotheses and every use in the proof supplies them. Sentinel lemmas record the relevant boundary cases.

### A4: `weak_ct_product_raw` (`Coleman.lean:365`): Brualdi 2006, Theorem 6.3.4 and §6.3

```lean
axiom weak_ct_product_raw {V : Type} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (col : V → Bool)
    (hIG : IsInterchangeGraph G) (hBB : IsProper2Coloring G col)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ ranks : List Nat, ranks ≠ [] ∧ (∀ a ∈ ranks, 2 ≤ a) ∧
      Nonempty (G ≃g CTProductGraph ranks)

-- Derived theorems:
theorem weak_ct_product_uncolored … :   -- canonical ranks, by the sort isomorphism
    ∃ ranks, CanonicalCTRanks ranks ∧ Nonempty (G ≃g CTProductGraph ranks) := …
theorem weak_ct_product … :             -- color-respecting classification
    ∃ ranks, CanonicalCTRanks ranks ∧
      ∃ e : G ≃g CTProductGraph ranks, ∀ v, CTProductColor ranks (e v) = col v := …
```

**Mathematics.** *Every bipartite interchange graph on at least 2 vertices is isomorphic to a nonempty Cartesian product of complete-transposition graphs whose ranks are at least 2.* The axiom gives the raw uncolored classification. Lean derives the canonical ordering and the color-respecting isomorphism.

**Source (verbatim).** Brualdi, *Combinatorial Matrix Classes* (2006), Theorem 6.3.4 (p. 298):
> "Let R = (r₁, r₂, …, r_m) and S = (s₁, s₂, …, s_n) be nonnegative integral vectors such that
> A(R,S) is nonempty and does not have any invariant positions. The following are equivalent:
> (i) G(R,S) is bipartite; (ii) G(R,S) does not have any cycles of length 3; (iii) m = n, and
> either R = S = (1, 1, …, 1) or R = S = (n − 1, n − 1, …, n − 1)."

**Source alignment.** Section 6.1 gives the invariant-block Cartesian-product decomposition. Theorem 6.3.4 classifies each nonempty invariant-free bipartite block as a permutation-matrix class or its complement, whose interchange graph is a complete-transposition graph. Trivial one-vertex factors drop from the product. The hypothesis `2 ≤ Fintype.card V` ensures that at least one nontrivial factor remains. Appendix A records the synthesis step by step.

**Guard.** A fully invariant one-vertex class corresponds to the empty product. The cardinality hypothesis excludes that case, and `one_vertex_class_not_equitable` tests the boundary.

**Where used.** `core_global` (`Ledger.lean:109`; guard discharged by a |V| < 4 vacuity branch)
and `interchange_bipartite_equitable` (`Coleman.lean:404`, the mechanized paper Prop 2.2).

**Direction-of-error.** Hypotheses = the book's standing setting (nonempty, and the degenerate
single-vertex case excluded) made explicit; conclusion is the book's representation restricted to
its nonempty-product cases. Sound.

**Derivation note.** Appendix A (one page) spells out the synthesis end to end; strip invariant
positions, factor into blocks, drop trivial factors, classify each bipartite block by
Theorem 6.3.4; so a referee can check the whole of A4 against the book in one sitting.

### A5: `invariantFree_nonbip_has_triangle` (`Sec5.lean:200`): Brualdi 2006, Thm 6.3.4 (ii)⟹(i) contrapositive

```lean
axiom invariantFree_nonbip_has_triangle {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hvar : ∀ i j, CellVaries r s i j)
    (hnb : ¬ ∃ col : MarginClass r s → Bool, ∀ M N, (flipGraph r s).Adj M N → col M ≠ col N) :
    ∃ M0 M1 M2 : MarginClass r s,
      (flipGraph r s).Adj M0 M1 ∧ (flipGraph r s).Adj M1 M2 ∧ (flipGraph r s).Adj M0 M2
```

**Mathematics.** *In a class with no invariant positions (every cell varies), a non-bipartite
interchange graph contains a triangle.*

**Source (verbatim).** Brualdi, *Combinatorial Matrix Classes* (2006), Theorem 6.3.4 (p. 298):
> "Let R = (r₁, r₂, …, r_m) and S = (s₁, s₂, …, s_n) be nonnegative integral vectors such that
> A(R,S) is nonempty and does not have any invariant positions. The following are equivalent:
> (i) G(R,S) is bipartite; (ii) G(R,S) does not have any cycles of length 3; (iii) m = n, and
> either R = S = (1, 1, …, 1) or R = S = (n − 1, n − 1, …, n − 1)."

The implication ¬(ii) ⟹ ¬(i) gives a 3-cycle from non-bipartiteness under the book's exact
hypothesis "no invariant positions," which is `hvar`. No nonemptiness guard is needed: for
`m,n ≥ 1`, `hvar` itself supplies a matrix, and in
every other degenerate case (m = 0, n = 0, or an empty class) the graph admits the trivial proper
coloring, so `hnb` fails and the axiom claims nothing.

**Where used.** Paper Lemma 5.10 (`rowQuotient_nonbip`, the non-bipartite quotient) via
`nonbip_has_triangle`.

**Direction-of-error.** Hypothesis is the book's, stated verbatim at matrix level; non-bipartite
stated as "no proper 2-coloring exists" (definitionally bipartiteness's negation). Sound.

### A6: `active_prime_cell_varies` (`Sec5.lean:189`): Brualdi–Manber 1983, Theorem 9

```lean
axiom active_prime_cell_varies {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hprime : ¬ IsDecomposable (Brualdi.flipGraph r s))
    (hne : Nonempty (MarginClass r s)) :
    ∀ i j, CellVaries r s i j
```

**Mathematics.** *For a nonempty fully-active class whose interchange graph is Cartesian-prime,
no position is invariant; every cell varies.* (Paper Lemma 5.2, "pivot freedom".)

**Source.** Brualdi & Manber, *Prime interchange graphs of classes of matrices of zeros and ones*,
Journal of Combinatorial Theory, Series B 35(2) (1983) 156–170, Theorem 9, p. 169:
> "Let 1 ≤ rᵢ ≤ n−1, 1 ≤ sⱼ ≤ m−1. Then G(R,S) is prime if and only if 𝔄(R,S) has no invariant
> positions."
**Source alignment.** The contrapositive used here says that an invariant position yields a nontrivial Cartesian decomposition. Brualdi–Manber's Theorem 1 constructs the factors as interchange graphs. Their activity bounds make both factors nontrivial. Row and column permutations remove the sources' monotonicity convention without changing invariant positions or decomposability.

**Guard.** `IsActive` does not imply feasibility. The explicit `Nonempty` hypothesis matches the source's standing nonempty-class convention. The sentinel `active_empty_class_exists` tests this distinction.

**Where used.** `nonbip_has_triangle` (`hne` derived from non-bipartiteness), the §5.9 Stage-B
uniqueness contradiction, and the Lemma-5.10 quotient wiring (`pivotBufferData_of_row_line`); the
latter two with explicit matrices in scope.

**Direction-of-error.** Hypotheses = source's active bounds + primeness + its standing
nonemptiness; conclusion = source's invariant-freeness. Sound.

### A7: `invariantFree_card_ge` (`Ledger.lean`): Brualdi 2006 §9.13

```lean
axiom invariantFree_card_ge {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hact : IsActive r s) (hIF : ∀ i j, CellVaries r s i j)
    (hne : Nonempty (MarginClass r s)) :
    (m - 1) * (n - 1) + 1 ≤ Fintype.card (MarginClass r s)

-- Derived theorem:
theorem prime_class_card_ge … :=
  invariantFree_card_ge r s hact (active_prime_cell_varies r s hact hprime hne) hne
```

**Mathematics.** *A nonempty active class with no invariant positions has at least `(m−1)(n−1)+1` matrices.* The derived theorem `prime_class_card_ge` first applies A6 to obtain invariant-freeness and then applies this axiom.

**Source (verbatim).** Brualdi, *Combinatorial Matrix Classes* (2006), §9.13,
pp. 491–493, presenting Brualdi–Hartfiel–Hwang, *On assignment functions*, Linear and Multilinear
Algebra 19 (1986) 203–219 (the book's ref [31]). The `(R,S)`-assignment polytope `Ω_{R,S}` is
defined by display (9.57): all real `m×n` matrices with `0 ≤ x_ij ≤ 1` and margins `R, S`. Then:
> **Theorem 9.13.11**: "Let R = (r₁, r₂, …, r_m) and S = (s₁, s₂, …, s_n) be positive integral
> vectors satisfying (9.56) [equal sums]. Then Ω_{R,S} ≠ ∅ if and only if A(R,S) ≠ ∅. In fact,
> Ω_{R,S} is the convex hull of the matrices in A(R,S)."
and, in-text with its footnote 26 (pp. 492–493):
> "Assuming that A(R,S) has no invariant 1's, the dimension of the polytope Ω_{R,S} equals
> (m−1)(n−1), and hence Ω_{R,S} has at least (m−1)(n−1)+1 extreme points."
> Footnote 26: "So |A(R,S)| ≥ (m−1)(n−1)+1 if R and S are positive integral vectors such that
> the class A(R,S) is nonempty and has no invariant 1's."
**Hypothesis alignment.** `IsActive` implies that the margins are positive integral vectors. A member of the margin class supplies equal sums and nonemptiness. Requiring every cell to vary is stronger than the source's condition that there are no invariant 1s. The axiom therefore assumes at least the source hypotheses and concludes exactly the bound in footnote 26.

**Guard.** The explicit `Nonempty` hypothesis excludes active but infeasible margins.

**Where used.** Via the derived `prime_class_card_ge`: `small_interchange_MH` (§6, the ≤6-vertex
dispatch), with `hne` from the ambient nonempty graph.

**Direction-of-error.** The hypotheses are stronger than the source's, and the conclusion is
exactly the source's cardinality bound. Sound.

### A8: `flipGraph_connected` (`Coleman.lean:262`): Ryser 1957

```lean
axiom flipGraph_connected {m n : ℕ} (r : Fin m → ℕ) (s : Fin n → ℕ)
    (hne : Nonempty (MarginClass r s)) : (Brualdi.flipGraph r s).Connected
```

**Mathematics.** *A nonempty class is connected under interchanges.* (Ryser's classical theorem;
mathlib's `Connected` = preconnected + nonempty, hence the `hne`.)

**Source (verbatim).** Ryser, *Combinatorial properties of matrices of zeros and ones*, Canadian Journal of Mathematics 9 (1957) 371–377, §3:
> **Theorem 3.1** (p. 374): "Let A and A* be two m by n matrices composed of 0's and 1's,
> possessing equal row sum vectors and equal column sum vectors. Then A is transformable into A*
> by a finite number of interchanges."
Ryser's interchange is the 2×2 switch defined in D3. The source quantifies over two members of the same margin class. The `Nonempty` hypothesis supplies mathlib's additional nonemptiness requirement for `Connected`.

**Where used.** §5's quotient-walk lifting (fiber connectivity via quotient connectivity).

**Direction-of-error.** `hne` matches the source's nonempty class; conclusion is the source's.
Sound.

### A9: `naddef_pulleyblank_baseExchange` (`Sec5.lean:861`): Naddef–Pulleyblank 1981, Thm 3.3.1 + Cor 3.3.2

```lean
axiom naddef_pulleyblank_baseExchange {α} [Fintype α] [DecidableEq α] (B : BaseFamily α) :
    ¬ (∃ col : {X : Finset α // B.Base X} → Bool,
        ∀ X Y, (baseExchangeGraph B).Adj X Y → col X ≠ col Y) →
      IsHamConnected (baseExchangeGraph B)
```

**Mathematics.** *The base-exchange graph of a matroid (any (B1)+(B2) base family, D24) is, when
non-bipartite, Hamilton-connected.*

**Source (verbatim).** Naddef & Pulleyblank,
*Hamiltonicity and combinatorial polyhedra*, JCTB 31 (1981) 297–312:
> **Theorem 3.3.1** (p. 309): "Let X be the set of incidence vectors of all bases of a matroid M.
> Then X is a combinatorial set."
> **Corollary 3.3.2** (p. 310): "The graph of B(M) is either a hypercube or else is hamilton
> connected."
(`B(M)` is the convex hull of the incidence vectors of the bases, defined just above on p. 309;
its graph is the matroid basis graph. Provenance honesty: the paper notes Thm 3.3.1 was "known to
Jack Edmonds in the early 1970s" and first "appears in print in Hausmann and Korte", with the
printed proof credited to them; the Hamilton-connectedness corollary is Naddef–Pulleyblank's.)
Hypercubes are bipartite, so non-bipartite ⟹ Hamilton-connected.

**Supporting source (verbatim).**
Hausmann & Korte, *Colouring criteria for adjacency on 0–1-polyhedra*, Mathematical Programming
Study 8 (1978) 106–127; the printed source N–P credit for Thm 3.3.1 (scanned PDF; OCR repaired
against surrounding text):
> **Theorem 4.3** (p. 117): "Let (E, 𝒮) be a matroid. Then two distinct 𝒮-sets F₁, F₂ are
> adjacent with respect to (E, 𝒮) iff (i) |F₁ Δ F₂| = 1, or (ii) |F₁ Δ F₂| = 2 and F₁ ∪ F₂ ∉ 𝒮."
For bases, `baseFamily_card_eq` proves that all feasible sets have the same cardinality. The first adjacency alternative cannot occur, and the second reduces to exchange of one element. Nonempty, equicardinal families satisfying the exchange axiom are exactly matroid basis families. This establishes the bridge from D24 to the source's matroid bases.

**Where used.** Corollary 5.5 (`rowQuotient_hamConnected`): the row-pattern quotient is a matroid
base-exchange graph (by the *proved* `rowPattern_baseFamily`), non-bipartite by paper Lemma 5.10, hence
Hamilton-connected.

**The `BaseFamily` to matroid-bases bridge.** The theorem `baseFamily_card_eq` proves from (B2)
that all bases of a `BaseFamily` are equicardinal. Nonempty, equicardinal families with the
exchange property give the classical basis-family presentation of a matroid (Oxley §1.2).

**Direction-of-error.** Degenerate check: (B1) forces the graph nonempty; a one-base family gives
K₁, which is vacuously Hamilton-connected; but K₁ also admits a (vacuous) proper coloring, so
the hypothesis fails and no claim is made. Sound; no guard needed.

### A10: `johnson_isMH` (`Ledger.lean:240`): Alspach 2013

```lean
axiom johnson_isMH (n k : ℕ) (hk : 0 < k) (hkn : k < n) : IsMH (Brualdi.Johnson.Jgraph n k)
```

**Mathematics.** *Johnson graphs J(n,k), 0 < k < n, are maximally Hamiltonian.*

**Source (verbatim).** Alspach, *Johnson graphs are
Hamilton-connected*, Ars Mathematica Contemporanea 6 (2013) 21–23:
> **Theorem 1.1** (p. 21): "The Johnson graph J(n, k) is Hamilton-connected for all n ≥ 1."
with his §1 conventions on the same page: "The Johnson graph J(n, k), 0 ≤ k ≤ n, is defined by
letting the vertices correspond to the k-subsets of an n-set, where two vertices are adjacent if
and only if the corresponding k-subsets have exactly k − 1 elements in common," and "The graph
with a single vertex is trivially Hamilton-connected." So his range is all `0 ≤ k ≤ n, n ≥ 1`;
the axiom's `0 < k < n` is a strict sub-range.

**Source alignment.** The axiom restricts Alspach's range to `0 < k < n` and concludes `IsMH`, which is weaker than Hamilton-connectedness.

**Where used.** `reduction_base` (`Ledger.lean:765`), the Johnson half of the base branch.

**Direction-of-error.** Conclusion strictly weaker than the source's. Sound-conservative. (J(n,k)
with 0 < k < n is nonempty and, being Hamilton-connected, non-vacuously MH for card ≥ 2; K₁ cases
are vacuous but true.)

---

## 4. Cross-cutting faithfulness notes

### 4.1 Permutation equivariance

Brualdi 2006 and Brualdi–Manber state several results for nonincreasing margin vectors, while Lean represents margins as arbitrary functions. Row and column permutations preserve invariant positions, primeness, feasibility, and the interchange relation. Permuting the margins induces an isomorphism of interchange graphs, so the translation is sound. Theorem 6.3.4 is already stated without a sorting hypothesis.

### 4.2 Naming conventions

`IsProper2Coloring` asserts properness only. Equal color-class sizes are expressed separately by `IsEquitableBipartite`. The laceable disjunct of `IsMH` carries its own properness and surjectivity guards.

### 4.3 Demand encodings

The pairwise opposite-colored demand encoding is equivalent to the sources' `S ⊆ V₁, T ⊆ V₂` encoding by relabeling endpoints within each pair and reversing paths when necessary. Entries D17 and D18 give the formal definitions.

### 4.4 Nonemptiness and vacuity

Universal hypotheses may hold vacuously on empty types, while existential conclusions fail. The formal statements therefore make the sources' standing conventions explicit. They require nonempty margin classes where needed and sufficient graph cardinality for the demands under consideration. The properness and surjectivity conditions in `IsMH` prevent a constant coloring from making laceability vacuous. The sentinel lemmas test these boundary cases.

### 4.5 Scope of the kernel check

A successful build and the axiom trace certify that the seven cited statements, as encoded here, imply `brualdi_MH` in classical logic. They do not certify that the encodings match the sources or that the cited results are correct. The source quotations support the first comparison; ordinary mathematical review addresses the second.

---

## 5. Sanity sentinels

`Sentinel.lean`, with one result in `Sec4.lean`, tests instances that the definitions must accept or reject.

- `isInterchangeGraph_flipGraph`: `Sentinel.lean:17`: the main hypothesis class is inhabited
  (theorem not vacuous).
- `isMH_edgeless_rejected`: `Sentinel.lean:25`: `IsMH` rejects the edgeless 2-vertex graph
  (theorem not vacuous).
- `isMH_const_blocked_on_edge`: `Sentinel.lean:41`: constant colorings blocked on any edge.
- C₄ not Hamilton-connected: `Sec4.lean`: §4's non-bipartiteness hypotheses are load-bearing.
- `active_empty_class_exists`: `Sentinel.lean:56`: `IsActive` ⇏ nonempty; A6/A7's `Nonempty`
  guards load-bearing.
- `one_vertex_class_not_equitable`: `Sentinel.lean:76`: A4's `2 ≤ card` guard load-bearing.
- `E2_spanning2_but_not_laceable`: `Sentinel.lean:105`: the demand-cardinality guard is
  load-bearing.
- `hamPath_isPath`: `Sentinel.lean`: D5: Hamilton walks are covering paths,
  machine-checked.
- `colemanTree_finite`: `Sentinel.lean`: D23: no infinite leaf; `Nat.card` always
  ordinary.
- `edgeless_two_not_interchangeGraph`: `Sentinel.lean`: D8:
  `IsInterchangeGraph` excludes E₂ (uses A8).
- `edgeless_two_not_baseClass`: `Sentinel.lean`: D11: the bundled guard makes
  `IsBaseClass` reject E₂ definitionally.
- `brualdi_MH_paper`: `Ledger.lean`: §1: the paper-facing corollary, isolated.
- `baseFamily_card_eq`: `Sentinel.lean`: A9: every `BaseFamily` has equicardinal
  bases = the matroid basis axioms.

---

## Appendix A: the A4 derivation note (Brualdi §6.3 → `weak_ct_product_raw`, in one page)

A4 is the one axiom that is a *synthesis*; Theorem 6.3.4 read together with §6.3's product
structure; rather than a single displayed statement. This appendix writes the synthesis out as
one compact argument, with each step pinned to the book, so the human comparison for A4 is a
line-by-line comparison against a single page rather than a reconstruction from scattered
references. Throughout, `A(R,S)` is nonempty, `G = G(R,S)` has at least two vertices, and `G` is
bipartite (it carries a proper 2-coloring). The claim to verify is exactly the axiom's
conclusion: `G` is isomorphic to a Cartesian product of complete-transposition graphs `CT_a`
over a **nonempty** list of ranks, **each rank ≥ 2**.

**Step 1; factor across invariant positions (§6.3, around Theorem 6.3.5, p. 299).** An
*invariant position* is a cell whose entry is the same in every matrix of the class. The
invariant positions cut the class into blocks: `A(R,S)` decomposes as a product of the block
classes, interchanges act within blocks, and the book's display gives the interchange graph as
the Cartesian product of the block interchange graphs (`G(R,S) = G(R₁,S₁) × G(R₂,S₂)`, iterated;
uniqueness of such factorizations is Sabidussi's theorem, quoted there). Each resulting block
class has no invariant positions of its own.

**Step 2; drop the trivial factors.** A block whose class is a single matrix contributes a
one-vertex graph, the identity for the Cartesian product, and is omitted. Since `G` has at
least two vertices (by the axiom's `hcard` guard), at least one
nontrivial block survives, so the factor list is nonempty. (A fully invariant class would leave
the *empty* product; the one-vertex case the guard excludes.)

**Step 3; factors of a bipartite product are bipartite.** Fixing all other coordinates embeds
each factor as a subgraph of `G`, and subgraphs of bipartite graphs are bipartite. So every
surviving block has a bipartite, invariant-free, nonempty interchange graph on ≥ 2 vertices.

**Step 4; classify each block (Theorem 6.3.4, p. 298, quoted verbatim in the A4 entry).** For a
nonempty invariant-free class, `G` bipartite forces `m = n` with `R = S = (1,…,1)` or
`R = S = (n−1,…,n−1)`. In the first case the matrices are the `n × n` permutation matrices and
an interchange multiplies by a transposition, so the block graph is `CT_n`; the graph on the
permutations of `n` letters joining `σ, τ` when `σ⁻¹τ` is a transposition, which is `D19`'s
`CompleteTranspositionGraph n` verbatim. In the second case complementation `A ↦ J − A` is a
bijection onto the first case carrying interchanges to interchanges, so the block graph is again
`CT_n`. A nontrivial block has at least two matrices, i.e. `n! ≥ 2`, i.e. `n ≥ 2`.

**Conclusion.** `G` is isomorphic to a Cartesian product of graphs `CT_a` over a nonempty rank
list with every `a ≥ 2`. This is exactly the statement of `weak_ct_product_raw`. Lean proves the
canonical reordering of the factor list and the color-respecting choice of isomorphism. The
reader can compare each step above with the cited pages of Brualdi's book.
