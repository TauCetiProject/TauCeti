# Roadmap: universal covers

Mathlib already has a substantial covering-space toolkit; what it lacks is the
**universal cover construction itself** and the **deck transformation group**, which sit
in PRs that stalled or died upstream. We are not waiting: **port the missing
construction into `TauCeti/`, sorry-free and attributed, consume the rest from Mathlib,
and build the theory of covers on top here.**

Suggested home: `TauCeti/AlgebraicTopology/UniversalCover/`. Original roadmap content:
the gist <https://gist.github.com/kim-em/70e1762ab143b88605c699059769111c>.

## Standing hypotheses and basepoint policy

The universal cover of `X` (based at `x₀`) requires `X` to be **path-connected**,
**locally path-connected**, and **semilocally simply connected**; based paths from `x₀`
only ever see the path component of `x₀`, so `proj` is surjective only under
path-connectedness (or one builds the cover of `pathComponent x₀`). State these as
explicit hypotheses, never bake them in.

Decide a **basepoint policy up front**, because the classification theorems are sensitive
to it: distinguish *pointed* covers (with a chosen lift `e₀` of the basepoint) from
*unpointed* covers, and build the API for basepoint change along a path, conjugation of
subgroups under basepoint change, and isomorphism of covers over `X`. Also fix a
left/right convention for path concatenation and deck-map composition early; several
target isomorphisms below are only correct up to `ᵐᵒᵖ` depending on it.

## What Mathlib already has (consume)

- **Covering maps:** `Mathlib/Topology/Covering/Basic.lean` (`IsCoveringMap`,
  `IsCoveringMapOn`), and **quotient covering maps** `…/Covering/Quotient.lean`
  (`IsQuotientCoveringMap`, properly-discontinuous/free `SMul` results); reuse these for
  `UniversalCover/H` instead of re-deriving quotient-cover facts.
- **Lifting:** `Mathlib/Topology/Homotopy/Lifting.lean`, with path lifting *and* **general
  homotopy lifting** `IsCoveringMap.liftHomotopy : C(I × A, E)` for an arbitrary parameter
  space `A`, the `monodromy_theorem`, the **monodromy functor**
  `IsCoveringMap.monodromyFunctor : FundamentalGroupoid X ⥤ Type _`, and the **lifting
  criterion** (two forms; see Stage 2).
- **Fundamental groupoid / group:** `Mathlib/AlgebraicTopology/FundamentalGroupoid/*`,
  covering `FundamentalGroupoid`, `FundamentalGroup`, homotopy-invariance/functoriality
  (`InducedMaps.lean`: `homotopicMapsNatIso`, `equivOfHomotopyEquiv`), `SimplyConnected`.
- **Homotopy groups:** `Mathlib/Topology/Homotopy/HomotopyGroup.lean` (`Ω^N`,
  `HomotopyGroup`) and `Mathlib/Topology/Covering/HomotopyGroup.lean`.
- **Galois-category abstraction:** `Mathlib/CategoryTheory/Galois/IsFundamentalgroup.lean`
  (`IsFundamentalGroup`, `toAutMulEquiv : G ≃* Aut F`), an alternative lens on the
  classification, via fibre functors.
- **Circle:** `Mathlib/Topology/Covering/AddCircle.lean`
  (`isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p)`): `ℝ` covers `S¹`.

## What is missing (port / build here)

- [mathlib4#31576](https://github.com/leanprover-community/mathlib4/pull/31576)
  (*the homotopy-class fibres are discrete*): **closed, unmerged**.
- [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
  (*universal cover construction*): open, depends on the closed #31576.
- [mathlib4#40135](https://github.com/leanprover-community/mathlib4/pull/40135)
  (*Deck transformation group*): open.

Plus, on top of these: the subgroup ↔ cover Galois correspondence, regular covers and the
deck group `N(H)/H`, and the higher-homotopy API.

---

## Stage 0: port the foundations into `TauCeti/`

Bring the existing, human-written construction into this library, sorry-free; credit the
original authors and source PR in each file.

1. **Discreteness of homotopy-class fibres** (from #31576). For `X` semilocally simply
   connected and locally path-connected, the **fibres** of "based paths modulo
   endpoint-preserving homotopy" over a fixed endpoint are **discrete** (this is what
   makes `proj` a covering map and gives the sheet decomposition). Note: the total space
   is *not* discrete in general; only the fibres are. This died upstream, so it lives
   here.
2. **The based-path space and the cover** (from #38292), under
   `[PathConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]`:
   - `BasedPath x₀` and the path-component machinery of `endpoint ⁻¹' U`;
   - `UniversalCover x₀` as `BasedPath x₀` modulo endpoint-preserving homotopy, with the
     quotient topology, plus `proj` and the sheet decomposition;
   - `IsCoveringMap proj`, `PathConnectedSpace`, `SimplyConnectedSpace (UniversalCover x₀)`,
     and the universal lifting property `existsUnique_continuousMap_lifts`.
3. **The π₁ action** (from #38292, `Action.lean`): the action of `π₁(X, x₀)` on
   `UniversalCover x₀`, with `FaithfulSMul`, `ContinuousConstSMul`, the local-disjointness
   predicate, packaged as `UniversalCover.isQuotientCoveringMap` (built on Mathlib's
   `IsQuotientCoveringMap`).
4. **Deck transformation group** (from #40135): `Deck p` as a `Subgroup (E ≃ₜ E)` for
   `p : E → X`, with the upstream `MulAction (X ≃ₜ X) X` / `FaithfulSMul` /
   `ContinuousConstSMul` instances; subgroup transfer gives `Deck p` its `Group`,
   `MulAction E`, `FaithfulSMul E`, `ContinuousConstSMul E`.

## Stage 1: close out the universal cover

5. **`Deck(proj) ≃* π₁(X, x₀)`.** The isomorphism connecting Stage 0.3 and 0.4. Once it lands,
   `UniversalCover x₀ / π₁(X, x₀) ≃ X` follows (via Mathlib's `IsQuotientCoveringMap`).
   ⚠ Convention check first: depending on the chosen left/right action and deck-map
   composition order, the correct statement may be
   `Deck(proj) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ`. Pin the convention before stating the
   target.

## Stage 2: lifting criterion and Galois correspondence

6. **General lifting criterion, already in Mathlib.** Consume
   `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`
   (`Mathlib/Topology/Homotopy/Lifting.lean`). State it in its Lean-shaped form, with the
   real hypotheses: `[PathConnectedSpace A] [LocPathConnectedSpace A]`, basepoints
   `a₀ : A`, `e₀ : E` with `he : p e₀ = f a₀`, and the precise subgroup-inclusion
   condition (the `f_*(π₁ A) ⊆ p_*(π₁ E)` shorthand hides this). Also note the
   simply-connected special case `existsUnique_continuousMap_lifts`.
7. **Cover associated to `H ≤ π₁(X, x₀)`.** `UniversalCover x₀ / H` with the quotient
   basepoint `⟦e₀⟧` is a *pointed* connected cover; prove `p_*(π₁(–)) = H` for that
   pointed cover. Separately, prove how the recovered subgroup transforms (by conjugacy)
   under basepoint change. With (6) this is the existence half of the correspondence.
8. **Galois correspondence: get the bookkeeping right.** Two distinct theorems:
   - **pointed** connected covers of `(X, x₀)` (with chosen lift `e₀`) ↔ **subgroups** of
     `π₁(X, x₀)`;
   - **unpointed** connected covers ↔ **conjugacy classes** of subgroups.

   For the cover attached to `H`, the deck group is `N(H)/H`; it is a **regular**
   (normal/Galois) cover iff `H ◁ π₁(X, x₀)`, and then the deck group is `π₁(X, x₀)/H`.
   Add milestones for the normalizer quotient and transitivity of the deck action on
   fibres before the regular-cover theorem. (Local path-connectedness of `X` is needed for
   the correspondence to be onto.)
   - *Alternative lens:* phrase the classification of connected covers via transitive
     `π₁(X)`-sets / the monodromy functor (`monodromyFunctor`,
     `Galois/IsFundamentalgroup`), with disconnected covers as functors out of the
     fundamental groupoid. Worth paving as a second route.

## Stage 3: higher homotopy

Cube/homotopy lifting is **not** the obstacle; Mathlib's `IsCoveringMap.liftHomotopy`
already lifts `C(I × A, E)` for arbitrary `A`. The real prerequisites are the
higher-homotopy-group API:

9.  **`π_n` API:** functoriality (`π_n` of a continuous map), pointed maps, the
    boundary-relative homotopy API on `Ω^N`, (pre)connectedness of cubes and cube
    boundaries for `n ≥ 2`, and basepoint-change isomorphisms. Mathlib's `HomotopyGroup`
    is thin here; this is the bulk of the work.
10. **`p_* : π_n(X̃) ≅ π_n(X)` for `n ≥ 2`**, any cover. With (9) and Mathlib's homotopy
    lifting, the proof mirrors the `π₁` injectivity argument with `S^n` for `S^1`.

## Stage 4: applications

11. `π_n(S¹) = 0` for `n ≥ 2` (universal cover `ℝ` is contractible).
12. `π₁(S¹) ≅ ℤ`, built from `AddCircle.isCoveringMap_coe` (`ℝ → S¹`) and deck
    transformations. (Mathlib has the covering map but, as far as the pin shows, not the
    `π₁ ≅ ℤ` statement, so this is an application target, not a reconciliation.)
13. `π_n(Tᵏ)`, `π₁(RPⁿ)`, `K(G, 1)` spaces.

## Ordering

Stage 0 first: a careful port that unblocks everything. Then Stage 1 (5), then Stage 2
(7)/(8); the basepoint/conjugacy bookkeeping is the subtle part there, not the topology.
Stage 3 is a larger, separable track, but lighter than it looks now that homotopy lifting
is available; the cost is the `π_n` API, not lifting. As each milestone's prerequisite
*types* exist in `TauCeti/`, state the milestone in `Targets.lean` (with `sorry`) and
hand it to the AIs to discharge.

## Acknowledgements

This roadmap builds directly on earlier discussions on the [Lean
Zulip](https://leanprover.zulipchat.com/), and would not have been possible without them:

- [#Is there code for X? > Universal cover of a topological space](https://leanprover.zulipchat.com/#narrow/channel/217875-Is%20there%20code%20for%20X%3F/topic/Universal%20cover%20of%20a%20topological%20space)
  (Laura Monk, Kim Morrison, Michael Rothgang, Damiano Testa, and others), where the
  universal-cover work was consolidated into mathlib4#38292.

Thanks to everyone who contributed to that discussion, and to the authors of
mathlib4#31576, mathlib4#38292, and mathlib4#40135.
