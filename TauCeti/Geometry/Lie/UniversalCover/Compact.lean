/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.Geometry.Lie.UniversalCover

import TauCeti.AlgebraicTopology.UniversalCover.Compact
import TauCeti.Geometry.Lie.Adjoint.Compact
import TauCeti.Geometry.Lie.Perfect
import TauCeti.Geometry.Manifold.Topology
import TauCeti.MeasureTheory.Group.RealCharacter

/-!
# Weyl's theorem on compact semisimple Lie groups

**Weyl's theorem**: the universal covering group of a compact Lie group `G` whose Lie algebra has
trivial centre, which for compact `G` means that its Lie algebra is semisimple, is compact, and
the fundamental group of `G` is finite.

The theorem is proved in a local form. Let `G` be a connected finite-dimensional real Lie group
with perfect Lie algebra, `⁅𝔤, 𝔤⁆ = 𝔤`, and `f : G →* K` a homomorphism to a compact group which
is a local homeomorphism, such as a covering homomorphism. Then `G` is compact and the kernel of
`f` is finite. Indeed the kernel is a discrete central subgroup of `G` with compact quotient, and
`G` has no nonzero continuous homomorphism to `ℝ` because its Lie algebra is perfect
(`MonoidHom.eq_one_of_continuous_of_derivedSeries_one_eq_top_real`); a central extension of a
compact group by a discrete group without real characters is compact with finite kernel
(`MonoidHom.compactSpace_of_isLocalHomeomorph_of_forall_continuous_eq_one`).

For the universal covering group `UniversalCover (1 : G)` of a compact Lie group `G`, the
covering projection is such a homomorphism, and the Lie algebra of the cover is that of `G`
(`TauCeti.UniversalCover.lieEquivProjHom`). The Lie algebra of a compact Lie group is perfect
exactly when its centre is trivial (`TauCeti.Lie.derivedSeries_one_eq_top_iff_center_eq_bot`). A
compact universal cover has finite fundamental group
(`TauCeti.UniversalCover.finite_fundamentalGroup_of_compactSpace`).

The circle shows that the hypothesis on the centre is needed: its Lie algebra is abelian, its
universal cover `ℝ` is not compact, and its fundamental group `ℤ` is infinite.

## Main results

* `MonoidHom.compactSpace_of_isLocalHomeomorph_of_derivedSeries_one_eq_top`,
  `MonoidHom.finite_ker_of_isLocalHomeomorph_of_derivedSeries_one_eq_top`: a connected Lie group
  with perfect Lie algebra that is locally homeomorphic to a compact group by a homomorphism is
  compact, and the homomorphism has finite kernel.
* `TauCeti.UniversalCover.compactSpace_of_center_eq_bot`: **Weyl's theorem**, the universal
  covering group of a compact Lie group whose Lie algebra has trivial centre is compact.
* `TauCeti.Lie.finite_fundamentalGroup_of_center_eq_bot`: such a group has finite fundamental
  group.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V.
* J. Hilgert, K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer, 2012, Chapter 12.
-/

public section

open LieAlgebra
open scoped ContDiff Manifold

namespace MonoidHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [ConnectedSpace G]
  {K : Type*} [Group K] [TopologicalSpace K] [SeparatelyContinuousMul K] [CompactSpace K]

/-- **A connected Lie group with perfect Lie algebra, locally isomorphic to a compact group, maps
to it with finite kernel.** If `f : G →* K` is a local homeomorphism, `K` is compact, and the Lie
algebra of `G` is perfect, then the kernel of `f` is finite. -/
theorem finite_ker_of_isLocalHomeomorph_of_derivedSeries_one_eq_top (f : G →* K)
    (hf : IsLocalHomeomorph f) (h : derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤) :
    Finite f.ker :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace H G
  f.finite_ker_of_isLocalHomeomorph_of_forall_continuous_eq_one hf fun F hF ↦
    F.eq_one_of_continuous_of_derivedSeries_one_eq_top_real hF h

/-- **A connected Lie group with perfect Lie algebra that is locally isomorphic to a compact group
is compact.** If `f : G →* K` is a local homeomorphism, `K` is compact, and the Lie algebra of `G`
is perfect, then `G` is compact. -/
theorem compactSpace_of_isLocalHomeomorph_of_derivedSeries_one_eq_top (f : G →* K)
    (hf : IsLocalHomeomorph f) (h : derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤) :
    CompactSpace G :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace H G
  f.compactSpace_of_isLocalHomeomorph_of_forall_continuous_eq_one hf fun F hF ↦
    F.eq_one_of_continuous_of_derivedSeries_one_eq_top_real hF h

end MonoidHom

namespace TauCeti.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

/-- The Lie algebra of the universal covering group of a compact Lie group whose Lie algebra has
trivial centre is perfect: it is the Lie algebra of `G`. -/
private theorem derivedSeries_one_eq_top_of_center_eq_bot [IsTopologicalGroup G]
    [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
    (h : center ℝ (LeftInvariantDerivation I G) = ⊥) :
    derivedSeries ℝ (LeftInvariantDerivation I (UniversalCover (1 : G))) 1 = ⊤ := by
  let e := (lieEquivProjHom I G).symm
  rw [← LieIdeal.derivedSeries_map_eq 1 (f := e.toLieHom) e.surjective,
    (Lie.derivedSeries_one_eq_top_iff_center_eq_bot (I := I)).mpr h,
    ← e.toLieHom.idealRange_eq_map, e.toLieHom.idealRange_eq_top_of_surjective e.surjective]

/-- **Weyl's theorem.** The universal covering group of a compact Lie group whose Lie algebra has
trivial centre, for instance one with semisimple Lie algebra (`LieAlgebra.center_eq_bot`), is
compact. -/
theorem compactSpace_of_center_eq_bot (h : center ℝ (LeftInvariantDerivation I G) = ⊥) :
    CompactSpace (UniversalCover (1 : G)) :=
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  have : SemilocallySimplyConnectedSpace G := I.semilocallySimplyConnectedSpace G
  MonoidHom.compactSpace_of_isLocalHomeomorph_of_derivedSeries_one_eq_top _
    isCoveringMap_projHom.isLocalHomeomorph (derivedSeries_one_eq_top_of_center_eq_bot h)

end TauCeti.UniversalCover

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

/-- **A compact Lie group whose Lie algebra has trivial centre has finite fundamental group**, for
instance one with semisimple Lie algebra (`LieAlgebra.center_eq_bot`). -/
theorem finite_fundamentalGroup_of_center_eq_bot
    (h : center ℝ (LeftInvariantDerivation I G) = ⊥) : Finite (FundamentalGroup G 1) :=
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  have : SemilocallySimplyConnectedSpace G := I.semilocallySimplyConnectedSpace G
  have := UniversalCover.compactSpace_of_center_eq_bot h
  UniversalCover.finite_fundamentalGroup_of_compactSpace 1

end TauCeti.Lie
