/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra

/-!
# Lie algebras of subgroup preimages and homomorphism kernels

For a smooth homomorphism of finite-dimensional real Lie groups, taking the Lie algebra of
a closed subgroup commutes with taking its preimage. In particular, the Lie algebra of a
homomorphism kernel is the kernel of the induced Lie-algebra homomorphism. Neither group is
required to be connected.

## Main results

* `TauCeti.Lie.lieSubalgebraOfSubgroup_comap`: the Lie algebra of a closed-subgroup preimage.
* `TauCeti.Lie.lieSubalgebraOfSubgroup_ker`: the Lie algebra of a homomorphism kernel.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Theorem 3.7(4) and Corollary 3.30.
-/

public section

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E'] [LieGroup I' ∞ G'] [T2Space G']

/-- The Lie algebra of a closed subgroup's preimage is the preimage of its Lie algebra
under the Lie map. -/
theorem lieSubalgebraOfSubgroup_comap (f : ContMDiffMonoidMorphism I I' ∞ G G') {K : Subgroup G'}
    (hK : IsClosed (K : Set G')) :
    lieSubalgebraOfSubgroup (I := I) (K.comap f.toMonoidHom) =
      (lieSubalgebraOfSubgroup (I := I') K).comap (lieMap f) := by
  ext X
  rw [mem_lieSubalgebraOfSubgroup (hK.preimage f.contMDiff_toFun.continuous),
    LieSubalgebra.mem_comap, mem_lieSubalgebraOfSubgroup hK]
  simp only [Subgroup.mem_comap, ContMDiffMonoidMorphism.coe_toMonoidHom]
  apply forall_congr'
  intro t
  rw [map_lieExp, map_smul]

/-- The Lie algebra of a smooth homomorphism kernel is the kernel of its Lie map. -/
@[simp]
theorem lieSubalgebraOfSubgroup_ker (f : ContMDiffMonoidMorphism I I' ∞ G G') :
    lieSubalgebraOfSubgroup (I := I) f.toMonoidHom.ker = (lieMap f).ker.toLieSubalgebra := by
  rw [← MonoidHom.comap_bot, lieSubalgebraOfSubgroup_comap f (by
    simpa only [Subgroup.coe_bot] using (isClosed_singleton : IsClosed ({1} : Set G'))),
    lieSubalgebraOfSubgroup_bot]
  ext X
  simp only [LieSubalgebra.mem_comap, LieSubalgebra.mem_bot,
    LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker]

end TauCeti.Lie
