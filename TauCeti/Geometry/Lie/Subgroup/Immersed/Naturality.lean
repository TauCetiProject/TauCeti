/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Image
public import TauCeti.Geometry.Lie.Subgroup.Immersed.Correspondence

/-!
# Naturality of integral leaf subgroups

Let `φ : G → G'` be a smooth homomorphism of second-countable finite-dimensional real Lie groups
and `𝔥` a Lie subalgebra of the Lie algebra of `G`. The image under `φ` of the integral leaf
subgroup of `𝔥` is the integral leaf subgroup of the image of `𝔥` under the Lie map of `φ`
(`LieSubalgebra.map_integralLeafSubgroup`). When `G` is connected, the range of `φ` is the integral
leaf subgroup of the range of its Lie map (`ContMDiffMonoidMorphism.range_eq_integralLeafSubgroup`);
in particular the image of `φ` is a connected immersed Lie subgroup of `G'`, closed or not.

Both statements reduce to generation by exponentials: an integral leaf subgroup is generated, as
an abstract subgroup, by the exponentials of its Lie subalgebra
(`LieSubalgebra.integralLeafSubgroup_eq_closure_lieExp_image`), `Subgroup.map` commutes with
`Subgroup.closure`, and `φ ∘ lieExp = lieExp ∘ lieMap φ` (`map_lieExp`).

With the Galois coinsertion of `TauCeti.Lie.gc_integralLeafSubgroup_lieSubalgebraOfSubgroup`,
naturality turns into an adjunction for images: the image of a connected immersed subgroup `K`
lies in an arbitrary subgroup `Q'` exactly when `K` lies in the integral leaf subgroup of the
preimage of `lieSubalgebraOfSubgroup Q'` under the Lie map
(`TauCeti.Lie.IsImmersedLieSubgroup.map_le_iff_le_integralLeafSubgroup_comap`).

Second countability enters through `LieSubalgebra.integralLeafSubgroup_eq_closure_lieExp_image`,
whose proof factors smooth maps through the intrinsic manifold structure of a Frobenius leaf.

## Main results

* `LieSubalgebra.map_integralLeafSubgroup`: a smooth homomorphism maps the integral leaf subgroup
  of `𝔥` onto the integral leaf subgroup of `𝔥.map (lieMap φ)`.
* `ContMDiffMonoidMorphism.range_eq_integralLeafSubgroup`: the range of a smooth homomorphism
  from a connected Lie group is the integral leaf subgroup of the range of its Lie map.
* `TauCeti.Lie.IsImmersedLieSubgroup.map_le_iff_le_integralLeafSubgroup_comap`: the image of a
  connected immersed subgroup lies in `Q'` exactly when the subgroup lies in the integral leaf
  subgroup of `(lieSubalgebraOfSubgroup Q').comap (lieMap φ)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Chapter I, §10:
  the image of a smooth homomorphism as an analytic subgroup.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Chapters 19 and 20.
-/

public section

open Set TauCeti TauCeti.Lie
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

universe w w'

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {G' : Type w'} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']
  [SecondCountableTopology G']

namespace LieSubalgebra

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G]

/-- **Naturality of integral leaf subgroups.** A smooth homomorphism maps the integral leaf
subgroup of `𝔥` onto the integral leaf subgroup of the image of `𝔥` under its Lie map. -/
theorem map_integralLeafSubgroup (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (𝔥 : LieSubalgebra ℝ (LeftInvariantDerivation I G)) :
    (𝔥.integralLeafSubgroup (I := I)).map φ.toMonoidHom =
      (𝔥.map (lieMap φ)).integralLeafSubgroup (I := I') := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  have hmap : ((𝔥.map (lieMap φ) : Set (LeftInvariantDerivation I' G'))) = lieMap φ '' 𝔥 :=
    Set.ext fun X ↦ mem_map (lieMap φ) 𝔥 X
  rw [integralLeafSubgroup_eq_closure_lieExp_image, integralLeafSubgroup_eq_closure_lieExp_image,
    MonoidHom.map_closure, hmap, image_image, image_image]
  congr 1
  exact image_congr fun X _ ↦ map_lieExp φ X

end LieSubalgebra

namespace TauCeti.Lie.IsImmersedLieSubgroup

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [SecondCountableTopology G] [T2Space G] [T2Space G']

/-- **The image of a connected immersed subgroup under a smooth homomorphism.** For a connected
immersed Lie subgroup `K ≤ G` and an arbitrary subgroup `Q' ≤ G'`, the image of `K` lies in `Q'`
exactly when `K` lies in the integral leaf subgroup of the preimage, under the Lie map, of the Lie
algebra of `Q'`. -/
theorem map_le_iff_le_integralLeafSubgroup_comap {K : Subgroup G}
    (hK : IsImmersedLieSubgroup (I := I) K) (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    {Q' : Subgroup G'} :
    K.map φ.toMonoidHom ≤ Q' ↔
      K ≤ ((lieSubalgebraOfSubgroup (I := I') Q').comap (lieMap φ)).integralLeafSubgroup
        (I := I) := by
  rw [← hK.integralLeafSubgroup_lieSubalgebraOfSubgroup, LieSubalgebra.map_integralLeafSubgroup,
    gc_integralLeafSubgroup_lieSubalgebraOfSubgroup, LieSubalgebra.map_le_iff_le_comap,
    LieSubalgebra.integralLeafSubgroup_le_integralLeafSubgroup_iff]

end TauCeti.Lie.IsImmersedLieSubgroup

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [PreconnectedSpace G]

/-- **The range formula.** The range of a smooth homomorphism from a connected Lie group is the
integral leaf subgroup of the range of its Lie map. -/
theorem range_eq_integralLeafSubgroup (φ : ContMDiffMonoidMorphism I I' ∞ G G') :
    MonoidHom.range φ.toMonoidHom = (lieMap φ).range.integralLeafSubgroup (I := I') := by
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  rw [φ.range_eq_closure_lieExp_image, LieSubalgebra.integralLeafSubgroup_eq_closure_lieExp_image]

end ContMDiffMonoidMorphism
