/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The period lattice in the tangent space of a compact commutative Lie group

For a commutative Lie group `G` modelled on a finite-dimensional real space `E`, the
tangent-space exponential `mulInvariantExp : E → G` is a homomorphism
(`TauCeti.mulInvariantExpAddMonoidHom`). It is the exponential `lieExpAddMonoidHom` of
left-invariant derivations, read through the identification of left-invariant derivations with the
tangent space at the identity. So its kernel `Λ` is discrete, and when `G` is compact `Λ` is a full
`ℤ`-lattice in `E` (`TauCeti.isZLattice_ker_mulInvariantExpAddMonoidHom`); when `G` is moreover
connected, `E ⧸ Λ ≃ G` as topological groups
(`TauCeti.mulInvariantExpQuotientKerContinuousAddEquiv`).

Stated on `E` rather than on left-invariant derivations, this is the form in which the lattice of
a complex torus `E ⧸ Λ` is attached to a compact connected commutative complex Lie group.

## Main results

* `TauCeti.mulInvariantExpAddMonoidHom`: `mulInvariantExp` as a homomorphism `E →+ Additive G`.
* `TauCeti.discreteTopology_ker_mulInvariantExpAddMonoidHom`: its kernel is discrete.
* `TauCeti.isZLattice_ker_mulInvariantExpAddMonoidHom`: for compact `G` its kernel is a full
  lattice.
* `TauCeti.mulInvariantExpQuotientKerContinuousAddEquiv`: for compact connected `G`,
  `E ⧸ ker ≃ₜ+ Additive G`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6).
-/

public section

noncomputable section

namespace TauCeti

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (I G) in
/-- The tangent-space exponential `mulInvariantExp : E → G` of a commutative Lie group, as a
homomorphism to `G` written additively: the exponential `lieExpAddMonoidHom` of left-invariant
derivations, read through `leftInvariantDerivationLinearIsometryEquivModelVectorSpace`. -/
def mulInvariantExpAddMonoidHom : E →+ Additive G :=
  (lieExpAddMonoidHom (I := I) (G := G)).comp
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G)).symm.toLinearEquiv.toAddMonoidHom

@[simp]
theorem mulInvariantExpAddMonoidHom_apply (v : E) :
    mulInvariantExpAddMonoidHom I G v =
      Additive.ofMul (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) := by
  change lieExpAddMonoidHom
    ((leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)).symm v) = _
  rw [lieExpAddMonoidHom_apply, lieExp_eq_mulInvariantExp]
  congr 2
  exact (leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply (I := I) (G := G)
    _).symm.trans (LinearIsometryEquiv.apply_symm_apply _ v)

/-- The kernel of `mulInvariantExp` is the image of the kernel of `lieExp`. -/
theorem coe_ker_mulInvariantExpAddMonoidHom :
    ((mulInvariantExpAddMonoidHom I G).ker : Set E) =
      (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)) ''
        ((lieExpAddMonoidHom (I := I) (G := G)).ker : Set _) := by
  ext v
  rw [(leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I)
    (G := G)).image_eq_preimage_symm]
  rfl

/-- `mulInvariantExp` is continuous. -/
theorem continuous_mulInvariantExpAddMonoidHom :
    Continuous (mulInvariantExpAddMonoidHom I G) :=
  continuous_lieExpAddMonoidHom.comp
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)).symm.continuous

/-- **The kernel of `mulInvariantExp` is discrete.** -/
instance discreteTopology_ker_mulInvariantExpAddMonoidHom :
    DiscreteTopology (mulInvariantExpAddMonoidHom I G).ker := by
  refine SetLike.isDiscrete_iff_discreteTopology.mp ?_
  rw [coe_ker_mulInvariantExpAddMonoidHom]
  exact (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance).image
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I)
      (G := G)).toHomeomorph.isInducing

variable [IsTopologicalGroup G]

/-- `mulInvariantExp` is an open map. -/
theorem isOpenMap_mulInvariantExpAddMonoidHom : IsOpenMap (mulInvariantExpAddMonoidHom I G) := by
  exact isOpenMap_lieExpAddMonoidHom.comp
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I)
      (G := G)).symm.toHomeomorph.isOpenMap

section Compact

variable [CompactSpace G]

/-- **The kernel of the exponential of a compact commutative Lie group is a full lattice in the
tangent space at the identity.** -/
instance isZLattice_ker_mulInvariantExpAddMonoidHom :
    IsZLattice ℝ (mulInvariantExpAddMonoidHom I G).ker.toIntSubmodule where
  span_top := by
    rw [AddSubgroup.coe_toIntSubmodule, coe_ker_mulInvariantExpAddMonoidHom]
    have := Submodule.span_image (R := ℝ)
      ((leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I)
        (G := G)).toLinearEquiv.toLinearMap)
      (s := ((lieExpAddMonoidHom (I := I) (G := G)).ker : Set _))
    rw [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at this
    rw [this, span_ker_lieExpAddMonoidHom_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)).surjective

end Compact

section Connected

variable [PreconnectedSpace G]

omit [IsTopologicalGroup G] in
/-- `mulInvariantExp` of a preconnected commutative Lie group is surjective. -/
theorem mulInvariantExpAddMonoidHom_surjective :
    Function.Surjective (mulInvariantExpAddMonoidHom I G) := by
  exact (lieExpAddMonoidHom_surjective_of_preconnectedSpace (I := I) (G := G)).comp
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)).symm.surjective

/-- **A preconnected commutative Lie group is the quotient of its tangent space at the identity by
the kernel of the exponential**, as topological groups. -/
def mulInvariantExpQuotientKerContinuousAddEquiv :
    (E ⧸ (mulInvariantExpAddMonoidHom I G).ker) ≃ₜ+ Additive G :=
  ContinuousAddEquiv.quotientKerEquivOfSurjective _
    ((isOpenMap_mulInvariantExpAddMonoidHom (I := I) (G := G)).isStrictMap
      (continuous_mulInvariantExpAddMonoidHom (I := I) (G := G)))
    mulInvariantExpAddMonoidHom_surjective

@[simp]
theorem mulInvariantExpQuotientKerContinuousAddEquiv_mk (v : E) :
    mulInvariantExpQuotientKerContinuousAddEquiv (I := I) (G := G) (QuotientAddGroup.mk v) =
      Additive.ofMul (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) := by
  rw [mulInvariantExpQuotientKerContinuousAddEquiv,
    ContinuousAddEquiv.quotientKerEquivOfSurjective_apply_mk, mulInvariantExpAddMonoidHom_apply]

end Connected

end TauCeti
