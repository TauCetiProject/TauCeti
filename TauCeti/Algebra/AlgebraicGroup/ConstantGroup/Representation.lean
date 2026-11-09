/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic

/-!
# Representations of finite constant groups as comodules

Let `G` be a finite group and `R` a commutative ring. A representation `ρ` of the abstract group
`G` on an `R`-module `V` is the same thing as a representation of the constant group scheme
attached to `G`: the coaction is

`v ↦ ∑ g, ρ g v ⊗ δ_g`,

where `δ_g = TauCeti.ConstantGroup.delta R G g` is the indicator function of `g` in the
coordinate ring `G → R`. This file constructs this comodule and shows that the rational point `g`
of the constant group acts on `V` through `ρ g`. No finiteness or freeness is required of `V`.

## Main declarations

* `TauCeti.ConstantGroup.representationComodule`: the comodule over the coordinate ring attached
  to a representation of `G`.
* `TauCeti.ConstantGroup.basePointsRepresentation_toPoints`: the rational point `g` acts through
  `ρ g`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.3.
* J. S. Milne, *Algebraic Groups* (2017), Section 4.a.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConstantGroup

universe u v w

section Comodule

variable (R : Type u) [CommRing R] {G : Type v} [Group G] [Fintype G]
variable {V : Type w} [AddCommMonoid V] [Module R V]

/-- The coaction `v ↦ ∑ g, ρ g v ⊗ δ_g` of the constant group attached to a representation. -/
private noncomputable def representationCoact (ρ : Representation R G V) :
    V →ₗ[R] V ⊗[R] coordinateRing R G :=
  ∑ g, (TensorProduct.mk R V (coordinateRing R G)).flip (delta R G g) ∘ₗ ρ g

private theorem representationCoact_apply (ρ : Representation R G V) (v : V) :
    representationCoact R ρ v = ∑ g, ρ g v ⊗ₜ[R] delta R G g := by
  simp [representationCoact]

/-- **A representation of a finite group is a representation of its constant group scheme.**
The coaction is `v ↦ ∑ g, ρ g v ⊗ δ_g`. -/
@[instance_reducible]
noncomputable def representationComodule (ρ : Representation R G V) :
    Comodule R (coordinateRing R G) V where
  coact := representationCoact R ρ
  coassoc := by
    ext v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      representationCoact_apply, map_sum, LinearMap.rTensor_tmul, TensorProduct.sum_tmul,
      TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, comul_delta, TensorProduct.tmul_sum]
    -- Sum over the first coefficient index `h` outermost on both sides, then substitute
    -- `g ↦ h * g` on the right.
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun g h ↦ ρ g v ⊗ₜ[R] (delta R G h ⊗ₜ[R] delta R G (h⁻¹ * g)))]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [← Equiv.sum_comp (Equiv.mulLeft h)
      (fun g ↦ ρ g v ⊗ₜ[R] (delta R G h ⊗ₜ[R] delta R G (h⁻¹ * g)))]
    simp
  lTensor_counit_comp_coact := by
    classical
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, representationCoact_apply, map_sum,
      LinearMap.lTensor_tmul, ConvolutionDual.counit_apply, ofConv_delta_one,
      LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [Finset.sum_eq_single 1 (fun g _ hg ↦ by simp [hg]) (by simp)]
    simp

/-- The coaction of `representationComodule` is `v ↦ ∑ g, ρ g v ⊗ δ_g`. -/
@[simp]
theorem representationComodule_coact_apply (ρ : Representation R G V) (v : V) :
    letI := representationComodule R ρ
    Comodule.coact (R := R) (C := coordinateRing R G) v = ∑ g, ρ g v ⊗ₜ[R] delta R G g :=
  representationCoact_apply R ρ v

/-- The rational point of the constant group given by `g` acts through `ρ g`. -/
@[simp]
theorem basePointsRepresentation_toPoints (ρ : Representation R G V) (g : G) (v : V) :
    letI := representationComodule R ρ
    Comodule.basePointsRepresentation (H := coordinateRing R G) V (toPoints R G g) v = ρ g v := by
  classical
  let := representationComodule R ρ
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, one_smul,
    TensorProduct.lid_comm, representationComodule_coact_apply]
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, toPoints_apply,
    eval_apply, functionAlgEquiv_apply, ofConv_delta_single, TensorProduct.rid_tmul, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Comodule

end TauCeti.ConstantGroup
