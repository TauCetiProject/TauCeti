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

where `δ_g` is the indicator function of `g` in the coordinate ring `G → R`. This file constructs
this comodule and shows that the rational point `g` of the constant group acts on `V` through
`ρ g`. No finiteness or freeness is required of `V`.

## Main declarations

* `TauCeti.ConstantGroup.delta`: the indicator function of a group element, as an element of the
  coordinate ring.
* `TauCeti.ConstantGroup.comul_delta`, `TauCeti.ConstantGroup.counit_delta`: the coalgebra
  structure on indicator functions.
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

section Delta

variable (R : Type u) [CommRing R] (G : Type v) [Finite G]

/-- The indicator function of `g`, as an element of the coordinate ring of the constant group:
the coordinate functional of `g` on the group algebra. -/
noncomputable def delta (g : G) : coordinateRing R G :=
  WithConv.toConv ((MonoidAlgebra.basis G R).coord g)

/-- Under the identification of the coordinate ring with `G → R`, the element `delta R G g` is the
indicator function of `g`. -/
@[simp]
theorem functionAlgEquiv_delta [DecidableEq G] (g : G) :
    functionAlgEquiv R G (delta R G g) = Pi.single g 1 := by
  ext h
  rw [functionAlgEquiv_apply, delta, WithConv.ofConv_toConv, ← MonoidAlgebra.basis_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]

/-- The indicator function of `g` takes the value `1` at `g` and `0` elsewhere. This is the
simp-normal form of its values. -/
@[simp]
theorem ofConv_delta_single [DecidableEq G] (g h : G) :
    (delta R G g).ofConv (MonoidAlgebra.single h 1) = if h = g then 1 else 0 := by
  rw [← functionAlgEquiv_apply, functionAlgEquiv_delta, Pi.single_apply]

/-- Evaluation at `h` sends the indicator function of `g` to `1` or `0`. -/
theorem eval_delta [DecidableEq G] (g h : G) :
    eval R G h (delta R G g) = if h = g then 1 else 0 := by
  rw [eval_apply, functionAlgEquiv_delta, Pi.single_apply]

variable [Monoid G]

/-- The counit of the indicator function of `g` is `1` if `g = 1` and `0` otherwise. -/
theorem counit_delta [DecidableEq G] (g : G) :
    Coalgebra.counit (R := R) (delta R G g) = if g = 1 then 1 else 0 := by
  rw [counit_apply, functionAlgEquiv_delta, Pi.single_apply]
  simp only [eq_comm]

end Delta

section Comul

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [Fintype G]

/-- The comultiplication of the indicator function of `g` splits `g` into all products
`h * (h⁻¹ * g)`. -/
theorem comul_delta (g : G) :
    Coalgebra.comul (R := R) (delta R G g) =
      ∑ h, delta R G h ⊗ₜ[R] delta R G (h⁻¹ * g) := by
  classical
  apply (ConvolutionDual.dualDistribEquiv R (MonoidAlgebra R G)).injective
  refine ((MonoidAlgebra.basis G R).tensorProduct (MonoidAlgebra.basis G R)).ext fun x ↦ ?_
  rw [Module.Basis.tensorProduct_apply', MonoidAlgebra.basis_apply, MonoidAlgebra.basis_apply,
    comul_apply, map_sum, LinearMap.sum_apply]
  simp only [ConvolutionDual.dualDistribEquiv_tmul_apply, ← functionAlgEquiv_apply,
    functionAlgEquiv_delta, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, eq_inv_mul_iff_mul_eq]

end Comul

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
    simp [Module.End.mul_apply]
  lTensor_counit_comp_coact := by
    classical
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, representationCoact_apply, map_sum,
      LinearMap.lTensor_tmul, counit_delta, LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [Finset.sum_eq_single 1 (fun g _ hg ↦ by simp [hg]) (by simp)]
    simp

/-- The coaction of `representationComodule` is `v ↦ ∑ g, ρ g v ⊗ δ_g`. -/
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
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, toPoints_apply, eval_delta,
    TensorProduct.rid_tmul, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

end Comodule

end TauCeti.ConstantGroup
