/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Comodules from natural actions on points

Let `H` be a commutative bialgebra over a commutative ring `R` and `V` an `R`-module. A
comodule structure on `V` makes each point `g : H →ₐ[R] A` act on the scalar extension
`A ⊗[R] V` by the `A`-linear map `TauCeti.Comodule.endOfPoint V g`; these actions are
multiplicative in `g` and natural in the commutative value ring `A`. This file proves the
converse, which is the Yoneda lemma for representations: a family of `A`-linear actions of the
convolution monoids `WithConv (H →ₐ[R] A)` on `A ⊗[R] V`, multiplicative and natural in `A`, is
`endOfPoint` for exactly one comodule structure on `V` (`TauCeti.Comodule.ofNaturality`,
`TauCeti.Comodule.endOfPoint_ofNaturality` and `TauCeti.Comodule.eq_ofNaturality`).

The coaction sends `v` to the action of the universal point `AlgHom.id R H` on `1 ⊗ v`, read in
`V ⊗[R] H`. Naturality along a point `g : H →ₐ[R] A` computes the action of `g` from this
universal value. The counit law is the action of the identity point, and coassociativity is
multiplicativity at the two inclusions `H → H ⊗[R] H`, whose convolution product is the
comultiplication.

Thus a linear action of an affine group on a vector group, given on points, is a representation.
This is how a torus acting by conjugation on the centre of the unipotent radical of a group gives
a comodule over its coordinate ring.

## Main declarations

* `TauCeti.Comodule.ofNaturality`: the comodule structure defined by a natural multiplicative
  family of linear actions on points.
* `TauCeti.Comodule.endOfPoint_ofNaturality`: its points act by the given family.
* `TauCeti.Comodule.eq_ofNaturality`: it is the only comodule structure whose points act by the
  given family.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part I, 2.8.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

universe u w

variable {R : Type u} [CommRing R] {H : Type u} [CommRing H] [Bialgebra R H]
  {V : Type w} [AddCommMonoid V] [Module R V]

section Naturality

variable (ρ : ∀ (A : Type u) [CommRing A] [Algebra R A],
    WithConv (H →ₐ[R] A) →* Module.End A (A ⊗[R] V))

/-- The coaction defined by a family of actions on points: `v` is sent to the action of the
universal point on `1 ⊗ v`, read in `V ⊗[R] H`. -/
private noncomputable def coactOfNaturality : V →ₗ[R] V ⊗[R] H :=
  (TensorProduct.comm R H V).toLinearMap ∘ₗ
    (ρ H (toConv (AlgHom.id R H))).restrictScalars R ∘ₗ TensorProduct.mk R H V 1

private theorem coactOfNaturality_apply (v : V) :
    coactOfNaturality ρ v =
      TensorProduct.comm R H V (ρ H (toConv (AlgHom.id R H)) (1 ⊗ₜ[R] v)) :=
  rfl

variable {ρ} (hρ : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) (x : A ⊗[R] V),
    LinearMap.rTensor V φ.toLinearMap (ρ A g x) =
      ρ B (AlgHom.mapValue φ g) (LinearMap.rTensor V φ.toLinearMap x))

include hρ in
/-- Naturality computes the action of every point from the action of the universal point. -/
private theorem apply_one_tmul_eq_rTensor {A : Type u} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (v : V) :
    ρ A g (1 ⊗ₜ[R] v) =
      LinearMap.rTensor V g.ofConv.toLinearMap (ρ H (toConv (AlgHom.id R H)) (1 ⊗ₜ[R] v)) := by
  rw [hρ H A g.ofConv, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]

include hρ in
/-- The action of a point on a pure tensor, computed from the universal point. -/
private theorem apply_tmul_eq {A : Type u} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) (a : A) (v : V) :
    ρ A g (a ⊗ₜ[R] v) =
      a • LinearMap.rTensor V g.ofConv.toLinearMap
        (ρ H (toConv (AlgHom.id R H)) (1 ⊗ₜ[R] v)) := by
  rw [← apply_one_tmul_eq_rTensor hρ, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hρ in
private theorem counit_coactOfNaturality :
    Coalgebra.counit.lTensor V ∘ₗ coactOfNaturality ρ = (TensorProduct.mk R V R).flip 1 := by
  ext v
  have h := apply_one_tmul_eq_rTensor hρ (1 : WithConv (H →ₐ[R] R)) v
  rw [map_one, one_apply_eq_self] at h
  rw [Bialgebra.ofConv_one_eq_counitAlgHom, Bialgebra.toLinearMap_counitAlgHom] at h
  simp only [LinearMap.coe_comp, Function.comp_apply, coactOfNaturality_apply,
    LinearMap.lTensor_comm, ← h, TensorProduct.comm_tmul, LinearMap.flip_apply,
    TensorProduct.mk_apply]

/-- Reassociating a pure tensor against `1 ⊗ h`: the shape of the left side of coassociativity. -/
private theorem comm_assoc_comm_tmul (y : H ⊗[R] V) (h : H) :
    TensorProduct.comm R V (H ⊗[R] H)
        (TensorProduct.assoc R V H H (TensorProduct.comm R H V y ⊗ₜ[R] h)) =
      ((1 : H) ⊗ₜ[R] h) •
        LinearMap.rTensor V (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H).toLinearMap
          y := by
  induction y using TensorProduct.inductionOn with
  | tmul h' w =>
    simp [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  | add y y' hy hy' =>
    rw [map_add, TensorProduct.add_tmul, map_add, map_add, hy, hy', map_add, smul_add]

include hρ in
private theorem coassoc_coactOfNaturality :
    TensorProduct.assoc R V H H ∘ₗ (coactOfNaturality ρ).rTensor H ∘ₗ coactOfNaturality ρ =
      Coalgebra.comul.lTensor V ∘ₗ coactOfNaturality ρ := by
  -- Both sides are compared after swapping the factor `V` to the right.
  ext v
  refine (TensorProduct.comm R V (H ⊗[R] H)).injective ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  -- The right side is the action of the comultiplication, the product of the two inclusions.
  have hright : TensorProduct.comm R V (H ⊗[R] H)
      (Coalgebra.comul.lTensor V (coactOfNaturality ρ v)) =
      ρ (H ⊗[R] H) (toConv Algebra.TensorProduct.includeLeft)
        (LinearMap.rTensor V
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap
          (ρ H (toConv (AlgHom.id R H)) (1 ⊗ₜ[R] v))) := by
    rw [coactOfNaturality_apply, LinearMap.lTensor_comm, TensorProduct.comm_comm,
      ← Bialgebra.toLinearMap_comulAlgHom,
      ← apply_one_tmul_eq_rTensor hρ (toConv (Bialgebra.comulAlgHom R H)) v,
      Bialgebra.comulPoint_eq_include_mul, map_mul, mul_apply_eq_comp,
      apply_one_tmul_eq_rTensor hρ
        (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)), ofConv_toConv]
  -- The left side is computed on pure tensors of the universal value.
  have hleft (x : H ⊗[R] V) :
      TensorProduct.comm R V (H ⊗[R] H) (TensorProduct.assoc R V H H
        ((coactOfNaturality ρ).rTensor H (TensorProduct.comm R H V x))) =
      ρ (H ⊗[R] H) (toConv Algebra.TensorProduct.includeLeft)
        (LinearMap.rTensor V
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap x) := by
    induction x using TensorProduct.inductionOn with
    | tmul h w =>
      rw [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, coactOfNaturality_apply,
        comm_assoc_comm_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeRight_apply,
        apply_tmul_eq hρ (toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)),
        ofConv_toConv]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hright, ← hleft, coactOfNaturality_apply]

/-- **The comodule structure defined by a natural action on points.** A family `ρ` of
`A`-linear actions of the convolution monoids `WithConv (H →ₐ[R] A)` on the scalar extensions
`A ⊗[R] V`, natural in the commutative value ring `A` (`hρ`), defines a comodule structure on `V`:
the coaction of `v` is the action of the universal point `AlgHom.id R H` on `1 ⊗ v`. Its points
act by `ρ` (`TauCeti.Comodule.endOfPoint_ofNaturality`), and it is the only comodule structure
with this property (`TauCeti.Comodule.eq_ofNaturality`). -/
@[instance_reducible]
noncomputable def ofNaturality : Comodule R H V where
  coact := coactOfNaturality ρ
  coassoc := coassoc_coactOfNaturality hρ
  lTensor_counit_comp_coact := counit_coactOfNaturality hρ

/-- The coaction of `TauCeti.Comodule.ofNaturality` sends `v` to the action of the universal
point on `1 ⊗ v`, read in `V ⊗[R] H`. -/
theorem coact_ofNaturality_apply (v : V) :
    letI := ofNaturality hρ
    coact (R := R) (C := H) v =
      TensorProduct.comm R H V (ρ H (toConv (AlgHom.id R H)) (1 ⊗ₜ[R] v)) :=
  (rfl)

/-- **The points of the comodule `TauCeti.Comodule.ofNaturality` act by the given family.** -/
theorem endOfPoint_ofNaturality (A : Type u) [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    letI := ofNaturality hρ
    endOfPoint V g.ofConv = ρ A g := by
  refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
  rw [endOfPoint_tmul, apply_tmul_eq hρ, ← pointCochain_apply, coact_ofNaturality_apply,
    pointCochain_comm]

/-- **Uniqueness of the comodule structure with given point actions.** A comodule structure on
`V` whose points act by a natural family `ρ` is `TauCeti.Comodule.ofNaturality`. -/
theorem eq_ofNaturality [c : Comodule R H V]
    (hc : ∀ (A : Type u) [CommRing A] [Algebra R A] (g : WithConv (H →ₐ[R] A)),
      endOfPoint V g.ofConv = ρ A g) :
    c = ofNaturality hρ := by
  refine Comodule.ext (LinearMap.ext fun v ↦ ?_)
  have h := congrArg (fun f ↦ TensorProduct.comm R H V (f (1 ⊗ₜ[R] v)))
    (hc H (toConv (AlgHom.id R H)))
  simp only [endOfPoint_tmul, one_smul, AlgHom.toLinearMap_id, LinearMap.lTensor_id,
    LinearMap.id_apply, TensorProduct.comm_comm] at h
  exact h.trans (coact_ofNaturality_apply hρ v).symm

end Naturality

end TauCeti.Comodule
