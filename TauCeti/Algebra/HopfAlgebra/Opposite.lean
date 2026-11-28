/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.MulOpposite
public import TauCeti.Algebra.Bialgebra.Coop
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# Opposite and co-opposite Hopf algebras

For a Hopf algebra `H` over a commutative semiring `R`:

* `(TauCeti.Coop H)ᵐᵒᵖ` is unconditionally a Hopf algebra (`MulOpposite.instHopfAlgebraCoop`)
  whose antipode is induced directly from the antipode `S` of `H`.
* When the antipode `S` of `H` is bijective, `Hᵐᵒᵖ` (`MulOpposite.hopfAlgebra`) carries a Hopf
  algebra structure whose antipode is induced by `S⁻¹` (`TauCeti.HopfAlgebra.inverseAntipode`).

## Main declarations

* `TauCeti.HopfAlgebra.antipode_axioms_of_anti`: transports the antipode axioms along an
  anti-multiplicative linear equivalence.
* `MulOpposite.instHopfAlgebraCoop`: the `HopfAlgebra` instance on `(Coop H)ᵐᵒᵖ`.
* `MulOpposite.hopfAlgebra`: the `HopfAlgebra` structure on `Hᵐᵒᵖ` when `S` is bijective.
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti.HopfAlgebra

/-- Transports the left and right antipode axioms along an anti-multiplicative `R`-linear
equivalence `e : K ≃ₗ[R] H` whose inverse commutes with comultiplication up to a map `f`. -/
theorem antipode_axioms_of_anti {R H K : Type*} [CommSemiring R]
    [Semiring H] [Bialgebra R H] [Semiring K] [Bialgebra R K]
    (e : K ≃ₗ[R] H) (S : H →ₗ[R] H)
    (hmul : ∀ a b : H, e.symm a * e.symm b = e.symm (b * a))
    (hone : e.symm 1 = 1)
    (hcounit : ∀ a : H, Coalgebra.counit (R := R) (e.symm a) = Coalgebra.counit (R := R) a)
    (f : H ⊗[R] H →ₗ[R] H ⊗[R] H)
    (hcomul : ∀ a : H, Coalgebra.comul (R := R) (e.symm a) =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap (f (Coalgebra.comul (R := R) a)))
    (hl : ∀ a : H, LinearMap.mul' R H
        (S.lTensor H (TensorProduct.comm R H H (f (Coalgebra.comul (R := R) a)))) =
      algebraMap R H (Coalgebra.counit (R := R) a))
    (hr : ∀ a : H, LinearMap.mul' R H
        (S.rTensor H (TensorProduct.comm R H H (f (Coalgebra.comul (R := R) a)))) =
      algebraMap R H (Coalgebra.counit (R := R) a)) :
    let SK : K →ₗ[R] K := e.symm.toLinearMap ∘ₗ S ∘ₗ e.toLinearMap
    LinearMap.mul' R K ∘ₗ SK.rTensor K ∘ₗ Coalgebra.comul =
        Algebra.linearMap R K ∘ₗ Coalgebra.counit ∧
      LinearMap.mul' R K ∘ₗ SK.lTensor K ∘ₗ Coalgebra.comul =
        Algebra.linearMap R K ∘ₗ Coalgebra.counit := by
  intro SK
  have hR (z : H ⊗[R] H) :
      LinearMap.mul' R K
          (SK.rTensor K (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap z)) =
        e.symm (LinearMap.mul' R H (S.lTensor H (TensorProduct.comm R H H z))) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul a b => simp [SK, hmul]
  have hL (z : H ⊗[R] H) :
      LinearMap.mul' R K
          (SK.lTensor K (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap z)) =
        e.symm (LinearMap.mul' R H (S.rTensor H (TensorProduct.comm R H H z))) := by
    induction z using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul a b => simp [SK, hmul]
  constructor
  · refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := e.symm.surjective x
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      hcomul, hcounit]
    rw [hR, hl]
    simp [Algebra.algebraMap_eq_smul_one, hone]
  · refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := e.symm.surjective x
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      hcomul, hcounit]
    rw [hL, hr]
    simp [Algebra.algebraMap_eq_smul_one, hone]

end TauCeti.HopfAlgebra

namespace MulOpposite

open TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

private theorem opCoop_antipode_axioms :
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ
        ((Coop.unopLinearEquiv R H).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R ∘ₗ
          (Coop.unopLinearEquiv R H).toLinearMap).rTensor (Coop H)ᵐᵒᵖ ∘ₗ
        Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit ∧
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ
        ((Coop.unopLinearEquiv R H).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R ∘ₗ
          (Coop.unopLinearEquiv R H).toLinearMap).lTensor (Coop H)ᵐᵒᵖ ∘ₗ
        Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit :=
  TauCeti.HopfAlgebra.antipode_axioms_of_anti (Coop.unopLinearEquiv R H) (HopfAlgebra.antipode R)
    (fun a b ↦ by
      rw [Coop.unopLinearEquiv_symm_apply, Coop.unopLinearEquiv_symm_apply,
        Coop.unopLinearEquiv_symm_apply, ← op_mul, ← Coop.mk_mul])
    (by rw [Coop.unopLinearEquiv_symm_apply, Coop.mk_one, op_one])
    (fun a ↦ by rw [Coop.unopLinearEquiv_symm_apply, counit_op, Coop.counit_mk])
    (TensorProduct.comm R H H).toLinearMap
    (fun a ↦ by
      simp only [Coop.unopLinearEquiv_symm_apply, LinearEquiv.coe_coe]
      rw [comul_op, Coop.comul_mk, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have hmap :
          TensorProduct.map
              ((opLinearEquiv R).toLinearMap ∘ₗ (Coop.linearEquiv R H).symm.toLinearMap)
              ((opLinearEquiv R).toLinearMap ∘ₗ (Coop.linearEquiv R H).symm.toLinearMap) =
            TensorProduct.map (Coop.unopLinearEquiv R H).symm.toLinearMap
              (Coop.unopLinearEquiv R H).symm.toLinearMap :=
        TensorProduct.ext' fun x y ↦ by simp
      exact LinearMap.congr_fun hmap _)
    (fun a ↦ by simp [HopfAlgebra.mul_antipode_lTensor_comul_apply])
    (fun a ↦ by simp [HopfAlgebra.mul_antipode_rTensor_comul_apply])

noncomputable instance instHopfAlgebraCoop : HopfAlgebra R (Coop H)ᵐᵒᵖ where
  antipode :=
    (Coop.unopLinearEquiv R H).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R ∘ₗ
      (Coop.unopLinearEquiv R H).toLinearMap
  -- Tactic mode (`by exact`) is required under `module` so the public `Prop` field can use the
  -- `private` helper.
  mul_antipode_rTensor_comul := by exact opCoop_antipode_axioms.1
  mul_antipode_lTensor_comul := by exact opCoop_antipode_axioms.2

@[simp]
theorem antipode_op_coop (a : H) :
    HopfAlgebra.antipode R (op (Coop.mk a)) = op (Coop.mk (HopfAlgebra.antipode R a)) :=
  rfl

private theorem mulOpposite_antipode_axioms
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ
        ((opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
          (opLinearEquiv R).symm.toLinearMap).rTensor Hᵐᵒᵖ ∘ₗ
        Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit ∧
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ
        ((opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
          (opLinearEquiv R).symm.toLinearMap).lTensor Hᵐᵒᵖ ∘ₗ
        Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit :=
  TauCeti.HopfAlgebra.antipode_axioms_of_anti (opLinearEquiv R (M := H)).symm
    (TauCeti.HopfAlgebra.inverseAntipode hS)
    (fun a b ↦ by simp only [LinearEquiv.symm_symm, coe_opLinearEquiv, ← op_mul])
    (by rw [LinearEquiv.symm_symm, coe_opLinearEquiv, op_one])
    (fun a ↦ by rw [LinearEquiv.symm_symm, coe_opLinearEquiv, counit_op])
    LinearMap.id
    (fun a ↦ by rw [LinearEquiv.symm_symm, coe_opLinearEquiv, comul_op, LinearMap.id_apply])
    (fun a ↦ TauCeti.HopfAlgebra.mul_inverseAntipode_lTensor_comm_comul_apply hS a)
    (fun a ↦ TauCeti.HopfAlgebra.mul_inverseAntipode_rTensor_comm_comul_apply hS a)

/-- When the antipode `S` of `H` is bijective, `Hᵐᵒᵖ` is a Hopf algebra with antipode `S⁻¹`. -/
@[instance_reducible]
noncomputable def hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    HopfAlgebra R Hᵐᵒᵖ where
  antipode := (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
    (opLinearEquiv R).symm.toLinearMap
  -- Tactic mode (`by exact`) is required under `module` so the public `Prop` field can use the
  -- `private` helper.
  mul_antipode_rTensor_comul := by exact (mulOpposite_antipode_axioms hS).1
  mul_antipode_lTensor_comul := by exact (mulOpposite_antipode_axioms hS).2

/-- Action of the antipode on `Hᵐᵒᵖ` under `MulOpposite.hopfAlgebra`. -/
@[simp]
theorem antipode_op_hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) :
    letI := hopfAlgebra hS
    HopfAlgebra.antipode R (op a) = op (TauCeti.HopfAlgebra.inverseAntipode hS a) :=
  rfl

end MulOpposite
