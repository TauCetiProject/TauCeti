/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.MulOpposite
public import TauCeti.Algebra.Coalgebra.Coop
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# Opposite and co-opposite Hopf algebras

For a Hopf algebra `H` over a commutative semiring `R`:

* `(TauCeti.Coop H)ᵐᵒᵖ` is unconditionally a Hopf algebra (`MulOpposite.instHopfAlgebraCoop`)
  whose antipode is induced directly from the antipode `S` of `H`.
* When the antipode `S` of `H` is bijective, both `Hᵐᵒᵖ` (`MulOpposite.hopfAlgebra`) and
  `TauCeti.Coop H` (`TauCeti.Coop.hopfAlgebra`) carry Hopf algebra structures whose antipode is
  induced by `S⁻¹` (`TauCeti.HopfAlgebra.inverseAntipode`).

## Main declarations

* `TauCeti.Coop.opLinearEquiv`: canonical `R`-linear equivalence `(Coop A)ᵐᵒᵖ ≃ₗ[R] A`.
* `MulOpposite.instHopfAlgebraCoop`: the `HopfAlgebra` instance on `(Coop H)ᵐᵒᵖ`.
* `MulOpposite.hopfAlgebra`: the `HopfAlgebra` structure on `Hᵐᵒᵖ` when `S` is bijective.
* `TauCeti.Coop.hopfAlgebra`: the `HopfAlgebra` structure on `Coop H` when `S` is bijective.
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti.Coop

variable (R A : Type*) [CommSemiring R] [AddCommMonoid A] [Module R A]

/-- The canonical `R`-linear equivalence `(Coop A)ᵐᵒᵖ ≃ₗ[R] A`. -/
def opLinearEquiv : (Coop A)ᵐᵒᵖ ≃ₗ[R] A :=
  (MulOpposite.opLinearEquiv R).symm.trans (linearEquiv R A)

@[simp]
theorem opLinearEquiv_apply (x : (Coop A)ᵐᵒᵖ) : opLinearEquiv R A x = x.unop.val :=
  rfl

@[simp]
theorem opLinearEquiv_symm_apply (a : A) :
    (opLinearEquiv R A).symm a = MulOpposite.op (mk a) :=
  rfl

section HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- Left antipode axiom for `Coop H` when the antipode of `H` is bijective. -/
private theorem coop_mul_antipode_rTensor_comul
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    let S : Coop H →ₗ[R] Coop H :=
      (linearEquiv R H).symm.toLinearMap ∘ₗ
        TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (linearEquiv R H).toLinearMap
    LinearMap.mul' R (Coop H) ∘ₗ S.rTensor (Coop H) ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H) ∘ₗ Coalgebra.counit := by
  let S : Coop H →ₗ[R] Coop H :=
    (linearEquiv R H).symm.toLinearMap ∘ₗ
      TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (linearEquiv R H).toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x with | mk x =>
  apply val_injective
  have hL :
      (linearEquiv R H).toLinearMap ∘ₗ LinearMap.mul' R (Coop H) ∘ₗ S.rTensor (Coop H) ∘ₗ
        TensorProduct.map (linearEquiv R H).symm.toLinearMap (linearEquiv R H).symm.toLinearMap =
        LinearMap.mul' R H ∘ₗ (TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (TensorProduct.comm R H H (Coalgebra.comul (R := R) x))
  simpa [comul_mk] using
    hL'.trans (TauCeti.HopfAlgebra.mul_inverseAntipode_rTensor_comm_comul_apply hS x)

/-- Right antipode axiom for `Coop H` when the antipode of `H` is bijective. -/
private theorem coop_mul_antipode_lTensor_comul
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    let S : Coop H →ₗ[R] Coop H :=
      (linearEquiv R H).symm.toLinearMap ∘ₗ
        TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (linearEquiv R H).toLinearMap
    LinearMap.mul' R (Coop H) ∘ₗ S.lTensor (Coop H) ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H) ∘ₗ Coalgebra.counit := by
  let S : Coop H →ₗ[R] Coop H :=
    (linearEquiv R H).symm.toLinearMap ∘ₗ
      TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (linearEquiv R H).toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x with | mk x =>
  apply val_injective
  have hL :
      (linearEquiv R H).toLinearMap ∘ₗ LinearMap.mul' R (Coop H) ∘ₗ S.lTensor (Coop H) ∘ₗ
        TensorProduct.map (linearEquiv R H).symm.toLinearMap (linearEquiv R H).symm.toLinearMap =
        LinearMap.mul' R H ∘ₗ (TauCeti.HopfAlgebra.inverseAntipode hS).lTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (TensorProduct.comm R H H (Coalgebra.comul (R := R) x))
  simpa [comul_mk] using
    hL'.trans (TauCeti.HopfAlgebra.mul_inverseAntipode_lTensor_comm_comul_apply hS x)

/-- When the antipode `S` of `H` is bijective, `Coop H` is a Hopf algebra with antipode `S⁻¹`. -/
@[instance_reducible]
noncomputable def hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    HopfAlgebra R (Coop H) where
  antipode := (linearEquiv R H).symm.toLinearMap ∘ₗ
    TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ (linearEquiv R H).toLinearMap
  mul_antipode_rTensor_comul := by exact coop_mul_antipode_rTensor_comul hS
  mul_antipode_lTensor_comul := by exact coop_mul_antipode_lTensor_comul hS

/-- Action of the antipode on `TauCeti.Coop H` under `Coop.hopfAlgebra`. -/
@[simp]
theorem antipode_mk_hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) :
    letI := hopfAlgebra hS
    HopfAlgebra.antipode R (mk a) = mk (TauCeti.HopfAlgebra.inverseAntipode hS a) :=
  rfl

end HopfAlgebra

end TauCeti.Coop

namespace MulOpposite

open TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- Left antipode axiom for `(Coop H)ᵐᵒᵖ`. -/
private theorem opCoop_mul_antipode_rTensor_comul :
    let e : Coop H ≃ₗ[R] H := Coop.linearEquiv R H
    let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
      (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
        HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let e : Coop H ≃ₗ[R] H := Coop.linearEquiv R H
  let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
    (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  induction x with | mk x =>
  have hL :
      LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ ∘ₗ
        TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (TensorProduct.comm R H H).toLinearMap =
        (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
          LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).lTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ)
      (Coalgebra.comul (R := R) (op (Coop.mk x))) = _
  rw [comul_op, Coop.comul_mk]
  have hL'' : (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.rTensor (Coop H)ᵐᵒᵖ)
      (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
        (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
          (TensorProduct.comm R H H (Coalgebra.comul (R := R) x)))) =
      (opLinearEquiv R).toLinearMap (e.symm.toLinearMap
        (LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H (Coalgebra.comul (R := R) x)))) :=
    hL'
  rw [hL'', HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.algebraMap_eq_smul_one, e]

/-- Right antipode axiom for `(Coop H)ᵐᵒᵖ`. -/
private theorem opCoop_mul_antipode_lTensor_comul :
    let e : Coop H ≃ₗ[R] H := Coop.linearEquiv R H
    let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
      (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
        HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R (Coop H)ᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let e : Coop H ≃ₗ[R] H := Coop.linearEquiv R H
  let S : (Coop H)ᵐᵒᵖ →ₗ[R] (Coop H)ᵐᵒᵖ :=
    (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ e.toLinearMap ∘ₗ (opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  induction x with | mk x =>
  have hL :
      LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ ∘ₗ
        TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
        TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (TensorProduct.comm R H H).toLinearMap =
        (opLinearEquiv R).toLinearMap ∘ₗ e.symm.toLinearMap ∘ₗ
          LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H :=
    TensorProduct.ext' fun a b ↦ rfl
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ)
      (Coalgebra.comul (R := R) (op (Coop.mk x))) = _
  rw [comul_op, Coop.comul_mk]
  have hL'' : (LinearMap.mul' R (Coop H)ᵐᵒᵖ ∘ₗ S.lTensor (Coop H)ᵐᵒᵖ)
      (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
        (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
          (TensorProduct.comm R H H (Coalgebra.comul (R := R) x)))) =
      (opLinearEquiv R).toLinearMap (e.symm.toLinearMap
        (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H (Coalgebra.comul (R := R) x)))) :=
    hL'
  rw [hL'', HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.algebraMap_eq_smul_one, e]

noncomputable instance instHopfAlgebraCoop : HopfAlgebra R (Coop H)ᵐᵒᵖ where
  antipode :=
    (opLinearEquiv R).toLinearMap ∘ₗ (Coop.linearEquiv R H).symm.toLinearMap ∘ₗ
      HopfAlgebra.antipode R ∘ₗ (Coop.linearEquiv R H).toLinearMap ∘ₗ
      (opLinearEquiv R).symm.toLinearMap
  mul_antipode_rTensor_comul := by exact opCoop_mul_antipode_rTensor_comul
  mul_antipode_lTensor_comul := by exact opCoop_mul_antipode_lTensor_comul

@[simp]
theorem antipode_op_coop (a : H) :
    HopfAlgebra.antipode R (op (Coop.mk a)) = op (Coop.mk (HopfAlgebra.antipode R a)) :=
  rfl

/-- Left antipode axiom for `Hᵐᵒᵖ` when the antipode of `H` is bijective. -/
private theorem mulOpposite_mul_antipode_rTensor_comul
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
      (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
        (opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
    (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
      (opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ ∘ₗ
        TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap =
        (opLinearEquiv R).toLinearMap ∘ₗ LinearMap.mul' R H ∘ₗ
          (TauCeti.HopfAlgebra.inverseAntipode hS).lTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap :=
    TensorProduct.ext' fun a b ↦ by simp [S]
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ)
      (Coalgebra.comul (R := R) (op x)) = _
  rw [comul_op]
  have hL'' : (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.rTensor Hᵐᵒᵖ)
      (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
        (Coalgebra.comul (R := R) x)) =
      (opLinearEquiv R).toLinearMap (LinearMap.mul' R H
        ((TauCeti.HopfAlgebra.inverseAntipode hS).lTensor H
          (TensorProduct.comm R H H (Coalgebra.comul (R := R) x)))) :=
    hL'
  rw [hL'']
  simp [Algebra.algebraMap_eq_smul_one]

/-- Right antipode axiom for `Hᵐᵒᵖ` when the antipode of `H` is bijective. -/
private theorem mulOpposite_mul_antipode_lTensor_comul
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
      (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
        (opLinearEquiv R).symm.toLinearMap
    LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ ∘ₗ Coalgebra.comul =
      Algebra.linearMap R Hᵐᵒᵖ ∘ₗ Coalgebra.counit := by
  let S : Hᵐᵒᵖ →ₗ[R] Hᵐᵒᵖ :=
    (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
      (opLinearEquiv R).symm.toLinearMap
  refine LinearMap.ext fun x ↦ ?_
  induction x using MulOpposite.rec' with | h x =>
  have hL :
      LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ ∘ₗ
        TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap =
        (opLinearEquiv R).toLinearMap ∘ₗ LinearMap.mul' R H ∘ₗ
          (TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap :=
    TensorProduct.ext' fun a b ↦ by simp [S]
  have hL' := LinearMap.congr_fun hL (Coalgebra.comul (R := R) x)
  change (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ)
      (Coalgebra.comul (R := R) (op x)) = _
  rw [comul_op]
  have hL'' : (LinearMap.mul' R Hᵐᵒᵖ ∘ₗ S.lTensor Hᵐᵒᵖ)
      (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
        (Coalgebra.comul (R := R) x)) =
      (opLinearEquiv R).toLinearMap (LinearMap.mul' R H
        ((TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H
          (TensorProduct.comm R H H (Coalgebra.comul (R := R) x)))) :=
    hL'
  rw [hL'']
  simp [Algebra.algebraMap_eq_smul_one]

/-- When the antipode `S` of `H` is bijective, `Hᵐᵒᵖ` is a Hopf algebra with antipode `S⁻¹`. -/
@[instance_reducible]
noncomputable def hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    HopfAlgebra R Hᵐᵒᵖ where
  antipode := (opLinearEquiv R).toLinearMap ∘ₗ TauCeti.HopfAlgebra.inverseAntipode hS ∘ₗ
    (opLinearEquiv R).symm.toLinearMap
  mul_antipode_rTensor_comul := by exact mulOpposite_mul_antipode_rTensor_comul hS
  mul_antipode_lTensor_comul := by exact mulOpposite_mul_antipode_lTensor_comul hS

/-- Action of the antipode on `Hᵐᵒᵖ` under `MulOpposite.hopfAlgebra`. -/
@[simp]
theorem antipode_op_hopfAlgebra
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) :
    letI := hopfAlgebra hS
    HopfAlgebra.antipode R (op a) = op (TauCeti.HopfAlgebra.inverseAntipode hS a) :=
  rfl

end MulOpposite
