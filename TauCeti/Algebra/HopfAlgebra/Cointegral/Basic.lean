/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic
public import TauCeti.Algebra.HopfAlgebra.Integral.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cointegrals

A right cointegral is a functional `φ` satisfying `∑ φ(h₁) • h₂ = φ(h) • 1`.
Left cointegrals satisfy the reflected equation. The predicates include the zero functional;
the corresponding submodules are the spaces whose nonzero elements are usually called
cointegrals. Only a coalgebra with a distinguished element `1` is needed for these
definitions; no compatibility between a multiplication and the coproduct is assumed.

The defining equations use contraction of the coproduct, not a chosen representation.
We also give their Sweedler-sum forms for any `Coalgebra.Repr`. On a projective module,
the equations are equivalent to the right and left integral equations for convolution.
For finite projective bialgebras the scalar in these equations is precisely the counit
of `TauCeti.ConvolutionDual`, so `rightCointegralsConvEquiv` and `leftCointegralsConvEquiv`
identify right and left cointegrals with right and left integrals in `ConvolutionDual`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
-/

public section

open scoped TensorProduct Coalgebra

namespace TauCeti

variable {k H : Type*} [CommSemiring k] [AddCommMonoid H] [One H] [Module k H]
  [Coalgebra k H]

/-- A right cointegral, allowing zero: contraction of the first coproduct factor is
scalar multiplication of the unit. -/
def IsRightCointegral (φ : Module.Dual k H) : Prop :=
  ∀ h, TensorProduct.lid k H (φ.rTensor H (Coalgebra.comul h)) = φ h • (1 : H)

/-- A left cointegral, allowing zero: contraction of the second coproduct factor is
scalar multiplication of the unit. -/
def IsLeftCointegral (φ : Module.Dual k H) : Prop :=
  ∀ h, TensorProduct.rid k H (φ.lTensor H (Coalgebra.comul h)) = φ h • (1 : H)

/-- The characteristic contraction equation for a right cointegral. -/
theorem isRightCointegral_def (φ : Module.Dual k H) :
    IsRightCointegral φ ↔ ∀ h,
      TensorProduct.lid k H (φ.rTensor H (Coalgebra.comul h)) = φ h • (1 : H) := Iff.rfl

/-- The characteristic contraction equation for a left cointegral. -/
theorem isLeftCointegral_def (φ : Module.Dual k H) :
    IsLeftCointegral φ ↔ ∀ h,
      TensorProduct.rid k H (φ.lTensor H (Coalgebra.comul h)) = φ h • (1 : H) := Iff.rfl

/-- The right-cointegral equation in any finite representation of the coproduct. -/
theorem IsRightCointegral.sum {φ : Module.Dual k H} (hφ : IsRightCointegral φ)
    {h : H} {ι : Type*} (r : Coalgebra.Repr k h ι) :
    ∑ i ∈ r.index, φ (r.left i) • r.right i = φ h • (1 : H) := by
  simpa [← r.eq] using hφ h

/-- The left-cointegral equation in any finite representation of the coproduct. -/
theorem IsLeftCointegral.sum {φ : Module.Dual k H} (hφ : IsLeftCointegral φ)
    {h : H} {ι : Type*} (r : Coalgebra.Repr k h ι) :
    ∑ i ∈ r.index, φ (r.right i) • r.left i = φ h • (1 : H) := by
  simpa [← r.eq] using hφ h

/-- Right cointegrals can be checked using any chosen family of coproduct representations. -/
theorem isRightCointegral_iff_sum (φ : Module.Dual k H) {ι : Type*}
    (r : ∀ h : H, Coalgebra.Repr k h ι) :
    IsRightCointegral φ ↔ ∀ h, ∑ i ∈ (r h).index, φ ((r h).left i) • (r h).right i =
      φ h • (1 : H) := by
  refine ⟨fun hφ h => hφ.sum (r h), fun hφ h => ?_⟩
  simpa [← (r h).eq] using hφ h

/-- Left cointegrals can be checked using any chosen family of coproduct representations. -/
theorem isLeftCointegral_iff_sum (φ : Module.Dual k H) {ι : Type*}
    (r : ∀ h : H, Coalgebra.Repr k h ι) :
    IsLeftCointegral φ ↔ ∀ h, ∑ i ∈ (r h).index, φ ((r h).right i) • (r h).left i =
      φ h • (1 : H) := by
  refine ⟨fun hφ h => hφ.sum (r h), fun hφ h => ?_⟩
  simpa [← (r h).eq] using hφ h

/-- The submodule of right cointegrals. No normalization or nonvanishing is imposed. -/
def rightCointegrals (k H : Type*) [CommSemiring k] [AddCommMonoid H] [One H] [Module k H]
    [Coalgebra k H] : Submodule k (Module.Dual k H) where
  carrier := {φ | IsRightCointegral φ}
  zero_mem' := by simp [IsRightCointegral]
  add_mem' := by
    intro φ ψ hφ hψ h
    simpa [LinearMap.rTensor_add, add_smul] using congrArg₂ (· + ·) (hφ h) (hψ h)
  smul_mem' := by
    intro c φ hφ h
    simpa [LinearMap.rTensor_smul, smul_smul] using congrArg (c • ·) (hφ h)

/-- The submodule of left cointegrals. No normalization or nonvanishing is imposed. -/
def leftCointegrals (k H : Type*) [CommSemiring k] [AddCommMonoid H] [One H] [Module k H]
    [Coalgebra k H] : Submodule k (Module.Dual k H) where
  carrier := {φ | IsLeftCointegral φ}
  zero_mem' := by simp [IsLeftCointegral]
  add_mem' := by
    intro φ ψ hφ hψ h
    simpa [LinearMap.lTensor_add, add_smul] using congrArg₂ (· + ·) (hφ h) (hψ h)
  smul_mem' := by
    intro c φ hφ h
    simpa [LinearMap.lTensor_smul, smul_smul] using congrArg (c • ·) (hφ h)

/-- Membership in the right-cointegral submodule is the right-cointegral predicate. -/
@[simp]
theorem mem_rightCointegrals (φ : Module.Dual k H) :
    φ ∈ rightCointegrals k H ↔ IsRightCointegral φ := Iff.rfl

/-- Membership in the left-cointegral submodule is the left-cointegral predicate. -/
@[simp]
theorem mem_leftCointegrals (φ : Module.Dual k H) :
    φ ∈ leftCointegrals k H ↔ IsLeftCointegral φ := Iff.rfl

/-- The zero functional is a right cointegral. -/
@[simp]
theorem isRightCointegral_zero : IsRightCointegral (0 : Module.Dual k H) :=
  (rightCointegrals k H).zero_mem

/-- The zero functional is a left cointegral. -/
@[simp]
theorem isLeftCointegral_zero : IsLeftCointegral (0 : Module.Dual k H) :=
  (leftCointegrals k H).zero_mem

/-- Left and right cointegrals coincide for a cocommutative coproduct. -/
theorem isLeftCointegral_iff_isRightCointegral [Coalgebra.IsCocomm k H] (φ : Module.Dual k H) :
    IsLeftCointegral φ ↔ IsRightCointegral φ := by
  have hswap (h : H) :
      TensorProduct.rid k H (φ.lTensor H (Coalgebra.comul h)) =
        TensorProduct.lid k H (φ.rTensor H (Coalgebra.comul h)) := by
    rw [← Coalgebra.comm_comul k h, LinearMap.lTensor_comm, TensorProduct.rid_comm,
      Coalgebra.comm_comul]
  simp only [isLeftCointegral_def, isRightCointegral_def, hswap]

/-- A right cointegral satisfies the right integral equation in the convolution algebra. -/
theorem IsRightCointegral.convMul {φ : Module.Dual k H} (hφ : IsRightCointegral φ)
    (ψ : ConvolutionDual k H) :
    WithConv.toConv φ * ψ = ψ.ofConv 1 • WithConv.toConv φ := by
  ext h
  rw [ConvolutionDual.mul_apply_eq_rTensor, WithConv.ofConv_toConv, hφ h]
  simp [mul_comm]

/-- A left cointegral satisfies the left integral equation in the convolution algebra. -/
theorem IsLeftCointegral.convMul {φ : Module.Dual k H} (hφ : IsLeftCointegral φ)
    (ψ : ConvolutionDual k H) :
    ψ * WithConv.toConv φ = ψ.ofConv 1 • WithConv.toConv φ := by
  ext h
  rw [ConvolutionDual.mul_apply_eq_lTensor, WithConv.ofConv_toConv, hφ h]
  simp [mul_comm]

/-- For a projective underlying module, the right convolution integral equation
characterizes right cointegrals. Finite generation is not needed. -/
theorem isRightCointegral_iff_convMul [Module.Projective k H] (φ : Module.Dual k H) :
    IsRightCointegral φ ↔ ∀ ψ : ConvolutionDual k H,
      WithConv.toConv φ * ψ = ψ.ofConv 1 • WithConv.toConv φ := by
  refine ⟨fun hφ => hφ.convMul, fun hφ h => ?_⟩
  apply Module.eval_apply_injective k
  ext ψ
  have heq := congrArg (fun f : ConvolutionDual k H => f h) (hφ (WithConv.toConv ψ))
  rw [ConvolutionDual.mul_apply_eq_rTensor] at heq
  simpa [mul_comm] using heq

/-- For a projective underlying module, the left convolution integral equation
characterizes left cointegrals. Finite generation is not needed. -/
theorem isLeftCointegral_iff_convMul [Module.Projective k H] (φ : Module.Dual k H) :
    IsLeftCointegral φ ↔ ∀ ψ : ConvolutionDual k H,
      ψ * WithConv.toConv φ = ψ.ofConv 1 • WithConv.toConv φ := by
  refine ⟨fun hφ => hφ.convMul, fun hφ h => ?_⟩
  apply Module.eval_apply_injective k
  ext ψ
  have heq := congrArg (fun f : ConvolutionDual k H => f h) (hφ (WithConv.toConv ψ))
  rw [ConvolutionDual.mul_apply_eq_lTensor] at heq
  simpa [mul_comm] using heq

section ConvolutionDual

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Module.Finite R H] [Module.Projective R H]

/-- Under `WithConv.toConv`, right integrals in `ConvolutionDual R H` are precisely right
cointegrals on `H`. -/
@[simp]
theorem toConv_mem_rightIntegral_iff (φ : Module.Dual R H) :
    WithConv.toConv φ ∈ rightIntegral R (ConvolutionDual R H) ↔ IsRightCointegral φ := by
  rw [mem_rightIntegral_iff, isRightCointegral_iff_convMul]
  simp only [ConvolutionDual.counit_apply]

/-- Under `WithConv.toConv`, left integrals in `ConvolutionDual R H` are precisely left
cointegrals on `H`. -/
@[simp]
theorem toConv_mem_leftIntegral_iff (φ : Module.Dual R H) :
    WithConv.toConv φ ∈ leftIntegral R (ConvolutionDual R H) ↔ IsLeftCointegral φ := by
  rw [mem_leftIntegral_iff, isLeftCointegral_iff_convMul]
  simp only [ConvolutionDual.counit_apply]

variable (R H) in
/-- `WithConv.toConv` restricts to an `R`-linear equivalence between right cointegrals on `H` and
right integrals in `ConvolutionDual R H`. -/
noncomputable def rightCointegralsConvEquiv :
    rightCointegrals R H ≃ₗ[R] rightIntegral R (ConvolutionDual R H) :=
  (WithConv.linearEquiv R (Module.Dual R H)).symm.ofSubmodules _ _ <| by
    ext ψ
    rw [Submodule.mem_map_equiv]
    exact (toConv_mem_rightIntegral_iff ψ.ofConv).symm

variable (R H) in
/-- `WithConv.toConv` restricts to an `R`-linear equivalence between left cointegrals on `H` and
left integrals in `ConvolutionDual R H`. -/
noncomputable def leftCointegralsConvEquiv :
    leftCointegrals R H ≃ₗ[R] leftIntegral R (ConvolutionDual R H) :=
  (WithConv.linearEquiv R (Module.Dual R H)).symm.ofSubmodules _ _ <| by
    ext ψ
    rw [Submodule.mem_map_equiv]
    exact (toConv_mem_leftIntegral_iff ψ.ofConv).symm

@[simp]
theorem rightCointegralsConvEquiv_apply (φ : rightCointegrals R H) :
    (rightCointegralsConvEquiv R H φ : ConvolutionDual R H) = WithConv.toConv φ.val := by
  simp [rightCointegralsConvEquiv]

@[simp]
theorem rightCointegralsConvEquiv_symm_apply (ψ : rightIntegral R (ConvolutionDual R H)) :
    ((rightCointegralsConvEquiv R H).symm ψ : Module.Dual R H) = ψ.val.ofConv := by
  simp [rightCointegralsConvEquiv]

@[simp]
theorem leftCointegralsConvEquiv_apply (φ : leftCointegrals R H) :
    (leftCointegralsConvEquiv R H φ : ConvolutionDual R H) = WithConv.toConv φ.val := by
  simp [leftCointegralsConvEquiv]

@[simp]
theorem leftCointegralsConvEquiv_symm_apply (ψ : leftIntegral R (ConvolutionDual R H)) :
    ((leftCointegralsConvEquiv R H).symm ψ : Module.Dual R H) = ψ.val.ofConv := by
  simp [leftCointegralsConvEquiv]

end ConvolutionDual

section Opposite

variable {k H : Type*} [CommSemiring k] [AddCommMonoid H] [One H] [Module k H] [Coalgebra k H]

/-- Precomposing with `MulOpposite.opLinearEquiv.symm` preserves and reflects right
cointegrals: a functional on `H` is a right cointegral iff its pushforward to `Hᵐᵒᵖ` is. -/
theorem IsRightCointegral.mulOpposite_iff (φ : Module.Dual k H) :
    IsRightCointegral (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap) ↔
      IsRightCointegral φ := by
  simp only [isRightCointegral_def]
  constructor
  · intro hφ h
    have hswap :
        (MulOpposite.opLinearEquiv k).symm.toLinearMap ∘ₗ
          (TensorProduct.lid k Hᵐᵒᵖ).toLinearMap ∘ₗ
          (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap).rTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv k).toLinearMap
            (MulOpposite.opLinearEquiv k).toLinearMap =
          (TensorProduct.lid k H).toLinearMap ∘ₗ φ.rTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) h)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg MulOpposite.unop (hφ (MulOpposite.op h))
    rw [MulOpposite.comul_op] at heq
    exact hL.symm.trans (by simpa using heq)
  · intro hφ y
    induction y using MulOpposite.rec' with | h y =>
    have hswap :
        (TensorProduct.lid k Hᵐᵒᵖ).toLinearMap ∘ₗ
          (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap).rTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv k).toLinearMap
            (MulOpposite.opLinearEquiv k).toLinearMap =
          (MulOpposite.opLinearEquiv k).toLinearMap ∘ₗ
            (TensorProduct.lid k H).toLinearMap ∘ₗ φ.rTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    rw [MulOpposite.comul_op]
    exact hL.trans (by simpa using congrArg MulOpposite.op (hφ y))

/-- Pushing a right cointegral on `H` forward to `Hᵐᵒᵖ` yields a right cointegral. -/
theorem IsRightCointegral.mulOpposite {φ : Module.Dual k H} (hφ : IsRightCointegral φ) :
    IsRightCointegral (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap) :=
  (IsRightCointegral.mulOpposite_iff φ).mpr hφ

/-- Precomposing with `MulOpposite.opLinearEquiv.symm` preserves and reflects left
cointegrals: a functional on `H` is a left cointegral iff its pushforward to `Hᵐᵒᵖ` is. -/
theorem IsLeftCointegral.mulOpposite_iff (φ : Module.Dual k H) :
    IsLeftCointegral (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap) ↔
      IsLeftCointegral φ := by
  simp only [isLeftCointegral_def]
  constructor
  · intro hφ h
    have hswap :
        (MulOpposite.opLinearEquiv k).symm.toLinearMap ∘ₗ
          (TensorProduct.rid k Hᵐᵒᵖ).toLinearMap ∘ₗ
          (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap).lTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv k).toLinearMap
            (MulOpposite.opLinearEquiv k).toLinearMap =
          (TensorProduct.rid k H).toLinearMap ∘ₗ φ.lTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) h)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg MulOpposite.unop (hφ (MulOpposite.op h))
    rw [MulOpposite.comul_op] at heq
    exact hL.symm.trans (by simpa using heq)
  · intro hφ y
    induction y using MulOpposite.rec' with | h y =>
    have hswap :
        (TensorProduct.rid k Hᵐᵒᵖ).toLinearMap ∘ₗ
          (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap).lTensor Hᵐᵒᵖ ∘ₗ
          TensorProduct.map (MulOpposite.opLinearEquiv k).toLinearMap
            (MulOpposite.opLinearEquiv k).toLinearMap =
          (MulOpposite.opLinearEquiv k).toLinearMap ∘ₗ
            (TensorProduct.rid k H).toLinearMap ∘ₗ φ.lTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    rw [MulOpposite.comul_op]
    exact hL.trans (by simpa using congrArg MulOpposite.op (hφ y))

/-- Pushing a left cointegral on `H` forward to `Hᵐᵒᵖ` yields a left cointegral. -/
theorem IsLeftCointegral.mulOpposite {φ : Module.Dual k H} (hφ : IsLeftCointegral φ) :
    IsLeftCointegral (φ ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap) :=
  (IsLeftCointegral.mulOpposite_iff φ).mpr hφ

/-- A functional on `H` is a right cointegral iff its pullback to `Coop H` is a left
cointegral. -/
theorem IsRightCointegral.coop_iff (φ : Module.Dual k H) :
    IsLeftCointegral (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap) ↔ IsRightCointegral φ := by
  simp only [isLeftCointegral_def, isRightCointegral_def]
  constructor
  · intro hφ h
    have hswap :
        (Coop.linearEquiv k H).toLinearMap ∘ₗ (TensorProduct.rid k (Coop H)).toLinearMap ∘ₗ
          (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap).lTensor (Coop H) ∘ₗ
          TensorProduct.map (Coop.linearEquiv k H).symm.toLinearMap
            (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
          (TensorProduct.comm k H H).toLinearMap =
          (TensorProduct.lid k H).toLinearMap ∘ₗ φ.rTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) h)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg Coop.val (hφ (Coop.mk h))
    rw [Coop.comul_mk] at heq
    exact hL.symm.trans (by simpa using heq)
  · intro hφ y
    induction y with | mk y =>
    have hswap :
        (TensorProduct.rid k (Coop H)).toLinearMap ∘ₗ
          (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap).lTensor (Coop H) ∘ₗ
          TensorProduct.map (Coop.linearEquiv k H).symm.toLinearMap
            (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
          (TensorProduct.comm k H H).toLinearMap =
          (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
            (TensorProduct.lid k H).toLinearMap ∘ₗ φ.rTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    rw [Coop.comul_mk]
    exact hL.trans (by simpa using congrArg Coop.mk (hφ y))

/-- Pulling a right cointegral on `H` back to `Coop H` yields a left cointegral. -/
theorem IsRightCointegral.coop {φ : Module.Dual k H} (hφ : IsRightCointegral φ) :
    IsLeftCointegral (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap) :=
  (IsRightCointegral.coop_iff φ).mpr hφ

/-- A functional on `H` is a left cointegral iff its pullback to `Coop H` is a right
cointegral. -/
theorem IsLeftCointegral.coop_iff (φ : Module.Dual k H) :
    IsRightCointegral (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap) ↔ IsLeftCointegral φ := by
  simp only [isRightCointegral_def, isLeftCointegral_def]
  constructor
  · intro hφ h
    have hswap :
        (Coop.linearEquiv k H).toLinearMap ∘ₗ (TensorProduct.lid k (Coop H)).toLinearMap ∘ₗ
          (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap).rTensor (Coop H) ∘ₗ
          TensorProduct.map (Coop.linearEquiv k H).symm.toLinearMap
            (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
          (TensorProduct.comm k H H).toLinearMap =
          (TensorProduct.rid k H).toLinearMap ∘ₗ φ.lTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) h)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    have heq := congrArg Coop.val (hφ (Coop.mk h))
    rw [Coop.comul_mk] at heq
    exact hL.symm.trans (by simpa using heq)
  · intro hφ y
    induction y with | mk y =>
    have hswap :
        (TensorProduct.lid k (Coop H)).toLinearMap ∘ₗ
          (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap).rTensor (Coop H) ∘ₗ
          TensorProduct.map (Coop.linearEquiv k H).symm.toLinearMap
            (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
          (TensorProduct.comm k H H).toLinearMap =
          (Coop.linearEquiv k H).symm.toLinearMap ∘ₗ
            (TensorProduct.rid k H).toLinearMap ∘ₗ φ.lTensor H :=
      TensorProduct.ext' fun a b ↦ by simp
    have hL := LinearMap.congr_fun hswap (Coalgebra.comul (R := k) y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL
    rw [Coop.comul_mk]
    exact hL.trans (by simpa using congrArg Coop.mk (hφ y))

/-- Pulling a left cointegral on `H` back to `Coop H` yields a right cointegral. -/
theorem IsLeftCointegral.coop {φ : Module.Dual k H} (hφ : IsLeftCointegral φ) :
    IsRightCointegral (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap) :=
  (IsLeftCointegral.coop_iff φ).mpr hφ

/-- A functional on `H` is a left cointegral iff its transfer to `(Coop H)ᵐᵒᵖ` is a right
cointegral. -/
theorem IsLeftCointegral.opCoop_iff (φ : Module.Dual k H) :
    IsRightCointegral
        (φ ∘ₗ ((MulOpposite.opLinearEquiv k).symm.trans (Coop.linearEquiv k H)).toLinearMap) ↔
      IsLeftCointegral φ :=
  (IsRightCointegral.mulOpposite_iff (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap)).trans
    (IsLeftCointegral.coop_iff φ)

/-- Transferring a left cointegral on `H` to `(Coop H)ᵐᵒᵖ` yields a right cointegral. -/
theorem IsLeftCointegral.opCoop {φ : Module.Dual k H} (hφ : IsLeftCointegral φ) :
    IsRightCointegral
      (φ ∘ₗ ((MulOpposite.opLinearEquiv k).symm.trans (Coop.linearEquiv k H)).toLinearMap) :=
  (IsLeftCointegral.opCoop_iff φ).mpr hφ

/-- A functional on `H` is a right cointegral iff its transfer to `(Coop H)ᵐᵒᵖ` is a left
cointegral. -/
theorem IsRightCointegral.opCoop_iff (φ : Module.Dual k H) :
    IsLeftCointegral
        (φ ∘ₗ ((MulOpposite.opLinearEquiv k).symm.trans (Coop.linearEquiv k H)).toLinearMap) ↔
      IsRightCointegral φ :=
  (IsLeftCointegral.mulOpposite_iff (φ ∘ₗ (Coop.linearEquiv k H).toLinearMap)).trans
    (IsRightCointegral.coop_iff φ)

/-- Transferring a right cointegral on `H` to `(Coop H)ᵐᵒᵖ` yields a left cointegral. -/
theorem IsRightCointegral.opCoop {φ : Module.Dual k H} (hφ : IsRightCointegral φ) :
    IsLeftCointegral
      (φ ∘ₗ ((MulOpposite.opLinearEquiv k).symm.trans (Coop.linearEquiv k H)).toLinearMap) :=
  (IsRightCointegral.opCoop_iff φ).mpr hφ

end Opposite

end TauCeti
