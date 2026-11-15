/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Antipode
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
of `TauCeti.ConvolutionDual`, identifying `rightCointegrals` and `leftCointegrals` with
`rightIntegral` and `leftIntegral` on `ConvolutionDual`. Over a Hopf algebra, precomposition
with the antipode exchanges right and left cointegrals.

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

instance {R A : Type*} [CommRing R] [AddCommMonoid A] [One A] [Module R A] [Coalgebra R A] :
    AddCommGroup (rightCointegrals R A) :=
  Submodule.addCommGroup _

instance {R A : Type*} [CommRing R] [AddCommMonoid A] [One A] [Module R A] [Coalgebra R A] :
    AddCommGroup (leftCointegrals R A) :=
  Submodule.addCommGroup _

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

section HopfAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Precomposing a right cointegral with the antipode produces a left cointegral. -/
theorem IsRightCointegral.comp_antipode {φ : Module.Dual R A} (hφ : IsRightCointegral φ) :
    IsLeftCointegral (φ ∘ₗ HopfAlgebra.antipode R) := by
  intro h
  let g : A →ₗ[R] A := Algebra.linearMap R A ∘ₗ φ ∘ₗ HopfAlgebra.antipode R
  have hSg : WithConv.toConv (HopfAlgebra.antipode R) * WithConv.toConv g = WithConv.toConv g := by
    apply WithConv.ofConv_injective
    ext x
    have hmul :
        (WithConv.toConv (HopfAlgebra.antipode R) * WithConv.toConv g).ofConv x =
          TensorProduct.lid R A (φ.rTensor A (Coalgebra.comul (HopfAlgebra.antipode R x))) := by
      rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, LinearMap.convMul_apply]
      induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a b => simp [g, Algebra.algebraMap_eq_smul_one]
    rw [hmul, hφ (HopfAlgebra.antipode R x)]
    simp [g, Algebra.algebraMap_eq_smul_one]
  have hidg : WithConv.toConv LinearMap.id * WithConv.toConv g = WithConv.toConv g :=
    calc
      WithConv.toConv LinearMap.id * WithConv.toConv g =
          WithConv.toConv LinearMap.id *
            (WithConv.toConv (HopfAlgebra.antipode R) * WithConv.toConv g) := by rw [hSg]
      _ = WithConv.toConv g := by rw [← mul_assoc, LinearMap.id_mul_antipode, one_mul]
  have heval :
      (WithConv.toConv LinearMap.id * WithConv.toConv g).ofConv h =
        TensorProduct.rid R A ((φ ∘ₗ HopfAlgebra.antipode R).lTensor A (Coalgebra.comul h)) := by
    rw [LinearMap.convMul_apply]
    induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul a b => simp [g, Algebra.algebraMap_eq_smul_one]
  have hgh := congrArg (fun u : WithConv (A →ₗ[R] A) ↦ u.ofConv h) hidg
  rw [heval] at hgh
  simpa [g, Algebra.algebraMap_eq_smul_one] using hgh

/-- Precomposing a left cointegral with the antipode produces a right cointegral. -/
theorem IsLeftCointegral.comp_antipode {φ : Module.Dual R A} (hφ : IsLeftCointegral φ) :
    IsRightCointegral (φ ∘ₗ HopfAlgebra.antipode R) := by
  intro h
  let g : A →ₗ[R] A := Algebra.linearMap R A ∘ₗ φ ∘ₗ HopfAlgebra.antipode R
  have hgS : WithConv.toConv g * WithConv.toConv (HopfAlgebra.antipode R) = WithConv.toConv g := by
    apply WithConv.ofConv_injective
    ext x
    have hmul :
        (WithConv.toConv g * WithConv.toConv (HopfAlgebra.antipode R)).ofConv x =
          TensorProduct.rid R A (φ.lTensor A (Coalgebra.comul (HopfAlgebra.antipode R x))) := by
      rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, LinearMap.convMul_apply]
      induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a b => simp [g, Algebra.algebraMap_eq_smul_one]
    rw [hmul, hφ (HopfAlgebra.antipode R x)]
    simp [g, Algebra.algebraMap_eq_smul_one]
  have hgid : WithConv.toConv g * WithConv.toConv LinearMap.id = WithConv.toConv g :=
    calc
      WithConv.toConv g * WithConv.toConv LinearMap.id =
          (WithConv.toConv g * WithConv.toConv (HopfAlgebra.antipode R)) *
            WithConv.toConv LinearMap.id := by rw [hgS]
      _ = WithConv.toConv g := by rw [mul_assoc, LinearMap.antipode_mul_id, mul_one]
  have heval :
      (WithConv.toConv g * WithConv.toConv LinearMap.id).ofConv h =
        TensorProduct.lid R A ((φ ∘ₗ HopfAlgebra.antipode R).rTensor A (Coalgebra.comul h)) := by
    rw [LinearMap.convMul_apply]
    induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul a b => simp [g, Algebra.algebraMap_eq_smul_one]
  have hgh := congrArg (fun u : WithConv (A →ₗ[R] A) ↦ u.ofConv h) hgid
  rw [heval] at hgh
  simpa [g, Algebra.algebraMap_eq_smul_one] using hgh

end HopfAlgebra

section FiniteProjectiveBialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- On a finite projective bialgebra, right integrals of `ConvolutionDual` are precisely right
cointegrals. -/
@[simp]
theorem toConv_mem_rightIntegral_iff (φ : Module.Dual R A) :
    WithConv.toConv φ ∈ rightIntegral R (ConvolutionDual R A) ↔ IsRightCointegral φ := by
  rw [mem_rightIntegral_iff, isRightCointegral_iff_convMul]
  simp [ConvolutionDual.counit_apply]

/-- On a finite projective bialgebra, left integrals of `ConvolutionDual` are precisely left
cointegrals. -/
@[simp]
theorem toConv_mem_leftIntegral_iff (φ : Module.Dual R A) :
    WithConv.toConv φ ∈ leftIntegral R (ConvolutionDual R A) ↔ IsLeftCointegral φ := by
  rw [mem_leftIntegral_iff, isLeftCointegral_iff_convMul]
  simp [ConvolutionDual.counit_apply]

variable (R A) in
/-- Linear equivalence identifying right cointegrals of a finite projective bialgebra with right
integrals of its convolution dual. -/
noncomputable def rightCointegralsEquivRightIntegral :
    rightCointegrals R A ≃ₗ[R] rightIntegral R (ConvolutionDual R A) where
  toFun φ :=
    ⟨WithConv.toConv φ.1, (toConv_mem_rightIntegral_iff φ.1).mpr ((mem_rightCointegrals _).mp φ.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    ⟨ψ.1.ofConv,
      (mem_rightCointegrals _).mpr ((toConv_mem_rightIntegral_iff ψ.1.ofConv).mp (by simp))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem rightCointegralsEquivRightIntegral_coe (φ : rightCointegrals R A) :
    (rightCointegralsEquivRightIntegral R A φ : ConvolutionDual R A) =
      WithConv.toConv (φ : Module.Dual R A) :=
  (rfl)

@[simp]
theorem rightCointegralsEquivRightIntegral_symm_coe (ψ : rightIntegral R (ConvolutionDual R A)) :
    ((rightCointegralsEquivRightIntegral R A).symm ψ : Module.Dual R A) =
      (ψ : ConvolutionDual R A).ofConv :=
  (rfl)

variable (R A) in
/-- Linear equivalence identifying left cointegrals of a finite projective bialgebra with left
integrals of its convolution dual. -/
noncomputable def leftCointegralsEquivLeftIntegral :
    leftCointegrals R A ≃ₗ[R] leftIntegral R (ConvolutionDual R A) where
  toFun φ :=
    ⟨WithConv.toConv φ.1, (toConv_mem_leftIntegral_iff φ.1).mpr ((mem_leftCointegrals _).mp φ.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    ⟨ψ.1.ofConv,
      (mem_leftCointegrals _).mpr ((toConv_mem_leftIntegral_iff ψ.1.ofConv).mp (by simp))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem leftCointegralsEquivLeftIntegral_coe (φ : leftCointegrals R A) :
    (leftCointegralsEquivLeftIntegral R A φ : ConvolutionDual R A) =
      WithConv.toConv (φ : Module.Dual R A) :=
  (rfl)

@[simp]
theorem leftCointegralsEquivLeftIntegral_symm_coe (ψ : leftIntegral R (ConvolutionDual R A)) :
    ((leftCointegralsEquivLeftIntegral R A).symm ψ : Module.Dual R A) =
      (ψ : ConvolutionDual R A).ofConv :=
  (rfl)

end FiniteProjectiveBialgebra

end TauCeti
