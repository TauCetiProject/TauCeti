/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The inverse of a bijective antipode

For a Hopf algebra with explicitly supplied bijective antipode, `inverseAntipode`
is its inverse linear map. It reverses multiplication, and its two inverse laws
allow the contragredient actions through `S` and `S⁻¹` to cancel on mixed double
duals. No commutativity or star structure is assumed. In a finite representation
`∑ a₁ ⊗ a₂` of the coproduct, its cancellation identities read `∑ S⁻¹(a₂) a₁ = ε(a)` and
`∑ a₂ S⁻¹(a₁) = ε(a)`.

Bijectivity holds in particular when `S²` is an inner automorphism `a ↦ g a g⁻¹`
(`antipode_bijective_of_antipode_antipode`), as for the group-like element `K⁻¹` of
`U_q(sl₂)`, and when `S` is involutive, as in a cocommutative Hopf algebra, where
`inverseAntipode` agrees with `antipode` (`inverseAntipode_eq_antipode_of_involutive` and
`inverseAntipode_eq_antipode_of_isCocomm`).

The construction uses Mathlib's `LinearEquiv.ofBijective`. See C. Kassel,
*Quantum Groups*, Chapter III, for inverse-antipode duality.
-/

public noncomputable section

namespace TauCeti.HopfAlgebra

open _root_.HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- If the square of the antipode is the inner automorphism `a ↦ g a g⁻¹` of a unit `g`, then
the antipode is bijective. -/
theorem antipode_bijective_of_antipode_antipode {g : Hˣ}
    (hg : ∀ a : H, antipode R (antipode R a) = g * a * ↑g⁻¹) :
    Function.Bijective (antipode R : H →ₗ[R] H) := by
  have h : Function.Bijective ((antipode R : H →ₗ[R] H) ∘ antipode R) := by
    simpa only [Function.comp_def, hg] using
      (Units.mulRight_bijective g⁻¹).comp (Units.mulLeft_bijective g)
  exact ⟨.of_comp h.1, .of_comp h.2⟩

/-- The inverse linear map of an explicitly bijective antipode. -/
def inverseAntipode (hS : Function.Bijective (antipode R : H →ₗ[R] H)) : H →ₗ[R] H :=
  (LinearEquiv.ofBijective (antipode R) hS).symm.toLinearMap

/-- Applying the antipode after its inverse gives the original element. -/
@[simp]
theorem antipode_inverseAntipode (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (a : H) :
    antipode R (inverseAntipode hS a) = a :=
  (LinearEquiv.ofBijective (antipode R) hS).apply_symm_apply a

/-- Applying the inverse antipode after the antipode gives the original element. -/
@[simp]
theorem inverseAntipode_antipode (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (a : H) :
    inverseAntipode hS (antipode R a) = a :=
  (LinearEquiv.ofBijective (antipode R) hS).symm_apply_apply a

/-- When the antipode is involutive, its inverse linear map is the antipode itself. -/
theorem inverseAntipode_eq_antipode_of_involutive (h : Function.Involutive (antipode R : H →ₗ[R] H))
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) :
    inverseAntipode hS = antipode R := by
  ext a
  exact hS.injective (by simp [h a])

/-- In a cocommutative Hopf algebra, the inverse of the antipode is the antipode itself. -/
@[simp]
theorem inverseAntipode_eq_antipode_of_isCocomm [Coalgebra.IsCocomm R H]
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) :
    inverseAntipode hS = antipode R :=
  inverseAntipode_eq_antipode_of_involutive antipode_involutive_of_isCocomm hS

/-- The inverse antipode preserves the unit. -/
@[simp]
theorem inverseAntipode_one (hS : Function.Bijective (antipode R : H →ₗ[R] H)) :
    inverseAntipode hS 1 = 1 := by
  apply hS.injective
  simp

/-- The inverse antipode reverses multiplication. -/
theorem inverseAntipode_mul (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (a b : H) :
    inverseAntipode hS (a * b) = inverseAntipode hS b * inverseAntipode hS a := by
  apply hS.injective
  simp [antipode_mul_antidistrib]

/-- The inverse antipode fixes the scalar algebra map. -/
@[simp]
theorem inverseAntipode_algebraMap (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (r : R) :
    inverseAntipode hS (algebraMap R H r) = algebraMap R H r := by
  simp [Algebra.algebraMap_eq_smul_one]

open scoped TensorProduct

/-- The inverse antipode cancels the first leg of the reversed coproduct. This is the
antipode identity used for evaluation of an inverse-antipode contragredient. -/
@[simp]
theorem mul_inverseAntipode_rTensor_comm_comul_apply
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (a : H) :
    LinearMap.mul' R H ((inverseAntipode hS).rTensor H
      (TensorProduct.comm R H H (Coalgebra.comul a))) = algebraMap R H (Coalgebra.counit a) := by
  have ht (t : H ⊗[R] H) :
      inverseAntipode hS (LinearMap.mul' R H ((antipode R).rTensor H t)) =
        LinearMap.mul' R H ((inverseAntipode hS).rTensor H (TensorProduct.comm R H H t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [inverseAntipode_mul]
    | add t s ht hs => simp [ht, hs]
  rw [← ht, mul_antipode_rTensor_comul_apply, inverseAntipode_algebraMap]

/-- The inverse antipode cancels the second leg of the reversed coproduct. This is the
antipode identity used for coevaluation of an inverse-antipode contragredient. -/
@[simp]
theorem mul_inverseAntipode_lTensor_comm_comul_apply
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) (a : H) :
    LinearMap.mul' R H ((inverseAntipode hS).lTensor H
      (TensorProduct.comm R H H (Coalgebra.comul a))) = algebraMap R H (Coalgebra.counit a) := by
  have ht (t : H ⊗[R] H) :
      inverseAntipode hS (LinearMap.mul' R H ((antipode R).lTensor H t)) =
        LinearMap.mul' R H ((inverseAntipode hS).lTensor H (TensorProduct.comm R H H t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [inverseAntipode_mul]
    | add t s ht hs => simp [ht, hs]
  rw [← ht, mul_antipode_lTensor_comul_apply, inverseAntipode_algebraMap]

/-- The inverse antipode cancels the first leg of the reversed coproduct, in any finite
representation `∑ᵢ a₁ᵢ ⊗ a₂ᵢ` of the coproduct of `a`: `∑ᵢ S⁻¹(a₂ᵢ) a₁ᵢ = ε(a)`. -/
theorem sum_inverseAntipode_mul_eq_algebraMap_counit
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) {a : H} {ι : Type*}
    (𝓡 : Coalgebra.Repr R a ι) :
    ∑ i ∈ 𝓡.index, inverseAntipode hS (𝓡.right i) * 𝓡.left i =
      algebraMap R H (Coalgebra.counit a) := by
  simpa [← 𝓡.eq, map_sum] using mul_inverseAntipode_rTensor_comm_comul_apply hS a

/-- The inverse antipode cancels the second leg of the reversed coproduct, in any finite
representation `∑ᵢ a₁ᵢ ⊗ a₂ᵢ` of the coproduct of `a`: `∑ᵢ a₂ᵢ S⁻¹(a₁ᵢ) = ε(a)`. -/
theorem sum_mul_inverseAntipode_eq_algebraMap_counit
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) {a : H} {ι : Type*}
    (𝓡 : Coalgebra.Repr R a ι) :
    ∑ i ∈ 𝓡.index, 𝓡.right i * inverseAntipode hS (𝓡.left i) =
      algebraMap R H (Coalgebra.counit a) := by
  simpa [← 𝓡.eq, map_sum] using mul_inverseAntipode_lTensor_comm_comul_apply hS a

/-- Coassociativity and the inverse antipode cancel in the reversed first factor of an iterated
coproduct: `∑ S⁻¹(a₂₁) a₁ ⊗ a₂₂ = 1 ⊗ a`, in finite representations `∑ᵢ a₁ᵢ ⊗ a₂ᵢ` of the
coproduct of `a` and `∑ⱼ a₂ᵢ₁ⱼ ⊗ a₂ᵢ₂ⱼ` of the coproduct of each `a₂ᵢ`. -/
theorem sum_inverseAntipode_mul_tmul_eq
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) {a : H} {ι : Type*} {κ : ι → Type*}
    (𝓡 : Coalgebra.Repr R a ι) (𝓡₂ : (i : ι) → Coalgebra.Repr R (𝓡.right i) (κ i)) :
    ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓡₂ i).index,
      (inverseAntipode hS ((𝓡₂ i).left j) * 𝓡.left i) ⊗ₜ[R] (𝓡₂ i).right j = 1 ⊗ₜ[R] a := by
  -- Apply `x ⊗ y ⊗ z ↦ S⁻¹(y) x ⊗ z` to coassociativity, then cancel `∑ S⁻¹(b₂) b₁ = ε(b)`.
  let Ψ : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    (TensorProduct.lift (LinearMap.mul R H ∘ₗ inverseAntipode hS).flip).rTensor H ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have key := congrArg Ψ (Coalgebra.sum_tmul_tmul_eq 𝓡
    (fun i => Coalgebra.Repr.arbitrary R (𝓡.left i)) 𝓡₂)
  conv_rhs => rw [← Coalgebra.sum_counit_smul 𝓡, TensorProduct.tmul_sum]
  simpa [Ψ, ← TensorProduct.sum_tmul, sum_inverseAntipode_mul_eq_algebraMap_counit,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul'] using key.symm

/-- Coassociativity and the inverse antipode cancel in the first factor of an iterated coproduct:
`∑ a₂₁ S⁻¹(a₁) ⊗ a₂₂ = 1 ⊗ a`, in finite representations `∑ᵢ a₁ᵢ ⊗ a₂ᵢ` of the coproduct of `a`
and `∑ⱼ a₂ᵢ₁ⱼ ⊗ a₂ᵢ₂ⱼ` of the coproduct of each `a₂ᵢ`. -/
theorem sum_mul_inverseAntipode_tmul_eq
    (hS : Function.Bijective (antipode R : H →ₗ[R] H)) {a : H} {ι : Type*} {κ : ι → Type*}
    (𝓡 : Coalgebra.Repr R a ι) (𝓡₂ : (i : ι) → Coalgebra.Repr R (𝓡.right i) (κ i)) :
    ∑ i ∈ 𝓡.index, ∑ j ∈ (𝓡₂ i).index,
      ((𝓡₂ i).left j * inverseAntipode hS (𝓡.left i)) ⊗ₜ[R] (𝓡₂ i).right j = 1 ⊗ₜ[R] a := by
  -- Apply `x ⊗ y ⊗ z ↦ y S⁻¹(x) ⊗ z` to coassociativity, then cancel `∑ b₂ S⁻¹(b₁) = ε(b)`.
  let Ψ : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    (TensorProduct.lift ((LinearMap.mul R H).flip ∘ₗ inverseAntipode hS)).rTensor H ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have key := congrArg Ψ (Coalgebra.sum_tmul_tmul_eq 𝓡
    (fun i => Coalgebra.Repr.arbitrary R (𝓡.left i)) 𝓡₂)
  conv_rhs => rw [← Coalgebra.sum_counit_smul 𝓡, TensorProduct.tmul_sum]
  simpa [Ψ, ← TensorProduct.sum_tmul, sum_mul_inverseAntipode_eq_algebraMap_counit,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul'] using key.symm

end TauCeti.HopfAlgebra
