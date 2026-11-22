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
duals. No commutativity or star structure is assumed.

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

/-- In any representation `∑ aᵢ' ⊗ aᵢ''` of the coproduct of `a`, `∑ S⁻¹(aᵢ'') * aᵢ' = ε(a) • 1`.
This is the Sweedler form of `mul_inverseAntipode_rTensor_comm_comul_apply`. -/
theorem sum_inverseAntipode_mul_eq_smul (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    {a : H} {ι : Type*} (r : Coalgebra.Repr R a ι) :
    ∑ i ∈ r.index, inverseAntipode hS (r.right i) * r.left i = Coalgebra.counit (R := R) a • 1 := by
  simpa [← r.eq, map_sum, Algebra.smul_def] using mul_inverseAntipode_rTensor_comm_comul_apply hS a

/-- In any representation `∑ aᵢ' ⊗ aᵢ''` of the coproduct of `a`, `∑ aᵢ'' * S⁻¹(aᵢ') = ε(a) • 1`.
This is the Sweedler form of `mul_inverseAntipode_lTensor_comm_comul_apply`. -/
theorem sum_mul_inverseAntipode_eq_smul (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    {a : H} {ι : Type*} (r : Coalgebra.Repr R a ι) :
    ∑ i ∈ r.index, r.right i * inverseAntipode hS (r.left i) = Coalgebra.counit (R := R) a • 1 := by
  simpa [← r.eq, map_sum, Algebra.smul_def] using mul_inverseAntipode_lTensor_comm_comul_apply hS a

end TauCeti.HopfAlgebra
