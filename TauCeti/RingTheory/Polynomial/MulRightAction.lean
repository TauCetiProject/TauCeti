/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial actions by right multiplication

For an algebra `Λ` over a commutative semiring `R`, `polynomialMulRightAction R ρ₀` lets
`Λ[X]` act on `Λ`: coefficients multiply on the left, while `X` multiplies on the right by
`ρ₀`. These operations commute even when `Λ` is noncommutative. The coefficient formula and
ideal-preservation lemmas allow polynomial relations to be evaluated modulo two-sided ideals.

The construction is used in Ribet's polynomial argument, following
`New.Selmer.exists_ribet_polynomial` in lsernau/grh-lean (Apache 2.0).
-/

public section

open Polynomial

namespace TauCeti

section Semiring

variable {R Λ : Type*} [CommSemiring R] [Semiring Λ] [Algebra R Λ]

variable (R) in
/-- `Λ[X]` acting on `Λ`: a coefficient acts by left multiplication and `X` by right
multiplication by `ρ₀`. -/
noncomputable def polynomialMulRightAction (ρ₀ : Λ) : Λ[X] →+* Module.End R Λ :=
  eval₂RingHom' (Algebra.lmul R Λ).toRingHom (LinearMap.mulRight R ρ₀)
    fun a ↦ LinearMap.commute_mulLeft_right a ρ₀

/-- A finite coefficient formula for the action by right multiplication. -/
theorem polynomialMulRightAction_apply (ρ₀ : Λ) {p : Λ[X]} {n : ℕ} (hn : p.natDegree < n)
    (q : Λ) : polynomialMulRightAction R ρ₀ p q =
      ∑ i ∈ Finset.range n, p.coeff i * (q * ρ₀ ^ i) := by
  simp [polynomialMulRightAction, eval₂_eq_sum_range' _ hn, LinearMap.sum_apply,
    LinearMap.pow_mulRight]

/-- A constant polynomial acts by left multiplication. -/
@[simp] theorem polynomialMulRightAction_C (ρ₀ a q : Λ) :
    polynomialMulRightAction R ρ₀ (C a) q = a * q := by
  simp [polynomialMulRightAction]

/-- The variable acts by right multiplication by the chosen element. -/
@[simp] theorem polynomialMulRightAction_X (ρ₀ q : Λ) :
    polynomialMulRightAction R ρ₀ X q = q * ρ₀ := by
  simp [polynomialMulRightAction]

/-- A polynomial over the scalar ring acts by right multiplication by its evaluation. -/
@[simp] theorem polynomialMulRightAction_map_algebraMap (ρ₀ : Λ) (F : R[X]) (q : Λ) :
    polynomialMulRightAction R ρ₀ (F.map (algebraMap R Λ)) q = q * aeval ρ₀ F := by
  have hn : (F.map (algebraMap R Λ)).natDegree < F.natDegree + 1 :=
    (natDegree_map_le).trans_lt (Nat.lt_succ_self _)
  rw [polynomialMulRightAction_apply ρ₀ hn, aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_map, Algebra.smul_def, ← mul_assoc, Algebra.commutes, mul_assoc]

end Semiring

variable {R Λ : Type*} [CommSemiring R] [Ring Λ] [Algebra R Λ]

/-- The polynomial action preserves every two-sided ideal. -/
theorem _root_.TwoSidedIdeal.polynomialMulRightAction_mem (𝔞 : TwoSidedIdeal Λ) (ρ₀ : Λ)
    (p : Λ[X]) {q : Λ} (hq : q ∈ 𝔞) : polynomialMulRightAction R ρ₀ p q ∈ 𝔞 := by
  rw [polynomialMulRightAction_apply ρ₀ (Nat.lt_succ_self _)]
  exact sum_mem fun i _ ↦ 𝔞.mul_mem_left _ _ (𝔞.mul_mem_right _ _ hq)

/-- A polynomial whose coefficients lie in a two-sided ideal acts into that ideal. -/
theorem _root_.TwoSidedIdeal.polynomialMulRightAction_mem_of_coeff_mem (𝔞 : TwoSidedIdeal Λ)
    (ρ₀ : Λ) {p : Λ[X]} (hp : ∀ k, p.coeff k ∈ 𝔞) (q : Λ) :
    polynomialMulRightAction R ρ₀ p q ∈ 𝔞 := by
  rw [polynomialMulRightAction_apply ρ₀ (Nat.lt_succ_self _)]
  exact sum_mem fun i _ ↦ 𝔞.mul_mem_right _ _ (hp i)

end TauCeti
