/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Evaluation of zero-sum-free polynomials

For a zero-sum-free semiring `S`, spelled `Subsingleton (AddUnits S)`, a polynomial's variable
values may be any non-zero-divisors. Evaluation reflects zero exactly when its coefficient map
does. Applied to natural-coefficient polynomials, this supplies the units needed to extend
evaluation through the regular localization.
-/

public section

namespace MvPolynomial

variable {K R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluation into a zero-sum-free semiring reflects zero when the coefficient map does and
every variable is assigned a non-zero-divisor. -/
theorem eval₂_eq_zero_iff [Subsingleton (AddUnits S)] (f : R →+* S)
    (hf : ∀ a, f a = 0 → a = 0) {y : K → S} (hy : ∀ i, y i ∈ nonZeroDivisors S)
    (p : MvPolynomial K R) : eval₂ f y p = 0 ↔ p = 0 := by
  rw [← coe_eval₂Hom]
  refine ⟨?_, fun h => by simp [h]⟩
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro h
    simp [hf a (by simpa using h)]
  | add p q hp hq =>
    rw [map_add, add_eq_zero]
    rintro ⟨h₁, h₂⟩
    simp [hp h₁, hq h₂]
  | mul_X p i hp =>
    intro h
    have he : eval₂Hom f y p * y i = 0 := by simpa using h
    have hz := mul_right_mem_nonZeroDivisors_eq_zero_iff (hy i) |>.mp he
    simp [hp hz]

/-- Evaluation at units in a zero-sum-free semiring reflects zero when the coefficient map does.
The values of the variables need not be distinct. -/
theorem eval₂Hom_units_eq_zero_iff [Subsingleton (AddUnits S)] (f : R →+* S)
    (hf : ∀ a, f a = 0 → a = 0) (y : K → Sˣ) (p : MvPolynomial K R) :
    eval₂Hom f (fun i => (y i : S)) p = 0 ↔ p = 0 := by
  change eval₂ f (fun i => (y i : S)) p = 0 ↔ p = 0
  exact eval₂_eq_zero_iff f hf (fun i => (y i).isUnit.mem_nonZeroDivisors) p

end MvPolynomial
