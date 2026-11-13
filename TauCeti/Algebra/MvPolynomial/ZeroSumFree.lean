/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.Algebra.Group.Units.ZeroSumFree

/-!
# Zero-sum-free polynomial evaluation

Multivariate polynomials over a zero-sum-free semiring are zero-sum-free coefficientwise.
Evaluation at units in a zero-sum-free semiring reflects zero if the coefficient map does.
-/

public section

namespace MvPolynomial

open TauCeti

variable {K R S : Type*} [CommSemiring R] [CommSemiring S]

instance [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (MvPolynomial K R)) :=
  Subsingleton.addUnits_of_isAddUnit fun p hp => by
    obtain ⟨q, h⟩ := hp.exists_neg
    ext d
    have hd : p.coeff d + q.coeff d = 0 := by
      simpa using congrArg (fun f : MvPolynomial K R => f.coeff d) h
    simpa using (add_eq_zero.mp hd).1

/-- Evaluating at units in a zero-sum-free semiring reflects zero when the coefficient map
reflects zero. The values of the variables need not be distinct. -/
theorem eval₂Hom_units_eq_zero_iff [Subsingleton (AddUnits S)] (f : R →+* S)
    (hf : ∀ a, f a = 0 → a = 0) (y : K → Sˣ) (p : MvPolynomial K R) :
    eval₂Hom f (fun i => (y i : S)) p = 0 ↔ p = 0 := by
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
    have he : eval₂Hom f (fun i => (y i : S)) p * (y i : S) = 0 := by simpa using h
    have hz := (y i).mul_left_inj.mp (he.trans (zero_mul _).symm)
    simp [hp hz]

end MvPolynomial
