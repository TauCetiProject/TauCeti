/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LambdaRing.Adams
import TauCeti.RingTheory.Binomial

/-!
# Examples of pre-λ structures

These examples test the definitions of pre-λ structures, their morphisms, λ-ideals, line
elements and Adams operations against the standard small cases.

* In the binomial structure on `ℤ`, `λ² 2 = 1` and `λ² 1 = 0`, so `λ²` is not additive and the
  ideal `(2)` is not a λ-ideal: a quotient structure on `ℤ ⧸ (2)` would identify `λ² 2 = 1` with
  `λ² 0 = 0`.
* The total operation `λ_t m = (1 + t + t²)ᵐ` defines a second pre-λ structure on `ℤ`, with
  `λ² 1 = 1`. There is no morphism from the binomial structure to it, so the identity of `ℤ` is
  not a morphism between the two.
* `0` is a line element, and it is not a unit of a nontrivial ring.
* In the line-monomial structure on the Laurent polynomials `ℤ[u, u⁻¹]`,
  `λ² (u + u⁻¹) = u u⁻¹ = 1`.
* For the trivial monoid the line-monomial structure is the binomial structure on `ℤ`.
* Adams operations are not power maps: in the binomial structure on `ℤ`, `ψ² (-1) = -1`, while
  the line `u` of `ℤ[u, u⁻¹]` has `ψ² u = u²`.
* The integral formula `ψ³ x = x³ - 3 x λ² x + 3 λ³ x` gives `ψ³ 2 = 8 - 6 + 0 = 2` in binomial
  `ℤ`, as it must since the binomial Adams operations are the identity.
* In the sum-law structure `λ_t m = (1 + t + t²)ᵐ`, `ψ² 1 = 1 - 2 = -1`, so `ψ²` does not fix
  `1` and is not a ring homomorphism; this structure is not special.

## References

* C. A. Weibel, *The K-book*, §II.4.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.PreLambdaStructure.Examples

/-- In the binomial structure on `ℤ`, `λ² 2 = 1` and `λ² 1 = 0`. -/
example : (binomial ℤ).lambda 2 2 = 1 ∧ (binomial ℤ).lambda 2 1 = 0 :=
  ⟨binomial_lambda_two_two, isLine_binomial_one.lambda_eq_zero le_rfl⟩

/-- `λ²` is not additive in the binomial structure on `ℤ`. -/
example : (binomial ℤ).lambda 2 (1 + 1) ≠ (binomial ℤ).lambda 2 1 + (binomial ℤ).lambda 2 1 := by
  rw [one_add_one_eq_two, binomial_lambda_two_two, isLine_binomial_one.lambda_eq_zero le_rfl]
  decide

/-- The ideal `(2)` of `ℤ` is not a λ-ideal of the binomial structure, since `λ² 2 = 1`. -/
example : ¬ (binomial ℤ).IsLambdaIdeal (Ideal.span {2}) := fun h => by
  have h2 := h.lambda_mem two_ne_zero (Ideal.subset_span (Set.mem_singleton (2 : ℤ)))
  rw [binomial_lambda_two_two, Ideal.mem_span_singleton] at h2
  exact absurd h2 (by decide)

/-- The unit `1 + t + t²` of `ℤ⟦t⟧`. -/
def oneAddXAddXSq : (ℤ⟦X⟧)ˣ :=
  (isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 + X + X ^ 2 : ℤ⟦X⟧)).unit

theorem coe_oneAddXAddXSq : (oneAddXAddXSq : ℤ⟦X⟧) = 1 + X + X ^ 2 :=
  IsUnit.unit_spec _

theorem constantCoeff_oneAddXAddXSq : constantCoeff (oneAddXAddXSq : ℤ⟦X⟧) = 1 := by
  simp [coe_oneAddXAddXSq]

theorem constantCoeff_zpow_oneAddXAddXSq (m : ℤ) :
    constantCoeff (↑(oneAddXAddXSq ^ m) : ℤ⟦X⟧) = 1 := by
  have h : Units.map (constantCoeff (R := ℤ)).toMonoidHom oneAddXAddXSq = 1 :=
    Units.ext constantCoeff_oneAddXAddXSq
  have hm := congrArg Units.val (map_zpow (Units.map (constantCoeff (R := ℤ)).toMonoidHom)
    oneAddXAddXSq m)
  rw [h, one_zpow, Units.val_one, Units.coe_map] at hm
  exact hm

theorem coeff_one_zpow_oneAddXAddXSq (m : ℤ) :
    PowerSeries.coeff 1 (↑(oneAddXAddXSq ^ m) : ℤ⟦X⟧) = m := by
  have hu : PowerSeries.coeff 1 (oneAddXAddXSq : ℤ⟦X⟧) = 1 := by
    simp [coe_oneAddXAddXSq, coeff_X, coeff_X_pow]
  have hstep (k : ℤ) : PowerSeries.coeff 1 (↑(oneAddXAddXSq ^ (k + 1)) : ℤ⟦X⟧) =
      PowerSeries.coeff 1 (↑(oneAddXAddXSq ^ k) : ℤ⟦X⟧) + 1 := by
    rw [zpow_add_one, Units.val_mul, coeff_one_mul, hu, constantCoeff_zpow_oneAddXAddXSq,
      constantCoeff_oneAddXAddXSq]
    ring
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih => rw [hstep, ih]
  | pred k ih =>
    have := hstep (-(k : ℤ) - 1)
    rw [sub_add_cancel, ih] at this
    omega

/-- The total operation `m ↦ (1 + t + t²)ᵐ`. -/
def sumLawTotal : Multiplicative ℤ →* ℤ⟦X⟧ :=
  (Units.coeHom _).comp (zpowersHom _ oneAddXAddXSq)

theorem sumLawTotal_apply (m : Multiplicative ℤ) :
    sumLawTotal m = ↑(oneAddXAddXSq ^ m.toAdd) :=
  (rfl)

/-- The pre-λ structure on `ℤ` with total operation `λ_t m = (1 + t + t²)ᵐ`. -/
def sumLaw : PreLambdaStructure ℤ :=
  ofTotalHom sumLawTotal
    (fun _ => by rw [sumLawTotal_apply]; exact constantCoeff_zpow_oneAddXAddXSq _)
    (fun _ => by rw [sumLawTotal_apply]; exact coeff_one_zpow_oneAddXAddXSq _)

theorem sumLaw_lambda_two_one : sumLaw.lambda 2 1 = 1 := by
  rw [sumLaw, ofTotalHom_lambda, sumLawTotal_apply]
  simp [coe_oneAddXAddXSq, coeff_X, coeff_X_pow]

/-- The sum-law structure has `λ² 1 = 1`, whereas the binomial structure has `λ² 1 = 0`. -/
example : sumLaw.lambda 2 1 = 1 ∧ (binomial ℤ).lambda 2 1 = 0 :=
  ⟨sumLaw_lambda_two_one, isLine_binomial_one.lambda_eq_zero le_rfl⟩

/-- There is no morphism from the binomial structure on `ℤ` to the sum-law structure; in
particular the identity of `ℤ` is not one. -/
example : IsEmpty (PreLambdaHom (binomial ℤ) sumLaw) := by
  refine ⟨fun f => ?_⟩
  have h := f.map_lambda 2 1
  rw [isLine_binomial_one.lambda_eq_zero le_rfl, map_zero, map_one, sumLaw_lambda_two_one] at h
  exact zero_ne_one h

/-- `0` is a line element of every pre-λ structure, and it is not a unit of a nontrivial ring. -/
example (R : Type*) [CommRing R] [Nontrivial R] (Λ : PreLambdaStructure R) :
    Λ.IsLine 0 ∧ ¬ IsUnit (0 : R) :=
  ⟨Λ.isLine_zero, not_isUnit_zero⟩

/-- In the line-monomial structure on the Laurent polynomials `ℤ[u, u⁻¹]`,
`λ² (u + u⁻¹) = 1`. -/
example :
    (lineMonomial (Multiplicative ℤ)).lambda 2
        (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd 1) +
          MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd (-1))) = 1 := by
  simp [lambda_add, Finset.Nat.sum_antidiagonal_succ, Ring.choose_one_of_two_le ℤ le_rfl,
    MonoidAlgebra.one_def]

/-- For the trivial monoid, the line-monomial structure is the binomial structure on `ℤ`. -/
example (n : ℕ) (c : ℤ) :
    MonoidAlgebra.uniqueRingEquiv Unit
        ((lineMonomial Unit).lambda n ((MonoidAlgebra.uniqueRingEquiv Unit).symm c)) =
      (binomial ℤ).lambda n c := by
  rw [MonoidAlgebra.uniqueRingEquiv_symm_apply, lineMonomial_lambda_single]
  simp

/-- In the binomial structure on `ℤ`, `ψ² (-1) = -1`, whereas `(-1) ^ 2 = 1`: Adams operations
are not power maps. -/
example : (binomial ℤ).adams 2 (-1) = -1 ∧ (-1 : ℤ) ^ 2 = 1 :=
  ⟨binomial_adams_apply two_ne_zero _, by norm_num⟩

/-- In the line-monomial structure on the Laurent polynomials `ℤ[u, u⁻¹]`, `ψ² u = u²`. -/
example :
    (lineMonomial (Multiplicative ℤ)).adams 2 (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd 1)) =
      MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd 2) := by
  rw [lineMonomial_adams_of two_ne_zero, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

/-- The integral formula for `ψ³` in binomial `ℤ`: `ψ³ 2 = 2³ - 3 · 2 · λ² 2 + 3 λ³ 2 = 2`. -/
example : (binomial ℤ).adams 3 2 = 2 := by
  rw [adams_three, binomial_lambda_two_two, ← Nat.cast_ofNat (R := ℤ) (n := 2),
    binomial_lambda_natCast]
  norm_num

/-- In the sum-law structure on `ℤ`, `ψ² 1 = -1`, so `ψ²` is not a ring homomorphism. -/
example : sumLaw.adams 2 1 = -1 := by
  rw [adams_two, sumLaw_lambda_two_one]
  norm_num

end TauCeti.PreLambdaStructure.Examples
