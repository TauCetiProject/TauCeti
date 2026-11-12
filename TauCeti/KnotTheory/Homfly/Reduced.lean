/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Homfly.Existence
public import TauCeti.KnotTheory.Jimbo.ReducedTrace

/-!
# The HOMFLY polynomial with unknot value one

The unreduced HOMFLY polynomial of a nonempty braid closure is divisible by the quantum
dimension `(a - a⁻¹) / z`. Its quotient, `TauCeti.MarkovBraid.reducedHomfly`, is a Laurent
polynomial with unknot value one. It is invariant under Markov equivalence and satisfies
`a P(L₊) - a⁻¹ P(L₋) = z P(L₀)`. Adding an uncrossed strand multiplies it by the quantum
dimension, so the unlink on `n + 1` components has value `((a - a⁻¹) / z) ^ n`.

The quotient is constructed in the Laurent polynomial ring, without inverting the quantum
dimension or requiring its specializations to be nonzero. It is characterized by multiplication
by that dimension; its positive-rank `sl_N` specializations recover the existing reduced
Jimbo traces.

The divisibility comes from the same Hecke spanning argument as the unreduced interpolation,
with its submodule restricted to polynomials divisible by the unknot value. No choice of a
component of a link is needed. The presentation is a braid closure; no classification of
geometric knots by Markov equivalence is asserted.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 4–6.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
-/

public noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace MarkovBraid

open KnotTheory

variable (K : Type*) [Field K]

/-- The classical HOMFLY polynomial of a braid closure, normalized to have unknot value one.
It is the Laurent polynomial quotient of `homfly` by `(a - a⁻¹) / z`. -/
def reducedHomfly (β : MarkovBraid) : LaurentPolynomial (LaurentPolynomial K) :=
  (homflyUnknot_dvd_homfly K β).choose

/-- Multiplying the reduced HOMFLY polynomial by the quantum dimension recovers the
unreduced polynomial. -/
@[simp]
theorem homflyUnknot_mul_reducedHomfly (β : MarkovBraid) :
    homflyUnknot K * β.reducedHomfly K = β.homfly K :=
  (homflyUnknot_dvd_homfly K β).choose_spec.symm

/-- A Laurent polynomial is the reduced HOMFLY polynomial exactly when multiplying it by
the unknot value gives the unreduced polynomial. -/
theorem reducedHomfly_eq_iff {β : MarkovBraid}
    {P : LaurentPolynomial (LaurentPolynomial K)} :
    β.reducedHomfly K = P ↔ homflyUnknot K * P = β.homfly K := by
  rw [← homflyUnknot_mul_reducedHomfly, mul_right_inj' (homflyUnknot_ne_zero K)]
  exact eq_comm

/-- Every positive-rank `sl_N` specialization of the reduced HOMFLY polynomial is the
reduced Jimbo trace at the rational-function variable. -/
@[simp]
theorem homflySpecialization_reducedHomfly (β : MarkovBraid) (N : ℕ) :
    homflySpecialization K (N + 1) (β.reducedHomfly K) =
      β.jimboReducedTrace (N := N + 1)
        (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero) := by
  rw [jimboReducedTrace_def, eq_div_iff (jimboWeight_sum_X_ne_zero N), mul_comm,
    ← homflySpecialization_homflyUnknot, ← map_mul, homflyUnknot_mul_reducedHomfly,
    homflySpecialization_homfly]

/-- The positive-rank reduced Jimbo specializations uniquely characterize the reduced
HOMFLY polynomial. -/
theorem reducedHomfly_eq_of_homflySpecialization_eq {β : MarkovBraid}
    {P : LaurentPolynomial (LaurentPolynomial K)}
    (h : ∀ N, homflySpecialization K (N + 1) P =
      β.jimboReducedTrace (N := N + 1)
        (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) :
    β.reducedHomfly K = P := by
  apply homflySpecialization_jointly_injective K
  funext N
  simpa only [homflySpecialization_reducedHomfly] using (h N).symm

/-- The reduced HOMFLY polynomial of the unlink on `n + 1` components. In particular, the
one-strand unknot has value one. -/
@[simp]
theorem reducedHomfly_one (n : ℕ) : reducedHomfly K ⟨n, 1⟩ = homflyUnknot K ^ n := by
  rw [reducedHomfly_eq_iff, homfly_one, pow_succ']

/-- The reduced HOMFLY polynomial satisfies the oriented skein relation in every braid
context, with the same parameters as the unreduced polynomial. -/
theorem reducedHomfly_skein {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    T 1 * reducedHomfly K ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ -
        T (-1) * reducedHomfly K ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ =
      C (T 1) * reducedHomfly K ⟨n, b * c⟩ := by
  apply mul_left_cancel₀ (homflyUnknot_ne_zero K)
  simpa only [mul_sub, mul_left_comm (homflyUnknot K), homflyUnknot_mul_reducedHomfly] using
    homfly_skein K b c i

/-- Adding an uncrossed strand multiplies the reduced HOMFLY polynomial by the unreduced
unknot value, as expected for disjoint union with an unknot. -/
@[simp]
theorem reducedHomfly_strandIncl {n : ℕ} (b : BraidGroup (n + 1)) :
    reducedHomfly K ⟨n + 1, BraidGroup.strandIncl b⟩ =
      homflyUnknot K * reducedHomfly K ⟨n, b⟩ := by
  rw [reducedHomfly_eq_iff, homfly_strandIncl, mul_left_comm,
    homflyUnknot_mul_reducedHomfly]

end MarkovBraid

/-- Markov-equivalent braids have the same classical, unknot-normalized HOMFLY polynomial. -/
theorem MarkovEquiv.reducedHomfly_eq (K : Type*) [Field K] {β γ : MarkovBraid}
    (h : MarkovEquiv β γ) : β.reducedHomfly K = γ.reducedHomfly K := by
  rw [MarkovBraid.reducedHomfly_eq_iff, MarkovBraid.homflyUnknot_mul_reducedHomfly]
  exact h.homfly_eq K |>.symm

namespace MarkovBraid

open KnotTheory

variable (K : Type*) [Field K]

/-- The single positive crossing on two strands closes to the unknot. -/
@[simp]
theorem reducedHomfly_sigma : reducedHomfly K ⟨1, BraidGroup.sigma (n := 2) 0⟩ = 1 := by
  simpa using markovEquiv_sigma_last_one_one.reducedHomfly_eq K

/-- The positive Hopf link, presented by the square of the two-strand generator. -/
theorem reducedHomfly_sigma_pow_two : reducedHomfly K ⟨1, (BraidGroup.sigma (n := 2) 0) ^ 2⟩ =
    T (-1) * C (T 1) + T (-2) * homflyUnknot K := by
  have h := reducedHomfly_skein K (BraidGroup.sigma (n := 2) 0) 1 0
  simp only [mul_one, mul_inv_cancel, reducedHomfly_one, reducedHomfly_sigma, pow_one] at h
  rw [pow_two]
  apply mul_left_cancel₀ (isUnit_T (R := LaurentPolynomial K) 1).ne_zero
  calc
    _ = C (T 1) + T (-1) * homflyUnknot K := eq_add_of_sub_eq h
    _ = _ := by
      simp only [mul_add, ← mul_assoc, ← T_add]
      norm_num

/-- The HOMFLY polynomial of the right-handed trefoil, presented by the cube of the
positive two-strand generator, is `a⁻² z² + 2 a⁻² - a⁻⁴`. -/
theorem reducedHomfly_sigma_pow_three : reducedHomfly K ⟨1, (BraidGroup.sigma (n := 2) 0) ^ 3⟩ =
    T (-2) * C (T 2) + 2 * T (-2) - T (-4) := by
  have h₂ := reducedHomfly_sigma_pow_two K
  have hc : (BraidGroup.sigma (n := 2) 0) ^ 2 * (BraidGroup.sigma (n := 2) 0)⁻¹ =
      BraidGroup.sigma (n := 2) 0 := by simp [pow_succ]
  have hz : (C (T 1) : LaurentPolynomial (LaurentPolynomial K)) * C (T (-1)) = 1 := by
    rw [← map_mul, ← T_add]
    norm_num
  have hz₂ : (C (T 1) : LaurentPolynomial (LaurentPolynomial K)) * C (T 1) = C (T 2) := by
    rw [← map_mul, ← T_add]
    norm_num
  have h := reducedHomfly_skein K ((BraidGroup.sigma (n := 2) 0) ^ 2) 1 0
  simp only [mul_one, hc, ← pow_succ, reducedHomfly_sigma, h₂] at h
  apply mul_left_cancel₀ (isUnit_T (R := LaurentPolynomial K) 1).ne_zero
  calc
    _ = C (T 1) * (T (-1) * C (T 1) + T (-2) * homflyUnknot K) + T (-1) :=
      eq_add_of_sub_eq h
    _ = _ := by
      rw [homflyUnknot_def]
      simp only [mul_add, mul_sub, sub_mul, ← mul_assoc, ← T_add]
      -- Normalize the integer exponents, leaving (in a,z notation)
      -- a⁻¹ z z + (a⁻¹ - a⁻³) z z⁻¹ + a⁻¹ = a⁻¹ z² + 2 a⁻¹ - a⁻³.
      norm_num
      linear_combination T (-1) * hz₂ + (T (-1) - T (-3)) * hz

end MarkovBraid

end TauCeti
