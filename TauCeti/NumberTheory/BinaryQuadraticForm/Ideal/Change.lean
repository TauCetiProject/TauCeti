/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Proper
public import TauCeti.Algebra.QuadraticAlgebra.NormTrace
public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Form ideals under proper changes of variables

For the left action `γ • f = f ∘ γ⁻¹`, write `γ = !![p,q;r,s]` and
`β = (-b + √D)/2`. The transformed ideal is the original ideal multiplied by
`star (a s + r β) / a`. This factor has norm `a'/a`, where `a'` is the transformed
leading coefficient. In particular its norm is positive precisely when the two leading
coefficients have the same sign; this is the comparison needed for the oriented narrow class.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra FractionalIdeal
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- The ideal-scaling factor for the left proper-equivalence action. -/
def idealChangeFactor (f : BinaryQuadraticForm ℤ) (D : ℤ) [Fact (¬ IsSquare D)]
    (γ : SL(2, ℤ)) : QuadraticAlgebra ℚ (D : ℚ) 0 :=
  star (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 1 0 • f.idealGenerator D) / f.a

/-- Scaling the first changed basis vector gives the new leading coefficient. -/
theorem idealChangeFactor_mul_first (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ *
      (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 1 0 • f.idealGenerator D) =
        (γ • f).a := by
  have ha : (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by
    exact_mod_cast (a_ne_zero_of_not_isSquare_discrim (f := f) (by rw [hf]; exact Fact.out))
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  rw [idealChangeFactor, div_mul_eq_mul_div, div_eq_iff ha]
  ext <;> simp [smul_a, pow_two]
  · linear_combination (γ 1 0 : ℚ) ^ 2 / 4 * hd
  · ring

/-- Scaling the second changed basis vector gives the new second ideal generator. -/
theorem idealChangeFactor_mul_second (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ *
      (γ 0 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 0 0 • f.idealGenerator D) =
        (γ • f).idealGenerator D := by
  have ha : (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by
    exact_mod_cast (a_ne_zero_of_not_isSquare_discrim (f := f) (by rw [hf]; exact Fact.out))
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  have hdet : (γ 0 0 : ℚ) * (γ 1 1 : ℚ) - (γ 0 1 : ℚ) * (γ 1 0 : ℚ) = 1 := by
    exact_mod_cast (show γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using γ.det_coe)
  rw [idealChangeFactor, div_mul_eq_mul_div, div_eq_iff ha]
  ext <;> simp [smul_b]
  · linear_combination (γ 0 0 : ℚ) * (γ 1 0 : ℚ) / 4 * hd
  · linear_combination (f.a : ℚ) / 2 * hdet

/-- The scaling factor has norm equal to the ratio of leading coefficients. -/
theorem norm_idealChangeFactor (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    Algebra.norm ℚ (f.idealChangeFactor D γ) = ((γ • f).a : ℚ) / (f.a : ℚ) := by
  rw [QuadraticAlgebra.algebraNorm_eq_norm]
  have hfa : f.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)
  have hga : (γ • f).a ≠ 0 := a_ne_zero_of_not_isSquare_discrim
    ((discrim_smul γ f).trans hf ▸ Fact.out)
  have hnorm : QuadraticAlgebra.norm
      (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 1 0 • f.idealGenerator D) =
        (f.a : ℚ) * ((γ • f).a : ℚ) := by
    rw [norm_idealGenerators f D hf]
    simp only [eval_def, smul_a, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_neg]
    ring
  have h := congrArg QuadraticAlgebra.norm (idealChangeFactor_mul_first f D hf γ)
  rw [map_mul, hnorm, norm_intCast] at h
  apply (eq_div_iff (show (f.a : ℚ) ≠ 0 by exact_mod_cast hfa)).mpr
  apply mul_right_cancel₀ (show ((γ • f).a : ℚ) ≠ 0 by exact_mod_cast hga)
  simpa [mul_assoc, pow_two] using h

/-- The factor for a proper change of variables is nonzero. -/
theorem idealChangeFactor_ne_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ ≠ 0 := by
  intro hz
  have ha : (γ • f).a ≠ 0 := a_ne_zero_of_not_isSquare_discrim
    ((discrim_smul γ f).trans hf ▸ Fact.out)
  have h := idealChangeFactor_mul_first f D hf γ
  rw [hz, zero_mul] at h
  exact ha (by exact_mod_cast h.symm)

/-- Properly equivalent forms have fractional ideals differing by the explicit principal factor. -/
theorem fractionalIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    (γ • f).fractionalIdeal D ((discrim_smul γ f).trans hf) =
      FractionalIdeal.spanSingleton _ (f.idealChangeFactor D γ) * f.fractionalIdeal D hf := by
  have h₀ := idealChangeFactor_mul_first f D hf γ
  have h₁ := idealChangeFactor_mul_second f D hf γ
  simp only [zsmul_eq_mul] at h₀ h₁
  apply le_antisymm
  · intro z hz
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff _ _ _ _).mp hz
    apply FractionalIdeal.mem_singleton_mul.mpr
    refine ⟨(m * γ 1 1 + n * γ 0 1) • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) +
      (m * γ 1 0 + n * γ 0 0) • f.idealGenerator D, ?_, ?_⟩
    · exact (mem_fractionalIdeal_iff f D hf _).mpr ⟨_, _, rfl⟩
    · simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul]
      linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * h₀ -
        (n : QuadraticAlgebra ℚ (D : ℚ) 0) * h₁
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff f D hf y).mp hy
    have hdet : (γ 0 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      exact_mod_cast (show γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 by
        simpa only [Matrix.det_fin_two] using γ.det_coe)
    apply (mem_fractionalIdeal_iff _ _ _ _).mpr
    refine ⟨γ 0 0 * m - γ 0 1 * n, -(γ 1 0 * m) + γ 1 1 * n, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg]
    linear_combination -((γ 0 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * m - γ 0 1 * n) * h₀ -
      (-(γ 1 0 * m) + γ 1 1 * n : QuadraticAlgebra ℚ (D : ℚ) 0) * h₁ +
      f.idealChangeFactor D γ * ((m : QuadraticAlgebra ℚ (D : ℚ) 0) * f.a +
        (n : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D) * hdet

/-- The native invertible form ideals differ by the explicit proper-change principal factor. -/
theorem invertibleFractionalIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ)
    [Fact (¬ IsSquare D)] (hf : f.discrim = D) (hprim : f.IsPrimitive)
    (γ : SL(2, ℤ)) :
    (γ • f).invertibleFractionalIdeal D ((discrim_smul γ f).trans hf)
      ((isPrimitive_smul_iff f γ).mpr hprim) =
      toPrincipalIdeal _ _
        (Units.mk0 (f.idealChangeFactor D γ) (idealChangeFactor_ne_zero f D hf γ)) *
          f.invertibleFractionalIdeal D hf hprim := by
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, coe_invertibleFractionalIdeal,
    coe_invertibleFractionalIdeal]
  exact fractionalIdeal_smul f D hf γ

end TauCeti.BinaryQuadraticForm
