/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Polynomial.Basic
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.RingTheory.Polynomial.GaussNorm
import TauCeti.Analysis.Polynomial.SupNorm.Factor
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Coefficient heights under factorization

The product of the relative coefficient heights of nonzero polynomials over a number
field is bounded by the coefficient height of their product, times a power of two.
The exponent is the field degree times the degree of the product. The logarithmic
form bounds the sum of factor heights and is useful for controlling roots with multiplicity.

The local height formula uses Gauss norms. At finite places they are multiplicative;
at infinite places the complex Gelfond bound supplies the power of two. The height
normalization is relative: divide logarithmic heights by the field degree to obtain
the corresponding absolute estimate.

## References

* Lukas Pottmeyer, *Diophantine Approximation* (17 January 2022), §3.2,
  Lemma 3.2.10 and Proposition 3.2.12.
-/

public section

namespace Polynomial

open NumberField Function

variable {K : Type*} [Field K] [NumberField K]

/-- The relative coefficient height is the product of local Gauss norms, with the
real or complex multiplicity at infinite places. -/
theorem mulHeight_eq_of_numberField {p : K[X]} (hp : p ≠ 0) :
    p.mulHeight =
      (∏ v : InfinitePlace K, p.gaussNorm v.val 1 ^ v.mult) *
        ∏ᶠ v : FinitePlace K, p.gaussNorm v.val 1 := by
  have hx : (fun i ↦ p.coeff i) ≠ 0 := by
    intro h
    apply hp
    ext i
    simpa using congrFun h i
  have hcoeff : ⇑p.toFinsupp.coeff = fun i ↦ p.coeff i := by
    ext i
    exact p.toFinsupp_apply i
  rw [mulHeight_eq_finsupp, Finsupp.mulHeight_eq_mulHeight_coe, hcoeff,
    NumberField.mulHeight_eq hx]
  simp only [gaussNorm_eq_iSup _ _ (by positivity : (0 : ℝ) ≤ 1), one_pow, mul_one,
    InfinitePlace.coe_apply, FinitePlace.coe_apply]

/-- A nonzero polynomial has local coefficient norm one at all but finitely many
finite places. -/
theorem hasFiniteMulSupport_gaussNorm {p : K[X]} (hp : p ≠ 0) :
    (fun v : FinitePlace K ↦ p.gaussNorm v.val 1).HasFiniteMulSupport := by
  classical
  have hs := support_nonempty.mpr hp
  simp only [gaussNorm, hs, ↓reduceDIte, one_pow, mul_one]
  exact HasFiniteMulSupport.sup' p.support
    (fun i hi ↦ FinitePlace.hasFiniteMulSupport (mem_support_iff.mp hi)) hs

/-- The Gelfond bound for relative coefficient heights of a finite family of nonzero
polynomials. The exponent depends on the degree of their product, not their number. -/
theorem prod_mulHeight_le_two_pow_mul_mulHeight_prod {ι : Type*} (s : Finset ι)
    (f : ι → K[X]) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∏ i ∈ s, (f i).mulHeight ≤
      2 ^ (Module.finrank ℚ K * (∏ i ∈ s, f i).natDegree) *
        (∏ i ∈ s, f i).mulHeight := by
  classical
  have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  have hi (v : InfinitePlace K) (p : K[X]) :
      p.gaussNorm v.val 1 = (p.map v.embedding).supNorm := by
    simp only [gaussNorm_eq_iSup _ _ (by positivity : (0 : ℝ) ≤ 1), one_pow, mul_one,
      supNorm_eq_iSup, coeff_map, InfinitePlace.norm_embedding_eq, InfinitePlace.coe_apply]
  have harch (v : InfinitePlace K) :
      ∏ i ∈ s, (f i).gaussNorm v.val 1 ≤
        2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).gaussNorm v.val 1 := by
    simpa only [hi, ← Polynomial.map_prod, natDegree_map] using
      prod_supNorm_le_two_pow_mul_supNorm_prod s (fun i ↦ (f i).map v.embedding)
  have hfinite (v : FinitePlace K) :
      (∏ i ∈ s, f i).gaussNorm v.val 1 = ∏ i ∈ s, (f i).gaussNorm v.val 1 := by
    let := gaussNorm_isAbsoluteValue (v := v.val) v.add_le (by norm_num : (0 : ℝ) < 1)
    exact map_prod (IsAbsoluteValue.toAbsoluteValue (gaussNorm v.val 1)) f s
  rw [mulHeight_eq_of_numberField hprod]
  simp_rw [Finset.prod_congr rfl (fun i hi ↦ mulHeight_eq_of_numberField (hf i hi))]
  rw [Finset.prod_mul_distrib, prod_finprod_comm s _ (fun i hi ↦
    hasFiniteMulSupport_gaussNorm (hf i hi))]
  simp_rw [← hfinite]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _
    (finprod_nonneg (fun v ↦ gaussNorm_nonneg _ _ (by positivity)))
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow]
  calc
    ∏ v : InfinitePlace K, (∏ i ∈ s, (f i).gaussNorm v.val 1) ^ v.mult ≤
        ∏ v : InfinitePlace K,
          (2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).gaussNorm v.val 1) ^ v.mult := by
      apply Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg
        (Finset.prod_nonneg (fun i _ ↦ gaussNorm_nonneg _ _ (by positivity))) _)
      intro v _
      exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ ↦
        gaussNorm_nonneg _ _ (by positivity))) (harch v) v.mult
    _ = 2 ^ (Module.finrank ℚ K * (∏ i ∈ s, f i).natDegree) *
        ∏ v : InfinitePlace K, (∏ i ∈ s, f i).gaussNorm v.val 1 ^ v.mult := by
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        ← Finset.mul_sum, InfinitePlace.sum_mult_eq, Nat.mul_comm]

/-- The logarithmic Gelfond bound for a finite family of nonzero polynomials over a
number field, with relative coefficient heights. -/
theorem sum_logHeight_le_logHeight_prod_add {ι : Type*} (s : Finset ι)
    (f : ι → K[X]) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∑ i ∈ s, (f i).logHeight ≤ (∏ i ∈ s, f i).logHeight +
      Module.finrank ℚ K * (∏ i ∈ s, f i).natDegree * Real.log 2 := by
  have h := Real.log_le_log (Finset.prod_pos (fun i _ ↦ mulHeight_pos (f i)))
    (prod_mulHeight_le_two_pow_mul_mulHeight_prod s f hf)
  rw [Real.log_prod (fun i _ ↦ (mulHeight_pos (f i)).ne'),
    Real.log_mul (by positivity) (mulHeight_pos _).ne', Real.log_pow] at h
  simpa only [← logHeight_eq_log_mulHeight, Nat.cast_mul, add_comm] using h

/-- The product of the heights of two nonzero polynomial factors is controlled by
the height of their product and its degree. -/
theorem mulHeight_mulHeight_le_two_pow_mul_mulHeight (f g : K[X])
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mulHeight * g.mulHeight ≤
      2 ^ (Module.finrank ℚ K * (f * g).natDegree) * (f * g).mulHeight := by
  simpa [Fin.prod_univ_two] using
    prod_mulHeight_le_two_pow_mul_mulHeight_prod Finset.univ ![f, g]
      (by simp [Fin.forall_fin_two, hf, hg])

/-- The sum of the relative logarithmic heights of two nonzero polynomial factors
is at most the height of their product plus the field degree times its degree times `log 2`. -/
theorem logHeight_add_logHeight_le_logHeight_mul_add (f g : K[X])
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f.logHeight + g.logHeight ≤ (f * g).logHeight +
      Module.finrank ℚ K * (f * g).natDegree * Real.log 2 := by
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using
    sum_logHeight_le_logHeight_prod_add Finset.univ ![f, g]
      (by simp [Fin.forall_fin_two, hf, hg])

end Polynomial
