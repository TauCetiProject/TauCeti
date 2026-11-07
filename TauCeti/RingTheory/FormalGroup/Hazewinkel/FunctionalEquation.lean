/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Basic
public import TauCeti.RingTheory.FormalGroup.FunctionalEquation
import TauCeti.Algebra.Module.Rat

/-!
# Integrality of Hazewinkel's formal group

For `p > 1`, suppose `σ` is an endomorphism of a `ℚ`-algebra and `σ(vᵢ) = vᵢ^p`.
Hazewinkel's logarithm then satisfies the exact functional equation
`f(X) - ∑ᵢ (vᵢ / p) (σⁱ f)(X^(pⁱ)) = X`.
The sum is interpreted coefficientwise using `functionalEquationSum`.

For `p` prime, if the `vᵢ` belong to a subring `A` and `σ` lifts Frobenius modulo
`p A`, every coefficient of `hazewinkelFormalGroup p v` lies in `A`.
This is the integrality criterion used to construct the polynomial coefficient ring
of a p-typical formal group from its rational logarithm. No integrality of the
logarithm itself is asserted.

## References

* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*,
  J. Pure Appl. Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2.
-/

public section

open PowerSeries Finset

namespace TauCeti

variable {K : Type*} [CommRing K] [Algebra ℚ K] {p : ℕ} (v : ℕ+ → K)

/-- The twisting coefficients `sᵢ = vᵢ / p` in Hazewinkel's functional equation,
extended by zero at index zero. -/
noncomputable def hazewinkelFunctionalCoeff (p : ℕ) (v : ℕ+ → K) (i : ℕ) : K :=
  if h : 0 < i then (p : ℚ)⁻¹ • v ⟨i, h⟩ else 0

@[simp]
theorem hazewinkelFunctionalCoeff_zero : hazewinkelFunctionalCoeff p v 0 = 0 := by
  simp [hazewinkelFunctionalCoeff]

@[simp]
theorem hazewinkelFunctionalCoeff_pos (i : ℕ+) :
    hazewinkelFunctionalCoeff p v i = (p : ℚ)⁻¹ • v i := by
  rw [hazewinkelFunctionalCoeff, dite_eq_left i.pos]
  congr 2

section Equation

variable [NeZero p]

/-- In degree `pⁿ`, the twisted sum is the sum in Hazewinkel's recursion. -/
private theorem coeff_pow_functionalEquationSum_hazewinkelLog (hp : 1 < p) (σ : K →+* K)
    (hσ : ∀ j, σ (v j) = v j ^ p) (n : ℕ) :
    coeff (p ^ n) (functionalEquationSum p σ (hazewinkelFunctionalCoeff p v)
      (hazewinkelLog p v).toPowerSeries : PowerSeries K) =
      ∑ i ∈ Icc 1 n, (p : ℚ)⁻¹ •
        (v (i - 1).succPNat *
          hazewinkelLogCoeff p (fun j ↦ v j ^ p ^ i) (n - i)) := by
  rw [powerSeries_coeff_functionalEquationSum]
  have hn : n ≤ p ^ n := (Nat.lt_pow_self hp).le
  rw [← sum_subset (Icc_subset_Icc_right hn)]
  · apply sum_congr rfl
    intro i hi
    have hin : i ≤ n := (mem_Icc.mp hi).2
    have hi0 : 0 < i := (mem_Icc.mp hi).1
    rw [ite_eq_left (pow_dvd_pow p hin), Nat.pow_div hin (by omega),
      coeff_hazewinkelLog_pow v hp, pow_apply_hazewinkelLogCoeff v σ hσ,
      hazewinkelFunctionalCoeff, dite_eq_left hi0, smul_mul_assoc]
    congr 2
    exact congrArg v (PNat.eq (by simp; omega))
  · intro i hi hni
    have hni' : n < i := by simp_all
    rw [ite_eq_right (by simpa only [Nat.pow_dvd_pow_iff_le_right hp, not_le] using hni'),
      mul_zero]

/-- Hazewinkel's logarithm has functional-equation defect exactly `X` when
`σ(vᵢ) = vᵢ^p`. -/
theorem hazewinkelLog_sub_functionalEquationSum (hp : 1 < p) (σ : K →+* K)
    (hσ : ∀ j, σ (v j) = v j ^ p) :
    (hazewinkelLog p v).toPowerSeries -
      functionalEquationSum p σ (hazewinkelFunctionalCoeff p v)
        (hazewinkelLog p v).toPowerSeries = (X : PowerSeries K) := by
  ext k
  rw [map_sub]
  by_cases hk : ∃ n, p ^ n = k
  · obtain ⟨n, rfl⟩ := hk
    rw [coeff_hazewinkelLog_pow v hp,
      coeff_pow_functionalEquationSum_hazewinkelLog v hp σ hσ]
    rcases n with _ | n
    · simp
    · have hrec := natCast_mul_hazewinkelLogCoeff_succ' (p := p) v (by omega) n
      have hsum : (∑ i ∈ Icc 1 (n + 1), (p : ℚ)⁻¹ •
          (v (i - 1).succPNat *
            hazewinkelLogCoeff p (fun j ↦ v j ^ p ^ i) (n + 1 - i))) =
          (p : ℚ)⁻¹ • ((p : K) * hazewinkelLogCoeff p v (n + 1)) := by
        rw [hrec, smul_sum, ← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        apply sum_congr rfl
        intro i _
        simp [Nat.add_comm]
      rw [hsum, inv_natCast_smul_natCast_mul (by omega), sub_self, coeff_X,
        ite_eq_right (ne_of_gt (Nat.one_lt_pow (by omega) hp))]
  · push Not at hk
    rw [coeff_hazewinkelLog_eq_zero v hk, powerSeries_coeff_functionalEquationSum,
      sum_eq_zero, sub_zero, coeff_X, ite_eq_right (by simpa [eq_comm] using hk 0)]
    intro i hi
    split_ifs with hdvd
    · rw [coeff_hazewinkelLog_eq_zero v, map_zero, mul_zero]
      intro n hn
      apply hk (n + i)
      rw [pow_add, hn, Nat.div_mul_cancel hdvd]
    · rw [mul_zero]

/-- Hazewinkel's logarithm satisfies the functional equation relative to every subring,
when the endomorphism sends each generator to its `p`-th power. -/
theorem satisfiesFunctionalEquation_hazewinkelLog (hp : 1 < p) (σ : K →+* K)
    (hσ : ∀ j, σ (v j) = v j ^ p) (A : Subring K) :
    SatisfiesFunctionalEquation p σ (hazewinkelFunctionalCoeff p v) A
      (hazewinkelLog p v).toPowerSeries := by
  apply powerSeries_satisfiesFunctionalEquation_iff.mpr
  intro n
  rw [hazewinkelLog_sub_functionalEquationSum v hp σ hσ, coeff_X]
  split_ifs
  exacts [A.one_mem, A.zero_mem]

end Equation

variable [hp : Fact p.Prime]

/-- **Integrality of Hazewinkel's formal group.** If `σ` lifts Frobenius
modulo `p A`, and sends the integral generators `vᵢ` to their `p`-th powers, the formal
group with Hazewinkel's rational logarithm has all its coefficients in `A`. -/
theorem coeff_hazewinkelFormalGroup_mem (σ : K →+* K) (A : Subring K)
    (hσp : ∀ a ∈ A, ∃ b ∈ A, σ a - a ^ p = p * b)
    (hσv : ∀ j, σ (v j) = v j ^ p) (hv : ∀ j, v j ∈ A) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (hazewinkelFormalGroup p v).toPowerSeries ∈ A := by
  have hσA : Set.MapsTo σ A A := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hσp a ha
    rw [← sub_add_cancel (σ a) (a ^ p), hab]
    exact A.add_mem (A.mul_mem (natCast_mem A p) hb) (A.pow_mem ha p)
  rw [hazewinkelFormalGroup_def]
  apply coeff_inv_smul_𝔾ₐ_toPowerSeries_mem hσA hσp
    (s := hazewinkelFunctionalCoeff p v) ?_ (hazewinkelLog p v) ?_
    (satisfiesFunctionalEquation_hazewinkelLog v hp.out.one_lt σ hσv A) d
  · intro i
    rcases i with _ | i
    · simp
    · have hi : i + 1 = (i.succPNat : ℕ) := rfl
      rw [hi, hazewinkelFunctionalCoeff_pos, mul_smul_comm,
        inv_natCast_smul_natCast_mul hp.out.ne_zero]
      exact hv _
  · exact ⟨1, A.one_mem, by simp⟩

end TauCeti
