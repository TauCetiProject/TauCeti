/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import TauCeti.RingTheory.Polynomial.Subresultant.FirstNonzero

/-!
# Analytic coefficients of monic polynomial gcds

The monic gcd of two polynomial families has analytic coefficients wherever both input degrees
and the gcd degree are locally constant. This permits gcd and squarefree calculations in
analytic coefficient families on coordinate neighborhoods. In submanifold charts the parameters
may have lower dimension than the original coefficient domain.

At a strict gcd index, the first nonzero subresultant gives the gcd after division by its
nonvanishing principal coefficient. At a terminal index, the gcd is the monic normalization of
the smaller input. Thus the result includes constant polynomials and divisibility cases, and
requires neither monicity nor squarefreeness of the inputs. Finite input degrees exclude zero
polynomials. Only coefficients up to the respective degree bounds need be analytic.

The argument uses the same subresultant formulas as
`TauCeti.continuousAt_coeff_normalize_gcd`, upgrading coefficient continuity to analyticity.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 4 (subresultant gcd recovery).
-/

public section

open Polynomial Filter Topology

namespace TauCeti

variable {𝕜 E R : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Subresultant

variable [NormedCommRing R] [NormedAlgebra 𝕜 R]
  {F G : E → R[X]} {x₀ : E} {m n : ℕ}

/-- A fixed-bound subresultant coefficient minor depends analytically on the input coefficients.
Only coefficients up to the respective formal bounds need be analytic. -/
@[fun_prop]
theorem analyticAt_subresultantCoeff
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    AnalyticAt 𝕜 (fun x => subresultantCoeff (F x) (G x) m n j k) x₀ := by
  simp only [subresultantCoeff_def]
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro l _
  generalize σ l = i
  induction l using Fin.addCases with
  | left l =>
      simp only [subresultantCoeffMatrix_castAdd]
      split_ifs <;> first | exact hG _ (by omega) | exact analyticAt_const
  | right l =>
      simp only [subresultantCoeffMatrix_natAdd]
      split_ifs <;> first | exact hF _ (by omega) | exact analyticAt_const

/-- Every coefficient of a fixed-bound subresultant polynomial is analytic in the input
coefficients, including outside the strict-index range where the polynomial is zero. -/
@[fun_prop]
theorem analyticAt_coeff_subresultant
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x => (G x).coeff i) x₀) (j k : ℕ) :
    AnalyticAt 𝕜 (fun x => (subresultant (F x) (G x) m n j).coeff k) x₀ := by
  simp only [coeff_subresultant]
  split_ifs
  · exact analyticAt_subresultantCoeff hF hG j k
  · exact analyticAt_const

end Subresultant

section Field

variable [NormedField R] [NormedAlgebra 𝕜 R] [DecidableEq R]
  {F G : E → R[X]} {x₀ : E} {m n j : ℕ}

/-- Monic normalization has analytic coefficients on a family of fixed finite degree. -/
@[fun_prop]
theorem analyticAt_coeff_normalize
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = m) (k : ℕ) :
    AnalyticAt 𝕜 (fun x => (normalize (F x)).coeff k) x₀ := by
  have hcoeff : AnalyticAt 𝕜 (fun x => (F x).coeff k) x₀ := by
    by_cases hk : k ≤ m
    · exact hF k hk
    · have hzero : AnalyticAt 𝕜 (fun _ : E => (0 : R)) x₀ := analyticAt_const
      apply hzero.congr
      filter_upwards [hdeg] with x hx
      exact (coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_eq_of_degree_eq_some hx]
        omega)).symm
  apply (((hF m le_rfl).inv (coeff_ne_zero_of_eq_degree hdeg.self_of_nhds)).mul hcoeff).congr
  filter_upwards [hdeg] with x hx
  have hp : F x ≠ 0 := by
    intro h
    simp [h] at hx
  simp only [Pi.mul_apply, Pi.inv_apply, normalize_apply, coe_normUnit_of_ne_zero hp,
    coeff_mul_C]
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some hx, mul_comm]

/-- The monic gcd has analytic coefficients when both input degrees and the gcd degree are
locally constant. The gcd may have the full degree of either input; neither input need be monic
or squarefree. Finite input degrees exclude zero polynomials. -/
@[fun_prop]
theorem analyticAt_coeff_normalize_gcd
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x => (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x => (G x).coeff i) x₀)
    (hdegF : ∀ᶠ x in 𝓝 x₀, (F x).degree = m)
    (hdegG : ∀ᶠ x in 𝓝 x₀, (G x).degree = n)
    (hgcd : ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F x) (G x)).natDegree = j) (k : ℕ) :
    AnalyticAt 𝕜 (fun x => (normalize (EuclideanDomain.gcd (F x) (G x))).coeff k) x₀ := by
  have hf₀ : F x₀ ≠ 0 := by
    intro h
    simpa [h] using hdegF.self_of_nhds
  have hg₀ : G x₀ ≠ 0 := by
    intro h
    simpa [h] using hdegG.self_of_nhds
  have hmn : j ≤ min m n := by
    have h₁ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left (F x₀) (G x₀)) hf₀
    have h₂ := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (F x₀) (G x₀)) hg₀
    rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegF.self_of_nhds] at h₁
    rw [hgcd.self_of_nhds, natDegree_eq_of_degree_eq_some hdegG.self_of_nhds] at h₂
    exact le_min h₁ h₂
  -- At a strict index the nonzero principal coefficient normalizes the subresultant.
  by_cases hj : j < min m n
  · have hc : psc (F x₀) (G x₀) m n j ≠ 0 := by
      rw [← hgcd.self_of_nhds]
      exact psc_natDegree_gcd_ne_zero hf₀
        (natDegree_eq_of_degree_eq_some hdegF.self_of_nhds)
        (natDegree_eq_of_degree_eq_some hdegG.self_of_nhds).le
    have han : AnalyticAt 𝕜 (fun x => psc (F x) (G x) m n j) x₀ := by
      simpa only [subresultantCoeff_self] using analyticAt_subresultantCoeff hF hG j j
    apply ((han.inv hc).mul (analyticAt_coeff_subresultant hF hG j k)).congr
    filter_upwards [hdegF, hdegG, hgcd] with x hf hg hx
    have hm := natDegree_eq_of_degree_eq_some hf
    have hn := natDegree_eq_of_degree_eq_some hg
    have hs := subresultant_natDegree_gcd hm.le hn.le (by rwa [hx])
    rw [hx] at hs
    have hc' : psc (F x) (G x) m n j ≠ 0 := by
      rw [← hx]
      apply psc_natDegree_gcd_ne_zero _ hm hn.le
      intro h
      simp [h] at hf
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [hs, coeff_C_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  -- At the terminal index the gcd is associated to an input of that degree.
  · have heq : j = m ∨ j = n := by omega
    rcases heq with rfl | rfl
    · apply (analyticAt_coeff_normalize hF hdegF k).congr
      filter_upwards [hdegF, hgcd] with x hf hx
      have ha := associated_of_dvd_of_natDegree_le
        (EuclideanDomain.gcd_dvd_left (F x) (G x))
        (degree_ne_bot.mp (by rw [hf]; exact WithBot.coe_ne_bot))
        (by rw [natDegree_eq_of_degree_eq_some hf, hx])
      rw [normalize_eq_normalize_iff_associated.mpr ha]
    · apply (analyticAt_coeff_normalize hG hdegG k).congr
      filter_upwards [hdegG, hgcd] with x hg hx
      have ha := associated_of_dvd_of_natDegree_le
        (EuclideanDomain.gcd_dvd_right (F x) (G x))
        (degree_ne_bot.mp (by rw [hg]; exact WithBot.coe_ne_bot))
        (by rw [natDegree_eq_of_degree_eq_some hg, hx])
      rw [normalize_eq_normalize_iff_associated.mpr ha]

end Field

end TauCeti
