/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Sqrt
public import TauCeti.Analysis.Calculus.Taylor.UpperSupport
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Smooth upper supports from approximate energy expansions

The square-root expansion normalizes the first jet and subtracts a positive rank-one term
from the Hessian. A common cubic bound then yields an exactly touching smooth support.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorems 3.27–3.29:
  these analytic estimates supply the distance support barriers used in localization.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter Topology
open scoped BigOperators ContDiff

namespace TauCeti

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Uniform approximate energy expansions give a touching smooth upper support with normalized
first derivative and a controlled Hessian trace. The central energies converge to the
contact value. -/
theorem exists_smooth_upper_support_of_energy_expansions
    (e : OrthonormalBasis ι ℝ E) (f : E → ℝ) (energy : ℕ → E → ℝ) (c : ℕ → ℝ)
    (L : ℕ → E →L[ℝ] ℝ) (Q : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (d R K B ρ0 C0 : ℝ)
    (hd : 0 < d) (hdR : d ≤ R) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hρ0 : 0 < ρ0) (hC0 : 0 ≤ C0) (hf0 : f 0 = d)
    (hc : ∀ j, d ≤ c j ∧ c j ≤ R) (hclim : Tendsto c atTop (𝓝 d))
    (henergy0 : ∀ j, energy j 0 = c j ^ 2)
    (hL : ∀ j, ‖L j‖ ≤ 2 * c j) (hQ : ∀ j, ‖Q j‖ ≤ B)
    (htrace : ∀ j, ∑ i, Q j (e i) (e i) ≤
      2 * (Fintype.card ι : ℝ) + 2 * (Fintype.card ι : ℝ) * K * c j ^ 2)
    (herror : ∀ j z, ‖z‖ < ρ0 →
      |energy j z - energy j 0 - L j z - Q j z z / 2| ≤ C0 * ‖z‖ ^ 3)
    (hmajor : ∀ j z, ‖z‖ < ρ0 → f z ≤ Real.sqrt (energy j z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : E → ℝ) (r : ℝ), 0 < r ∧ r ≤ ρ0 ∧ ContDiff ℝ ∞ P ∧
      P 0 = d ∧ (∀ z, ‖z‖ < r → f z ≤ P z) ∧
      ‖fderiv ℝ P 0‖ ≤ 1 ∧
      (∑ i, fderiv ℝ (fderiv ℝ P) 0 (e i) (e i)) ≤
        (Fintype.card ι : ℝ) / d + (Fintype.card ι : ℝ) * K * d + ε := by
  classical
  have hR : 0 < R := hd.trans_le hdR
  have hcpos (j : ℕ) : 0 < c j := hd.trans_le (hc j).1
  have hLbound (j : ℕ) : ‖L j‖ ≤ 2 * R :=
    (hL j).trans (mul_le_mul_of_nonneg_left (hc j).2 (by norm_num))
  let T : ℕ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun j ↦ (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (L j) (L j)
  have hTapply (j : ℕ) (v w : E) : T j v w = L j v * L j w := rfl
  have hTnorm (j : ℕ) : ‖T j‖ ≤ (2 * R) ^ 2 := by
    apply (T j).opNorm_le_bound₂ (sq_nonneg _)
    intro v w
    rw [hTapply, norm_mul]
    calc
      ‖L j v‖ * ‖L j w‖ ≤ ((2 * R) * ‖v‖) * ((2 * R) * ‖w‖) := by
        apply mul_le_mul
        · exact ((L j).le_opNorm v).trans
            (mul_le_mul_of_nonneg_right (hLbound j) (norm_nonneg v))
        · exact ((L j).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (hLbound j) (norm_nonneg w))
        · exact norm_nonneg _
        · positivity
      _ = (2 * R) ^ 2 * ‖v‖ * ‖w‖ := by ring
  let A : ℕ → E →L[ℝ] ℝ := fun j ↦ (2 * c j)⁻¹ • L j
  let H : ℕ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun j ↦ (2 * c j)⁻¹ • Q j - (4 * c j ^ 3)⁻¹ • T j
  have hAapply (j : ℕ) (v : E) : A j v = L j v / (2 * c j) := by
    simp only [A, smul_apply, smul_eq_mul]
    ring
  have hHapply (j : ℕ) (v w : E) : H j v w =
      Q j v w / (2 * c j) - (L j v * L j w) / (4 * c j ^ 3) := by
    simp only [H, sub_apply, smul_apply,
      smul_eq_mul, hTapply]
    ring
  have hAnorm (j : ℕ) : ‖A j‖ ≤ 1 := by
    have hden : 0 < 2 * c j := mul_pos (by norm_num) (hcpos j)
    rw [show A j = (2 * c j)⁻¹ • L j from rfl, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hden]
    calc
      (2 * c j)⁻¹ * ‖L j‖ ≤ (2 * c j)⁻¹ * (2 * c j) :=
        mul_le_mul_of_nonneg_left (hL j) (inv_nonneg.mpr hden.le)
      _ = 1 := inv_mul_cancel₀ hden.ne'
  have hHnorm (j : ℕ) : ‖H j‖ ≤ B / (2 * d) + (2 * R) ^ 2 / (4 * d ^ 3) := by
    have hden : 0 < 2 * c j := mul_pos (by norm_num) (hcpos j)
    have hcube : 0 < 4 * c j ^ 3 := by have := hcpos j; positivity
    apply (H j).opNorm_le_bound₂ (by positivity)
    intro v w
    have hQeval : |Q j v w| ≤ B * ‖v‖ * ‖w‖ := by
      simpa only [Real.norm_eq_abs] using ((Q j).le_opNorm₂ v w).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hQ j) (norm_nonneg v)) (norm_nonneg w))
    have hTeval : |L j v * L j w| ≤ (2 * R) ^ 2 * ‖v‖ * ‖w‖ := by
      simpa only [hTapply, Real.norm_eq_abs] using ((T j).le_opNorm₂ v w).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hTnorm j) (norm_nonneg v)) (norm_nonneg w))
    calc
      ‖H j v w‖ ≤ |Q j v w| / (2 * c j) +
          |L j v * L j w| / (4 * c j ^ 3) := by
        rw [Real.norm_eq_abs, hHapply]
        have habs := abs_sub_le (Q j v w / (2 * c j)) 0
          (L j v * L j w / (4 * c j ^ 3))
        simpa only [sub_zero, zero_sub, abs_neg, abs_div,
          abs_of_pos hden, abs_of_pos hcube] using habs
      _ ≤ (B * ‖v‖ * ‖w‖) / (2 * d) +
          ((2 * R) ^ 2 * ‖v‖ * ‖w‖) / (4 * d ^ 3) := by
        apply add_le_add
        · exact div_le_div₀ (by positivity) hQeval (by positivity)
            (mul_le_mul_of_nonneg_left (hc j).1 (by norm_num))
        · exact div_le_div₀ (by positivity) hTeval (by positivity)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le (hc j).1 3)
              (by norm_num))
      _ = (B / (2 * d) + (2 * R) ^ 2 / (4 * d ^ 3)) * ‖v‖ * ‖w‖ := by ring
  have hHtrace (j : ℕ) : ∑ i, H j (e i) (e i) ≤
      (Fintype.card ι : ℝ) / c j + (Fintype.card ι : ℝ) * K * c j := by
    have hden : 0 < 2 * c j := mul_pos (by norm_num) (hcpos j)
    have hcube : 0 ≤ 4 * c j ^ 3 := by have := hcpos j; positivity
    calc
      (∑ i, H j (e i) (e i)) ≤ ∑ i, Q j (e i) (e i) / (2 * c j) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hHapply]
        exact sub_le_self _ (div_nonneg (mul_self_nonneg _) hcube)
      _ = (∑ i, Q j (e i) (e i)) / (2 * c j) := by rw [Finset.sum_div]
      _ ≤ (2 * (Fintype.card ι : ℝ) + 2 * (Fintype.card ι : ℝ) * K * c j ^ 2) / (2 * c j) :=
        div_le_div_of_nonneg_right (htrace j) hden.le
      _ = (Fintype.card ι : ℝ) / c j + (Fintype.card ι : ℝ) * K * c j := by
        field_simp [(hcpos j).ne']
  obtain ⟨ρ, C, hρ, _hρ1, hρρ0, hC, hsqrt⟩ :=
    exists_sqrt_energy_cubic_majorant_on_ball (V := E) d (2 * R) B C0 ρ0
      hd (by positivity) hB hC0 hρ0
  have hsupport (j : ℕ) (z : E) (hz : ‖z‖ < ρ) :
      f z ≤ c j + A j z + (1 / 2 : ℝ) * H j z z + C * ‖z‖ ^ 3 := by
    have happrox := (hsqrt (c j) (energy j) (L j) (Q j) (hc j).1
      (hLbound j) (hQ j) (fun z hz ↦ by
        simpa only [henergy0 j] using herror j z hz) z hz).2
    have hpoly : c j + A j z + (1 / 2 : ℝ) * H j z z + C * ‖z‖ ^ 3 =
        c j + L j z / (2 * c j) + Q j z z / (4 * c j) -
          (L j z) ^ 2 / (8 * c j ^ 3) + C * ‖z‖ ^ 3 := by
      rw [hAapply, hHapply]
      field_simp [(hcpos j).ne']
      ring
    rw [hpoly]
    exact (hmajor j z (hz.trans_le hρρ0)).trans happrox
  have htraceLim : Tendsto (fun j ↦ (Fintype.card ι : ℝ) / c j + (Fintype.card ι : ℝ) * K * c j)
      atTop (𝓝 ((Fintype.card ι : ℝ) / d + (Fintype.card ι : ℝ) * K * d)) :=
    (tendsto_const_nhds.div hclim hd.ne').add (tendsto_const_nhds.mul hclim)
  have hconstantLim : Tendsto c atTop (𝓝 (f 0)) := by simpa only [hf0] using hclim
  obtain ⟨P, r, hr, hrρ, hP, hP0, hPmajor, hPgrad, hPlap⟩ :=
    exists_smooth_upper_support_of_bounded_jets e f c
      (fun j ↦ (Fintype.card ι : ℝ) / c j + (Fintype.card ι : ℝ) * K * c j) A H 1 ρ C
      (B / (2 * d) + (2 * R) ^ 2 / (4 * d ^ 3))
      ((Fintype.card ι : ℝ) / d + (Fintype.card ι : ℝ) * K * d)
      hρ hC hconstantLim htraceLim hAnorm hHnorm hHtrace hsupport ε hε
  exact ⟨P, r, hr, hrρ.trans hρρ0, hP, hP0.trans hf0, hPmajor, hPgrad, hPlap⟩

end TauCeti
