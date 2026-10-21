/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Continuity
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss convergence of principal-minor series

A common null row majorant upgrades coefficientwise convergence of principal-minor series to
convergence in every positive-radius Gauss norm. In particular, uniform entrywise convergence of
matrices with a common null row majorant implies Gauss convergence of their determinants.
This is the continuity needed to pass finite determinant identities to infinite determinants.
Coefficientwise convergence alone, without uniform control of the tails, does not suffice.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

namespace TauCeti

open Filter Finset Topology

variable {ι R α : Type*} [DecidableEq ι]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  {l : Filter α} {A : α → Matrix ι ι R} {B : Matrix ι ι R} {r : ι → ℝ}

/-- A common null row majorant upgrades convergence of each principal-minor coefficient to
Gauss convergence at every positive radius. No completeness is needed once coefficient
convergence is supplied. -/
theorem tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_common_majorant
    (hA : ∀ a i j, ‖A a i j‖ ≤ r i) (hB : ∀ i j, ‖B i j‖ ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0))
    (hcoeff : ∀ n, Tendsto (fun a ↦ (A a).charCoeff n) l (𝓝 (B.charCoeff n)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun a ↦ ((A a).charPowerSeries - B.charPowerSeries).gaussNorm norm ρ)
      l (𝓝 0) := by
  obtain ⟨T, C, hC, hT, hrC, hlim⟩ :=
    exists_geometric_bound_of_tendsto_cofinite hr hρ.le
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  let b := fun n : ℕ ↦ C ^ T.card * (1 / 2 : ℝ) ^ (n - T.card)
  have hbA (a : α) (n : ℕ) : ‖(A a).charCoeff n‖ * ρ ^ n ≤ b n :=
    Matrix.norm_charCoeff_mul_pow_le (hA a) hρ (by norm_num) (by norm_num) hC T hT hrC n
  have hbB (n : ℕ) : ‖B.charCoeff n‖ * ρ ^ n ≤ b n :=
    Matrix.norm_charCoeff_mul_pow_le hB hρ (by norm_num) (by norm_num) hC T hT hrC n
  refine PowerSeries.tendsto_gaussNorm_zero_of_coeff_bound (b := fun n ↦ 2 * b n)
    (fun n ↦ ?_) (fun a n ↦ ?_) (by simpa [b] using hlim.const_mul 2)
  · simpa only [map_sub, Matrix.coeff_charPowerSeries, sub_self] using
      (hcoeff n).sub_const (B.charCoeff n)
  · simp only [map_sub, Matrix.coeff_charPowerSeries]
    calc ‖(A a).charCoeff n - B.charCoeff n‖ * ρ ^ n
        ≤ (‖(A a).charCoeff n‖ + ‖B.charCoeff n‖) * ρ ^ n :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hρ.le _)
      _ ≤ 2 * b n := by nlinarith [hbA a n, hbB n]

/-- Uniform entrywise convergence, with a common null row majorant, implies convergence of
principal-minor series in every positive-radius Gauss norm. Completeness ensures that the
principal-minor families defining the coefficients are summable. -/
theorem tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_tendstoUniformly [CompleteSpace R]
    (hA : ∀ a i j, ‖A a i j‖ ≤ r i) (hB : ∀ i j, ‖B i j‖ ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0))
    (hAB : TendstoUniformly (fun a (p : ι × ι) ↦ A a p.1 p.2)
      (fun p ↦ B p.1 p.2) l) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun a ↦ ((A a).charPowerSeries - B.charPowerSeries).gaussNorm norm ρ)
      l (𝓝 0) := by
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  exact tendsto_gaussNorm_charPowerSeries_sub_charPowerSeries_of_common_majorant hA hB hr
    (fun n ↦ tendsto_charCoeff_of_tendstoUniformly n
      (fun i j ↦ (hB i j).trans (hM ⟨i, rfl⟩))
      (Eventually.of_forall fun a ↦ Matrix.summable_principalMinor (hA a) hr n)
      (Matrix.summable_principalMinor hB hr n) hAB) hρ

end TauCeti
