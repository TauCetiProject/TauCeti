/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Weierstrass.Legendre
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Weierstrass.Sigma

/-!
# Reduced sigma functions of complex lattices

The reduced sigma function is the Weierstrass product multiplied by `exp (-s₂ z² / 2)`,
where `s₂` removes the complex-linear part of the quasi-period map. Its transformation law
involves only the Hermitian form `π conj(l) z / area(ℂ/Λ)` and the sign that is positive
exactly on `2Λ`. It is entire, odd, has derivative one at zero, and has simple zeros exactly
on the lattice. Both the correction and the function depend only on the lattice.

This normalization permits translating sigma by a half-period to construct even theta
functions with a Hermitian transformation law.

## References

* A. Weil, *Elliptic Functions according to Eisenstein and Kronecker* (1976).
* J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, I.5.

-/

public section

noncomputable section

open Complex
open scoped ComplexConjugate

namespace PeriodPair

variable (L : PeriodPair)

/-- The complex-linear correction to the quasi-period map of a lattice. Subtracting `s₂ l`
from `η(l)` leaves `π conj(l) / area(ℂ/Λ)`. -/
def sigmaCorrection : ℂ :=
  (L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ -
    (Real.pi / ZLattice.covolume L.lattice : ℝ) * conj L.ω₁) / L.ω₁

/-- The formula for the complex-linear sigma correction in a pair of periods. -/
theorem sigmaCorrection_def :
    L.sigmaCorrection = (L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ -
      (Real.pi / ZLattice.covolume L.lattice : ℝ) * conj L.ω₁) / L.ω₁ := (rfl)

/-- The corrected quasi-period map is conjugate-linear, with coefficient `π / area(ℂ/Λ)`. -/
theorem quasiPeriod_sub_sigmaCorrection_mul (l : L.lattice) :
    L.quasiPeriod l - L.sigmaCorrection * l =
      (Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) := by
  have h₁ : L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ - L.sigmaCorrection * L.ω₁ =
      (Real.pi / ZLattice.covolume L.lattice : ℝ) * conj L.ω₁ := by
    rw [sigmaCorrection_def, div_mul_cancel₀ _ L.ω₁_ne_zero]
    ring
  have h₂ : L.quasiPeriod ⟨_, L.ω₂_mem_lattice⟩ - L.sigmaCorrection * L.ω₂ =
      (Real.pi / ZLattice.covolume L.lattice : ℝ) * conj L.ω₂ := by
    apply mul_right_cancel₀ L.ω₁_ne_zero
    linear_combination L.ω₂ * h₁ - L.quasiPeriod_legendre_covolume
  obtain ⟨m, n, h⟩ := mem_lattice.mp l.property
  rw [L.quasiPeriod_eq_intCast_mul_add l h, ← h, map_add, map_mul, map_mul]
  simp only [map_intCast]
  linear_combination (m : ℂ) * h₁ + (n : ℂ) * h₂

/-- The sigma correction is independent of the generators of the lattice. -/
theorem sigmaCorrection_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.sigmaCorrection = L'.sigmaCorrection := by
  have h₁ := L.quasiPeriod_sub_sigmaCorrection_mul ⟨_, L.ω₁_mem_lattice⟩
  have h₂ := L'.quasiPeriod_sub_sigmaCorrection_mul ⟨_, h ▸ L.ω₁_mem_lattice⟩
  have hη := L.quasiPeriod_eq_of_lattice_eq h ⟨_, L.ω₁_mem_lattice⟩
  rw [← hη] at h₂
  simp only at h₁ h₂
  rw [← h] at h₂
  exact mul_right_cancel₀ L.ω₁_ne_zero (by linear_combination h₂ - h₁)

/-- The reduced sigma function of a complex lattice: the Weierstrass product with its
quadratic exponential correction. -/
def reducedSigma (z : ℂ) : ℂ :=
  exp (-(L.sigmaCorrection * z ^ 2 / 2)) * L.weierstrassSigma z

/-- The relation between reduced sigma and the Weierstrass product. -/
theorem reducedSigma_def (z : ℂ) :
    L.reducedSigma z = exp (-(L.sigmaCorrection * z ^ 2 / 2)) * L.weierstrassSigma z := (rfl)

/-- The reduced sigma function is entire. -/
theorem differentiable_reducedSigma : Differentiable ℂ L.reducedSigma := by
  unfold reducedSigma
  exact Differentiable.mul (by fun_prop) L.differentiable_weierstrassSigma

/-- The reduced sigma function is odd. -/
@[simp]
theorem reducedSigma_neg (z : ℂ) : L.reducedSigma (-z) = -L.reducedSigma z := by
  simp [reducedSigma_def]

/-- Reduced sigma vanishes exactly on the period lattice. -/
@[simp]
theorem reducedSigma_eq_zero_iff {z : ℂ} : L.reducedSigma z = 0 ↔ z ∈ L.lattice := by
  simp [reducedSigma_def, L.weierstrassSigma_eq_zero_iff]

/-- Reduced sigma vanishes at the origin. -/
@[simp]
theorem reducedSigma_zero : L.reducedSigma 0 = 0 :=
  L.reducedSigma_eq_zero_iff.mpr (zero_mem _)

/-- Reduced sigma has derivative one at the origin. -/
theorem hasDerivAt_reducedSigma_zero : HasDerivAt L.reducedSigma 1 0 := by
  have he : DifferentiableAt ℂ (fun z : ℂ ↦ exp (-(L.sigmaCorrection * z ^ 2 / 2))) 0 := by
    fun_prop
  convert he.hasDerivAt.mul L.hasDerivAt_weierstrassSigma_zero using 1
  · exact funext fun z ↦ L.reducedSigma_def z
  · simp

@[simp]
theorem deriv_reducedSigma_zero : deriv L.reducedSigma 0 = 1 :=
  L.hasDerivAt_reducedSigma_zero.deriv

/-- The reduced sigma function depends only on the lattice. -/
theorem reducedSigma_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.reducedSigma = L'.reducedSigma := by
  ext z
  rw [reducedSigma_def, reducedSigma_def, sigmaCorrection_eq_of_lattice_eq h,
    weierstrassSigma_eq_of_lattice_eq h]

open Classical in
/-- The Hermitian transformation law of reduced sigma. The multiplier is positive exactly
at twice a lattice vector. -/
theorem reducedSigma_add_coe (z : ℂ) (l : L.lattice) :
    L.reducedSigma (z + l) =
      (if (l : ℂ) / 2 ∈ L.lattice then (1 : ℂ) else -1) *
        exp ((Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) * (z + l / 2)) *
          L.reducedSigma z := by
  classical
  have hW : L.weierstrassSigma (z + l) =
      (if (l : ℂ) / 2 ∈ L.lattice then (1 : ℂ) else -1) *
        exp (L.quasiPeriod l * (z + l / 2)) * L.weierstrassSigma z := by
    split_ifs with hl
    · simpa using L.weierstrassSigma_add_coe_of_div_two_mem z hl
    · simpa using L.weierstrassSigma_add_coe_of_div_two_notMem z hl
  have he : exp (-(L.sigmaCorrection * (z + l) ^ 2 / 2)) *
        exp (L.quasiPeriod l * (z + l / 2)) =
      exp ((Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) * (z + l / 2)) *
        exp (-(L.sigmaCorrection * z ^ 2 / 2)) := by
    rw [← exp_add, ← exp_add, ← L.quasiPeriod_sub_sigmaCorrection_mul l]
    congr 1
    ring
  rw [reducedSigma_def, hW, reducedSigma_def]
  linear_combination L.weierstrassSigma z *
    (if (l : ℂ) / 2 ∈ L.lattice then (1 : ℂ) else -1) * he

/-- Every zero of reduced sigma is simple. -/
theorem analyticOrderAt_reducedSigma_coe (l : L.lattice) :
    analyticOrderAt L.reducedSigma l = 1 := by
  have he : AnalyticAt ℂ (fun z : ℂ ↦ exp (-(L.sigmaCorrection * z ^ 2 / 2))) l := by
    fun_prop
  have hfun : L.reducedSigma =
      (fun z : ℂ ↦ exp (-(L.sigmaCorrection * z ^ 2 / 2))) * L.weierstrassSigma :=
    funext fun z ↦ L.reducedSigma_def z
  rw [hfun, analyticOrderAt_mul he (L.differentiable_weierstrassSigma.analyticAt l),
    he.analyticOrderAt_eq_zero.mpr (exp_ne_zero _), L.analyticOrderAt_weierstrassSigma_coe,
    zero_add]

end PeriodPair
