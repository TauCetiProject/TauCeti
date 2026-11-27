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
involves only the Hermitian form `π conj(l) z / area(ℂ/Λ)` and a sign that is `1` exactly
on `2Λ` and `-1` otherwise. It is entire, odd, has derivative one at zero, and has simple
zeros exactly on the lattice. Both the correction and the function depend only on the lattice.

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

/-- The reduced sigma function of a complex lattice: the Weierstrass product with its
quadratic exponential correction. -/
def reducedSigma (z : ℂ) : ℂ :=
  exp (-(L.sigmaCorrection * z ^ 2 / 2)) * L.weierstrassSigma z

/-- The relation between reduced sigma and the Weierstrass product. -/
theorem reducedSigma_def (z : ℂ) :
    L.reducedSigma z = exp (-(L.sigmaCorrection * z ^ 2 / 2)) * L.weierstrassSigma z := (rfl)

/-- Reduced sigma as the pointwise product of the correction factor and the Weierstrass product. -/
theorem reducedSigma_eq_mul :
    L.reducedSigma =
      (fun z : ℂ ↦ exp (-(L.sigmaCorrection * z ^ 2 / 2))) * L.weierstrassSigma :=
  funext fun z ↦ L.reducedSigma_def z

/-- The reduced sigma function is entire. -/
@[fun_prop]
theorem differentiable_reducedSigma : Differentiable ℂ L.reducedSigma := by
  rw [reducedSigma_eq_mul]
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
  rw [reducedSigma_eq_mul]
  simpa using he.hasDerivAt.mul L.hasDerivAt_weierstrassSigma_zero

@[simp]
theorem deriv_reducedSigma_zero : deriv L.reducedSigma 0 = 1 :=
  L.hasDerivAt_reducedSigma_zero.deriv

/-- The reduced sigma function depends only on the lattice. -/
theorem reducedSigma_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.reducedSigma = L'.reducedSigma := by
  ext z
  rw [reducedSigma_def, reducedSigma_def, sigmaCorrection_eq_of_lattice_eq h,
    weierstrassSigma_eq_of_lattice_eq h]

/-- The Hermitian transformation law of reduced sigma. The multiplier is a sign times an
exponential; the sign is `1` exactly when `l` is twice a lattice vector and `-1` otherwise. -/
theorem reducedSigma_add_coe (z : ℂ) (l : L.lattice)
    [Decidable ((l : ℂ) / 2 ∈ L.lattice)] :
    L.reducedSigma (z + l) =
      (if (l : ℂ) / 2 ∈ L.lattice then (1 : ℂ) else -1) *
        exp ((Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) * (z + l / 2)) *
          L.reducedSigma z := by
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

/-- The Hermitian transformation law for a period in twice the lattice. -/
theorem reducedSigma_add_coe_of_div_two_mem (z : ℂ) {l : L.lattice}
    (hl : (l : ℂ) / 2 ∈ L.lattice) :
    L.reducedSigma (z + l) =
      exp ((Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) * (z + l / 2)) *
        L.reducedSigma z := by
  classical
  simpa [hl] using L.reducedSigma_add_coe z l

/-- The Hermitian transformation law for a period outside twice the lattice. -/
theorem reducedSigma_add_coe_of_div_two_notMem (z : ℂ) {l : L.lattice}
    (hl : (l : ℂ) / 2 ∉ L.lattice) :
    L.reducedSigma (z + l) =
      -exp ((Real.pi / ZLattice.covolume L.lattice : ℝ) * conj (l : ℂ) * (z + l / 2)) *
        L.reducedSigma z := by
  classical
  simpa [hl] using L.reducedSigma_add_coe z l

/-- Every zero of reduced sigma is simple. -/
@[simp]
theorem analyticOrderAt_reducedSigma_coe (l : L.lattice) :
    analyticOrderAt L.reducedSigma l = 1 := by
  have he : AnalyticAt ℂ (fun z : ℂ ↦ exp (-(L.sigmaCorrection * z ^ 2 / 2))) l := by
    fun_prop
  rw [reducedSigma_eq_mul, analyticOrderAt_mul he (L.differentiable_weierstrassSigma.analyticAt l),
    he.analyticOrderAt_eq_zero.mpr (exp_ne_zero _), L.analyticOrderAt_weierstrassSigma_coe,
    zero_add]

end PeriodPair
