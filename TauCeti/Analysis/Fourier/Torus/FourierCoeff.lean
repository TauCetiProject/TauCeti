/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Fourier coefficients of trigonometric polynomials on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` the monomials `mFourier n` are orthonormal, so the
Fourier coefficients of the monomial `mFourier n` are the Kronecker delta at `n`, and those of a
trigonometric polynomial `∑ n ∈ s, mFourier n • c n` with values in a complex Banach space are its
coefficients `c` on `s` and zero elsewhere.

## Main declarations

* `TauCeti.UnitAddTorus.mFourierCoeff_mFourier`: the Fourier coefficients of a monomial.
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_smul`: the Fourier coefficients of a
  trigonometric polynomial, with the scalar forms
  `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_mul` and
  `TauCeti.UnitAddTorus.mFourierCoeff_sum_mul_mFourier`.
-/

public section

open MeasureTheory UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

namespace TauCeti.UnitAddTorus

/-- The Fourier coefficients of the monomial `mFourier n` are those of the Kronecker delta at
`n`. -/
@[simp]
theorem mFourierCoeff_mFourier (n m : d → ℤ) :
    mFourierCoeff (mFourier n) m = (Pi.single n 1 : (d → ℤ) → ℂ) m := by
  have h : mFourierBasis.repr (mFourierBasis n) m = _ := mFourierBasis_repr _ m
  rw [HilbertBasis.repr_self, lp.single_apply, coe_mFourierBasis, mFourierCoeff_toLp] at h
  exact h.symm

/-- The Fourier coefficients of a trigonometric polynomial `∑ n ∈ s, mFourier n • c n` are its
coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_smul (s : Finset (d → ℤ)) (c : (d → ℤ) → E) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x • c n) m = if m ∈ s then c m else 0 := by
  have hmono (n : d → ℤ) : Integrable fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n) :=
    (by fun_prop : Continuous fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n)).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hcoeff (n : d → ℤ) : ∫ z, mFourier (-m) z • (mFourier n z • c n) =
      (Pi.single n 1 : (d → ℤ) → ℂ) m • c n := by
    rw [← mFourierCoeff_mFourier, mFourierCoeff_eq_integral_volume (mFourier n),
      ← integral_smul_const]
    simp_rw [smul_smul, smul_eq_mul]
  rw [mFourierCoeff_eq_integral_volume]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum _ fun n _ ↦ hmono n]
  simp only [hcoeff]
  split_ifs with hm
  · rw [Finset.sum_eq_single m (fun n _ hn ↦ by simp [Ne.symm hn]) (fun h ↦ absurd hm h)]
    simp
  · refine Finset.sum_eq_zero fun n hn ↦ ?_
    have hnm : m ≠ n := fun h ↦ hm (h ▸ hn)
    simp [hnm]

/-- The Fourier coefficients of a scalar trigonometric polynomial `∑ n ∈ s, mFourier n * c n`, the
`simp` normal form of `mFourierCoeff_sum_mFourier_smul` for `E = ℂ`. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_mul (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x * c n) m = if m ∈ s then c m else 0 := by
  simpa only [smul_eq_mul] using mFourierCoeff_sum_mFourier_smul s c m

/-- The Fourier coefficients of a scalar trigonometric polynomial `∑ n ∈ s, c n * mFourier n` are
its coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mul_mFourier (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, c n * mFourier n x) m = if m ∈ s then c m else 0 := by
  simp_rw [mul_comm (c _)]
  exact mFourierCoeff_sum_mFourier_mul s c m

end TauCeti.UnitAddTorus
