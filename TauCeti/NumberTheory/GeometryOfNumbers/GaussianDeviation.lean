/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Algebra.Module.ZLattice.Dual
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Fourier.Poisson.Remainder

/-!
# Gaussian mass of a translated dual lattice

The Gaussian at unit scale on a translate of the dual lattice has mass close to the covolume
of the original lattice whenever the nonzero vectors of that lattice carry little Gaussian
mass. The estimate is uniform in the translate, as needed for covering-radius bounds.

This is Lemma 9 of Oded Regev, [*Transference Theorems*][regev], Lecture 11 of *Lattices in
Computer Science* (2004).

[regev]: https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/transference.pdf
-/

public section

open Complex MeasureTheory
open scoped FourierTransform

namespace Submodule

open ZLattice

/-- The error from the covolume in the unit-scale Gaussian mass of any dual translate is bounded
by the covolume times the Gaussian mass of the nonzero vectors of the original lattice. -/
theorem abs_tsum_gaussian_dual_sub_covolume_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (v : E) :
    |(∑' y : dual L, Real.exp (-(Real.pi * ‖v + (y : E)‖ ^ 2))) - covolume L volume| ≤
      covolume L volume * ∑' x : {x : L // x ≠ 0}, Real.exp (-(Real.pi * ‖(x.val : E)‖ ^ 2)) := by
  have hπ : 0 < (Real.pi : ℂ).re := by simpa using Real.pi_pos
  have hFourier (x : E) : 𝓕 (SchwartzMap.gaussian hπ : E → ℂ) x =
      (Real.exp (-(Real.pi * ‖x‖ ^ 2)) : ℂ) := by
    rw [SchwartzMap.coe_gaussian, fourier_gaussian_innerProductSpace hπ x, Complex.ofReal_exp]
    have hπ₀ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [div_self hπ₀, one_cpow, one_mul]
    congr 1
    push_cast
    field_simp
  have h := (SchwartzMap.gaussian hπ).norm_tsum_lattice_sub_le (dual L) v
  simp only [hFourier] at h
  rw [covolume_dual, dual_dual, ← ofReal_inv, inv_inv, SchwartzMap.coe_gaussian_ofReal hπ,
    ← ofReal_tsum] at h
  simpa only [norm_zero, zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, ofReal_one,
    mul_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h

end Submodule
