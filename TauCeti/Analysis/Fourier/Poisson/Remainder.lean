/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Poisson.Lattice

/-!
# Error bound in lattice Poisson summation

The deviation of a periodized Schwartz function from its mean is bounded uniformly in the
translate by the absolute sum of the nonzero dual Fourier terms, divided by the covolume.
-/

public section

open Complex MeasureTheory
open scoped FourierTransform Real RealInnerProductSpace SchwartzMap

namespace SchwartzMap

/-- The nonzero Fourier modes bound the deviation of a lattice sum from its constant term. -/
theorem norm_tsum_lattice_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (v : E) :
    ‖(∑' x : L, f (v + x)) - (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) 0‖ ≤
      (ZLattice.covolume L)⁻¹ * ∑' y : {y : ZLattice.dual L // y ≠ 0}, ‖𝓕 (f : E → ℂ) y.val‖ := by
  let g (y : ZLattice.dual L) := 𝓕 (f : E → ℂ) y * cexp (2 * π * I * ⟪v, (y : E)⟫)
  have hnorm (y : ZLattice.dual L) : ‖g y‖ = ‖𝓕 (f : E → ℂ) y‖ := by
    simp [g, Complex.norm_exp]
  have hg₀ : g 0 = 𝓕 (f : E → ℂ) 0 := by simp [g]
  have hg : Summable fun y ↦ ‖g y‖ := ZLattice.summable_norm_poisson_right L f v
  have hsplit : g 0 + (∑' y : {y : ZLattice.dual L // y ≠ 0}, g y.val) = ∑' y, g y := by
    classical
    have h := hg.of_norm.sum_add_tsum_compl (s := {0})
    rw [Finset.sum_singleton, Finset.coe_singleton, Set.compl_singleton_eq] at h
    exact h
  have hpoisson : (∑' x : L, f (v + x)) = (ZLattice.covolume L : ℂ)⁻¹ * ∑' y, g y :=
    f.tsum_eq_tsum_dual_fourier L v
  rw [hpoisson, ← hsplit, hg₀, ← mul_sub, add_sub_cancel_left, norm_mul, norm_inv, norm_real,
    Real.norm_of_nonneg (ZLattice.covolume_pos L volume).le]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (ZLattice.covolume_pos L volume).le)
  simpa only [hnorm] using norm_tsum_le_tsum_norm (hg.subtype _)

end SchwartzMap
