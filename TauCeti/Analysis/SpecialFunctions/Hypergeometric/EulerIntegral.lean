/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.Complex.SlitPlane

/-!
# Euler's integral for the Gauss hypergeometric function

Euler's integral (DLMF 15.6.1), normalized by `Γ(b) Γ(c - b)`, represents the
regularized Gauss function when `0 < re b < re c`. We define this integral using
principal complex powers and prove convergence for every `z` in the cut plane
`{z | 1 - z ∈ Complex.slitPlane}`. The endpoint singularities are those of the
Beta integral; the remaining power is continuous on the closed integration interval.

The integral is defined at all parameters, but no representation of the Gauss
function is asserted outside the convergence region. In particular, its normalized
value can vanish when a Gamma factor has a pole.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation 15.6.1.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Complex

/-- Euler's integral, normalized to represent the regularized Gauss function in
its convergence region `0 < b.re < c.re`, with `1 - z ∈ Complex.slitPlane`.
Outside that region this is only the totalized integral, not an analytic continuation. -/
def eulerIntegral (a b c z : ℂ) : ℂ :=
  (Gamma b * Gamma (c - b))⁻¹ *
    ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (1 - z * t) ^ (-a)

/-- The defining normalized integral representation of `eulerIntegral`, at all parameters. -/
theorem eulerIntegral_def (a b c z : ℂ) :
    eulerIntegral a b c z =
      (Gamma b * Gamma (c - b))⁻¹ *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := (rfl)

/-- The Euler kernel has no branch-cut crossing on the closed integration interval. -/
theorem continuousOn_eulerKernel (a : ℂ) {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => (1 - z * t) ^ (-a)) (Icc 0 1) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
  exact one_sub_mul_ofReal_mem_slitPlane hz ht

/-- Euler's integrand is interval integrable throughout its classical parameter
region, for every argument off the cut `[1, ∞)`. -/
theorem intervalIntegrable_eulerIntegrand (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hcb : b.re < c.re) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ =>
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a))
      volume 0 1 := by
  exact (betaIntegral_convergent hb (by simpa using sub_pos.mpr hcb)).mul_continuousOn
    (by simpa only [uIcc_of_le zero_le_one] using continuousOn_eulerKernel a hz)

/-- For fixed endpoint exponents in the convergence region, Euler's integral is
jointly continuous in the first parameter and the argument, away from the cut. -/
theorem continuousOn_eulerIntegral {b c : ℂ} (hb : 0 < b.re) (hcb : b.re < c.re) :
    ContinuousOn (fun p : ℂ × ℂ => eulerIntegral p.1 b c p.2)
      {p | 1 - p.2 ∈ slitPlane} := by
  let U : Set (ℂ × ℂ) := {p | 1 - p.2 ∈ slitPlane}
  have hU : IsOpen U := isOpen_slitPlane.preimage (by fun_prop)
  have hβ := betaIntegral_convergent (v := c - b) hb (by simpa using sub_pos.mpr hcb)
  intro p hp
  obtain ⟨K, hK, hpK, hKU⟩ := exists_compact_subset hU hp
  have hKnhds : K ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hpK
  -- Compactness controls the nonsingular kernel uniformly near both parameters.
  have hk : ContinuousOn (fun q : (ℂ × ℂ) × ℝ =>
      (1 - q.1.2 * q.2) ^ (-q.1.1)) (K ×ˢ Icc 0 1) := by
    refine ContinuousOn.cpow (by fun_prop) (by fun_prop) fun q hq => ?_
    exact one_sub_mul_ofReal_mem_slitPlane (hKU hq.1) hq.2
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hk
  have hi : ContinuousAt (fun q : ℂ × ℂ =>
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - q.2 * t) ^ (-q.1)) p := by
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun t => ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ * M)
      ?_ ?_ (hβ.norm.mul_const M) ?_
    · filter_upwards [hKnhds] with q hq
      exact (intervalIntegrable_eulerIntegrand q.1 hb hcb
        (hKU hq)).aestronglyMeasurable_restrict_uIoc
    · filter_upwards [hKnhds] with q hq
      refine ae_of_all _ fun t ht => ?_
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (q, t) ⟨hq, ht.1.le, ht.2⟩) (norm_nonneg _)
    · refine ae_of_all _ fun t ht => ?_
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
      exact one_sub_mul_ofReal_mem_slitPlane hp ⟨ht.1.le, ht.2⟩
  exact (hi.const_mul _).continuousWithinAt

/-- With first parameter zero the normalized Euler integral is constant, even when
its argument lies on the cut. This statement does not identify a continued function there. -/
@[simp]
theorem eulerIntegral_zero_left {b c : ℂ} (hb : 0 < b.re) (hcb : b.re < c.re) (z : ℂ) :
    eulerIntegral 0 b c z = (Gamma c)⁻¹ := by
  have hcb' : 0 < (c - b).re := by simpa using sub_pos.mpr hcb
  simp only [eulerIntegral_def, neg_zero, cpow_zero, mul_one]
  rw [← betaIntegral, betaIntegral_eq_Gamma_mul_div b (c - b) hb hcb', add_sub_cancel]
  field_simp [Gamma_ne_zero_of_re_pos hb, Gamma_ne_zero_of_re_pos hcb']

/-- At zero argument the normalized Euler integral is the reciprocal Gamma factor. -/
@[simp]
theorem eulerIntegral_zero (a : ℂ) {b c : ℂ} (hb : 0 < b.re) (hcb : b.re < c.re) :
    eulerIntegral a b c 0 = (Gamma c)⁻¹ := by
  simpa [eulerIntegral_def] using eulerIntegral_zero_left hb hcb 0

end Complex
