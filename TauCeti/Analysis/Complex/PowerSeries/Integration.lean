/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ContinuousMap

/-!
# Integrating native power series against torus weights

A native formal multilinear series representing a function on a ball can be integrated term
by term against any continuous weight on a smaller polytorus. The variables of the power
series are the contour variables themselves. Convergence is first established in the uniform
norm on the entire boundary, rather than merely at each boundary point.

In particular this justifies passing a native series through the weighted integrals that
extract multivariate Cauchy coefficients. The boundary radii can differ; a common upper bound
must be strictly inside the ball of representation. Zero radii and dimension zero are allowed
for continuous weights. Cauchy coefficient weights require positive radii.

The construction uses `HasFPowerSeriesOnBall.hasSum_compact` and
`TauCeti.torusIntegralCLM`.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Metric Set
open scoped ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {n : ℕ} {f : (Fin n → ℂ) → F} {p : FormalMultilinearSeries ℂ (Fin n → ℂ) F}
  {c : Fin n → ℂ} {R : Fin n → ℝ} {r : ℝ≥0∞}

/-- Integrate a native power series term by term against any continuous boundary weight.
Only the values of the weight on the polytorus matter. The expansion variables, rather than
an external parameter, are integrated. -/
theorem HasFPowerSeriesOnBall.hasSum_torusIntegral_smul
    (hf : HasFPowerSeriesOnBall f p c r) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < r) (hR : ∀ i, |R i| ≤ s)
    (w : (Fin n → ℂ) → ℂ)
    (hw : Continuous (fun z : (i : Fin n) → sphere (c i) |R i| ↦ w (fun i ↦ z i))) :
    HasSum (fun k ↦ ∯ z in T(c, R), w z • p k (fun _ ↦ z - c))
      (∯ z in T(c, R), w z • f z) := by
  let K := (i : Fin n) → sphere (c i) |R i|
  let g : C(K, Fin n → ℂ) := ⟨fun z i ↦ z i, by fun_prop⟩
  have hg (z : K) : ‖g z - c‖ ≤ s := by
    apply (pi_norm_le_iff_of_nonneg s.2).2
    intro i
    exact (mem_sphere_iff_norm.1 (z i).2).le.trans (hR i)
  let W : C(K, ℂ) := ⟨fun z ↦ w (fun i ↦ z i), hw⟩
  have hW : Continuous (fun v : C(K, F) ↦ W • v) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (W.continuous.comp continuous_snd).smul continuous_eval
  have hsum := (hf.hasSum_compact g hs hg).map
    (DistribSMul.toAddMonoidHom C(K, F) W) hW
  have hint := hsum.mapL (TauCeti.torusIntegralCLM c R)
  convert hint using 1
  · funext k
    exact (TauCeti.torusIntegralCLM_eq_torusIntegral c R _
      (fun z ↦ w z • p k (fun _ ↦ z - c)) (fun _ ↦ rfl)).symm
  · exact (TauCeti.torusIntegralCLM_eq_torusIntegral c R _
      (fun z ↦ w z • f z) (fun _ ↦ rfl)).symm

/-- The weighted torus integral extracting a multivariate Cauchy coefficient commutes with
summation of a native multilinear series. No symmetry of the multilinear terms is required.
The coefficient is unnormalized: divide by `(2 * π * I) ^ n` to obtain the usual coefficient. -/
theorem HasFPowerSeriesOnBall.hasSum_torusIntegral_cauchyCoeff
    (hf : HasFPowerSeriesOnBall f p c r) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < r) (hR : ∀ i, 0 < R i) (hRs : ∀ i, R i ≤ s)
    (m : Fin n → ℕ) :
    HasSum (fun k ↦ ∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ •
      p k (fun _ ↦ z - c))
      (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) := by
  apply hf.hasSum_torusIntegral_smul hs (fun i ↦ (abs_of_pos (hR i)).symm ▸ hRs i)
  apply Continuous.inv₀ (by fun_prop)
  intro z
  apply Finset.prod_ne_zero_iff.2
  intro i _
  apply pow_ne_zero
  intro h
  have hz := mem_sphere_iff_norm.1 (z i).2
  rw [h, norm_zero, abs_of_pos (hR i)] at hz
  exact (hR i).ne' hz.symm
