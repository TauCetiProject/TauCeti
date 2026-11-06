/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
import TauCeti.Probability.Distributions.Stable.Decomposition
import TauCeti.Probability.Distributions.Stable.LargeJumps
import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Affine
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Second moments of scalar stable laws

A stable law with valid parameters has a finite second moment exactly when its scale is zero
or its shape is two. In particular, every positive-scale non-Gaussian stable law has a
non-integrable square, including shape one and both fully skewed boundaries.

The obstruction comes from the independent large-jump factor. Square integrability of the
convolution would give square integrability of a translate of that factor, contradicting its
sharp absolute-moment threshold. Affine transport gives the result at every scale and location;
the exceptions use the existing Dirac and Gaussian moment theory.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m : ℝ}

private theorem not_memLp_two_id_stableMeasure_one_zero
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    ¬ MemLp id 2 (stableMeasure α β 1 0) := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ
    (by norm_num : (0 : ℝ) < 1)
  have hsq := h.integrable_sq
  rw [← hρ] at hsq
  obtain ⟨a, ha⟩ := ((integrable_conv_iff (by fun_prop)).1 hsq).1.exists
  have hmap : MemLp id 2 ((stableCompensatedPoissonMeasure α β 1).map
      (fun x : ℝ ↦ a + 1 * x)) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    exact (memLp_two_iff_integrable_sq (by fun_prop)).2 (by simpa using ha)
  have hlarge := (memLp_id_map_affine_iff one_ne_zero).1 hmap
  have hmoment : Integrable (fun x : ℝ ↦ |x| ^ (2 : ℝ))
      (stableCompensatedPoissonMeasure α β 1) := by
    simpa only [Real.rpow_two, sq_abs, id_eq] using hlarge.integrable_sq
  have := (integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)).1 hmoment
  linarith [hα.2]

/-- A valid scalar stable law is square-integrable exactly in the Dirac and Gaussian cases.
The criterion is independent of its location and skewness. -/
@[simp]
theorem memLp_two_id_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) :
    MemLp id 2 (stableMeasure α β s m) ↔ s = 0 ∨ α = 2 := by
  by_cases hs : s = 0
  · simp [hs, stableMeasure_zero_scale hα hβ]
  by_cases htwo : α = 2
  · subst α
    simp only [stableMeasure_two hβ, or_true, iff_true]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hnorm : ‖(s : ℝ)‖₊ = s := by
    ext
    simp
  have hmap : (stableMeasure α β 1 0).map (fun x : ℝ ↦ m + s * x) =
      stableMeasure α β s m := by
    simpa only [Real.sign_of_pos hspos, one_mul, mul_zero, add_zero, mul_one,
      hnorm] using
      (stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0)
        (a := m) (b := (s : ℝ)) (Or.inl hspos.ne'))
  rw [← hmap, memLp_id_map_affine_iff hspos.ne']
  simp only [hs, htwo, or_self, iff_false]
  exact not_memLp_two_id_stableMeasure_one_zero ⟨hα.1, lt_of_le_of_ne hα.2 htwo⟩ hβ

/-- The square is integrable under a valid stable law exactly at zero scale or shape two.
Thus it is non-integrable for every positive-scale non-Gaussian stable law. -/
@[simp]
theorem integrable_sq_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) :
    Integrable (fun x : ℝ ↦ x ^ 2) (stableMeasure α β s m) ↔ s = 0 ∨ α = 2 := by
  simpa only [id_eq] using
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).symm.trans
      (memLp_two_id_stableMeasure_iff hα hβ (s := s) (m := m))

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- A real random variable with a valid stable law has an integrable square exactly when
the law is a Dirac mass or Gaussian. -/
theorem integrable_sq_iff_stableMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {α β : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α β s m) P)
    (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) :
    Integrable (fun ω ↦ X ω ^ 2) P ↔ s = 0 ∨ α = 2 := by
  rw [← TauCeti.Probability.integrable_sq_stableMeasure_iff hα hβ, ← hX.map_eq]
  exact (integrable_map_measure (g := fun x : ℝ ↦ x ^ 2)
    (by fun_prop) hX.aemeasurable).symm

end ProbabilityTheory.HasLaw
