/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.Instances.Real.UniformGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Bounded
import TauCeti.MeasureTheory.Function.Lp.Order

/-!
# Maximal uniform-grid increments of real processes

Defines the maximal adjacent increment `TauCeti.Probability.maxInc` of a real process `X` along
the uniform grid `TauCeti.uniformGridFin s t m` on `[s, t]`, together with its evaluation
formulas, nonnegativity, almost-sure uniform bound, `Lᵖ` membership, and `L²` convergence to `0`
for processes continuous and bounded on `[s, t]`, without any adaptation or martingale hypotheses.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

/-- The maximal absolute increment of a real process `X` along consecutive points of the uniform
grid `TauCeti.uniformGridFin s t m`. -/
def maxInc {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty fun k ↦
    |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω|

/-- Function-level defining equation for `TauCeti.Probability.maxInc`. -/
theorem maxInc_def {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) :
    maxInc X s t m = fun ω ↦ (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
      fun k ↦ |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω| :=
  (rfl)

/-- Pointwise evaluation formula for `TauCeti.Probability.maxInc`. -/
theorem maxInc_apply {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    maxInc X s t m ω = (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty fun k ↦
      |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω| :=
  (rfl)

/-- The maximal uniform-grid increment is nonnegative everywhere. -/
theorem maxInc_nonneg {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    0 ≤ maxInc X s t m ω :=
  (abs_nonneg _).trans (Finset.le_sup' (f := fun k : Fin (m + 1) ↦
    |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω|)
    (Finset.mem_univ 0))

/-- If the grid values of `X` are almost surely bounded in absolute value by `R`, then the
maximal uniform-grid increment is almost surely at most `2 * R`. -/
theorem ae_maxInc_le {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (s t : ℝ≥0) (m : ℕ)
    (hXR : ∀ k : Fin (m + 2), ∀ᵐ ω ∂P, |X (uniformGridFin s t m k) ω| ≤ R) :
    ∀ᵐ ω ∂P, maxInc X s t m ω ≤ 2 * R :=
  (ae_all_iff.2 fun k : Fin (m + 1) ↦
    ae_norm_sub_le (f := X (uniformGridFin s t m k.succ))
      (g := X (uniformGridFin s t m k.castSucc)) (R₁ := R) (R₂ := R)
      ((hXR k.succ).mono fun _ h ↦ by rwa [Real.norm_eq_abs])
      ((hXR k.castSucc).mono fun _ h ↦ by rwa [Real.norm_eq_abs])).mono fun _ h ↦
    Finset.sup'_le _ _ fun k _ ↦ by simpa only [Real.norm_eq_abs, two_mul] using h k

/-- Under a finite measure, the maximal uniform-grid increment of a process whose grid values are
a.e. strongly measurable and almost surely bounded by `R` lies in `Lᵖ` for every `p`. -/
theorem memLp_maxInc {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {R : ℝ} (p : ℝ≥0∞) (s t : ℝ≥0) (m : ℕ)
    (hX : ∀ k : Fin (m + 2), AEStronglyMeasurable (X (uniformGridFin s t m k)) P)
    (hXR : ∀ k : Fin (m + 2), ∀ᵐ ω ∂P, |X (uniformGridFin s t m k) ω| ≤ R) :
    MemLp (maxInc X s t m) p P := by
  have hm_eq : maxInc X s t m = (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
      fun k ω ↦ |X (uniformGridFin s t m k.succ) ω - X (uniformGridFin s t m k.castSucc) ω| := by
    ext ω; simp [maxInc_apply]
  rw [hm_eq]
  refine memLp_finset_sup' Finset.univ_nonempty fun k _ ↦ MemLp.of_bound
    (continuous_abs.comp_aestronglyMeasurable ((hX k.succ).sub (hX k.castSucc))) (2 * R) ?_
  filter_upwards [ae_norm_sub_le (f := X (uniformGridFin s t m k.succ))
    (g := X (uniformGridFin s t m k.castSucc)) (R₁ := R) (R₂ := R)
    ((hXR k.succ).mono fun _ h ↦ by rwa [Real.norm_eq_abs])
    ((hXR k.castSucc).mono fun _ h ↦ by rwa [Real.norm_eq_abs])] with ω hω
  rw [Real.norm_eq_abs, abs_abs]
  simpa only [Real.norm_eq_abs, two_mul] using hω

/-- For a real process almost surely continuous and pointwise bounded on `[s, t]` (`s ≤ t`) under a
finite measure, the second moment of its maximal uniform-grid increment tends to `0`. -/
theorem tendsto_integral_maxInc_sq {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hX : ∀ u ∈ Set.Icc s t, AEStronglyMeasurable (X u) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (X · ω) (Set.Icc s t))
    (hXR : ∀ u ∈ Set.Icc s t, ∀ᵐ ω ∂P, |X u ω| ≤ R) :
    Tendsto (fun m ↦ ∫ ω, maxInc X s t m ω ^ 2 ∂P) atTop (𝓝 0) := by
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (F := fun m ω ↦ maxInc X s t m ω ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (2 * R) ^ 2)
    (fun m ↦ (memLp_maxInc 2 s t m (fun k ↦ hX _ (uniformGridFin_mem_Icc hst m k))
      (fun k ↦ hXR _ (uniformGridFin_mem_Icc hst m k))).aestronglyMeasurable.pow 2)
    (integrable_const _)
    (fun m ↦ (ae_maxInc_le s t m (fun k ↦ hXR _ (uniformGridFin_mem_Icc hst m k))).mono
      fun ω h ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (maxInc_nonneg X s t m ω) h 2)
    (hcont.mono fun ω hω ↦ by
      rw [← zero_pow two_ne_zero]
      simpa only [maxInc_apply, Real.dist_eq] using
        (tendsto_sup'_dist_uniformGridFin hst hω).pow 2)

end TauCeti.Probability
