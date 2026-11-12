/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.GraphDomain
public import TauCeti.Analysis.Sobolev.Trace.Hyperplane
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# One-sided control of the flat `W^{1,p}` trace

For `1 ≤ p < ∞`, the trace of a whole-space `W^{1,p}` function `u` on `{a} × E` is controlled by
its Sobolev norm on the half-space `H = (a, ∞) × E`, not just by its whole-space norm:

`‖Tr u‖ₚᵖ ≤ (p - 1) ‖u‖_{Lᵖ(H)}ᵖ + ‖∇u‖_{Lᵖ(H)}ᵖ`

(`TauCeti.W1p.norm_hyperplaneTrace_rpow_le_restrictL`). For `p = 2` the right side is the squared
`H¹(H)` norm (`TauCeti.W1p.norm_hyperplaneTrace_le_norm_restrictL`). Consequently two whole-space
extensions of the same Sobolev function on this half-space have the same boundary trace. This is
the extension-independence step in constructing traces on domains with flat boundary, including
local boundary charts of strips.

The Euclidean product norm is represented by `WithLp 2`. The estimate is first proved on
test functions using the one-sided trace inequality
`TauCeti.integral_hyperplane_abs_rpow_le_integral_halfSpace`, then extended by whole-space Sobolev
density. This one-sided estimate bounds the trace `TauCeti.W1p.halfSpaceTrace` of arbitrary
half-space Sobolev functions, which is in `TauCeti.Analysis.Sobolev.Trace.Extension` together with
the reflection extension operator `TauCeti.W1p.extendByReflectionL`.

The argument follows L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions Gradient ENNReal

variable {E : Type*} [NormedAddCommGroup E]

variable [MeasurableSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem norm_hyperplaneTrace_ofTestFunction_rpow_le (hp : p ≠ ∞) (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖W1p.hyperplaneTrace hp a (W1p.ofTestFunctionₗ volume ⊤ p φ)‖ ^ p.toReal ≤
      (p.toReal - 1) * ‖W1p.value (W1p.restrictL (le_top (a := normalHalfSpace (E := E) a))
        (W1p.ofTestFunctionₗ volume ⊤ p φ))‖ ^ p.toReal +
      ‖W1p.gradient (W1p.restrictL (le_top (a := normalHalfSpace (E := E) a))
        (W1p.ofTestFunctionₗ volume ⊤ p φ))‖ ^ p.toReal := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  let v := W1p.restrictL (le_top (a := normalHalfSpace (E := E) a))
    (W1p.ofTestFunctionₗ volume ⊤ p φ)
  have hu : ContDiff ℝ 1 (φ : WithLp 2 (ℝ × E) → ℝ) := φ.contDiff.of_le (by simp)
  have hv : W1p.value v =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] φ := by
    apply (W1p.value_restrictL_ae le_top _).trans
    rw [W1p.value_ofTestFunctionₗ]
    have hφ := testFunctionLp_apply_ae (mu := volume) p φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact hφ.filter_mono (ae_mono Measure.restrict_le_self)
  have hg : W1p.gradient v =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] ∇ φ := by
    apply (W1p.gradient_restrictL_ae le_top _).trans
    rw [W1p.gradient_ofTestFunctionₗ]
    have hφ := gradientTestFunctionLp_apply_ae (mu := volume) p φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact hφ.filter_mono (ae_mono Measure.restrict_le_self)
  -- The left side of the one-sided trace inequality, as a power of an `Lᵖ` norm.
  have htr : ‖W1p.hyperplaneTrace hp a (W1p.ofTestFunctionₗ volume ⊤ p φ)‖ ^ p.toReal =
      ∫ y : E, |φ (WithLp.toLp 2 (a, y))| ^ p.toReal := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp]
    apply integral_congr_ae
    filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ] with y hy
    rw [hy, Real.norm_eq_abs]
  have key := integral_hyperplane_abs_rpow_le_integral_halfSpace hu φ.hasCompactSupport a hr
  rw [← coe_normalHalfSpace a, integral_rpow_energy_eq_of_ae_eq hp hv hg, ← htr] at key
  exact key

/-- **One-sided control of the flat trace.** For `1 ≤ p < ∞`, the `p`-th power of the `Lᵖ` norm
of the flat trace of `u ∈ W^{1,p}(ℝ × E)` is at most `(p - 1) ‖u‖ᵖ + ‖∇u‖ᵖ`, with both norms
taken on the right-hand half-space alone. -/
theorem W1p.norm_hyperplaneTrace_rpow_le_restrictL (hp : p ≠ ∞) (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    ‖W1p.hyperplaneTrace hp a u‖ ^ p.toReal ≤
      (p.toReal - 1) * ‖W1p.value (W1p.restrictL
        (le_top (a := normalHalfSpace (E := E) a)) u)‖ ^ p.toReal +
      ‖W1p.gradient (W1p.restrictL (le_top (a := normalHalfSpace (E := E) a)) u)‖ ^ p.toReal := by
  have hr0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  let R := W1p.restrictL (mu := volume) (p := p) (le_top (a := normalHalfSpace (E := E) a))
  have hc1 : Continuous fun w ↦ ‖W1p.value (R w)‖ ^ p.toReal := by
    simpa only [ContinuousLinearMap.comp_apply, W1p.valueL_apply] using
      ((W1p.valueL.comp R).continuous.norm).rpow_const fun _ ↦ Or.inr hr0
  have hc2 : Continuous fun w ↦ ‖W1p.gradient (R w)‖ ^ p.toReal := by
    simpa only [ContinuousLinearMap.comp_apply, W1p.gradientL_apply] using
      ((W1p.gradientL.comp R).continuous.norm).rpow_const fun _ ↦ Or.inr hr0
  refine (W1p.denseRange_ofTestFunctionₗ_top
    (mu := (volume : Measure (WithLp 2 (ℝ × E)))) hp).induction_on u
      (isClosed_le ((W1p.hyperplaneTrace hp a).continuous.norm.rpow_const fun _ ↦ Or.inr hr0)
        ((continuous_const.mul hc1).add hc2))
      (norm_hyperplaneTrace_ofTestFunction_rpow_le hp a)

/-- The flat `H¹` trace is controlled by the Sobolev norm on the right-hand half-space alone. -/
theorem W1p.norm_hyperplaneTrace_le_norm_restrictL (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    ‖W1p.hyperplaneTrace ENNReal.ofNat_ne_top a u‖ ≤
      ‖W1p.restrictL (le_top (a := normalHalfSpace (E := E) a)) u‖ := by
  have h := W1p.norm_hyperplaneTrace_rpow_le_restrictL (p := 2) (by norm_num) a u
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [show (2 : ℝ) - 1 = 1 by norm_num, one_mul,
    ← W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Whole-space extensions whose values agree almost everywhere on the right-hand half-space
have the same flat trace. Equality of their gradients need not be assumed. -/
theorem W1p.hyperplaneTrace_eq_of_value_ae_eq (hp : p ≠ ∞) (a : ℝ)
    {u v : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p}
    (hvalue : W1p.value u =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] W1p.value v) :
    W1p.hyperplaneTrace hp a u = W1p.hyperplaneTrace hp a v := by
  have hp1 : 1 ≤ p := Fact.out
  have hr0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hp
  have h : W1p.restrictL (le_top (a := normalHalfSpace (E := E) a)) u =
      W1p.restrictL (le_top (a := normalHalfSpace (E := E) a)) v := by
    apply W1p.ext_value
    apply Lp.ext
    exact ((W1p.value_restrictL_ae le_top u).trans hvalue).trans
      (W1p.value_restrictL_ae le_top v).symm
  have hsub :
      W1p.restrictL (le_top (a := normalHalfSpace (E := E) a)) (u - v) = 0 := by
    rw [map_sub, h, sub_self]
  have hb := W1p.norm_hyperplaneTrace_rpow_le_restrictL (E := E) hp a (u - v)
  simp only [hsub, ← W1p.valueL_apply, ← W1p.gradientL_apply, map_zero, norm_zero,
    Real.zero_rpow hr0.ne', mul_zero, add_zero] at hb
  have hz : W1p.hyperplaneTrace (E := E) hp a (u - v) = 0 :=
    norm_le_zero_iff.mp (le_of_eq ((Real.rpow_eq_zero (norm_nonneg _) hr0.ne').mp
      (le_antisymm hb (Real.rpow_nonneg (norm_nonneg _) _))))
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

end TauCeti
