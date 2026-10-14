/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Hyperplane
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# One-sided control of the flat `H¹` trace

The trace of a whole-space `H¹` function on `{a} × E` is bounded by its Sobolev norm on
`(a, ∞) × E`, not just by its whole-space norm. Consequently two whole-space extensions
of the same Sobolev function on this half-space have the same boundary trace. This is the
extension-independence step in constructing traces on domains with flat boundary, including
local boundary charts of strips.

The Euclidean product norm is represented by `WithLp 2`. The estimate is first proved on
test functions using the one-sided fundamental-theorem-of-calculus estimate, then extended
by whole-space Sobolev density. This one-sided estimate bounds the trace
`TauCeti.W1p.halfSpaceTrace` of arbitrary half-space Sobolev functions, which is in
`TauCeti.Analysis.Sobolev.Trace.Extension` together with the reflection extension operator
`TauCeti.W1p.extendByReflectionL`.

The argument follows L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions Gradient ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- The open half-space to the right of the normal coordinate `a` in the Euclidean product
`ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1},
    isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ E).fst⟩

/-- Membership in the normal-coordinate half-space is a strict inequality. -/
@[simp]
theorem mem_normalHalfSpace (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalHalfSpace (E := E) a ↔ a < (WithLp.ofLp x).1 := Iff.rfl

variable [MeasurableSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

private theorem norm_hyperplaneTrace_ofTestFunction_le (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖W1p.hyperplaneTrace a (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ≤
      ‖W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ := by
  let v := W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
    (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hv : W1p.value v =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] φ := by
    apply (W1p.value_restrictL_ae le_top _).trans
    rw [W1p.value_ofTestFunctionₗ]
    have hφ := testFunctionLp_apply_ae (mu := volume) 2 φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact hφ.filter_mono (ae_mono Measure.restrict_le_self)
  have hg : W1p.gradient v =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] ∇ φ := by
    apply (W1p.gradient_restrictL_ae le_top _).trans
    rw [W1p.gradient_ofTestFunctionₗ]
    have hφ := gradientTestFunctionLp_apply_ae (mu := volume) 2 φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφ
    exact hφ.filter_mono (ae_mono Measure.restrict_le_self)
  have henergy :
      (∫ x in normalHalfSpace (E := E) a, φ x ^ 2 + ‖fderiv ℝ φ x‖ ^ 2) = ‖v‖ ^ 2 := by
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
      ← W1p.integral_value_sq_eq_norm_value_sq,
      ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    rw [← integral_add
      (Lp.memLp (W1p.value v)).integrable_sq
      ((Lp.memLp (W1p.gradient v)).integrable_norm_pow (by norm_num))]
    apply integral_congr_ae
    filter_upwards [hv, hg] with x hx hy
    simp only [hx, hy, norm_gradient_eq_norm_fderiv]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y : E, φ (WithLp.toLp 2 (a, y)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae a φ] with y hy
      simp only [hy, Real.norm_eq_abs, sq_abs]
    _ ≤ _ := (integral_hyperplane_sq_le_integral_halfSpace_sq_add_norm_fderiv_sq
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport a).trans_eq henergy

/-- The flat `H¹` trace is controlled by the Sobolev norm on the right-hand half-space alone. -/
theorem W1p.norm_hyperplaneTrace_le_norm_restrictL (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    ‖W1p.hyperplaneTrace a u‖ ≤
      ‖W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) u‖ := by
  refine (W1p.denseRange_ofTestFunctionₗ_top
    (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)).induction_on u
      (isClosed_le (W1p.hyperplaneTrace a).continuous.norm
        (W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)).continuous.norm)
      (norm_hyperplaneTrace_ofTestFunction_le a)

/-- Whole-space extensions whose values agree almost everywhere on the right-hand half-space
have the same flat trace. Equality of their gradients need not be assumed. -/
theorem W1p.hyperplaneTrace_eq_of_value_ae_eq (a : ℝ)
    {u v : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2}
    (hvalue : W1p.value u =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] W1p.value v) :
    W1p.hyperplaneTrace a u = W1p.hyperplaneTrace a v := by
  have h : W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) u =
      W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) v := by
    apply W1p.ext_value
    apply Lp.ext
    exact ((W1p.value_restrictL_ae le_top u).trans hvalue).trans
      (W1p.value_restrictL_ae le_top v).symm
  have hsub :
      W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) (u - v) = 0 := by
    rw [map_sub, h, sub_self]
  have hb := W1p.norm_hyperplaneTrace_le_norm_restrictL (E := E) a (u - v)
  rw [hsub, norm_zero] at hb
  have hz : W1p.hyperplaneTrace (E := E) a (u - v) = 0 := norm_le_zero_iff.mp hb
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

end TauCeti
