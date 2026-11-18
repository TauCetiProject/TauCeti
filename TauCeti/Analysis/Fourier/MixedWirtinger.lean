/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Fourier.TwistedWirtinger
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Poincaré inequalities on an interval with mixed boundary conditions

Let `f : ℝ → V` be a `C¹` function valued in a finite-dimensional real inner product space. The
sharp Poincaré inequality

`(π / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`

holds on `[a, b]` under each of the following conditions.

* **Neumann.** `f` has mean zero on `[a, b]`, with no condition at the endpoints
  (`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_integral_eq_zero`).
* **Mixed.** For a subspace `K`, both endpoint values `f a` and `f b` lie in `K` and the integral
  `∫ₐᵇ f` lies in the orthogonal complement `Kᗮ`
  (`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_mem_of_integral_mem_orthogonal`). The
  component of `f` in `Kᗮ` then satisfies the Dirichlet condition and the component in `K` the
  Neumann condition. For `K = ⊤` this is the Neumann case, and for `K = ⊥` it is the Dirichlet case
  `f a = f b = 0`, a special case of the antiperiodic inequality
  `TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_eq_neg`.

The constant `π / (b - a)` is half the one of Wirtinger's inequality for loops
(`TauCeti.integral_norm_sq_le_of_integral_eq_zero`), in which the function is periodic. The mixed
condition is the one satisfied by the `t`-derivative `ξ = ∂t u` of a map `u` of the strip
`ℝ × [0, 1]` with boundary on a Lagrangian subspace `L`: the integral of each slice of `ξ` is
`u(s, 1) - u(s, 0) ∈ L`, while the Floer equation puts the boundary values of `ξ` in `J L`.

The Neumann case is reduced to the Dirichlet case by duality: for `F(t) = ∫ₐᵗ f`, which vanishes
at both endpoints, an integration by parts gives `∫ ‖f‖ ^ 2 = -∫ ⟪f', F⟫`, and the Dirichlet
inequality for `F` bounds the right-hand side.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, Cambridge University Press, 1934,
  Theorem 257 and Theorem 258.
-/

public section

open MeasureTheory Set intervalIntegral
open scoped Real RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {a b : ℝ} {f f' : ℝ → V}

omit [FiniteDimensional ℝ V] in
/-- A function with continuous derivative everywhere is `C¹`. -/
private theorem contDiff_one_of_hasDerivAt (hff' : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') : ContDiff ℝ 1 f :=
  contDiff_one_iff_deriv.2
    ⟨fun t ↦ (hff' t).differentiableAt, (funext fun t ↦ (hff' t).deriv) ▸ hf'⟩

/-- **The Dirichlet inequality for `C¹` functions.** If `f` has a continuous derivative and
vanishes at both endpoints, then `(π / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`. -/
private theorem mul_integral_norm_sq_le_of_eq_zero_of_eq_zero (hab : a < b)
    (hff' : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (ha : f a = 0) (hb : f b = 0) :
    (π / (b - a)) ^ 2 * ∫ t in a..b, ‖f t‖ ^ 2 ≤ ∫ t in a..b, ‖f' t‖ ^ 2 :=
  mul_integral_norm_sq_le_integral_norm_sq_of_eq_neg hab
    (contDiff_one_of_hasDerivAt hff' hf').contDiffOn.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun t _ ↦ hff' t)
    (hf'.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self 2)
    (by rw [ha, hb, neg_zero])

/-- **The Poincaré inequality for mean-zero functions on an interval.** If `f` has a continuous
derivative `f'` and mean zero on `[a, b]`, then
`(π / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`. No condition is imposed at the endpoints. The
constant is sharp: equality holds for `f t = cos (π (t - a) / (b - a)) • v`. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_of_integral_eq_zero (hab : a < b)
    (hff' : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hmean : ∫ t in a..b, f t = 0) :
    (π / (b - a)) ^ 2 * ∫ t in a..b, ‖f t‖ ^ 2 ≤ ∫ t in a..b, ‖f' t‖ ^ 2 := by
  have hf : Continuous f := (contDiff_one_of_hasDerivAt hff' hf').continuous
  -- The primitive `F` of `f` vanishes at both endpoints and satisfies the Dirichlet inequality.
  set F : ℝ → V := fun t ↦ ∫ x in a..t, f x
  have hF (t : ℝ) : HasDerivAt F (f t) t := (hf.integral_hasStrictDerivAt a t).hasDerivAt
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t ↦ (hF t).continuousAt
  have hD := mul_integral_norm_sq_le_of_eq_zero_of_eq_zero hab hF hf
    (integral_same (f := f)) hmean
  -- Integrating `⟪f, F⟫` by parts gives `∫ ‖f‖ ^ 2 = -∫ ⟪f', F⟫`.
  have hIBP : ∫ t in a..b, (⟪f t, f t⟫ + ⟪f' t, F t⟫) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt (fun t _ ↦ (hff' t).inner ℝ (hF t))
      ((by fun_prop : Continuous fun t ↦ ⟪f t, f t⟫ + ⟪f' t, F t⟫).intervalIntegrable _ _)]
    simp [F, hmean]
  -- Pointwise, `-⟪f', F⟫ ≤ ‖f'‖ ^ 2 / (2 λ) + λ ‖F‖ ^ 2 / 2` for `λ = (π / (b - a)) ^ 2`.
  set l := (π / (b - a)) ^ 2
  have hl : 0 < l := by have := sub_pos.2 hab; positivity
  have hpt (t : ℝ) : -⟪f' t, F t⟫ ≤ ‖f' t‖ ^ 2 / (2 * l) + l * ‖F t‖ ^ 2 / 2 := by
    have h := neg_le_of_abs_le (abs_real_inner_le_norm (f' t) (F t))
    rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖f' t‖ - l * ‖F t‖)]
  have hc₁ := (by fun_prop : Continuous fun t ↦ ⟪f t, f t⟫).intervalIntegrable (μ := volume) a b
  have hc₂ := (by fun_prop : Continuous fun t ↦ ⟪f' t, F t⟫).intervalIntegrable (μ := volume) a b
  have hc₃ := (by fun_prop : Continuous fun t ↦ ‖f' t‖ ^ 2 / (2 * l)).intervalIntegrable
    (μ := volume) a b
  have hc₄ := (by fun_prop : Continuous fun t ↦ l * ‖F t‖ ^ 2 / 2).intervalIntegrable
    (μ := volume) a b
  have hint := integral_mono_on (f := fun t ↦ -⟪f' t, F t⟫) hab.le hc₂.neg (hc₃.add hc₄)
    fun t _ ↦ hpt t
  rw [integral_add hc₁ hc₂, add_eq_zero_iff_eq_neg] at hIBP
  rw [intervalIntegral.integral_neg, ← hIBP, integral_add hc₃ hc₄, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hint
  simp only [real_inner_self_eq_norm_sq] at hint
  -- Combining with the Dirichlet inequality `l ∫ ‖F‖ ^ 2 ≤ ∫ ‖f‖ ^ 2` gives the claim.
  have h1 : ∫ t in a..b, ‖f t‖ ^ 2 ≤ 2 * ((∫ t in a..b, ‖f' t‖ ^ 2) / (2 * l)) := by linarith
  calc l * ∫ t in a..b, ‖f t‖ ^ 2
      ≤ l * (2 * ((∫ t in a..b, ‖f' t‖ ^ 2) / (2 * l))) := mul_le_mul_of_nonneg_left h1 hl.le
    _ = ∫ t in a..b, ‖f' t‖ ^ 2 := by field_simp

/-- **The Poincaré inequality with mixed boundary conditions.** Let `K` be a subspace and `f` a
function with continuous derivative `f'` whose endpoint values `f a` and `f b` lie in `K` and
whose integral over `[a, b]` lies in `Kᗮ`. Then
`(π / (b - a)) ^ 2 ∫ₐᵇ ‖f‖ ^ 2 ≤ ∫ₐᵇ ‖f'‖ ^ 2`. -/
theorem mul_integral_norm_sq_le_integral_norm_sq_of_mem_of_integral_mem_orthogonal (hab : a < b)
    (hff' : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') {K : Submodule ℝ V}
    (ha : f a ∈ K) (hb : f b ∈ K) (hint : ∫ t in a..b, f t ∈ Kᗮ) :
    (π / (b - a)) ^ 2 * ∫ t in a..b, ‖f t‖ ^ 2 ≤ ∫ t in a..b, ‖f' t‖ ^ 2 := by
  have hf : Continuous f := (contDiff_one_of_hasDerivAt hff' hf').continuous
  set P := K.starProjection
  set Q := Kᗮ.starProjection
  -- The component in `K` has mean zero, and the component in `Kᗮ` vanishes at both endpoints.
  have hP := mul_integral_norm_sq_le_integral_norm_sq_of_integral_eq_zero hab
    (f := fun t ↦ P (f t)) (fun t ↦ P.hasFDerivAt.comp_hasDerivAt t (hff' t))
    (P.continuous.comp hf')
    (by
      rw [P.intervalIntegral_comp_comm (hf.intervalIntegrable a b)]
      exact (Submodule.starProjection_apply_eq_zero_iff K).2 hint)
  have hQ := mul_integral_norm_sq_le_of_eq_zero_of_eq_zero hab (f := fun t ↦ Q (f t))
    (fun t ↦ Q.hasFDerivAt.comp_hasDerivAt t (hff' t)) (Q.continuous.comp hf')
    (Submodule.starProjection_orthogonal_apply_eq_zero ha)
    (Submodule.starProjection_orthogonal_apply_eq_zero hb)
  -- Both sides split as the sums of the two components, by Pythagoras.
  have hsplit (g : ℝ → V) (hg : Continuous g) :
      ∫ t in a..b, ‖g t‖ ^ 2 = (∫ t in a..b, ‖P (g t)‖ ^ 2) + ∫ t in a..b, ‖Q (g t)‖ ^ 2 := by
    rw [← integral_add ((by fun_prop : Continuous fun t ↦ ‖P (g t)‖ ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t ↦ ‖Q (g t)‖ ^ 2).intervalIntegrable _ _)]
    exact integral_congr fun t _ ↦ Submodule.norm_sq_eq_add_norm_sq_starProjection (g t) K
  rw [hsplit f hf, hsplit f' hf', mul_add]
  exact add_le_add hP hQ

end TauCeti
