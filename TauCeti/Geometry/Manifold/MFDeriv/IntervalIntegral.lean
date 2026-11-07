/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating integrals along a two-parameter family of points of a manifold

Let `f : ℝ → M → F` be a time-dependent function on a manifold `M` with values in a normed space,
jointly `C¹` on `ℝ × M`, and let `u : ℝ × ℝ → M` be a `C¹` map of the plane, read as the family of
curves `t ↦ u(s, t)`. Then `s ↦ ∫_c^d f(t, u(s, t)) dt` is differentiable, with derivative the
integral of the differential of `f t` on the transverse velocity `∂_s u`:

`d/ds ∫_c^d f(t, u(s, t)) dt = ∫_c^d d(f t)(∂_s u) dt`

(`TauCeti.Manifold.hasDerivAt_intervalIntegral_comp`). The integrand is continuous in both
parameters (`TauCeti.Manifold.continuous_mvfderiv_apply_mfderiv`). This is how the Hamiltonian
term `∫₀¹ H(t, γ(t)) dt` of an action functional varies along a family of loops.

The proof reads `(s, t) ↦ f(t, u(s, t))` as a `C¹` function on the plane, differentiates under
the integral sign with `TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn`, and identifies its
partial derivative in `s` with `d(f t)(∂_s u)` by the chain rule `mvfderiv_comp_apply`.

## Main results

* `TauCeti.Manifold.continuous_mvfderiv_apply_mfderiv`: `(s, t) ↦ d(f t)(∂_s u)` is continuous.
* `TauCeti.Manifold.hasDerivAt_intervalIntegral_comp`: differentiation under the integral sign
  along a family of curves in a manifold.
-/

public section

noncomputable section

open scoped Manifold Interval

namespace TauCeti.Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → M → F} {u : ℝ × ℝ → M}

/-- The function `(s, t) ↦ f(t, u(s, t))` is `C¹` on the plane. -/
private theorem contDiff_uncurry_comp
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (Function.uncurry f))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) : ContDiff ℝ 1 fun z : ℝ × ℝ ↦ f z.2 (u z) :=
  contMDiff_iff_contDiff.mp <| hf.comp ((contDiff_snd.contMDiff).prodMk hu)

/-- The partial derivative in `s` of `(s, t) ↦ f(t, u(s, t))` is `d(f t)(∂_s u)`. -/
private theorem fderiv_uncurry_comp_apply
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (Function.uncurry f))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (s t : ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ f z.2 (u z)) (s, t) (1, 0) =
      mvfderiv I (f t) (u (s, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (1, 0)) := by
  -- Compare the function with `f t ∘ u` along the line through `(s, t)` in direction `s`.
  have hft : ContMDiff I 𝓘(ℝ, F) 1 (f t) := hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hK : ContDiff ℝ 1 (f t ∘ u) := contMDiff_iff_contDiff.mp (hft.comp hu)
  have hline : HasDerivAt (fun s' : ℝ ↦ (s', t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  have h₁ := (((contDiff_uncurry_comp hf hu).differentiable one_ne_zero) (s, t)).hasFDerivAt
    |>.comp_hasDerivAt s hline
  have h₂ := ((hK.differentiable one_ne_zero) (s, t)).hasFDerivAt.comp_hasDerivAt s hline
  have h₃ := mvfderiv_comp_apply (s, t) ((hft (u (s, t))).mdifferentiableAt one_ne_zero)
    ((hu (s, t)).mdifferentiableAt one_ne_zero) (1, 0)
  rw [mvfderiv_eq_fderiv] at h₃
  exact (h₁.unique h₂).trans h₃

/-- For a function `f` jointly `C¹` on `ℝ × M` and a `C¹` map `u` of the plane, the differential
`d(f t)(∂_s u)` along `u` is a continuous function of `(s, t)`. -/
theorem continuous_mvfderiv_apply_mfderiv
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (Function.uncurry f))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) :
    Continuous fun z : ℝ × ℝ ↦ mvfderiv I (f z.2) (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0)) :=
  (((contDiff_uncurry_comp hf hu).continuous_fderiv one_ne_zero).clm_apply continuous_const).congr
    fun z ↦ fderiv_uncurry_comp_apply hf hu z.1 z.2

/-- **Differentiation under the integral sign along a family of curves.** For a function `f`
jointly `C¹` on `ℝ × M` and a `C¹` map `u` of the plane,
`d/ds ∫_c^d f(t, u(s, t)) dt = ∫_c^d d(f t)(∂_s u) dt`. -/
theorem hasDerivAt_intervalIntegral_comp
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (Function.uncurry f))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (c d s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in c..d, f t (u (s, t)))
      (∫ t in c..d, mvfderiv I (f t) (u (s, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (1, 0))) s :=
  (hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ (contDiff_uncurry_comp hf hu).contDiffOn
    (Set.subset_univ _) (x₀ := s) (a := c) (b := d)).2.congr_deriv
    (intervalIntegral.integral_congr fun t _ ↦ fderiv_uncurry_comp_apply hf hu s t)

end TauCeti.Manifold
