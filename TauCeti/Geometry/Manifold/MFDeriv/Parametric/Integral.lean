/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating integrals of time-dependent functions along maps of the plane

Let `G : ℝ → M → F` be a time-dependent function on a manifold `M`, jointly `C¹` on `ℝ × M`, and
`w : ℝ × ℝ → M` a `C¹` map of the plane, with coordinates `(s, t)`. This file differentiates in
`s` the integral over `t` of `G` along `w`:
`d/ds ∫_a^b G(t, w(s, t)) dt = ∫_a^b dG_t(∂_s w(s, t)) dt`
(`TauCeti.Manifold.hasDerivAt_intervalIntegral_apply_comp`). It is the manifold form of
`TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn`, whose partial derivative `∂_s` is identified
with the manifold differential of `G_t` applied to the partial derivative `∂_s w`.

## Main results

* `TauCeti.Manifold.fderiv_apply_comp_apply`: the partial derivative in `s` of
  `(s, t) ↦ G t (w (s, t))` is `dG_t(∂_s w)`.
* `TauCeti.Manifold.continuous_mvfderiv_apply_mfderiv`: this partial derivative is continuous
  in `t`.
* `TauCeti.Manifold.hasDerivAt_intervalIntegral_apply_comp`: differentiation under the integral.
-/

public section

open Function Set
open scoped Manifold Interval ContDiff

namespace TauCeti.Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ → M → F} {w : ℝ × ℝ → M}

/-- For a jointly `C^n` time-dependent function `G` and a `C^n` map `w` of the plane, the function
`(s, t) ↦ G t (w (s, t))` is `C^n`. -/
theorem contDiff_apply_comp {n : ℕ∞ω} (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (uncurry G))
    (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w) : ContDiff ℝ n fun z : ℝ × ℝ ↦ G z.2 (w z) :=
  contMDiff_iff_contDiff.mp (hG.comp (contDiff_snd.contMDiff.prodMk hw))

/-- For a jointly `C¹` time-dependent function `G` and a `C¹` map `w` of the plane, the partial
derivative in `s` of `(s, t) ↦ G t (w (s, t))` is `dG_t(∂_s w)`. -/
theorem fderiv_apply_comp_apply (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (uncurry G))
    (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (z : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ G z.2 (w z)) z (1, 0) =
      mvfderiv I (G z.2) (w z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I w z (1, 0)) := by
  obtain ⟨s, t⟩ := z
  have h₁ : HasDerivAt (fun s' ↦ G t (w (s', t)))
      (fderiv ℝ (fun z : ℝ × ℝ ↦ G z.2 (w z)) (s, t) (1, 0)) s :=
    ((contDiff_apply_comp hG hw).differentiable one_ne_zero (s, t)).hasFDerivAt.comp_hasDerivAt
      (f := fun s' : ℝ ↦ (s', t)) s ((hasDerivAt_id' s).prodMk (hasDerivAt_const s t))
  have hGt : MDifferentiableAt I 𝓘(ℝ, F) (G t) (w (s, t)) :=
    ((hG.comp (contMDiff_const.prodMk contMDiff_id)) (w (s, t))).mdifferentiableAt one_ne_zero
  exact h₁.unique (hasDerivAt_comp_curve hGt
    (hasMFDerivAt_apply_fst ((hw (s, t)).mdifferentiableAt one_ne_zero)))

/-- For a jointly `C¹` time-dependent function `G` and a `C¹` map `w` of the plane, the integrand
`t ↦ dG_t(∂_s w)(s₀, t)` of the derivative of `s ↦ ∫ G(t, w(s, t)) dt` is continuous. -/
theorem continuous_mvfderiv_apply_mfderiv
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (uncurry G)) (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w)
    (s₀ : ℝ) :
    Continuous fun t ↦ mvfderiv I (G t) (w (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)) :=
  ((((contDiff_apply_comp hG hw).continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
    (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ (s₀, t))).congr
    fun t ↦ fderiv_apply_comp_apply hG hw (s₀, t)

/-- **Differentiation under the integral along a map of the plane.** For a jointly `C¹`
time-dependent function `G` and a `C¹` map `w` of the plane, `s ↦ ∫_a^b G(t, w(s, t)) dt` has
derivative `∫_a^b dG_t(∂_s w(s₀, t)) dt` at `s₀`. -/
theorem hasDerivAt_intervalIntegral_apply_comp
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) 1 (uncurry G)) (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w)
    (s₀ a b : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, G t (w (s, t)))
      (∫ t in a..b, mvfderiv I (G t) (w (s₀, t)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)))
      s₀ := by
  obtain ⟨-, hd⟩ := hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ
    (contDiff_apply_comp hG hw).contDiffOn (subset_univ ({s₀} ×ˢ [[a, b]])) (x₀ := s₀)
  simpa only [fderiv_apply_comp_apply hG hw] using hd

end TauCeti.Manifold
