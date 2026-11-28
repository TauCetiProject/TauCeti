/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Inverse

/-!
# Analytic charts for regular zero sets of analytic submersions

Let `𝕜` be a complete nontrivially normed field and let `f : E → F` be analytic at a zero `p₀`
between finite-dimensional normed spaces over `𝕜`, with surjective derivative `fderiv 𝕜 f p₀`.
Splitting `E` along `ker (fderiv 𝕜 f p₀)` and identifying this kernel with a space `K` of
dimension `finrank 𝕜 E - finrank 𝕜 F` yields a continuous linear projection `L : E →L[𝕜] K`
completing `f` to a local analytic diffeomorphism `p ↦ (f p, L (p - p₀))`. Restricting its local
inverse to `{0} × K` gives an analytic parametrization `g : K → E` of the zero set `{p | f p = 0}`
near `p₀` with `g 0 = p₀`.

## Main results

* `AnalyticAt.exists_zero_set_chart`: existence of a continuous linear coordinate map
  `L : E →L[𝕜] K` and an analytic local parametrization `g : K → E` of the zero set of `f` near a
  regular zero `p₀`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/LieExponential.lean` (`exists_zero_set_chart`), generalized from
globally analytic maps `(ι → ℂ) → (σ → ℂ)` to maps analytic at a single point between arbitrary
finite-dimensional normed spaces over any complete nontrivially normed field `𝕜`.
-/

public section

open Filter Topology

/-- Near a regular zero `p₀` of an analytic map `f : E → F` between finite-dimensional normed
spaces over a complete nontrivially normed field `𝕜` (meaning `f p₀ = 0` and `fderiv 𝕜 f p₀` is
surjective), there exist a continuous linear map `L : E →L[𝕜] K` (for any space `K` of dimension
`finrank 𝕜 E - finrank 𝕜 F`) and a map `g : K → E`, analytic at `0` with `g 0 = p₀`, that locally
parametrizes the zero set of `f` with inverse `p ↦ L (p - p₀)`. -/
theorem AnalyticAt.exists_zero_set_chart {𝕜 E F K : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    {f : E → F} {p₀ : E} (hf : AnalyticAt 𝕜 f p₀) (hf0 : f p₀ = 0)
    (hsurj : Function.Surjective (fderiv 𝕜 f p₀))
    (hdim : Module.finrank 𝕜 E - Module.finrank 𝕜 F = Module.finrank 𝕜 K) :
    ∃ (L : E →L[𝕜] K) (g : K → E),
      AnalyticAt 𝕜 g 0 ∧ g 0 = p₀ ∧
      (∀ᶠ z in 𝓝 (0 : K), f (g z) = 0 ∧ L (g z - p₀) = z) ∧
      (∀ᶠ p in 𝓝 p₀, f p = 0 → g (L (p - p₀)) = p) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  obtain ⟨s, hs⟩ := (fderiv 𝕜 f p₀).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurj)
  have hright : Function.RightInverse s.toContinuousLinearMap (fderiv 𝕜 f p₀) :=
    fun y ↦ LinearMap.congr_fun hs y
  let G₀ : E ≃L[𝕜] F × (fderiv 𝕜 f p₀).ker :=
    ContinuousLinearEquiv.equivOfRightInverse (fderiv 𝕜 f p₀) s.toContinuousLinearMap hright
  have hker : Module.finrank 𝕜 (fderiv 𝕜 f p₀).ker = Module.finrank 𝕜 K := by
    have hrank := G₀.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at hrank
    omega
  let G : E ≃L[𝕜] F × K := G₀.trans
    (LinearEquiv.prodCongr (.refl 𝕜 F) (LinearEquiv.ofFinrankEq _ _ hker)).toContinuousLinearEquiv
  let L : E →L[𝕜] K := ContinuousLinearMap.snd 𝕜 F K ∘L G.toContinuousLinearMap
  let Φ : E → F × K := fun p ↦ (f p, L (p - p₀))
  have hΦ : HasStrictFDerivAt Φ G.toContinuousLinearMap p₀ := by
    have hL : HasStrictFDerivAt (fun p ↦ L (p - p₀)) L p₀ := by
      simpa using L.hasStrictFDerivAt.comp p₀ ((hasStrictFDerivAt_id p₀).sub_const p₀)
    have hprod := hf.hasStrictFDerivAt.prodMk hL
    have heq : (fderiv 𝕜 f p₀).prod L = G.toContinuousLinearMap := by
      ext p <;> simp [L, G, G₀]
    rwa [heq] at hprod
  have hΦ0 : Φ p₀ = (0, 0) := by simp [Φ, hf0]
  have hΦ_an : AnalyticAt 𝕜 Φ p₀ :=
    hf.prod ((L.analyticAt 0).comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self p₀))
  let g : K → E := fun z ↦ hΦ.localInverse Φ G p₀ (0, z)
  have hinv_an : AnalyticAt 𝕜 (hΦ.localInverse Φ G p₀) (0, 0) :=
    hΦ0 ▸ hΦ.analyticAt_localInverse hΦ_an
  refine ⟨L, g, hinv_an.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl, ?_, ?_, ?_⟩
  · simpa [g, hΦ0] using hΦ.localInverse_apply_image
  · have hcont : ContinuousAt (fun z : K ↦ ((0 : F), z)) 0 :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hcont.eventually (hΦ0 ▸ hΦ.eventually_right_inverse)] with z hz
    simpa [g, Φ, Prod.ext_iff] using hz
  · filter_upwards [hΦ.eventually_left_inverse] with p hp hfp
    simpa [g, Φ, hfp] using hp
