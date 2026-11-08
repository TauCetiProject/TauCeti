/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic functions and their values on the real line

Two entire functions with values in a complex Banach space that agree at every real point are
equal. This is the identity principle `AnalyticOnNhd.eq_of_frequently_eq`, applied at the
accumulation point `0` of the real axis. It is the uniqueness statement behind analytic
continuation of real one-parameter orbits to complex time.

At a real point, the order of vanishing of a holomorphic function equals the order of vanishing
of its restriction to the real line (`AnalyticAt.analyticOrderAt_comp_ofReal`). This lets the
order of a real analytic function be read off any holomorphic extension of it.
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Two entire functions agreeing on the real line are equal. -/
theorem Differentiable.eq_of_ofReal_eq {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ t : ℝ, f t = g t) : f = g := by
  have hmaps : Set.MapsTo ((↑) : ℝ → ℂ) {0}ᶜ {0}ᶜ := fun t ht => by
    simpa using ht
  have htendsto : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa using Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (x := (0 : ℝ)) hmaps
  exact AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hf.analyticAt z)
    (fun z _ => hg.analyticAt z) (htendsto.frequently (Frequently.of_forall h))

/-- At a real point `t`, a holomorphic function `f` and its restriction `s ↦ f s` to the real line
vanish to the same order. -/
theorem AnalyticAt.analyticOrderAt_comp_ofReal {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ℂ → F} {t : ℝ} (hf : AnalyticAt ℂ f t) :
    analyticOrderAt (fun s : ℝ => f s) t = analyticOrderAt f t := by
  have hT : Tendsto ((↑) : ℝ → ℂ) (𝓝 t) (𝓝 t) := Complex.continuous_ofReal.tendsto t
  by_cases htop : analyticOrderAt f t = ⊤
  · rw [htop, analyticOrderAt_eq_top]
    exact hT.eventually (analyticOrderAt_eq_top.1 htop)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.1 hn.symm
  have hr : AnalyticAt ℝ (fun s : ℝ => f s) t :=
    (hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  rw [← hn, hr.analyticOrderAt_eq_natCast]
  refine ⟨fun s : ℝ => g s, (hg.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t),
    hg0, ?_⟩
  filter_upwards [hT.eventually hfg] with s hs
  rw [hs, ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.coe_smul]
