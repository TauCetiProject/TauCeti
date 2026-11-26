/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Contour.Argument.Principle

/-!
# Finite part of a logarithmic derivative

At a point of finite meromorphic order `n`, the logarithmic derivative has at most a simple
pole. `TauCeti.logDerivFinitePart` extracts the value of the regular part, after subtracting
`n / (z - a)`. This is also the constant used in removing the main terms from Riesz integrals.
-/

public section

open Filter Topology

namespace TauCeti

/-- The constant Laurent coefficient of `logDeriv f` at `a`, obtained by subtracting its
principal part and taking the value of the meromorphic normal form at `a`. -/
noncomputable def logDerivFinitePart (f : ℂ → ℂ) (a : ℂ) : ℂ :=
  toMeromorphicNFAt (fun z ↦ logDeriv f z - (meromorphicOrderAt f a).untop₀ / (z - a)) a a

/-- The finite part of a logarithmic derivative depends only on the punctured germ. -/
theorem logDerivFinitePart_congr_nhdsNE {f g : ℂ → ℂ} {a : ℂ}
    (h : f =ᶠ[𝓝[≠] a] g) : logDerivFinitePart f a = logDerivFinitePart g a := by
  unfold logDerivFinitePart
  apply Filter.EventuallyEq.eq_of_nhds (toMeromorphicNFAt_eventuallyEq_nhds_congr ?_)
  filter_upwards [logDeriv_congr_nhdsNE h] with z hz
  rw [meromorphicOrderAt_congr h, hz]

/-- The finite part can be read from any analytic representative of the regular part. -/
theorem _root_.AnalyticAt.logDerivFinitePart_eq {f g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a)
    (heq : (fun z ↦ logDeriv f z - (meromorphicOrderAt f a).untop₀ / (z - a)) =ᶠ[𝓝[≠] a] g) :
    logDerivFinitePart f a = g a := by
  rw [logDerivFinitePart]
  exact ((toMeromorphicNFAt_eventuallyEq_nhds_congr heq).trans
    ((toMeromorphicNFAt_eq_self.mpr hg.meromorphicNFAt).eventuallyEq)).eq_of_nhds

/-- Subtracting the principal part of a logarithmic derivative leaves an analytic germ,
including for a function that is identically zero near `a`. -/
theorem _root_.MeromorphicAt.exists_analyticAt_logDeriv_sub_order_div
    {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (fun z ↦ logDeriv f z - (meromorphicOrderAt f a).untop₀ / (z - a)) =ᶠ[𝓝[≠] a] g := by
  by_cases ht : meromorphicOrderAt f a = ⊤
  · refine ⟨fun _ ↦ 0, analyticAt_const, ?_⟩
    filter_upwards [logDeriv_congr_nhdsNE (meromorphicOrderAt_eq_top_iff.mp ht)] with z hz
    simp [ht, hz, logDeriv_apply]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    obtain ⟨g, ha, hg, heq⟩ := Contour.logDeriv_eventuallyEq_principalPart hf hn.symm
    refine ⟨logDeriv g, ha.logDeriv hg, ?_⟩
    filter_upwards [heq] with z hz
    simp [hz, ← hn, div_eq_mul_inv]

/-- At a regular nonzero point, the finite part is the usual logarithmic derivative. -/
theorem _root_.AnalyticAt.logDerivFinitePart_eq_logDeriv {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : f a ≠ 0) : logDerivFinitePart f a = logDeriv f a :=
  (hf.logDeriv ha).logDerivFinitePart_eq
    (by simp [hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr ha])

end TauCeti
