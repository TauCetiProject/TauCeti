/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.LaplaceTransform.Meromorphic

/-!
# One-sided Landau comparison for a difference

An eventual upper bound for a function with continued transform `F - G` can exclude poles of
`F` at points where `G` has no pole. This requires control of `G` only on the real segment
where Landau's real pole could occur and at the point being tested, not on the entire half-plane.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- Suppose `F - G` continues the Laplace transform of a function eventually bounded above by
`C * exp (θ * u)`. If the real poles of `F` between `θ` and the initial convergence line have
nonnegative real leading coefficients, and `G` has no poles on that segment, then `F` has no pole
at any point in `re s > θ` where `G` has none. -/
theorem meromorphicOrderAt_nonneg_of_hasLaplace_sub_of_ae_le_exp
    {g : ℝ → ℝ} {F G : ℂ → ℂ} {A θ C u₀ : ℝ} {s : ℂ}
    (hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), g u ≤ C * Real.exp (θ * u))
    (hF : MeromorphicOn F {z | θ < z.re}) (hG : MeromorphicOn G {z | θ < z.re})
    (hL : ∀ z : ℂ, A < z.re → HasLaplace (fun u ↦ (g u : ℂ)) z ((F - G) z))
    (hsign : ∀ b ∈ Ioc θ A, meromorphicOrderAt F (b : ℂ) < 0 →
      0 ≤ (meromorphicTrailingCoeffAt F (b : ℂ)).re)
    (hGreal : ∀ b ∈ Ioc θ A, 0 ≤ meromorphicOrderAt G (b : ℂ))
    (hs : θ < s.re) (hGs : 0 ≤ meromorphicOrderAt G s) :
    0 ≤ meromorphicOrderAt F s := by
  have horder {z : ℂ} (hz : θ < z.re) (hGz : 0 ≤ meromorphicOrderAt G z)
      (hp : meromorphicOrderAt F z < 0) :
      meromorphicOrderAt (F - G) z = meromorphicOrderAt F z := by
    rw [sub_eq_add_neg]
    apply meromorphicOrderAt_add_eq_left_of_lt (hG z hz).neg
    simpa only [← meromorphicOrderAt_neg] using hp.trans_le hGz
  have hsign' (b : ℝ) (hb : b ∈ Ioc θ A) (hp : meromorphicOrderAt (F - G) (b : ℂ) < 0) :
      0 ≤ (meromorphicTrailingCoeffAt (F - G) (b : ℂ)).re := by
    have hb' : θ < (b : ℂ).re := by simpa using hb.1
    have hFb : meromorphicOrderAt F (b : ℂ) < 0 := by
      contrapose! hp
      rw [sub_eq_add_neg]
      refine (le_min hp ?_).trans (meromorphicOrderAt_add (hF b hb') (hG b hb').neg)
      simpa only [← meromorphicOrderAt_neg] using hGreal b hb
    rw [(hG b hb').meromorphicTrailingCoeffAt_sub_eq_left_of_lt
      (hFb.trans_le (hGreal b hb))]
    exact hsign b hb hFb
  have h := (hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg (hF.sub hG) hL hsign').1 s hs
  exact le_of_not_gt fun hp ↦ (horder hs hGs hp ▸ h).not_gt hp

end TauCeti
