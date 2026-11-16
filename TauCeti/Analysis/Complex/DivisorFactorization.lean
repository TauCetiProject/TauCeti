/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Meromorphic.FactorizedRational

/-!
# Holomorphic functions with equal divisors differ by an exponential factor

On a simply connected open domain, two holomorphic functions that are nonzero
somewhere and have equal divisors satisfy `f = g * exp L` for a holomorphic
function `L`. The equality includes common zeros of `f` and `g`.

Equal divisors allow the zeros to cancel, reducing comparison of holomorphic
functions to a nowhere-zero exponential factor. This is the step that separates
the prescribed zeros of an entire function from the remaining growth information
in its factorization. Bounds on that growth can then restrict the holomorphic
exponent, for example to an affine function in Hadamard's theorem.

Both functions must be nonzero somewhere: Mathlib's divisor assigns zero to
an infinite-order germ, so the divisor of an identically zero function is zero.

On a closed disc, `AnalyticOnNhd.exists_eq_finprod_zpow_mul` divides out the zeros lying in a
smaller concentric closed disc: `f = (∏ᶠ ρ, (· - ρ) ^ m_ρ) * G` with `G` zero-free on the smaller
disc and `m_ρ` the divisor of `f` there. The product is stated as a function, in the normal form
of Mathlib's `Function.FactorizedRational`, so the API of
`TauCeti.Analysis.Meromorphic.FactorizedRational` applies to it directly.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

/-- Two holomorphic functions with equal divisors on a simply connected open domain
differ by a holomorphic exponential factor, provided neither function is identically zero.
The factorization holds at every point of the domain, including common zeros. -/
theorem exists_differentiableOn_eqOn_mul_exp_of_divisor_eq {U : Set ℂ} {f g : ℂ → ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hf0 : ∃ z ∈ U, f z ≠ 0) (hg0 : ∃ z ∈ U, g z ≠ 0)
    (hd : MeromorphicOn.divisor f U = MeromorphicOn.divisor g U) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      EqOn f (fun z ↦ g z * exp (L z)) U := by
  have hfn (z : ℂ) (hz : z ∈ U) :=
    hf.meromorphicOrderAt_ne_top_of_exists_ne_zero hUc.isPathConnected.isConnected hf0 hz
  have hgn (z : ℂ) (hz : z ∈ U) :=
    hg.meromorphicOrderAt_ne_top_of_exists_ne_zero hUc.isPathConnected.isConnected hg0 hz
  have horder (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z = meromorphicOrderAt g z :=
    hf.meromorphicOn.meromorphicOrderAt_eq_of_divisor_eq hg.meromorphicOn hd hz
      (hfn z hz) (hgn z hz)
  let q := toMeromorphicNFOn (fun z ↦ f z / g z) U
  have hqm : MeromorphicOn (fun z ↦ f z / g z) U := hf.meromorphicOn.div hg.meromorphicOn
  have hqnf : MeromorphicNFOn q U := meromorphicNFOn_toMeromorphicNFOn _ _
  have hqorder (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt q z = 0 := by
    dsimp only [q]
    rw [meromorphicOrderAt_toMeromorphicNFOn hqm hz,
      fun_meromorphicOrderAt_div (hf z hz).meromorphicAt (hg z hz).meromorphicAt, horder z hz]
    lift meromorphicOrderAt g z to ℤ using hgn z hz with n hn
    simp
  have hqa : AnalyticOnNhd ℂ q U := fun z hz ↦
    (hqnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hqorder z hz])
  have hqne (z : ℂ) (hz : z ∈ U) : q z ≠ 0 :=
    (hqnf hz).meromorphicOrderAt_eq_zero_iff.mp (hqorder z hz)
  have hprod (z : ℂ) (hz : z ∈ U) : f z = g z * q z := by
    have hge : f =ᶠ[𝓝[≠] z] fun w ↦ g w * q w := by
      filter_upwards [hqm.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
        (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hg z hz).meromorphicAt).mp (hgn z hz)]
        with w hqw hgw
      have hqw' : q w = f w / g w := hqw
      rw [mul_comm (g w), hqw', div_mul_cancel₀ _ hgw]
    exact (((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hg z hz).mul (hqa z hz)).continuousAt).mp hge).eq_of_nhds
  obtain ⟨L, hL, heq⟩ := exists_differentiableOn_eqOn_exp_comp hUc hUo
    (fun z hz ↦ (hqa z hz).differentiableAt.differentiableWithinAt)
    (by rintro ⟨z, hz, hzero⟩; exact hqne z hz hzero)
  refine ⟨L, hL, fun z hz ↦ ?_⟩
  calc
    f z = g z * q z := hprod z hz
    _ = g z * exp (L z) := congrArg (fun a ↦ g z * a) (heq hz).symm

end TauCeti

namespace AnalyticOnNhd

open Metric MeromorphicOn

variable {f : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}

/-- **Dividing out the zeros in a smaller disc.** If `f` is analytic on `closedBall z₀ R` and not
identically zero there, and `0 < R` and `r ≤ R`, then `f = (∏ᶠ ρ, (· - ρ) ^ m_ρ) * G` on
`closedBall z₀ R`, where `m_ρ` is the divisor of `f` on `closedBall z₀ r` and `G` is analytic on
`closedBall z₀ R` without zeros in `closedBall z₀ r`. -/
theorem exists_eq_finprod_zpow_mul (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hR : 0 < R) (hrR : r ≤ R) (h₀ : ∃ u ∈ closedBall z₀ R, f u ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (closedBall z₀ R) ∧ (∀ z ∈ closedBall z₀ r, G z ≠ 0) ∧
      ∀ z ∈ closedBall z₀ R,
        f z = (∏ᶠ ρ, (· - ρ) ^ divisor f (closedBall z₀ r) ρ) z * G z := by
  classical
  set D := divisor f (closedBall z₀ R)
  set D' := divisor f (closedBall z₀ r) with hD'_def
  -- Extract all zeros of `f` on the large disc: `f = (∏ᶠ u, (· - u) ^ D u) • g` off a
  -- codiscrete set, with `g` analytic and zero-free there.
  have hz₀R : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hconn : IsConnected (closedBall z₀ R) :=
    (convex_closedBall z₀ R).isConnected ⟨z₀, hz₀R⟩
  obtain ⟨g, hg, hg0, hfg⟩ := hf.meromorphicOn.extract_zeros_poles
    (fun u ↦ hf.meromorphicOrderAt_ne_top_of_exists_ne_zero hconn h₀ u.2)
    (D.finiteSupport (isCompact_closedBall z₀ R))
  -- The divisor on the small disc is the restriction of `D`, so `0 ≤ D' ≤ D`.
  have hD' (ρ : ℂ) : D' ρ = if ρ ∈ closedBall z₀ r then D ρ else 0 := by
    rw [hD'_def, ← hf.meromorphicOn.divisor_restrict (closedBall_subset_closedBall hrR),
      Function.locallyFinsuppWithin.restrict_apply]
  have hD (ρ : ℂ) : 0 ≤ D ρ := hf.divisor_nonneg ρ
  have hD'D (ρ : ℂ) : 0 ≤ D' ρ ∧ D' ρ ≤ D ρ := by
    rw [hD']; split_ifs <;> simp [hD ρ]
  -- Split the zeros into those in the small disc (exponent `D'`) and the rest (`D - D'`).
  have hsplit := Function.FactorizedRational.finprod_eq_finprod_mul_finprod_sub
    (D.finiteSupport (isCompact_closedBall _ _)) (d' := D') fun u hu hDu ↦ hu <| by
      simp [hD' u, show D u = 0 from hDu]
  -- `G` is the factor for the zeros outside the small disc times `g`.
  refine ⟨(∏ᶠ u, (· - u) ^ (D u - D' u)) * g, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · exact (Function.FactorizedRational.analyticAt (d := fun u ↦ D u - D' u)
      (sub_nonneg.2 (hD'D z).2)).mul (hg z hz)
  · refine mul_ne_zero (Function.FactorizedRational.ne_zero (d := fun u ↦ D u - D' u) ?_)
      (hg0 ⟨z, closedBall_subset_closedBall hrR hz⟩)
    simp [hD' z, hz]
  -- `f` agrees with `(∏ᶠ u, (· - u) ^ D u) • g` near `z₀`, hence on the whole connected disc.
  · have hQ : AnalyticOnNhd ℂ ((∏ᶠ u, (· - u) ^ D u) • g) (closedBall z₀ R) := fun x hx ↦
      (Function.FactorizedRational.analyticAt (d := fun u ↦ D u) (hD x)).smul (hg x hx)
    have hfreq : ∃ᶠ x in 𝓝[≠] z₀, f x = ((∏ᶠ u, (· - u) ^ D u) • g) x := by
      have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hfg z₀ hz₀R
      refine Eventually.frequently ?_
      filter_upwards [this, nhdsWithin_le_nhds (closedBall_mem_nhds z₀ hR)] with x hx hxU
      exact hx.resolve_right (not_not_intro hxU)
    rw [hf.eqOn_of_preconnected_of_frequently_eq hQ hconn.isPreconnected hz₀R hfreq hz, hsplit]
    simp only [Pi.mul_apply, smul_eq_mul, mul_assoc]

end AnalyticOnNhd
