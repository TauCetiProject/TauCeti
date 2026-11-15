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
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Holomorphic functions with equal divisors differ by an exponential factor

On a simply connected open domain, two holomorphic functions that are nonzero
somewhere and have equal divisors satisfy `f = g * exp L` for a holomorphic
function `L`, unique on any preconnected open domain up to an additive constant
in `2πiℤ`. The equality includes common zeros of `f` and `g`. Specializing to
`Set.univ` gives the entire equal-divisor factorization `f z = exp (g z) * F z`
(either from equal whole-plane divisors or from equal `analyticOrderAt` at every
point), with `g` entire and unique up to `2πiℤ`.

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

/-- On a preconnected open domain, the holomorphic exponent in `g · * exp (L ·)` is unique up to
an integer multiple of `2 * π * I` whenever `g` is analytic on a neighborhood of the domain and
not identically zero there. -/
theorem exists_int_eqOn_add_mul_two_pi_I_of_eqOn_mul_exp {U : Set ℂ} {g L₁ L₂ : ℂ → ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hg : AnalyticOnNhd ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0)
    (hL₁ : DifferentiableOn ℂ L₁ U) (hL₂ : DifferentiableOn ℂ L₂ U)
    (heq : EqOn (fun z ↦ g z * exp (L₁ z)) (fun z ↦ g z * exp (L₂ z)) U) :
    ∃ k : ℤ, EqOn L₁ (fun z ↦ L₂ z + k * (2 * Real.pi * I)) U := by
  obtain ⟨z₀, hz₀U, hgz₀⟩ := hg0
  have hexp₀ : exp (L₁ z₀) = exp (L₂ z₀) := mul_left_cancel₀ hgz₀ (heq hz₀U)
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp hexp₀
  refine ⟨k, ?_⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, w ∈ U ∧ g w ≠ 0 :=
    (eventually_of_mem (hUo.mem_nhds hz₀U) fun _ h ↦ h).and
      ((hg z₀ hz₀U).continuousAt.eventually_ne hgz₀)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  have hBsub : Metric.ball z₀ r ⊆ U := fun w hw ↦ (hball (Metric.mem_ball.mp hw)).1
  have hball_eq : EqOn L₁ (fun w ↦ L₂ w + k * (2 * Real.pi * I)) (Metric.ball z₀ r) :=
    eqOn_of_eqOn_exp_comp Metric.isOpen_ball (convex_ball z₀ r).isPreconnected
      (hL₁.mono hBsub) ((hL₂.add_const _).mono hBsub)
      (g := fun w ↦ exp (L₂ w))
      (fun w hw ↦ mul_left_cancel₀ (hball (Metric.mem_ball.mp hw)).2 (heq (hBsub hw)))
      (fun w _ ↦ exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩)
      (Metric.mem_ball_self hr) hk
  exact (hL₁.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    ((hL₂.add_const _).analyticOnNhd hUo) hUc hz₀U
    (eventuallyEq_of_mem (Metric.ball_mem_nhds z₀ hr) fun w hw ↦ hball_eq hw)

/-- If `F` is entire and not identically zero, two entire functions `g₁` and `g₂` satisfying
`exp (g₁ z) * F z = exp (g₂ z) * F z` everywhere differ by an integer multiple of `2 * π * I`. -/
theorem exists_int_eq_add_mul_two_pi_I_of_exp_mul_eq {F g₁ g₂ : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hF0 : ∃ z, F z ≠ 0) (hg₁ : Differentiable ℂ g₁)
    (hg₂ : Differentiable ℂ g₂) (heq : ∀ z, exp (g₁ z) * F z = exp (g₂ z) * F z) :
    ∃ k : ℤ, ∀ z, g₁ z = g₂ z + k * (2 * Real.pi * I) := by
  obtain ⟨z₀, hz₀⟩ := hF0
  obtain ⟨k, hk⟩ := exists_int_eqOn_add_mul_two_pi_I_of_eqOn_mul_exp
    isPreconnected_univ isOpen_univ (fun z _ ↦ hF.analyticAt z) ⟨z₀, mem_univ z₀, hz₀⟩
    hg₁.differentiableOn hg₂.differentiableOn
    (fun z _ ↦ by simpa only [mul_comm] using heq z)
  exact ⟨k, fun z ↦ hk (mem_univ z)⟩

/-- Two entire functions with equal whole-plane divisors, neither identically zero, satisfy
`f z = exp (g z) * F z` for an entire function `g`, unique up to an additive constant in
`2 * π * I * ℤ`. -/
theorem exists_differentiable_eq_exp_mul_of_divisor_eq {f F : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : Differentiable ℂ F) (hf0 : ∃ z, f z ≠ 0) (hF0 : ∃ z, F z ≠ 0)
    (hd : MeromorphicOn.divisor f Set.univ = MeromorphicOn.divisor F Set.univ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = exp (g z) * F z) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' → (∀ z, f z = exp (g' z) * F z) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  obtain ⟨z₁, hz₁⟩ := hf0
  obtain ⟨z₂, hz₂⟩ := hF0
  obtain ⟨g, hg, heq⟩ := exists_differentiableOn_eqOn_mul_exp_of_divisor_eq
    (convex_univ.isSimplyConnected univ_nonempty) isOpen_univ
    (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hF.analyticAt z)
    ⟨z₁, mem_univ z₁, hz₁⟩ ⟨z₂, mem_univ z₂, hz₂⟩ hd
  have hg' : Differentiable ℂ g := differentiableOn_univ.mp hg
  have hfg (z : ℂ) : f z = exp (g z) * F z := by
    simpa only [mul_comm] using heq (mem_univ z)
  refine ⟨g, hg', hfg, fun g₁ hg₁ hfg₁ ↦ ?_⟩
  exact exists_int_eq_add_mul_two_pi_I_of_exp_mul_eq hF ⟨z₂, hz₂⟩ hg₁ hg'
    fun z ↦ (hfg₁ z).symm.trans (hfg z)

/-- Variant of `exists_differentiable_eq_exp_mul_of_divisor_eq` assuming equal `analyticOrderAt`
at every complex point rather than equality of `MeromorphicOn.divisor`. -/
theorem exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq {f F : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : Differentiable ℂ F) (hf0 : ∃ z, f z ≠ 0) (hF0 : ∃ z, F z ≠ 0)
    (hord : ∀ z, analyticOrderAt f z = analyticOrderAt F z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = exp (g z) * F z) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' → (∀ z, f z = exp (g' z) * F z) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  refine exists_differentiable_eq_exp_mul_of_divisor_eq hf hF hf0 hF0 ?_
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun w _ ↦ hF.analyticAt w
  ext z
  rw [hfa.meromorphicOn.divisor_eq_analyticOrderNatAt (hf.analyticAt z) (mem_univ z),
    hFa.meromorphicOn.divisor_eq_analyticOrderNatAt (hF.analyticAt z) (mem_univ z),
    analyticOrderNatAt, analyticOrderNatAt, hord z]

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
