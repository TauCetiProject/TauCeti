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
