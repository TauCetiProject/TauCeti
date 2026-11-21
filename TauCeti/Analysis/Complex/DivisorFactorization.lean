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
public import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.CauchyIntegral
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

On nested closed discs, `AnalyticOnNhd.finprod_zpow_factorization` gives the canonical quotient
after dividing out the inner-disc divisor. It applies to normed complex vector-valued functions,
normalizes only on the divisor support, and preserves the raw quotient everywhere else. The
factorization `f = (∏ᶠ ρ, (· - ρ) ^ m_ρ) • G` holds globally, including at the removed zeros.
The product is stated as a function, in the normal form of Mathlib's
`Function.FactorizedRational`, so the API of
`Mathlib.Analysis.Meromorphic.FactorizedRational` applies to it directly.
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
an integer multiple of `2 * π * I` whenever `g` is continuous on the domain and not identically
zero there. -/
theorem exists_int_eqOn_add_mul_two_pi_I_of_eqOn_mul_exp {U : Set ℂ} {g L₁ L₂ : ℂ → ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hg : ContinuousOn g U) (hg0 : ∃ z ∈ U, g z ≠ 0)
    (hL₁ : DifferentiableOn ℂ L₁ U) (hL₂ : DifferentiableOn ℂ L₂ U)
    (heq : EqOn (fun z ↦ g z * exp (L₁ z)) (fun z ↦ g z * exp (L₂ z)) U) :
    ∃ k : ℤ, EqOn L₁ (fun z ↦ L₂ z + k * (2 * Real.pi * I)) U := by
  obtain ⟨z₀, hz₀U, hgz₀⟩ := hg0
  have hexp₀ : exp (L₁ z₀) = exp (L₂ z₀) := mul_left_cancel₀ hgz₀ (heq hz₀U)
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp hexp₀
  refine ⟨k, ?_⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, w ∈ U ∧ g w ≠ 0 :=
    (eventually_of_mem (hUo.mem_nhds hz₀U) fun _ h ↦ h).and
      ((hg.continuousAt (hUo.mem_nhds hz₀U)).eventually_ne hgz₀)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  have hBsub : Metric.ball z₀ r ⊆ U := fun w hw ↦ (hball (Metric.mem_ball.mp hw)).1
  have hball_eq : EqOn L₁ (fun w ↦ L₂ w + k * (2 * Real.pi * I)) (Metric.ball z₀ r) :=
    ((hL₁.mono hBsub).continuousOn).eqOn_of_eqOn_exp_comp
      ((hL₂.add_const _).mono hBsub).continuousOn
      (convex_ball z₀ r).isPreconnected
      (fun w hw ↦ (mul_left_cancel₀ (hball (Metric.mem_ball.mp hw)).2 (heq (hBsub hw))).trans
        (exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩).symm)
      (Metric.mem_ball_self hr) hk
  exact (hL₁.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    ((hL₂.add_const _).analyticOnNhd hUo) hUc hz₀U
    (eventuallyEq_of_mem (Metric.ball_mem_nhds z₀ hr) fun w hw ↦ hball_eq hw)

end TauCeti

namespace Differentiable

/-- If `F` is continuous and not identically zero, two entire functions `g₁` and `g₂` satisfying
`Complex.exp (g₁ z) * F z = Complex.exp (g₂ z) * F z` everywhere differ by an integer multiple of
`2 * π * I`. -/
theorem exists_int_eq_add_mul_two_pi_I_of_exp_mul_eq {F g₁ g₂ : ℂ → ℂ}
    (hg₁ : Differentiable ℂ g₁) (hg₂ : Differentiable ℂ g₂) (hF : Continuous F)
    (hF0 : ∃ z, F z ≠ 0) (heq : ∀ z, Complex.exp (g₁ z) * F z = Complex.exp (g₂ z) * F z) :
    ∃ k : ℤ, ∀ z, g₁ z = g₂ z + k * (2 * Real.pi * I) := by
  obtain ⟨z₀, hz₀⟩ := hF0
  obtain ⟨k, hk⟩ := TauCeti.exists_int_eqOn_add_mul_two_pi_I_of_eqOn_mul_exp
    isPreconnected_univ isOpen_univ hF.continuousOn ⟨z₀, mem_univ z₀, hz₀⟩
    hg₁.differentiableOn hg₂.differentiableOn
    (fun z _ ↦ by simpa only [mul_comm] using heq z)
  exact ⟨k, fun z ↦ hk (mem_univ z)⟩

/-- Two entire functions with equal whole-plane divisors, neither identically zero, satisfy
`f z = Complex.exp (g z) * F z` for an entire function `g`, unique up to an additive constant in
`2 * π * I * ℤ`. -/
theorem exists_differentiable_eq_exp_mul_of_divisor_eq {f F : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : Differentiable ℂ F) (hf0 : ∃ z, f z ≠ 0) (hF0 : ∃ z, F z ≠ 0)
    (hd : MeromorphicOn.divisor f Set.univ = MeromorphicOn.divisor F Set.univ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = Complex.exp (g z) * F z) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' → (∀ z, f z = Complex.exp (g' z) * F z) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  obtain ⟨z₁, hz₁⟩ := hf0
  obtain ⟨z₂, hz₂⟩ := hF0
  obtain ⟨g, hg, heq⟩ := TauCeti.exists_differentiableOn_eqOn_mul_exp_of_divisor_eq
    (convex_univ.isSimplyConnected univ_nonempty) isOpen_univ
    (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hF.analyticAt z)
    ⟨z₁, mem_univ z₁, hz₁⟩ ⟨z₂, mem_univ z₂, hz₂⟩ hd
  have hg' : Differentiable ℂ g := differentiableOn_univ.mp hg
  have hfg (z : ℂ) : f z = Complex.exp (g z) * F z := by
    simpa only [mul_comm] using heq (mem_univ z)
  refine ⟨g, hg', hfg, fun g₁ hg₁ hfg₁ ↦ ?_⟩
  exact hg₁.exists_int_eq_add_mul_two_pi_I_of_exp_mul_eq hg' hF.continuous ⟨z₂, hz₂⟩
    fun z ↦ (hfg₁ z).symm.trans (hfg z)

/-- The whole-plane divisor of an entire function equals its natural-valued analytic order
`analyticOrderNatAt f z`. -/
theorem divisor_univ_eq_analyticOrderNatAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f Set.univ z = (analyticOrderNatAt f z : ℤ) :=
  (AnalyticOnNhd.meromorphicOn fun w _ ↦ hf.analyticAt w).divisor_eq_analyticOrderNatAt
    (hf.analyticAt z) (mem_univ z)

/-- Variant of `Differentiable.exists_differentiable_eq_exp_mul_of_divisor_eq` assuming equal
`analyticOrderAt` at every complex point rather than equality of `MeromorphicOn.divisor`. -/
theorem exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq {f F : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hF : Differentiable ℂ F) (hf0 : ∃ z, f z ≠ 0)
    (hord : ∀ z, analyticOrderAt f z = analyticOrderAt F z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = Complex.exp (g z) * F z) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' → (∀ z, f z = Complex.exp (g' z) * F z) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  obtain ⟨z₀, hz₀⟩ := hf0
  have hF0 : ∃ z, F z ≠ 0 :=
    ⟨z₀, (hF.analyticAt z₀).analyticOrderAt_eq_zero.mp
      ((hord z₀).symm.trans ((hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hz₀))⟩
  refine hf.exists_differentiable_eq_exp_mul_of_divisor_eq hF ⟨z₀, hz₀⟩ hF0 ?_
  ext z
  rw [hf.divisor_univ_eq_analyticOrderNatAt z, hF.divisor_univ_eq_analyticOrderNatAt z,
    analyticOrderNatAt, analyticOrderNatAt, hord z]

end Differentiable

namespace AnalyticOnNhd

open Metric MeromorphicOn

/-- **Canonical removal of the inner-disc divisor.** For a function into a normed complex space,
normalize the raw quotient only on the support of its inner-disc divisor. The resulting function
is analytic on the outer disc and nonzero on the inner disc. The factorization holds globally,
and outside the divisor support the cofactor is exactly the raw quotient. A nonzero value on the
outer disc rules out infinite-order germs; no strict positivity of either radius is required. -/
theorem finprod_zpow_factorization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z₀ : ℂ} {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hrR : r ≤ R)
    (h₀ : ∃ u ∈ closedBall z₀ R, f u ≠ 0) :
    let D := MeromorphicOn.divisor f (closedBall z₀ r)
    let P : ℂ → ℂ := ∏ᶠ ρ, (fun z : ℂ ↦ z - ρ) ^ D ρ
    let G := toMeromorphicNFOn (P⁻¹ • f) D.support
    AnalyticOnNhd ℂ G (closedBall z₀ R) ∧
      (∀ z ∈ closedBall z₀ r, G z ≠ 0) ∧
      f = P • G ∧ EqOn G (P⁻¹ • f) D.supportᶜ := by
  classical
  -- The finite inner divisor records exactly the zeros removed by the quotient.
  let D := MeromorphicOn.divisor f (closedBall z₀ r)
  let P : ℂ → ℂ := ∏ᶠ ρ, (fun z : ℂ ↦ z - ρ) ^ D ρ
  let q := P⁻¹ • f
  let G := toMeromorphicNFOn q D.support
  have hsub : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall hrR
  have hinner := hf.mono hsub
  have hconn : IsConnected (closedBall z₀ R) :=
    (convex_closedBall z₀ R).isConnected (h₀.elim fun u hu ↦ ⟨u, hu.1⟩)
  have hfinorder (z : ℂ) (hz : z ∈ closedBall z₀ R) :=
    hf.meromorphicOrderAt_ne_top_of_exists_ne_zero hconn h₀ hz
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hD (z : ℂ) : 0 ≤ D z := hinner.divisor_nonneg z
  have hP (z : ℂ) : MeromorphicAt P z :=
    (Function.FactorizedRational.meromorphicNFOn_univ (D : ℂ → ℤ)).meromorphicOn z trivial
  have hPorder (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq (D : ℂ → ℤ) hfin
  have horder (z : ℂ) (hz : z ∈ closedBall z₀ r) :
      meromorphicOrderAt f z = (D z : WithTop ℤ) := by
    rw [hinner.meromorphicOn.divisor_apply hz,
      WithTop.coe_untop₀_of_ne_top (hfinorder z (hsub hz))]
  have hzeros : closedBall z₀ r ∩ f ⁻¹' {0} = D.support :=
    hinner.meromorphicNFOn.zero_set_eq_divisor_support
      (fun u ↦ hfinorder u (hsub u.property))
  have hqm : MeromorphicOn q D.support := fun z hz ↦
    (hP z).inv.smul (hf z (hsub (D.supportWithinDomain hz))).meromorphicAt
  -- Normalize only on the divisor support. On the rest of the outer disc, the raw quotient
  -- is already analytic.
  have hGnf : MeromorphicNFOn G D.support := meromorphicNFOn_toMeromorphicNFOn _ _
  have hGorder (z : ℂ) (hz : z ∈ D.support) : meromorphicOrderAt G z = 0 := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hqm hz,
      meromorphicOrderAt_smul (hP z).inv
        (hf z (hsub (D.supportWithinDomain hz))).meromorphicAt,
      meromorphicOrderAt_inv, hPorder z, horder z (D.supportWithinDomain hz)]
    simp
  have hraw : EqOn G q D.supportᶜ := toMeromorphicNFOn_eq_self_on_compl hqm
  have hG : AnalyticOnNhd ℂ G (closedBall z₀ R) := by
    intro z hz
    by_cases hs : z ∈ D.support
    · exact (hGnf hs).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hGorder z hs).ge
    · have hPz : P z ≠ 0 := Function.FactorizedRational.ne_zero (Function.notMem_support.mp hs)
      have hqa : AnalyticAt ℂ q z :=
        ((Function.FactorizedRational.analyticAt (hD z)).inv hPz).smul (hf z hz)
      apply hqa.congr
      filter_upwards [hfin.isClosed.isOpen_compl.mem_nhds hs] with w hw
      exact (hraw hw).symm
  -- Read nonvanishing from order zero and reconstruct the factorization at every point.
  refine ⟨hG, ?_, ?_, hraw⟩
  · intro z hz
    -- Fold the displayed representative so the normal-form and complement equalities apply.
    change G z ≠ 0
    by_cases hs : z ∈ D.support
    · exact (hGnf hs).meromorphicOrderAt_eq_zero_iff.mp (hGorder z hs)
    · have hfz : f z ≠ 0 := fun h ↦ hs (hzeros ▸ ⟨hz, h⟩)
      have hPz : P z ≠ 0 := Function.FactorizedRational.ne_zero (Function.notMem_support.mp hs)
      rw [hraw hs]
      exact smul_ne_zero (inv_ne_zero hPz) hfz
  · ext z
    -- Use the same local representative for pointwise reconstruction.
    change f z = P z • G z
    by_cases hs : z ∈ D.support
    · have hfz : f z = 0 := (hzeros.symm ▸ hs).2
      have hPz : P z = 0 :=
        Function.FactorizedRational.eq_zero (d := (D : ℂ → ℤ)) hfin hs
      simp [hfz, hPz]
    · have hPz : P z ≠ 0 := Function.FactorizedRational.ne_zero (Function.notMem_support.mp hs)
      rw [hraw hs]
      simp only [q, Pi.smul_apply', Pi.inv_apply, smul_smul, mul_inv_cancel₀ hPz, one_smul]

end AnalyticOnNhd
