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

end TauCeti

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
