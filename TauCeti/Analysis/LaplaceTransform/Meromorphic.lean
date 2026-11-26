/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.LaplaceTransform.Landau
import TauCeti.Analysis.Meromorphic.Identity
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.Meromorphic.TrailingCoefficient

/-!
# Meromorphic Landau theorem for Laplace transforms

If the one-sided Laplace transform of an eventually nonnegative real function continues
meromorphically to a right half-plane, then either it converges throughout that half-plane,
or the real point at its abscissa of convergence is a pole. In the first case there are no
poles in the half-plane. In the second there are none strictly to the right of the real pole.
Applying this to `C * exp (θ * u) - g u` gives the one-sided upper-bound version: if there is
a pole to the right of `θ`, the rightmost real pole has negative real trailing coefficient.

We use the local Landau theorem `TauCeti.integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg`
(Widder, *The Laplace Transform*, Chapter II, Theorem 5b) at the real abscissa, and the
meromorphic identity theorem to identify the transform with the normal form of its continuation.
`TauCeti.exists_ae_le_exp_of_eventually_le_rpow` turns an eventual bound `f x ≤ C * x ^ θ`, as for
arithmetic functions summed up to `x`, into the almost-everywhere bound on `f (exp u)` that the
one-sided version takes.

The dichotomy is Landau's theorem (E. Landau, *Über einen Satz von Tschebyschef*, Math. Ann. 61
(1905)), and the one-sided form follows the comparison argument in Montgomery and Vaughan,
*Multiplicative Number Theory I*, Section 15.1.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti

/-- On any common half-plane of convergence and meromorphic continuation, the transform
agrees with the continuation in normal form, provided they agree on some right half-plane. -/
private theorem hasLaplace_normalForm_of_convergence {g : ℝ → ℂ} {F : ℂ → ℂ} {a b c : ℝ}
    (hF : MeromorphicOn F {s | b < s.re}) (hL : ∀ s : ℂ, a < s.re → HasLaplace g s (F s))
    (hbc : b ≤ c)
    (hint : ∀ s : ℂ, c < s.re → IntegrableOn (fun u : ℝ ↦ exp (-s * u) • g u) (Ioi 0)) :
    ∀ s : ℂ, c < s.re → HasLaplace g s (toMeromorphicNFOn F {z | b < z.re} s) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ u : ℝ in Ioi 0, exp (-s * u) • g u
  have hΦ (s) (hs : c < s.re) : HasLaplace g s (Φ s) := (hint s hs).integrable.hasLaplace
  have hΦan := (differentiableOn_of_hasLaplace_re_gt hΦ).analyticOnNhd
    (isOpen_lt continuous_const continuous_re)
  let x : ℂ := ((max a c + 1 : ℝ) : ℂ)
  have hx : max a c < x.re := by simp [x]
  have hEq : F =ᶠ[𝓝 x] Φ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hx] with z hz
    exact (hL z ((le_max_left a c).trans_lt hz)).unique (hΦ z ((le_max_right a c).trans_lt hz))
  have hn : MeromorphicNFOn (toMeromorphicNFOn F {z | b < z.re}) {z | c < z.re} :=
    fun _ hz ↦ meromorphicNFOn_toMeromorphicNFOn F _ (hbc.trans_lt hz)
  have hEqN := hn.eqOn_of_isPreconnected hΦan.meromorphicNFOn
    (convex_halfSpace_re_gt c).isPreconnected ((le_max_right a c).trans_lt hx)
    ((hF.toMeromorphicNFOn_eq_self_on_nhdsNE (hbc.trans_lt ((le_max_right a c).trans_lt hx))).trans
      (hEq.filter_mono nhdsWithin_le_nhds))
  exact fun s hs ↦ hEqN hs ▸ hΦ s hs

/-- Meromorphic Landau dichotomy. For an eventually nonnegative real function, a meromorphic
continuation to `re s > b` is either pole-free there or has a rightmost pole at a real point
`β ∈ (b, a]`. The Laplace integral represents its normal form throughout the pole-free
half-plane `re s > b` or `re s > β`, respectively. -/
theorem hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a b u₀ : ℝ}
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : MeromorphicOn F {s | b < s.re})
    (hL : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s)) :
    ((∀ s : ℂ, b < s.re → 0 ≤ meromorphicOrderAt F s) ∧
      ∀ s : ℂ, b < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s
        (toMeromorphicNFOn F {z | b < z.re} s)) ∨
    ∃ β : ℝ, b < β ∧ β ≤ a ∧ meromorphicOrderAt F (β : ℂ) < 0 ∧
      (∀ s : ℂ, β < s.re → 0 ≤ meromorphicOrderAt F s) ∧
      ∀ s : ℂ, β < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s
        (toMeromorphicNFOn F {z | b < z.re} s) := by
  -- Clip the abscissa at `b`, so the infimum is real even for an entire transform.
  let S : Set ℝ := {t | b ≤ t ∧ ∀ s : ℂ, t < s.re →
    IntegrableOn (fun u : ℝ ↦ exp (-s * u) • (f u : ℂ)) (Ioi 0)}
  have hS : max a b ∈ S := ⟨le_max_right _ _, fun s hs ↦
    (hL s ((le_max_left _ _).trans_lt hs)).integrableOn⟩
  have hB : BddBelow S := ⟨b, fun _ ht ↦ ht.1⟩
  let β := sInf S
  have hbβ : b ≤ β := le_csInf ⟨_, hS⟩ fun _ ht ↦ ht.1
  have hβab : β ≤ max a b := csInf_le hB hS
  have hβ (s : ℂ) (hs : β < s.re) :
      IntegrableOn (fun u : ℝ ↦ exp (-s * u) • (f u : ℂ)) (Ioi 0) := by
    obtain ⟨t, ht, hts⟩ := exists_lt_of_csInf_lt ⟨_, hS⟩ hs
    exact ht.2 s hts
  have hLap := hasLaplace_normalForm_of_convergence hF hL hbβ hβ
  have hAn := (differentiableOn_of_hasLaplace_re_gt hLap).analyticOnNhd
    (isOpen_lt continuous_const continuous_re)
  have hNoPole (s : ℂ) (hs : β < s.re) : 0 ≤ meromorphicOrderAt F s := by
    rw [← meromorphicOrderAt_toMeromorphicNFOn hF (hbβ.trans_lt hs)]
    exact (hAn s hs).meromorphicOrderAt_nonneg
  rcases hbβ.eq_or_lt with he | hlt
  · exact Or.inl ⟨he ▸ hNoPole, he ▸ hLap⟩
  refine Or.inr ⟨β, hlt, (le_max_iff.mp hβab).resolve_right hlt.not_ge, ?_, hNoPole, hLap⟩
  by_contra! horder
  have hz : (β : ℂ) ∈ {z : ℂ | b < z.re} := by simpa using hlt
  have hAnalytic := (meromorphicNFOn_toMeromorphicNFOn F _ hz)
    |>.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by simpa only [meromorphicOrderAt_toMeromorphicNFOn hF hz] using horder)
  obtain ⟨r, hr, hball⟩ := hAnalytic.exists_ball_analyticOnNhd
  have hm : max b (β - r) ∈ S := ⟨le_max_left _ _, fun s hs ↦
    integrableOn_cexp_neg_mul_smul_ofReal_of_ae_nonneg hf hr hball.differentiableOn
      (fun z _ hz ↦ hLap z hz) ((le_max_right _ _).trans_lt hs)⟩
  exact ((csInf_le hB hm).not_gt) (max_lt hlt (sub_lt_self _ hr))

/-- If a meromorphic continuation of an eventually nonnegative function's Laplace transform
has no real pole in `(b, a]`, it has no pole anywhere in `re s > b`, and the Laplace integral
represents its normal form throughout that half-plane. -/
theorem hasLaplace_toMeromorphicNFOn_of_ae_nonneg
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a b u₀ : ℝ}
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hF : MeromorphicOn F {s | b < s.re})
    (hL : ∀ s : ℂ, a < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (F s))
    (hreal : ∀ β ∈ Ioc b a, 0 ≤ meromorphicOrderAt F (β : ℂ)) :
    (∀ s : ℂ, b < s.re → 0 ≤ meromorphicOrderAt F s) ∧
    ∀ s : ℂ, b < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s
      (toMeromorphicNFOn F {z | b < z.re} s) := by
  rcases hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole hf hF hL with
    h | ⟨β, hb, ha, hp, _, _⟩
  · exact h
  · exact (hp.not_ge (hreal β ⟨hb, ha⟩)).elim

/-- At a real pole of the Laplace transform of an eventually nonnegative real function, the
trailing coefficient is positive real if the transform converges at real points just to the
right of the pole. -/
theorem meromorphicTrailingCoeffAt_pos_of_ae_nonneg_of_hasLaplace
    {f : ℝ → ℝ} {F : ℂ → ℂ} {β u₀ : ℝ}
    (hf : ∀ᵐ u ∂volume.restrict (Ioi u₀), 0 ≤ f u)
    (hp : meromorphicOrderAt F (β : ℂ) < 0)
    (hL : ∀ᶠ (t : ℝ) in 𝓝[>] β, HasLaplace (fun u ↦ (f u : ℂ)) (t : ℂ) (F t)) :
    0 < (meromorphicTrailingCoeffAt F (β : ℂ)).re ∧
      (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 := by
  let K (t u : ℝ) := Real.exp (-t * u) * f u
  have hcast (t u : ℝ) : exp (-(t : ℂ) * u) • (f u : ℂ) = (K t u : ℂ) := by
    simp [K, smul_eq_mul]
  have hInt (t : ℝ) {z : ℂ} (h : HasLaplace (fun u ↦ (f u : ℂ)) (t : ℂ) z) :
      IntegrableOn (K t) (Ioi 0) := by
    rw [IntegrableOn]
    simpa using (h.integrable.congr (.of_forall (hcast t))).re
  -- Only the bounded initial interval can contribute negatively. Dominate it using
  -- an integrable weight at a fixed point `r` to the right of `β`.
  obtain ⟨r, hr, hβr⟩ := (hL.and (self_mem_nhdsWithin (s := Ioi β))).exists
  let B := Real.exp ((r - β) * max u₀ 0)
  let D (u : ℝ) := -(B * ‖K r u‖)
  have hD : IntegrableOn D (Ioi 0) := ((hInt r hr).norm.const_mul B).neg
  refine meromorphicTrailingCoeffAt_pos_of_eventually_real_bddBelow hp
    (M := ∫ u in Ioi 0, D u) ?_
  filter_upwards [Ioo_mem_nhdsGT (mem_Ioi.mp hβr), hL] with t ht htL
  have hValue : F t = ((∫ u in Ioi 0, K t u : ℝ) : ℂ) := by
    rw [← htL.integral_eq, ← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall (hcast t))
  rw [hValue, ofReal_im, ofReal_re]
  refine ⟨rfl, integral_mono_ae hD (hInt t htL) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioi).mp hf)] with u hu hfu
  by_cases h : u₀ < u
  · exact (neg_nonpos.mpr (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).trans
      (mul_nonneg (Real.exp_nonneg _) (hfu h))
  have hu₀ : (r - t) * u ≤ (r - β) * max u₀ 0 :=
    mul_le_mul (sub_le_sub_left ht.1.le r) ((not_lt.mp h).trans (le_max_left u₀ 0))
      hu.le (sub_nonneg.mpr (mem_Ioi.mp hβr).le)
  have hK : K t u = Real.exp ((r - t) * u) * K r u := by
    dsimp [K]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hbound : ‖K t u‖ ≤ B * ‖K r u‖ := by
    rw [hK, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu₀) (norm_nonneg _)
  exact (neg_le_neg hbound).trans (neg_abs_le _)

/-- **One-sided Landau theorem.** Suppose `g` is eventually bounded above by `C * exp (θ * u)`.
If its Laplace transform continues meromorphically to `re s > θ`, then it is either pole-free
there or has a rightmost pole `β ∈ (θ, A]` on the real axis with negative real trailing
coefficient. The integral converges throughout `re s > θ` or `re s > β`, respectively. -/
theorem hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole_of_ae_le_exp
    {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ C u₀ : ℝ}
    (hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), g u ≤ C * Real.exp (θ * u))
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s)) :
    ((∀ s : ℂ, θ < s.re → 0 ≤ meromorphicOrderAt F s) ∧
      ∀ s : ℂ, θ < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s
        (toMeromorphicNFOn F {z | θ < z.re} s)) ∨
    ∃ β : ℝ, θ < β ∧ β ≤ A ∧ meromorphicOrderAt F (β : ℂ) < 0 ∧
      (meromorphicTrailingCoeffAt F (β : ℂ)).re < 0 ∧
      (meromorphicTrailingCoeffAt F (β : ℂ)).im = 0 ∧
      (∀ s : ℂ, β < s.re → 0 ≤ meromorphicOrderAt F s) ∧
      ∀ s : ℂ, β < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s
        (toMeromorphicNFOn F {z | θ < z.re} s) := by
  let P (s : ℂ) := (C : ℂ) * (s - θ)⁻¹
  let H (s : ℂ) := P s - F s
  let f (u : ℝ) := C * Real.exp (θ * u) - g u
  have hP (s : ℂ) (hs : θ < s.re) : AnalyticAt ℂ P s := by
    have hne : s - (θ : ℂ) ≠ 0 := sub_ne_zero.mpr fun he ↦ by simp [he] at hs
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hne)
  have hH : MeromorphicOn H {s | θ < s.re} := fun s hs ↦
    (hP s hs).meromorphicAt.sub (hF s hs)
  have hPS (s : ℂ) (hs : θ < s.re) :
      HasLaplace (fun u : ℝ ↦ ((C * Real.exp (θ * u) : ℝ) : ℂ)) s (P s) := by
    exact ((hasLaplace_cexp_mul (w := (θ : ℂ)) (by simpa using hs)).const_smul
      (C : ℂ)).congr_ae (.of_forall fun u ↦ by simp [smul_eq_mul])
  have hHS (s : ℂ) (hs : max A θ < s.re) : HasLaplace (fun u ↦ (f u : ℂ)) s (H s) := by
    exact ((hPS s ((le_max_right _ _).trans_lt hs)).sub
      (hL s ((le_max_left _ _).trans_lt hs))).congr_ae (.of_forall fun u ↦ by simp [f])
  have hconv {c : ℝ} (hc : θ ≤ c) {Z : ℂ → ℂ}
      (hl : ∀ s : ℂ, c < s.re → HasLaplace (fun u ↦ (f u : ℂ)) s (Z s)) :=
    hasLaplace_normalForm_of_convergence hF hL hc (fun s hs ↦
      (((hPS s (hc.trans_lt hs)).sub (hl s hs)).congr_ae
        (.of_forall fun u ↦ by simp [f])).integrableOn)
  have hNo (s : ℂ) (hs : θ < s.re) :
      0 ≤ meromorphicOrderAt H s ↔ 0 ≤ meromorphicOrderAt F s :=
    (hP s hs).meromorphicOrderAt_fun_sub_nonneg_iff
  have hf := hg.mono fun _ hu ↦ sub_nonneg.mpr hu
  rcases hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole hf hH hHS with
    ⟨hn, hl⟩ | ⟨β, hb, ha, hp, hn, hl⟩
  · exact Or.inl ⟨fun s hs ↦ (hNo s hs).mp (hn s hs), hconv le_rfl hl⟩
  have hb' : θ < (β : ℂ).re := by simpa using hb
  have hlt := not_le.mp fun h ↦ hp.not_ge ((hNo β hb').mpr h)
  have hcoef : meromorphicTrailingCoeffAt H (β : ℂ) = -meromorphicTrailingCoeffAt F (β : ℂ) :=
    (hP β hb').meromorphicTrailingCoeffAt_fun_sub_of_neg hlt
  obtain ⟨hre, him⟩ := meromorphicTrailingCoeffAt_pos_of_ae_nonneg_of_hasLaplace
    (F := toMeromorphicNFOn H {s | θ < s.re}) (β := β) hf
    (by simpa only [meromorphicOrderAt_toMeromorphicNFOn hH hb'] using hp)
    (by
      filter_upwards [self_mem_nhdsWithin (s := Ioi β)] with t ht
      exact hl t (by simpa using ht))
  simp only [meromorphicTrailingCoeffAt_congr_nhdsNE (hH.toMeromorphicNFOn_eq_self_on_nhdsNE hb'),
    hcoef, neg_re, neg_im, neg_eq_zero] at hre him
  exact Or.inr ⟨β, hb, (le_max_iff.mp ha).resolve_right hb.not_ge, hlt, neg_pos.mp hre, him,
    fun s hs ↦ (hNo s (hb.trans hs)).mp (hn s hs), hconv hb.le hl⟩

/-- Nonnegative real parts of the trailing coefficients at the real poles exclude every pole
in `re s > θ` under an eventual upper bound by `C * exp (θ * u)`. The continued transform,
in normal form, is represented there by the absolutely convergent Laplace integral. -/
theorem hasLaplace_toMeromorphicNFOn_of_ae_le_exp
    {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ C u₀ : ℝ}
    (hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), g u ≤ C * Real.exp (θ * u))
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    (hsign : ∀ β ∈ Ioc θ A, meromorphicOrderAt F (β : ℂ) < 0 →
      0 ≤ (meromorphicTrailingCoeffAt F (β : ℂ)).re) :
    (∀ s : ℂ, θ < s.re → 0 ≤ meromorphicOrderAt F s) ∧
    ∀ s : ℂ, θ < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s
      (toMeromorphicNFOn F {z | θ < z.re} s) := by
  rcases hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole_of_ae_le_exp hg hF hL with
    h | ⟨β, hθ, hA, hp, hc, _⟩
  · exact h
  · exact (hc.not_ge (hsign β ⟨hθ, hA⟩ hp)).elim

/-- Substituting `x = exp u` turns an eventual bound `f x ≤ C * x ^ θ` into an almost-everywhere
bound `f (exp u) ≤ C * exp (θ * u)` on a ray, the hypothesis of
`TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp` and
`TauCeti.hasLaplace_toMeromorphicNFOn_or_exists_rightmost_real_pole_of_ae_le_exp`. -/
theorem exists_ae_le_exp_of_eventually_le_rpow {f : ℝ → ℝ} {θ C : ℝ}
    (h : ∀ᶠ x in atTop, f x ≤ C * x ^ θ) :
    ∃ u₀, ∀ᵐ u ∂volume.restrict (Ioi u₀), f (Real.exp u) ≤ C * Real.exp (θ * u) := by
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (Real.tendsto_exp_atTop.eventually h)
  refine ⟨u₀, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [mul_comm θ u, Real.exp_mul]
  exact hu₀ u (le_of_lt hu)

end TauCeti
