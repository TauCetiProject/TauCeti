/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Transform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Integral curves of log-Lipschitz fields

A time-dependent field `v : ℝ → E → E` is *log-Lipschitz* with constant `C` at small scales if

`dist (v t p) (v t q) ≤ C ℓ(dist p q)` whenever `dist p q ≤ 1`, with `ℓ(r) = r (1 - log r)`.

On `[0, 1]` the modulus `ℓ` agrees with `r (1 + log⁺ r⁻¹)`. Such a field need not be Lipschitz,
so the Grönwall comparison of `TauCeti.Analysis.ODE.Gronwall.IntegralCurve` does not apply; but
`ℓ` satisfies Osgood's condition `∫₀¹ dr / ℓ(r) = ∞`, and integral curves are still unique. This is
the regularity of the velocity of a two-dimensional incompressible flow with bounded vorticity
(Yudovich theory), where the velocity is log-Lipschitz but in general not Lipschitz.

The quantitative form is a Hölder estimate with an exponent decaying in time. If `γ₁` and `γ₂`
are integral curves on `[a, b]` with `r₀ = dist (γ₁ a) (γ₂ a)` below the threshold
`exp (1 - exp (C (b - a)))`, then for `t ∈ [a, b]`

`dist (γ₁ t) (γ₂ t) ≤ exp (1 - exp (-C (t - a))) * r₀ ^ exp (-C (t - a))`

(`IsIntegralCurveOn.dist_le_exp_mul_dist_rpow`). The right side is the solution of the comparison
equation `B' = C B (1 - log B)`, `B a = r₀`: with `s = exp (-C (t - a))` it equals
`exp (1 - s (1 - log r₀))`, so `1 - log B` decays like `s`. The threshold on `r₀` is the condition
that this solution stays below `1` up to time `b`, where the modulus `ℓ` is in force. For a
family of integral curves `γ_x` with `γ_x a = x`, this says that `x ↦ γ_x t` is Hölder continuous
with exponent `exp (-C (t - a))` at small scales, with constant `exp (1 - exp (-C (t - a))) ≤ e`.
At `r₀ = 0` the bound vanishes, which gives uniqueness: two integral curves on
`[a, b]` that agree at one time agree on `[a, b]`
(`IsIntegralCurveOn.eqOn_Icc_of_logLipschitz`).

## The argument

The comparison is a barrier argument (`image_norm_le_of_norm_deriv_right_lt_deriv_boundary`)
applied to `γ₁ - γ₂`, against the explicit solution of `B' = c B (1 - log B)` with `c > C` and
initial value `x ≥ r₀`, `x > 0`. The slack `c > C` makes the barrier strict at contact points.
Letting `(c, x) → (C, r₀)` along `c = C + δ`, `x = r₀ + δ` gives the estimate, since the barrier
is continuous in `(c, x)` in the form `exp (1 - s) * x ^ s` with `s > 0`, including at `x = 0`.
Uniqueness backward in time follows by reversing time (`IsIntegralCurveOn.comp_mul`).

## References

* W. F. Osgood, *Beweis der Existenz einer Lösung der Differentialgleichung dy/dx = f(x, y) ohne
  Hinzunahme der Cauchy-Lipschitz'schen Bedingung*, Monatsh. Math. Phys. 9 (1898), 331–345.
* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Chapter 3, §3.1 (Osgood's lemma and flows of log-Lipschitz vector
  fields).
* A. J. Majda, A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University Press,
  2002, Chapter 8, §8.2 (particle trajectories of Yudovich solutions).
-/

public section

open Set Filter Real
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The comparison function in exponential form: for `x > 0`,
`exp (1 - s) * x ^ s = exp (1 - s * (1 - log x))`. -/
private theorem exp_one_sub_mul_rpow_eq {x : ℝ} (hx : 0 < x) (s : ℝ) :
    exp (1 - s) * x ^ s = exp (1 - s * (1 - log x)) := by
  rw [rpow_def_of_pos hx, ← exp_add]
  ring_nf

/-- **Barrier step.** For `c > C`, `c ≥ 0` and `0 < x ≤ 1` with `dist (γ₁ a) (γ₂ a) ≤ x`, the
distance of two integral curves stays below the solution `exp (1 - exp (-c (t - a)) (1 - log x))`
of `B' = c B (1 - log B)`, as long as that solution stays below `1`. -/
private theorem dist_le_exp_one_sub_exp_mul_of_lt
    {γ₁ γ₂ : ℝ → E} {v : ℝ → E → E} {a b C c x : ℝ}
    (h₁ : IsIntegralCurveOn γ₁ v (Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Icc a b))
    (hv : ∀ t ∈ Ico a b, ∀ p q : E, dist p q ≤ 1 →
      dist (v t p) (v t q) ≤ C * (dist p q * (1 - log (dist p q))))
    (hCc : C < c) (hc : 0 ≤ c) (hx₀ : 0 < x) (hx₁ : x ≤ 1) (h₀ : dist (γ₁ a) (γ₂ a) ≤ x)
    (hb : exp (1 - exp (-(c * (b - a))) * (1 - log x)) ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) :
    dist (γ₁ t) (γ₂ t) ≤ exp (1 - exp (-(c * (t - a))) * (1 - log x)) := by
  set B : ℝ → ℝ := fun t ↦ exp (1 - exp (-(c * (t - a))) * (1 - log x))
  have hL : 0 < 1 - log x := by linarith [log_nonpos hx₀.le hx₁]
  have hB' (t : ℝ) : HasDerivAt B (B t * (c * exp (-(c * (t - a))) * (1 - log x))) t := by
    have h0 : HasDerivAt (fun t ↦ -(c * (t - a))) (-c) t := by
      convert (((hasDerivAt_id' t).sub_const a).const_mul c).neg using 1
      ring
    convert (h0.exp.mul_const (1 - log x)).const_sub 1 |>.exp using 1
    ring
  -- The barrier increases in time, so it stays below `1` on `[a, b]`.
  have hB1 (t : ℝ) (ht : t ∈ Icc a b) : B t ≤ 1 := by
    refine le_trans (exp_le_exp.2 ?_) hb
    have : c * (t - a) ≤ c * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hc
    gcongr
  have hBa : B a = x := by simp [B, exp_log hx₀]
  have key := image_norm_le_of_norm_deriv_right_lt_deriv_boundary (f := fun t ↦ γ₁ t - γ₂ t)
    (f' := fun t ↦ v t (γ₁ t) - v t (γ₂ t)) (h₁.continuousOn.sub h₂.continuousOn)
    (fun t ht ↦ ((h₁ t (Ico_subset_Icc_self ht)).sub
      (h₂ t (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (by rw [hBa, ← dist_eq_norm]; exact h₀) hB' (fun t ht heq ↦ ?_) ht
  · rwa [dist_eq_norm]
  -- At a contact point `dist (γ₁ t) (γ₂ t) = B t ≤ 1`, the modulus gives a velocity below `B' t`.
  have hd : dist (γ₁ t) (γ₂ t) = B t := by rw [dist_eq_norm]; exact heq
  have hlogB : log (B t) = 1 - exp (-(c * (t - a))) * (1 - log x) := log_exp _
  have hpos : 0 < B t * (exp (-(c * (t - a))) * (1 - log x)) := by positivity
  rw [← dist_eq_norm]
  calc dist (v t (γ₁ t)) (v t (γ₂ t))
      ≤ C * (dist (γ₁ t) (γ₂ t) * (1 - log (dist (γ₁ t) (γ₂ t)))) :=
        hv t ht _ _ (hd ▸ hB1 t (Ico_subset_Icc_self ht))
    _ = C * (B t * (exp (-(c * (t - a))) * (1 - log x))) := by rw [hd, hlogB]; ring
    _ < c * (B t * (exp (-(c * (t - a))) * (1 - log x))) := mul_lt_mul_of_pos_right hCc hpos
    _ = B t * (c * exp (-(c * (t - a))) * (1 - log x)) := by ring

/-- **Hölder stability of integral curves of a log-Lipschitz field.** Let `v` satisfy
`dist (v t p) (v t q) ≤ C ℓ(dist p q)` for `dist p q ≤ 1` and `t ∈ [a, b)`, with
`ℓ(r) = r (1 - log r)`. If two integral curves on `[a, b]` start at distance
`r₀ < exp (1 - exp (C (b - a)))`, then at every `t ∈ [a, b]` their distance is at most
`exp (1 - exp (-C (t - a))) * r₀ ^ exp (-C (t - a))`.

This is the explicit solution of `B' = C B (1 - log B)` with `B a = r₀`, and the threshold on `r₀`
says that this solution stays below `1` on `[a, b]`. -/
theorem IsIntegralCurveOn.dist_le_exp_mul_dist_rpow {γ₁ γ₂ : ℝ → E} {v : ℝ → E → E}
    {a b : ℝ} {C : ℝ≥0}
    (h₁ : IsIntegralCurveOn γ₁ v (Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Icc a b))
    (hv : ∀ t ∈ Ico a b, ∀ p q : E, dist p q ≤ 1 →
      dist (v t p) (v t q) ≤ C * (dist p q * (1 - log (dist p q))))
    (h₀ : dist (γ₁ a) (γ₂ a) < exp (1 - exp (C * (b - a)))) {t : ℝ} (ht : t ∈ Icc a b) :
    dist (γ₁ t) (γ₂ t) ≤
      exp (1 - exp (-(C * (t - a)))) * dist (γ₁ a) (γ₂ a) ^ exp (-(C * (t - a))) := by
  set r₀ := dist (γ₁ a) (γ₂ a)
  -- The barrier with rate `C + δ` and initial value `r₀ + δ`, at elapsed time `τ`.
  set Φ : ℝ → ℝ → ℝ := fun τ δ ↦
    exp (1 - exp (-((C + δ) * τ))) * (r₀ + δ) ^ exp (-((C + δ) * τ)) with hΦ
  have hcont (τ : ℝ) : ContinuousAt (Φ τ) 0 := by
    have hs : Continuous fun δ : ℝ ↦ exp (-((C + δ) * τ)) := by fun_prop
    exact ((continuous_const.sub hs).rexp.continuousAt).mul
      ((continuous_const.add continuous_id).continuousAt.rpow hs.continuousAt
        (.inr (exp_pos _)))
  have hΦ0 (τ : ℝ) : Φ τ 0 = exp (1 - exp (-(C * τ))) * r₀ ^ exp (-(C * τ)) := by
    simp only [hΦ, add_zero]
  have hab : 0 ≤ b - a := by linarith [ht.1, ht.2]
  have hr₀ : r₀ < 1 := h₀.trans_le (exp_le_one_iff.2 (by
    linarith [one_le_exp (mul_nonneg C.coe_nonneg hab)]))
  -- The limiting barrier stays below `1` up to time `b`.
  have hlt : Φ (b - a) 0 < 1 := by
    rw [hΦ0]
    rcases (show (0 : ℝ) ≤ r₀ from dist_nonneg).eq_or_lt with h | h
    · rw [← h, zero_rpow (exp_pos _).ne', mul_zero]
      exact one_pos
    rw [exp_one_sub_mul_rpow_eq h, Real.exp_lt_one_iff, sub_neg]
    have hlog : log r₀ < 1 - exp (C * (b - a)) := (log_lt_iff_lt_exp h).2 h₀
    have hinv : exp (-(C * (b - a))) * exp (C * (b - a)) = 1 := by
      rw [← exp_add, neg_add_cancel, exp_zero]
    nlinarith [exp_pos (-(C * (b - a)))]
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), dist (γ₁ t) (γ₂ t) ≤ Φ (t - a) δ := by
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), Φ (b - a) δ < 1 := (hcont (b - a)).eventually (gt_mem_nhds hlt)
    have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), r₀ + δ < 1 :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (gt_mem_nhds (by simpa using hr₀))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with δ hδ1 hδ2 (hδ : 0 < δ)
    have hx : 0 < r₀ + δ := by positivity
    simp only [hΦ, exp_one_sub_mul_rpow_eq hx] at hδ1 ⊢
    exact dist_le_exp_one_sub_exp_mul_of_lt h₁ h₂ hv (lt_add_of_pos_right _ hδ) (by positivity)
      hx hδ2.le (le_add_of_nonneg_right hδ.le) hδ1.le ht
  have hlim := (hcont (t - a)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [hΦ0] at hlim
  exact ge_of_tendsto hlim hev

/-- Forward uniqueness: integral curves of a log-Lipschitz field on `[a, b]` that agree at `a`
agree on `[a, b]`. -/
private theorem IsIntegralCurveOn.eqOn_Icc_of_logLipschitz_of_left {γ₁ γ₂ : ℝ → E}
    {v : ℝ → E → E} {a b : ℝ} {C : ℝ≥0}
    (h₁ : IsIntegralCurveOn γ₁ v (Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Icc a b))
    (hv : ∀ t ∈ Ico a b, ∀ p q : E, dist p q ≤ 1 →
      dist (v t p) (v t q) ≤ C * (dist p q * (1 - log (dist p q))))
    (hγ : γ₁ a = γ₂ a) : EqOn γ₁ γ₂ (Icc a b) := fun t ht ↦ by
  have h := h₁.dist_le_exp_mul_dist_rpow h₂ hv (by rw [hγ, dist_self]; exact exp_pos _) ht
  rw [hγ, dist_self, zero_rpow (exp_pos _).ne', mul_zero] at h
  exact dist_le_zero.1 h

/-- **Uniqueness of integral curves of a log-Lipschitz field** (Osgood). Let `v` satisfy
`dist (v t p) (v t q) ≤ C ℓ(dist p q)` for `dist p q ≤ 1` and `t ∈ [a, b]`, with
`ℓ(r) = r (1 - log r)`. Two integral curves of `v` on `[a, b]` that agree at one time `c ∈ [a, b]`
agree on all of `[a, b]`. -/
theorem IsIntegralCurveOn.eqOn_Icc_of_logLipschitz {γ₁ γ₂ : ℝ → E} {v : ℝ → E → E}
    {a b c : ℝ} {C : ℝ≥0}
    (h₁ : IsIntegralCurveOn γ₁ v (Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Icc a b))
    (hv : ∀ t ∈ Icc a b, ∀ p q : E, dist p q ≤ 1 →
      dist (v t p) (v t q) ≤ C * (dist p q * (1 - log (dist p q))))
    (hc : c ∈ Icc a b) (hγ : γ₁ c = γ₂ c) : EqOn γ₁ γ₂ (Icc a b) := by
  intro t ht
  rcases le_total c t with hct | htc
  · -- Forward in time, on `[c, b]`.
    have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
    exact IsIntegralCurveOn.eqOn_Icc_of_logLipschitz_of_left (h₁.mono hsub) (h₂.mono hsub)
      (fun s hs ↦ hv s (hsub (Ico_subset_Icc_self hs))) hγ ⟨hct, ht.2⟩
  · -- Backward in time: reverse time and apply the forward statement on `[-c, -a]`.
    have hsub : Icc (-c) (-a) ⊆ {s | s * -1 ∈ Icc a b} := fun s hs ↦
      ⟨by linarith [hs.2], by linarith [hs.1, hc.2]⟩
    have hv' : ∀ s ∈ Ico (-c) (-a), ∀ p q : E, dist p q ≤ 1 →
        dist (((-1 : ℝ) • v ∘ (· * -1)) s p) (((-1 : ℝ) • v ∘ (· * -1)) s q) ≤
          C * (dist p q * (1 - log (dist p q))) := fun s hs p q hpq ↦ by
      simpa only [Function.comp_apply, Pi.smul_apply, neg_one_smul, dist_neg_neg] using
        hv (s * -1) (hsub (Ico_subset_Icc_self hs)) p q hpq
    have h := IsIntegralCurveOn.eqOn_Icc_of_logLipschitz_of_left ((h₁.comp_mul (-1)).mono hsub)
      ((h₂.comp_mul (-1)).mono hsub) hv' (by simpa using hγ) (a := -c) (b := -a)
      (x := -t) ⟨neg_le_neg htc, neg_le_neg ht.1⟩
    simpa using h
