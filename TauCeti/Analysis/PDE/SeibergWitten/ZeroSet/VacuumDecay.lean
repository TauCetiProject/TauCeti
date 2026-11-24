/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
public import TauCeti.Analysis.PDE.SeibergWitten.NormSqGradient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Exponential decay of the vacuum defect where the spinor is not small

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β` and vacuum defect
`w₊ = max (1 - |α|²) 0`. Away from the zeros of `α` the solution is exponentially close to the
vacuum on the length scale `h = (2 r)^(-1/2)`. This file proves the decay mechanism behind that
statement, in a flat chart: on a ball of radius `R` on which `|α|² ≥ θ`, the vacuum defect at the
centre is

`1 - |α(z)|² ≤ 1216 C² / (θ³ r) + 2 log θ⁻¹ e^{2n/3} exp (-√(θ r) R / 4)`

(`TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`), with `n` the dimension of the chart and
`C` the constant of Taubes's coarse bounds.

The function that decays is `u = -log |α|²`, not `1 - |α|²`. The projected Weitzenböck equation
`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞` gives

`Δ |α|² / 2 = |∇_a α|² - (r / 4) (1 - |α|² - |β|²) |α|² - Re ⟪𝔞, α⟫`,

whose gradient term `|∇_a α|²`, of size `r w₊`, has the wrong sign for a maximum principle. Taking
the logarithm adds `|∇ |α|²|² / |α|⁴`, and for a complex-linear `∇_a α` the identity
`|∇ |α|²|² = 2 |α|² |∇_a α|²` cancels it exactly: then `Δ log |α|²` sees only the curvature, as for
the vortex equations. In general the defect is controlled by the `J`-antilinear part
`∂bar_a α` (`TauCeti.SeibergWitten.covariantDBar`): for every `ε > 0`,

`2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²`

with Hilbert–Schmidt norms over an orthonormal basis
(`TauCeti.SeibergWitten.two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq`, in
`TauCeti.Analysis.PDE.SeibergWitten.NormSqGradient`). The Laplacian of the logarithm is
`ContDiffAt.laplacian_log`.

With `ε = θ / (8 C)`, the coarse bounds `|β|² ≤ (C / r) w₊ + C / r²`,
`|∇_a α|² + r |∇β|² ≤ C r w₊ + C`, `|α|² ≤ 1 + C / r` and `|∂bar_a α|² ≤ C` absorb every error into
a quarter of the potential `(r / 2) w₊`, and `1 - |α|² ≥ |α|² u ≥ θ u` turns the rest into the
screened inequality `Δ u ≥ (θ r / 4) u - 304 C² / θ²` on the ball. The interior decay estimate for
subsolutions of `-Δ + c²`
(`TauCeti.le_div_sq_add_two_mul_mul_exp_of_mul_sub_le_laplacian`), with `c² = θ r / 4`, and
`1 - |α|² ≤ u` conclude.

The analytic inputs are hypotheses, in the form in which Taubes's coarse bounds are stated
elsewhere: the projected Weitzenböck equation is used in the direction opposite to
`TauCeti.SeibergWitten.norm_sq_add_norm_sq_le_one_add_div`, the bound on `β` is the conclusion of
`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_add_div_sq`, and the lower bound `|α|² ≥ θ` on the
ball is assumed. The estimate is the decay mechanism behind the off-zero bound taken as a
hypothesis by `TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_le`, but it does not yet give
that bound: it still has to be transported from the flat chart to the manifold, and combined with a
lower bound on `|α|` at distance at least a fixed multiple of `h` from the zeros of `α`. Neither
step is carried out here.

## Main results

* `TauCeti.SeibergWitten.one_sub_sq_le_div_add_mul_exp`: exponential decay of the vacuum defect
  on balls where `|α|² ≥ θ`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III (exponential decay of vortices through `log |α|²`).
-/

public section

open InnerProductSpace Laplacian Metric
open scoped Gradient

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### `-log |α|²` is a screened subsolution where `|α|` is bounded below -/

/-- A real number with `t² ≤ 2 C`, `C ≥ 1`, satisfies `|t| ≤ 2 C`. -/
private theorem abs_le_two_mul_of_sq_le {t C : ℝ} (hC : 1 ≤ C) (ht : t ^ 2 ≤ 2 * C) :
    |t| ≤ 2 * C :=
  abs_le.mpr (abs_le_of_sq_le_sq' (ht.trans (by nlinarith)) (by linarith))

/-- The coarse bound `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ ≤ 1` and `r ≥ 1`, gives
`|β|² ≤ 2 C / r`. -/
private theorem sq_le_two_mul_div {b C r w : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C) (hw1 : w ≤ 1)
    (hβ : b ^ 2 ≤ C / r * w + C / r ^ 2) : b ^ 2 ≤ 2 * C / r := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have h1 : C / r * w ≤ C / r := by
    calc C / r * w ≤ C / r * 1 := by gcongr
      _ = C / r := mul_one _
  have h2 : C / r ^ 2 ≤ C / r := div_le_div_of_nonneg_left hC hr0 (by nlinarith)
  linarith [show C / r + C / r = 2 * C / r by ring]

/-- Where `θ ≤ s ≤ 1 + C / r`, the potential term `(r / 2) (1 - s)`, after absorbing a quarter of
the vacuum defect `w₊ = max (1 - s) 0`, dominates `(θ r / 4) (-log s)` up to `C / 2`. -/
private theorem mul_neg_log_sub_le {s r w θ C : ℝ} (hr0 : 0 < r) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hθs : θ ≤ s) (hw : w = max (1 - s) 0) (hup : s ≤ 1 + C / r) :
    θ * r / 4 * -Real.log s - C / 2 ≤ r / 2 * (1 - s) - r * w / 4 := by
  have hs : 0 < s := hθ.trans_le hθs
  rcases le_or_gt s 1 with hs1 | hs1
  · have hw' : w = 1 - s := hw ▸ max_eq_left (by linarith)
    have hl : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.le hs1)
    -- `s (-log s) ≤ 1 - s` is `log s ≥ 1 - 1 / s`.
    have hsl : s * -Real.log s ≤ 1 - s := by
      have h := Real.one_sub_inv_le_log_of_pos hs
      have h' : s * (1 - s⁻¹) = s - 1 := by field_simp
      nlinarith
    have h := (mul_le_mul_of_nonneg_right hθs hl).trans hsl
    rw [hw']
    nlinarith
  · have hw' : w = 0 := hw ▸ max_eq_right (by linarith)
    have hl : Real.log s > 0 := Real.log_pos hs1
    have hup' : r * (s - 1) ≤ C := by
      have := mul_le_mul_of_nonneg_left (show s - 1 ≤ C / r by linarith) hr0.le
      rwa [mul_div_cancel₀ _ hr0.ne'] at this
    rw [hw']
    nlinarith [mul_pos (mul_pos hθ hr0) hl]

/-- The error from `∇_a α`: with `ε = θ / (8 C)` and `|∇_a α|² ≤ C r w₊ + C`,
`2 ε |∇_a α|² ≤ s (r w₊ + 1) / 4` wherever `θ ≤ s`. -/
private theorem two_mul_mul_sq_le {da ε θ C r w s : ℝ} (hC0 : 0 < C) (hθ : 0 ≤ θ)
    (hε : ε = θ / (8 * C)) (hθs : θ ≤ s) (hr0 : 0 < r) (hw0 : 0 ≤ w)
    (hda : da ^ 2 ≤ C * r * w + C) :
    2 * ε * da ^ 2 ≤ s * ((r * w + 1) / 4) := by
  have hε0 : 0 ≤ ε := hε ▸ by positivity
  calc 2 * ε * da ^ 2 ≤ 2 * ε * (C * r * w + C) := by gcongr
    _ = θ * ((r * w + 1) / 4) := by rw [hε]; field_simp; ring
    _ ≤ s * ((r * w + 1) / 4) := by gcongr

/-- For `C ≥ 1` and `0 < θ ≤ 1`, `C ≤ C² / θᵏ`. -/
private theorem le_sq_div_pow {C θ : ℝ} (k : ℕ) (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    C ≤ C ^ 2 / θ ^ k := by
  rw [le_div_iff₀ (pow_pos hθ k)]
  calc C * θ ^ k ≤ C * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hθ.le hθ1) (by linarith)
    _ ≤ C ^ 2 := by nlinarith

/-- The error from `∂bar_a α`: with `ε = θ / (8 C)`, `|∂bar_a α|² ≤ C`, `C ≥ 1` and `θ ≤ 1`,
`2 (2 + 18 / ε) |∂bar_a α|² ≤ s · 292 C² / θ²` wherever `θ ≤ s`. -/
private theorem two_mul_two_add_div_mul_sq_le {q ε θ C s : ℝ} (hC : 1 ≤ C) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hε : ε = θ / (8 * C)) (hθs : θ ≤ s) (hq : q ^ 2 ≤ C) :
    2 * (2 + 18 / ε) * q ^ 2 ≤ s * (292 * C ^ 2 / θ ^ 2) := by
  have hK : 2 + 18 / ε = 2 + 144 * C / θ := by
    rw [hε]
    field_simp
    ring
  rw [hK]
  have e1 : 2 * (2 + 144 * C / θ) * q ^ 2 ≤ 2 * (2 + 144 * C / θ) * C :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have e2 : 2 * (2 + 144 * C / θ) * C = 4 * C + 288 * (C ^ 2 / θ) := by ring
  have e3 : C ≤ C ^ 2 / θ := by simpa using le_sq_div_pow 1 hC hθ hθ1
  have e4 : θ * (292 * C ^ 2 / θ ^ 2) ≤ s * (292 * C ^ 2 / θ ^ 2) :=
    mul_le_mul_of_nonneg_right hθs (by positivity)
  have e5 : θ * (292 * C ^ 2 / θ ^ 2) = 292 * (C ^ 2 / θ) := by
    field_simp
  linarith

/-- The error from the zeroth-order terms of the Weitzenböck equation: with `|∇β| ≤ 2 C`,
`|β| ≤ 2 C` and `θ ≤ |α|`, `2 C α (|∇β| + α + |β|) ≤ |α|² (2 C + 8 C² / θ)`. -/
private theorem two_mul_mul_add_add_le {a b db C θ : ℝ} (hC0 : 0 < C) (hθ : 0 < θ)
    (ha : θ ≤ |a|) (hdb : |db| ≤ 2 * C) (hb : |b| ≤ 2 * C) :
    2 * C * a * (db + a + b) ≤ a ^ 2 * (2 * C + 8 * C ^ 2 / θ) := by
  have ha0 : 0 < |a| := hθ.trans_le ha
  have h1 : a * db + a * b ≤ |a| * (4 * C) := by
    have : a * db + a * b ≤ |a| * (|db| + |b|) := by
      rw [mul_add, ← abs_mul, ← abs_mul]
      exact add_le_add (le_abs_self _) (le_abs_self _)
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith) ha0.le)
  -- `|a| = |a|² / |a| ≤ |a|² / θ`.
  have h2 : |a| * (4 * C) ≤ a ^ 2 * (4 * C / θ) := by
    rw [← sq_abs, mul_div_assoc', le_div_iff₀ hθ]
    have := mul_le_mul_of_nonneg_left ha (mul_nonneg ha0.le (by positivity : (0 : ℝ) ≤ 4 * C))
    nlinarith
  calc 2 * C * a * (db + a + b) = 2 * C * (a * db + a * b) + 2 * C * a ^ 2 := by ring
    _ ≤ 2 * C * (a ^ 2 * (4 * C / θ)) + 2 * C * a ^ 2 := by gcongr; exact h1.trans h2
    _ = a ^ 2 * (2 * C + 8 * C ^ 2 / θ) := by ring

/-- The constants collected in the pointwise inequality: for `C ≥ 1` and `0 < θ ≤ 1`,
`1 / 4 + C + 292 C² / θ² + 2 C + 8 C² / θ + C / 2 ≤ 304 C² / θ²`. -/
private theorem const_le {C θ : ℝ} (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    1 / 4 + C + 292 * C ^ 2 / θ ^ 2 + (2 * C + 8 * C ^ 2 / θ) + C / 2 ≤ 304 * C ^ 2 / θ ^ 2 := by
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hCθ : C ≤ C ^ 2 / θ ^ 2 := le_sq_div_pow 2 hC hθ hθ1
  have h8 : 8 * C ^ 2 / θ ≤ 8 * C ^ 2 / θ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hθ2
  have e : 304 * C ^ 2 / θ ^ 2 = 292 * C ^ 2 / θ ^ 2 + 8 * C ^ 2 / θ ^ 2 + 4 * (C ^ 2 / θ ^ 2) := by
    ring
  linarith

/-- Dividing the gradient inequality by `|α|⁴` and the projected Weitzenböck equation by `|α|²`
gives `Δ (-log |α|²) ≥ (r / 2) (1 - |α|² - |β|²) - N / |α|²`, where `N` collects the error terms of
`∇_a α`, `∂bar_a α` and of the zeroth-order terms. -/
private theorem sub_sub_div_le_div_sub_div {a b da db q L G r C ε : ℝ} (hs : 0 < a ^ 2)
    (hW : -(C * a * (db + a + b)) ≤ -L / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2)
    (hG : 2 * a ^ 2 * ((1 - ε) * da ^ 2 - (2 + 18 / ε) * q ^ 2) ≤ G) :
    r / 2 * (1 - a ^ 2) - r / 2 * b ^ 2 -
        (2 * ε * da ^ 2 + 2 * (2 + 18 / ε) * q ^ 2 + 2 * C * a * (db + a + b)) / a ^ 2 ≤
      G / (a ^ 2) ^ 2 - L / a ^ 2 := by
  have hGs : 2 * ((1 - ε) * da ^ 2 - (2 + 18 / ε) * q ^ 2) / a ^ 2 ≤ G / (a ^ 2) ^ 2 := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  have hLs : (-(2 * C * a * (db + a + b)) - 2 * da ^ 2 -
      r / 2 * (a ^ 2 + b ^ 2 - 1) * a ^ 2) / a ^ 2 ≤ -L / a ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hs.le
  have hsplit : 2 * ((1 - ε) * da ^ 2 - (2 + 18 / ε) * q ^ 2) / a ^ 2 +
      (-(2 * C * a * (db + a + b)) - 2 * da ^ 2 - r / 2 * (a ^ 2 + b ^ 2 - 1) * a ^ 2) / a ^ 2 =
        r / 2 * (1 - a ^ 2) - r / 2 * b ^ 2 -
          (2 * ε * da ^ 2 + 2 * (2 + 18 / ε) * q ^ 2 + 2 * C * a * (db + a + b)) / a ^ 2 := by
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hs
    field_simp
    ring
  rw [neg_div] at hLs
  linarith

/-- The pointwise inequality behind the decay: at a point where `θ ≤ |α|²`, the projected
Weitzenböck equation for `α`, the gradient inequality of
`two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq` at `ε = θ / (8 C)` and Taubes's coarse bounds
give `Δ (-log |α|²) ≥ (θ r / 4) (-log |α|²) - 304 C² / θ²`. Here `a`, `b`, `da`, `db`, `q` stand
for `|α|`, `|β|`, `|∇_a α|`, `|∇β|`, `|∂bar_a α|`, and `L`, `G` for `Δ |α|²` and `|∇ |α|²|²`. -/
private theorem mul_neg_log_sub_le_div_sub_div {a b da db q L G r C θ : ℝ} (hr : 1 ≤ r)
    (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθa : θ ≤ a ^ 2)
    (hW : -(C * a * (db + a + b)) ≤ -L / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2)
    (hG : 2 * a ^ 2 * ((1 - θ / (8 * C)) * da ^ 2 - (2 + 18 / (θ / (8 * C))) * q ^ 2) ≤ G)
    (hβ : b ^ 2 ≤ C / r * max (1 - a ^ 2) 0 + C / r ^ 2)
    (hgrad : da ^ 2 + r * db ^ 2 ≤ C * r * max (1 - a ^ 2) 0 + C)
    (hup : a ^ 2 ≤ 1 + C / r) (hq : q ^ 2 ≤ C) :
    θ * r / 4 * -Real.log (a ^ 2) - 304 * C ^ 2 / θ ^ 2 ≤ G / (a ^ 2) ^ 2 - L / a ^ 2 := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have hC0 : 0 < C := one_pos.trans_le hC
  have hs : 0 < a ^ 2 := hθ.trans_le hθa
  obtain ⟨w, hw⟩ : ∃ w, w = max (1 - a ^ 2) 0 := ⟨_, rfl⟩
  rw [← hw] at hβ hgrad
  have hw0 : 0 ≤ w := hw ▸ le_max_right _ _
  have hw1 : w ≤ 1 := hw ▸ max_le (by nlinarith) zero_le_one
  obtain ⟨ε, hε⟩ : ∃ ε, ε = θ / (8 * C) := ⟨_, rfl⟩
  rw [← hε] at hG
  -- Coarse consequences: `|∇β|, |β| ≤ 2 C`, `(r / 2) |β|² ≤ C`, `|α| ≥ θ`.
  have hb2r := sq_le_two_mul_div hr hC0.le hw1 hβ
  have hb2 : r / 2 * b ^ 2 ≤ C := by
    calc r / 2 * b ^ 2 ≤ r / 2 * (2 * C / r) := by gcongr
      _ = C := by field_simp
  have hCrw : C * r * w ≤ C * r := by
    nlinarith [mul_le_mul_of_nonneg_left hw1 (mul_nonneg hC0.le hr0.le)]
  have hdb2 : db ^ 2 ≤ 2 * C :=
    le_of_mul_le_mul_left (show r * db ^ 2 ≤ r * (2 * C) by nlinarith [sq_nonneg da]) hr0
  have hdb := abs_le_two_mul_of_sq_le hC hdb2
  have hb := abs_le_two_mul_of_sq_le hC (hb2r.trans (div_le_self (by positivity) hr))
  have ha : θ ≤ |a| := (pow_le_pow_iff_left₀ hθ.le (abs_nonneg a) two_ne_zero).mp
    (by rw [sq_abs]; nlinarith)
  -- The three error terms, each at most `|α|²` times a constant.
  have hN₁ := two_mul_mul_sq_le hC0 hθ.le hε hθa hr0 hw0 (by nlinarith [sq_nonneg db] :
    da ^ 2 ≤ C * r * w + C)
  have hN₂ := two_mul_two_add_div_mul_sq_le hC hθ hθ1 hε hθa hq
  have hN₃ := two_mul_mul_add_add_le hC0 hθ ha hdb hb
  have hlog := mul_neg_log_sub_le hr0 hC0.le hθ hθa hw hup
  have hdiv := sub_sub_div_le_div_sub_div hs hW hG
  have hNs : (2 * ε * da ^ 2 + 2 * (2 + 18 / ε) * q ^ 2 + 2 * C * a * (db + a + b)) / a ^ 2 ≤
      (r * w + 1) / 4 + 292 * C ^ 2 / θ ^ 2 + (2 * C + 8 * C ^ 2 / θ) := by
    rw [div_le_iff₀ hs]
    linarith
  have hconst := const_le hC hθ hθ1
  linarith

/-- **Exponential decay of the vacuum defect where `|α|` is bounded below.** Consider, on the
closed ball of radius `R` about `z` in a finite-dimensional real inner product space,
functions `a`, `b`, `da`, `db`, `q` standing for `|α|`, `|β|`, `|∇_a α|`, `|∇β|`, `|∂bar_a α|` of
a solution of Taubes's large-parameter Seiberg–Witten equations at parameter `r ≥ 1`, with `|α|²`
of class `C²`.
Assume, with a constant `C ≥ 1`,

* the projected Weitzenböck equation for `α`, in the direction
  `-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≥ -C |α| (|∇β| + |α| + |β|)`;
* the gradient inequality `2 |α|² ((1 - ε) |∇_a α|² - (2 + 18 / ε) |∂bar_a α|²) ≤ |∇ |α|²|²` at
  `ε = θ / (8 C)`, which `two_mul_norm_sq_mul_sub_le_norm_gradient_norm_sq` supplies;
* Taubes's coarse bounds `|β|² ≤ (C / r) w₊ + C / r²`, `|∇_a α|² + r |∇β|² ≤ C r w₊ + C`,
  `|α|² ≤ 1 + C / r` and `|∂bar_a α|² ≤ C`, with `w₊ = max (1 - |α|²) 0`.

If `|α|² ≥ θ` on the whole ball, `0 < θ ≤ 1`, then at its centre

`1 - |α(z)|² ≤ 1216 C² / (θ³ r) + 2 log θ⁻¹ e^{2n/3} exp (-√(θ r) R / 4)`,  `n = dim E`.

So, with the length scale `h = (2 r)^(-1/2)`, the vacuum defect is `O(1 / r)` up to an error
`exp (-c R / h)`, with `c = √θ / (4 √2)`, on balls of radius `R` where `|α|` stays bounded below.
-/
theorem one_sub_sq_le_div_add_mul_exp [Nontrivial E] {a b da db q : E → ℝ} {z : E} {r R C θ : ℝ}
    (hr : 1 ≤ r) (hR : 0 ≤ R) (hC : 1 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hcont : ContinuousOn (fun y ↦ a y ^ 2) (closedBall z R))
    (hcd : ∀ x ∈ ball z R, ContDiffAt ℝ 2 (fun y ↦ a y ^ 2) x)
    (hθa : ∀ x ∈ closedBall z R, θ ≤ a x ^ 2)
    (hW : ∀ x ∈ ball z R, -(C * a x * (db x + a x + b x)) ≤
      -Δ (fun y ↦ a y ^ 2) x / 2 + da x ^ 2 + r / 4 * (a x ^ 2 + b x ^ 2 - 1) * a x ^ 2)
    (hG : ∀ x ∈ ball z R, 2 * a x ^ 2 * ((1 - θ / (8 * C)) * da x ^ 2 -
      (2 + 18 / (θ / (8 * C))) * q x ^ 2) ≤ ‖∇ (fun y ↦ a y ^ 2) x‖ ^ 2)
    (hβ : ∀ x ∈ ball z R, b x ^ 2 ≤ C / r * max (1 - a x ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ x ∈ ball z R, da x ^ 2 + r * db x ^ 2 ≤ C * r * max (1 - a x ^ 2) 0 + C)
    (hup : ∀ x ∈ ball z R, a x ^ 2 ≤ 1 + C / r) (hq : ∀ x ∈ ball z R, q x ^ 2 ≤ C) :
    1 - a z ^ 2 ≤ 1216 * C ^ 2 / (θ ^ 3 * r) +
      2 * Real.log θ⁻¹ * Real.exp (2 * Module.finrank ℝ E / 3) *
        Real.exp (-(√(θ * r) * R / 4)) := by
  have hpos : ∀ x ∈ closedBall z R, 0 < a x ^ 2 := fun x hx ↦ hθ.trans_le (hθa x hx)
  set u : E → ℝ := fun y ↦ -Real.log (a y ^ 2) with hu
  -- `u = -log |α|²` is a subsolution of `-Δ + θ r / 4` with forcing `304 C² / θ²`.
  set c := √(θ * r) / 2 with hc
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = θ * r / 4 := by
    rw [hc, div_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsub : ∀ x ∈ ball z R, (fun _ ↦ θ * r / 4) x * u x - 304 * C ^ 2 / θ ^ 2 ≤ Δ u x := by
    intro x hx
    have hΔ := (hcd x hx).laplacian_log (hpos x (ball_subset_closedBall hx)).ne'
    rw [hu, ← Pi.neg_def, laplacian_neg]
    simp only [Pi.neg_apply, hΔ, neg_sub]
    exact mul_neg_log_sub_le_div_sub_div hr hC hθ hθ1 (hθa x (ball_subset_closedBall hx)) (hW x hx)
      (hG x hx) (hβ x hx) (hgrad x hx) (hup x hx) (hq x hx)
  have hbdry : ∀ x ∈ sphere z R, u x ≤ Real.log θ⁻¹ := by
    intro x hx
    rw [hu, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log hθ (hθa x (sphere_subset_closedBall hx))
  have hucont : ContinuousOn u (closedBall z R) :=
    (hcont.log fun x hx ↦ (hpos x hx).ne').neg
  have hucd : ∀ x ∈ ball z R, ContDiffAt ℝ 2 u x := fun x hx ↦
    ((hcd x hx).log (hpos x (ball_subset_closedBall hx)).ne').neg
  have hdecay := le_div_sq_add_two_mul_mul_exp_of_mul_sub_le_laplacian hR
    (by positivity : (0 : ℝ) ≤ c / 2) (by linarith : c / 2 < c)
    (Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hθ, hθ1⟩)) (by positivity) hucont hucd
    (fun _ _ ↦ hc2.le) hsub hbdry
  -- `1 - |α|² ≤ -log |α|²`.
  have hz := hpos z (mem_closedBall_self hR)
  have hlog : 1 - a z ^ 2 ≤ u z := by
    have := Real.log_le_sub_one_of_pos hz
    simp only [hu]
    linarith
  -- Simplify the constants of the decay estimate.
  have hB : 304 * C ^ 2 / θ ^ 2 / c ^ 2 = 1216 * C ^ 2 / (θ ^ 3 * r) := by
    rw [hc2]
    field_simp
    ring
  have hexp : -(c / 2 * (R - Module.finrank ℝ E * c / (c ^ 2 - (c / 2) ^ 2))) =
      2 * Module.finrank ℝ E / 3 + -(√(θ * r) * R / 4) := by
    rw [hc]
    field_simp
    ring
  rw [hB, hexp, Real.exp_add] at hdecay
  linarith [mul_assoc (2 * Real.log θ⁻¹) (Real.exp (2 * Module.finrank ℝ E / 3))
    (Real.exp (-(√(θ * r) * R / 4)))]

end TauCeti.SeibergWitten
