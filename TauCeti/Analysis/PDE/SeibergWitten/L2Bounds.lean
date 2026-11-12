/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# `L²` bounds on `β` and `∂bar_a α` at large parameter

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `ψ = α u₀ + β`. The component `β` satisfies a
projected Weitzenböck equation `∇*∇β + (r / 4) (|α|² + |β|² + 1) β = 𝔟`, where the error `𝔟` is
bounded by `c (|∇_a α| + |α| + |β|)` with a constant `c` independent of `r`. Pairing with `β` and
writing `Δ = div ∘ grad`, so that `⟪∇*∇β, β⟫ = |∇β|² - Δ|β|² / 2`, gives the scalar inequality

`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.

On a closed manifold `Δ|β|²` integrates to zero, and integrating this inequality gives Taubes's
`L²` bound on `β` (`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le`): for
`r ≥ 8 c`,

`‖∇β‖₂² + (r / 16) ‖β‖₂² ≤ (8 c² / r) (‖∇_a α‖₂² + ‖α‖₂²)`,

that is `‖∇β‖₂ + √r ‖β‖₂ ≤ 16 c r^(-1/2) (‖∇_a α‖₂ + ‖α‖₂)`
(`TauCeti.SeibergWitten.sqrt_integral_norm_sq_add_sqrt_mul_sqrt_integral_norm_sq_le`).

Taubes's canonical connection `A₀` satisfies `D_{A₀} u₀ = 0`, so the Dirac equation `D_A ψ = 0`
reads `√2 ∂bar_a α = -D_A β` and bounds `∂bar_a α` pointwise by `c (|∇β| + |β|)`. Since
`|∇_a α|² = |∂_a α|² + |∂bar_a α|²`, the `β` bound then gives Taubes's `L²` bound on `∂bar_a α`
in terms of `∂_a α`
(`TauCeti.SeibergWitten.integral_norm_sq_le_of_norm_le_mul_add_norm`): for `r ≥ 16` and
`r ≥ 32 c⁴`,

`‖∂bar_a α‖₂² ≤ (32 c⁴ / r) (‖∂_a α‖₂² + ‖α‖₂²)`,

so `‖∂bar_a α‖₂ ≤ 6 c² r^(-1/2) (‖∂_a α‖₂ + ‖α‖₂)`
(`TauCeti.SeibergWitten.sqrt_integral_norm_sq_le_of_norm_le_mul_add_norm`). When `‖α‖₂ ≤ K`, for
instance under the pointwise bound `|α|² ≤ 1 + C / r` on a space of finite volume, this is the
estimate `‖∂bar_a α‖₂ ≤ C' r^(-1/2) (‖∂_a α‖₂ + 1)` with `C' = 6 c² max 1 K`, which
`TauCeti.SeibergWitten.integral_norm_sq_le_div` takes as a hypothesis.

The measure-space statements take the fields as functions on an arbitrary measure space with
values in arbitrary normed groups, and the function `g` standing for `Δ|β|²` as an integrable
function of integral zero, so they apply on any domain where that integral vanishes. On a closed
Riemannian manifold this is the divergence theorem, and
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami` states the
`β` bound with the Laplace–Beltrami operator itself.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210, Section 2.
-/

public section

open MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti.SeibergWitten

variable {X A B F₁ F₂ F₃ F₄ : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
  [NormedAddCommGroup F₃] [NormedAddCommGroup F₄] {α : X → A} {β : X → B} {Dα : X → F₁}
  {Dβ : X → F₂} {c r : ℝ}

/-- The pointwise form of the `β` bound: the cross term of the projected Weitzenböck inequality
is split between the potential and the derivative of `α`. Here `a`, `b`, `da`, `db` stand for the
values of `|α|`, `|β|`, `|∇_a α|`, `|∇β|`, and `g` for that of `Δ|β|²`. -/
private theorem neg_div_two_add_sq_add_mul_sq_le {a b da db g : ℝ} (hr : 0 < r)
    (hcr : 8 * c ≤ r)
    (hW : -g / 2 + db ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (da + a + b)) :
    -g / 2 + db ^ 2 + r / 16 * b ^ 2 ≤ 8 * c ^ 2 / r * (da ^ 2 + a ^ 2) := by
  have hpot : r / 4 * b ^ 2 ≤ r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 := by
    have : b ^ 2 ≤ (a ^ 2 + b ^ 2 + 1) * b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    nlinarith
  -- `c b s ≤ (r / 16) b² + (4 c² / r) s²`, from `(r b / 4 - 2 c s)² ≥ 0`.
  have hcross : c * b * (da + a) ≤ r / 16 * b ^ 2 + 4 * c ^ 2 / r * (da + a) ^ 2 := by
    have hsq : r / 16 * b ^ 2 + 4 * c ^ 2 / r * (da + a) ^ 2 - c * b * (da + a) =
        (r * b / 4 - 2 * c * (da + a)) ^ 2 / r := by
      field_simp
      ring
    have : 0 ≤ (r * b / 4 - 2 * c * (da + a)) ^ 2 / r := by positivity
    linarith
  have hsum : (da + a) ^ 2 ≤ 2 * (da ^ 2 + a ^ 2) := by nlinarith [sq_nonneg (da - a)]
  have hcsq : 4 * c ^ 2 / r * (da + a) ^ 2 ≤ 8 * c ^ 2 / r * (da ^ 2 + a ^ 2) := by
    have h4 : 0 ≤ 4 * c ^ 2 / r := by positivity
    calc 4 * c ^ 2 / r * (da + a) ^ 2 ≤ 4 * c ^ 2 / r * (2 * (da ^ 2 + a ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum h4
      _ = 8 * c ^ 2 / r * (da ^ 2 + a ^ 2) := by ring
  have hbb : c * b * b ≤ r / 8 * b ^ 2 := by nlinarith [sq_nonneg b]
  nlinarith

/-- **Taubes's `L²` bound on `β`.** Let `g` be an integrable function of integral zero, standing
for `Δ|β|²`, and suppose the projected Weitzenböck inequality
`-g / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)` holds almost
everywhere, with `8 c ≤ r`. Then
`∫ |∇β|² + (r / 16) ∫ |β|² ≤ (8 c² / r) (∫ |∇_a α|² + ∫ |α|²)`. Here `∇_a α` and `∇β` are any
functions `Dα` and `Dβ` satisfying these hypotheses. -/
theorem integral_norm_sq_add_mul_integral_norm_sq_le {g : X → ℝ} (hr : 0 < r)
    (hcr : 8 * c ≤ r) (hg : Integrable g μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hDα : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ) (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ)
    (hW : ∀ᵐ x ∂μ, -g x / 2 + ‖Dβ x‖ ^ 2 + r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ) := by
  have hg' : Integrable (fun x ↦ -g x / 2) μ := hg.neg.div_const 2
  have hL : Integrable (fun x ↦ -g x / 2 + ‖Dβ x‖ ^ 2 + r / 16 * ‖β x‖ ^ 2) μ :=
    (hg'.add hDβ).add (hβ.const_mul _)
  have hR : Integrable (fun x ↦ 8 * c ^ 2 / r * (‖Dα x‖ ^ 2 + ‖α x‖ ^ 2)) μ :=
    (hDα.add hα).const_mul _
  have hint := integral_mono_ae hL hR <| by
    filter_upwards [hW] with x hx
    exact neg_div_two_add_sq_add_mul_sq_le hr hcr hx
  have hsplitL : ∫ x, (-g x / 2 + ‖Dβ x‖ ^ 2 + r / 16 * ‖β x‖ ^ 2) ∂μ =
      ∫ x, (-g x / 2 + ‖Dβ x‖ ^ 2) ∂μ + ∫ x, r / 16 * ‖β x‖ ^ 2 ∂μ :=
    integral_add (hg'.add hDβ) (hβ.const_mul _)
  have hsplitL' : ∫ x, (-g x / 2 + ‖Dβ x‖ ^ 2) ∂μ = ∫ x, -g x / 2 ∂μ + ∫ x, ‖Dβ x‖ ^ 2 ∂μ :=
    integral_add hg' hDβ
  have hsplitR : ∫ x, (‖Dα x‖ ^ 2 + ‖α x‖ ^ 2) ∂μ = ∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ :=
    integral_add hDα hα
  rw [hsplitL, hsplitL', integral_div, integral_neg, hg0, integral_const_mul, integral_const_mul,
    hsplitR] at hint
  linarith

/-- **Taubes's `L²` bound on `β`, in norm form.** Under the hypotheses of
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le`,
`‖∇β‖₂ + √r ‖β‖₂ ≤ 16 c r^(-1/2) (‖∇_a α‖₂ + ‖α‖₂)`, with `L²` norms written `√(∫ |f|²)`. -/
theorem sqrt_integral_norm_sq_add_sqrt_mul_sqrt_integral_norm_sq_le {g : X → ℝ} (hr : 0 < r)
    (hc : 0 ≤ c) (hcr : 8 * c ≤ r) (hg : Integrable g μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hDα : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ) (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ)
    (hW : ∀ᵐ x ∂μ, -g x / 2 + ‖Dβ x‖ ^ 2 + r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    √(∫ x, ‖Dβ x‖ ^ 2 ∂μ) + √r * √(∫ x, ‖β x‖ ^ 2 ∂μ) ≤
      16 * c / √r * (√(∫ x, ‖Dα x‖ ^ 2 ∂μ) + √(∫ x, ‖α x‖ ^ 2 ∂μ)) := by
  have hbound := integral_norm_sq_add_mul_integral_norm_sq_le hr hcr hg hg0 hα hβ hDα hDβ hW
  set P := ∫ x, ‖Dβ x‖ ^ 2 ∂μ
  set Q := ∫ x, ‖β x‖ ^ 2 ∂μ
  set T₁ := ∫ x, ‖Dα x‖ ^ 2 ∂μ
  set T₂ := ∫ x, ‖α x‖ ^ 2 ∂μ
  have hP : 0 ≤ P := integral_nonneg fun x ↦ by positivity
  have hQ : 0 ≤ Q := integral_nonneg fun x ↦ by positivity
  have hT₁ : 0 ≤ T₁ := integral_nonneg fun x ↦ by positivity
  have hT₂ : 0 ≤ T₂ := integral_nonneg fun x ↦ by positivity
  have hsr := Real.sq_sqrt hr.le
  have hsP := Real.sq_sqrt hP
  have hsQ := Real.sq_sqrt hQ
  have hsT₁ := Real.sq_sqrt hT₁
  have hsT₂ := Real.sq_sqrt hT₂
  have hrpos : 0 < √r := Real.sqrt_pos.2 hr
  -- Square both sides: `(√P + √r √Q)² ≤ 2 (P + r Q) ≤ 256 c² (T₁ + T₂) / r`.
  have hPQ : P + r * Q ≤ 128 * c ^ 2 / r * (T₁ + T₂) := by
    have : P ≤ 16 * P := by linarith
    have h16 : P + r * Q ≤ 16 * (P + r / 16 * Q) := by nlinarith
    calc P + r * Q ≤ 16 * (P + r / 16 * Q) := h16
      _ ≤ 16 * (8 * c ^ 2 / r * (T₁ + T₂)) := by gcongr
      _ = 128 * c ^ 2 / r * (T₁ + T₂) := by ring
  have hT : T₁ + T₂ ≤ (√T₁ + √T₂) ^ 2 := by nlinarith [Real.sqrt_nonneg T₁, Real.sqrt_nonneg T₂]
  have hrhs : 0 ≤ 16 * c / √r * (√T₁ + √T₂) := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) hrhs two_ne_zero).1 ?_
  have hlhs : (√P + √r * √Q) ^ 2 ≤ 2 * (P + r * Q) := by
    nlinarith [sq_nonneg (√P - √r * √Q)]
  have hmain : 2 * (P + r * Q) ≤ (16 * c / √r * (√T₁ + √T₂)) ^ 2 := by
    rw [mul_pow, div_pow, hsr]
    calc 2 * (P + r * Q) ≤ 2 * (128 * c ^ 2 / r * (T₁ + T₂)) := by gcongr
      _ = 16 ^ 2 * c ^ 2 / r * (T₁ + T₂) := by ring
      _ ≤ 16 ^ 2 * c ^ 2 / r * (√T₁ + √T₂) ^ 2 := by gcongr
      _ = (16 * c) ^ 2 / r * (√T₁ + √T₂) ^ 2 := by ring
  exact hlhs.trans hmain

/-- **Taubes's `L²` bound on `∂bar_a α`.** Suppose the `L²` bound on `β` of
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le` holds, the covariant
derivative splits as `|∇_a α|² ≤ |∂_a α|² + |∂bar_a α|²`, and the Dirac equation gives
`|∂bar_a α| ≤ c (|∇β| + |β|)`. If `16 ≤ r` and `32 c⁴ ≤ r`, then
`∫ |∂bar_a α|² ≤ (32 c⁴ / r) (∫ |∂_a α|² + ∫ |α|²)`. Here `∇_a α`, `∇β`, `∂_a α` and `∂bar_a α`
are any functions `Dα`, `Dβ`, `Dα'` and `Dbar` satisfying these hypotheses. -/
theorem integral_norm_sq_le_of_norm_le_mul_add_norm {Dα' : X → F₃} {Dbar : X → F₄}
    (hr16 : 16 ≤ r) (hcr : 32 * c ^ 4 ≤ r) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hDα : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ) (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ)
    (hDα' : Integrable (fun x ↦ ‖Dα' x‖ ^ 2) μ) (hDbar : Integrable (fun x ↦ ‖Dbar x‖ ^ 2) μ)
    (hbound : ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ))
    (hsplit : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 ≤ ‖Dα' x‖ ^ 2 + ‖Dbar x‖ ^ 2)
    (hdirac : ∀ᵐ x ∂μ, ‖Dbar x‖ ≤ c * (‖Dβ x‖ + ‖β x‖)) :
    ∫ x, ‖Dbar x‖ ^ 2 ∂μ ≤ 32 * c ^ 4 / r * (∫ x, ‖Dα' x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ) := by
  have hr : 0 < r := by linarith
  set P := ∫ x, ‖Dβ x‖ ^ 2 ∂μ
  set Q := ∫ x, ‖β x‖ ^ 2 ∂μ
  set T₁ := ∫ x, ‖Dα x‖ ^ 2 ∂μ
  set T₂ := ∫ x, ‖α x‖ ^ 2 ∂μ
  set T' := ∫ x, ‖Dα' x‖ ^ 2 ∂μ
  set Z := ∫ x, ‖Dbar x‖ ^ 2 ∂μ
  have hQ : 0 ≤ Q := integral_nonneg fun x ↦ by positivity
  have hZ : 0 ≤ Z := integral_nonneg fun x ↦ by positivity
  -- Integrate the splitting of `∇_a α` and the square of the Dirac bound.
  have hT₁ : T₁ ≤ T' + Z := by
    rw [← integral_add hDα' hDbar]
    exact integral_mono_ae hDα (hDα'.add hDbar) hsplit
  have hZPQ : Z ≤ 2 * c ^ 2 * (P + Q) := by
    rw [← integral_add hDβ hβ, ← integral_const_mul]
    refine integral_mono_ae hDbar ((hDβ.add hβ).const_mul _) ?_
    filter_upwards [hdirac] with x hx
    have h0 : 0 ≤ ‖Dbar x‖ := norm_nonneg _
    have hsq : ‖Dbar x‖ ^ 2 ≤ (c * (‖Dβ x‖ + ‖β x‖)) ^ 2 := pow_le_pow_left₀ h0 hx 2
    nlinarith [sq_nonneg (‖Dβ x‖ - ‖β x‖)]
  -- Since `r ≥ 16`, the `β` bound controls `P + Q`.
  have hPQ : P + Q ≤ 8 * c ^ 2 / r * (T₁ + T₂) := by
    have : Q ≤ r / 16 * Q := by nlinarith
    linarith
  have hK : 16 * c ^ 4 / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]
    linarith
  have hK0 : 0 ≤ 16 * c ^ 4 / r := by positivity
  have hc2 : 0 ≤ 2 * c ^ 2 := by positivity
  -- `Z ≤ (16 c⁴ / r) (T' + T₂) + (16 c⁴ / r) Z`, and the last term is absorbed.
  have hZ' : Z ≤ 16 * c ^ 4 / r * (T' + T₂) + 16 * c ^ 4 / r * Z := by
    calc Z ≤ 2 * c ^ 2 * (P + Q) := hZPQ
      _ ≤ 2 * c ^ 2 * (8 * c ^ 2 / r * (T₁ + T₂)) := mul_le_mul_of_nonneg_left hPQ hc2
      _ ≤ 2 * c ^ 2 * (8 * c ^ 2 / r * (T' + Z + T₂)) := by
          have : 0 ≤ 8 * c ^ 2 / r := by positivity
          gcongr
      _ = 16 * c ^ 4 / r * (T' + T₂) + 16 * c ^ 4 / r * Z := by ring
  have hKZ : 16 * c ^ 4 / r * Z ≤ Z / 2 := by nlinarith
  have : 32 * c ^ 4 / r * (T' + T₂) = 2 * (16 * c ^ 4 / r * (T' + T₂)) := by ring
  linarith

/-- **Taubes's `L²` bound on `∂bar_a α`, in norm form.** Under the hypotheses of
`TauCeti.SeibergWitten.integral_norm_sq_le_of_norm_le_mul_add_norm`,
`‖∂bar_a α‖₂ ≤ 6 c² r^(-1/2) (‖∂_a α‖₂ + ‖α‖₂)`, with `L²` norms written `√(∫ |f|²)`. -/
theorem sqrt_integral_norm_sq_le_of_norm_le_mul_add_norm {Dα' : X → F₃} {Dbar : X → F₄}
    (hr16 : 16 ≤ r) (hcr : 32 * c ^ 4 ≤ r) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hDα : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ) (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ)
    (hDα' : Integrable (fun x ↦ ‖Dα' x‖ ^ 2) μ) (hDbar : Integrable (fun x ↦ ‖Dbar x‖ ^ 2) μ)
    (hbound : ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ))
    (hsplit : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 ≤ ‖Dα' x‖ ^ 2 + ‖Dbar x‖ ^ 2)
    (hdirac : ∀ᵐ x ∂μ, ‖Dbar x‖ ≤ c * (‖Dβ x‖ + ‖β x‖)) :
    √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ≤
      6 * c ^ 2 / √r * (√(∫ x, ‖Dα' x‖ ^ 2 ∂μ) + √(∫ x, ‖α x‖ ^ 2 ∂μ)) := by
  have hZ := integral_norm_sq_le_of_norm_le_mul_add_norm hr16 hcr hβ hDα hDβ hDα' hDbar
    hbound hsplit hdirac
  have hr : 0 < r := by linarith
  set Z := ∫ x, ‖Dbar x‖ ^ 2 ∂μ
  set T' := ∫ x, ‖Dα' x‖ ^ 2 ∂μ
  set T₂ := ∫ x, ‖α x‖ ^ 2 ∂μ
  have hZ0 : 0 ≤ Z := integral_nonneg fun x ↦ by positivity
  have hT' : 0 ≤ T' := integral_nonneg fun x ↦ by positivity
  have hT₂ : 0 ≤ T₂ := integral_nonneg fun x ↦ by positivity
  have hsT' := Real.sq_sqrt hT'
  have hsT₂ := Real.sq_sqrt hT₂
  have hrhs : 0 ≤ 6 * c ^ 2 / √r * (√T' + √T₂) := by positivity
  refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) hrhs two_ne_zero).1 ?_
  have hT : T' + T₂ ≤ (√T' + √T₂) ^ 2 := by nlinarith [Real.sqrt_nonneg T', Real.sqrt_nonneg T₂]
  rw [Real.sq_sqrt hZ0, mul_pow, div_pow, Real.sq_sqrt hr.le]
  calc Z ≤ 32 * c ^ 4 / r * (T' + T₂) := hZ
    _ ≤ 36 * c ^ 4 / r * (T' + T₂) := by
        gcongr
        linarith [pow_nonneg (sq_nonneg c) 2, show c ^ 4 = (c ^ 2) ^ 2 by ring]
    _ ≤ 36 * c ^ 4 / r * (√T' + √T₂) ^ 2 := by gcongr
    _ = (6 * c ^ 2) ^ 2 / r * (√T' + √T₂) ^ 2 := by ring

section Manifold

open Bundle TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Taubes's `L²` bound on `β` on a closed manifold.** On a compact Riemannian manifold without
boundary, let `α`, `β`, `∇_a α`, `∇β` be continuous fields with `|β|²` of class `C²`, satisfying the
projected Weitzenböck inequality
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)` with the
Laplace–Beltrami operator `Δ = div ∘ grad`. If `8 c ≤ r`, then
`∫ |∇β|² + (r / 16) ∫ |β|² ≤ (8 c² / r) (∫ |∇_a α|² + ∫ |α|²)` for the Riemannian volume. -/
theorem integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami
    {α : M → A} {β : M → B} {Dα : M → F₁} {Dβ : M → F₂} (hr : 0 < r) (hcr : 8 * c ≤ r)
    (hα : Continuous α) (hβ : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ‖β x‖ ^ 2))
    (hDα : Continuous Dα) (hDβ : Continuous Dβ)
    (hW : ∀ x, -laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    ∫ x, ‖Dβ x‖ ^ 2 ∂riemannianVolume I M +
        r / 16 * ∫ x, ‖β x‖ ^ 2 ∂riemannianVolume I M ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖α x‖ ^ 2 ∂riemannianVolume I M) := by
  have hcpt (f : M → ℝ) (hf : Continuous f) : Integrable f (riemannianVolume I M) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  exact integral_norm_sq_add_mul_integral_norm_sq_le hr hcr
    (hcpt _ (continuous_laplaceBeltrami hβ))
    (integral_laplaceBeltrami_eq_zero hβ (HasCompactSupport.of_compactSpace _))
    (hcpt _ (hα.norm.pow 2)) (hcpt _ hβ.continuous) (hcpt _ (hDα.norm.pow 2))
    (hcpt _ (hDβ.norm.pow 2)) (Filter.Eventually.of_forall hW)

end Manifold

end TauCeti.SeibergWitten
