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
`0 < r` with `r ≥ 8 c`,

`‖∇β‖₂² + (r / 16) ‖β‖₂² ≤ (8 c² / r) (‖∇_a α‖₂² + ‖α‖₂²)`,

so, for `c ≥ 0`, `‖∇β‖₂ + √r ‖β‖₂ ≤ 16 c r^(-1/2) (‖∇_a α‖₂ + ‖α‖₂)`
(`TauCeti.SeibergWitten.sqrt_integral_norm_sq_add_sqrt_mul_sqrt_integral_norm_sq_le`).

Taubes's canonical connection `A₀` satisfies `D_{A₀} u₀ = 0`, so the Dirac equation `D_A ψ = 0`
reads `√2 ∂bar_a α = -D_A β` and bounds `∂bar_a α` pointwise by `c (|∇β| + |β|)`. Since
`∇_a α = ∂_a α + ∂bar_a α` gives `|∇_a α| ≤ |∂_a α| + |∂bar_a α|`, the `β` bound then gives
Taubes's `L²` bound on `∂bar_a α` in terms of `∂_a α`
(`TauCeti.SeibergWitten.integral_norm_sq_le_of_norm_le_mul_add_norm`): for `r ≥ 16` and
`r ≥ 64 c⁴`,

`‖∂bar_a α‖₂² ≤ (64 c⁴ / r) (‖∂_a α‖₂² + ‖α‖₂²)`,

so `‖∂bar_a α‖₂ ≤ 8 c² r^(-1/2) (‖∂_a α‖₂ + ‖α‖₂)`
(`TauCeti.SeibergWitten.sqrt_integral_norm_sq_le_of_norm_le_mul_add_norm`). When `‖α‖₂ ≤ K`, for
instance under the pointwise bound `|α|² ≤ 1 + C / r` on a space of finite volume, this is the
estimate `‖∂bar_a α‖₂ ≤ C' r^(-1/2) (‖∂_a α‖₂ + 1)` with `C' = 8 c² max 1 K`, which
`TauCeti.SeibergWitten.integral_norm_sq_le_div` takes as a hypothesis.

Only the pointwise norms of the fields enter, so every statement takes the fields as sections of
arbitrary families of seminormed groups, such as the fibres of a vector bundle. The measure-space
statements work over an arbitrary measure space and take the function `g` standing for `Δ|β|²` as
an integrable function of integral zero, so they apply on any domain where that integral vanishes.
On a closed Riemannian manifold this is the divergence theorem, and
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami` states the
`β` bound with the Laplace–Beltrami operator itself, for sections with `|β|²` of class `C²` and
`|α|²` and `|∇_a α|²` continuous. The norm forms take the integrated `β` bound as a hypothesis,
so they apply to both.

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

variable {c r : ℝ}

section MeasureSpace

variable {X : Type*} {A B F₁ F₂ F₃ F₄ : X → Type*} [MeasurableSpace X] {μ : Measure X}
  [∀ x, SeminormedAddCommGroup (A x)] [∀ x, SeminormedAddCommGroup (B x)]
  [∀ x, SeminormedAddCommGroup (F₁ x)] [∀ x, SeminormedAddCommGroup (F₂ x)]
  [∀ x, SeminormedAddCommGroup (F₃ x)] [∀ x, SeminormedAddCommGroup (F₄ x)]
  {α : (x : X) → A x} {β : (x : X) → B x} {Dα : (x : X) → F₁ x} {Dβ : (x : X) → F₂ x}

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
everywhere, with `0 < r` and `8 c ≤ r`. Then
`∫ |∇β|² + (r / 16) ∫ |β|² ≤ (8 c² / r) (∫ |∇_a α|² + ∫ |α|²)`. Here `∇_a α` and `∇β` are any
functions `Dα` and `Dβ` satisfying these hypotheses. -/
theorem integral_norm_sq_add_mul_integral_norm_sq_le {g : X → ℝ} (hr : 0 < r)
    (hcr : 8 * c ≤ r) (hg : Integrable g μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ) (hDα : Integrable (fun x ↦ ‖Dα x‖ ^ 2) μ)
    (hW : ∀ᵐ x ∂μ, -g x / 2 + ‖Dβ x‖ ^ 2 + r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ) := by
  -- Both terms on the left are bounded by an integrable majorant `G`, which integrates to the
  -- right-hand side because `g` has integral zero.
  have hg' : Integrable (fun x ↦ g x / 2) μ := hg.div_const 2
  have hR : Integrable (fun x ↦ 8 * c ^ 2 / r * (‖Dα x‖ ^ 2 + ‖α x‖ ^ 2)) μ :=
    (hDα.add hα).const_mul _
  set G := fun x ↦ g x / 2 + 8 * c ^ 2 / r * (‖Dα x‖ ^ 2 + ‖α x‖ ^ 2) with hGdef
  have hG : Integrable G μ := hg'.add hR
  have hGint : ∫ x, G x ∂μ = 8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ) := by
    simp only [hGdef, integral_add hg' hR, integral_add hDα hα, integral_const_mul, integral_div,
      hg0, zero_div, zero_add]
  have hFG : ∀ᵐ x ∂μ, ‖Dβ x‖ ^ 2 + r / 16 * ‖β x‖ ^ 2 ≤ G x := by
    filter_upwards [hW] with x hx
    have := neg_div_two_add_sq_add_mul_sq_le hr hcr hx
    rw [hGdef]
    linarith
  have hr16 : 0 ≤ r / 16 := by positivity
  have hDβG : ∫ x, ‖Dβ x‖ ^ 2 ∂μ ≤ ∫ x, G x ∂μ := by
    refine integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) hG ?_
    filter_upwards [hFG] with x hx
    nlinarith [sq_nonneg ‖β x‖, hr16]
  have hβG : ∫ x, r / 16 * ‖β x‖ ^ 2 ∂μ ≤ ∫ x, G x ∂μ := by
    refine integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) hG ?_
    filter_upwards [hFG] with x hx
    nlinarith [sq_nonneg ‖Dβ x‖, hr16]
  rw [← hGint, ← integral_const_mul]
  by_cases hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ
  · by_cases hβ : Integrable (fun x ↦ r / 16 * ‖β x‖ ^ 2) μ
    · rw [← integral_add hDβ hβ]
      exact integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) hG hFG
    · rw [integral_undef hβ, add_zero]
      exact hDβG
  · rw [integral_undef hDβ, zero_add]
    exact hβG

/-- Taking square roots in an `L²` bound: if `Z ≤ (K² / r) (T + T')`, then
`√Z ≤ K r^(-1/2) (√T + √T')`. -/
private theorem sqrt_le_div_sqrt_mul_add_sqrt {Z T T' K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hT' : 0 ≤ T') (hZ : Z ≤ K ^ 2 / r * (T + T')) :
    √Z ≤ K / √r * (√T + √T') := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, div_pow, Real.sq_sqrt hr.le]
  have hsum : T + T' ≤ (√T + √T') ^ 2 := by
    nlinarith [Real.sqrt_nonneg T, Real.sqrt_nonneg T', Real.sq_sqrt hT, Real.sq_sqrt hT']
  calc Z ≤ K ^ 2 / r * (T + T') := hZ
    _ ≤ K ^ 2 / r * (√T + √T') ^ 2 := by gcongr

/-- **Taubes's `L²` bound on `β`, in norm form.** Let `0 < r` and `0 ≤ c`. If the integrated
`β` bound `∫ |∇β|² + (r / 16) ∫ |β|² ≤ (8 c² / r) (∫ |∇_a α|² + ∫ |α|²)` holds, as given by
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le` or
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami`, then
`‖∇β‖₂ + √r ‖β‖₂ ≤ 16 c r^(-1/2) (‖∇_a α‖₂ + ‖α‖₂)`, with `L²` norms written `√(∫ |f|²)`. -/
theorem sqrt_integral_norm_sq_add_sqrt_mul_sqrt_integral_norm_sq_le (hr : 0 < r) (hc : 0 ≤ c)
    (hbound : ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ)) :
    √(∫ x, ‖Dβ x‖ ^ 2 ∂μ) + √r * √(∫ x, ‖β x‖ ^ 2 ∂μ) ≤
      16 * c / √r * (√(∫ x, ‖Dα x‖ ^ 2 ∂μ) + √(∫ x, ‖α x‖ ^ 2 ∂μ)) := by
  set P := ∫ x, ‖Dβ x‖ ^ 2 ∂μ
  set Q := ∫ x, ‖β x‖ ^ 2 ∂μ
  set T₁ := ∫ x, ‖Dα x‖ ^ 2 ∂μ
  set T₂ := ∫ x, ‖α x‖ ^ 2 ∂μ
  have hP : 0 ≤ P := integral_nonneg fun x ↦ by positivity
  have hQ : 0 ≤ Q := integral_nonneg fun x ↦ by positivity
  have hT₁ : 0 ≤ T₁ := integral_nonneg fun x ↦ by positivity
  have hT₂ : 0 ≤ T₂ := integral_nonneg fun x ↦ by positivity
  -- `(√P + √r √Q)² ≤ 2 (P + r Q) ≤ 256 c² (T₁ + T₂) / r`.
  have hPQ : P + r * Q ≤ 128 * c ^ 2 / r * (T₁ + T₂) := by
    have : P ≤ 16 * P := by linarith
    have h16 : P + r * Q ≤ 16 * (P + r / 16 * Q) := by nlinarith
    calc P + r * Q ≤ 16 * (P + r / 16 * Q) := h16
      _ ≤ 16 * (8 * c ^ 2 / r * (T₁ + T₂)) := by gcongr
      _ = 128 * c ^ 2 / r * (T₁ + T₂) := by ring
  have hsq : (√P + √r * √Q) ^ 2 ≤ 2 * (P + r * Q) := by
    nlinarith [sq_nonneg (√P - √r * √Q), Real.sq_sqrt hr.le, Real.sq_sqrt hP, Real.sq_sqrt hQ]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ √P + √r * √Q)]
  refine sqrt_le_div_sqrt_mul_add_sqrt hr (by positivity) hT₁ hT₂ ?_
  calc (√P + √r * √Q) ^ 2 ≤ 2 * (P + r * Q) := hsq
    _ ≤ 2 * (128 * c ^ 2 / r * (T₁ + T₂)) := by gcongr
    _ = (16 * c) ^ 2 / r * (T₁ + T₂) := by ring

/-- **Taubes's `L²` bound on `∂bar_a α`.** Suppose the `L²` bound on `β` of
`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le` holds, the covariant
derivative satisfies `|∇_a α| ≤ |∂_a α| + |∂bar_a α|`, and the Dirac equation gives
`|∂bar_a α| ≤ c (|∇β| + |β|)`. If `16 ≤ r` and `64 c⁴ ≤ r`, then
`∫ |∂bar_a α|² ≤ (64 c⁴ / r) (∫ |∂_a α|² + ∫ |α|²)`. Here `∇_a α`, `∇β`, `∂_a α` and `∂bar_a α`
are any functions `Dα`, `Dβ`, `Dα'` and `Dbar` satisfying these hypotheses. -/
theorem integral_norm_sq_le_of_norm_le_mul_add_norm {Dα' : (x : X) → F₃ x} {Dbar : (x : X) → F₄ x}
    (hr16 : 16 ≤ r) (hcr : 64 * c ^ 4 ≤ r) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ) (hDα' : Integrable (fun x ↦ ‖Dα' x‖ ^ 2) μ)
    (hbound : ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ))
    (hsplit : ∀ᵐ x ∂μ, ‖Dα x‖ ≤ ‖Dα' x‖ + ‖Dbar x‖)
    (hdirac : ∀ᵐ x ∂μ, ‖Dbar x‖ ≤ c * (‖Dβ x‖ + ‖β x‖)) :
    ∫ x, ‖Dbar x‖ ^ 2 ∂μ ≤ 64 * c ^ 4 / r * (∫ x, ‖Dα' x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ) := by
  have hr : 0 < r := by linarith
  -- If `|∂bar_a α|²` is not integrable, its integral vanishes.
  by_cases hDbar : Integrable (fun x ↦ ‖Dbar x‖ ^ 2) μ; swap
  · rw [integral_undef hDbar]
    have hT' : 0 ≤ ∫ x, ‖Dα' x‖ ^ 2 ∂μ := integral_nonneg fun x ↦ by positivity
    have hT₂ : 0 ≤ ∫ x, ‖α x‖ ^ 2 ∂μ := integral_nonneg fun x ↦ by positivity
    exact mul_nonneg (by positivity) (add_nonneg hT' hT₂)
  set P := ∫ x, ‖Dβ x‖ ^ 2 ∂μ
  set Q := ∫ x, ‖β x‖ ^ 2 ∂μ
  set T₁ := ∫ x, ‖Dα x‖ ^ 2 ∂μ
  set T₂ := ∫ x, ‖α x‖ ^ 2 ∂μ
  set T' := ∫ x, ‖Dα' x‖ ^ 2 ∂μ
  set Z := ∫ x, ‖Dbar x‖ ^ 2 ∂μ
  have hQ : 0 ≤ Q := integral_nonneg fun x ↦ by positivity
  have hT₂ : 0 ≤ T₂ := integral_nonneg fun x ↦ by positivity
  have hZ : 0 ≤ Z := integral_nonneg fun x ↦ by positivity
  -- Integrate the square of the splitting of `∇_a α` and of the Dirac bound.
  have hT₁ : T₁ ≤ 2 * (T' + Z) := by
    rw [← integral_add hDα' hDbar, ← integral_const_mul]
    refine integral_mono_of_nonneg (.of_forall fun x ↦ by positivity)
      ((hDα'.add hDbar).const_mul _) ?_
    filter_upwards [hsplit] with x hx
    have hsq : ‖Dα x‖ ^ 2 ≤ (‖Dα' x‖ + ‖Dbar x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    nlinarith [sq_nonneg (‖Dα' x‖ - ‖Dbar x‖)]
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
  have hK : 32 * c ^ 4 / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]
    linarith
  have hc2 : 0 ≤ 2 * c ^ 2 := by positivity
  have h8 : 0 ≤ 8 * c ^ 2 / r := by positivity
  -- `Z ≤ (32 c⁴ / r) (T' + T₂) + (32 c⁴ / r) Z`, and the last term is absorbed.
  have hZ' : Z ≤ 32 * c ^ 4 / r * (T' + T₂) + 32 * c ^ 4 / r * Z := by
    calc Z ≤ 2 * c ^ 2 * (P + Q) := hZPQ
      _ ≤ 2 * c ^ 2 * (8 * c ^ 2 / r * (T₁ + T₂)) := mul_le_mul_of_nonneg_left hPQ hc2
      _ ≤ 2 * c ^ 2 * (8 * c ^ 2 / r * (2 * (T' + Z) + 2 * T₂)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) h8) hc2
      _ = 32 * c ^ 4 / r * (T' + T₂) + 32 * c ^ 4 / r * Z := by ring
  have hKZ : 32 * c ^ 4 / r * Z ≤ Z / 2 := by nlinarith
  have : 64 * c ^ 4 / r * (T' + T₂) = 2 * (32 * c ^ 4 / r * (T' + T₂)) := by ring
  linarith

/-- **Taubes's `L²` bound on `∂bar_a α`, in norm form.** Under the hypotheses of
`TauCeti.SeibergWitten.integral_norm_sq_le_of_norm_le_mul_add_norm`,
`‖∂bar_a α‖₂ ≤ 8 c² r^(-1/2) (‖∂_a α‖₂ + ‖α‖₂)`, with `L²` norms written `√(∫ |f|²)`. -/
theorem sqrt_integral_norm_sq_le_of_norm_le_mul_add_norm {Dα' : (x : X) → F₃ x}
    {Dbar : (x : X) → F₄ x} (hr16 : 16 ≤ r) (hcr : 64 * c ^ 4 ≤ r)
    (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ) (hDβ : Integrable (fun x ↦ ‖Dβ x‖ ^ 2) μ)
    (hDα' : Integrable (fun x ↦ ‖Dα' x‖ ^ 2) μ)
    (hbound : ∫ x, ‖Dβ x‖ ^ 2 ∂μ + r / 16 * ∫ x, ‖β x‖ ^ 2 ∂μ ≤
      8 * c ^ 2 / r * (∫ x, ‖Dα x‖ ^ 2 ∂μ + ∫ x, ‖α x‖ ^ 2 ∂μ))
    (hsplit : ∀ᵐ x ∂μ, ‖Dα x‖ ≤ ‖Dα' x‖ + ‖Dbar x‖)
    (hdirac : ∀ᵐ x ∂μ, ‖Dbar x‖ ≤ c * (‖Dβ x‖ + ‖β x‖)) :
    √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ≤
      8 * c ^ 2 / √r * (√(∫ x, ‖Dα' x‖ ^ 2 ∂μ) + √(∫ x, ‖α x‖ ^ 2 ∂μ)) := by
  have hZ := integral_norm_sq_le_of_norm_le_mul_add_norm hr16 hcr hβ hDβ hDα' hbound hsplit
    hdirac
  have hr : 0 < r := by linarith
  have hT' : 0 ≤ ∫ x, ‖Dα' x‖ ^ 2 ∂μ := integral_nonneg fun x ↦ by positivity
  have hT₂ : 0 ≤ ∫ x, ‖α x‖ ^ 2 ∂μ := integral_nonneg fun x ↦ by positivity
  exact sqrt_le_div_sqrt_mul_add_sqrt hr (by positivity) hT' hT₂ (hZ.trans_eq (by ring))

end MeasureSpace

section Manifold

open Bundle TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {A B F₁ F₂ : M → Type*} [∀ x, SeminormedAddCommGroup (A x)] [∀ x, SeminormedAddCommGroup (B x)]
  [∀ x, SeminormedAddCommGroup (F₁ x)] [∀ x, SeminormedAddCommGroup (F₂ x)]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Taubes's `L²` bound on `β` on a closed manifold.** On a compact Riemannian manifold without
boundary, with a `C¹` Riemannian metric, let `α`, `β`, `Dα`, `Dβ` be sections of families of
seminormed groups, standing for `α`, `β`, `∇_a α`, `∇β`, such that `|α|²` and `|∇_a α|²` are
continuous and `|β|²` is of class `C²`, satisfying the projected Weitzenböck inequality
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)` with the
Laplace–Beltrami operator `Δ = div ∘ grad`. If `0 < r` and `8 c ≤ r`, then
`∫ |∇β|² + (r / 16) ∫ |β|² ≤ (8 c² / r) (∫ |∇_a α|² + ∫ |α|²)` for the Riemannian volume. -/
theorem integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami
    {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F₁ x} {Dβ : (x : M) → F₂ x}
    (hr : 0 < r) (hcr : 8 * c ≤ r) (hα : Continuous fun x ↦ ‖α x‖ ^ 2)
    (hβ : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ‖β x‖ ^ 2)) (hDα : Continuous fun x ↦ ‖Dα x‖ ^ 2)
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
    (hcpt _ hα) (hcpt _ hDα)
    (Filter.Eventually.of_forall hW)

end Manifold

end TauCeti.SeibergWitten
