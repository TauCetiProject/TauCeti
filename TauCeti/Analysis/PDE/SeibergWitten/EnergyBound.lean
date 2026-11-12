/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Taubes's scaled `L²` energy bound at large parameter

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `χ = α u₀ + β` and an `E`-connection `a` with
curvature `F_a`. Among Taubes's coarse a priori estimates is the scaled energy bound

`r⁻¹ ‖F_a‖₂² + ‖∇χ‖₂² + r ‖1 - |χ|²‖₂² ≤ C`,

with `C` independent of `r` and of the solution. This file derives its spinor part and its
self-dual curvature part by integrating the projected Weitzenböck inequalities

`-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇β| + |α| + |β|)`,
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`,

which come from pairing the projected equations `∇*∇α + (r / 4) (|χ|² - 1) α = 𝔞` and
`∇*∇β + (r / 4) (|χ|² + 1) β = 𝔟` with `α` and `β`, where `|𝔞| ≤ c (|∇β| + |α| + |β|)` and
`|𝔟| ≤ c (|∇_a α| + |α| + |β|)`. Here `Δ = div ∘ grad`.

Write `s = |α|²`, `t = |β|²` and `u = s + t = |χ|²`. Adding the two inequalities, the potential
terms combine exactly into

`(r / 4) ((u - 1) s + (u + 1) t) = (r / 4) (1 - u)² + r t - (r / 4) (1 - s + t)`,

and the cross terms are absorbed by the gradient and potential terms. This gives the pointwise
inequality

`|∇_a α|² + |∇β|² + (r / 4) (1 - u)² + 2 r t ≤ (r / 2) (1 - s + t) + Δ(s + t) + K (1 + K / r)`,

with `K = c² + 4c`. The Laplacian integrates to zero. The remaining integral `r ∫ (1 - s + t)` is
fixed by topology: the `ω`-component of the curvature equation is
`⟪ω, F⟫ / 2 = (r / 8) (1 - s + t) - ⟪ω, η⟫ / 4`
(`TauCeti.SeibergWitten.inner_div_two_eq_of_add_hodgeStar_eq`), so integrating it expresses
`r ∫ (1 - s + t)` through the pairing of `[F] = 2π c₁(E)` with `[ω]` and the forcing `η`. For any
bound `r ∫ (1 - s + t) ≤ L`,

`∫ (|∇_a α|² + |∇β|² + (r / 4) (1 - |χ|²)² + 2 r |β|²) ≤ L / 2 + K (1 + K / r) Vol`

(`TauCeti.SeibergWitten.integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le`). In
particular `‖∇_a α‖₂`, `‖∇β‖₂`, `√r ‖1 - |χ|²‖₂` and `√r ‖β‖₂` are bounded independently of
`r ≥ 1`. The pointwise bound `|χ|² ≤ 1 + C / r` is not needed. On a compact Riemannian manifold
without boundary the Laplacian is the Laplace–Beltrami operator
(`integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le_of_laplaceBeltrami`).

For the curvature, the large-parameter curvature equation
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` for `F = i F_a` and `φ = α u₀` gives the pointwise
bound `‖F + ⋆F + η‖² ≤ (r² / 8) ((1 - s + t)² + 4 s t)`
(`TauCeti.SeibergWitten.norm_add_hodgeStar_add_sq_le`), and
`(1 - s + t)² + 4 s t = (1 - u)² + 4 t`. So `r⁻¹ ‖F + ⋆F + η‖² ≤ (r / 8) (1 - u)² + (r / 2) t`,
which is at most half the right side of the pointwise energy inequality. Integrating, the
self-dual part of the curvature satisfies

`r⁻¹ ∫ ‖F + ⋆F + η‖² ≤ L / 4 + K (1 + K / r) Vol / 2`

(`TauCeti.SeibergWitten.integral_norm_add_hodgeStar_add_sq_div_le`). Since `F + ⋆F = 2 F⁺`, this
bounds `r⁻¹ ‖F_a⁺‖₂²` up to the forcing. The anti-self-dual part `r⁻¹ ‖F_a⁻‖₂²` is not treated
here.

The fields are functions on a measure space with values in arbitrary normed groups, and the
Laplacians are integrable functions of integral zero, as in
`TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open MeasureTheory

namespace TauCeti.SeibergWitten

variable {X A B F₁ F₂ : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
  {c r L : ℝ}

/-- The pointwise energy inequality: the sum of the two projected Weitzenböck inequalities, with
the cross terms absorbed. Here `a`, `b`, `p`, `q` stand for the values of `|α|`, `|β|`,
`|∇_a α|`, `|∇β|`, and `gα`, `gβ` for those of `Δ|α|²`, `Δ|β|²`. -/
private theorem sq_add_sq_add_mul_sq_add_mul_sq_le {a b p q gα gβ : ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    (hα : -gα / 2 + p ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤ c * a * (q + a + b))
    (hβ : -gβ / 2 + q ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (p + a + b)) :
    p ^ 2 + q ^ 2 + r / 4 * (1 - a ^ 2 - b ^ 2) ^ 2 + 2 * r * b ^ 2 ≤
      r / 2 * (1 - a ^ 2 + b ^ 2) + gα + gβ + (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r) := by
  set K := c ^ 2 + 4 * c
  set w := 1 - a ^ 2 - b ^ 2
  -- The potential terms combine into `(r / 4) w² + r b² - (r / 4) (1 - a² + b²)`.
  have hpot : r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 =
      r / 4 * w ^ 2 + r * b ^ 2 - r / 4 * (1 - a ^ 2 + b ^ 2) := by
    simp only [w]
    ring
  -- The cross terms: `c a q ≤ (q² + c² a²) / 2`, `c b p ≤ (p² + c² b²) / 2` and
  -- `c (a + b)² ≤ 2 c (a² + b²)`, so they total at most `(p² + q²) / 2 + (K / 2) (1 - w)`.
  have hcross : c * a * (q + a + b) + c * b * (p + a + b) ≤
      (p ^ 2 + q ^ 2) / 2 + K / 2 * (1 - w) := by
    have h1 : c * a * q ≤ (q ^ 2 + c ^ 2 * a ^ 2) / 2 := by nlinarith [sq_nonneg (q - c * a)]
    have h2 : c * b * p ≤ (p ^ 2 + c ^ 2 * b ^ 2) / 2 := by nlinarith [sq_nonneg (p - c * b)]
    have h3 : c * (a + b) ^ 2 ≤ 2 * c * (a ^ 2 + b ^ 2) := by
      nlinarith [mul_nonneg hc (sq_nonneg (a - b))]
    simp only [K, w]
    nlinarith [h1, h2, h3]
  -- `-(K / 2) w ≤ (r / 8) w² + K² / (2 r)`, from `(r / 8) (w + 2 K / r)² ≥ 0`.
  have hamgm : -(K / 2 * w) ≤ r / 8 * w ^ 2 + K ^ 2 / (2 * r) := by
    have hsq : r / 8 * w ^ 2 + K ^ 2 / (2 * r) + K / 2 * w = r / 8 * (w + 2 * K / r) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ r / 8 * (w + 2 * K / r) ^ 2 := by positivity
    linarith
  have hK : K * (1 + K / r) = K + K ^ 2 / r := by
    field_simp
  rw [hK]
  have hK' : K ^ 2 / r = 2 * (K ^ 2 / (2 * r)) := by
    field_simp
  linarith [hα, hβ, hpot, hcross, hamgm, hK']

section Integral

variable [IsFiniteMeasure μ] {α : X → A} {β : X → B} {gα gβ : X → ℝ}

/-- The right side of the pointwise energy inequality is integrable. -/
private theorem integrable_weitzenbockBound (hgα : Integrable gα μ) (hgβ : Integrable gβ μ)
    (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ) (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ) :
    Integrable (fun x ↦ r / 2 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) + gα x + gβ x +
      (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r)) μ :=
    ((((((integrable_const 1).sub hα).add hβ).const_mul _).add hgα).add hgβ).add
      (integrable_const _)

/-- The integral of the right side of the pointwise energy inequality, when the Laplacians
`gα`, `gβ` integrate to zero and `r ∫ (1 - |α|² + |β|²) ≤ L`. -/
private theorem integral_weitzenbockBound_le (hgα : Integrable gα μ) (hgα0 : ∫ x, gα x ∂μ = 0)
    (hgβ : Integrable gβ μ) (hgβ0 : ∫ x, gβ x ∂μ = 0) (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ)
    (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ) (hL : r * ∫ x, (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ∂μ ≤ L) :
    ∫ x, (r / 2 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) + gα x + gβ x +
        (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r)) ∂μ ≤
      L / 2 + (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r) * μ.real Set.univ := by
  have hδ : Integrable (fun x ↦ r / 2 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2)) μ :=
    (((integrable_const 1).sub hα).add hβ).const_mul _
  have hδα : Integrable (fun x ↦ r / 2 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) + gα x) μ := hδ.add hgα
  have hδαβ : Integrable (fun x ↦ r / 2 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) + gα x + gβ x) μ :=
    hδα.add hgβ
  rw [integral_add hδαβ (integrable_const _), integral_add hδα hgβ, integral_add hδ hgα,
    integral_const_mul, integral_const, smul_eq_mul, hgα0, hgβ0]
  linarith

end Integral

/-- **Taubes's scaled `L²` energy bound.** Let `gα`, `gβ` be integrable functions of integral zero,
standing for `Δ|α|²` and `Δ|β|²`, and suppose the projected Weitzenböck inequalities
`-gα / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇β| + |α| + |β|)` and
`-gβ / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)` hold almost
everywhere on a finite measure space, with `c ≥ 0` and `r > 0`. If `r ∫ (1 - |α|² + |β|²) ≤ L`,
then

`∫ (|∇_a α|² + |∇β|² + (r / 4) (1 - |α|² - |β|²)² + 2 r |β|²) ≤ L / 2 + K (1 + K / r) Vol`

with `K = c² + 4 c`. Here `∇_a α` and `∇β` are any functions `Dα` and `Dβ` satisfying these
hypotheses. -/
theorem integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le [IsFiniteMeasure μ]
    {α : X → A} {β : X → B} {Dα : X → F₁} {Dβ : X → F₂} {gα gβ : X → ℝ} (hr : 0 < r)
    (hc : 0 ≤ c) (hgα : Integrable gα μ) (hgα0 : ∫ x, gα x ∂μ = 0) (hgβ : Integrable gβ μ)
    (hgβ0 : ∫ x, gβ x ∂μ = 0) (hα : Integrable (fun x ↦ ‖α x‖ ^ 2) μ)
    (hβ : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hL : r * ∫ x, (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ∂μ ≤ L)
    (hWα : ∀ᵐ x ∂μ, -gα x / 2 + ‖Dα x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤
      c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ᵐ x ∂μ, -gβ x / 2 + ‖Dβ x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    ∫ x, (‖Dα x‖ ^ 2 + ‖Dβ x‖ ^ 2 + r / 4 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 +
        2 * r * ‖β x‖ ^ 2) ∂μ ≤
      L / 2 + (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r) * μ.real Set.univ := by
  refine (integral_mono_of_nonneg (.of_forall fun x ↦ by positivity)
    (integrable_weitzenbockBound hgα hgβ hα hβ) ?_).trans
    (integral_weitzenbockBound_le hgα hgα0 hgβ hgβ0 hα hβ hL)
  filter_upwards [hWα, hWβ] with x hxα hxβ
  exact sq_add_sq_add_mul_sq_add_mul_sq_le hr hc hxα hxβ

section Manifold

open Bundle TauCeti.Manifold
open scoped ContDiff _root_.Manifold

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

/-- **Taubes's scaled `L²` energy bound on a closed manifold.** On a compact Riemannian manifold
without boundary, let `α`, `β` be fields with `|α|²` and `|β|²` of class `C²`, and let `∇_a α`,
`∇β` be fields satisfying the projected Weitzenböck inequalities
`-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇β| + |α| + |β|)` and
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)` with the
Laplace–Beltrami operator `Δ = div ∘ grad`, where `c ≥ 0` and `r > 0`. If
`r ∫ (1 - |α|² + |β|²) ≤ L`, then, for the Riemannian volume and `K = c² + 4 c`,

`∫ (|∇_a α|² + |∇β|² + (r / 4) (1 - |α|² - |β|²)² + 2 r |β|²) ≤ L / 2 + K (1 + K / r) Vol`. -/
theorem integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le_of_laplaceBeltrami
    {α : M → A} {β : M → B} {Dα : M → F₁} {Dβ : M → F₂} (hr : 0 < r) (hc : 0 ≤ c)
    (hα : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ‖α x‖ ^ 2)) (hβ : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ‖β x‖ ^ 2))
    (hL : r * ∫ x, (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ∂riemannianVolume I M ≤ L)
    (hWα : ∀ x, -laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x / 2 + ‖Dα x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤
      c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ x, -laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖)) :
    ∫ x, (‖Dα x‖ ^ 2 + ‖Dβ x‖ ^ 2 + r / 4 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 +
        2 * r * ‖β x‖ ^ 2) ∂riemannianVolume I M ≤
      L / 2 + (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r) *
        (riemannianVolume I M).real Set.univ := by
  have hcpt (f : M → ℝ) (hf : Continuous f) : Integrable f (riemannianVolume I M) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  exact integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le hr hc
    (hcpt _ (continuous_laplaceBeltrami hα))
    (integral_laplaceBeltrami_eq_zero hα (HasCompactSupport.of_compactSpace _))
    (hcpt _ (continuous_laplaceBeltrami hβ))
    (integral_laplaceBeltrami_eq_zero hβ (HasCompactSupport.of_compactSpace _))
    (hcpt _ hα.continuous) (hcpt _ hβ.continuous) hL (.of_forall hWα) (.of_forall hWβ)

end Manifold

section Curvature

open Module

attribute [local instance] finiteDimensional_of_finrank_four

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- **Taubes's scaled `L²` bound on the self-dual curvature.** Suppose that at almost every point
the large-parameter curvature equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` holds for the real
two-form `F = i F_a`, where `φ` and `β` lie in the `-2i`- and `2i`-eigenspaces of `ω`, `|ω|² = 2`
and `W⁺` has complex dimension two. Suppose moreover the hypotheses of
`TauCeti.SeibergWitten.integral_norm_sq_add_norm_sq_add_mul_sq_add_mul_norm_sq_le` for `φ`, `β`:
the projected Weitzenböck inequalities with Laplacians `gα`, `gβ` of integral zero, and
`r ∫ (1 - |φ|² + |β|²) ≤ L`. Then, with `K = c² + 4 c`,

`r⁻¹ ∫ ‖F + ⋆F + η‖² ≤ L / 4 + K (1 + K / r) Vol / 2`.

Since `F + ⋆F = 2 F⁺`, this bounds `r⁻¹ ‖F_a⁺‖₂²` up to the forcing `η`. -/
theorem integral_norm_add_hodgeStar_add_sq_div_le [IsFiniteMeasure μ] {ω : ⋀[ℝ]^2 V}
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V) (hω : o.hodgeStar hkl ω = ω)
    (hω₂ : ‖ω‖ ^ 2 = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (CliffordAlgebra.ι Q v)) = -ρ (CliffordAlgebra.ι Q v))
    (h₂ : finrank ℂ (CliffordAlgebra.positiveHalfSpinors o ρ) = 2)
    {φ β : X → CliffordAlgebra.positiveHalfSpinors o ρ} {F η : X → ⋀[ℝ]^2 V} {Dα : X → F₁}
    {Dβ : X → F₂} {gα gβ : X → ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    (hφ : ∀ᵐ x ∂μ, cliffordProjection o ρ ω (φ x) = φ x)
    (hβ : ∀ᵐ x ∂μ, cliffordProjection o ρ ω (β x) = 0)
    (hF : ∀ᵐ x ∂μ, F x + o.hodgeStar hkl (F x) = (r / 4) • ω -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 V) - η x)
    (hgα : Integrable gα μ) (hgα0 : ∫ x, gα x ∂μ = 0) (hgβ : Integrable gβ μ)
    (hgβ0 : ∫ x, gβ x ∂μ = 0) (hφi : Integrable (fun x ↦ ‖φ x‖ ^ 2) μ)
    (hβi : Integrable (fun x ↦ ‖β x‖ ^ 2) μ)
    (hL : r * ∫ x, (1 - ‖φ x‖ ^ 2 + ‖β x‖ ^ 2) ∂μ ≤ L)
    (hWα : ∀ᵐ x ∂μ, -gα x / 2 + ‖Dα x‖ ^ 2 +
        r / 4 * (‖φ x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖φ x‖ ^ 2 ≤
      c * ‖φ x‖ * (‖Dβ x‖ + ‖φ x‖ + ‖β x‖))
    (hWβ : ∀ᵐ x ∂μ, -gβ x / 2 + ‖Dβ x‖ ^ 2 +
        r / 4 * (‖φ x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖φ x‖ + ‖β x‖)) :
    (∫ x, ‖F x + o.hodgeStar hkl (F x) + η x‖ ^ 2 ∂μ) / r ≤
      L / 4 + (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r) * μ.real Set.univ / 2 := by
  set K := (c ^ 2 + 4 * c) * (1 + (c ^ 2 + 4 * c) / r)
  have hint := integral_mono_of_nonneg
    (f := fun x ↦ ‖F x + o.hodgeStar hkl (F x) + η x‖ ^ 2)
    (g := fun x ↦ r / 2 * (r / 2 * (1 - ‖φ x‖ ^ 2 + ‖β x‖ ^ 2) + gα x + gβ x + K))
    (.of_forall fun x ↦ by positivity)
    ((integrable_weitzenbockBound hgα hgβ hφi hβi).const_mul (r / 2)) <| by
    filter_upwards [hφ, hβ, hF, hWα, hWβ] with x hφx hβx hFx hxα hxβ
    have h := norm_add_hodgeStar_add_sq_le hQ hkl hω hω₂ hφx hβx hρ h₂ hr.le hFx
    -- The pointwise energy inequality, multiplied by `r / 2`.
    have hE := mul_le_mul_of_nonneg_left (sq_add_sq_add_mul_sq_add_mul_sq_le hr hc hxα hxβ)
      (by positivity : (0 : ℝ) ≤ r / 2)
    -- `(1 - s + t)² + 4 s t = (1 - s - t)² + 4 t` for `s = |φ|²` and `t = |β|²`.
    have hsq : (1 - ‖φ x‖ ^ 2 + ‖β x‖ ^ 2) ^ 2 + 4 * ‖φ x‖ ^ 2 * ‖β x‖ ^ 2 =
        (1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 + 4 * ‖β x‖ ^ 2 := by ring
    rw [hsq] at h
    have hD : 0 ≤ r / 2 * (‖Dα x‖ ^ 2 + ‖Dβ x‖ ^ 2) := by positivity
    have hβr : 0 ≤ r ^ 2 * ‖β x‖ ^ 2 := by positivity
    nlinarith [h, hE, hD, hβr]
  have hb := mul_le_mul_of_nonneg_left
    (integral_weitzenbockBound_le (c := c) hgα hgα0 hgβ hgβ0 hφi hβi hL)
    (by positivity : (0 : ℝ) ≤ r / 2)
  rw [integral_const_mul] at hint
  rw [div_le_iff₀ hr]
  nlinarith [hint, hb]

end Curvature

end TauCeti.SeibergWitten
