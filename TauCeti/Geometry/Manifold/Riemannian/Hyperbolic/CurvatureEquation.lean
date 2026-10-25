/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# The curvature equation for conformal metrics on surfaces

Let `g` be a smooth Riemannian metric on a surface and `ĝ = e^(2φ) g` a conformal metric. In
dimension two the scalar curvature is twice the Gaussian curvature, and the conformal change of
scalar curvature becomes `Scal^ĝ = e^(-2φ) (Scal^g - 2 Δφ)`, with `Δ = div ∘ grad` the
Laplace–Beltrami operator of `g`. Thus `ĝ` has constant Gaussian curvature `-1` exactly when
`φ` solves the curvature equation

`Δ⁺φ + K + e^(2φ) = 0`,

where `Δ⁺ = -Δ` is the nonnegative Laplacian and `K = Scal^g / 2` the Gaussian curvature of `g`.
This is the equation whose solution on a closed surface of negative Euler characteristic gives
the hyperbolic metric in a conformal class.

On a closed surface the right side of `Δφ = K + e^(2φ)` is strictly increasing in `φ`, so the
maximum principle controls solutions: evaluating the equation at a maximum or a minimum of `φ`
gives the barriers `min (-K) ≤ e^(2φ) ≤ max (-K)`, forces `K` to be negative somewhere, and the
comparison principle gives uniqueness of the conformal factor. The statements below are proved
for every constant negative scalar curvature `c`, the hyperbolic case being `c = -2`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_of_finrank_eq_two`: the conformal
  change of scalar curvature on a surface.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_eq_iff_of_finrank_eq_two`: `e^(2φ) g`
  has scalar curvature `c` exactly when `-Δφ + Scal^g / 2 = (c / 2) e^(2φ)`.
* `Bundle.ContMDiffRiemannianMetric.apply_le_of_scalarCurvature_rescale_eq`,
  `Bundle.ContMDiffRiemannianMetric.le_apply_of_scalarCurvature_rescale_eq`: the upper and
  lower barriers for the conformal factor.
* `Bundle.ContMDiffRiemannianMetric.exists_scalarCurvature_neg_of_scalarCurvature_rescale_eq`:
  the sign obstruction.
* `Bundle.ContMDiffRiemannianMetric.eq_of_scalarCurvature_rescale_eq`: uniqueness of the metric
  of constant negative curvature in a conformal class of a closed surface.

## References

* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
-/

public section

open Bundle Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Scalar curvature under conformal change on a surface.** Let `g` be a smooth metric on a
surface and `f = e^(2φ)` a smooth positive function. Then
`Scal^(f g) = f⁻¹ (Scal^g - 2 Δφ)`, where `Δφ = div grad φ` is taken for `g`. -/
theorem scalarCurvature_rescale_of_finrank_eq_two (hE : finrank ℝ E = 2)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) :
    (g.rescale f hf hf_pos).scalarCurvature x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (f x)⁻¹ * (g.scalarCurvature x - 2 * laplaceBeltrami I φ x) := by
  rw [g.scalarCurvature_rescale hf hf_pos hfφ x, hE]
  norm_num

/-- **The prescribed curvature equation on a surface.** Let `g` be a smooth metric on a surface
and `f = e^(2φ)` a smooth positive function. Then `e^(2φ) g` has scalar curvature `c` at `x`
exactly when `-Δφ + Scal^g / 2 = (c / 2) e^(2φ)` there, where `Δφ = div grad φ` is taken for
`g`. Since the scalar curvature of a surface is twice its Gaussian curvature, for `c = -2` this is
the equation `Δ⁺φ + K + e^(2φ) = 0` for a metric of Gaussian curvature `-1`, where
`Δ⁺ = -div grad` and `K = Scal^g / 2`. -/
theorem scalarCurvature_rescale_eq_iff_of_finrank_eq_two (hE : finrank ℝ E = 2)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (c : ℝ) (x : M) :
    (g.rescale f hf hf_pos).scalarCurvature x = c ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      -laplaceBeltrami I φ x + g.scalarCurvature x / 2 = c / 2 * Real.exp (2 * φ x) := by
  rw [scalarCurvature_rescale_of_finrank_eq_two g hE hf hf_pos hfφ x, ← hfφ x,
    inv_mul_eq_iff_eq_mul₀ (hf_pos x).ne']
  constructor <;> intro h <;> linarith

/-- If `f g` has constant scalar curvature `c` on a surface, the logarithmic conformal factor
`log f / 2` solves `Δ (log f / 2) = Scal^g / 2 - (c / 2) f`. -/
private theorem laplaceBeltrami_half_log (hE : finrank ℝ E = 2)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {c : ℝ}
    (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) (x : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    laplaceBeltrami I (fun y ↦ Real.log (f y) / 2) x = g.scalarCurvature x / 2 - c / 2 * f x := by
  have hfφ (y : M) : f y = Real.exp (2 * (Real.log (f y) / 2)) := by
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hf_pos y)]
  have := (scalarCurvature_rescale_eq_iff_of_finrank_eq_two g hE hf hf_pos hfφ c x).1 (h x)
  rw [← hfφ x] at this
  linarith

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The logarithmic conformal factor `log f / 2` of a smooth positive function is `C²`. -/
private theorem contMDiff_half_log {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) : ContMDiff I 𝓘(ℝ) 2 (fun y ↦ Real.log (f y) / 2) :=
  ((hf.of_le (by simp)).log fun y ↦ (hf_pos y).ne').div_const 2

/-- **Upper barrier.** On a closed surface, let `f g` have constant negative scalar curvature
`c`. If `c C ≤ Scal^g` everywhere, then `f ≤ C`; for `c = -2` this says that the conformal factor
of a metric of Gaussian curvature `-1` is at most `max (-K)`, with `K = Scal^g / 2`. -/
theorem apply_le_of_scalarCurvature_rescale_eq [CompactSpace M] [I.Boundaryless]
    (hE : finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    {c : ℝ} (hc : c < 0) (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) {C : ℝ}
    (hC : ∀ x, c * C ≤ g.scalarCurvature x) (x : M) : f x ≤ C := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- At a maximum `x₀` of `f`, also a maximum of `log f / 2`, the Laplacian is nonpositive.
  obtain ⟨x₀, -, hx₀⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hmax : IsLocalMax (fun y ↦ Real.log (f y) / 2) x₀ :=
    Filter.Eventually.of_forall fun y ↦ by
      have := Real.log_le_log (hf_pos y) (hx₀ (Set.mem_univ y))
      dsimp only
      linarith
  have hΔ := laplaceBeltrami_nonpos_of_isLocalMax (contMDiff_half_log hf hf_pos).contMDiffAt hmax
  rw [laplaceBeltrami_half_log g hE hf hf_pos h x₀] at hΔ
  have hx : f x ≤ f x₀ := hx₀ (Set.mem_univ x)
  nlinarith [hC x₀]

/-- **Lower barrier.** On a closed surface, let `f g` have constant negative scalar curvature
`c`. If `Scal^g ≤ c C` everywhere, then `C ≤ f`; for `c = -2` this says that the conformal factor
of a metric of Gaussian curvature `-1` is at least `min (-K)`, with `K = Scal^g / 2`. -/
theorem le_apply_of_scalarCurvature_rescale_eq [CompactSpace M] [I.Boundaryless]
    (hE : finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    {c : ℝ} (hc : c < 0) (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) {C : ℝ}
    (hC : ∀ x, g.scalarCurvature x ≤ c * C) (x : M) : C ≤ f x := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- At a minimum `x₀` of `f`, also a minimum of `log f / 2`, the Laplacian is nonnegative.
  obtain ⟨x₀, -, hx₀⟩ :=
    isCompact_univ.exists_isMinOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hmin : IsLocalMin (fun y ↦ Real.log (f y) / 2) x₀ :=
    Filter.Eventually.of_forall fun y ↦ by
      have := Real.log_le_log (hf_pos x₀) (hx₀ (Set.mem_univ y))
      dsimp only
      linarith
  have hΔ := laplaceBeltrami_nonneg_of_isLocalMin (contMDiff_half_log hf hf_pos).contMDiffAt hmin
  rw [laplaceBeltrami_half_log g hE hf hf_pos h x₀] at hΔ
  have hx : f x₀ ≤ f x := hx₀ (Set.mem_univ x)
  nlinarith [hC x₀]

/-- **Sign obstruction.** If a metric `g` on a nonempty closed surface is conformal to a metric of
constant negative scalar curvature, then the scalar curvature of `g` is negative somewhere. -/
theorem exists_scalarCurvature_neg_of_scalarCurvature_rescale_eq [CompactSpace M]
    [I.Boundaryless] [Nonempty M] (hE : finrank ℝ E = 2) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {c : ℝ} (hc : c < 0)
    (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) :
    ∃ x, g.scalarCurvature x < 0 := by
  by_contra! hnonneg
  obtain ⟨x⟩ := ‹Nonempty M›
  have := apply_le_of_scalarCurvature_rescale_eq g hE hf hf_pos hc h (C := 0)
    (fun y ↦ by simpa using hnonneg y) x
  linarith [hf_pos x]

/-- **Uniqueness of the constant negative curvature metric in a conformal class.** On a closed
surface, two metrics `f₁ g` and `f₂ g` conformal to `g` with the same constant negative scalar
curvature coincide. In particular a conformal class contains at most one metric of Gaussian
curvature `-1`. -/
theorem eq_of_scalarCurvature_rescale_eq [CompactSpace M] [I.Boundaryless]
    (hE : finrank ℝ E = 2) {f₁ f₂ : M → ℝ} (hf₁ : ContMDiff I 𝓘(ℝ) ∞ f₁)
    (hf₁_pos : ∀ x, 0 < f₁ x) (hf₂ : ContMDiff I 𝓘(ℝ) ∞ f₂) (hf₂_pos : ∀ x, 0 < f₂ x)
    {c : ℝ} (hc : c < 0) (h₁ : ∀ x, (g.rescale f₁ hf₁ hf₁_pos).scalarCurvature x = c)
    (h₂ : ∀ x, (g.rescale f₂ hf₂ hf₂_pos).scalarCurvature x = c) : f₁ = f₂ := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- Both `log fᵢ / 2` solve `Δ φ = Scal^g / 2 - (c / 2) e^(2 φ)`, whose right side is strictly
  -- increasing in `φ` because `c < 0`; the comparison principle applies in both directions.
  have hmono (x : M) :
      StrictMono fun t : ℝ ↦ g.scalarCurvature x / 2 - c / 2 * Real.exp (2 * t) := by
    intro s t hst
    have := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hst two_pos)
    dsimp only
    nlinarith
  have hsol {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
      (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) (x : M) :
      laplaceBeltrami I (fun y ↦ Real.log (f y) / 2) x =
        g.scalarCurvature x / 2 - c / 2 * Real.exp (2 * (Real.log (f x) / 2)) := by
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hf_pos x)]
    exact laplaceBeltrami_half_log g hE hf hf_pos h x
  have hle₁₂ := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (contMDiff_half_log hf₁ hf₁_pos) (contMDiff_half_log hf₂ hf₂_pos)
    (fun x ↦ (hsol hf₁ hf₁_pos h₁ x).ge) (fun x ↦ (hsol hf₂ hf₂_pos h₂ x).le)
  have hle₂₁ := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (contMDiff_half_log hf₂ hf₂_pos) (contMDiff_half_log hf₁ hf₁_pos)
    (fun x ↦ (hsol hf₂ hf₂_pos h₂ x).ge) (fun x ↦ (hsol hf₁ hf₁_pos h₁ x).le)
  funext x
  have := le_antisymm (hle₁₂ x) (hle₂₁ x)
  simpa [Real.log_injOn_pos.eq_iff (hf₁_pos x) (hf₂_pos x)] using this

end Bundle.ContMDiffRiemannianMetric
