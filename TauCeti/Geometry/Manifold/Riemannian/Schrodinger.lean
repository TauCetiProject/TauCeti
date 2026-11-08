/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.Poincare
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Coercivity of Schrödinger operators with a nonnegative potential on a closed manifold

Let `M` be a compact connected manifold without boundary with a continuous Riemannian metric and
its Riemannian volume `dV`, and let `f ≥ 0` be a continuous potential that does not vanish
identically. The quadratic form of the Schrödinger operator `-Δ + f` is then coercive: there is
`c > 0` with

`c ∫ u² dV ≤ ∫ ‖∇u‖² dV + ∫ f u² dV`

for every `C¹` function `u`
(`TauCeti.Manifold.exists_pos_mul_integral_sq_le_integral_norm_sq_mgradient_add_integral_mul_sq`),
and hence also `c (∫ u² dV + ∫ ‖∇u‖² dV) ≤ ∫ ‖∇u‖² dV + ∫ f u² dV`, which is coercivity in the
`H¹` norm (`TauCeti.Manifold.exists_pos_mul_integral_sq_add_integral_norm_sq_mgradient_le`). The
Dirichlet energy alone only controls `u` up to constants; the potential controls the constants.

The argument is direct and needs no compactness of the Sobolev embedding. Write `m` for the mean
of `u` and `F = ∫ f dV > 0`. The pointwise inequalities `m² ≤ 2 u² + 2 (u - m)²` and
`u² ≤ 2 m² + 2 (u - m)²`, together with `f ≤ B`, give

`m² F ≤ 2 ∫ f u² dV + 2 B ∫ (u - m)² dV`,  `∫ u² dV ≤ 2 m² vol(M) + 2 ∫ (u - m)² dV`,

and the Poincaré–Wirtinger inequality
(`TauCeti.Manifold.exists_integral_sq_sub_average_le_mul_integral_norm_sq_mgradient`) bounds
`∫ (u - m)² dV` by the Dirichlet energy.

With Green's first identity the coercivity shows that `-Δ + f` has trivial kernel: a `C²`
solution of `Δu = f u` vanishes (`TauCeti.Manifold.eq_zero_of_laplaceBeltrami_eq_mul`). Here
`Δ = div ∘ grad` is `TauCeti.Manifold.laplaceBeltrami`, a nonpositive operator.

In Seiberg–Witten theory the linearized gauge action at a configuration `(A, ψ)` is
`d₀ ξ = (-2 dξ, ξ ψ)` on imaginary functions `ξ`, and `d₀* d₀ ξ = -4 Δξ + |ψ|² ξ`, whose energy is
`4 ∫ ‖∇ξ‖² dV + ∫ |ψ|² |ξ|² dV`. For a continuous spinor `ψ` that does not vanish identically, the
results here, applied to the potential `|ψ|² / 4`, give the coercivity of this energy and the
injectivity of `d₀* d₀` behind the local slice theorem. Without the potential the kernel consists
of the constants, the stabilizer of a reducible configuration.

## Main results

* `TauCeti.Manifold.exists_pos_mul_integral_sq_le_integral_norm_sq_mgradient_add_integral_mul_sq`:
  `c ∫ u² dV ≤ ∫ ‖∇u‖² dV + ∫ f u² dV`.
* `TauCeti.Manifold.exists_pos_mul_integral_sq_add_integral_norm_sq_mgradient_le`:
  `c (∫ u² dV + ∫ ‖∇u‖² dV) ≤ ∫ ‖∇u‖² dV + ∫ f u² dV`.
* `TauCeti.Manifold.eq_zero_of_laplaceBeltrami_eq_mul`: a `C²` solution of `Δu = f u` is zero.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, Chapter 4 (the
  local structure of the moduli space at an irreducible configuration).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), §7.8 (the Poincaré–Wirtinger inequality).
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

section Mean

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f u : X → ℝ}

/-- A nonnegative potential `f ≤ B` controls a constant `m` through
`m² ∫ f ≤ 2 ∫ f u² + 2 B ∫ (u - m)²`. -/
private lemma sq_mul_integral_le (hf : Continuous f) (hu : Continuous u) (hf₀ : 0 ≤ f) {B : ℝ}
    (hfB : ∀ x, f x ≤ B) (m : ℝ) :
    m ^ 2 * ∫ x, f x ∂μ ≤ 2 * ∫ x, f x * u x ^ 2 ∂μ + 2 * B * ∫ x, (u x - m) ^ 2 ∂μ := by
  have hint {g : X → ℝ} (hg : Continuous g) : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  calc m ^ 2 * ∫ x, f x ∂μ = ∫ x, m ^ 2 * f x ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ x, (2 * (f x * u x ^ 2) + 2 * B * (u x - m) ^ 2) ∂μ := by
        refine integral_mono (hint (by fun_prop)) (hint (by fun_prop)) fun x ↦ ?_
        -- `2 f u² + 2 B (u - m)² - m² f = f (2 u - m)² + 2 (B - f) (u - m)²`.
        nlinarith [mul_nonneg (hf₀ x) (sq_nonneg (2 * u x - m)),
          mul_nonneg (sub_nonneg.2 (hfB x)) (sq_nonneg (u x - m))]
    _ = _ := by
        rw [integral_add (hint (by fun_prop)) (hint (by fun_prop)), integral_const_mul,
          integral_const_mul]

/-- A constant `m` and the oscillation of `u` about it control `∫ u²`. -/
private lemma integral_sq_le (hu : Continuous u) (m : ℝ) :
    ∫ x, u x ^ 2 ∂μ ≤ 2 * μ.real univ * m ^ 2 + 2 * ∫ x, (u x - m) ^ 2 ∂μ := by
  have hint {g : X → ℝ} (hg : Continuous g) : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  calc ∫ x, u x ^ 2 ∂μ ≤ ∫ x, (2 * m ^ 2 + 2 * (u x - m) ^ 2) ∂μ :=
        integral_mono (hint (by fun_prop)) (hint (by fun_prop)) fun x ↦ by
          nlinarith [sq_nonneg (u x - 2 * m)]
    _ = _ := by
        rw [integral_add (integrable_const _) (hint (by fun_prop)), integral_const,
          integral_const_mul, smul_eq_mul]
        ring

end Mean

section Coercive

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M]

/-- **Coercivity of a Schrödinger form.** On a compact connected manifold without boundary with
a continuous Riemannian metric, let `f ≥ 0` be a continuous function that does not vanish
identically. There is `c > 0` with `c ∫ u² dV ≤ ∫ ‖∇u‖² dV + ∫ f u² dV` for every `C¹`
function `u`. -/
theorem exists_pos_mul_integral_sq_le_integral_norm_sq_mgradient_add_integral_mul_sq
    [PreconnectedSpace M] {f : M → ℝ} (hf : Continuous f) (hf₀ : 0 ≤ f) (hf₁ : f ≠ 0) :
    ∃ c > 0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      c * ∫ x, u x ^ 2 ∂riemannianVolume I M ≤
        ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, f x * u x ^ 2 ∂riemannianVolume I M := by
  set μ := riemannianVolume I M
  obtain ⟨C, hC⟩ :=
    exists_integral_sq_sub_average_le_mul_integral_norm_sq_mgradient (I := I) (M := M)
  obtain ⟨B, hB⟩ := (isCompact_range hf).bddAbove
  have hfB (x : M) : f x ≤ B := hB ⟨x, rfl⟩
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hf₁
  have hB₀ : 0 ≤ B := (hf₀ x₀).trans (hfB x₀)
  -- The potential has positive integral, since it is positive on a nonempty open set.
  have hF : 0 < ∫ x, f x ∂μ :=
    hf.integral_pos_of_hasCompactSupport_nonneg_ne_zero (HasCompactSupport.of_compactSpace f) hf₀
      hx₀
  set F := ∫ x, f x ∂μ
  set V := μ.real univ
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨(4 * V / F + (4 * V * B / F + 2) * C + 1)⁻¹, by positivity, fun u hu ↦ ?_⟩
  set m := ⨍ y, u y ∂μ
  set P := ∫ x, ‖mgradient I u x‖ ^ 2 ∂μ
  set S := ∫ x, f x * u x ^ 2 ∂μ
  set W := ∫ x, (u x - m) ^ 2 ∂μ
  have hP : 0 ≤ P := integral_nonneg fun x ↦ by positivity
  have hS : 0 ≤ S := integral_nonneg fun x ↦ mul_nonneg (hf₀ x) (sq_nonneg _)
  -- The potential controls the mean, and the Poincaré–Wirtinger inequality the oscillation.
  have hm : 2 * V * m ^ 2 ≤ 4 * V / F * S + 4 * V * B / F * W := by
    calc 2 * V * m ^ 2 ≤ 2 * V * ((2 * S + 2 * B * W) / F) := by
          gcongr
          rw [le_div_iff₀ hF]
          exact sq_mul_integral_le hf hu.continuous hf₀ hfB m
      _ = 4 * V / F * S + 4 * V * B / F * W := by
          field_simp
          ring
  have hWP : (4 * V * B / F + 2) * W ≤ (4 * V * B / F + 2) * C * P := by
    calc _ ≤ (4 * V * B / F + 2) * (C * P) :=
          mul_le_mul_of_nonneg_left (hC u hu) (by positivity)
      _ = _ := by ring
  have hsq := integral_sq_le (μ := μ) hu.continuous m
  rw [inv_mul_le_iff₀ (by positivity)]
  have hA : 0 ≤ 4 * V / F := by positivity
  have hA' : 0 ≤ (4 * V * B / F + 2) * C := by positivity
  nlinarith

/-- **`H¹` coercivity of a Schrödinger form.** On a compact connected manifold without boundary
with a continuous Riemannian metric, let `f ≥ 0` be a continuous function that does not vanish
identically. There is `c > 0` with `c (∫ u² dV + ∫ ‖∇u‖² dV) ≤ ∫ ‖∇u‖² dV + ∫ f u² dV` for every
`C¹` function `u`. -/
theorem exists_pos_mul_integral_sq_add_integral_norm_sq_mgradient_le [PreconnectedSpace M]
    {f : M → ℝ} (hf : Continuous f) (hf₀ : 0 ≤ f) (hf₁ : f ≠ 0) :
    ∃ c > 0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      c * (∫ x, u x ^ 2 ∂riemannianVolume I M +
          ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M) ≤
        ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, f x * u x ^ 2 ∂riemannianVolume I M := by
  obtain ⟨c, hc, hcu⟩ :=
    exists_pos_mul_integral_sq_le_integral_norm_sq_mgradient_add_integral_mul_sq (I := I)
      hf hf₀ hf₁
  refine ⟨min c 1 / 2, by positivity, fun u hu ↦ ?_⟩
  have h := hcu u hu
  have hX : 0 ≤ ∫ x, u x ^ 2 ∂riemannianVolume I M := integral_nonneg fun x ↦ sq_nonneg _
  have hP : 0 ≤ ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I M :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hS : 0 ≤ ∫ x, f x * u x ^ 2 ∂riemannianVolume I M :=
    integral_nonneg fun x ↦ mul_nonneg (hf₀ x) (sq_nonneg _)
  have h₁ : min c 1 ≤ c := min_le_left c 1
  have h₂ : min c 1 ≤ 1 := min_le_right c 1
  nlinarith [mul_le_mul_of_nonneg_right h₁ hX, mul_le_mul_of_nonneg_right h₂ hP]

end Coercive

section Kernel

variable [IsManifold I ∞ M] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M]

/-- **The kernel of a Schrödinger operator is trivial.** On a compact connected manifold without
boundary with a `C¹` Riemannian metric, let `f ≥ 0` be a continuous function that does not vanish
identically. A `C²` function `u` with `Δu = f u` vanishes. -/
theorem eq_zero_of_laplaceBeltrami_eq_mul [PreconnectedSpace M]
    {f u : M → ℝ} (hf : Continuous f) (hf₀ : 0 ≤ f) (hf₁ : f ≠ 0)
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hΔ : ∀ x, laplaceBeltrami I u x = f x * u x) : u = 0 := by
  obtain ⟨c, hc, hcu⟩ :=
    exists_pos_mul_integral_sq_le_integral_norm_sq_mgradient_add_integral_mul_sq (I := I)
      hf hf₀ hf₁
  -- Green's first identity: `∫ f u² dV = ∫ u Δu dV = -∫ ‖∇u‖² dV`.
  have hGreen := integral_mul_laplaceBeltrami (hu.of_le one_le_two)
    (HasCompactSupport.of_compactSpace u) hu
  simp only [hΔ, real_inner_self_eq_norm_sq] at hGreen
  have hfu : (fun x ↦ u x * (f x * u x)) = fun x ↦ f x * u x ^ 2 := by
    ext x
    ring
  rw [hfu] at hGreen
  have hcont : Continuous fun x ↦ u x ^ 2 := hu.continuous.pow 2
  have hX : 0 ≤ ∫ x, u x ^ 2 ∂riemannianVolume I M := integral_nonneg fun x ↦ sq_nonneg _
  have hzero : ∫ x, u x ^ 2 ∂riemannianVolume I M = 0 := by
    have h := hcu u (hu.of_le one_le_two)
    rw [hGreen, add_neg_cancel] at h
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (u x))
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hzero
  ext x
  exact pow_eq_zero_iff two_ne_zero |>.mp
    (congrFun ((hcont.ae_eq_iff_eq _ continuous_zero).mp hae) x)

end Kernel

end TauCeti.Manifold
