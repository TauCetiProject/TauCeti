/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Taubes's pointwise bound on the spinor component `β`

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a solution at parameter `r` has normalized spinor `χ = α u₀ + β`, with `α` a section of the
twisting line `E` and `β` the component orthogonal to the canonical spinor `u₀`. Write
`w₊ = max (1 - |α|²) 0` for the vacuum defect and `Δ = div ∘ grad`
(`TauCeti.Manifold.laplaceBeltrami`). Taubes's coarse estimates include the pointwise bound

`|β|² ≤ (C / r) w₊ + C / r²`,

with `C` independent of `r`, which says that `β` is of order `r^(-1/2)` near the zeros of `α` and
of order `1 / r` where `α` is close to the vacuum. This file derives it by the maximum principle on
a compact boundaryless Riemannian manifold from the projected Weitzenböck inequalities for `α`
and `β`, obtained by pairing the projected equations for `α` and `β` with `α` and `β`:

`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`,
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.

The first is the inequality behind Taubes's gradient bound on `α`
(`TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`); the second is the inequality behind
the `L²` bound on `β` (`TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le`),
with the nonnegative term `|∇β|²` dropped.

The two are combined at a maximum of `f = |β|² - (4 c² / r)(1 - |α|²)`. By the first inequality
the Laplacian of `(4 c² / r)(1 - |α|²)` is at most
`-(8 c² / r)|∇_a α|² + 2 c² (1 - |α|²)|α|² + 8 c² K₁ / r`, and the gain
`-(8 c² / r)|∇_a α|²` absorbs the cross term `c |β| |∇_a α|`, which is the only coupling of `β` to
the large derivative of `α` near its zeros. Where `f ≥ 0` the potential term `(r / 4)|α|²|β|²`
dominates the loss `c² (1 - |α|²)|α|²`, and the remaining terms give
`|β|² ≤ 32 c² (1 + K₁ + |α|²) / r²` at such a maximum
(`TauCeti.SeibergWitten.norm_sq_le_mul_div_sq_of_isLocalMax`). On a compact manifold the first
inequality also gives `|α|² ≤ 1 + 4 K₁ / r` at a maximum of `|α|²`, hence everywhere
(`TauCeti.SeibergWitten.norm_sq_le_one_add_mul_div`), and the two bounds give everywhere

`|β|² ≤ (4 c² / r) w₊ + 4 c² (16 + 12 K₁ + 32 K₁ / r) / r²`

(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_sq`). The constants are explicit in
`c` and `K₁` and, for `r ≥ 1`, bounded independently of `r`, the manifold and the solution.
This is the pointwise bound on `β` that the integrated coarse bounds
(`TauCeti.SeibergWitten.integral_le_of_le_mul_max_one_sub`) and the pointwise curvature bounds of
`TauCeti.SeibergWitten` take as a hypothesis, and the bound on `|α|²` is the coarse hypothesis
`|α|² ≤ 1 + K₃ / r` of the gradient bound on `α`.

The sections are arbitrary families of seminormed groups, such as the fibres of a vector bundle,
and only `|α|²` and `|β|²` need to be `C²`.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_one_add_mul_div`: the bound `|α|² ≤ 1 + 4 K₁ / r` on a
  compact manifold.
* `TauCeti.SeibergWitten.norm_sq_le_mul_div_sq_of_isLocalMax`: the bound on `|β|²` at a local
  maximum of `|β|² + (4 c² / r)|α|²` where `(4 c² / r)(1 - |α|²) ≤ |β|²`.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_sq`: the bound
  `|β|² ≤ (4 c² / r) w₊ + C / r²` on a compact manifold.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten equations and the Weinstein conjecture*, Geom. Topol. 11
  (2007), 2117–2202, Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SeibergWitten

/-- The algebra of the `β` bound at a maximum point. Here `a`, `b`, `d` stand for `|α|`, `|β|`,
`|∇_a α|`, and `La`, `Lb` for the Laplacians of `|α|²` and `|β|²` at a point where the Laplacian
`Lb + (4 c² / r) La` of `|β|² + (4 c² / r)|α|²` is nonpositive and
`(4 c² / r)(1 - |α|²) ≤ |β|²`. -/
private theorem sq_le_mul_div_sq_of_add_mul_nonpos {a b d r c K₁ La Lb : ℝ} (hr : 0 < r)
    (hA : -(La / 2) + d ^ 2 - r / 4 * (1 - a ^ 2) * a ^ 2 ≤ K₁)
    (hB : -(Lb / 2) + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (d + a + b))
    (hmax : Lb + 4 * c ^ 2 / r * La ≤ 0) (hf : 4 * c ^ 2 / r * (1 - a ^ 2) ≤ b ^ 2) :
    b ^ 2 ≤ 32 * c ^ 2 * (1 + K₁ + a ^ 2) / r ^ 2 := by
  -- Clear the denominators of `hmax` and `hf`.
  have hmax' : r * Lb + 4 * c ^ 2 * La ≤ 0 := by
    have h : r * Lb + 4 * c ^ 2 * La = r * (Lb + 4 * c ^ 2 / r * La) := by
      field_simp
    exact h ▸ mul_nonpos_of_nonneg_of_nonpos hr.le hmax
  have hf' : 4 * c ^ 2 * (1 - a ^ 2) ≤ r * b ^ 2 := by
    rwa [div_mul_eq_mul_div, div_le_iff₀' hr] at hf
  -- Where `f ≥ 0`, the potential `(r / 4)|α|²|β|²` dominates the loss `c² (1 - |α|²)|α|²`.
  have hpot : r * a ^ 2 * (4 * c ^ 2 * (1 - a ^ 2)) ≤ r * a ^ 2 * (r * b ^ 2) :=
    mul_le_mul_of_nonneg_left hf' (by positivity)
  -- Scaled by `4 c²`, the inequality for `|α|²` carries the gain `4 c² |∇_a α|²`.
  have hA' : 4 * c ^ 2 * (-(La / 2) + d ^ 2 - r / 4 * (1 - a ^ 2) * a ^ 2) ≤ 4 * c ^ 2 * K₁ :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hB' : r * (-(Lb / 2) + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2) ≤ r * (c * b * (d + a + b)) :=
    mul_le_mul_of_nonneg_left hB hr.le
  -- That gain absorbs the cross term with `|∇_a α|`, and the other cross terms are absorbed by
  -- the potential, by `2 x y ≤ x² + y²`.
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (r * b / 4 - 2 * c * d), sq_nonneg (r * b / 4 - 2 * c * a),
    sq_nonneg (r * b ^ 2 / 2 - c), sq_nonneg c]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {A B F : M → Type*} [∀ x, SeminormedAddCommGroup (A x)] [∀ x, SeminormedAddCommGroup (B x)]
  [∀ x, SeminormedAddCommGroup (F x)]
  {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F x} {r c K₁ : ℝ}

/-- **Taubes's bound on `β` at a maximum point.** Suppose that at a point `x₀` the functions
`|α|²` and `|β|²` are `C²` and satisfy the projected Weitzenböck inequalities
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁` and
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`. If `x₀` is a local
maximum of `|β|² + (4 c² / r)|α|²` where `(4 c² / r)(1 - |α|²) ≤ |β|²`, then
`|β(x₀)|² ≤ 32 c² (1 + K₁ + |α(x₀)|²) / r²`. -/
theorem norm_sq_le_mul_div_sq_of_isLocalMax (hr : 0 < r) {x₀ : M}
    (hα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖α y‖ ^ 2) x₀)
    (hβ : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖β y‖ ^ 2) x₀)
    (hWα : -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x₀ / 2) + ‖Dα x₀‖ ^ 2 -
      r / 4 * (1 - ‖α x₀‖ ^ 2) * ‖α x₀‖ ^ 2 ≤ K₁)
    (hWβ : -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x₀ / 2) +
      r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 + 1) * ‖β x₀‖ ^ 2 ≤
        c * ‖β x₀‖ * (‖Dα x₀‖ + ‖α x₀‖ + ‖β x₀‖))
    (hmax : IsLocalMax (fun y ↦ ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2) x₀)
    (hf : 4 * c ^ 2 / r * (1 - ‖α x₀‖ ^ 2) ≤ ‖β x₀‖ ^ 2) :
    ‖β x₀‖ ^ 2 ≤ 32 * c ^ 2 * (1 + K₁ + ‖α x₀‖ ^ 2) / r ^ 2 := by
  have hcα : ContMDiffAt I 𝓘(ℝ) 2 ((4 * c ^ 2 / r) • fun y ↦ ‖α y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hα
  have hΔ := Manifold.laplaceBeltrami_nonpos_of_isLocalMax (hβ.add hcα) hmax
  rw [Manifold.laplaceBeltrami_add_of_contMDiffAt I hβ hcα,
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hα] at hΔ
  exact sq_le_mul_div_sq_of_add_mul_nonpos hr hWα hWβ hΔ hf

/-- **Taubes's bound** `|α|² ≤ 1 + C / r`. On a compact boundaryless Riemannian manifold, suppose
`|α|²` is `C²` and satisfies `-Δ|α|² / 2 - (r / 4)(1 - |α|²)|α|² ≤ K₁` everywhere, as the projected
Weitzenböck inequality for `α` gives after dropping `|∇_a α|²`. Then `|α|² ≤ 1 + 4 K₁ / r`
everywhere. -/
theorem norm_sq_le_one_add_mul_div [CompactSpace M] (hr : 0 < r)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2)
    (hWα : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁) (y : M) :
    ‖α y‖ ^ 2 ≤ 1 + 4 * K₁ / r := by
  -- At a maximum `x₀` of `|α|²` the Laplacian is nonpositive, so
  -- `(r / 4)(|α|² - 1)|α|² ≤ K₁` there.
  obtain ⟨x₀, -, hx₀⟩ :=
    isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩ hα.continuous.continuousOn
  have hΔ := Manifold.laplaceBeltrami_nonpos_of_isLocalMax (hα x₀)
    (hx₀.isLocalMax Filter.univ_mem)
  refine (hx₀ (Set.mem_univ y)).trans ?_
  have h₁ := hWα x₀
  -- Since `r (|α|² - 1) ≤ r (|α|² - 1)|α|²`, this gives `r (|α|² - 1) ≤ 4 K₁`.
  rw [← sub_le_iff_le_add', le_div_iff₀ hr]
  nlinarith [mul_nonneg hr.le (sq_nonneg (‖α x₀‖ ^ 2 - 1))]

/-- **Taubes's bound** `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ = max (1 - |α|²) 0`. On a compact
boundaryless Riemannian manifold, suppose `|α|²` and `|β|²` are `C²` and satisfy the projected
Weitzenböck inequalities `-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁` and
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`, with `K₁ ≥ 0`. Then
everywhere

`|β|² ≤ (4 c² / r) w₊ + 4 c² (16 + 12 K₁ + 32 K₁ / r) / r²`. -/
theorem norm_sq_le_div_mul_max_one_sub_add_div_sq [CompactSpace M] (hr : 0 < r)
    (hK₁ : 0 ≤ K₁) (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2)
    (hβ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖β y‖ ^ 2)
    (hWα : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) + ‖Dα y‖ ^ 2 -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁)
    (hWβ : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) y / 2) +
      r / 4 * (‖α y‖ ^ 2 + ‖β y‖ ^ 2 + 1) * ‖β y‖ ^ 2 ≤ c * ‖β y‖ * (‖Dα y‖ + ‖α y‖ + ‖β y‖))
    (y : M) :
    ‖β y‖ ^ 2 ≤ 4 * c ^ 2 / r * max (1 - ‖α y‖ ^ 2) 0 +
      4 * c ^ 2 * (16 + 12 * K₁ + 32 * K₁ / r) / r ^ 2 := by
  set κ := 4 * c ^ 2 / r with hκ
  have hκ₀ : 0 ≤ κ := by positivity
  have hC := norm_sq_le_one_add_mul_div (K₁ := K₁) hr hα fun y ↦ by
    nlinarith [hWα y, sq_nonneg ‖Dα y‖]
  -- `|β|² + κ |α|²` attains its maximum at some `x₀`.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (hβ.continuous.add (continuous_const.mul hα.continuous)).continuousOn
  have hgy : ‖β y‖ ^ 2 + κ * ‖α y‖ ^ 2 ≤ ‖β x₀‖ ^ 2 + κ * ‖α x₀‖ ^ 2 := hx₀ (Set.mem_univ y)
  have hw : κ * (1 - ‖α y‖ ^ 2) ≤ κ * max (1 - ‖α y‖ ^ 2) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hκ₀
  have hC₀ : 0 ≤ 4 * c ^ 2 * (16 + 12 * K₁ + 32 * K₁ / r) / r ^ 2 := by positivity
  rcases le_or_gt (κ * (1 - ‖α x₀‖ ^ 2)) (‖β x₀‖ ^ 2) with hf | hf
  · -- At a maximum where `f ≥ 0`, `|β|²` is of order `1 / r²`.
    have hx := norm_sq_le_mul_div_sq_of_isLocalMax hr (hα x₀) (hβ x₀) (hWα x₀) (hWβ x₀)
      (hx₀.isLocalMax Filter.univ_mem) hf
    have hα₀ : 32 * c ^ 2 * (1 + K₁ + ‖α x₀‖ ^ 2) / r ^ 2 ≤
        32 * c ^ 2 * (1 + K₁ + (1 + 4 * K₁ / r)) / r ^ 2 := by
      gcongr
      exact hC x₀
    have hκα : κ * (‖α x₀‖ ^ 2 - 1) ≤ κ * (4 * K₁ / r) :=
      mul_le_mul_of_nonneg_left (by linarith [hC x₀]) hκ₀
    have hsum : 32 * c ^ 2 * (1 + K₁ + (1 + 4 * K₁ / r)) / r ^ 2 + κ * (4 * K₁ / r) =
        4 * c ^ 2 * (16 + 12 * K₁ + 32 * K₁ / r) / r ^ 2 := by
      rw [hκ]
      field_simp
      ring
    linarith
  · -- Otherwise `f < 0` at its maximum, hence everywhere.
    linarith

end TauCeti.SeibergWitten
