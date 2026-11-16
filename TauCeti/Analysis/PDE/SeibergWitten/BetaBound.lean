/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Taubes's pointwise bound on the spinor component `β` at large parameter

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a solution at parameter `r` has normalized spinor `χ = α u₀ + β`, with `α` a section of the
twisting line `E` and `β` the component orthogonal to the canonical spinor `u₀`. Write
`w₊ = max (1 - |α|²) 0` for the vacuum defect and `Δ = div ∘ grad`
(`TauCeti.Manifold.laplaceBeltrami`). Among Taubes's coarse estimates is the pointwise bound

`|β|² ≤ (C / r) w₊ + C / r²`,

with `C` independent of `r`: the component `β` is of order `r^(-1/2)` near the zeros of `α` and
of order `r^(-1)` near the vacuum. This file derives it by the maximum principle on a compact
boundaryless Riemannian manifold from the two projected Weitzenböck inequalities.

* The inequality for `|β|²`, obtained by pairing the projected equation
  `∇*∇β + (r / 4)(|α|² + |β|² + 1) β = 𝔟` with `β`, where `|𝔟| ≤ c (|∇_a α| + |α| + |β|)`:

  `-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.

  This is the hypothesis of the `L²` bound
  `TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami` with its
  nonnegative term `|∇β|²` dropped.
* The inequality for `|α|²`, the hypothesis of the gradient bound
  `TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`:

  `-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`.

The first inequality alone bounds `|β|²` by a constant multiple of `(c² / r²) |∇_a α|²` up to
lower-order terms, which is of order `1 / r` near the zeros of `α`, where `|∇_a α|²` may be of
order `r`. To trade `|∇_a α|²` for the vacuum defect, consider `f = |β|² + (4 c² / r) |α|²`. At a
maximum of `f` its Laplacian is nonpositive, and adding `4 c² / r` times the second inequality to
the first cancels the gradient terms, leaving

`(r / 16) (2 |α|² + 3) |β|² ≤ c² (1 - |α|²) |α|² + c² (3 + 4 K₁) / r`

there. This gives `|β|² ≤ (4 c² / r) (w₊ + 4 (1 + 2 K₁) / r)` at such a maximum
(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax`). Bounding `f` by
its maximum, with the coarse bound `|α|² ≤ 1 + K₃ / r` controlling `f` where `|α| > 1`, gives
everywhere

`|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)`

(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div`). The constants depend only on
`c`, `K₁` and `K₃`, not on `r`, the manifold or the solution. In particular `β = 0` when `c = 0`.

The sections and their covariant derivatives are arbitrary sections of families of seminormed
groups. Only `|α|²` and `|β|²` need to be `C²`.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax`: the bound on
  `|β|²` at a local maximum of `|β|² + (4 c² / r) |α|²`, on any boundaryless Riemannian manifold.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div`: the bound
  `|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)` on a compact boundaryless Riemannian manifold.

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

/-- The cross term of the `β` inequality, split between the potential and the derivative of `α`.
Here `x`, `y`, `z` stand for `|α|`, `|β|`, `|∇_a α|`, and `Lb` for `Δ|β|²`. -/
private theorem neg_div_two_add_mul_sq_mul_sq_add_mul_sq_le {x y z Lb c r : ℝ} (hr : 0 < r)
    (hW : -(Lb / 2) + r / 4 * (x ^ 2 + y ^ 2 + 1) * y ^ 2 ≤ c * y * (z + x + y)) :
    -(Lb / 2) + r / 8 * x ^ 2 * y ^ 2 + 3 * r / 16 * y ^ 2 ≤
      4 * c ^ 2 / r * z ^ 2 + 3 * c ^ 2 / r := by
  -- Each piece of `c y (z + x + y)` is absorbed by completing a square.
  have hz : c * y * z ≤ r / 16 * y ^ 2 + 4 * c ^ 2 / r * z ^ 2 := by
    have : r / 16 * y ^ 2 + 4 * c ^ 2 / r * z ^ 2 - c * y * z =
        (r * y / 4 - 2 * c * z) ^ 2 / r := by
      field_simp
      ring
    linarith [div_nonneg (sq_nonneg (r * y / 4 - 2 * c * z)) hr.le]
  have hx : c * y * x ≤ r / 8 * x ^ 2 * y ^ 2 + 2 * c ^ 2 / r := by
    have : r / 8 * x ^ 2 * y ^ 2 + 2 * c ^ 2 / r - c * y * x = r / 8 * (x * y - 4 * c / r) ^ 2 := by
      field_simp
      ring
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ r / 8) (sq_nonneg (x * y - 4 * c / r))]
  have hyy : c * y * y ≤ r / 4 * y ^ 4 + c ^ 2 / r := by
    have : r / 4 * y ^ 4 + c ^ 2 / r - c * y * y = r / 4 * (y ^ 2 - 2 * c / r) ^ 2 := by
      field_simp
      ring
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ r / 4) (sq_nonneg (y ^ 2 - 2 * c / r))]
  linear_combination hW + hz + hx + hyy

/-- The algebra at a maximum point. Here `x`, `y`, `z` stand for `|α|`, `|β|`, `|∇_a α|`, and
`La`, `Lb` for the Laplacians of `|α|²` and `|β|²` at a point where the Laplacian
`Lb + (4 c² / r) La` of `|β|² + (4 c² / r) |α|²` is nonpositive. -/
private theorem sq_le_of_add_div_mul_nonpos {x y z La Lb c r K₁ : ℝ} (hr : 0 < r)
    (hK₁ : 0 ≤ K₁)
    (hWβ : -(Lb / 2) + r / 4 * (x ^ 2 + y ^ 2 + 1) * y ^ 2 ≤ c * y * (z + x + y))
    (hWα : -(La / 2) + z ^ 2 - r / 4 * (1 - x ^ 2) * x ^ 2 ≤ K₁)
    (hmax : Lb + 4 * c ^ 2 / r * La ≤ 0) :
    y ^ 2 ≤ 4 * c ^ 2 / r * (max (1 - x ^ 2) 0 + 4 * (1 + 2 * K₁) / r) := by
  have hβ := neg_div_two_add_mul_sq_mul_sq_add_mul_sq_le hr hWβ
  have hA : 0 ≤ 4 * c ^ 2 / r := by positivity
  -- Adding `4 c² / r` times the `α` inequality cancels the gradient terms.
  have hα : 4 * c ^ 2 / r * (-(La / 2) + z ^ 2 - r / 4 * (1 - x ^ 2) * x ^ 2) ≤
      4 * c ^ 2 / r * K₁ :=
    mul_le_mul_of_nonneg_left hWα hA
  have hkey : r / 16 * (2 * x ^ 2 + 3) * y ^ 2 ≤
      c ^ 2 * (1 - x ^ 2) * x ^ 2 + c ^ 2 * (3 + 4 * K₁) / r := by
    have e₁ : 4 * c ^ 2 / r * (-(La / 2) + z ^ 2 - r / 4 * (1 - x ^ 2) * x ^ 2) =
        -(4 * c ^ 2 / r * La / 2) + 4 * c ^ 2 / r * z ^ 2 - c ^ 2 * (1 - x ^ 2) * x ^ 2 := by
      field_simp
    rw [e₁] at hα
    linear_combination hβ + hα + hmax / 2
  -- Dividing by `(r / 16) (2 x² + 3)` gives the bound.
  set w := max (1 - x ^ 2) 0
  have hw₀ : 0 ≤ w := le_max_right _ _
  have hw₁ : 1 - x ^ 2 ≤ w := le_max_left _ _
  have hpos : 0 < r / 16 * (2 * x ^ 2 + 3) := by positivity
  have hwx : (1 - x ^ 2) * x ^ 2 ≤ (2 * x ^ 2 + 3) / 4 * w := by
    rcases le_or_gt (x ^ 2) 1 with h | h
    · nlinarith [sq_nonneg x]
    · nlinarith [sq_nonneg x]
  have hrhs : c ^ 2 * (1 - x ^ 2) * x ^ 2 + c ^ 2 * (3 + 4 * K₁) / r ≤
      r / 16 * (2 * x ^ 2 + 3) * (4 * c ^ 2 / r * (w + 4 * (1 + 2 * K₁) / r)) := by
    have e : r / 16 * (2 * x ^ 2 + 3) * (4 * c ^ 2 / r * (w + 4 * (1 + 2 * K₁) / r)) =
        c ^ 2 * ((2 * x ^ 2 + 3) / 4 * w) + c ^ 2 * ((2 * x ^ 2 + 3) * (1 + 2 * K₁)) / r := by
      field_simp
      ring
    rw [e]
    have h₁ : c ^ 2 * ((1 - x ^ 2) * x ^ 2) ≤ c ^ 2 * ((2 * x ^ 2 + 3) / 4 * w) :=
      mul_le_mul_of_nonneg_left hwx (sq_nonneg c)
    have h₂ : c ^ 2 * (3 + 4 * K₁) / r ≤ c ^ 2 * ((2 * x ^ 2 + 3) * (1 + 2 * K₁)) / r := by
      gcongr
      nlinarith [sq_nonneg x]
    linear_combination h₁ + h₂
  exact le_of_mul_le_mul_left (hkey.trans hrhs) hpos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {A B F : M → Type*} [∀ x, SeminormedAddCommGroup (A x)] [∀ x, SeminormedAddCommGroup (B x)]
  [∀ x, SeminormedAddCommGroup (F x)]
  {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F x} {c r K₁ : ℝ}

/-- **Taubes's `β` bound at a maximum point.** Suppose that at a point `x₀` the functions
`|α|²` and `|β|²` are `C²` and satisfy the projected Weitzenböck inequalities
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)` and
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, with `0 < r` and `0 ≤ K₁`. If `x₀` is a
local maximum of `|β|² + (4 c² / r) |α|²`, then
`|β(x₀)|² ≤ (4 c² / r) (max (1 - |α(x₀)|²) 0 + 4 (1 + 2 K₁) / r)`. -/
theorem norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax (hr : 0 < r) (hK₁ : 0 ≤ K₁)
    {x₀ : M} (hα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖α y‖ ^ 2) x₀)
    (hβ : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖β y‖ ^ 2) x₀)
    (hWβ : -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x₀ / 2) +
        r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 + 1) * ‖β x₀‖ ^ 2 ≤
      c * ‖β x₀‖ * (‖Dα x₀‖ + ‖α x₀‖ + ‖β x₀‖))
    (hWα : -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x₀ / 2) + ‖Dα x₀‖ ^ 2 -
      r / 4 * (1 - ‖α x₀‖ ^ 2) * ‖α x₀‖ ^ 2 ≤ K₁)
    (hmax : IsLocalMax (fun y ↦ ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2) x₀) :
    ‖β x₀‖ ^ 2 ≤ 4 * c ^ 2 / r * (max (1 - ‖α x₀‖ ^ 2) 0 + 4 * (1 + 2 * K₁) / r) := by
  have hcα : ContMDiffAt I 𝓘(ℝ) 2 ((4 * c ^ 2 / r) • fun y ↦ ‖α y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hα
  have hf : (fun y ↦ ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2) =
      (fun y ↦ ‖β y‖ ^ 2) + (4 * c ^ 2 / r) • fun y ↦ ‖α y‖ ^ 2 := by
    ext; simp
  have hΔ := Manifold.laplaceBeltrami_nonpos_of_isLocalMax (hβ.add hcα) (hf ▸ hmax)
  rw [Manifold.laplaceBeltrami_add_of_contMDiffAt I hβ hcα,
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hα] at hΔ
  exact sq_le_of_add_div_mul_nonpos hr hK₁ hWβ hWα hΔ

/-- **Taubes's pointwise bound** `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ = max (1 - |α|²) 0`.
On a compact boundaryless Riemannian manifold, suppose `|α|²` and `|β|²` are `C²` and satisfy
the projected Weitzenböck inequalities
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)` and
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, and the coarse bound
`|α|² ≤ 1 + K₃ / r`, with `0 < r`, `0 ≤ K₁` and `0 ≤ K₃`. Then everywhere

`|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)`. -/
theorem norm_sq_le_div_mul_max_one_sub_add_div [CompactSpace M] {K₃ : ℝ} (hr : 0 < r)
    (hK₁ : 0 ≤ K₁) (hK₃ : 0 ≤ K₃)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2) (hβ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖β y‖ ^ 2)
    (hWβ : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) y / 2) +
        r / 4 * (‖α y‖ ^ 2 + ‖β y‖ ^ 2 + 1) * ‖β y‖ ^ 2 ≤
      c * ‖β y‖ * (‖Dα y‖ + ‖α y‖ + ‖β y‖))
    (hWα : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) + ‖Dα y‖ ^ 2 -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁)
    (hC : ∀ y, ‖α y‖ ^ 2 ≤ 1 + K₃ / r) (y : M) :
    ‖β y‖ ^ 2 ≤ 4 * c ^ 2 / r * (max (1 - ‖α y‖ ^ 2) 0 + (4 + 8 * K₁ + K₃) / r) := by
  -- `|β|² + (4 c² / r) |α|²` attains its maximum at some `x₀`.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (hβ.continuous.add (continuous_const.mul hα.continuous)).continuousOn
  have hfy : ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2 ≤
      ‖β x₀‖ ^ 2 + 4 * c ^ 2 / r * ‖α x₀‖ ^ 2 :=
    hx₀ (Set.mem_univ y)
  have hx := norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax hr hK₁ (hα x₀) (hβ x₀)
    (hWβ x₀) (hWα x₀) (hx₀.isLocalMax Filter.univ_mem)
  have hA : 0 ≤ 4 * c ^ 2 / r := by positivity
  -- At the maximum, `w₊ + |α|² = max 1 |α|² ≤ 1 + K₃ / r`.
  have hmax₀ : max (1 - ‖α x₀‖ ^ 2) 0 + ‖α x₀‖ ^ 2 ≤ 1 + K₃ / r := by
    rcases le_total (1 - ‖α x₀‖ ^ 2) 0 with h | h
    · rw [max_eq_right h]; linarith [hC x₀]
    · rw [max_eq_left h]; linarith [div_nonneg hK₃ hr.le]
  have hw : 1 - ‖α y‖ ^ 2 ≤ max (1 - ‖α y‖ ^ 2) 0 := le_max_left _ _
  -- Bounding `|β(y)|² + (4 c² / r) |α(y)|²` by its value at `x₀`.
  have h₁ : 4 * c ^ 2 / r * (max (1 - ‖α x₀‖ ^ 2) 0 + ‖α x₀‖ ^ 2) ≤
      4 * c ^ 2 / r * (1 + K₃ / r) :=
    mul_le_mul_of_nonneg_left hmax₀ hA
  have h₂ : 4 * c ^ 2 / r * (1 - ‖α y‖ ^ 2) ≤ 4 * c ^ 2 / r * max (1 - ‖α y‖ ^ 2) 0 :=
    mul_le_mul_of_nonneg_left hw hA
  linear_combination hfy + hx + h₁ + h₂

end TauCeti.SeibergWitten
