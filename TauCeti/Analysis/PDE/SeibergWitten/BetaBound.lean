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
(`TauCeti.Manifold.laplaceBeltrami`). Taubes's coarse estimates include the pointwise bound

`|β|² ≤ (C / r) w₊ + C / r²`,

with `C` independent of `r`: the component `β` is of size `r^(-1/2)` at most, and of size `r⁻¹`
wherever `α` is close to the vacuum `|α| = 1`. This is the form in which the bound on `β` is used
by the cone-defect, mass and defect-energy estimates
(`TauCeti.SeibergWitten.integral_infDist_positiveCone_le`,
`TauCeti.SeibergWitten.exists_mass_integral_wedge_le_of_add_hodgeStar_eq`). This file derives it
by the maximum principle on a compact boundaryless Riemannian manifold from three inputs.

* The projected Weitzenböck inequality for `|α|²`, in the form used for the gradient bound
  `TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`:

  `-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`.
* The projected Weitzenböck inequality for `|β|²`, obtained by pairing
  `∇*∇β + (r / 4)(|α|² + |β|² + 1) β = 𝔟` with `β` and dropping the nonnegative terms `|∇β|²`
  and `(r / 4)|β|⁴`; the error satisfies `|𝔟| ≤ c (|∇_a α| + |α| + |β|)`, as in the `L²` bound
  `TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami`:

  `-Δ|β|² / 2 + (r / 4)(|α|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.
* The coarse bound `|α|² + |β|² ≤ 1 + K₃ / r`
  (`CovariantDerivative.IsMetricCompatible.norm_sq_le_max_of_roughLaplacian_add_eq_zero`).

The potential `(r / 4)(|α|² + 1)` of the second inequality controls `|β|²` up to the cross term
`c |β| |∇_a α|`, which is of size `|∇_a α|² / r` after splitting. The first inequality bounds
`|∇_a α|²` by `(1 / 2) d*d (1 - |α|²)` plus `(r / 4)(1 - |α|²)|α|²` up to a constant. So, with
`κ = 4 c²`, the function `y = |β|² - (κ / r)(1 - |α|²)` satisfies, wherever it is positive,

`(1 / 2) d*d y + (r / 8) y ≤ C₀ / r`,  `C₀ = 4 c² (K₁ + K₃ / 8 + 2 (1 + K₃ / r))`,

where `d*d = -Δ`. At a maximum of `y`, where `Δ y ≤ 0`, this gives `y ≤ 8 C₀ / r²`
(`TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax_of_le_const`),
and hence everywhere, for `r ≥ 1`,

`|β|² ≤ (C / r) w₊ + C / r²`,  `C = 32 c² (K₁ + 3 K₃ + 2)`

(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_sq`). The constants
depend only on `c`, `K₁` and `K₃`, not on `r`, the manifold or the solution.

If the `β` inequality keeps the term `(r / 4)|β|⁴`, that is if it reads
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`, the cross term
`c |β|²` is absorbed by it, and at a maximum of `|β|² + (4 c² / r)|α|²` one gets
`(r / 16)(2 |α|² + 3)|β|² ≤ c² (1 - |α|²)|α|² + c² (3 + 4 K₁) / r` without the coarse bound
(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax`). The coarse bound
`|α|² ≤ 1 + K₃ / r` on `α` alone then gives, for every `r > 0`,

`|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)`

(`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div`). In particular `β = 0` when
`c = 0`.

The sections and their covariant derivatives are arbitrary dependent functions with values in
seminormed groups, such as the fibres of vector bundles. Only `|α|²` and `|β|²` need to be `C²`.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax_of_le_const`: the bound
  on `|β|² - (4 c² / r)(1 - |α|²)` at a local maximum of `|β|² + (4 c² / r)|α|²`, on any
  boundaryless Riemannian manifold.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_sq`: the bound
  `|β|² ≤ (C / r) w₊ + C / r²` on a compact boundaryless Riemannian manifold, for `r ≥ 1`.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div_of_isLocalMax`: the bound on
  `|β|²` at a local maximum of `|β|² + (4 c² / r) |α|²` when the `β` inequality keeps its full
  potential `(r / 4)(|α|² + |β|² + 1)`, without a coarse bound at that point.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_one_sub_add_div`: then
  `|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)` on a compact boundaryless Riemannian manifold,
  for every `r > 0`, from the coarse bound `|α|² ≤ 1 + K₃ / r` on `α` alone.

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

/-- The algebra at a maximum point. Here `a`, `b`, `d` stand for the values of `|α|`, `|β|` and
`|∇_a α|`, and `Lu`, `Lb` for those of the Laplacians of `|α|²` and `|β|²`, at a point where the
Laplacian `Lb + (4 c² / r) Lu` of `|β|² + (4 c² / r) |α|²` is nonpositive. -/
private theorem sq_le_of_add_mul_nonpos {a b d r c K₁ K₃ Lu Lb : ℝ} (hr : 0 < r) (hK₁ : 0 ≤ K₁)
    (hK₃ : 0 ≤ K₃)
    (hu : -(Lu / 2) + d ^ 2 - r / 4 * (1 - a ^ 2) * a ^ 2 ≤ K₁)
    (hb : -(Lb / 2) + r / 4 * (a ^ 2 + 1) * b ^ 2 ≤ c * b * (d + a + b))
    (hmax : Lb + 4 * c ^ 2 / r * Lu ≤ 0) (hC : a ^ 2 + b ^ 2 ≤ 1 + K₃ / r) :
    b ^ 2 ≤ 4 * c ^ 2 / r * (1 - a ^ 2) +
      32 * c ^ 2 * (K₁ + K₃ / 8 + 2 * (1 + K₃ / r)) / r ^ 2 := by
  have hmax' : r * Lb + 4 * c ^ 2 * Lu ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left hmax hr.le
    have e : r * (Lb + 4 * c ^ 2 / r * Lu) = r * Lb + 4 * c ^ 2 * Lu := by field_simp
    linarith
  -- The cross terms `c b d` and `c b (a + b)` are split between `r² b²` and `c²`.
  have h₁ : 16 * r * (c * b * d) ≤ r ^ 2 * b ^ 2 + 64 * c ^ 2 * d ^ 2 := by
    nlinarith [sq_nonneg (r * b - 8 * c * d)]
  have h₂ : 16 * r * (c * b * (a + b)) ≤ r ^ 2 * b ^ 2 + 64 * c ^ 2 * (a + b) ^ 2 := by
    nlinarith [sq_nonneg (r * b - 8 * c * (a + b))]
  have hrC : r * (a ^ 2 + b ^ 2) ≤ r + K₃ := by
    have h := mul_le_mul_of_nonneg_left hC hr.le
    have e : r * (1 + K₃ / r) = r + K₃ := by field_simp
    linarith
  have hab : (a + b) ^ 2 ≤ 2 * (1 + K₃ / r) := by nlinarith [sq_nonneg (a - b)]
  have e₁ := mul_le_mul_of_nonneg_left hb hr.le
  have e₂ := mul_le_mul_of_nonneg_left hu (sq_nonneg c)
  have e₃ := mul_le_mul_of_nonneg_left hrC (sq_nonneg c)
  have e₄ := mul_le_mul_of_nonneg_left hab (sq_nonneg c)
  have e₅ : 0 ≤ c ^ 2 * r * b ^ 2 := by positivity
  -- With `Y = r² y`, combining the two inequalities with `hmax'` gives
  -- `(|α|² + 1 / 2) Y ≤ 16 c² ((|α| + |β|)² + K₁) + 2 c² K₃`.
  set Y := r ^ 2 * b ^ 2 - 4 * c ^ 2 * r * (1 - a ^ 2) with hY
  have key : (a ^ 2 + 1 / 2) * Y ≤ 16 * c ^ 2 * ((a + b) ^ 2 + K₁) + 2 * c ^ 2 * K₃ := by
    rw [hY]
    nlinarith
  have hYle : Y ≤ 32 * c ^ 2 * (K₁ + K₃ / 8 + 2 * (1 + K₃ / r)) := by
    rcases le_or_gt Y 0 with h | h
    · exact h.trans (by positivity)
    · nlinarith [key, e₄, mul_nonneg (sq_nonneg a) h.le]
  have hb₂ : b ^ 2 = 4 * c ^ 2 / r * (1 - a ^ 2) + Y / r ^ 2 := by
    rw [hY]
    field_simp
    ring
  rw [hb₂]
  gcongr

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
  {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F x} {r c K₁ K₃ : ℝ}

/-- **Taubes's bound on `β` at a maximum point.** Suppose that at a point `x₀` the functions
`|α|²` and `|β|²` are `C²` and satisfy the projected Weitzenböck inequalities
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁` and
`-Δ|β|² / 2 + (r / 4)(|α|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`, and the coarse bound
`|α|² + |β|² ≤ 1 + K₃ / r`. If `x₀` is a local maximum of `|β|² + (4 c² / r)|α|²`, then

`|β(x₀)|² ≤ (4 c² / r)(1 - |α(x₀)|²) + 32 c² (K₁ + K₃ / 8 + 2 (1 + K₃ / r)) / r²`. -/
theorem norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax_of_le_const (hr : 0 < r)
    (hK₁ : 0 ≤ K₁) (hK₃ : 0 ≤ K₃) {x₀ : M}
    (hα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖α y‖ ^ 2) x₀)
    (hβ : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖β y‖ ^ 2) x₀)
    (hWα : -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x₀ / 2) + ‖Dα x₀‖ ^ 2 -
      r / 4 * (1 - ‖α x₀‖ ^ 2) * ‖α x₀‖ ^ 2 ≤ K₁)
    (hWβ : -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x₀ / 2) +
      r / 4 * (‖α x₀‖ ^ 2 + 1) * ‖β x₀‖ ^ 2 ≤ c * ‖β x₀‖ * (‖Dα x₀‖ + ‖α x₀‖ + ‖β x₀‖))
    (hC : ‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 ≤ 1 + K₃ / r)
    (hmax : IsLocalMax (fun y ↦ ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2) x₀) :
    ‖β x₀‖ ^ 2 ≤ 4 * c ^ 2 / r * (1 - ‖α x₀‖ ^ 2) +
      32 * c ^ 2 * (K₁ + K₃ / 8 + 2 * (1 + K₃ / r)) / r ^ 2 := by
  exact sq_le_of_add_mul_nonpos hr hK₁ hK₃ hWα hWβ
    (Manifold.laplaceBeltrami_add_mul_nonpos_of_isLocalMax hβ hα hmax) hC

/-- **Taubes's pointwise bound** `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ = max (1 - |α|²) 0` and
`C = 32 c² (K₁ + 3 K₃ + 2)`. On a compact boundaryless Riemannian manifold, suppose `|α|²` and
`|β|²` are `C²` and satisfy the projected Weitzenböck inequalities
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁` and
`-Δ|β|² / 2 + (r / 4)(|α|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)`, and the coarse bound
`|α|² + |β|² ≤ 1 + K₃ / r`, with `r ≥ 1`. Then the bound holds everywhere. -/
theorem norm_sq_le_div_mul_max_one_sub_add_div_sq [CompactSpace M] (hr : 1 ≤ r) (hK₁ : 0 ≤ K₁)
    (hK₃ : 0 ≤ K₃)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2) (hβ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖β y‖ ^ 2)
    (hWα : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) + ‖Dα y‖ ^ 2 -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁)
    (hWβ : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) y / 2) +
      r / 4 * (‖α y‖ ^ 2 + 1) * ‖β y‖ ^ 2 ≤ c * ‖β y‖ * (‖Dα y‖ + ‖α y‖ + ‖β y‖))
    (hC : ∀ y, ‖α y‖ ^ 2 + ‖β y‖ ^ 2 ≤ 1 + K₃ / r) (y : M) :
    ‖β y‖ ^ 2 ≤ 32 * c ^ 2 * (K₁ + 3 * K₃ + 2) / r * max (1 - ‖α y‖ ^ 2) 0 +
      32 * c ^ 2 * (K₁ + 3 * K₃ + 2) / r ^ 2 := by
  have hr₀ : 0 < r := one_pos.trans_le hr
  -- `|β|² + (4 c² / r) |α|²` attains its maximum at some `x₀`.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (hβ.continuous.add (continuous_const.mul hα.continuous)).continuousOn
  have hgy : ‖β y‖ ^ 2 + 4 * c ^ 2 / r * ‖α y‖ ^ 2 ≤
      ‖β x₀‖ ^ 2 + 4 * c ^ 2 / r * ‖α x₀‖ ^ 2 :=
    hx₀ (Set.mem_univ y)
  have hx := norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax_of_le_const hr₀ hK₁ hK₃ (hα x₀)
    (hβ x₀) (hWα x₀) (hWβ x₀) (hC x₀) (hx₀.isLocalMax Filter.univ_mem)
  -- Compare the two terms with those of the claimed bound, using `K₃ / r ≤ K₃`.
  have hw : 4 * c ^ 2 / r * (1 - ‖α y‖ ^ 2) ≤
      32 * c ^ 2 * (K₁ + 3 * K₃ + 2) / r * max (1 - ‖α y‖ ^ 2) 0 := by
    have hc : 4 * c ^ 2 / r ≤ 32 * c ^ 2 * (K₁ + 3 * K₃ + 2) / r := by
      refine div_le_div_of_nonneg_right ?_ hr₀.le
      nlinarith [mul_nonneg (sq_nonneg c) (by positivity : 0 ≤ 32 * K₁ + 96 * K₃ + 60)]
    calc 4 * c ^ 2 / r * (1 - ‖α y‖ ^ 2) ≤ 4 * c ^ 2 / r * max (1 - ‖α y‖ ^ 2) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (le_max_right _ _)
  have hK : 32 * c ^ 2 * (K₁ + K₃ / 8 + 2 * (1 + K₃ / r)) / r ^ 2 ≤
      32 * c ^ 2 * (K₁ + 3 * K₃ + 2) / r ^ 2 := by
    have : K₃ / r ≤ K₃ := div_le_self hK₃ hr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      (by positivity)
  linarith

/-! ### The bound with the full potential of the `β` inequality

Keeping the term `(r / 4)|β|⁴` of the `β` inequality, the coarse bound is only needed for `|α|²`,
and it enters only away from the maximum point. -/

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
  exact sq_le_of_add_div_mul_nonpos hr hK₁ hWβ hWα
    (Manifold.laplaceBeltrami_add_mul_nonpos_of_isLocalMax hβ hα hmax)

/-- **Taubes's pointwise bound** `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ = max (1 - |α|²) 0`.
On a compact boundaryless Riemannian manifold, suppose `|α|²` and `|β|²` are `C²` and satisfy
the projected Weitzenböck inequalities
`-Δ|β|² / 2 + (r / 4)(|α|² + |β|² + 1)|β|² ≤ c |β| (|∇_a α| + |α| + |β|)` and
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, and the coarse bound
`|α|² ≤ 1 + K₃ / r`, with `0 < r`, `0 ≤ K₁` and `0 ≤ K₃`. Then everywhere

`|β|² ≤ (4 c² / r) (w₊ + (4 + 8 K₁ + K₃) / r)`. -/
theorem norm_sq_le_div_mul_max_one_sub_add_div [CompactSpace M] (hr : 0 < r)
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
