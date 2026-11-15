/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Taubes's pointwise gradient bound for the large-parameter spinor component `α`

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a solution at parameter `r` has normalized spinor `χ = α u₀ + β`, with `α` a section of the
twisting line `E` and `β` the component orthogonal to the canonical spinor `u₀`. Write
`w₊ = max (1 - |α|²) 0` for the vacuum defect and `Δ = div ∘ grad`
(`TauCeti.Manifold.laplaceBeltrami`). Taubes's coarse estimates include the pointwise gradient
bound

`|∇_a α|² ≤ C r w₊ + C`,

with `C` independent of `r`, which says that `∇_a α` is of order one wherever `α` is close to the
vacuum `|α| = 1`, while near the zeros of `α` it may grow like `√r`, the inverse of the length
scale of the vortex cores. This file derives it by the maximum principle on a compact
boundaryless Riemannian manifold from two differential inequalities.

* The projected Weitzenböck inequality for `|α|²`, obtained by pairing the projected equation
  `∇*∇α + (r / 4)(|χ|² - 1) α = 𝔞` with `α`, namely
  `-Δ|α|² / 2 + |∇_a α|² + (r / 4)(|α|² + |β|² - 1)|α|² = Re ⟨𝔞, α⟩`. Dropping the nonnegative
  term `(r / 4)|β|²|α|²` and bounding `Re ⟨𝔞, α⟩` by a constant `K₁`, as is possible once `|α|`,
  `|β|` and `|∇β|` are bounded, it reads

  `-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`.
* A lower bound on the Laplacian of `x = |∇_a α|²`,

  `-K₂ r (|∇_a α|² + 1) ≤ Δ|∇_a α|² / 2`.

  This is what the Bochner formula for `∇_a α` gives after dropping `|∇∇_a α|² ≥ 0`, under
  Taubes's a priori bounds at the length scale `r^(-1/2)`, `|χ| ≤ C`, `|∇β| ≤ C` and
  `|F_a| ≤ C r`: the potential `(r / 4)(|χ|² - 1)`, the curvature `F_a`, the divergence
  `d* F_a`, which the curvature equation bounds by `C r (|∇_a α| + |∇β| + 1)`, and the
  derivatives of `|χ|²` and of the forcing then contribute at most `C r (|∇_a α|² + 1)`.

The second inequality alone allows `|∇_a α|²` to be of order `r` everywhere. The first one
improves this where `α` is near the vacuum: there `r (1 - |α|²)` is a supersolution whose
Laplacian is bounded above by `-2 r |∇_a α|²` up to lower-order terms. At a maximum of
`f = |∇_a α|² - (K₂ + 1) r (1 - |α|²)` the term `2 (K₂ + 1) r |∇_a α|²` coming from the first
inequality dominates the loss `2 K₂ r |∇_a α|²` allowed by the second, while the cross term
`(K₂ + 1) r² (1 - |α|²) |α|² / 2` is at most `r |∇_a α|² / 2` wherever `f ≥ 0`. This gives
`|∇_a α|² ≤ 4 (K₁ + K₂ + K₁ K₂) / 3` at such a maximum
(`TauCeti.SeibergWitten.norm_sq_le_of_isLocalMax`). Bounding `f` by its maximum, with the
coarse bound `|α|² ≤ 1 + K₃ / r` controlling `f` where `|α| > 1`, gives everywhere

`|∇_a α|² ≤ (K₂ + 1) r w₊ + 4 (K₁ + K₂ + K₁ K₂) / 3 + (K₂ + 1) K₃`

(`TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`). The constants depend only on `K₁`,
`K₂` and `K₃`, not on `r`, the manifold or the solution.

The sections and their covariant derivatives are arbitrary functions with values in normed
groups. Only `|α|²` and `|∇_a α|²` need to be `C²`.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_of_isLocalMax`: the bound on `|∇_a α|²` at a local maximum of
  `|∇_a α|² + (K₂ + 1) r |α|²` where `|∇_a α|² ≥ (K₂ + 1) r (1 - |α|²)`, on any boundaryless
  Riemannian manifold.
* `TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`: the gradient bound
  `|∇_a α|² ≤ (K₂ + 1) r w₊ + C` on a compact boundaryless Riemannian manifold.

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

/-- The algebra at a maximum point. Here `u = |α|²`, `x = |∇_a α|²`, and `Lu`, `Lx`
are the Laplacians of `u` and `x` at a point where the Laplacian `Lx + (K₂ + 1) r Lu` of
`x + (K₂ + 1) r u` is nonpositive and `(K₂ + 1) r (1 - u) ≤ x`. -/
private theorem le_of_add_mul_nonpos {u x r K₁ K₂ Lu Lx : ℝ} (hu₀ : 0 ≤ u) (hx₀ : 0 ≤ x)
    (hr : 0 < r) (hK₂ : 0 ≤ K₂)
    (hu : -(Lu / 2) + x - r / 4 * (1 - u) * u ≤ K₁) (hx : -(K₂ * r * (x + 1)) ≤ Lx / 2)
    (hmax : Lx + (K₂ + 1) * r * Lu ≤ 0) (hf : (K₂ + 1) * r * (1 - u) ≤ x) :
    x ≤ 4 / 3 * (K₁ + K₂ + K₁ * K₂) := by
  have hM : 0 ≤ (K₂ + 1) * r := by positivity
  -- Where `f ≥ 0`, the cross term `(K₂ + 1) r (1 - u) u` is at most `x`.
  have hw : (K₂ + 1) * r * (1 - u) * u ≤ x := by
    rcases le_or_gt u 1 with h | h
    · calc (K₂ + 1) * r * (1 - u) * u ≤ x * u := mul_le_mul_of_nonneg_right hf hu₀
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left h hx₀
        _ = x := mul_one x
    · have : (K₂ + 1) * r * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM (by linarith)
      linarith [mul_nonpos_of_nonpos_of_nonneg this hu₀]
  -- Combining the two inequalities with `hmax` leaves `r (3 x / 4 - K₂ - (K₂ + 1) K₁) ≤ 0`.
  have h₁ : (K₂ + 1) * r * (x - r / 4 * (1 - u) * u - K₁) ≤ (K₂ + 1) * r * (Lu / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  have h₂ : r / 4 * ((K₂ + 1) * r * (1 - u) * u) ≤ r / 4 * x :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have h₄ : r * (3 / 4 * x - K₂ - (K₂ + 1) * K₁) ≤ r * 0 := by
    linear_combination hx + h₁ + h₂ + hmax / 2
  linarith [le_of_mul_le_mul_left h₄ hr]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {A F : Type*} [NormedAddCommGroup A] [NormedAddCommGroup F]
  {α : M → A} {Dα : M → F} {r K₁ K₂ : ℝ}

/-- **Taubes's gradient bound at a maximum point.** Suppose that at a point `x₀` the functions
`|α|²` and `x = |∇_a α|²` are `C²` and satisfy the projected Weitzenböck inequality
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁` and the bound
`-K₂ r (|∇_a α|² + 1) ≤ Δ|∇_a α|² / 2`. If `x₀` is a local maximum of
`|∇_a α|² + (K₂ + 1) r |α|²` where `(K₂ + 1) r (1 - |α|²) ≤ |∇_a α|²`, the gradient is bounded
independently of `r`: `|∇_a α(x₀)|² ≤ 4 (K₁ + K₂ + K₁ K₂) / 3`. -/
theorem norm_sq_le_of_isLocalMax (hr : 0 < r) (hK₂ : 0 ≤ K₂) {x₀ : M}
    (hα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖α y‖ ^ 2) x₀)
    (hDα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖Dα y‖ ^ 2) x₀)
    (hW : -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x₀ / 2) + ‖Dα x₀‖ ^ 2 -
      r / 4 * (1 - ‖α x₀‖ ^ 2) * ‖α x₀‖ ^ 2 ≤ K₁)
    (hB : -(K₂ * r * (‖Dα x₀‖ ^ 2 + 1)) ≤
      Manifold.laplaceBeltrami I (fun y ↦ ‖Dα y‖ ^ 2) x₀ / 2)
    (hmax : IsLocalMax (fun y ↦ ‖Dα y‖ ^ 2 + (K₂ + 1) * r * ‖α y‖ ^ 2) x₀)
    (hf : (K₂ + 1) * r * (1 - ‖α x₀‖ ^ 2) ≤ ‖Dα x₀‖ ^ 2) :
    ‖Dα x₀‖ ^ 2 ≤ 4 / 3 * (K₁ + K₂ + K₁ * K₂) := by
  have hcα : ContMDiffAt I 𝓘(ℝ) 2 (((K₂ + 1) * r) • fun y ↦ ‖α y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hα
  have hΔ := Manifold.laplaceBeltrami_nonpos_of_isLocalMax (hDα.add hcα) hmax
  rw [Manifold.laplaceBeltrami_add_of_contMDiffAt I hDα hcα,
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hα] at hΔ
  exact le_of_add_mul_nonpos (by positivity) (by positivity) hr hK₂ hW hB hΔ hf

/-- **Taubes's pointwise gradient bound** `|∇_a α|² ≤ C r w₊ + C`, with `w₊ = max (1 - |α|²) 0`.
On a compact boundaryless Riemannian manifold, suppose `|α|²` and `|∇_a α|²` are `C²` and satisfy
the projected Weitzenböck inequality
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, the bound
`-K₂ r (|∇_a α|² + 1) ≤ Δ|∇_a α|² / 2` and the coarse bound `|α|² ≤ 1 + K₃ / r`. Then everywhere

`|∇_a α|² ≤ (K₂ + 1) r w₊ + 4 (K₁ + K₂ + K₁ K₂) / 3 + (K₂ + 1) K₃`. -/
theorem norm_sq_le_mul_max_one_sub_add [CompactSpace M] {K₃ : ℝ} (hr : 0 < r) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2) (hDα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖Dα y‖ ^ 2)
    (hW : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) + ‖Dα y‖ ^ 2 -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁)
    (hB : ∀ y, -(K₂ * r * (‖Dα y‖ ^ 2 + 1)) ≤
      Manifold.laplaceBeltrami I (fun y ↦ ‖Dα y‖ ^ 2) y / 2)
    (hC : ∀ y, ‖α y‖ ^ 2 ≤ 1 + K₃ / r) (y : M) :
    ‖Dα y‖ ^ 2 ≤ (K₂ + 1) * r * max (1 - ‖α y‖ ^ 2) 0 +
      (4 / 3 * (K₁ + K₂ + K₁ * K₂) + (K₂ + 1) * K₃) := by
  -- `|∇_a α|² + (K₂ + 1) r |α|²` attains its maximum at some `x₀`.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (hDα.continuous.add (continuous_const.mul hα.continuous)).continuousOn
  have hgy : ‖Dα y‖ ^ 2 + (K₂ + 1) * r * ‖α y‖ ^ 2 ≤
      ‖Dα x₀‖ ^ 2 + (K₂ + 1) * r * ‖α x₀‖ ^ 2 :=
    hx₀ (Set.mem_univ y)
  have hM : 0 ≤ (K₂ + 1) * r := by positivity
  have hw : (K₂ + 1) * r * (1 - ‖α y‖ ^ 2) ≤ (K₂ + 1) * r * max (1 - ‖α y‖ ^ 2) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hM
  have hC' : (K₂ + 1) * r * ‖α x₀‖ ^ 2 ≤ (K₂ + 1) * r + (K₂ + 1) * K₃ := by
    calc (K₂ + 1) * r * ‖α x₀‖ ^ 2 ≤ (K₂ + 1) * r * (1 + K₃ / r) :=
          mul_le_mul_of_nonneg_left (hC x₀) hM
      _ = (K₂ + 1) * r + (K₂ + 1) * K₃ := by field_simp
  have hK : 0 ≤ 4 / 3 * (K₁ + K₂ + K₁ * K₂) + (K₂ + 1) * K₃ := by positivity
  rcases le_or_gt ((K₂ + 1) * r * (1 - ‖α x₀‖ ^ 2)) (‖Dα x₀‖ ^ 2) with hf | hf
  · -- At a maximum where `f ≥ 0`, the gradient is bounded independently of `r`.
    have hx := norm_sq_le_of_isLocalMax hr hK₂ (hα x₀) (hDα x₀) (hW x₀) (hB x₀)
      (hx₀.isLocalMax Filter.univ_mem) hf
    linarith
  · -- Otherwise `f < 0` at its maximum, hence everywhere.
    linarith

end TauCeti.SeibergWitten
