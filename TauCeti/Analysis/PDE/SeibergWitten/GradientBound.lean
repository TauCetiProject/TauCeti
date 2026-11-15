/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Taubes's pointwise gradient bounds for the large-parameter spinor components

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

**The joint bound.** Taubes's coarse estimates also bound the derivative of `β`:

`|∇_a α|² + r |∇β|² ≤ C r w₊ + C`,

so `∇β` is of order `r^(-1/2)` near the vacuum. The component `β` solves
`∇*∇β + (r / 4)(1 + |α|² + |β|²) β = 𝔟` (see `TauCeti.Analysis.PDE.SeibergWitten.L2Bounds`),
whose potential exceeds the potential `(r / 4)|α|²` of the equation for `α` by at least `r / 4`.
Its Bochner formula, after dropping `|∇∇β|² ≥ 0` and spending part of the potential on the cross
terms, takes the form

`-Δ|∇β|² / 2 + (r / 4)(θ + |α|²)|∇β|² ≤ K₄ (|∇_a α|² + r w₊ + 1) + K₅ |∇∇_a α| |∇β|`

for some `θ > 0`. The source `r w₊` accounts for the curvature `F_a`, whose coarse bound is
`C r w₊ + C`. The last term comes from the first-order coupling of `β` to `α` in `𝔟`, whose
derivative involves the Hessian `∇∇_a α`. That Hessian is absorbed by the term `|∇∇_a α|²`
which the Bochner formula for `∇_a α` provides,

`-Δ|∇_a α|² / 2 + |∇∇_a α|² ≤ K₂ r (|∇_a α|² + 1)`,

the inequality used above before this term is dropped. As before, the derivation of these
inequalities from the equations is not part of this file; they are the hypotheses.

The comparison function is again `K r (1 - |α|²)`: by the projected Weitzenböck inequality,
`-Δ/2` of it is at least `K r |∇_a α|² - (K r² / 4)|α|²(1 - |α|²) - K r K₁`. Against the larger
potential `(r / 4)(θ + |α|²)` of `r |∇β|²`, half of whose `θ` part goes to the coupling term, this
leaves `(K θ r² / 8)(1 - |α|²)`, which absorbs the source `K₄ r² w₊` when `8 K₄ ≤ θ K`. At a
maximum of `r |∇β|² + μ |∇_a α|² + K r |α|²`, with `2 K₅² ≤ θ μ` so that `μ |∇∇_a α|²` absorbs
the coupling, the gain `K r |∇_a α|²` absorbs the losses `K₄ r |∇_a α|²` and `μ K₂ r |∇_a α|²`, and
`r |∇β|² + μ |∇_a α|² - K r (1 - |α|²)` is bounded independently of `r`
(`TauCeti.SeibergWitten.mul_norm_sq_add_mul_norm_sq_sub_le_of_isLocalMax`). With `μ ≥ 1` this
gives everywhere

`|∇_a α|² + r |∇β|² ≤ K r w₊ + 16 (K₄ + μ K₂ + K K₁) / θ + K K₃`

(`TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le_mul_max_one_sub_add`), the form in which
`TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds` takes the gradient bound.

The sections and their covariant derivatives are arbitrary functions with values in normed
groups. Only `|α|²`, `|∇_a α|²` and `|∇β|²` need to be `C²`.

## Main results

* `TauCeti.SeibergWitten.norm_sq_le_of_isLocalMax`: the bound on `|∇_a α|²` at a local maximum of
  `|∇_a α|² + (K₂ + 1) r |α|²` where `|∇_a α|² ≥ (K₂ + 1) r (1 - |α|²)`, on any boundaryless
  Riemannian manifold.
* `TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`: the gradient bound
  `|∇_a α|² ≤ (K₂ + 1) r w₊ + C` on a compact boundaryless Riemannian manifold.
* `TauCeti.SeibergWitten.mul_norm_sq_add_mul_norm_sq_sub_le_of_isLocalMax`: the bound on
  `r |∇β|² + μ |∇_a α|² - K r (1 - |α|²)` at a local maximum of
  `r |∇β|² + μ |∇_a α|² + K r |α|²`, on any boundaryless Riemannian manifold.
* `TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le_mul_max_one_sub_add`: the joint gradient
  bound `|∇_a α|² + r |∇β|² ≤ K r w₊ + C` on a compact boundaryless Riemannian manifold.

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

/-- The coupling term `r K₅ h b` of the Bochner inequality for `|∇β|²` is absorbed by `μ h²` and
`(r² θ / 8) b²` once `2 K₅² ≤ θ μ`. -/
private theorem mul_mul_mul_le_add_of_two_mul_sq_le {r K₅ h b θ μ : ℝ} (hμ : 0 < μ)
    (hμK₅ : 2 * K₅ ^ 2 ≤ θ * μ) :
    r * K₅ * h * b ≤ μ * h ^ 2 + r ^ 2 * θ / 8 * b ^ 2 := by
  have hT : 0 ≤ (r * b) ^ 2 * (θ * μ / 2 - K₅ ^ 2) := mul_nonneg (sq_nonneg _) (by linarith)
  have h4 : 4 * μ * 0 ≤ 4 * μ * (μ * h ^ 2 + r ^ 2 * θ / 8 * b ^ 2 - r * K₅ * h * b) := by
    linear_combination sq_nonneg (2 * μ * h - r * K₅ * b) + hT
  linarith [le_of_mul_le_mul_left h4 (by positivity)]

/-- The inequality at a maximum point for the joint bound. Here `s = |α|²`, `x = |∇_a α|²`,
`b = |∇β|`, `h = |∇∇_a α|`, and `Ls`, `Lx`, `Ly` are the Laplacians of `s`, `x` and `b²` at a
point where the Laplacian `r Ly + μ Lx + K r Ls` of `r b² + μ x + K r s` is nonpositive. Summing
the three differential inequalities against this condition eliminates the Laplacians. -/
private theorem le_of_add_mul_nonpos_of_two_mul_sq_le
    {s x b h r θ K₁ K₂ K₄ K₅ μ K Ls Lx Ly : ℝ} (hr : 0 < r) (hμ : 0 < μ) (hK : 0 ≤ K)
    (hμK₅ : 2 * K₅ ^ 2 ≤ θ * μ) (hW : -(Ls / 2) + x - r / 4 * (1 - s) * s ≤ K₁)
    (hα : -(Lx / 2) + h ^ 2 ≤ K₂ * r * (x + 1))
    (hβ : -(Ly / 2) + r / 4 * (θ + s) * b ^ 2 ≤
      K₄ * (x + r * max (1 - s) 0 + 1) + K₅ * h * b)
    (hmax : r * Ly + μ * Lx + K * r * Ls ≤ 0) :
    r / 4 * (θ / 2 + s) * b ^ 2 + (K - K₄ - μ * K₂) * x - K₄ * r * max (1 - s) 0 -
      K * r / 4 * (1 - s) * s ≤ K₄ + μ * K₂ + K * K₁ := by
  have h₁ := mul_le_mul_of_nonneg_left hβ hr.le
  have h₂ := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ K * r)
  have h₃ := mul_le_mul_of_nonneg_left hα hμ.le
  have hAM := mul_mul_mul_le_add_of_two_mul_sq_le (r := r) (h := h) (b := b) hμ hμK₅
  refine le_of_mul_le_mul_left ?_ hr
  linear_combination h₁ + h₂ + h₃ + hmax / 2 + hAM

/-- The algebra at a maximum point for the joint bound: the inequality of
`le_of_add_mul_nonpos_of_two_mul_sq_le` bounds `r b² + μ x - K r (1 - s)`, separately near the
vacuum `s ≤ 1` and away from it. -/
private theorem mul_sq_add_mul_sub_le_of_add_mul_nonpos
    {s x b h r θ K₁ K₂ K₃ K₄ K₅ μ K Ls Lx Ly : ℝ}
    (hs₀ : 0 ≤ s) (hx₀ : 0 ≤ x) (hr : 0 < r) (hθ : 0 < θ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hμ : 1 ≤ μ) (hμK₅ : 2 * K₅ ^ 2 ≤ θ * μ)
    (hK : K₄ + μ * K₂ + μ * (θ + 2) / 8 ≤ K) (hK' : 8 * K₄ ≤ θ * K)
    (hW : -(Ls / 2) + x - r / 4 * (1 - s) * s ≤ K₁)
    (hα : -(Lx / 2) + h ^ 2 ≤ K₂ * r * (x + 1))
    (hβ : -(Ly / 2) + r / 4 * (θ + s) * b ^ 2 ≤
      K₄ * (x + r * max (1 - s) 0 + 1) + K₅ * h * b)
    (hmax : r * Ly + μ * Lx + K * r * Ls ≤ 0) (hC : s ≤ 1 + K₃ / r) :
    r * b ^ 2 + μ * x - K * r * (1 - s) ≤ 16 * (K₄ + μ * K₂ + K * K₁) / θ + K * K₃ := by
  have hμ₀ : 0 < μ := by linarith
  have hK₀ : 0 ≤ K := by
    have : 0 ≤ K₄ + μ * K₂ + μ * (θ + 2) / 8 := by positivity
    linarith
  have key := le_of_add_mul_nonpos_of_two_mul_sq_le hr hμ₀ hK₀ hμK₅ hW hα hβ hmax
  set C₀ := K₄ + μ * K₂ + K * K₁ with hC₀
  have hb : 0 ≤ r * b ^ 2 := by positivity
  have hK₃' : 0 ≤ K * K₃ := mul_nonneg hK₀ hK₃
  have h16 : 8 * C₀ / θ + 8 * C₀ / θ = 16 * C₀ / θ := by ring
  have h8 : 0 ≤ 8 * C₀ / θ := by positivity
  rcases le_or_gt s 1 with hs | hs
  · -- Near the vacuum `w₊ = 1 - s`, and `(θ / 2 + s) / 4` times the left side is at most `C₀`.
    rw [max_eq_left (by linarith)] at key
    have hx : 0 ≤ (K - K₄ - μ * K₂ - μ * (θ / 2 + s) / 4) * x := by
      have : μ * s ≤ μ * 1 := mul_le_mul_of_nonneg_left hs hμ₀.le
      exact mul_nonneg (by linarith) hx₀
    have hw : 0 ≤ r * (1 - s) * (K * θ / 8 - K₄) :=
      mul_nonneg (mul_nonneg hr.le (by linarith)) (by linarith)
    have hg : (θ / 2 + s) / 4 * (r * b ^ 2 + μ * x - K * r * (1 - s)) ≤ C₀ := by
      linear_combination key + hx + hw
    rcases le_or_gt (r * b ^ 2 + μ * x - K * r * (1 - s)) 0 with hg₀ | hg₀
    · linarith
    · have : θ / 8 * (r * b ^ 2 + μ * x - K * r * (1 - s)) ≤ C₀ := by
        linear_combination hg + mul_nonneg hs₀ hg₀.le / 4
      have : r * b ^ 2 + μ * x - K * r * (1 - s) ≤ 8 * C₀ / θ := by
        rw [le_div_iff₀ hθ]; linarith
      linarith
  · -- Away from the vacuum `w₊ = 0`, and each of the three terms is at most `C₀`.
    rw [max_eq_right (by linarith)] at key
    have h₅ : 0 ≤ K * r / 4 * (s - 1) * s := by
      have := sub_nonneg.2 hs.le
      positivity
    have h₄ : 0 ≤ (K - K₄ - μ * K₂) * x := mul_nonneg (by nlinarith) hx₀
    have h₆ : 0 ≤ (K - K₄ - μ * K₂ - μ * θ / 8) * x := mul_nonneg (by nlinarith) hx₀
    have h₇ : 0 ≤ r / 4 * (θ / 2 + s) * b ^ 2 := by positivity
    have hb' : r * b ^ 2 ≤ 8 * C₀ / θ := by
      rw [le_div_iff₀ hθ]; linear_combination 8 * key + 8 * h₄ + 8 * h₅ + 2 * mul_nonneg hs₀ hb
    have hx' : μ * x ≤ 8 * C₀ / θ := by
      rw [le_div_iff₀ hθ]; linear_combination 8 * key + 8 * h₆ + 8 * h₅ + 8 * h₇
    have hs' : K * r * (s - 1) ≤ K * K₃ := by
      have : r * (s - 1) ≤ K₃ := by
        have := (le_div_iff₀' hr).1 (by linarith : s - 1 ≤ K₃ / r)
        linarith
      calc K * r * (s - 1) = K * (r * (s - 1)) := by ring
        _ ≤ K * K₃ := mul_le_mul_of_nonneg_left this hK₀
    linarith

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

variable {F₂ G : Type*} [NormedAddCommGroup F₂] [NormedAddCommGroup G] {Dβ : M → F₂}
  {D2α : M → G} {θ μ K K₃ K₄ K₅ : ℝ}

/-- **Taubes's joint gradient bound at a maximum point.** Suppose that at a point `x₀` the
functions `|α|²`, `|∇_a α|²` and `|∇β|²` are `C²` and satisfy the projected Weitzenböck inequality
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, the Bochner inequality
`-Δ|∇_a α|² / 2 + |∇∇_a α|² ≤ K₂ r (|∇_a α|² + 1)`, the Bochner inequality
`-Δ|∇β|² / 2 + (r / 4)(θ + |α|²)|∇β|² ≤ K₄ (|∇_a α|² + r w₊ + 1) + K₅ |∇∇_a α| |∇β|` and the
coarse bound `|α|² ≤ 1 + K₃ / r`. If `x₀` is a local maximum of
`r |∇β|² + μ |∇_a α|² + K r |α|²`, where `μ` and `K` are large enough in terms of `θ`, `K₂`, `K₄`
and `K₅`, then `r |∇β|² + μ |∇_a α|² - K r (1 - |α|²)` is bounded at `x₀` independently of `r`. -/
theorem mul_norm_sq_add_mul_norm_sq_sub_le_of_isLocalMax (hr : 0 < r) (hθ : 0 < θ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hμ : 1 ≤ μ)
    (hμK₅ : 2 * K₅ ^ 2 ≤ θ * μ) (hK : K₄ + μ * K₂ + μ * (θ + 2) / 8 ≤ K)
    (hK' : 8 * K₄ ≤ θ * K) {x₀ : M}
    (hα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖α y‖ ^ 2) x₀)
    (hDα : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖Dα y‖ ^ 2) x₀)
    (hDβ : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖Dβ y‖ ^ 2) x₀)
    (hW : -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x₀ / 2) + ‖Dα x₀‖ ^ 2 -
      r / 4 * (1 - ‖α x₀‖ ^ 2) * ‖α x₀‖ ^ 2 ≤ K₁)
    (hBα : -(Manifold.laplaceBeltrami I (fun y ↦ ‖Dα y‖ ^ 2) x₀ / 2) + ‖D2α x₀‖ ^ 2 ≤
      K₂ * r * (‖Dα x₀‖ ^ 2 + 1))
    (hBβ : -(Manifold.laplaceBeltrami I (fun y ↦ ‖Dβ y‖ ^ 2) x₀ / 2) +
        r / 4 * (θ + ‖α x₀‖ ^ 2) * ‖Dβ x₀‖ ^ 2 ≤
      K₄ * (‖Dα x₀‖ ^ 2 + r * max (1 - ‖α x₀‖ ^ 2) 0 + 1) + K₅ * ‖D2α x₀‖ * ‖Dβ x₀‖)
    (hmax : IsLocalMax (fun y ↦ r * ‖Dβ y‖ ^ 2 + μ * ‖Dα y‖ ^ 2 + K * r * ‖α y‖ ^ 2) x₀)
    (hC : ‖α x₀‖ ^ 2 ≤ 1 + K₃ / r) :
    r * ‖Dβ x₀‖ ^ 2 + μ * ‖Dα x₀‖ ^ 2 - K * r * (1 - ‖α x₀‖ ^ 2) ≤
      16 * (K₄ + μ * K₂ + K * K₁) / θ + K * K₃ := by
  have hcβ : ContMDiffAt I 𝓘(ℝ) 2 (r • fun y ↦ ‖Dβ y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hDβ
  have hcα' : ContMDiffAt I 𝓘(ℝ) 2 (μ • fun y ↦ ‖Dα y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hDα
  have hcα : ContMDiffAt I 𝓘(ℝ) 2 ((K * r) • fun y ↦ ‖α y‖ ^ 2) x₀ := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hα
  have hΔ := Manifold.laplaceBeltrami_nonpos_of_isLocalMax ((hcβ.add hcα').add hcα) hmax
  rw [Manifold.laplaceBeltrami_add_of_contMDiffAt I (hcβ.add hcα') hcα,
    Manifold.laplaceBeltrami_add_of_contMDiffAt I hcβ hcα',
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hDβ,
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hDα,
    Manifold.laplaceBeltrami_smul_of_contMDiffAt I _ hα] at hΔ
  exact mul_sq_add_mul_sub_le_of_add_mul_nonpos (by positivity) (by positivity) hr hθ hK₁ hK₂
    hK₃ hK₄ hμ hμK₅ hK hK' hW hBα hBβ hΔ hC

/-- **Taubes's pointwise gradient bound** `|∇_a α|² + r |∇β|² ≤ C r w₊ + C`, with
`w₊ = max (1 - |α|²) 0`. On a compact boundaryless Riemannian manifold, suppose `|α|²`,
`|∇_a α|²` and `|∇β|²` are `C²` and satisfy everywhere the projected Weitzenböck inequality
`-Δ|α|² / 2 + |∇_a α|² - (r / 4)(1 - |α|²)|α|² ≤ K₁`, the Bochner inequalities
`-Δ|∇_a α|² / 2 + |∇∇_a α|² ≤ K₂ r (|∇_a α|² + 1)` and
`-Δ|∇β|² / 2 + (r / 4)(θ + |α|²)|∇β|² ≤ K₄ (|∇_a α|² + r w₊ + 1) + K₅ |∇∇_a α| |∇β|`, with
`θ > 0`, and the coarse bound `|α|² ≤ 1 + K₃ / r`. Let `μ ≥ 1` with `2 K₅² ≤ θ μ`, and let `K`
satisfy `K₄ + μ K₂ + μ (θ + 2) / 8 ≤ K` and `8 K₄ ≤ θ K`. Then everywhere

`|∇_a α|² + r |∇β|² ≤ K r w₊ + 16 (K₄ + μ K₂ + K K₁) / θ + K K₃`. -/
theorem norm_sq_add_mul_norm_sq_le_mul_max_one_sub_add [CompactSpace M] (hr : 0 < r)
    (hθ : 0 < θ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hμ : 1 ≤ μ)
    (hμK₅ : 2 * K₅ ^ 2 ≤ θ * μ) (hK : K₄ + μ * K₂ + μ * (θ + 2) / 8 ≤ K)
    (hK' : 8 * K₄ ≤ θ * K)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖α y‖ ^ 2) (hDα : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖Dα y‖ ^ 2)
    (hDβ : ContMDiff I 𝓘(ℝ) 2 fun y ↦ ‖Dβ y‖ ^ 2)
    (hW : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) y / 2) + ‖Dα y‖ ^ 2 -
      r / 4 * (1 - ‖α y‖ ^ 2) * ‖α y‖ ^ 2 ≤ K₁)
    (hBα : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖Dα y‖ ^ 2) y / 2) + ‖D2α y‖ ^ 2 ≤
      K₂ * r * (‖Dα y‖ ^ 2 + 1))
    (hBβ : ∀ y, -(Manifold.laplaceBeltrami I (fun y ↦ ‖Dβ y‖ ^ 2) y / 2) +
        r / 4 * (θ + ‖α y‖ ^ 2) * ‖Dβ y‖ ^ 2 ≤
      K₄ * (‖Dα y‖ ^ 2 + r * max (1 - ‖α y‖ ^ 2) 0 + 1) + K₅ * ‖D2α y‖ * ‖Dβ y‖)
    (hC : ∀ y, ‖α y‖ ^ 2 ≤ 1 + K₃ / r) (y : M) :
    ‖Dα y‖ ^ 2 + r * ‖Dβ y‖ ^ 2 ≤ K * r * max (1 - ‖α y‖ ^ 2) 0 +
      (16 * (K₄ + μ * K₂ + K * K₁) / θ + K * K₃) := by
  -- `r |∇β|² + μ |∇_a α|² + K r |α|²` attains its maximum at some `x₀`.
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨y, Set.mem_univ y⟩
    (((continuous_const.mul hDβ.continuous).add (continuous_const.mul hDα.continuous)).add
      (continuous_const.mul hα.continuous)).continuousOn
  have hgy : r * ‖Dβ y‖ ^ 2 + μ * ‖Dα y‖ ^ 2 + K * r * ‖α y‖ ^ 2 ≤
      r * ‖Dβ x₀‖ ^ 2 + μ * ‖Dα x₀‖ ^ 2 + K * r * ‖α x₀‖ ^ 2 :=
    hx₀ (Set.mem_univ y)
  have hx := mul_norm_sq_add_mul_norm_sq_sub_le_of_isLocalMax hr hθ hK₁ hK₂ hK₃ hK₄ hμ hμK₅ hK
    hK' (hα x₀) (hDα x₀) (hDβ x₀) (hW x₀) (hBα x₀) (hBβ x₀) (hx₀.isLocalMax Filter.univ_mem)
    (hC x₀)
  have hK₀ : 0 ≤ K * r := by
    have : 0 ≤ K₄ + μ * K₂ + μ * (θ + 2) / 8 := by positivity
    exact mul_nonneg (by linarith) hr.le
  have hw : K * r * (1 - ‖α y‖ ^ 2) ≤ K * r * max (1 - ‖α y‖ ^ 2) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hK₀
  have hμx : ‖Dα y‖ ^ 2 ≤ μ * ‖Dα y‖ ^ 2 := le_mul_of_one_le_left (by positivity) hμ
  linarith

end TauCeti.SeibergWitten
