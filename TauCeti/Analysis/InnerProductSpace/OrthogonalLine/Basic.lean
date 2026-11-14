/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Covectors and graphs over an orthogonal hyperplane

Let `e` be a unit vector of a real inner product space and `v` a vector of the orthogonal
hyperplane `(ℝ ∙ e)ᗮ` with `‖v‖ ≤ 1`. By Pythagoras in orthogonal line coordinates
(`TauCeti.norm_add_smul_sq`), the vectors `±√(1 - ‖v‖²) e - v` have norm one, so every covector
`L` satisfies `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`. This pointwise bound is what lets the variation
of a function along `e`, weighted by `√(1 - ‖v‖²)`, be combined with its variation in the
transverse direction `-v` without exceeding its total variation.

Orthogonal line coordinates `TauCeti.orthogonalLineEquiv` also identify the graph
`Set.range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` of a scalar function `g : (ℝ ∙ v)ᗮ → ℝ` over
the orthogonal hyperplane of a unit vector `v` with the image of `g.graph`: when `g` is continuous
(and in particular when `g` is Lipschitz), this graph is closed in `E`, and when `g` is
`K`-Lipschitz the parametrization `w ↦ (w : E) + g w • v` is `(1 + K)`-Lipschitz.

## Main results

* `TauCeti.sqrt_mul_abs_apply_sub_apply_le`: `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖` for a covector `L`,
  a unit vector `e` and `v ⊥ e` with `‖v‖ ≤ 1`.
* `TauCeti.lipschitzWith_coe_add_smul`: `w ↦ (w : E) + g w • v` is `(1 + K)`-Lipschitz when
  `‖v‖ = 1` and `g : (ℝ ∙ v)ᗮ → ℝ` is `K`-Lipschitz.
* `TauCeti.isClosed_range_add_smul_of_continuous` and
  `TauCeti.isClosed_range_add_smul_of_lipschitzWith`: a continuous or globally Lipschitz graph over
  `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is closed.
-/

public section

open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A covector `L` and a vector `v ⊥ e` with `‖v‖ ≤ 1` satisfy
`√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`: the left side is `L` applied to `±√(1 - ‖v‖²) e - v`, a vector
of norm one by `TauCeti.norm_add_smul_sq`. -/
theorem sqrt_mul_abs_apply_sub_apply_le (e : E) (he : ‖e‖ = 1) (L : E →L[ℝ] ℝ)
    {v : (ℝ ∙ e)ᗮ} (hv : ‖v‖ ≤ 1) :
    √(1 - ‖v‖ ^ 2) * |L e| - L v ≤ ‖L‖ := by
  have key (σ : ℝ) (hσ : σ ^ 2 = 1) : σ * √(1 - ‖v‖ ^ 2) * L e - L v ≤ ‖L‖ := by
    set z : E := ((-v : (ℝ ∙ e)ᗮ) : E) + (σ * √(1 - ‖v‖ ^ 2)) • e
    have hz : ‖z‖ ^ 2 = 1 := by
      rw [norm_add_smul_sq e he, norm_neg, mul_pow, hσ,
        Real.sq_sqrt (by nlinarith [norm_nonneg v])]
      ring
    calc σ * √(1 - ‖v‖ ^ 2) * L e - L v = L z := by simp [z, sub_eq_neg_add]
      _ ≤ ‖L‖ * 1 := (le_abs_self _).trans (L.le_opNorm_of_le (by nlinarith [norm_nonneg z]))
      _ = ‖L‖ := mul_one _
  rcases le_total 0 (L e) with h | h
  · simpa [abs_of_nonneg h] using key 1 (by norm_num)
  · simpa [abs_of_nonpos h] using key (-1) (by norm_num)

/-- The graph map `w ↦ (w : E) + g w • v` over `(ℝ ∙ v)ᗮ` along a unit vector `v` is
`(1 + K)`-Lipschitz when `g` is `K`-Lipschitz. -/
theorem lipschitzWith_coe_add_smul {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) :
    LipschitzWith (1 + K) (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  refine LipschitzWith.of_dist_le_mul fun w₁ w₂ => ?_
  have hsub : ((w₁ : E) + g w₁ • v) - ((w₂ : E) + g w₂ • v) =
      ((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E) + (g w₁ - g w₂) • v := by
    simp only [Submodule.coe_sub, sub_smul]
    abel
  rw [dist_eq_norm, hsub]
  calc
    ‖((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E) + (g w₁ - g w₂) • v‖
      ≤ ‖((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E)‖ + ‖(g w₁ - g w₂) • v‖ := norm_add_le _ _
    _ = dist w₁ w₂ + dist (g w₁) (g w₂) := by
      rw [Submodule.norm_coe, ← dist_eq_norm, norm_smul, hv, mul_one, Real.norm_eq_abs,
        ← Real.dist_eq]
    _ ≤ 1 * dist w₁ w₂ + K * dist w₁ w₂ := by
      gcongr
      · rw [one_mul]
      · exact hg.dist_le_mul w₁ w₂
    _ = ↑(1 + K) * dist w₁ w₂ := by push_cast; ring

/-- The graph `Set.range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over the orthogonal complement of
a unit vector `v` is closed whenever `g` is continuous (in particular whenever `g` is Lipschitz). -/
theorem isClosed_range_add_smul_of_continuous {v : E} (hv : ‖v‖ = 1) {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : Continuous g) :
    IsClosed (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  have heq : (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) =
      orthogonalLineEquiv v hv '' g.graph := by
    ext z
    simp [Function.graph, eq_comm]
  rw [heq]
  exact (orthogonalLineEquiv v hv).toHomeomorph.isClosed_image.mpr hg.isClosed_graph

/-- A globally Lipschitz graph over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is closed. -/
theorem isClosed_range_add_smul_of_lipschitzWith {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0}
    {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    IsClosed (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) :=
  isClosed_range_add_smul_of_continuous hv hg.continuous

end TauCeti
