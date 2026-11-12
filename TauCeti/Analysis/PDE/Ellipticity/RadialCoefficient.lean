/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Radial coefficient fields

For real numbers `α` and `β`, the coefficient field `TauCeti.PDE.radialCoefficient α β` on `ℝⁿ` is

`a(x) = α I + β x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

with eigenvalue `α + β` in the radial direction and `α` in the tangential directions. It is
symmetric, measurable and bounded, homogeneous of degree `0`, and for `β ≠ 0` discontinuous at the
origin. For `α > 0` and `β ≥ 0` it is uniformly elliptic with constants `α` and `α + β`. Such
fields are the standard sources of explicit singular solutions of elliptic equations with bounded
measurable coefficients, in divergence form (Meyers) and in non-divergence form (Gilbarg–Serrin).

## Main declarations

* `TauCeti.PDE.radialCoefficient`: the coefficient field `α I + β x̂ x̂ᵀ`.
* `TauCeti.PDE.dotProduct_radialCoefficient_mulVec`: its bilinear form.
* `TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le`: its bilinear form is bounded by
  `|α| + |β|`.
* `TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`,
  `TauCeti.PDE.isSymm_radialCoefficient`, `TauCeti.PDE.stronglyMeasurable_radialCoefficient`:
  it is uniformly elliptic with constants `α` and `α + β`, symmetric and measurable.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α β : ℝ}

/-- The coefficient field `a(x) = α I + β x xᵀ / ‖x‖²` on `ℝⁿ`. Its eigenvalue in the radial
direction `x` is `α + β` and in the tangential directions is `α`. At the origin, where the
direction is undefined, it is `α I`. -/
def radialCoefficient (α β : ℝ) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  α • 1 + (β / ‖x‖ ^ 2) • Matrix.vecMulVec x x

/-- The entries of `TauCeti.PDE.radialCoefficient`: `aⁱʲ(x) = α δᵢⱼ + β xᵢ xⱼ / ‖x‖²`. -/
theorem radialCoefficient_apply (x : EuclideanSpace ℝ ι) (i j : ι) :
    radialCoefficient α β x i j = (if i = j then α else 0) + β / ‖x‖ ^ 2 * (x i * x j) := by
  simp [radialCoefficient, Matrix.one_apply, Matrix.vecMulVec_apply]

/-- The bilinear form of the radial coefficient:
`ηᵀ a(x) ξ = α ⟪η, ξ⟫ + β ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`. -/
theorem dotProduct_radialCoefficient_mulVec (x η ξ : EuclideanSpace ℝ ι) :
    η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ) =
      α * ⟪η, ξ⟫_ℝ + β / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ) := by
  have hin : ∀ u v : EuclideanSpace ℝ ι, ⟪u, v⟫_ℝ = u.ofLp ⬝ᵥ v.ofLp := fun u v => by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp only [radialCoefficient, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, op_smul_eq_smul, hin]
  ring

/-- The radial coefficient is symmetric. -/
theorem isSymm_radialCoefficient (x : EuclideanSpace ℝ ι) : (radialCoefficient α β x).IsSymm :=
  Matrix.IsSymm.add (Matrix.isSymm_one.smul _)
    (Matrix.IsSymm.smul (by simp [Matrix.IsSymm, Matrix.transpose_vecMulVec]) _)

/-- The bilinear form of the radial coefficient is bounded by `|α| + |β|`. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le (x η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ (|α| + |β|) * ‖η‖ * ‖ξ‖ := by
  have hcx : |β / ‖x‖ ^ 2| * ‖x‖ ^ 2 ≤ |β| := by
    rcases eq_or_ne ‖x‖ 0 with h | h
    · simp [h]
    · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2),
        div_mul_cancel₀ _ (pow_ne_zero 2 h)]
  rw [dotProduct_radialCoefficient_mulVec]
  calc |α * ⟪η, ξ⟫_ℝ + β / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ)|
      ≤ |α| * (‖η‖ * ‖ξ‖) + |β / ‖x‖ ^ 2| * ((‖η‖ * ‖x‖) * (‖x‖ * ‖ξ‖)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
        · gcongr
          exact abs_real_inner_le_norm _ _
        · rw [abs_mul]
          gcongr <;> exact abs_real_inner_le_norm _ _
    _ = (|α| + |β / ‖x‖ ^ 2| * ‖x‖ ^ 2) * ‖η‖ * ‖ξ‖ := by ring
    _ ≤ (|α| + |β|) * ‖η‖ * ‖ξ‖ := by gcongr

/-- For `α > 0` and `β ≥ 0`, the radial coefficient is uniformly elliptic with constants `α` and
`α + β`. -/
theorem uniformlyEllipticOn_radialCoefficient (hα : 0 < α) (hβ : 0 ≤ β)
    (Ω : Set (EuclideanSpace ℝ ι)) :
    UniformlyEllipticOn Ω (radialCoefficient α β) α (α + β) := by
  refine UniformlyEllipticOn.of_bounds hα (by linarith) (fun x _ ξ => ?_) (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_radialCoefficient_mulVec,
      real_inner_self_eq_norm_sq, real_inner_comm x ξ]
    have : 0 ≤ β / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) :=
      mul_nonneg (div_nonneg hβ (by positivity)) (mul_self_nonneg _)
    linarith
  · simpa [abs_of_pos hα, abs_of_nonneg hβ] using
      abs_dotProduct_radialCoefficient_mulVec_le (α := α) (β := β) x η ξ

/-- The radial coefficient is strongly measurable. -/
theorem stronglyMeasurable_radialCoefficient :
    StronglyMeasurable (radialCoefficient (ι := ι) α β) := by
  have : Measurable (radialCoefficient (ι := ι) α β) := by
    unfold radialCoefficient
    fun_prop
  -- The matrix space is metrizable through its underlying function type.
  exact Measurable.stronglyMeasurable (β := ι → ι → ℝ) this

end PDE

end TauCeti
