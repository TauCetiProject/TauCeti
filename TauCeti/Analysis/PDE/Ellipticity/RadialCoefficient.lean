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
import TauCeti.LinearAlgebra.Projectivization.Projector

/-!
# Radially structured coefficient fields

For real `α` and `β` let `a = TauCeti.PDE.radialCoefficient α β` be the coefficient field on `ℝⁿ`

`a(x) = α I + β x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

whose eigenvalue in the radial direction `x̂` is `α + β` and in the directions orthogonal to `x`
is `α`; here `x̂ x̂ᵀ` is the rank-one projector `TauCeti.rankOneProjector x` onto the line
through `x`. The field is measurable and symmetric, constant on every punctured line through the
origin, uniformly elliptic with constants `α` and `α + β` for `α > 0` and `β ≥ 0` and with
constants `α + β` and `α` for `β ≤ 0 < α + β`, and, when two
rays carry different values, it has no limit at the origin. Meyers' planar coefficient field
`TauCeti.PDE.meyersCoefficient` and the coefficient field of
`TauCeti.PDE.exists_radialCoefficient_not_exists_wkp` are of this form.

## Main declarations

* `TauCeti.PDE.radialCoefficient`: the coefficient field `α I + β x̂ x̂ᵀ`.
* `TauCeti.PDE.dotProduct_radialCoefficient_mulVec`: its bilinear form
  `α ⟪η, ξ⟫ + β ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`, bounded by `(|α| + |β|) ‖η‖ ‖ξ‖`
  (`TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le`).
* `TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`: for `α > 0` and `β ≥ 0` it is uniformly
  elliptic with constants `α` and `α + β`;
  `TauCeti.PDE.uniformlyEllipticOn_radialCoefficient_of_nonpos`: for `β ≤ 0 < α + β`, with
  constants `α + β` and `α`, from the sharp bound `α ‖η‖ ‖ξ‖` on its bilinear form
  (`TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le_of_nonpos`).
* `TauCeti.PDE.not_exists_tendsto_radialCoefficient_of_ne`: if it takes different values at two
  points whose open rays lie in `s`, it has no limit at the origin within `s`;
  `TauCeti.PDE.not_exists_tendsto_radialCoefficient`: for `n ≥ 2` and `β ≠ 0` it has no limit at
  the origin.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology Matrix

namespace TauCeti

namespace PDE

variable {n : ℕ} {α β : ℝ}

/-- The coefficient field `a(x) = α I + β x xᵀ / ‖x‖²` on `ℝⁿ`, where `x xᵀ / ‖x‖²` is the
rank-one projector `TauCeti.rankOneProjector x` onto the line through `x`. Its eigenvalue in the
radial direction `x` is `α + β` and in the directions orthogonal to `x` is `α`. At the origin,
where the direction is undefined, it is `α I`. -/
def radialCoefficient (α β : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  α • 1 + β • rankOneProjector (WithLp.ofLp x)

/-- The entries of `TauCeti.PDE.radialCoefficient`: `aᵢⱼ(x) = α δᵢⱼ + β xᵢ xⱼ / ‖x‖²`. -/
theorem radialCoefficient_apply_apply (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    radialCoefficient α β x i j =
      α * (if i = j then 1 else 0) + β / ‖x‖ ^ 2 * (x i * x j) := by
  have hx : WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm
  simp only [radialCoefficient, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    rankOneProjector_apply, hx, smul_eq_mul]
  ring

/-- Unfolding `TauCeti.PDE.radialCoefficient` with the norm in place of the dot product. -/
theorem radialCoefficient_apply (x : EuclideanSpace ℝ (Fin n)) :
    radialCoefficient α β x = α • 1 + (β / ‖x‖ ^ 2) • Matrix.vecMulVec x x := by
  ext i j
  simp [radialCoefficient_apply_apply, Matrix.one_apply, Matrix.vecMulVec_apply]

/-- The radial coefficient is symmetric. -/
theorem isSymm_radialCoefficient (x : EuclideanSpace ℝ (Fin n)) :
    (radialCoefficient α β x).IsSymm :=
  (Matrix.isSymm_one.smul α).add ((isSymm_rankOneProjector _).smul β)

/-- The bilinear form of the radial coefficient:
`ηᵀ a(x) ξ = α ⟪η, ξ⟫ + β ⟪η, x⟫ ⟪x, ξ⟫ / ‖x‖²`. -/
theorem dotProduct_radialCoefficient_mulVec (x η ξ : EuclideanSpace ℝ (Fin n)) :
    η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ) =
      α * ⟪η, ξ⟫_ℝ + β / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ) := by
  simp only [dotProduct, Matrix.mulVec, radialCoefficient_apply_apply, add_mul, ite_mul,
    zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_add, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The bilinear form of the radial coefficient is bounded by `|α| + |β|`. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le (x η ξ : EuclideanSpace ℝ (Fin n)) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ (|α| + |β|) * ‖η‖ * ‖ξ‖ := by
  have hcx : |β / ‖x‖ ^ 2| * ‖x‖ ^ 2 ≤ |β| := by
    rcases eq_or_ne ‖x‖ 0 with h | h
    · simp [h]
    · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2),
        div_mul_cancel₀ _ (pow_ne_zero 2 h)]
  rw [dotProduct_radialCoefficient_mulVec]
  calc |α * ⟪η, ξ⟫_ℝ + β / ‖x‖ ^ 2 * (⟪η, x⟫_ℝ * ⟪x, ξ⟫_ℝ)|
      ≤ |α| * (‖η‖ * ‖ξ‖) + |β / ‖x‖ ^ 2| * ((‖η‖ * ‖x‖) * (‖x‖ * ‖ξ‖)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (abs_real_inner_le_norm _ _)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)) (abs_nonneg _)
    _ = (|α| + |β / ‖x‖ ^ 2| * ‖x‖ ^ 2) * ‖η‖ * ‖ξ‖ := by ring
    _ ≤ (|α| + |β|) * ‖η‖ * ‖ξ‖ := by gcongr

/-- For `α > 0` and `β ≥ 0`, the radial coefficient is uniformly elliptic with constants `α` and
`α + β`, so its ellipticity ratio is `(α + β) / α`. -/
theorem uniformlyEllipticOn_radialCoefficient (hα : 0 < α) (hβ : 0 ≤ β)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    UniformlyEllipticOn Ω (radialCoefficient α β) α (α + β) := by
  refine UniformlyEllipticOn.of_bounds hα (by linarith) (fun x _ ξ => ?_) (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_radialCoefficient_mulVec,
      real_inner_self_eq_norm_sq, real_inner_comm x ξ]
    have : 0 ≤ β / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) :=
      mul_nonneg (div_nonneg hβ (by positivity)) (mul_self_nonneg _)
    linarith
  · simpa [abs_of_pos hα, abs_of_nonneg hβ] using
      abs_dotProduct_radialCoefficient_mulVec_le (α := α) (β := β) x η ξ

/-- For `β ≤ 0` and `2 α + β ≥ 0`, so that `|α + β| ≤ α`, the bilinear form of the radial
coefficient is bounded by its tangential eigenvalue: `|ηᵀ a(x) ξ| ≤ α ‖η‖ ‖ξ‖`. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le_of_nonpos (hβ : β ≤ 0) (hαβ : 0 ≤ 2 * α + β)
    (x η ξ : EuclideanSpace ℝ (Fin n)) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ α * ‖η‖ * ‖ξ‖ := by
  have hα : 0 ≤ α := by linarith
  -- Write `ηᵀ a(x) ξ = ⟪η, α ξ + t x⟫` and show `‖α ξ + t x‖ ≤ α ‖ξ‖`.
  set t : ℝ := β / ‖x‖ ^ 2 * ⟪x, ξ⟫_ℝ with ht
  have heq : η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ) = ⟪η, α • ξ + t • x⟫_ℝ := by
    rw [dotProduct_radialCoefficient_mulVec, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, ht]
    ring
  -- The cross term `t (2 α ⟪ξ, x⟫ + t ‖x‖²) = β (2 α + β) ⟪x, ξ⟫² / ‖x‖²` is nonpositive.
  have hcross : t * (2 * α * ⟪ξ, x⟫_ℝ + t * ‖x‖ ^ 2) ≤ 0 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ht]
    have h : t * (2 * α * ⟪ξ, x⟫_ℝ + t * ‖x‖ ^ 2) =
        β * (2 * α + β) / ‖x‖ ^ 2 * ⟪x, ξ⟫_ℝ ^ 2 := by
      rw [ht, real_inner_comm ξ x]
      field_simp
    rw [h]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hβ hαβ) (by positivity)) (sq_nonneg _)
  have hw : ‖α • ξ + t • x‖ ≤ α * ‖ξ‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα]
    nlinarith [sq_abs t]
  rw [heq, mul_assoc, mul_comm ‖η‖, ← mul_assoc]
  exact (abs_real_inner_le_norm _ _).trans
    (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (norm_nonneg η))

/-- For `β ≤ 0 < α + β`, the radial coefficient is uniformly elliptic with constants `α + β` and
`α`, so its ellipticity ratio is `α / (α + β)`. -/
theorem uniformlyEllipticOn_radialCoefficient_of_nonpos (hαβ : 0 < α + β) (hβ : β ≤ 0)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    UniformlyEllipticOn Ω (radialCoefficient α β) (α + β) α := by
  refine UniformlyEllipticOn.of_bounds hαβ (by linarith) (fun x _ ξ => ?_)
    (fun x _ η ξ => abs_dotProduct_radialCoefficient_mulVec_le_of_nonpos hβ (by linarith) x η ξ)
  rw [Matrix.toQuadraticForm'_apply, dotProduct_radialCoefficient_mulVec,
    real_inner_self_eq_norm_sq, real_inner_comm x ξ]
  -- The radial term loses at most `-β ‖ξ‖²`, by the Cauchy–Schwarz inequality.
  have hcs : ⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ ≤ ‖x‖ ^ 2 * ‖ξ‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le x ξ
  have h : -β / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) ≤ -β * ‖ξ‖ ^ 2 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
        zero_mul]
      exact mul_nonneg (by linarith) (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcs (by linarith : (0 : ℝ) ≤ -β)]
  have h' : β / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ) = -(-β / ‖x‖ ^ 2 * (⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ)) := by
    ring
  linarith

/-- The radial coefficient is strongly measurable. -/
theorem stronglyMeasurable_radialCoefficient :
    StronglyMeasurable (radialCoefficient (n := n) α β) := by
  have : Measurable (radialCoefficient (n := n) α β) := by
    simp only [funext radialCoefficient_apply]
    fun_prop
  -- The matrix space is metrizable through its underlying function type.
  exact Measurable.stronglyMeasurable (β := Fin n → Fin n → ℝ) this

/-- At the origin, where the direction is undefined, the radial coefficient is `α I`. -/
@[simp]
theorem radialCoefficient_zero :
    radialCoefficient α β (0 : EuclideanSpace ℝ (Fin n)) = α • 1 := by
  simp [radialCoefficient]

/-- The radial coefficient is constant on every line through the origin, away from the origin. -/
@[simp]
theorem radialCoefficient_smul {t : ℝ} (ht : t ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    radialCoefficient α β (t • x) = radialCoefficient α β x := by
  simp only [radialCoefficient, WithLp.ofLp_smul, rankOneProjector_smul ht]

/-- **The radial coefficient is discontinuous at the origin** as soon as it takes different
values at two points `v` and `w` whose open rays `t v`, `t w`, `t > 0`, lie in `s`: it has no
limit at the origin within `s`. -/
theorem not_exists_tendsto_radialCoefficient_of_ne {s : Set (EuclideanSpace ℝ (Fin n))}
    {v w : EuclideanSpace ℝ (Fin n)} (hv : ∀ t : ℝ, 0 < t → t • v ∈ s)
    (hw : ∀ t : ℝ, 0 < t → t • w ∈ s)
    (hvw : radialCoefficient α β v ≠ radialCoefficient α β w) :
    ¬ ∃ L, Tendsto (radialCoefficient α β) (𝓝[s] 0) (𝓝 L) := by
  rintro ⟨L, hL⟩
  -- Along the ray through `u`, the field is the constant `a(u)`, so `L = a(u)`.
  have key : ∀ u, (∀ t : ℝ, 0 < t → t • u ∈ s) → radialCoefficient α β u = L := by
    intro u hu
    have hray : Tendsto (fun t : ℝ => t • u) (𝓝[>] 0) (𝓝[s] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using ((continuous_id.smul continuous_const).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ))) (f := fun t : ℝ => t • u)
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        exact hu t ht
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) (hL.comp hray)
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (radialCoefficient_smul ht.ne' u).symm
  exact hvw ((key v hv).trans (key w hw).symm)

/-- **The radial coefficient is discontinuous at the origin.** For `n ≥ 2` and `β ≠ 0` it has no
limit at the origin: along the ray through `e₀` its entry `a₀₀` is `α + β`, and along the ray
through `e₁` it is `α`. -/
theorem not_exists_tendsto_radialCoefficient (hn : 2 ≤ n) (hβ : β ≠ 0) :
    ¬ ∃ L, Tendsto (radialCoefficient (n := n) α β) (𝓝[≠] 0) (𝓝 L) := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hray : ∀ j : Fin n, ∀ t : ℝ, 0 < t →
      t • EuclideanSpace.single j (1 : ℝ) ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun j t ht => by simp [ht.ne']
  refine not_exists_tendsto_radialCoefficient_of_ne (hray i₀) (hray i₁) fun h => hβ ?_
  have h00 := congrFun (congrFun h i₀) i₀
  simpa [radialCoefficient_apply_apply, hne] using h00

end PDE

end TauCeti
