/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Topology.Instances.Matrix

/-!
# Radial coefficient fields

For real numbers `α` and `β`, the coefficient field `TauCeti.PDE.radialCoefficient α β` on `ℝⁿ` is

`a(x) = α I + β x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

with eigenvalue `α + β` in the radial direction and `α` in the tangential directions. It is
symmetric, measurable and bounded, homogeneous of degree `0`, and for `β ≠ 0` discontinuous at the
origin. Its bilinear form is bounded by `max |α| |α + β|`, and for `α > 0` and `α + β > 0` it is
uniformly elliptic with constants `min α (α + β)` and `max α (α + β)`. Such fields are the
standard sources of explicit singular solutions of elliptic equations with bounded measurable
coefficients, in divergence form (Meyers) and in non-divergence form (Gilbarg–Serrin).

## Main declarations

* `TauCeti.PDE.radialCoefficient`: the coefficient field `α I + β x̂ x̂ᵀ`.
* `TauCeti.PDE.radialCoefficient_smul`, `TauCeti.PDE.not_continuousAt_radialCoefficient`: it is
  homogeneous of degree `0`, and for `β ≠ 0` discontinuous at the origin.
* `TauCeti.PDE.dotProduct_radialCoefficient_mulVec`: its bilinear form.
* `TauCeti.PDE.sum_radialCoefficient_mul_inner_single`: its contraction `aⁱʲ ⟪H eᵢ, eⱼ⟫` with a
  linear map `H` is `α tr H + β ⟪H x, x⟫ / ‖x‖²`.
* `TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le_max`: its bilinear form is bounded by
  `max |α| |α + β|`, hence by `|α| + |β|`
  (`TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le`), and for `β ≤ 0 ≤ 2 α + β` by `α`
  (`TauCeti.PDE.abs_dotProduct_radialCoefficient_mulVec_le_of_nonpos`).
* `TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`: for `α > 0` and `α + β > 0`, it is
  uniformly elliptic with constants `min α (α + β)` and `max α (α + β)`, that is, `α` and `α + β`
  for `β ≥ 0` (`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient_of_nonneg`) and `α + β` and `α`
  for `β ≤ 0` (`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient_of_nonpos`).
* `TauCeti.PDE.isSymm_radialCoefficient`, `TauCeti.PDE.measurable_radialCoefficient`,
  `TauCeti.PDE.stronglyMeasurable_radialCoefficient`: it is symmetric and measurable.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α β : ℝ}

/-- The coefficient field `a(x) = α I + β x xᵀ / ‖x‖²` on `ℝⁿ`. Its eigenvalue in the radial
direction `x` is `α + β` and in the tangential directions is `α`. At the origin, where the
direction is undefined, it is `α I`. -/
def radialCoefficient (α β : ℝ) (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  α • 1 + (β / ‖x‖ ^ 2) • Matrix.vecMulVec x x

/-- Unfolding `TauCeti.PDE.radialCoefficient`. -/
theorem radialCoefficient_def (x : EuclideanSpace ℝ ι) :
    radialCoefficient α β x = α • 1 + (β / ‖x‖ ^ 2) • Matrix.vecMulVec x x :=
  (rfl)

/-- The entries of `TauCeti.PDE.radialCoefficient`: `aⁱʲ(x) = α δᵢⱼ + β xᵢ xⱼ / ‖x‖²`. -/
@[simp]
theorem radialCoefficient_apply (x : EuclideanSpace ℝ ι) (i j : ι) :
    radialCoefficient α β x i j = (if i = j then α else 0) + β / ‖x‖ ^ 2 * (x i * x j) := by
  simp [radialCoefficient, Matrix.one_apply, Matrix.vecMulVec_apply]

/-- At the origin the radial coefficient is `α I`. -/
@[simp]
theorem radialCoefficient_zero : radialCoefficient α β (0 : EuclideanSpace ℝ ι) = α • 1 := by
  simp [radialCoefficient_def]

/-- Without its radial part the radial coefficient is `α I`. -/
@[simp]
theorem radialCoefficient_zero_right (x : EuclideanSpace ℝ ι) :
    radialCoefficient α 0 x = α • 1 := by
  simp [radialCoefficient_def]

/-- The radial coefficient is homogeneous of degree `0`: it depends only on the direction of
`x`. -/
theorem radialCoefficient_smul {c : ℝ} (hc : c ≠ 0) (x : EuclideanSpace ℝ ι) :
    radialCoefficient α β (c • x) = radialCoefficient α β x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  ext i j
  simp only [radialCoefficient_apply, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp

/-- For `β ≠ 0` the radial coefficient is discontinuous at the origin: it is constant, equal to
`α I + β e eᵀ`, along the ray through a unit vector `e`, but equals `α I` at the origin. -/
theorem not_continuousAt_radialCoefficient [Nonempty ι] (hβ : β ≠ 0) :
    ¬ ContinuousAt (radialCoefficient (ι := ι) α β) 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have hlim : Tendsto (fun t : ℝ => radialCoefficient α β (t • e)) (𝓝[>] 0)
      (𝓝 (radialCoefficient α β 0)) := by
    refine h.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    exact Continuous.tendsto' (f := fun t : ℝ => t • e) (by fun_prop) 0 0 (by simp)
  have hconst : radialCoefficient α β e = radialCoefficient α β 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono
      fun t ht => (radialCoefficient_smul (ne_of_gt ht) e).symm)) hlim
  have hii := Matrix.ext_iff.2 hconst i i
  exact hβ (by simpa [e] using hii)

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

/-- Contracting the radial coefficient against a linear map `H` gives `α` times the trace of `H`
plus `β` times its radial value: `aⁱʲ(x) ⟪H eᵢ, eⱼ⟫ = α tr H + β ⟪H x, x⟫ / ‖x‖²`. -/
theorem sum_radialCoefficient_mul_inner_single (x : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, radialCoefficient α β x i j *
        ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
      α * ∑ i, ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫_ℝ +
        β / ‖x‖ ^ 2 * ⟪H x, x⟫_ℝ := by
  have hH : ∀ j, H x j = ∑ i, x i * H (EuclideanSpace.single i 1) j := fun j => by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr x]
    simp
  have hin : ⟪H x, x⟫_ℝ = ∑ j, x j * H x j := by
    simp [PiLp.inner_apply]
  simp only [radialCoefficient_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, EuclideanSpace.inner_single_right, conj_trivial,
    hin, hH, Finset.mul_sum, one_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The radial coefficient is symmetric. -/
theorem isSymm_radialCoefficient (x : EuclideanSpace ℝ ι) : (radialCoefficient α β x).IsSymm :=
  Matrix.IsSymm.add (Matrix.isSymm_one.smul _)
    (Matrix.IsSymm.smul (by simp [Matrix.IsSymm, Matrix.transpose_vecMulVec]) _)

/-- The bilinear form of the radial coefficient is bounded by the larger absolute value
`max |α| |α + β|` of its eigenvalues. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le_max (x η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ max |α| |α + β| * ‖η‖ * ‖ξ‖ := by
  set M := max |α| |α + β|
  set t : ℝ := β / ‖x‖ ^ 2 * ⟪x, ξ⟫_ℝ with ht
  have heq : η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ) = ⟪η, α • ξ + t • x⟫_ℝ := by
    rw [dotProduct_radialCoefficient_mulVec, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, ht]
    ring
  have hα : α ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg α) (le_max_left _ _) 2
  have hαβ : (α + β) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs (α + β)]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  -- In the radial direction `a(x)` scales by `α + β`, and tangentially by `α`.
  have hw : ‖α • ξ + t • x‖ ^ 2 ≤ (M * ‖ξ‖) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [show t = 0 by rw [ht, inner_zero_left, mul_zero]]
      nlinarith [mul_le_mul_of_nonneg_right hα (sq_nonneg ‖ξ‖)]
    have hN : 0 < ‖x‖ ^ 2 := by positivity
    set q := ⟪x, ξ⟫_ℝ ^ 2 / ‖x‖ ^ 2
    have hq0 : 0 ≤ q := by positivity
    have hq : q ≤ ‖ξ‖ ^ 2 := by
      rw [div_le_iff₀ hN, ← mul_pow, mul_comm, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x ξ) 2
    have h1 : t * ⟪ξ, x⟫_ℝ = β * q := by
      rw [ht, real_inner_comm x ξ]
      simp only [q]
      field_simp
    have h2 : t ^ 2 * ‖x‖ ^ 2 = β ^ 2 * q := by
      rw [ht]
      simp only [q]
      field_simp
    rw [h1, h2]
    nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hq), mul_nonneg (sub_nonneg.2 hαβ) hq0]
  have hw' : ‖α • ξ + t • x‖ ≤ M * ‖ξ‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hw
  rw [heq, mul_assoc, mul_comm ‖η‖, ← mul_assoc]
  exact (abs_real_inner_le_norm _ _).trans
    (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw' (norm_nonneg η))

/-- The bilinear form of the radial coefficient is bounded by `|α| + |β|`. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le (x η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ (|α| + |β|) * ‖η‖ * ‖ξ‖ := by
  refine (abs_dotProduct_radialCoefficient_mulVec_le_max x η ξ).trans ?_
  gcongr
  exact max_le (le_add_of_nonneg_right (abs_nonneg β)) (abs_add_le α β)

/-- For `β ≤ 0 ≤ 2 α + β`, the bilinear form of the radial coefficient is bounded by `α`, its
tangential eigenvalue. -/
theorem abs_dotProduct_radialCoefficient_mulVec_le_of_nonpos (hβ : β ≤ 0) (hαβ : 0 ≤ 2 * α + β)
    (x η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (radialCoefficient α β x *ᵥ ξ)| ≤ α * ‖η‖ * ‖ξ‖ := by
  refine (abs_dotProduct_radialCoefficient_mulVec_le_max x η ξ).trans ?_
  have hα : 0 ≤ α := by linarith
  gcongr
  exact max_le (abs_of_nonneg hα).le (abs_le.2 ⟨by linarith, by linarith⟩)

/-- For `α > 0` and `α + β > 0`, the radial coefficient is uniformly elliptic with constants
`min α (α + β)` and `max α (α + β)`, its smaller and larger eigenvalues. -/
theorem uniformlyEllipticOn_radialCoefficient (hα : 0 < α) (hαβ : 0 < α + β)
    (Ω : Set (EuclideanSpace ℝ ι)) :
    UniformlyEllipticOn Ω (radialCoefficient α β) (min α (α + β)) (max α (α + β)) := by
  refine UniformlyEllipticOn.of_bounds (lt_min hα hαβ) min_le_max (fun x _ ξ => ?_)
    (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, dotProduct_radialCoefficient_mulVec,
      real_inner_self_eq_norm_sq, real_inner_comm x ξ]
    -- The quadratic form is `α (‖ξ‖² - q) + (α + β) q` with `0 ≤ q ≤ ‖ξ‖²`.
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
        zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have hN : 0 < ‖x‖ ^ 2 := by positivity
    have hq0 : 0 ≤ ⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ / ‖x‖ ^ 2 := div_nonneg (mul_self_nonneg _) hN.le
    have hq : ⟪x, ξ⟫_ℝ * ⟪x, ξ⟫_ℝ / ‖x‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [div_le_iff₀ hN]
      simpa only [real_inner_self_eq_norm_sq, mul_comm] using real_inner_mul_inner_self_le x ξ
    have hm1 : min α (α + β) ≤ α := min_le_left _ _
    have hm2 : min α (α + β) ≤ α + β := min_le_right _ _
    rw [div_mul_eq_mul_div, mul_div_assoc]
    nlinarith [mul_nonneg (sub_nonneg.2 hm1) (sub_nonneg.2 hq), mul_nonneg (sub_nonneg.2 hm2) hq0]
  · simpa only [abs_of_pos hα, abs_of_pos hαβ] using
      abs_dotProduct_radialCoefficient_mulVec_le_max (α := α) (β := β) x η ξ

/-- For `α > 0` and `β ≥ 0`, the radial coefficient is uniformly elliptic with constants `α` and
`α + β`. -/
theorem uniformlyEllipticOn_radialCoefficient_of_nonneg (hα : 0 < α) (hβ : 0 ≤ β)
    (Ω : Set (EuclideanSpace ℝ ι)) :
    UniformlyEllipticOn Ω (radialCoefficient α β) α (α + β) := by
  have h := uniformlyEllipticOn_radialCoefficient hα (by linarith : 0 < α + β) Ω
  rwa [min_eq_left (le_add_of_nonneg_right hβ), max_eq_right (le_add_of_nonneg_right hβ)] at h

/-- For `β ≤ 0 < α + β`, the radial coefficient is uniformly elliptic with constants `α + β` and
`α`. -/
theorem uniformlyEllipticOn_radialCoefficient_of_nonpos (hβ : β ≤ 0) (hαβ : 0 < α + β)
    (Ω : Set (EuclideanSpace ℝ ι)) :
    UniformlyEllipticOn Ω (radialCoefficient α β) (α + β) α := by
  have h := uniformlyEllipticOn_radialCoefficient (by linarith : 0 < α) hαβ Ω
  rwa [min_eq_right (add_le_of_nonpos_right hβ), max_eq_left (add_le_of_nonpos_right hβ)] at h

/-- The radial coefficient is measurable. -/
@[fun_prop]
theorem measurable_radialCoefficient : Measurable (radialCoefficient (ι := ι) α β) := by
  unfold radialCoefficient
  fun_prop

/-- The radial coefficient is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_radialCoefficient :
    StronglyMeasurable (radialCoefficient (ι := ι) α β) :=
  measurable_radialCoefficient.stronglyMeasurable

end PDE

end TauCeti
