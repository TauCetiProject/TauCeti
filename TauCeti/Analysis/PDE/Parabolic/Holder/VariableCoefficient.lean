/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.ConstantCoefficient.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Freezing
public import TauCeti.Analysis.Matrix.QuadraticBounds

/-!
# The parabolic Schauder estimate for maps of small support

On `ℝⁿ × [0, T]`, `ℝⁿ = EuclideanSpace ℝ ι`, let

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - ∑ᵢ bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, norms at most `M`, and `a` uniformly elliptic, `lam ‖ξ‖² ≤ ξᵀ a(x, t) ξ` with
`0 < lam`. No symmetry of `a`, no sign of `c` and no smallness of the coefficients is assumed.
This file proves the local form of the Schauder estimate for `P`: there are a radius `r₀ > 0` and
a constant `C`, depending only on `α`, `lam`, `M`, `T` and the dimension, such that

`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α} + ‖u‖_∞)`

for every `u ∈ C_b^{2+α,1+α/2}` whose spatial Hessian vanishes outside the closed parabolic ball
of radius `r₀` about some point `z₀`
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_of_spatialSecondFDerivL_eq_zero`).
The radius and the constant are independent of `z₀` and of the coefficients within these bounds.
An upper ellipticity bound is not a separate hypothesis: it follows from the bound on `a`
(`Matrix.toQuadraticForm'_le_of_forall_abs_le`).

This is the local step of the global Schauder estimate for variable coefficients. Applied to the
localizations `χ u` of a map `u` by space-time cutoffs centred at every point, whose commutator
with `P` involves only `u` and `D_x u`
(`TauCeti.ParabolicC2HolderSpace.exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le`),
it bounds every localization of `u` uniformly, which is what a global estimate patches together.

## The argument

Freezing `a` at `z₀` gives
`P_{a(z₀)} u = P u + (a - a(z₀))·D_x²u + b·D_xu + c u`
(`TauCeti.ParabolicC2HolderSpace.euclideanParabolicOperatorL_const_apply_eq_add`). The
constant-coefficient estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_const`), uniform over
the frozen matrices, bounds `‖u‖` by the norm of the right side and of `u(·, 0)`. For
`r₀` small the freezing error is at most a small multiple of `‖u‖` plus a multiple of `‖u‖_∞`
(`TauCeti.ParabolicC2HolderSpace.exists_norm_spatialOperatorL_sub_const_apply_le`), and so are the
lower-order terms by interpolation
(`TauCeti.ParabolicC2HolderSpace.exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le`);
both are absorbed into the left side.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (freezing the coefficients in the interior Schauder estimate).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}

/-- A local shortcut for the norm on Euclidean Hessians. Without it, instance search for the norm
on the coefficient space of the second-order term fails, as in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance : NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for scalar operations on Euclidean Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance

/-- **The perturbation by freezing at a point.** For every `η > 0` there are a radius `r₀ > 0` and
a constant `C`, depending only on `α`, `M`, `η` and the dimension, such that freezing the
coefficient matrix at `z₀` and dropping the lower-order terms changes `P u` by at most
`η ‖u‖ + C ‖u‖_∞`, whenever the spatial Hessian of `u` vanishes outside the closed parabolic ball of
radius `r₀` about `z₀` and the coefficients have norms at most `M`. -/
private theorem exists_norm_euclideanParabolicOperatorL_const_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ r₀ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁}
      (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
      (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
      (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ),
      (∀ i j, ‖a i j‖ ≤ M) → (∀ i, ‖b i‖ ≤ M) → ‖c‖ ≤ M →
      ∀ (z₀ : slab (E := EuclideanSpace ℝ ι) t₀ t₁)
        (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht),
      (∀ p, r₀ < dist p z₀ → spatialSecondFDerivL u p = 0) →
      ‖euclideanParabolicOperatorL hα₁.le (fun i j ↦ HolderSpace.const (a i j z₀)) 0 0 u‖ ≤
        ‖euclideanParabolicOperatorL hα₁.le a b c u‖ + η * ‖u‖ + C * ‖valueL u‖ := by
  -- Bounds for the assembled coefficient fields.
  set MA := ∑ _i : ι, ∑ _j : ι, M
  set MB := max (∑ _i : ι, M + M) 0
  have hMB : 0 ≤ MB := le_max_right _ _
  -- The freezing error and the lower-order terms each get half of `η`.
  obtain ⟨r₀, hr₀, C₁, hfreeze⟩ :=
    exists_norm_spatialOperatorL_sub_const_apply_le (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀
      hα₁.le MA.toNNReal (half_pos hη)
  have hη' : 0 < η / 2 / (MB + 1) := by positivity
  obtain ⟨C₂, hlow⟩ :=
    exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le (E := EuclideanSpace ℝ ι) (F := ℝ)
      hα₁ hη'
  refine ⟨r₀, hr₀, |C₁| + MB * |C₂|, by positivity,
    fun {t₀ t₁ ht} a b c ha hb hc z₀ u hu ↦ ?_⟩
  rw [euclideanParabolicOperatorL_const_apply_eq_add hα₁.le a b c z₀ u]
  -- The frozen principal error.
  have hA : nnHolderNorm α (euclideanSecondOrderCoeff a : slab (E := EuclideanSpace ℝ ι) t₀ t₁ → _)
      ≤ MA.toNNReal := by
    have h := HolderSpace.nnHolderNorm_le (euclideanSecondOrderCoeff a)
    rw [HolderSpace.coe_toBoundedContinuousFunction] at h
    rw [← Real.toNNReal_coe (r := nnHolderNorm α _)]
    exact Real.toNNReal_le_toNNReal (h.trans ((norm_euclideanSecondOrderCoeff_le a).trans
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ha i j)))
  have h₁ := hfreeze (euclideanSecondOrderCoeff a) z₀ u hA hr₀.le le_rfl hu
  -- The lower-order part, after interpolation.
  have hBC : ‖euclideanFirstOrderCoeff b‖ + ‖euclideanZerothOrderCoeff c‖ ≤ MB :=
    le_max_of_le_left (add_le_add ((norm_euclideanFirstOrderCoeff_le b).trans
      (Finset.sum_le_sum fun i _ ↦ hb i)) ((norm_euclideanZerothOrderCoeff_le c).trans hc))
  have h₂ : ‖spatialOperatorL hα₁.le 0 (euclideanFirstOrderCoeff b)
      (euclideanZerothOrderCoeff c) u‖ ≤ MB * (η / 2 / (MB + 1) * ‖u‖ + C₂ * ‖valueL u‖) := by
    refine (norm_spatialOperatorL_apply_le hα₁.le u).trans ?_
    rw [norm_zero, zero_mul, zero_add]
    calc _ ≤ (‖euclideanFirstOrderCoeff b‖ + ‖euclideanZerothOrderCoeff c‖) *
          (‖valueHolderL hα₁.le u‖ + ‖spatialFDerivHolderL hα₁.le u‖) := by
          nlinarith [norm_nonneg (euclideanFirstOrderCoeff b),
            norm_nonneg (euclideanZerothOrderCoeff c), norm_nonneg (valueHolderL hα₁.le u),
            norm_nonneg (spatialFDerivHolderL hα₁.le u)]
      _ ≤ _ := mul_le_mul hBC (hlow u) (by positivity) hMB
  -- Collect the three terms.
  have hsum := (norm_add₃_le (a := euclideanParabolicOperatorL hα₁.le a b c u)).trans
    (add_le_add_three le_rfl h₁ h₂)
  have hu₀ := norm_nonneg u
  have hv := norm_nonneg (valueL u)
  have e₁ : MB * (η / 2 / (MB + 1) * ‖u‖) ≤ η / 2 * ‖u‖ := by
    rw [← mul_assoc, mul_div_assoc']
    refine mul_le_mul_of_nonneg_right ?_ hu₀
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hMB, hη]
  have e₂ : C₁ * ‖valueL u‖ + MB * (C₂ * ‖valueL u‖) ≤ (|C₁| + MB * |C₂|) * ‖valueL u‖ := by
    have hC₁v := mul_le_mul_of_nonneg_right (le_abs_self C₁) hv
    have hC₂v := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C₂) hv) hMB
    nlinarith only [hC₁v, hC₂v]
  have expand : MB * (η / 2 / (MB + 1) * ‖u‖ + C₂ * ‖valueL u‖) =
      MB * (η / 2 / (MB + 1) * ‖u‖) + MB * (C₂ * ‖valueL u‖) := by ring
  linarith only [hsum, e₁, e₂, expand]

/-- **The Schauder estimate for maps of small support.** There are a radius `r₀ > 0` and a
constant `C`, depending only on `α`, `lam`, `M`, `T` and the dimension, such that
`‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖ + ‖u‖_∞)` whenever the spatial Hessian of `u` vanishes outside the
closed parabolic ball of radius `r₀` about some point. -/
theorem exists_norm_le_of_spatialSecondFDerivL_eq_zero (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (M : ℝ) (hT : (0 : ℝ) < T) :
    ∃ r₀ > 0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ M) → (∀ i, ‖b i‖ ≤ M) → ‖c‖ ≤ M →
      ∀ (z₀ : slab (E := EuclideanSpace ℝ ι) 0 T)
        (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT),
      (∀ p, r₀ < dist p z₀ → spatialSecondFDerivL u p = 0) →
      ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
        ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ + ‖valueL u‖) := by
  -- The constant-coefficient estimate, uniform over the frozen matrices.
  obtain ⟨C₀, hC₀, hconst⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_const (ι := ι) hα₀ hα₁
      (Lam := ∑ _i : ι, ∑ _j : ι, M) hlam
  set D := C₀ * (1 + T)
  have hD : 0 ≤ D := by positivity
  have hη : 0 < 1 / (2 * (D + 1)) := by positivity
  have hDη : D * (1 / (2 * (D + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hD]
  obtain ⟨r₀, hr₀, C₁, hC₁, hpert⟩ :=
    exists_norm_euclideanParabolicOperatorL_const_le (ι := ι) hα₀ hα₁ M hη
  refine ⟨r₀, hr₀, 2 * (D + 1) * (1 + C₁), by positivity,
    fun a b c hlow ha hb hc z₀ u hu ↦ ?_⟩
  -- The coefficient bound gives the upper ellipticity bound.
  have hup : ∀ p (ξ : EuclideanSpace ℝ ι), (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤
      (∑ _i : ι, ∑ _j : ι, M) * ‖ξ‖ ^ 2 := fun p ↦
    Matrix.toQuadraticForm'_le_of_forall_abs_le fun i j ↦
      ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le (a i j) p)).trans (ha i j)
  set X := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  set τ := ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖
  set v := ‖valueL u‖
  -- The constant-coefficient estimate for the matrix frozen at `z₀`, and the perturbation.
  have h₀ := hconst (Matrix.of fun i j ↦ a i j z₀) (hlow z₀) (hup z₀) T hT u
  simp only [Matrix.of_apply] at h₀
  have h₁ := hpert a b c ha hb hc z₀ u hu
  have h₂ : ‖u‖ ≤ D * ((X + C₁ * v + τ) + 1 / (2 * (D + 1)) * ‖u‖) := by
    refine h₀.trans (mul_le_mul_of_nonneg_left ?_ hD)
    linarith only [h₁]
  -- Absorb the multiple of `‖u‖` into the left side.
  have h₃ : ‖u‖ ≤ 2 * D * (X + C₁ * v + τ) := by
    have h' : D * (1 / (2 * (D + 1)) * ‖u‖) ≤ 1 / 2 * ‖u‖ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hDη (norm_nonneg u)
    nlinarith only [h₂, h']
  have hX : 0 ≤ X := norm_nonneg _
  have hτ : 0 ≤ τ := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  calc ‖u‖ ≤ 2 * D * (X + C₁ * v + τ) := h₃
    _ ≤ 2 * (D + 1) * (1 + C₁) * (X + τ + v) := by
      nlinarith only [hD, hC₁, hX, hτ, hv, mul_nonneg hC₁ hX, mul_nonneg hC₁ hτ,
        mul_nonneg hD (mul_nonneg hC₁ hX), mul_nonneg hD (mul_nonneg hC₁ hτ), mul_nonneg hD hv,
        mul_nonneg hD hX, mul_nonneg hD hτ]

end TauCeti.ParabolicC2HolderSpace
