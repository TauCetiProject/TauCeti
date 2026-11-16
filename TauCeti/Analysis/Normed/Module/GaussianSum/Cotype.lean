/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Basic
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Probability.Distributions.Gaussian.L2

/-!
# Gaussian cotype

A real normed space `E` has *Gaussian cotype `q` with constant `C`* if every finite family `y` in
`E` satisfies `‖y‖_q ≤ C G₂(y)`, where `G₂(y) = (𝔼_g ‖∑ i, gᵢ yᵢ‖²)^(1/2)` is the Gaussian second
moment (`TauCeti.gaussianSecondMoment`) and `‖y‖_q = ‖WithLp.toLp q y‖`.

Gaussian cotype passes along bounded additive maps with a lower bound (in particular along linear
isometries with the same constant, and along bounded linear equivalences `U` with constant
multiplied by `‖U⁻¹‖ ‖U‖`). No nontrivial real normed space has Gaussian cotype with constant
`C < 1` or exponent `q < 2`.

At exponent `2`, Rademacher cotype `2` with constant `C` implies Gaussian cotype `2` with the same
constant `C`: applying the Rademacher cotype inequality pointwise to the Gaussian-weighted family
`(gᵢ yᵢ)ᵢ` and integrating over the standard Gaussian measure recovers `∑ ‖yᵢ‖²` on the left (since
`𝔼[gᵢ²] = 1`) and `C² G₂(y)²` on the right by coordinatewise sign-flip invariance of the standard
Gaussian law.

## Main declarations

* `TauCeti.HasGaussianCotype`: Gaussian cotype `q` with constant `C`.
* `TauCeti.HasGaussianCotype.norm_toLp_le`: the defining inequality for families indexed by any
  finite type.
* `TauCeti.HasGaussianCotype.of_map`, `TauCeti.HasGaussianCotype.of_linearIsometry`,
  `TauCeti.HasGaussianCotype.of_continuousLinearEquiv`: transport of Gaussian cotype.
* `TauCeti.HasGaussianCotype.subsingleton_of_lt_one`: a space with Gaussian cotype constant `< 1`
  is a subsingleton.
* `TauCeti.HasGaussianCotype.two_le`: a nonzero real normed space has no Gaussian cotype `q < 2`.
* `TauCeti.HasCotype.hasGaussianCotype_two`: Rademacher cotype `2` implies Gaussian cotype `2`
  with the same constant.
* `TauCeti.hasGaussianCotype_two_of_innerProductSpace`: inner product spaces have Gaussian cotype
  `2` with constant `1`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*, §3, pp. 33–37.
* M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, §9.2.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E) in
/-- `E` has *Gaussian cotype `q` with constant `C`* if every finite family `y` in `E` satisfies
`‖y‖_q ≤ C G₂(y)`, where `G₂(y) = gaussianSecondMoment y` and `‖y‖_q = ‖WithLp.toLp q y‖`. -/
def HasGaussianCotype (q : ℝ≥0∞) (C : ℝ≥0) : Prop :=
  ∀ (n : ℕ) (y : Fin n → E), ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y

variable {q : ℝ≥0∞} {C C' : ℝ≥0}

/-- The defining inequality of Gaussian cotype `q` with constant `C`, for families indexed by
`Fin n`. -/
theorem hasGaussianCotype_iff :
    HasGaussianCotype E q C ↔
      ∀ (n : ℕ) (y : Fin n → E), ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y :=
  Iff.rfl

/-- A Gaussian cotype constant may be enlarged. -/
theorem HasGaussianCotype.mono_const (h : HasGaussianCotype E q C) (hC : C ≤ C') :
    HasGaussianCotype E q C' :=
  fun n y ↦ (h n y).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hC) (gaussianSecondMoment_nonneg _))

/-- The Gaussian cotype inequality holds for families indexed by any finite type. -/
theorem HasGaussianCotype.norm_toLp_le {ι : Type*} [Fintype ι] (h : HasGaussianCotype E q C)
    (y : ι → E) :
    ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y := by
  let e := Fintype.equivFin ι
  have hy := h _ (y ∘ e.symm)
  rwa [gaussianSecondMoment_comp_equiv, PiLp.norm_toLp_comp_equiv] at hy

/-! ### Degeneracy and exponent bounds -/

/-- A real normed space with Gaussian cotype constant strictly smaller than `1` is a
subsingleton. -/
theorem HasGaussianCotype.subsingleton_of_lt_one (h : HasGaussianCotype E q C) (hC : C < 1) :
    Subsingleton E := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  by_contra hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hC1 : (C : ℝ) < 1 := NNReal.coe_lt_coe.2 hC
  rcases eq_or_ne q 0 with rfl | hq
  · let y : E := (2 * ‖x‖)⁻¹ • x
    have hy_norm : ‖y‖ = 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp [hx0.ne']
    have h1 := h 1 (fun _ ↦ y)
    rw [gaussianSecondMoment_unique, PiLp.norm_eq_card] at h1
    simp [hy_norm] at h1
    linarith
  · have h1 := h 1 (fun _ ↦ x)
    rw [gaussianSecondMoment_unique] at h1
    have hnorm : ‖WithLp.toLp q (fun _ : Fin 1 ↦ x)‖ = ‖x‖ := by
      rcases eq_or_ne q ∞ with rfl | hqtop
      · simp [PiLp.norm_eq_ciSup]
      · rw [PiLp.norm_eq_sum (ENNReal.toReal_pos hq hqtop)]
        simp [← Real.rpow_mul (norm_nonneg x),
          mul_inv_cancel₀ (ENNReal.toReal_pos hq hqtop).ne']
    rw [hnorm] at h1
    nlinarith

/-- A nonzero real normed space has no Gaussian cotype `q < 2`: the family of `n` copies of a
nonzero vector has `ℓ^q` norm `n ^ (1 / q) ‖y‖` (or `n` for `q = 0`) while `G₂ = √n ‖y‖`. -/
theorem HasGaussianCotype.two_le [Nontrivial E] (h : HasGaussianCotype E q C) : 2 ≤ q := by
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  rcases eq_or_ne q ∞ with rfl | hqtop
  · exact le_top
  rcases eq_or_ne q 0 with rfl | hq0
  · exfalso
    have key : (1 : ℝ) ≤ 1 / 2 := le_of_forall_rpow_le_mul_rpow (C := C * ‖y‖) fun n ↦ by
      have hn := h (n + 1) (fun _ ↦ y)
      rw [PiLp.norm_eq_card, gaussianSecondMoment_const] at hn
      simp [hy, Real.sqrt_eq_rpow] at hn
      simpa only [Real.rpow_one, one_div] using hn.trans_eq (by ring)
    norm_num at key
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have key : q.toReal⁻¹ ≤ 1 / 2 := le_of_forall_rpow_le_mul_rpow (C := C) fun n ↦ by
    have hn := h (n + 1) (fun _ ↦ y)
    rw [PiLp.norm_eq_sum hqpos, gaussianSecondMoment_const, Real.sqrt_eq_rpow] at hn
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, ← mul_assoc] at hn
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel hqpos.ne', Real.rpow_one, one_div] at hn
    exact le_of_mul_le_mul_right hn hy'
  rw [← ENNReal.ofReal_toReal hqtop]
  refine (ENNReal.ofReal_ofNat 2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
  rw [inv_le_iff_one_le_mul₀ hqpos] at key
  linarith

/-! ### Transport -/

section Transport

variable {𝓕 : Type*} [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] {K M : ℝ≥0}

/-- Gaussian cotype passes to the domain of an additive map `f` with `‖x‖ ≤ K ‖f x‖` and
`‖f x‖ ≤ M ‖x‖`, the constant being multiplied by `K M`. -/
theorem HasGaussianCotype.of_map (h : HasGaussianCotype F q C) (f : 𝓕)
    (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    HasGaussianCotype E q (K * C * M) := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · intro n y
    have hy (i : Fin n) : ‖y i‖ = 0 :=
      le_antisymm ((hK (y i)).trans (by simp [Subsingleton.elim (f (y i)) 0])) (norm_nonneg _)
    have hnorm : ‖WithLp.toLp q y‖ = 0 := by
      rcases q.trichotomy with rfl | rfl | hq
      · simp [PiLp.norm_eq_card, hy]
      · simp [PiLp.norm_eq_ciSup, hy]
      · simp [PiLp.norm_eq_sum hq, hy, Real.zero_rpow hq.ne',
          Real.zero_rpow (inv_ne_zero hq.ne')]
    rw [hnorm]
    exact mul_nonneg (NNReal.coe_nonneg _) (gaussianSecondMoment_nonneg _)
  · have : Fact (1 ≤ q) := ⟨one_le_two.trans h.two_le⟩
    intro n y
    calc ‖WithLp.toLp q y‖ ≤ K * ‖WithLp.toLp q (fun i ↦ f (y i))‖ := by
          calc ‖WithLp.toLp q y‖ ≤ ‖(K : ℝ) • WithLp.toLp q (fun i ↦ ‖f (y i)‖)‖ :=
                PiLp.norm_mono fun i ↦ by simpa [abs_of_nonneg K.2] using hK (y i)
            _ = K * ‖WithLp.toLp q (fun i ↦ f (y i))‖ := by
                rw [norm_smul, Real.norm_eq_abs, NNReal.abs_eq,
                  PiLp.norm_norm (WithLp.toLp q fun i ↦ f (y i))]
      _ ≤ K * (C * (M * gaussianSecondMoment y)) := by
          gcongr
          exact (h n _).trans (by gcongr; exact gaussianSecondMoment_map_le f hM y)
      _ = (K * C * M : ℝ≥0) * gaussianSecondMoment y := by push_cast; ring

/-- Gaussian cotype passes along linear isometries with the same constant; in particular it passes
to subspaces, through `Submodule.subtypeₗᵢ`. -/
theorem HasGaussianCotype.of_linearIsometry {R : Type*} [Semiring R] [Module R E] [Module R F]
    (h : HasGaussianCotype F q C) (f : E →ₗᵢ[R] F) : HasGaussianCotype E q C := fun n y ↦ by
  have hG := gaussianSecondMoment_map_le f (M := 1) (fun x ↦ by simp) y
  have hy : ‖WithLp.toLp q fun i ↦ f (y i)‖ = ‖WithLp.toLp q y‖ :=
    le_antisymm (PiLp.norm_mono fun i ↦ by simp) (PiLp.norm_mono fun i ↦ by simp)
  rw [one_mul] at hG
  rw [← hy]
  exact (h n _).trans (by gcongr)

/-- Gaussian cotype passes along a bounded linear equivalence `U`, the constant being multiplied by
`‖U⁻¹‖ ‖U‖`. -/
theorem HasGaussianCotype.of_continuousLinearEquiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (h : HasGaussianCotype F q C) (U : E ≃L[𝕜] F) :
    HasGaussianCotype E q (‖(U.symm : F →L[𝕜] E)‖₊ * C * ‖(U : E →L[𝕜] F)‖₊) :=
  h.of_map U (fun x ↦ by simpa using (U.symm : F →L[𝕜] E).le_opNorm (U x))
    fun x ↦ (U : E →L[𝕜] F).le_opNorm x

end Transport

/-! ### Comparison from Rademacher cotype `2` -/

private theorem integrable_coord_sq_stdGaussian {n : ℕ} (i : Fin n) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) ↦ g i ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hsq (g : EuclideanSpace ℝ (Fin n)) :
      g i ^ 2 = ‖⟪EuclideanSpace.single i (1 : ℝ), g⟫‖ ^ 2 := by
    rw [EuclideanSpace.inner_single_left]; simp
  simp_rw [hsq]
  exact (TauCeti.Probability.memLp_inner_stdGaussian (EuclideanSpace.single i (1 : ℝ)) 2
    (by simp)).integrable_norm_pow (by norm_num)

private theorem integral_coord_sq_stdGaussian {n : ℕ} (i : Fin n) :
    ∫ g : EuclideanSpace ℝ (Fin n), g i ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 1 := by
  have hproj (g : EuclideanSpace ℝ (Fin n)) : g i = ⟪EuclideanSpace.single i (1 : ℝ), g⟫ := by
    rw [EuclideanSpace.inner_single_left]; simp
  simp_rw [hproj]
  rw [TauCeti.Probability.integral_sq_inner_stdGaussian]
  simp

/-- Rademacher cotype `2` with constant `C` implies Gaussian cotype `2` with the same constant. -/
theorem HasCotype.hasGaussianCotype_two (h : HasCotype E 2 C) : HasGaussianCotype E 2 C := by
  intro n y
  set γ : Measure (EuclideanSpace ℝ (Fin n)) := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hrew (ε : Fin n → ℤˣ) (g : EuclideanSpace ℝ (Fin n)) :
      ∑ i, ε i • (g i • y i) = ∑ i, g i • (ε i • y i) :=
    Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  have hint_rhs : Integrable (fun g : EuclideanSpace ℝ (Fin n) ↦
      (C : ℝ) ^ 2 * 𝔼 ε : Fin n → ℤˣ, ‖∑ i, ε i • (g i • y i)‖ ^ 2) γ := by
    simp_rw [Fintype.expect_eq_sum_div_card, hrew]
    exact ((integrable_finsetSum _ fun ε _ ↦
      integrable_norm_sq_gaussianSum (fun i ↦ ε i • y i)).div_const _).const_mul _
  have hpt (g : EuclideanSpace ℝ (Fin n)) :
      ∑ i, g i ^ 2 * ‖y i‖ ^ 2 ≤
        (C : ℝ) ^ 2 * 𝔼 ε : Fin n → ℤˣ, ‖∑ i, ε i • (g i • y i)‖ ^ 2 := by
    have hsq := pow_le_pow_left₀ (PiLp.norm_nonneg' _) (h.norm_toLp_le fun i ↦ g i • y i) 2
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, rademacherSecondMoment_sq] at hsq
    simpa [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hsq
  have hint := integral_mono (integrable_finsetSum _ fun i _ ↦
    (integrable_coord_sq_stdGaussian i).mul_const _) hint_rhs hpt
  have hlhs : ∫ g, ∑ i, g i ^ 2 * ‖y i‖ ^ 2 ∂γ = ‖WithLp.toLp 2 y‖ ^ 2 := by
    rw [integral_finsetSum _ fun i _ ↦ (integrable_coord_sq_stdGaussian i).mul_const _]
    simp_rw [integral_mul_const, integral_coord_sq_stdGaussian, one_mul, PiLp.norm_sq_eq_of_L2]
  have hrhs : ∫ g, (C : ℝ) ^ 2 * 𝔼 ε : Fin n → ℤˣ, ‖∑ i, ε i • (g i • y i)‖ ^ 2 ∂γ =
      ((C : ℝ) * gaussianSecondMoment y) ^ 2 := by
    simp_rw [Fintype.expect_eq_sum_div_card, hrew]
    rw [integral_const_mul, integral_div, integral_finsetSum _ fun ε _ ↦
      integrable_norm_sq_gaussianSum (fun i ↦ ε i • y i)]
    have hε (ε : Fin n → ℤˣ) :
        ∫ g, ‖∑ i, g i • (ε i • y i)‖ ^ 2 ∂γ = gaussianSecondMoment y ^ 2 := by
      rw [← gaussianSecondMoment_sq, gaussianSecondMoment_units_smul]
    simp_rw [hε, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Fin n → ℤˣ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp [hcard]
  rw [hlhs, hrhs] at hint
  exact (pow_le_pow_iff_left₀ (PiLp.norm_nonneg' _)
    (mul_nonneg C.2 (gaussianSecondMoment_nonneg y)) two_ne_zero).1 hint

section InnerProductSpace

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [NormedSpace ℝ H]

include 𝕜 in
/-- An inner product space has Gaussian cotype `2` with constant `1`. -/
theorem hasGaussianCotype_two_of_innerProductSpace : HasGaussianCotype H 2 1 :=
  (hasCotype_two_of_innerProductSpace 𝕜 H).hasGaussianCotype_two

end InnerProductSpace

end TauCeti
