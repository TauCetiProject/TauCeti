/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Basic
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Probability.Distributions.Gaussian.TailMoment

/-!
# Gaussian cotype

A real normed space `E` has *Gaussian cotype `q` with constant `C`* if every finite family `y` in
`E` satisfies `‖y‖_q ≤ C * G₂(y)`, where `‖y‖_q = ‖WithLp.toLp q y‖` is the `ℓ^q` norm of the
family and `G₂(y)` is its Gaussian second moment `TauCeti.gaussianSecondMoment y`.

Like Rademacher cotype (`TauCeti.HasCotype`), Gaussian cotype passes to the domain of any additive
map `f : E → F` with `‖x‖ ≤ K ‖f x‖` and `‖f x‖ ≤ M ‖x‖` (since the upper bound makes `f`
continuous and hence `ℝ`-linear), multiplying the constant by `K M`. In particular it passes with
the same constant along any linear isometry (including subspaces) and along any bounded linear
equivalence `U` with constant multiplied by `‖U⁻¹‖ ‖U‖`. Every real normed space has Gaussian
cotype `∞` with constant `1`, every inner product space has Gaussian cotype `2` with constant `1`,
no nonzero space has Gaussian cotype `q < 2` (`HasGaussianCotype.two_le`), and Gaussian cotype `q`
with constant `0` forces `E` to be subsingleton (`HasGaussianCotype.subsingleton_of_zero`).

At exponent `2`, Rademacher cotype implies Gaussian cotype with the **same** constant `C`: applying
the Rademacher cotype inequality pointwise to the Gaussian-weighted family `i ↦ g i • y i`,
squaring, and integrating over `stdGaussian` uses sign-flip invariance of standard Gaussians to
yield `HasCotype.hasGaussianCotype_two`. The converse equivalence (Pisier Lemma 3.8, via truncation
and Pietsch domination) is proved in
`TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Cotype`.

## Main declarations

* `TauCeti.HasGaussianCotype`: Gaussian cotype `q` with constant `C`.
* `TauCeti.HasGaussianCotype.norm_toLp_le`: the defining inequality for families indexed by any
  finite type.
* `TauCeti.HasGaussianCotype.of_map`, `TauCeti.HasGaussianCotype.of_linearIsometry`,
  `TauCeti.HasGaussianCotype.of_continuousLinearEquiv`: transport along bounded maps, linear
  isometries, and bounded linear equivalences.
* `TauCeti.HasGaussianCotype.subsingleton_of_zero`: constant `0` forces the space to be
  subsingleton, for every exponent `q : ℝ≥0∞`.
* `TauCeti.hasGaussianCotype_top`: every real normed space has Gaussian cotype `∞` with
  constant `1`.
* `TauCeti.hasGaussianCotype_two_of_innerProductSpace`: inner product spaces have Gaussian
  cotype `2` with constant `1`.
* `TauCeti.HasGaussianCotype.two_le`: no nonzero real normed space has Gaussian cotype `q < 2`.
* `TauCeti.HasCotype.hasGaussianCotype_two`: Rademacher cotype `2` implies Gaussian cotype `2`
  with the same constant `C`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, pp. 33–37.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E) in
/-- `E` has *Gaussian cotype `q` with constant `C`* if every finite family `y` in `E` satisfies
`‖y‖_q ≤ C * G₂(y)`, where `‖y‖_q = ‖WithLp.toLp q y‖` is the `ℓ^q` norm of the family and
`G₂(y)` is its Gaussian second moment. -/
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
    HasGaussianCotype E q C' := fun n y ↦
  (h n y).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hC) (gaussianSecondMoment_nonneg _))

/-- The Gaussian cotype inequality holds for families indexed by any finite type. -/
theorem HasGaussianCotype.norm_toLp_le {ι : Type*} [Fintype ι] (h : HasGaussianCotype E q C)
    (y : ι → E) :
    ‖WithLp.toLp q y‖ ≤ C * gaussianSecondMoment y := by
  let e := Fintype.equivFin ι
  have hy := h _ (y ∘ e.symm)
  rwa [gaussianSecondMoment_comp_equiv, PiLp.norm_toLp_comp_equiv] at hy

/-- A real normed space with Gaussian cotype `q` and constant `0` is subsingleton, for every
exponent `q : ℝ≥0∞`. -/
theorem HasGaussianCotype.subsingleton_of_zero (h : HasGaussianCotype E q 0) : Subsingleton E := by
  refine subsingleton_iff_forall_eq 0 |>.2 fun y ↦ ?_
  have hy := h 1 (fun _ : Fin 1 ↦ y)
  simp only [NNReal.coe_zero, zero_mul] at hy
  rcases q.trichotomy with rfl | rfl | hq
  · rw [PiLp.norm_eq_card] at hy
    have h0 := Set.eq_empty_iff_forall_notMem.1
      (Set.Finite.toFinset_eq_empty.1 (Finset.card_eq_zero.1 (Nat.cast_nonpos.1 hy))) 0
    simpa [Set.mem_ofPred_eq] using h0
  · rw [PiLp.norm_eq_ciSup] at hy
    have h0 : ‖y‖ ≤ 0 := by simpa using hy
    exact norm_eq_zero.1 (le_antisymm h0 (norm_nonneg _))
  · rw [PiLp.norm_eq_sum hq] at hy
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      one_div] at hy
    rw [← Real.rpow_mul (norm_nonneg y), mul_inv_cancel₀ hq.ne', Real.rpow_one] at hy
    exact norm_eq_zero.1 (le_antisymm hy (norm_nonneg _))

/-! ### Transport -/

section Transport

variable {𝓕 : Type*} [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] {K M : ℝ≥0}

/-- Gaussian cotype passes to the domain of an additive map `f` with `‖x‖ ≤ K ‖f x‖` and
`‖f x‖ ≤ M ‖x‖`, the constant being multiplied by `K M`. -/
theorem HasGaussianCotype.of_map [Fact (1 ≤ q)] (h : HasGaussianCotype F q C) (f : 𝓕)
    (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    HasGaussianCotype E q (K * C * M) := fun n y ↦ calc
  ‖WithLp.toLp q y‖ ≤ K * ‖WithLp.toLp q (fun i ↦ f (y i))‖ := by
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
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Fact (1 ≤ q)] (h : HasGaussianCotype F q C)
    (U : E ≃L[𝕜] F) :
    HasGaussianCotype E q (‖(U.symm : F →L[𝕜] E)‖₊ * C * ‖(U : E →L[𝕜] F)‖₊) :=
  h.of_map U (fun x ↦ by simpa using (U.symm : F →L[𝕜] E).le_opNorm (U x))
    fun x ↦ (U : E →L[𝕜] F).le_opNorm x

end Transport

/-! ### Examples and exponent bound -/

variable (E) in
/-- Every real normed space has Gaussian cotype `∞` with constant `1`. -/
theorem hasGaussianCotype_top : HasGaussianCotype E ∞ 1 := fun n y ↦ by
  rw [PiLp.norm_eq_ciSup, NNReal.coe_one, one_mul]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp
  exact ciSup_le fun i ↦ norm_le_gaussianSecondMoment y i

section InnerProductSpace

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

include 𝕜 in
/-- An inner product space has Gaussian cotype `2` with constant `1`. -/
theorem hasGaussianCotype_two_of_innerProductSpace : HasGaussianCotype H 2 1 := fun n y ↦ by
  rw [gaussianSecondMoment_eq_norm_toLp_two 𝕜, NNReal.coe_one, one_mul]

end InnerProductSpace

/-- A nonzero real normed space has no Gaussian cotype `q < 2`: the family of `n` copies of a
nonzero vector has `ℓ^q` norm `n ^ (1 / q) ‖y‖` but `G₂ = √n ‖y‖`. -/
theorem HasGaussianCotype.two_le [Fact (1 ≤ q)] [Nontrivial E] (h : HasGaussianCotype E q C) :
    2 ≤ q := by
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have key : (q⁻¹).toReal ≤ 1 / 2 := le_of_forall_rpow_le_mul_rpow (C := C) fun n ↦ by
    have := h (n + 1) (Function.const _ y)
    rw [PiLp.norm_toLp_const', ← Function.const_def, gaussianSecondMoment_const, ← mul_assoc]
      at this
    simpa [Real.sqrt_eq_rpow] using le_of_mul_le_mul_right this hy'
  have hq : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne'
  rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal hq]
  calc ENNReal.ofReal (q⁻¹).toReal ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal key
    _ = (2 : ℝ≥0∞)⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-! ### Rademacher cotype 2 implies Gaussian cotype 2 -/

/-- Integrating the Rademacher cotype-2 inequality over Gaussian weights shows that Rademacher
cotype `2` implies Gaussian cotype `2` with the **same** constant `C`. -/
theorem HasCotype.hasGaussianCotype_two (h : HasCotype E 2 C) :
    HasGaussianCotype E 2 C := fun n y ↦ by
  have hflip_eq (ε : Fin n → ℤˣ) (g : EuclideanSpace ℝ (Fin n)) :
      ∑ i : Fin n, (Probability.signFlipEquiv ε g) i • y i = ∑ i, ε i • (g i • y i) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Int.units_eq_one_or (ε i) with he | he <;> simp [he]
  have hpt (g : EuclideanSpace ℝ (Fin n)) :
      ∑ i : Fin n, g i ^ 2 * ‖y i‖ ^ 2 ≤ (C : ℝ) ^ 2 *
        𝔼 ε : Fin n → ℤˣ, ‖∑ i : Fin n, (Probability.signFlipEquiv ε g) i • y i‖ ^ 2 := by
    have hsq := (sq_le_sq₀ (PiLp.norm_nonneg' _)
      (mul_nonneg C.2 (rademacherSecondMoment_nonneg _))).2 (h.norm_toLp_le fun i ↦ g i • y i)
    rw [mul_pow, rademacherSecondMoment_sq, PiLp.norm_eq_of_L2,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at hsq
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ ↦ ?_) (hsq.trans_eq ?_)
    · rw [PiLp.toLp_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    · congr 1
      refine Finset.expect_congr rfl fun ε _ ↦ congrArg (‖·‖ ^ 2) (hflip_eq ε g).symm
  have hint_flip (ε : Fin n → ℤˣ) : Integrable
      (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖∑ i, (Probability.signFlipEquiv ε g) i • y i‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    have hrew (g : EuclideanSpace ℝ (Fin n)) :
        ∑ i, (Probability.signFlipEquiv ε g) i • y i = ∑ i, g i • (ε i • y i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases Int.units_eq_one_or (ε i) with he | he <;> simp [he]
    simpa only [hrew] using integrable_norm_sq_gaussianSum (fun i ↦ ε i • y i)
  apply (sq_le_sq₀ (PiLp.norm_nonneg' _)
    (mul_nonneg C.2 (gaussianSecondMoment_nonneg _))).1
  rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    mul_pow, gaussianSecondMoment_sq]
  calc ∑ i : Fin n, ‖y i‖ ^ 2
      = ∫ g : EuclideanSpace ℝ (Fin n), ∑ i, g i ^ 2 * ‖y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        rw [integral_finsetSum _ fun i _ ↦
          (Probability.integrable_eval_sq_stdGaussian i).mul_const _]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [integral_mul_const, Probability.integral_eval_sq_stdGaussian i, one_mul]
    _ ≤ ∫ g : EuclideanSpace ℝ (Fin n), (C : ℝ) ^ 2 * 𝔼 ε : Fin n → ℤˣ,
            ‖∑ i, (Probability.signFlipEquiv ε g) i • y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        refine integral_mono
          (integrable_finsetSum _ fun i _ ↦
            (Probability.integrable_eval_sq_stdGaussian i).mul_const _) ?_ hpt
        simp_rw [Finset.expect_eq_sum_div_card]
        exact ((integrable_finsetSum _ fun ε _ ↦ hint_flip ε).div_const _).const_mul _
    _ = (C : ℝ) ^ 2 * ∫ g : EuclideanSpace ℝ (Fin n), ‖∑ i, g i • y i‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        simp_rw [Finset.expect_eq_sum_div_card]
        rw [integral_const_mul, integral_div, integral_finsetSum _ fun ε _ ↦ hint_flip ε]
        simp_rw [Probability.integral_comp_signFlipEquiv_stdGaussian _
          (fun g : EuclideanSpace ℝ (Fin n) ↦ ‖∑ i, g i • y i‖ ^ 2)]
        simp [Finset.sum_const, nsmul_eq_mul]

end TauCeti
