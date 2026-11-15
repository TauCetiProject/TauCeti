/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Contracting an endomorphism of `ℝⁿ` with a matrix

For a real `n × n` matrix `A`, the contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of endomorphisms `H` of
`ℝⁿ` is a continuous linear functional. Applied to the Hessian of a function `u`, it is the
non-divergence-form operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` with constant coefficients `A`.

## Main declarations

* `Matrix.contraction`: the contraction with `A`, as a continuous linear functional.
* `Matrix.contraction_add`, `Matrix.contraction_sub`, `Matrix.contraction_smul`: the
  contraction is linear in the matrix.
* `Matrix.contraction_one`: contraction with the identity matrix is the trace.
* `Matrix.abs_contraction_le`: if every entry of `M` is at most `ε` in absolute value,
  then the contraction of `H` with `M` is at most `n² ε ‖H‖` in absolute value.
* `Matrix.abs_sum_sum_mul_apply_single_single_le`: the same bound for the contraction
  `∑ᵢⱼ Mᵢⱼ B eᵢ eⱼ` of a continuous bilinear form `B`, such as a second derivative.
* `Matrix.enorm_contraction_le`: the contraction of `H` with `M` is at most
  `(∑ᵢⱼ ‖Mᵢⱼ‖ₑ) ‖H‖ₑ` in extended norm.
* `Matrix.aestronglyMeasurable_contraction`: the contraction of almost everywhere strongly
  measurable fields of matrices and endomorphisms is almost everywhere strongly measurable.
* `Matrix.abs_sum_sum_mul_apply_single_le`: the contraction `∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ` of an
  endomorphism `T` is at most `(∑ᵢⱼ |Aᵢⱼ|) ‖T‖` in absolute value.
* `Matrix.setLAverage_enorm_contraction_sq_le`: Hölder's inequality for the mean square of the
  contraction of a field `H` with a field `A - a` of matrices, in terms of the mean of
  `∑ᵢⱼ ‖A - a‖ᵢⱼ` and a higher mean of `‖H‖`.
-/

public section

noncomputable section

namespace Matrix

open scoped InnerProductSpace

open TauCeti

variable {n : ℕ}

/-- The contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of an endomorphism of `ℝⁿ` with a matrix `A`, as a
continuous linear functional. -/
def contraction (A : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1))

/-- `Matrix.contraction A` evaluates to `∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫`. -/
@[simp]
theorem contraction_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    contraction A H = ∑ i, ∑ j, A i j *
      ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ := by
  simp [contraction, real_inner_comm]

/-- The contraction is additive in the matrix. -/
@[simp]
theorem contraction_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    contraction (A + B) = contraction A + contraction B := by
  ext H
  simp [add_mul, Finset.sum_add_distrib]

/-- The contraction commutes with subtraction of matrices. -/
@[simp]
theorem contraction_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    contraction (A - B) = contraction A - contraction B := by
  ext H
  simp [sub_mul, Finset.sum_sub_distrib]

/-- The contraction is homogeneous in the matrix. -/
@[simp]
theorem contraction_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    contraction (c • A) = c • contraction A := by
  ext H
  simp [mul_assoc, Finset.mul_sum]

/-- Contraction with the identity matrix is the trace. -/
theorem contraction_one :
    contraction (1 : Matrix (Fin n) (Fin n) ℝ) = traceCLM ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext H
  rw [contraction_apply, TauCeti.traceCLM_apply,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [Matrix.one_apply, real_inner_comm]

/-- If every entry of `M` is at most `ε` in absolute value, then
`|∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫| ≤ n² ε ‖H‖`. -/
theorem abs_contraction_le {M : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hM : ∀ i j, |M i j| ≤ ε) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |contraction M H| ≤ n ^ 2 * ε * ‖H‖ := by
  have h1 : ∀ k : Fin n, ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := fun k => by simp
  rw [contraction_apply]
  calc |∑ i, ∑ j, M i j * ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε * ‖H‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hM i j) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [h1, mul_one]
        exact (H.le_opNorm_of_le (h1 i).le).trans_eq (mul_one _)
    _ = n ^ 2 * ε * ‖H‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- If every entry of `M` is at most `ε` in absolute value, then for a continuous bilinear form
`B` on `EuclideanSpace ℝ ι`, `|∑ᵢⱼ Mᵢⱼ B eᵢ eⱼ| ≤ (card ι)² ε ‖B‖`. Applied to the second
derivative of a function, this bounds the principal part `∑ᵢⱼ Mᵢⱼ ∂ᵢ∂ⱼh` of a
non-divergence-form operator by the operator norm of the Hessian. -/
theorem abs_sum_sum_mul_apply_single_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} {ε : ℝ} (hM : ∀ i j, |M i j| ≤ ε)
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    |∑ i, ∑ j, M i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
      Fintype.card ι ^ 2 * ε * ‖B‖ := by
  calc |∑ i, ∑ j, M i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)|
      ≤ ∑ _i : ι, ∑ _j : ι, ε * ‖B‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hM i j) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
        simpa using B.le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    _ = Fintype.card ι ^ 2 * ε * ‖B‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The contraction of `H` with `M` is at most `(∑ᵢⱼ ‖Mᵢⱼ‖ₑ) ‖H‖ₑ` in extended norm. -/
theorem enorm_contraction_le (M : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖contraction M H‖ₑ ≤ (∑ i, ∑ j, ‖M i j‖ₑ) * ‖H‖ₑ := by
  have h1 : ∀ k : Fin n, ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := fun k => by simp
  rw [contraction_apply, Finset.sum_mul]
  refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [eNorm_mul]
  gcongr
  rw [eNorm_le_iff_norm_le, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [h1, mul_one]
  exact (H.le_opNorm_of_le (h1 i).le).trans_eq (mul_one _)

/-- The contraction `x ↦ ∑ᵢⱼ bᵢⱼ(x) ⟪H(x) eᵢ, eⱼ⟫` of almost everywhere strongly measurable fields
`b` and `H` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_contraction {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {b : X → Matrix (Fin n) (Fin n) ℝ}
    (hb : MeasureTheory.AEStronglyMeasurable b μ)
    {H : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hH : MeasureTheory.AEStronglyMeasurable H μ) :
    MeasureTheory.AEStronglyMeasurable (fun x => contraction (b x) (H x)) μ := by
  simp only [contraction_apply]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _
    fun j _ => ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable hb).mul ?_
  exact ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i (1 : ℝ))).continuous.inner
    continuous_const).comp_aestronglyMeasurable hH

/-- For an endomorphism `T` of `EuclideanSpace ℝ ι`, the contraction `∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ`, such as
the principal part `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` with `T` a Hessian operator, is at most `(∑ᵢⱼ |Aᵢⱼ|) ‖T‖` in
absolute value. -/
theorem abs_sum_sum_mul_apply_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i| ≤ (∑ i, ∑ j, |A i j|) * ‖T‖ := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |T (EuclideanSpace.single j 1) i| ≤ ‖T (EuclideanSpace.single j 1)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (T (EuclideanSpace.single j 1)) i
    _ ≤ ‖T‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := T.le_opNorm _
    _ = ‖T‖ := by simp

section Average

open MeasureTheory

open scoped ENNReal

/-- **The coefficient error in mean.** Let `H` vanish almost everywhere on `s ∖ S`, and let the
entries of `A - a` have absolute values summing to at most `W` on `s`. For Hölder conjugate
exponents `t, t'`, the mean square of the error `∑ᵢⱼ (A - a)ᵢⱼ ⟪H eᵢ, eⱼ⟫` on `s` is controlled by
the average over `s` of `w = ∑ᵢⱼ ‖A - a‖ᵢⱼ` restricted to `S` and the `L^{2t}` mean of `H` on `s`:

`⨍_s (∑ᵢⱼ (A - a)ᵢⱼ ⟪H eᵢ, eⱼ⟫)² ≤ (W^(2t' - 1) ⨍_s 1_S w)^(1/t') (⨍_s ‖H‖^(2t))^(1/t)`. -/
theorem setLAverage_enorm_contraction_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s S : Set X} {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    {a : X → Matrix (Fin m) (Fin m) ℝ}
    {H : X → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)} {W : ℝ}
    (hW : ∀ᵐ x ∂μ.restrict s, ∑ i, ∑ j, |A i j - a x i j| ≤ W) (hS : MeasurableSet S)
    (hw : AEMeasurable (fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ) (μ.restrict s))
    (hH : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict s))
    (hsupp : ∀ᵐ x ∂μ.restrict s, x ∉ S → H x = 0) {t t' : ℝ} (htt : t.HolderConjugate t') :
    ⨍⁻ x in s, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ∂μ ≤
      (ENNReal.ofReal W ^ (2 * t' - 1) *
        ⨍⁻ x in s, S.indicator (fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ) x ∂μ) ^ (1 / t') *
        (⨍⁻ x in s, ‖H x‖ₑ ^ (2 * t) ∂μ) ^ (1 / t) := by
  set w : X → ℝ≥0∞ := fun x => ∑ i, ∑ j, ‖A i j - a x i j‖ₑ
  set v : X → ℝ≥0∞ := S.indicator w
  set ν : Measure X := (μ s)⁻¹ • μ.restrict s
  have hν : ν ≪ μ.restrict s := Measure.smul_absolutelyContinuous
  have ht' : 1 < t' := htt.symm.lt
  -- Pointwise: `‖err‖ₑ² ≤ v² ‖H‖ₑ²`, since `H = 0` off `S`.
  have hpt : ∀ᵐ x ∂ν, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ≤ v x ^ 2 * ‖H x‖ₑ ^ 2 := by
    filter_upwards [hν.ae_le hsupp] with x hx
    by_cases hxS : x ∈ S
    · have h := enorm_contraction_le (A - a x) (H x)
      simp only [Matrix.sub_apply] at h
      rw [show v x = w x from Set.indicator_of_mem hxS w, ← mul_pow]
      gcongr
    · simp [hx hxS]
  -- The bound `v ≤ W` on `s`.
  have hvW : ∀ᵐ x ∂ν, v x ≤ ENNReal.ofReal W := by
    filter_upwards [hν.ae_le hW] with x hx
    refine (Set.indicator_le_self S w x).trans ?_
    refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hx)
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun i => ∑ j, |A i j - a x i j|)
      fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun j => |A i j - a x i j|) fun _ _ => abs_nonneg _]
    exact Finset.sum_congr rfl fun j _ => Real.eNorm_eq_ofReal_abs _
  have hvm : AEMeasurable v ν := ((hw.indicator hS)).mono_ac hν
  have hHm : AEMeasurable (fun x => ‖H x‖ₑ) ν := hH.mono_ac hν
  have hv2 : ∀ᵐ x ∂ν, (v x ^ 2) ^ t' ≤ ENNReal.ofReal W ^ (2 * t' - 1) * v x := by
    filter_upwards [hvW] with x hx
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
    conv_lhs => rw [show 2 * t' = (2 * t' - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    gcongr
    linarith
  have hH2 : ∀ x, (‖H x‖ₑ ^ 2) ^ t = ‖H x‖ₑ ^ (2 * t) := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
  simp only [setLAverage_eq']
  calc ∫⁻ x, ‖contraction (A - a x) (H x)‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ x, ((fun x => v x ^ 2) * fun x => ‖H x‖ₑ ^ 2) x ∂ν := lintegral_mono_ae hpt
    _ ≤ (∫⁻ x, (v x ^ 2) ^ t' ∂ν) ^ (1 / t') * (∫⁻ x, (‖H x‖ₑ ^ 2) ^ t ∂ν) ^ (1 / t) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq ν htt.symm (hvm.pow_const 2) (hHm.pow_const 2)
    _ ≤ (∫⁻ x, ENNReal.ofReal W ^ (2 * t' - 1) * v x ∂ν) ^ (1 / t') *
          (∫⁻ x, ‖H x‖ₑ ^ (2 * t) ∂ν) ^ (1 / t) := by
        simp_rw [hH2]
        gcongr ?_ * _
        exact ENNReal.rpow_le_rpow (lintegral_mono_ae hv2)
          (one_div_nonneg.2 (zero_le_one.trans ht'.le))
    _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          ENNReal.ofReal_ne_top)]

end Average

end Matrix
