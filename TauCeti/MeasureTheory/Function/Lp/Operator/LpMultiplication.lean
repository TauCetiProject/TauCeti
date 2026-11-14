/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TauCeti.MeasureTheory.Function.Lp.Operator.Norm

/-!
# Operator-valued `L∞` multiplication operators on `Lᵖ`

An essentially bounded operator-valued function `A : Lp (E →L[𝕜] F) ∞ μ` acts on `Lp E p μ`
(`1 ≤ p ≤ ∞`) by `x ↦ A x (f x)`. This file bundles that action as
`MeasureTheory.Lp.operatorMultiplication p : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ`
via `(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p`, proving:
* `1`, `algebraMap`, and `A * B` laws (`operatorMultiplication_one`,
  `operatorMultiplication_algebraMap`, `operatorMultiplication_comp_operatorMultiplication`);
* the `L²` adjoint `adjoint_operatorMultiplication` and `operatorMultiplicationStarAlgHom`;
* `‖operatorMultiplication p A‖ = ‖A‖` and `isometry_operatorMultiplication` for `[SigmaFinite μ]`.

Compare `MeasureTheory.Lp.multiplicationOperator` and `BoundedContinuousFunction.mulLp`.
-/

public noncomputable section

open ENNReal ContinuousLinearMap
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α 𝕜 E F G : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- Pointwise application of `A : Lp (E →L[𝕜] F) ∞ μ` as a continuous bilinear map on `Lp E p μ`. -/
def operatorMultiplication : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ :=
  (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p

/-- `operatorMultiplication` acts by pointwise operator application almost everywhere. -/
theorem operatorMultiplication_ae (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p A f =ᵐ[μ] fun x ↦ A x (f x) := by
  simpa only [operatorMultiplication, holderL_apply_apply, id_apply] using
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).coeFn_holder (r := p) A f

/-- `operatorMultiplication` is characterized by its almost-everywhere pointwise action. -/
theorem operatorMultiplication_eq_iff {A : Lp (E →L[𝕜] F) ∞ μ} {f : Lp E p μ} {g : Lp F p μ} :
    operatorMultiplication p A f = g ↔ (fun x ↦ A x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (operatorMultiplication_ae A f).symm,
    fun h ↦ Lp.ext ((operatorMultiplication_ae A f).trans h)⟩

/-- The operator norm of `operatorMultiplication p A` is at most the `L∞` norm of `A`. -/
theorem norm_operatorMultiplication_le (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ ≤ ‖A‖ := by
  have h : ‖(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p‖ ≤ 1 :=
    (norm_holderL_le (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F))).trans norm_id_le
  rw [operatorMultiplication]; simpa only [one_mul] using le_of_opNorm_le _ h A

/-- Applying `operatorMultiplication p A` changes the `Lᵖ` norm by at most `‖A‖`. -/
theorem norm_operatorMultiplication_apply_le (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    ‖operatorMultiplication p A f‖ ≤ ‖A‖ * ‖f‖ :=
  (operatorMultiplication p A).le_of_opNorm_le (norm_operatorMultiplication_le A) f

/-- `operatorMultiplication` commutes with heterogeneous `Lp` scalar multiplication on the right. -/
theorem operatorMultiplication_lpSMul_right {q r : ℝ≥0∞} [Fact (1 ≤ r)] [HolderTriple q p r]
    (a : Lp 𝕜 q μ) (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication r A (a • f : Lp E r μ) =
      (a • operatorMultiplication p A f : Lp F r μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae (p := r) A (a • f : Lp E r μ),
    Lp.coeFn_lpSMul (r := r) a f, Lp.coeFn_lpSMul (r := r) a (operatorMultiplication p A f),
    operatorMultiplication_ae (p := p) A f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', map_smul, h₄]

/-- Multiplying the operator symbol on the left by an `L∞` scalar function scales the output. -/
theorem operatorMultiplication_lpSMul_left (a : Lp 𝕜 ∞ μ) (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p (a • A : Lp (E →L[𝕜] F) ∞ μ) f =
      (a • operatorMultiplication p A f : Lp F p μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae (a • A : Lp (E →L[𝕜] F) ∞ μ) f,
    Lp.coeFn_lpSMul (r := ∞) a A, Lp.coeFn_lpSMul (r := p) a (operatorMultiplication p A f),
    operatorMultiplication_ae A f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', smul_apply, h₄]

/-- A symbol equal almost everywhere to a constant `T : E →L[𝕜] F` acts as `T.compLpL`. -/
theorem operatorMultiplication_of_ae_eq_const {A : Lp (E →L[𝕜] F) ∞ μ} {T : E →L[𝕜] F}
    (hA : A =ᵐ[μ] fun _ ↦ T) : operatorMultiplication p A = T.compLpL p μ := by
  ext1 f; rw [operatorMultiplication_eq_iff]
  filter_upwards [hA, T.coeFn_compLpL f] with x hx hT; rw [hx, hT]

/-- On a finite measure space, a constant continuous linear map `T` in `L∞` acts as `T.compLpL`. -/
@[simp] theorem operatorMultiplication_const [IsFiniteMeasure μ] (T : E →L[𝕜] F) :
    operatorMultiplication p (Lp.const ∞ μ T) = T.compLpL p μ :=
  operatorMultiplication_of_ae_eq_const (Lp.coeFn_const ∞ μ T)

/-- The identity symbol `1 : Lp (E →L[𝕜] E) ∞ μ` acts as the identity operator on `Lp E p μ`. -/
@[simp] theorem operatorMultiplication_one :
    operatorMultiplication p (1 : Lp (E →L[𝕜] E) ∞ μ) = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f; rw [operatorMultiplication_eq_iff, id_apply]
  filter_upwards [Lp.coeFn_one (E := E →L[𝕜] E) (μ := μ)] with x hx; simp [hx]

/-- Scalar multiples of the identity symbol via `algebraMap` act by scalar multiplication. -/
@[simp] theorem operatorMultiplication_algebraMap (c : 𝕜) :
    operatorMultiplication p (algebraMap 𝕜 (Lp (E →L[𝕜] E) ∞ μ) c) =
      c • ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, operatorMultiplication_one]

/-- Heterogeneous composition of operator-valued `L∞` multipliers via `compL.holderL`. -/
theorem operatorMultiplication_comp_eq_operatorMultiplication_compL_holderL
    (A : Lp (F →L[𝕜] G) ∞ μ) (B : Lp (E →L[𝕜] F) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p ((compL 𝕜 E F G).holderL μ ∞ ∞ ∞ A B) := by
  ext1 f; symm; rw [comp_apply, operatorMultiplication_eq_iff]
  filter_upwards [(compL 𝕜 E F G).coeFn_holder (r := ∞) A B,
    operatorMultiplication_ae A (operatorMultiplication p B f), operatorMultiplication_ae B f]
    with x hAB hA hB
  rw [holderL_apply_apply, hAB, compL_apply, comp_apply, hA, hB]

/-- For endomorphism-valued `L∞` symbols, `compL.holderL` agrees with the ring product `A * B`. -/
theorem compL_holderL_eq_mul (A B : Lp (E →L[𝕜] E) ∞ μ) :
    (compL 𝕜 E E E).holderL μ ∞ ∞ ∞ A B = A * B := Lp.ext <| by
  filter_upwards [(compL 𝕜 E E E).coeFn_holder (r := ∞) A B, Lp.coeFn_mul A B] with x h₁ h₂
  rw [holderL_apply_apply, h₁, h₂, compL_apply, Pi.mul_apply, mul_def]

/-- Composing endomorphism-valued `L∞` multipliers multiplies their symbols in the same order. -/
theorem operatorMultiplication_comp_operatorMultiplication (A B : Lp (E →L[𝕜] E) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p (A * B) := by
  rw [operatorMultiplication_comp_eq_operatorMultiplication_compL_holderL, compL_holderL_eq_mul]

/-- On a σ-finite space, `‖operatorMultiplication p A‖ = ‖A‖` (`1 ≤ p ≤ ∞`). -/
@[simp] theorem norm_operatorMultiplication [SigmaFinite μ] (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ = ‖A‖ := by
  apply le_antisymm (norm_operatorMultiplication_le A); by_contra! hlt
  set c := (‖operatorMultiplication p A‖ + ‖A‖) / 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨u, t, ht, hts, hμt_pos, hμt_top⟩ :=
    exists_measurableSet_mul_norm_lt_norm_apply_measure_lt_top A hc0 (by linarith [hc_def, hlt])
  have hu_ne : u ≠ 0 := by
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hμt_pos.ne'
    rintro rfl; exact absurd (hts x₀ hx₀) (by simp)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set f := indicatorConstLp p ht hμt_top.ne u
  set g := indicatorConstLp p ht hμt_top.ne (c * ‖u‖)
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne']; exact mul_pos (norm_pos_iff.mpr hu_ne)
      (Real.rpow_pos_of_pos (ENNReal.toReal_pos hμt_pos.ne' hμt_top.ne) _)
  have hfg : c * ‖f‖ = ‖g‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne', norm_indicatorConstLp' hp0 hμt_pos.ne',
      Real.norm_of_nonneg (mul_nonneg hc0 (norm_nonneg u)), mul_assoc]
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖operatorMultiplication p A f x‖ := by
    filter_upwards [operatorMultiplication_ae (p := p) A f,
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := u),
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := c * ‖u‖)]
      with x hmul hf_ae hg_ae
    rw [hmul, hf_ae, hg_ae]; by_cases hx : x ∈ t
    · simpa [Set.indicator_of_mem hx, Real.norm_of_nonneg (mul_nonneg hc0 (norm_nonneg u))]
        using (hts x hx).le
    · simp [Set.indicator_of_notMem hx]
  have hcancel : c * ‖f‖ ≤ ‖operatorMultiplication p A‖ * ‖f‖ :=
    hfg ▸ (Lp.norm_le_norm_of_ae_le hpoint).trans (le_opNorm _ _)
  exact (not_le_of_gt (by linarith [hc_def, hlt] : ‖operatorMultiplication p A‖ < c))
    (le_of_mul_le_mul_right hcancel hf_pos)

/-- On a σ-finite measure space, `operatorMultiplication p` is an isometry. -/
theorem isometry_operatorMultiplication [SigmaFinite μ] :
    Isometry (operatorMultiplication p : Lp (E →L[𝕜] F) ∞ μ →L[𝕜] Lp E p μ →L[𝕜] Lp F p μ) :=
  AddMonoidHomClass.isometry_of_norm _ norm_operatorMultiplication

end NormedSpace

section Hilbert

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On Hilbert-valued `L²`, `(operatorMultiplication 2 A)† = operatorMultiplication 2 (star A)`. -/
@[simp] theorem adjoint_operatorMultiplication (A : Lp (E →L[𝕜] E) ∞ μ) :
    adjoint (operatorMultiplication 2 A) = operatorMultiplication 2 (star A) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]; refine integral_congr_ae ?_
  filter_upwards [operatorMultiplication_ae (p := 2) (star A) f,
    operatorMultiplication_ae (p := 2) A g, Lp.coeFn_star A] with x hf hg hA
  simp [hf, hg, hA, star_eq_adjoint, adjoint_inner_left]

variable (𝕜 E μ) in
/-- Pointwise operator multiplication on `L²(μ, E)` as a unital ⋆-algebra homomorphism. -/
def operatorMultiplicationStarAlgHom :
    Lp (E →L[𝕜] E) ∞ μ →⋆ₐ[𝕜] (Lp E 2 μ →L[𝕜] Lp E 2 μ) where
  toFun A := operatorMultiplication 2 A
  map_one' := by rw [operatorMultiplication_one, ← ContinuousLinearMap.one_def]
  map_mul' _ _ := by
    rw [← operatorMultiplication_comp_operatorMultiplication, ContinuousLinearMap.mul_def]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' _ := by rw [operatorMultiplication_algebraMap, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.one_def]
  map_star' _ := by rw [star_eq_adjoint, adjoint_operatorMultiplication]

/-- Evaluation of `operatorMultiplicationStarAlgHom` produces `operatorMultiplication 2`. -/
@[simp] theorem operatorMultiplicationStarAlgHom_apply (A : Lp (E →L[𝕜] E) ∞ μ) :
    operatorMultiplicationStarAlgHom 𝕜 E μ A = operatorMultiplication 2 A := (rfl)

end Hilbert

end MeasureTheory.Lp
