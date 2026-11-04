/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Operator-valued `L∞` multiplication operators on `Lᵖ`

An essentially bounded operator-valued function `A : Lp (E →L[𝕜] F) ∞ μ` acts on `Lp E p μ`, for
`1 ≤ p ≤ ∞`, by pointwise operator application `x ↦ A x (f x)`. This file bundles that action as
`MeasureTheory.Lp.operatorMultiplication p A : Lp E p μ →L[𝕜] Lp F p μ` via Mathlib's bilinear
Hölder map `(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p`, and proves its algebraic,
adjoint, and exact-norm properties:

* `MeasureTheory.Lp.operatorMultiplication_ae`: pointwise almost-everywhere action `x ↦ A x (f x)`;
* `MeasureTheory.Lp.operatorMultiplication_comp_operatorMultiplication`: composition of
  endomorphism-valued multipliers corresponds to the pointwise `L∞` product `A • B`;
* `MeasureTheory.Lp.adjoint_operatorMultiplication`: on `L²` with values in a Hilbert space, the
  adjoint of `operatorMultiplication 2 A` is `operatorMultiplication 2 (star A)`;
* `MeasureTheory.Lp.norm_operatorMultiplication`: on a σ-finite measure space, when the domain fibre
  `E` is second-countable, the operator norm of `operatorMultiplication p A` on `Lp E p μ` is
  exactly the essential-supremum operator norm `‖A‖`.

Compare `MeasureTheory.Lp.multiplicationOperator` (scalar `ℂ`-valued `L∞` symbols on `L²`) and
`BoundedContinuousFunction.mulLp` (bounded continuous operator-valued symbols on non-σ-finite
spaces).
-/

public section

noncomputable section

open ENNReal ContinuousLinearMap
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

variable {α 𝕜 E F G : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- Pointwise application of an essentially bounded operator-valued symbol
`A : Lp (E →L[𝕜] F) ∞ μ`, as a bounded linear operator `Lp E p μ →L[𝕜] Lp F p μ`. -/
def operatorMultiplication (A : Lp (E →L[𝕜] F) ∞ μ) : Lp E p μ →L[𝕜] Lp F p μ :=
  (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p A

/-- `operatorMultiplication` acts by pointwise operator application almost everywhere. -/
theorem operatorMultiplication_ae (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p A f =ᵐ[μ] fun x ↦ A x (f x) := by
  simpa only [operatorMultiplication, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.id_apply] using
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).coeFn_holder (r := p) A f

/-- `operatorMultiplication` is characterized by its almost-everywhere pointwise action. -/
theorem operatorMultiplication_eq_iff {A : Lp (E →L[𝕜] F) ∞ μ} {f : Lp E p μ} {g : Lp F p μ} :
    operatorMultiplication p A f = g ↔ (fun x ↦ A x (f x)) =ᵐ[μ] g :=
  ⟨fun h ↦ h ▸ (operatorMultiplication_ae A f).symm,
    fun h ↦ Lp.ext ((operatorMultiplication_ae A f).trans h)⟩

/-- Applying `operatorMultiplication p A` changes the `Lᵖ` norm by at most `‖A‖`. -/
theorem norm_operatorMultiplication_apply_le (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    ‖operatorMultiplication p A f‖ ≤ ‖A‖ * ‖f‖ :=
  Lp.norm_le_mul_norm_of_ae_le_mul <| by
    filter_upwards [operatorMultiplication_ae A f, Lp.ae_norm_le_norm_top A] with x hx hAx
    exact hx ▸ (A x).le_of_opNorm_le hAx (f x)

/-- The operator norm of `operatorMultiplication p A` is at most the `L∞` norm of `A`. -/
theorem norm_operatorMultiplication_le (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ ≤ ‖A‖ :=
  opNorm_le_bound _ (norm_nonneg A) (norm_operatorMultiplication_apply_le A)

/-- The zero symbol defines the zero operator on `Lp E p μ`. -/
@[simp]
theorem operatorMultiplication_zero :
    operatorMultiplication p (0 : Lp (E →L[𝕜] F) ∞ μ) = 0 := by simp [operatorMultiplication]

/-- Operator multiplication is additive in the symbol. -/
@[simp]
theorem operatorMultiplication_add (A B : Lp (E →L[𝕜] F) ∞ μ) :
    operatorMultiplication p (A + B) =
      operatorMultiplication p A + operatorMultiplication p B := by simp [operatorMultiplication]

/-- Operator multiplication commutes with scalar multiplication of the symbol. -/
@[simp]
theorem operatorMultiplication_smul (c : 𝕜) (A : Lp (E →L[𝕜] F) ∞ μ) :
    operatorMultiplication p (c • A) = c • operatorMultiplication p A := by
  simp [operatorMultiplication]

/-- Pointwise operator application commutes with heterogeneous scalar multiplication by an `L∞`
scalar function. -/
theorem operatorMultiplication_lpSMul (a : Lp 𝕜 ∞ μ) (A : Lp (E →L[𝕜] F) ∞ μ) (f : Lp E p μ) :
    operatorMultiplication p A (a • f : Lp E p μ) =
      (a • operatorMultiplication p A f : Lp F p μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae A (a • f : Lp E p μ), Lp.coeFn_lpSMul (r := p) a f,
    Lp.coeFn_lpSMul (r := p) a (operatorMultiplication p A f), operatorMultiplication_ae A f]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', map_smul, h₄]

/-- Multiplying the operator symbol by an `L∞` scalar function scales the resulting `Lᵖ` output. -/
theorem operatorMultiplication_lpSMul_symbol (a : Lp 𝕜 ∞ μ) (A : Lp (E →L[𝕜] F) ∞ μ)
    (f : Lp E p μ) :
    operatorMultiplication p (a • A : Lp (E →L[𝕜] F) ∞ μ) f =
      (a • operatorMultiplication p A f : Lp F p μ) := Lp.ext <| by
  filter_upwards [operatorMultiplication_ae (a • A : Lp (E →L[𝕜] F) ∞ μ) f,
    Lp.coeFn_lpSMul (r := ∞) a A, Lp.coeFn_lpSMul (r := p) a (operatorMultiplication p A f),
    operatorMultiplication_ae A f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, Pi.smul_apply', Pi.smul_apply', smul_apply, h₄]

/-- A symbol equal almost everywhere to a constant continuous linear map `T` acts as `T.compLpL`. -/
theorem operatorMultiplication_of_ae_eq_const {A : Lp (E →L[𝕜] F) ∞ μ} {T : E →L[𝕜] F}
    (hA : A =ᵐ[μ] fun _ ↦ T) :
    operatorMultiplication p A = T.compLpL p μ := by
  ext1 f; rw [operatorMultiplication_eq_iff]
  filter_upwards [hA, T.coeFn_compLpL f] with x hx hT; rw [hx, hT]

/-- On a finite measure space, a constant continuous linear map `T` in `L∞` acts as `T.compLpL`. -/
@[simp]
theorem operatorMultiplication_const [IsFiniteMeasure μ] (T : E →L[𝕜] F) :
    operatorMultiplication p (Lp.const ∞ μ T) = T.compLpL p μ :=
  operatorMultiplication_of_ae_eq_const (Lp.coeFn_const ∞ μ T)

/-- Heterogeneous composition of operator-valued `L∞` multipliers via `compL.holderL`. -/
theorem operatorMultiplication_comp_holderL (A : Lp (F →L[𝕜] G) ∞ μ) (B : Lp (E →L[𝕜] F) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p ((ContinuousLinearMap.compL 𝕜 E F G).holderL μ ∞ ∞ ∞ A B) := by
  ext1 f; symm; rw [ContinuousLinearMap.comp_apply, operatorMultiplication_eq_iff]
  filter_upwards [(ContinuousLinearMap.compL 𝕜 E F G).coeFn_holder (r := ∞) A B,
    operatorMultiplication_ae A (operatorMultiplication p B f), operatorMultiplication_ae B f]
    with x hAB hA hB
  rw [ContinuousLinearMap.holderL_apply_apply, hAB, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, hA, hB]

/-- Composing endomorphism-valued `L∞` multipliers multiplies their symbols in the same order. -/
theorem operatorMultiplication_comp_operatorMultiplication (A B : Lp (E →L[𝕜] E) ∞ μ) :
    operatorMultiplication p A ∘L operatorMultiplication p B =
      operatorMultiplication p (A • B : Lp (E →L[𝕜] E) ∞ μ) := by
  ext1 f; symm; rw [ContinuousLinearMap.comp_apply, operatorMultiplication_eq_iff]
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) A B,
    operatorMultiplication_ae A (operatorMultiplication p B f), operatorMultiplication_ae B f]
    with x hAB hA hB
  rw [hAB, Pi.smul_apply', smul_eq_mul, mul_apply_eq_comp, hA, hB]

end NormedSpace

section Hilbert

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On `L²` with values in a Hilbert space, the adjoint of `operatorMultiplication 2 A` is
`operatorMultiplication 2 (star A)`. -/
@[simp]
theorem adjoint_operatorMultiplication (A : Lp (E →L[𝕜] E) ∞ μ) :
    ContinuousLinearMap.adjoint (operatorMultiplication 2 A) =
      operatorMultiplication 2 (star A) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]; refine integral_congr_ae ?_
  filter_upwards [operatorMultiplication_ae (p := 2) (star A) f,
    operatorMultiplication_ae (p := 2) A g, Lp.coeFn_star A] with x hf hg hA
  simp [hf, hg, hA, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end Hilbert

section ExactNorm

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_subset_measure_lt_norm_apply [SigmaFinite μ] (A : Lp (E →L[𝕜] F) ∞ μ)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt : c < ‖A‖) :
    ∃ (u : E) (t : Set α), MeasurableSet t ∧ (∀ x ∈ t, c * ‖u‖ < ‖A x u‖) ∧
      0 < μ t ∧ μ t < ∞ := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense E
  have hsub : {x | c < ‖A x‖} ⊆ ⋃ u ∈ D, {x | c * ‖u‖ < ‖A x u‖} := fun x hx ↦ by
    have hnot : ¬ ∀ w : E, ‖A x w‖ ≤ c * ‖w‖ := fun h ↦
      (not_le_of_gt hx) ((A x).opNorm_le_bound hc_nonneg h)
    push Not at hnot; obtain ⟨w, hw⟩ := hnot
    obtain ⟨u, huU, huD⟩ := hD_dense.inter_open_nonempty {u : E | c * ‖u‖ < ‖A x u‖}
      (isOpen_lt (by fun_prop) (by fun_prop)) ⟨w, hw⟩
    exact Set.mem_biUnion huD huU
  have hμ_union : μ (⋃ u ∈ D, {x | c * ‖u‖ < ‖A x u‖}) ≠ 0 :=
    mt (measure_mono_null hsub) (Lp.measure_lt_norm_ne_zero hc_nonneg hc_lt)
  obtain ⟨u, _, hμs⟩ : ∃ u ∈ D, μ {x | c * ‖u‖ < ‖A x u‖} ≠ 0 := by
    by_contra! hzero; exact hμ_union ((measure_biUnion_null_iff hD_count).2 hzero)
  have hs : MeasurableSet {x | c * ‖u‖ < ‖A x u‖} := measurableSet_lt measurable_const
    (((ContinuousLinearMap.apply 𝕜 F u).continuous.norm.comp_stronglyMeasurable
      (Lp.stronglyMeasurable A)).measurable)
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  exact ⟨u, t, ht, hts, hμt_pos, hμt_top⟩

/-- On a σ-finite measure space, when the domain fibre `E` has a second-countable topology, the
operator norm of `operatorMultiplication p A` on `Lp E p μ` (`1 ≤ p ≤ ∞`) equals the `L∞` operator
norm of `A`. -/
@[simp]
theorem norm_operatorMultiplication [SigmaFinite μ] (A : Lp (E →L[𝕜] F) ∞ μ) :
    ‖operatorMultiplication p A‖ = ‖A‖ := by
  apply le_antisymm (norm_operatorMultiplication_le A)
  by_contra hle
  have hlt : ‖operatorMultiplication p A‖ < ‖A‖ := lt_of_not_ge hle
  set c := (‖operatorMultiplication p A‖ + ‖A‖) / 2 with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  obtain ⟨u, t, ht, hts, hμt_pos, hμt_top⟩ :=
    exists_subset_measure_lt_norm_apply A hc_nonneg (by linarith [hc_def])
  have hu_ne : u ≠ 0 := by
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hμt_pos.ne'
    rintro rfl; exact absurd (hts x₀ hx₀) (by simp)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set f := indicatorConstLp p ht hμt_top.ne u
  set g := indicatorConstLp p ht hμt_top.ne (c * ‖u‖)
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne']
    exact mul_pos (norm_pos_iff.mpr hu_ne)
      (Real.rpow_pos_of_pos (ENNReal.toReal_pos hμt_pos.ne' hμt_top.ne) _)
  have hfg : c * ‖f‖ = ‖g‖ := by
    rw [norm_indicatorConstLp' hp0 hμt_pos.ne', norm_indicatorConstLp' hp0 hμt_pos.ne',
      Real.norm_of_nonneg (mul_nonneg hc_nonneg (norm_nonneg u)), mul_assoc]
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖operatorMultiplication p A f x‖ := by
    filter_upwards [operatorMultiplication_ae (p := p) A f,
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := u),
      indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := c * ‖u‖)]
      with x hmul hf_ae hg_ae
    rw [hmul, hf_ae, hg_ae]
    by_cases hx : x ∈ t
    · simp only [Set.indicator_of_mem hx,
        Real.norm_of_nonneg (mul_nonneg hc_nonneg (norm_nonneg u))]
      exact (hts x hx).le
    · simp [Set.indicator_of_notMem hx]
  have hcancel : c * ‖f‖ ≤ ‖operatorMultiplication p A‖ * ‖f‖ :=
    hfg ▸ (Lp.norm_le_norm_of_ae_le hpoint).trans (le_opNorm _ _)
  exact (not_le_of_gt (by linarith [hc_def] : ‖operatorMultiplication p A‖ < c))
    (le_of_mul_le_mul_right hcancel hf_pos)

end ExactNorm

end MeasureTheory.Lp
