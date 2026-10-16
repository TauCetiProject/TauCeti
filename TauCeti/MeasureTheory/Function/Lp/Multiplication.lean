/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Multiplication operators on complex L²

An essentially bounded complex function `a` acts on `L²` by pointwise multiplication.  This file
bundles that action as `MeasureTheory.Lp.multiplicationOperator a` and records its algebraic,
adjoint, and norm properties.  In particular, on a finite measure space the operator norm is
exactly the `L∞` norm of the symbol.

The construction is Mathlib's Hölder map for scalar multiplication with one exponent equal to
infinity.  The resulting operator is the ambient multiplication operator compressed in the
definition of a Toeplitz operator.
-/

public section

noncomputable section

open scoped ENNReal ComplexInnerProductSpace InnerProduct

namespace MeasureTheory.Lp

open ContinuousLinearMap

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pointwise multiplication by an essentially bounded complex symbol, as a bounded operator on
`L²`. -/
def multiplicationOperator (a : Lp ℂ ∞ μ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2 a

/-- The multiplication operator acts by pointwise multiplication almost everywhere. -/
theorem multiplicationOperator_ae (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplicationOperator a f =ᵐ[μ] fun x ↦ a x • f x := by
  simpa only [multiplicationOperator, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.lsmul_apply] using
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).coeFn_holder (r := 2) a f

/-- Applying the multiplication operator is heterogeneous `Lp` scalar multiplication. -/
theorem multiplicationOperator_apply (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    multiplicationOperator a f = a • f := by
  apply Lp.ext
  exact (multiplicationOperator_ae a f).trans (coeFn_lpSMul (r := 2) a f).symm

/-- Multiplication by `a` changes the `L²` norm by at most `‖a‖∞`. -/
theorem norm_multiplicationOperator_apply_le (a : Lp ℂ ∞ μ) (f : Lp E 2 μ) :
    ‖multiplicationOperator a f‖ ≤ ‖a‖ * ‖f‖ := by
  change ‖(a • f : Lp E 2 μ)‖ ≤ ‖a‖ * ‖f‖
  exact Lp.norm_smul_le a f

/-- The operator norm of multiplication by `a` is at most its `L∞` norm. -/
theorem norm_multiplicationOperator_le (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := E) a‖ ≤ ‖a‖ :=
  opNorm_le_bound _ (norm_nonneg a) (norm_multiplicationOperator_apply_le a)

@[simp]
theorem multiplicationOperator_zero :
    multiplicationOperator (E := E) (0 : Lp ℂ ∞ μ) = 0 := by
  simp [multiplicationOperator]

/-- Multiplication operators depend additively on their symbols. -/
theorem multiplicationOperator_add (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (a + b) =
      multiplicationOperator a + multiplicationOperator b := by
  simp [multiplicationOperator]

/-- Multiplication operators depend complex-linearly on their symbols. -/
theorem multiplicationOperator_smul (c : ℂ) (a : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (c • a) = c • multiplicationOperator a := by
  simp [multiplicationOperator]

/-- Composing multiplication operators multiplies their symbols in the same order. -/
theorem multiplicationOperator_comp_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) a ∘L multiplicationOperator b =
      multiplicationOperator (a • b : Lp ℂ ∞ μ) := by
  ext f
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f,
    multiplicationOperator_ae (a • b : Lp ℂ ∞ μ) f,
    coeFn_lpSMul (r := ∞) a b] with x ha hb hab hsmul
  simp only [comp_apply, ha, hb, hab, hsmul, Pi.smul_apply', smul_eq_mul]
  rw [smul_smul]

/-- A symbol equal almost everywhere to a constant acts by scalar multiplication. -/
theorem multiplicationOperator_of_ae_eq_const {a : Lp ℂ ∞ μ} {c : ℂ}
    (ha : a =ᵐ[μ] fun _ ↦ c) :
    multiplicationOperator (E := E) a = c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
  ext f
  filter_upwards [multiplicationOperator_ae a f, Lp.coeFn_smul c f, ha] with x h hf ha'
  simp [h, hf, ha']

end NormedSpace

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The adjoint of multiplication by `a` is multiplication by its complex conjugate. -/
theorem adjoint_multiplicationOperator (a : Lp ℂ ∞ μ) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Lp E 2 μ) (F := Lp E 2 μ)
      (multiplicationOperator (E := E) a) =
      multiplicationOperator (E := E) (star a) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multiplicationOperator_ae (star a) f,
    multiplicationOperator_ae a g, Lp.coeFn_star a] with x hf hg ha
  simp [hf, hg, ha, inner_smul_left, inner_smul_right]

end InnerProductSpace

section FiniteMeasure

variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsFiniteMeasure μ]

@[simp]
theorem multiplicationOperator_const (c : ℂ) :
    multiplicationOperator (E := E) (Lp.const ∞ μ c) =
      c • ContinuousLinearMap.id ℂ (Lp E 2 μ) :=
  multiplicationOperator_of_ae_eq_const (Lp.coeFn_const (μ := μ) ∞ c)

end FiniteMeasure

section ExactNorm

variable [IsFiniteMeasure μ]

/-- On a finite measure space, the operator norm of scalar multiplication by `a` is exactly the
`L∞` norm of `a`. -/
theorem norm_multiplicationOperator (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := ℂ) a‖ = ‖a‖ := by
  apply le_antisymm (norm_multiplicationOperator_le a)
  by_contra hle
  have hlt : ‖multiplicationOperator (E := ℂ) a‖ < ‖a‖ := lt_of_not_ge hle
  let c := (‖multiplicationOperator (E := ℂ) a‖ + ‖a‖) / 2
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hop_lt_c : ‖multiplicationOperator (E := ℂ) a‖ < c := by
    dsimp [c]
    linarith
  have hc_lt : c < ‖a‖ := by
    dsimp [c]
    linarith
  let s := {x | c < ‖a x‖}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const (Lp.stronglyMeasurable a).norm.measurable
  have hμs : μ s ≠ 0 := by
    intro hμs_zero
    have hae : ∀ᵐ x ∂μ, ‖a x‖ ≤ c :=
      (measure_eq_zero_iff_ae_notMem.mp hμs_zero).mono fun x hx ↦ le_of_not_gt hx
    have hess : eLpNormEssSup a μ ≤ ENNReal.ofReal c :=
      eLpNormEssSup_le_of_ae_bound hae
    have ha_le : ‖a‖ ≤ c := by
      rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable a)]
      calc
        ENNReal.toReal (eLpNormEssSup a μ) ≤ ENNReal.toReal (ENNReal.ofReal c) :=
          ENNReal.toReal_mono (by finiteness) hess
        _ = c := ENNReal.toReal_ofReal hc_nonneg
    exact (not_lt_of_ge ha_le) hc_lt
  let f : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  have hf_pos : 0 < ‖f‖ := by
    change 0 < ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)‖
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    have hμs_real : μ.real s ≠ 0 :=
      (measureReal_ne_zero_iff (μ := μ) (s := s)).mpr hμs
    have hμs_pos : 0 < μ.real s := lt_of_le_of_ne measureReal_nonneg (Ne.symm hμs_real)
    rw [norm_one, one_mul]
    exact Real.rpow_pos_of_pos hμs_pos _
  have hfcoe : f =ᵐ[μ] s.indicator fun _ ↦ (1 : ℂ) := by
    simpa only [f] using
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s)
        (c := (1 : ℂ)))
  let g : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ)
  have hgcoe : g =ᵐ[μ] s.indicator fun _ ↦ (c : ℂ) := by
    simpa only [g] using
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s)
        (c := (c : ℂ)))
  have hpoint : ∀ᵐ x ∂μ,
      ‖g x‖ ≤ ‖multiplicationOperator (E := ℂ) a f x‖ := by
    filter_upwards [multiplicationOperator_ae a f, hfcoe, hgcoe] with x hmul hf hg
    by_cases hx : x ∈ s
    · have hf_one : f x = 1 := hf.trans (Set.indicator_of_mem hx (fun _ ↦ (1 : ℂ)))
      have hg_c : g x = c := hg.trans (Set.indicator_of_mem hx (fun _ ↦ (c : ℂ)))
      rw [hmul, hf_one, hg_c]
      simpa [abs_of_nonneg hc_nonneg] using (show c ≤ ‖a x‖ from hx.le)
    · have hf_zero : f x = 0 := hf.trans (Set.indicator_of_notMem hx (fun _ ↦ (1 : ℂ)))
      have hg_zero : g x = 0 := hg.trans (Set.indicator_of_notMem hx (fun _ ↦ (c : ℂ)))
      simp [hmul, hf_zero, hg_zero]
  have hlower : c * ‖f‖ ≤ ‖multiplicationOperator (E := ℂ) a f‖ := by
    calc
      c * ‖f‖ = ‖g‖ := by
        change c * ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)‖ =
          ‖indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ)‖
        rw [norm_indicatorConstLp (by norm_num) (by norm_num),
          norm_indicatorConstLp (by norm_num) (by norm_num)]
        simp [abs_of_nonneg hc_nonneg]
      _ ≤ ‖multiplicationOperator (E := ℂ) a f‖ := Lp.norm_le_norm_of_ae_le hpoint
  have hcancel : c * ‖f‖ ≤ ‖multiplicationOperator (E := ℂ) a‖ * ‖f‖ :=
    hlower.trans (ContinuousLinearMap.le_opNorm _ _)
  have := le_of_mul_le_mul_right hcancel hf_pos
  exact (not_le_of_gt hop_lt_c) this

end ExactNorm

end MeasureTheory.Lp
