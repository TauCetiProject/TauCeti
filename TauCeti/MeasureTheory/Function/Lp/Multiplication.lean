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
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Multiplication operators on complex L²

An essentially bounded complex function `a` acts on `L²` by pointwise multiplication.  This file
bundles that action as `MeasureTheory.Lp.multiplicationOperator a` and records its algebraic,
adjoint, and norm properties.  In particular, on a sigma-finite measure space the operator norm on
`L²` with values in any nontrivial space is exactly the `L∞` norm of the symbol, and a symbol of
modulus one almost everywhere preserves the `L²` norm.

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
  rw [multiplicationOperator_apply]
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
@[simp]
theorem multiplicationOperator_add (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) (a + b) =
      multiplicationOperator a + multiplicationOperator b := by
  simp [multiplicationOperator]

/-- Multiplication operators depend complex-linearly on their symbols. -/
@[simp]
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

/-- Multiplication operators commute with each other. -/
theorem commute_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    Commute (multiplicationOperator (E := E) a) (multiplicationOperator b) := by
  refine (commute_iff_eq _ _).2 (ContinuousLinearMap.ext fun f ↦ Lp.ext ?_)
  filter_upwards [multiplicationOperator_ae a (multiplicationOperator b f),
    multiplicationOperator_ae b f, multiplicationOperator_ae b (multiplicationOperator a f),
    multiplicationOperator_ae a f] with x hab hb hba ha
  simp only [mul_apply_eq_comp, hab, hb, hba, ha, smul_smul, mul_comm]

/-- Multiplication by a symbol of modulus one almost everywhere preserves the `L²` norm. -/
theorem norm_multiplicationOperator_apply_of_ae_norm_eq_one {u : Lp ℂ ∞ μ}
    (hu : ∀ᵐ x ∂μ, ‖u x‖ = 1) (f : Lp E 2 μ) :
    ‖multiplicationOperator u f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂μ, ‖multiplicationOperator u f x‖ = ‖f x‖ := by
    filter_upwards [multiplicationOperator_ae u f, hu] with x hx hux
    rw [hx, norm_smul, hux, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.ge))

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
@[simp]
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

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `c ≤ ‖a‖` pointwise on `s`, then multiplication by `a` scales the `L²` norm of a constant
indicator of `s` by at least `c`. -/
private theorem mul_norm_indicatorConstLp_le {a : Lp ℂ ∞ μ} {c : ℝ} (hc_nonneg : 0 ≤ c)
    {s : Set α} (hs : MeasurableSet s) (hs_top : μ s ≠ ∞) (ha : ∀ x ∈ s, c ≤ ‖a x‖)
    (v : E) :
    c * ‖indicatorConstLp 2 hs hs_top v‖ ≤
      ‖multiplicationOperator a (indicatorConstLp 2 hs hs_top v)‖ := by
  set f := indicatorConstLp 2 hs hs_top v
  set g := indicatorConstLp 2 hs hs_top ((c : ℂ) • v)
  have hfg : c * ‖f‖ = ‖g‖ := by
    simp only [f, g, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_nonneg, mul_assoc]
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖multiplicationOperator a f x‖ := by
    filter_upwards [multiplicationOperator_ae a f, indicatorConstLp_coeFn (p := 2) (c := v),
      indicatorConstLp_coeFn (p := 2) (c := (c : ℂ) • v)] with x hmul hf hg
    rw [hmul, hf, hg]
    by_cases hx : x ∈ s
    · have hcx : c ≤ ‖a x‖ := ha x hx
      simp only [Set.indicator_of_mem hx, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc_nonneg]
      gcongr
    · simp [Set.indicator_of_notMem hx]
  rw [hfg]
  exact Lp.norm_le_norm_of_ae_le hpoint

/-- On a sigma-finite measure space, the operator norm of multiplication by `a` on `L²` with
values in a nontrivial space is exactly the `L∞` norm of `a`. -/
@[simp]
theorem norm_multiplicationOperator [SigmaFinite μ] [Nontrivial E] (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := E) a‖ = ‖a‖ := by
  apply le_antisymm (norm_multiplicationOperator_le a)
  by_contra hle
  have hlt : ‖multiplicationOperator (E := E) a‖ < ‖a‖ := lt_of_not_ge hle
  -- Test the operator on the indicator of the set where `‖a‖` exceeds a level `c` strictly
  -- between the operator norm and `‖a‖`.
  set c := (‖multiplicationOperator (E := E) a‖ + ‖a‖) / 2 with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have hop_lt_c : ‖multiplicationOperator (E := E) a‖ < c := by linarith [hc_def]
  have hc_lt : c < ‖a‖ := by linarith [hc_def]
  set s := {x | c < ‖a x‖}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable a).norm.measurable
  have hμs : μ s ≠ 0 := measure_lt_norm_ne_zero hc_nonneg hc_lt
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.mpr hμs)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set f := indicatorConstLp 2 ht hμt_top.ne v
  have hf_pos : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    have hμt_real_pos : 0 < μ.real t := ENNReal.toReal_pos hμt_pos.ne' hμt_top.ne
    exact mul_pos (norm_pos_iff.mpr hv) (Real.rpow_pos_of_pos hμt_real_pos _)
  -- Comparing the lower bound on `f` with the operator norm forces `c ≤ ‖M_a‖`.
  have hcancel : c * ‖f‖ ≤ ‖multiplicationOperator (E := E) a‖ * ‖f‖ :=
    (mul_norm_indicatorConstLp_le hc_nonneg ht hμt_top.ne
      (fun _ hx ↦ le_of_lt (hts hx)) v).trans
      (le_opNorm _ _)
  exact (not_le_of_gt hop_lt_c) (le_of_mul_le_mul_right hcancel hf_pos)

end ExactNorm

end MeasureTheory.Lp
