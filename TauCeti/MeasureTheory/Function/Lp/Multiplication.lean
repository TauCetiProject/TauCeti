/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra
import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication

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

/-- `multiplicationOperator a` is `operatorMultiplication 2` by `a • 1`. -/
private theorem multiplicationOperator_eq_operatorMultiplication (a : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) a =
      operatorMultiplication 2 (a • (1 : Lp (E →L[ℂ] E) ∞ μ)) := by
  ext1 f
  rw [multiplicationOperator_apply, operatorMultiplication_lpSMul_left,
    operatorMultiplication_one, id_apply]

private theorem coeFn_lpSMul_one (a : Lp ℂ ∞ μ) :
    (a • (1 : Lp (E →L[ℂ] E) ∞ μ) : Lp (E →L[ℂ] E) ∞ μ) =ᵐ[μ] fun x ↦ a x • 1 := by
  filter_upwards [coeFn_lpSMul (r := ∞) a (1 : Lp (E →L[ℂ] E) ∞ μ),
    coeFn_one (E := E →L[ℂ] E) (μ := μ)] with x hx h1
  rw [hx, Pi.smul_apply', h1, Pi.one_apply]

/-- Composing multiplication operators multiplies their symbols in the same order. -/
theorem multiplicationOperator_comp_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    multiplicationOperator (E := E) a ∘L multiplicationOperator b =
      multiplicationOperator (a * b) := by
  simp only [multiplicationOperator_eq_operatorMultiplication,
    operatorMultiplication_comp_operatorMultiplication]
  congr 1; apply Lp.ext
  filter_upwards [coeFn_mul (a • (1 : Lp (E →L[ℂ] E) ∞ μ)) (b • 1), coeFn_lpSMul_one (E := E) a,
    coeFn_lpSMul_one (E := E) b, coeFn_lpSMul_one (E := E) (a * b), coeFn_mul a b]
    with x h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.mul_apply, h₂, h₃, h₄, h₅, Pi.mul_apply, smul_mul_smul_comm, one_mul]

/-- Multiplication operators commute with each other. -/
theorem commute_multiplicationOperator (a b : Lp ℂ ∞ μ) :
    Commute (multiplicationOperator (E := E) a) (multiplicationOperator b) := by
  rw [commute_iff_eq, mul_def, mul_def, multiplicationOperator_comp_multiplicationOperator,
    multiplicationOperator_comp_multiplicationOperator, mul_comm]

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

/-- The scalar embedding into L∞ acts on L² by scalar multiplication. -/
@[simp]
theorem multiplicationOperator_algebraMap (c : ℂ) :
    multiplicationOperator (E := E) (algebraMap ℂ (Lp ℂ ∞ μ) c) =
      c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
  rw [multiplicationOperator_eq_operatorMultiplication,
    ← operatorMultiplication_algebraMap (p := 2)]
  congr 1; apply Lp.ext
  filter_upwards [coeFn_lpSMul_one (E := E) _, coeFn_algebraMap (R := ℂ) (μ := μ) c,
    coeFn_algebraMap (R := E →L[ℂ] E) (μ := μ) c] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, Algebra.algebraMap_self_apply, Algebra.algebraMap_eq_smul_one]

end NormedSpace

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The adjoint of multiplication by `a` is multiplication by its complex conjugate. -/
@[simp]
theorem adjoint_multiplicationOperator (a : Lp ℂ ∞ μ) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Lp E 2 μ) (F := Lp E 2 μ)
      (multiplicationOperator (E := E) a) =
      multiplicationOperator (E := E) (star a) := by
  simp only [multiplicationOperator_eq_operatorMultiplication, adjoint_operatorMultiplication]
  congr 1; apply Lp.ext
  filter_upwards [coeFn_star (a • (1 : Lp (E →L[ℂ] E) ∞ μ)), coeFn_lpSMul_one (E := E) a,
    coeFn_lpSMul_one (E := E) (star a), coeFn_star a] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.star_apply, h₂, h₃, h₄, Pi.star_apply, star_smul, star_one]

end InnerProductSpace

section FiniteMeasure

variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsFiniteMeasure μ]

@[simp]
theorem multiplicationOperator_const (c : ℂ) :
    multiplicationOperator (E := E) (Lp.const ∞ μ c) =
      c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
  rw [← multiplicationOperator_algebraMap, Lp.algebraMap_eq_const, Algebra.algebraMap_self_apply]

end FiniteMeasure

section ExactNorm

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On a sigma-finite measure space, the operator norm of multiplication by `a` on `L²` with
values in a nontrivial space is exactly the `L∞` norm of `a`. -/
@[simp]
theorem norm_multiplicationOperator [SigmaFinite μ] [Nontrivial E] (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator (E := E) a‖ = ‖a‖ := by
  rw [multiplicationOperator_eq_operatorMultiplication, norm_operatorMultiplication]
  have h : ∀ᵐ x ∂μ, ‖(a • (1 : Lp (E →L[ℂ] E) ∞ μ) : Lp (E →L[ℂ] E) ∞ μ) x‖ = ‖a x‖ :=
    (coeFn_lpSMul_one (E := E) a).mono fun x hx ↦ by
      rw [hx, norm_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id, mul_one]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx ↦ hx.ge))

end ExactNorm

end MeasureTheory.Lp
