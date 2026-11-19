/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Kernel.PMF
public import TauCeti.Probability.Kernel.Composition.Power
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Finite transition matrices and Markov kernels

The singleton masses of a finite kernel form a matrix with nonnegative real entries.
On finite state spaces, Markov kernels correspond exactly to Mathlib's row-stochastic
matrices. Matrix multiplication follows the order in which transitions are taken:
`(η ∘ₖ κ).toMatrix = κ.toMatrix * η.toMatrix`. In particular, kernel powers become
matrix powers and propagation of an initial law becomes row-vector multiplication.

The inverse construction uses `Kernel.ofPMF` and `PMF.ofFintype`; no new probability-vector
or stochastic-matrix structure is introduced. The correspondence includes the empty state
space, where both the kernel and the matrix are unique.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The nonnegative real singleton-mass matrix of a kernel, with the source indexing rows.
Infinite masses become zero, following `ENNReal.toNNReal`. For finite kernels,
`coe_toMatrix_apply` recovers the original masses. -/
def toMatrix (κ : Kernel α β) : Matrix α β ℝ≥0 :=
  fun a b => (κ a {b}).toNNReal

/-- The entries of the transition matrix are the singleton masses of the kernel. -/
@[simp]
theorem toMatrix_apply (κ : Kernel α β) (a : α) (b : β) :
    κ.toMatrix a b = (κ a {b}).toNNReal := (rfl)

/-- Coercing a transition-matrix entry to the extended nonnegative reals recovers its mass. -/
theorem coe_toMatrix_apply (κ : Kernel α β) [IsFiniteKernel κ] (a : α) (b : β) :
    (κ.toMatrix a b : ℝ≥0∞) = κ a {b} :=
  ENNReal.coe_toNNReal (measure_ne_top _ _)

/-- Finite kernels with countable target are determined by their transition matrices. -/
@[simp]
theorem toMatrix_inj [Countable β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    κ.toMatrix = η.toMatrix ↔ κ = η := by
  constructor
  · intro h
    ext a : 1
    apply Measure.ext_iff_singleton.mpr
    intro b
    simpa only [coe_toMatrix_apply] using
      congrArg (fun M : Matrix α β ℝ≥0 => (M a b : ℝ≥0∞)) h
  · rintro rfl
    rfl

/-- Composition of finite kernels is matrix multiplication, in transition order. -/
@[simp]
theorem toMatrix_comp [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (κ : Kernel α β) (η : Kernel β γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    (η ∘ₖ κ).toMatrix = κ.toMatrix * η.toMatrix := by
  funext a c
  apply ENNReal.coe_injective
  simp only [coe_toMatrix_apply, Matrix.mul_apply, ENNReal.ofNNReal_finsetSum,
    ENNReal.coe_mul]
  rw [comp_apply' _ _ _ (measurableSet_singleton _), lintegral_fintype]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- The identity kernel has the identity transition matrix. -/
@[simp]
theorem toMatrix_id [DecidableEq α] [MeasurableSingletonClass α] :
    (Kernel.id : Kernel α α).toMatrix = 1 := by
  funext a b
  by_cases h : a = b <;> simp [Kernel.id_apply, Matrix.one_apply, Measure.dirac_apply', h]

/-- Kernel powers give the usual powers of the transition matrix. -/
@[simp]
theorem toMatrix_pow [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
    (κ : Kernel α α) [IsFiniteKernel κ] (n : ℕ) :
    (κ ^ n).toMatrix = κ.toMatrix ^ n := by
  induction n with
  | zero => exact toMatrix_id
  | succ n ih =>
    rw [Kernel.pow_add, pow_one, toMatrix_comp, ih, pow_succ']

/-- On a finite state space, a Markov kernel has a row-stochastic transition matrix. -/
theorem toMatrix_mem_rowStochastic [Fintype α] [DecidableEq α]
    [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ] :
    κ.toMatrix ∈ Matrix.rowStochastic ℝ≥0 α := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨fun _ _ => zero_le, fun a => ?_⟩
  apply ENNReal.coe_injective
  simp only [ENNReal.ofNNReal_finsetSum, coe_toMatrix_apply, ENNReal.coe_one]
  simp

/-- Propagating an initial finite measure is multiplication of its mass row vector by the
transition matrix. -/
theorem comp_apply_singleton_eq_vecMul [Fintype α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (κ : Kernel α β) [IsFiniteKernel κ]
    (ν : Measure α) [IsFiniteMeasure ν] (b : β) :
    ((κ ∘ₘ ν) {b}).toNNReal = ((fun a => (ν {a}).toNNReal) ᵥ* κ.toMatrix) b := by
  apply ENNReal.coe_injective
  simp only [ENNReal.coe_toNNReal (measure_ne_top _ _), Matrix.vecMul, dotProduct,
    ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul, coe_toMatrix_apply]
  rw [Measure.bind_apply (measurableSet_singleton _) κ.aemeasurable, lintegral_fintype]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end ProbabilityTheory.Kernel

namespace Matrix.rowStochastic

variable {α : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The Markov kernel with a given row-stochastic transition matrix. -/
def toKernel (M : rowStochastic ℝ≥0 α) : Kernel α α :=
  Kernel.ofPMF fun a => PMF.ofFintype (fun b => (M.val a b : ℝ≥0∞)) (by
    norm_cast
    exact sum_row_of_mem_rowStochastic M.property a)

instance (M : rowStochastic ℝ≥0 α) : IsMarkovKernel (toKernel M) :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofPMF _))

/-- The constructed kernel has the prescribed transition masses. -/
@[simp]
theorem toKernel_apply_singleton (M : rowStochastic ℝ≥0 α) (a b : α) :
    toKernel M a {b} = (M.val a b : ℝ≥0∞) := by
  simp [toKernel, PMF.ofFintype_apply]

/-- Converting a stochastic matrix to a kernel and back recovers the matrix. -/
@[simp]
theorem toMatrix_toKernel (M : rowStochastic ℝ≥0 α) : (toKernel M).toMatrix = M.val := by
  funext a b
  simp

/-- Stochastic-matrix multiplication performs the first transition and then the second. -/
@[simp]
theorem toKernel_mul (M N : rowStochastic ℝ≥0 α) :
    toKernel (M * N) = toKernel N ∘ₖ toKernel M := by
  apply (Kernel.toMatrix_inj _ _).mp
  simp only [toMatrix_toKernel, Kernel.toMatrix_comp, Submonoid.coe_mul]

/-- The identity stochastic matrix gives the identity kernel. -/
@[simp]
theorem toKernel_one : toKernel (1 : rowStochastic ℝ≥0 α) = Kernel.id := by
  apply (Kernel.toMatrix_inj _ _).mp
  simp only [toMatrix_toKernel, Kernel.toMatrix_id, Submonoid.coe_one]

/-- Powers of a stochastic matrix agree with powers of its Markov kernel. -/
@[simp]
theorem toKernel_pow (M : rowStochastic ℝ≥0 α) (n : ℕ) :
    toKernel (M ^ n) = (toKernel M) ^ n := by
  induction n with
  | zero => exact toKernel_one
  | succ n ih =>
    rw [pow_succ, toKernel_mul, ih]
    simpa only [pow_one, Nat.add_comm] using (Kernel.pow_add (toKernel M) 1 n).symm

end Matrix.rowStochastic

namespace ProbabilityTheory.Kernel

variable {α : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Converting a finite Markov kernel to its stochastic matrix and back recovers the kernel. -/
@[simp]
theorem toKernel_toMatrix (κ : Kernel α α) [IsMarkovKernel κ] :
    Matrix.rowStochastic.toKernel ⟨κ.toMatrix, κ.toMatrix_mem_rowStochastic⟩ = κ := by
  apply (toMatrix_inj _ _).mp
  simp only [Matrix.rowStochastic.toMatrix_toKernel]

/-- Finite Markov kernels correspond bijectively to row-stochastic matrices. Multiplication
corresponds to kernel composition in transition order, as in `Matrix.rowStochastic.toKernel_mul`. -/
def rowStochasticEquiv : Matrix.rowStochastic ℝ≥0 α ≃ {κ : Kernel α α // IsMarkovKernel κ} where
  toFun M := ⟨Matrix.rowStochastic.toKernel M, inferInstance⟩
  invFun κ := by
    let _ := κ.property
    exact ⟨κ.val.toMatrix, κ.val.toMatrix_mem_rowStochastic⟩
  left_inv M := Subtype.ext (Matrix.rowStochastic.toMatrix_toKernel M)
  right_inv κ := by
    let _ := κ.property
    exact Subtype.ext (toKernel_toMatrix κ.val)

/-- The matrix-to-kernel equivalence is the canonical kernel construction. -/
@[simp]
theorem rowStochasticEquiv_apply (M : Matrix.rowStochastic ℝ≥0 α) :
    (rowStochasticEquiv M).val = Matrix.rowStochastic.toKernel M := (rfl)

/-- The inverse equivalence reads off the matrix of transition masses. -/
@[simp]
theorem rowStochasticEquiv_symm_apply (κ : {κ : Kernel α α // IsMarkovKernel κ}) :
    (rowStochasticEquiv.symm κ).val = κ.val.toMatrix := (rfl)

end ProbabilityTheory.Kernel
