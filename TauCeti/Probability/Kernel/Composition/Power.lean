/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Invariance

/-!
# Powers of s-finite, finite and Markov kernels

Iterating an s-finite kernel remains s-finite; iterating a uniformly finite kernel remains
uniformly finite. The latter permits taking finite transition masses, and thus nonnegative real
transition matrices, for every iterate.
Iterating a Markov kernel also preserves the probability normalization of every row, and any
measure invariant under a kernel remains invariant under all its powers, as well as under scalar
multiples and binary sums.

The powers of a deterministic kernel are the deterministic kernels of the iterates. Restricting
the Chapman–Kolmogorov integral to one intermediate state bounds `(κ ^ (m + n)) x s` below by
`(κ ^ m) x {y} * (κ ^ n) y s`; this is how positivity of multi-step transition masses propagates
along paths of states.
-/

public section

open scoped ENNReal

namespace ProbabilityTheory

/-- Every natural power of an s-finite kernel is s-finite. -/
instance IsSFiniteKernel.pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsSFiniteKernel κ] (n : ℕ) : IsSFiniteKernel (κ ^ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsSFiniteKernel Kernel.id)
  | succ n ih =>
    -- Multiplication in the kernel monoid is composition.
    exact inferInstanceAs (IsSFiniteKernel ((κ ^ n) ∘ₖ κ))

/-- Every natural power of a finite kernel is finite. -/
instance IsFiniteKernel.pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsFiniteKernel κ] (n : ℕ) : IsFiniteKernel (κ ^ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteKernel Kernel.id)
  | succ n ih =>
    -- Multiplication in the kernel monoid is composition.
    exact inferInstanceAs (IsFiniteKernel ((κ ^ n) ∘ₖ κ))

/-- Every natural power of a Markov kernel is a Markov kernel. -/
instance IsMarkovKernel.pow {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    -- Multiplication in the kernel monoid is composition.
    exact inferInstanceAs (IsMarkovKernel ((κ ^ n) ∘ₖ κ))

namespace Kernel

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The unit of the monoid of kernels `Kernel α α` is the identity kernel. -/
theorem one_def : (1 : Kernel α α) = Kernel.id := (rfl)

/-- Every measure is invariant under the identity kernel. -/
@[simp]
theorem Invariant.id (μ : Measure α) : Kernel.id.Invariant μ :=
  Measure.id_comp

/-- A measure invariant under `κ` is invariant under every natural power `κ ^ n`. -/
theorem Invariant.pow {κ : Kernel α α} {μ : Measure α} (h : κ.Invariant μ) (n : ℕ) :
    (κ ^ n).Invariant μ := by
  induction n with
  | zero => simp [one_def]
  | succ n ih =>
    rw [pow_add, pow_one]
    exact ih.comp h

/-- The zero measure is invariant under every kernel. -/
@[simp]
theorem Invariant.zero (κ : Kernel α α) : κ.Invariant 0 :=
  Measure.bind_zero_left κ

/-- Scalar multiples of an invariant measure remain invariant. -/
theorem Invariant.smul {κ : Kernel α α} {μ : Measure α} (h : κ.Invariant μ) (c : ℝ≥0∞) :
    κ.Invariant (c • μ) := by
  rw [Invariant, Measure.comp_smul, h.def]

/-- The sum of two invariant measures is invariant. -/
theorem Invariant.add {κ : Kernel α α} {μ ν : Measure α}
    (hμ : κ.Invariant μ) (hν : κ.Invariant ν) :
    κ.Invariant (μ + ν) := by
  rw [Invariant, Measure.comp_add, hμ.def, hν.def]

/-- A kernel intertwining two one-step kernels also intertwines all their powers. -/
theorem comp_pow_eq_pow_comp_of_comp_eq {β : Type*} [MeasurableSpace β]
    {e : Kernel β α} {η : Kernel β β} {κ : Kernel α α}
    (h : e ∘ₖ η = κ ∘ₖ e) (n : ℕ) : e ∘ₖ (η ^ n) = (κ ^ n) ∘ₖ e := by
  induction n with
  | zero => simp [one_def]
  | succ n ih =>
    -- Use the composition form of powers; the monoid instance does not expose multiplication.
    simp only [Nat.add_comm n 1, pow_add, pow_one]
    rw [← comp_assoc, h, comp_assoc, ih, comp_assoc]

/-- The `n`-th power of the deterministic kernel of `f` is the deterministic kernel of the
`n`-th iterate of `f`. -/
@[simp]
theorem deterministic_pow {f : α → α} (hf : Measurable f) (n : ℕ) :
    deterministic f hf ^ n = deterministic f^[n] (hf.iterate n) := by
  induction n with
  | zero =>
    ext
    simp [one_def, id_apply, deterministic_apply]
  | succ n ih =>
    rw [pow_add, pow_one, ih, deterministic_comp_deterministic]
    simp_rw [Function.iterate_succ]

/-- **Chapman–Kolmogorov lower bound.** The `m + n`-step mass of a measurable set `s` is at least
the mass of the paths that sit at the intermediate state `y` at time `m`. -/
theorem pow_apply_singleton_mul_le_pow_add_apply (κ : Kernel α α) (m n : ℕ) (x y : α)
    {s : Set α} (hs : MeasurableSet s) :
    (κ ^ m) x {y} * (κ ^ n) y s ≤ (κ ^ (m + n)) x s := by
  rw [pow_add_apply_eq_lintegral _ _ _ _ hs, mul_comm,
    ← lintegral_singleton' ((κ ^ n).measurable_coe hs)]
  exact setLIntegral_le_lintegral _ _

/-- Positive multi-step masses compose: if `x` reaches `y` with positive probability in `m` steps
and `y` reaches `s` with positive probability in `n` steps, then `x` reaches `s` with positive
probability in `m + n` steps. -/
theorem pow_add_apply_pos {κ : Kernel α α} {m n : ℕ} {x y : α} {s : Set α}
    (hs : MeasurableSet s) (hxy : 0 < (κ ^ m) x {y}) (hy : 0 < (κ ^ n) y s) :
    0 < (κ ^ (m + n)) x s :=
  (ENNReal.mul_pos hxy.ne' hy.ne').trans_le
    (pow_apply_singleton_mul_le_pow_add_apply κ m n x y hs)

end Kernel

end ProbabilityTheory
