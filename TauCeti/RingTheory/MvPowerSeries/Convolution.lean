/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Convolution of power series with coefficient families

Let `R` be a semiring and `E` an `R`-module. A formal power series `f : MvPowerSeries σ R` acts
on a coefficient family `a : (σ →₀ ℕ) → E` by convolution,

```text
(f • a) t = ∑_{p + q = t} f_p • a_q.
```

This file defines the convolution `MvPowerSeries.convSMul` and proves its module laws: it is
additive in both arguments, constant series act through their constants, and it is compatible
with multiplication of series. For `E = R` it is the coefficient family of the product
(`MvPowerSeries.convSMul_coeff`), and linear maps of coefficient modules commute with it
(`MvPowerSeries.convSMul_comp`). No norm or topology is needed.

## Implementation notes

The reindexing bijection in `MvPowerSeries.mul_convSMul` is the one Mathlib uses to prove
associativity of multiplication, `MvPowerSeries.mul_assoc`.
-/

public section

open Finset

namespace MvPowerSeries

variable {σ R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]

/-- The convolution action of a formal power series `f` on a coefficient family `a`: the
coefficient of `f • a` at `t` is `∑_{p + q = t} f_p • a_q`. For `E = R` this is the coefficient
family of the product (`MvPowerSeries.convSMul_coeff`). -/
noncomputable def convSMul (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) : (σ →₀ ℕ) → E :=
  letI := Classical.decEq σ
  fun t ↦ ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2

theorem convSMul_apply [DecidableEq σ] (f : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E)
    (t : σ →₀ ℕ) : convSMul f a t = ∑ p ∈ antidiagonal t, coeff p.1 f • a p.2 := by
  rw [convSMul, Subsingleton.elim (Classical.decEq σ) ‹DecidableEq σ›]

@[simp]
theorem zero_convSMul (a : (σ →₀ ℕ) → E) : convSMul (0 : MvPowerSeries σ R) a = 0 := by
  classical
  ext t
  simp [convSMul_apply]

@[simp]
theorem convSMul_zero (f : MvPowerSeries σ R) : convSMul f (0 : (σ →₀ ℕ) → E) = 0 := by
  classical
  ext t
  simp [convSMul_apply]

theorem add_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f + g) a = convSMul f a + convSMul g a := by
  classical
  ext t
  simp [convSMul_apply, add_smul, Finset.sum_add_distrib]

theorem convSMul_add (f : MvPowerSeries σ R) (a b : (σ →₀ ℕ) → E) :
    convSMul f (a + b) = convSMul f a + convSMul f b := by
  classical
  ext t
  simp [convSMul_apply, smul_add, Finset.sum_add_distrib]

/-- A constant series acts on coefficient families through its constant. -/
@[simp]
theorem C_convSMul (r : R) (a : (σ →₀ ℕ) → E) : convSMul (C r : MvPowerSeries σ R) a = r • a := by
  classical
  ext t
  rw [convSMul_apply, Finset.sum_eq_single_of_mem (0, t) (by simp)]
  · simp
  · rintro ⟨p, q⟩ hpq hne
    have hp : p ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hpq)
    simp [coeff_C, hp]

@[simp]
theorem one_convSMul (a : (σ →₀ ℕ) → E) : convSMul (1 : MvPowerSeries σ R) a = a := by
  simpa using C_convSMul (σ := σ) (1 : R) a

/-- Convolution is compatible with multiplication of series. -/
theorem mul_convSMul (f g : MvPowerSeries σ R) (a : (σ →₀ ℕ) → E) :
    convSMul (f * g) a = convSMul f (convSMul g a) := by
  classical
  ext t
  simp only [convSMul_apply, coeff_mul, Finset.sum_smul, Finset.smul_sum, mul_smul,
    Finset.sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc])

/-- An `R`-linear map of coefficient modules commutes with convolution. -/
theorem convSMul_comp [AddCommMonoid F] [Module R F] (φ : E →ₗ[R] F) (f : MvPowerSeries σ R)
    (a : (σ →₀ ℕ) → E) : convSMul f (φ ∘ a) = φ ∘ convSMul f a := by
  classical
  ext t
  simp [convSMul_apply]

/-- For coefficients in the ring itself, convolution with the coefficients of `g` gives the
coefficients of the product `f * g`. -/
theorem convSMul_coeff (f g : MvPowerSeries σ R) :
    convSMul f (fun t ↦ coeff t g) = fun t ↦ coeff t (f * g) := by
  classical
  ext t
  simp [convSMul_apply, coeff_mul]

end MvPowerSeries
