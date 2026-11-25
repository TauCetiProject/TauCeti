/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic

import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite differences of finitely supported sequences

Identity minus the left shift on finitely supported sequences is invertible: its inverse takes
finite tail sums. No completeness or divisibility assumptions on the coefficient group are needed.
-/

public section

namespace Finsupp

variable {A : Type*}

/-- The finitely supported sequence of finite tail sums. -/
noncomputable def tailSum [AddCommMonoid A] (f : ℕ →₀ A) : ℕ →₀ A :=
  f.sum (fun i a ↦ ∑ j ∈ Finset.Iic i, Finsupp.single j a)

/-- The tail at `n` sums the coefficients at all supported indices `i ≥ n`, including `n`. -/
@[simp]
theorem tailSum_apply [AddCommMonoid A] (f : ℕ →₀ A) (n : ℕ) :
    tailSum f n = f.sum (fun i a ↦ if n ≤ i then a else 0) := by
  simp [tailSum, Finsupp.sum_apply, Finset.sum_apply', Finsupp.single_apply]

/-- Identity minus the left shift, sending `f` to the sequence `n ↦ f n - f (n + 1)`. -/
noncomputable def oneSubShift [AddCommGroup A] : (ℕ →₀ A) →+ (ℕ →₀ A) :=
  AddMonoidHom.id _ - comapDomain.addMonoidHom Nat.succ_injective

@[simp]
theorem oneSubShift_apply [AddCommGroup A] (f : ℕ →₀ A) (n : ℕ) :
    oneSubShift f n = f n - f (n + 1) := by
  rfl

/-- Taking differences of the finite tail sums recovers the original sequence. -/
@[simp]
theorem oneSubShift_tailSum [AddCommGroup A] (f : ℕ →₀ A) :
    oneSubShift (tailSum f) = f := by
  ext n
  rw [oneSubShift_apply, tailSum_apply, tailSum_apply, ← sum_sub]
  calc
    _ = f.sum (fun i a ↦ if n = i then a else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp
      split_ifs <;> simp_all <;> omega
    _ = f n := sum_ite_self_eq f n

/-- Identity minus the left shift is injective on finitely supported sequences. -/
theorem oneSubShift_injective [AddCommGroup A] :
    Function.Injective (oneSubShift (A := A)) := by
  apply (injective_iff_map_eq_zero (oneSubShift (A := A))).2
  intro f hf
  have hstep (n : ℕ) : f n = f (n + 1) := by
    have h := DFunLike.congr_fun hf n
    simpa only [oneSubShift_apply, zero_apply, sub_eq_zero] using h
  have hconst (n : ℕ) : f n = f 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).symm.trans ih
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset f.support
  have hzero : f k = 0 := notMem_support_iff.mp hk
  ext n
  exact (hconst n).trans ((hconst k).symm.trans hzero)

/-- Taking finite tail sums of the differences recovers the original finitely supported sequence. -/
@[simp]
theorem tailSum_oneSubShift [AddCommGroup A] (f : ℕ →₀ A) :
    tailSum (oneSubShift f) = f :=
  oneSubShift_injective (oneSubShift_tailSum (oneSubShift f))

/-- Identity minus the left shift on finitely supported sequences, with inverse given by finite
tail sums. -/
noncomputable def oneSubShiftEquiv [AddCommGroup A] : (ℕ →₀ A) ≃+ (ℕ →₀ A) where
  toFun := oneSubShift
  invFun := tailSum
  map_add' := map_add oneSubShift
  left_inv := tailSum_oneSubShift
  right_inv := oneSubShift_tailSum

@[simp]
theorem oneSubShiftEquiv_apply [AddCommGroup A] (f : ℕ →₀ A) :
    oneSubShiftEquiv f = oneSubShift f := by
  rfl

@[simp]
theorem oneSubShiftEquiv_symm_apply [AddCommGroup A] (f : ℕ →₀ A) :
    oneSubShiftEquiv.symm f = tailSum f := by
  rfl

end Finsupp
