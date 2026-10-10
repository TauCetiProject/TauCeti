/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Weakly regular sequences of length two in a ring

A sequence `[f, g]` of elements of a commutative ring `R` is weakly regular on `R` exactly when `f`
is a nonzerodivisor and `g` is a nonzerodivisor modulo `f`, that is, `f ∣ g * a` implies `f ∣ a`.
This file records this divisibility form of `RingTheory.Sequence.IsWeaklyRegular` and the
consequence that `f ^ n ∣ g ^ j * a` implies `f ^ n ∣ a`. The latter is the step that clears
denominators when comparing fractions `a / fⁿ` and `b / gᵏ`, as in the computation of the global
sections of a projective spectrum from two standard affine charts.

## Main results

* `RingTheory.Sequence.isWeaklyRegular_pair_iff`: `[f, g]` is weakly regular on `R` if and only if
  `f` is a nonzerodivisor of `R` and `f ∣ g * a` implies `f ∣ a`.
* `RingTheory.Sequence.IsWeaklyRegular.pow_dvd_of_pow_dvd_pow_mul`: for a weakly regular sequence
  `[f, g]`, `f ^ n ∣ g ^ j * a` implies `f ^ n ∣ a`.
-/

public section

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] {f g : R}

/-- A sequence `[f, g]` is weakly regular on a commutative ring `R` exactly when `f` is a
nonzerodivisor of `R` and `g` is a nonzerodivisor modulo `f`, in the form `f ∣ g * a → f ∣ a`. -/
theorem isWeaklyRegular_pair_iff :
    IsWeaklyRegular R [f, g] ↔ f ∈ nonZeroDivisors R ∧ ∀ a : R, f ∣ g * a → f ∣ a := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff, ← isLeftRegular_iff,
    isLeftRegular_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]
  refine and_congr_right fun _ ↦ isSMulRegular_iff_right_eq_zero_of_smul.trans
    ⟨fun h a ⟨b, hb⟩ ↦ ?_, fun h x hx ↦ ?_⟩
  · -- `a` vanishes in `R ⧸ f • R` because `g * a = f * b` does
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
      (Submodule.Quotient.mk_eq_zero _).mp <| h (Submodule.Quotient.mk a) <| by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, hb, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    exact ⟨c, hc.symm⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, -, hb⟩ := hx
    obtain ⟨c, rfl⟩ := h a ⟨b, hb.symm⟩
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- If `[f, g]` is a weakly regular sequence on `R`, then `f ^ n ∣ g ^ j * a` implies
`f ^ n ∣ a`. -/
theorem IsWeaklyRegular.pow_dvd_of_pow_dvd_pow_mul (h : IsWeaklyRegular R [f, g]) {n j : ℕ}
    {a : R} (hfa : f ^ n ∣ g ^ j * a) : f ^ n ∣ a := by
  obtain ⟨hf₀, hg⟩ := isWeaklyRegular_pair_iff.mp h
  -- `g ^ j` is a nonzerodivisor modulo `f`
  have hgj (j : ℕ) (a : R) (ha : f ∣ g ^ j * a) : f ∣ a := by
    induction j generalizing a with
    | zero => simpa using ha
    | succ j ih => exact hg a (ih _ (by rwa [← mul_assoc, ← pow_succ]))
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨b, rfl⟩ := hgj j a (dvd_trans (dvd_pow_self f n.succ_ne_zero) hfa)
    rw [pow_succ', dvd_cancel_left_mem_nonZeroDivisors hf₀]
    rw [pow_succ', mul_left_comm, dvd_cancel_left_mem_nonZeroDivisors hf₀] at hfa
    exact ih hfa

end RingTheory.Sequence
