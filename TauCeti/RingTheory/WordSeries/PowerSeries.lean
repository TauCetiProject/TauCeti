/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WordSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# One-letter word series and ordinary power series

For a one-element alphabet, a word is determined by its length. The ring equivalence
`TauCeti.WordSeries.powerSeriesEquiv` identifies its coefficient with the coefficient of that
degree in Mathlib's `PowerSeries`. It preserves constant series and sends the ordinary
indeterminate to the unique letter. The multiplication comparison identifies the cuts of a
word with the natural-number antidiagonal, so it respects the formal Cauchy product.
-/

public section

noncomputable section

namespace TauCeti.WordSeries

variable {ι R : Type*} [Semiring R] [Unique ι]

/-- On a one-element alphabet, ordinary power series are exactly word series. The coefficient
of a word is the coefficient of its length. -/
def powerSeriesEquiv : PowerSeries R ≃+* WordSeries ι R where
  toFun p := mk fun w => PowerSeries.coeff w.toList.length p
  invFun f := PowerSeries.mk fun n => coeff (FreeMonoid.ofList (List.replicate n default)) f
  left_inv p := by
    ext n
    simp
  right_inv f := by
    ext w
    simp only [coeff_mk, PowerSeries.coeff_mk]
    have hw : FreeMonoid.ofList (List.replicate w.toList.length default) = w := by
      apply FreeMonoid.ext
      exact (List.eq_replicate_length.mpr (fun _ _ => Subsingleton.elim _ _)).symm
    rw [hw]
  map_add' p q := by
    ext w
    simp
  map_mul' p q := by
    ext w
    rw [coeff_mul, FreeMonoid.sum_mulAntidiagonal]
    simp only [coeff_mk, List.length_take, List.length_drop]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.min_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

@[simp] theorem coeff_powerSeriesEquiv (p : PowerSeries R) (w : FreeMonoid ι) :
    coeff w (powerSeriesEquiv p : WordSeries ι R) = PowerSeries.coeff w.toList.length p := by
  simp [powerSeriesEquiv]

@[simp] theorem coeff_powerSeriesEquiv_symm (f : WordSeries ι R) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesEquiv.symm f) =
      coeff (FreeMonoid.ofList (List.replicate n default)) f := by
  simp [powerSeriesEquiv]

@[simp] theorem powerSeriesEquiv_C (r : R) :
    powerSeriesEquiv (PowerSeries.C r) = (C r : WordSeries ι R) := by
  ext w
  classical
  simp only [coeff_powerSeriesEquiv, PowerSeries.coeff_C, coeff_C]
  have hw : w.toList.length = 0 ↔ w = 1 :=
    ⟨fun h => FreeMonoid.ext (List.length_eq_zero_iff.mp h), fun h => by simp [h]⟩
  simp only [hw]

@[simp] theorem powerSeriesEquiv_X :
    powerSeriesEquiv (PowerSeries.X : PowerSeries R) = (X default : WordSeries ι R) := by
  ext w
  classical
  simp only [coeff_powerSeriesEquiv, PowerSeries.coeff_X, coeff_X]
  congr 1
  apply propext
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp h
    apply FreeMonoid.ext
    simpa [Subsingleton.elim i default] using hi
  · intro h
    simp [h]

end TauCeti.WordSeries
