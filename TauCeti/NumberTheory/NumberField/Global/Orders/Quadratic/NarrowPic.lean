/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.NarrowPic
import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.InfinitePlace
import TauCeti.RingTheory.FractionalIdeal.Operations

/-!
# Positive-norm generators for quadratic narrow ideal classes

For an order in a quadratic number field, a principal ideal admits a totally positive
generator exactly when it admits a generator of positive norm. An element of positive
norm is totally positive up to a global sign, and negation preserves its principal ideal.
Thus the existing narrow Picard group also has the positive-norm generator criterion used
in the correspondence with primitive binary forms.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
-/

public section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace NumberFieldOrder

/-- For a quadratic order, narrowly principal ideals are exactly those with a positive-norm
generator. The narrow principal subgroup retains its totally-positive definition. -/
theorem mem_narrowPrincipal_iff_exists_norm_pos (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) {I : O.invertibleProperFractionalIdeals} :
    I ∈ O.narrowPrincipal ↔
      ∃ x : Kˣ, 0 < Algebra.norm ℚ (x : K) ∧ toPrincipalIdeal O.toSubalgebra K x = I := by
  rw [mem_narrowPrincipal_iff]
  constructor
  · rintro ⟨x, hx, hI⟩
    exact ⟨x, norm_pos_of_isTotallyPositive x.ne_zero hx, hI⟩
  · rintro ⟨x, hx, hI⟩
    obtain ⟨θ, d, hmin, hgen, -⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
    rcases isTotallyPositive_or_isTotallyPositive_neg_of_norm_pos hmin hgen hx with h | h
    · exact ⟨x, h, hI⟩
    · refine ⟨-x, by simpa using h, ?_⟩
      exact (toPrincipalIdeal_neg x).trans hI

end NumberFieldOrder

namespace NarrowPic

/-- Two quadratic-order ideals have equal narrow classes exactly when they differ by a
principal ideal admitting a positive-norm generator. -/
theorem mk_eq_mk_iff_exists_norm_pos (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) {I J : O.invertibleProperFractionalIdeals} :
    mk O I = mk O J ↔
      ∃ x : Kˣ, 0 < Algebra.norm ℚ (x : K) ∧
        I * toPrincipalIdeal O.toSubalgebra K x = J := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨P, hP, hIP⟩
    obtain ⟨x, hx, rfl⟩ := (O.mem_narrowPrincipal_iff_exists_norm_pos hK).mp hP
    exact ⟨x, hx, hIP⟩
  · rintro ⟨x, hx, hIJ⟩
    exact ⟨toPrincipalIdeal O.toSubalgebra K x,
      (O.mem_narrowPrincipal_iff_exists_norm_pos hK).mpr ⟨x, hx, rfl⟩, hIJ⟩

/-- A positive-norm element generates the trivial narrow class in a quadratic order. -/
theorem mkPrincipal_eq_one_of_norm_pos (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) {x : Kˣ} (hx : 0 < Algebra.norm ℚ (x : K)) :
    mkPrincipal O x = 1 := by
  rw [mkPrincipal_apply, mk_eq_one_iff, O.mem_narrowPrincipal_iff_exists_norm_pos hK]
  exact ⟨x, hx, rfl⟩

end NarrowPic

end TauCeti.GlobalNumberFields
