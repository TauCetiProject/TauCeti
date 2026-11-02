/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import TauCeti.Analysis.AbsoluteValue.Archimedean
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Absolute values of a field extension lying over an infinite place

Let `F / K` be a field extension and `v` an infinite place of `K`. This file shows that the
absolute values `w : AbsoluteValue F ℝ` lying over `v`, in the sense of Mathlib's
`AbsoluteValue.LiesOver`, that is, whose restriction to `K` is `v` on the nose, are exactly the
underlying absolute values of the infinite places of `F` lying over `v`. Unlike the finite case,
no root is taken: an infinite place restricts to an infinite place without changing exponents.

This is what lets statements about a finite extension take an absolute value lying over an
infinite place of the base without passing to a completion.

## Main results

* `NumberField.isInfinitePlace_iff_forall_apply_natCast`: an absolute value on a field is an
  infinite place if and only if it takes the value `n` at every natural number `n`.
* `NumberField.isInfinitePlace_of_liesOver`: an absolute value lying over an infinite place is an
  infinite place.
* `NumberField.liesOver_infinitePlace_iff`: the absolute values lying over `v` are exactly the
  underlying absolute values of the infinite places of `F` lying over `v`.
* `NumberField.not_isNonarchimedean_of_liesOver`: such an absolute value is archimedean.
* `NumberField.finite_setOf_liesOver_infinitePlace` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: for a number field `F`, respectively an
  algebraic extension `F / K`, the absolute values of `F` lying over `v` form a finite,
  respectively nonempty, set.

## Implementation notes

An absolute value `w` lying over `v` agrees with `v` on the natural numbers, where `v` is the
usual absolute value. By `AbsoluteValue.exists_ringHom_complex_apply_eq_norm`, which runs the real
Gelfand–Mazur theorem in the completion of `F` at `w`, it is then `x ↦ ‖φ x‖` for some
`φ : F →+* ℂ`. No hypothesis on `K` or `F / K` is needed for this.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {w : AbsoluteValue F ℝ}

/-- An absolute value on a field is an infinite place if and only if it takes the value `n` at
every natural number `n`. -/
theorem isInfinitePlace_iff_forall_apply_natCast :
    IsInfinitePlace w ↔ ∀ n : ℕ, w n = n := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨φ, rfl⟩ n
    simp [place_apply]
  · obtain ⟨φ, hφ⟩ := exists_ringHom_complex_apply_eq_norm h
    exact ⟨φ, AbsoluteValue.ext fun x ↦ (hφ x).symm⟩

/-- An absolute value of a field extension lying over an infinite place of the base is an infinite
place. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w :=
  isInfinitePlace_iff_forall_apply_natCast.mpr fun n ↦ by
    rw [← map_natCast (algebraMap K F), LiesOver.apply_algebraMap v.1, ← InfinitePlace.coe_apply,
      InfinitePlace.map_natCast]

/-- The absolute values of a field extension lying over an infinite place `v` of the base are
exactly the underlying absolute values of the infinite places lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
    exact ⟨w', ‹_›, rfl⟩
  · rintro ⟨w', hw', rfl⟩
    exact hw'

/-- An absolute value of a field extension lying over an infinite place of the base is
archimedean. -/
theorem not_isNonarchimedean_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ¬IsNonarchimedean w := by
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact w'.not_isNonarchimedean

/-- A number field has only finitely many absolute values lying over a given infinite place of a
subfield. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  refine (Set.finite_range fun w' : InfinitePlace F ↦ w'.1).subset fun w (hw : w.LiesOver _) ↦ ?_
  obtain ⟨w', -, rfl⟩ := liesOver_infinitePlace_iff.mp hw
  exact ⟨w', rfl⟩

/-- Every infinite place of `K` has an absolute value of an algebraic extension lying over it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w'.1, InfinitePlace.liesOver_iff_comap_eq.mpr hw'⟩

end NumberField
