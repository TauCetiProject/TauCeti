/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of number fields

This file records general facts about the finite places of a number field.

The valuation dictionary `FinitePlace.mk_apply_le_one_iff` and
`FinitePlace.mk_apply_eq_one_iff` compares the finite-place absolute value with the adic valuation.
These comparisons follow Ralf Stephan's `ArithmeticHeights/SUnit.lean` in
`rwst/Subspace-Theorems` at `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).

The file also records that a number field always *has* a finite place: the finite places are the
height one primes of its ring of integers, and that ring is a Dedekind domain which is not a
field, so it has a maximal ideal. Recording this as a `Nonempty` instance lets local-global
arguments pick a finite place with `Classical.arbitrary` whenever a hypothesis quantified over
all finite places has to be used at some place — for instance to read off an invariant, such as
the dimension of the underlying space, that is the same at every place. Without the instance
each such argument has to rebuild the existence proof inline.
-/

public section
noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K]

/-- A number field has a finite place: its ring of integers is not a field. -/
instance [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) :=
  ⟨(HeightOneSpectrum.equivMaximalSpectrum (RingOfIntegers.not_isField K)).symm
    (Classical.choice (inferInstance : Nonempty (MaximalSpectrum (𝓞 K))))⟩

end TauCeti

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- An element is integral at a prime iff its finite-place absolute value is at most one. -/
theorem mk_apply_le_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

/-- An element has valuation one at a prime iff its finite-place absolute value is one. -/
theorem mk_apply_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x = 1 ↔ v.valuation K x = 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (HeightOneSpectrum.absNorm_ne_zero v)
    (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

end NumberField.FinitePlace
