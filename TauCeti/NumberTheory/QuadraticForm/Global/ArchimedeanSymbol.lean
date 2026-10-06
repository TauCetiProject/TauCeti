/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.FieldTheory.SquareClassGroup.Real
import TauCeti.NumberTheory.HilbertSymbol.IsAlgClosed
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.HilbertSymbol.Archimedean
public import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# The archimedean Hilbert symbol

The archimedean symbol is the norm-equation Hilbert symbol read over the completion at an infinite
place.  This module records that symbol for *global* units at the *places of a number field*, the
square criterion for a global unit at a real place, and the real-place half of the sign
prescription.

At a real place the symbol of two elements is `-1` exactly when both are negative there, and `1`
exactly when one of them is positive there.  A product of such symbols over a prescribed set of
real places is therefore a product of signs, and the bimultiplicativity it needs is that of
`TauCeti.hilbertSymbol_real_mul_left` and `TauCeti.hilbertSymbol_real_mul_right`, in
`TauCeti.NumberTheory.HilbertSymbol.Archimedean`; both are `[simp]`, so `simp` expands a
product of global units inside the localized symbol.
At a complex place the symbol is `1` for the same reason the
archimedean classification of a form is by rank alone: every element of `ℂˣ` is a square, so
`TauCeti.hilbertSymbol_eq_one_of_isAlgClosed`, in
`TauCeti.NumberTheory.HilbertSymbol.IsAlgClosed`, already settles the complex places of a number
field and the real places alone decide such a product. For the symbol of two arbitrary elements
of the completion `K_w` itself, such as the coordinates of an idele, the same two facts are read
through the isomorphisms of `K_w` with `ℝ` and with `ℂ`.

The real-place half of the sign prescription of O'Meara 71:19 is recorded as well.  Given a
prescribed element `b` that is a nonsquare at a real place,
`exists_hilbertSymbol_eq_neg_one_atRealPlace` turns it into a local non-norm, which is what a
sign-prescription argument needs at each place of its set; a field unit negative at every real
place is such a `b`.

## Main results

* `TauCeti.hilbertSymbol_unitAtRealPlace_eq_neg_one_iff` and
  `TauCeti.hilbertSymbol_unitAtRealPlace_eq_one_iff`: the archimedean symbol of two global units
  at a real place, in both signs.
* Bimultiplicativity, by which the symbols at the real places of a prescribed set can be
  multiplied, is `TauCeti.hilbertSymbol_real_mul_left` and
  `TauCeti.hilbertSymbol_real_mul_right` read at a place; both are `[simp]`, so `simp` expands a
  product of global units inside a localized symbol.
* `TauCeti.isSquare_unitAtRealPlace_iff` and `TauCeti.not_isSquare_unitAtRealPlace_iff`: a
  global unit is a square at a real place exactly when it is positive there.
* `TauCeti.exists_hilbertSymbol_eq_neg_one_atRealPlace`: a *prescribed* negative global unit at a
  real place has a negative partner with symbol `-1` there.
* `TauCeti.hilbertSymbol_completion_eq_one_of_isComplex` and
  `TauCeti.hilbertSymbol_completion_mul_left`: over the completion `K_w` at an infinite place
  itself, the symbol is `1` at a complex place and multiplicative in its first argument at every
  infinite place. These are the archimedean factors of a product of local symbols over all places.

## A value-group convention

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, whose
multiplicative identity `1` is the value zero, that is, order of vanishing zero.  So
`v.valuation K x = 1` says that `x` is a local unit at `v`, while an element of order of vanishing
`1` is written `WithZero.exp (-1)`, the value of a generator of `v.asIdeal`; the additive order of
vanishing of an element is the negative logarithm of its value, as
`IsDedekindDomain.HeightOneSpectrum.neg_log_valuation_eq_one_iff` records.  A criterion phrased
with the hypothesis `v.valuation K (a : K) = 1` would therefore be false, and `a = 1` is the
counterexample: its image in the completion is the unit `1`, which is a square.

The finite-place nonsquare criterion that does hold is
`IsDedekindDomain.HeightOneSpectrum.not_isSquare_adicCompletion_of_valuation_eq_exp_of_not_even`:
an element of odd order of vanishing is a nonsquare in the completion, and the prime of a
prescribed modulus supplies an element of that kind.  Here `Kˣ` is the group of all nonzero
elements of `K`, not the unit group of the ring of integers, so a field unit of odd order of
vanishing at a finite place is a nonsquare in its completion by that criterion, exactly as any
other element of odd order of vanishing is.  The criterion is one way to obtain a nonsquare and
not a description of all of them; in particular it says nothing about the local units, which are
the case `v.valuation K x = 1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:18 and 71:19.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.1 and §1.2.
-/

public section
noncomputable section

local notation "𝒪" => _root_.NumberField.RingOfIntegers

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open NumberField.InfinitePlace

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The archimedean symbol at a real place is `-1` exactly when both global units are negative
there.  This is the real formula `TauCeti.hilbertSymbol_real`, read at a place of a number field
through `TauCeti.unitAtRealPlace`; it is the sign criterion by which a sign prescription multiplies
the symbols of a prescribed set over its real places. -/
@[simp]
theorem hilbertSymbol_unitAtRealPlace_eq_neg_one_iff (w : {w : InfinitePlace K // w.IsReal})
    (a b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 ↔
      embedding_of_isReal w.2 (a : K) < 0 ∧ embedding_of_isReal w.2 (b : K) < 0 := by
  rw [hilbertSymbol_real_eq_neg_one_iff, unitAtRealPlace_apply, unitAtRealPlace_apply]

omit [NumberField K] in
/-- The archimedean symbol at a real place is `1` exactly when one of the two global units is
positive there. -/
theorem hilbertSymbol_unitAtRealPlace_eq_one_iff (w : {w : InfinitePlace K // w.IsReal})
    (a b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 ↔
      0 < embedding_of_isReal w.2 (a : K) ∨ 0 < embedding_of_isReal w.2 (b : K) := by
  rw [hilbertSymbol_real_eq_one_iff, unitAtRealPlace_apply, unitAtRealPlace_apply]

omit [NumberField K] in
/-- A global unit is a square at a real place exactly when it is positive there. -/
theorem isSquare_unitAtRealPlace_iff (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    IsSquare (unitAtRealPlace w a) ↔ 0 < embedding_of_isReal w.2 (a : K) := by
  rw [Units.isSquare_iff_pos, unitAtRealPlace_apply]

omit [NumberField K] in
/-- A global unit is a nonsquare at a real place exactly when it is negative there. -/
theorem not_isSquare_unitAtRealPlace_iff (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    ¬IsSquare (unitAtRealPlace w a) ↔ embedding_of_isReal w.2 (a : K) < 0 := by
  rw [not_congr (isSquare_unitAtRealPlace_iff w a), not_lt, lt_iff_le_and_ne]
  have hne : (embedding_of_isReal w.2 (a : K)) ≠ 0 := by
    intro hz
    have h1 : (embedding_of_isReal w.2 (a : K)) = (embedding_of_isReal w.2 0) := by
      simpa only [map_zero] using hz
    exact a.ne_zero ((embedding_of_isReal w.2).injective h1)
  exact ⟨fun h => ⟨h, hne⟩, fun h => h.1⟩

omit [NumberField K] in
/-- **A prescribed negative global unit at a real place has a partner with symbol `-1`.**

Given the element `b` whose local nonsquareness a sign-prescription argument presupposes, there is
a global unit `a` whose symbol with `b` at `w` is `-1`, and `a` is negative there.  Both operands
are read at the same real place, so that the symbol can be multiplied with the symbols at the
other places of the prescribed set.  This is the step that turns a prescribed nonsquare into a
local non-norm. -/
theorem exists_hilbertSymbol_eq_neg_one_atRealPlace (w : {w : InfinitePlace K // w.IsReal})
    (b : Kˣ) (hb : embedding_of_isReal w.2 (b : K) < 0) :
    ∃ a : Kˣ, embedding_of_isReal w.2 (a : K) < 0 ∧
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 :=
  ⟨-1, by simp, by
      rw [hilbertSymbol_unitAtRealPlace_eq_neg_one_iff]
      norm_num [hb]⟩

omit [NumberField K] in
/-- The image of a global unit in the completion `K_w` at a real place `w`, read in `ℝ` through
the isomorphism `K_w ≃ ℝ`, is its image under the real embedding at `w`. -/
theorem units_map_ringEquivRealOfIsReal_algebraMap (w : {w : InfinitePlace K // w.IsReal})
    (b : Kˣ) :
    Units.map (Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →* ℝ)
      (Units.map (algebraMap K w.1.Completion).toMonoidHom b) = unitAtRealPlace w b :=
  Units.ext (by simp)

omit [NumberField K] in
/-- Over the completion at a complex place, every Hilbert symbol is `1`: the completion is
isomorphic to `ℂ`, where every element is a square. -/
theorem hilbertSymbol_completion_eq_one_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (a c : w.Completionˣ) : hilbertSymbol a c = 1 := by
  rw [← hilbertSymbol_units_map_ringEquiv (Completion.ringEquivComplexOfIsComplex hw)]
  exact hilbertSymbol_eq_one_of_isAlgClosed _ _

omit [NumberField K] in
/-- Over the completion at an infinite place, the Hilbert symbol is multiplicative in its first
argument: at a real place this is `TauCeti.hilbertSymbol_real_mul_left` read through the
isomorphism with `ℝ`, and at a complex place every symbol is `1`. -/
theorem hilbertSymbol_completion_mul_left (w : InfinitePlace K) (a a' c : w.Completionˣ) :
    hilbertSymbol (a * a') c = hilbertSymbol a c * hilbertSymbol a' c := by
  rcases w.isReal_or_isComplex with hw | hw
  · -- At a real place, transport the symbol to `ℝ`, where it is bimultiplicative.
    let e := Completion.ringEquivRealOfIsReal hw
    rw [← hilbertSymbol_units_map_ringEquiv e (a * a') c, ← hilbertSymbol_units_map_ringEquiv e a c,
      ← hilbertSymbol_units_map_ringEquiv e a' c, map_mul, hilbertSymbol_real_mul_left]
  · simp [hilbertSymbol_completion_eq_one_of_isComplex hw]

omit [NumberField K] in
/-- Over the completion at an infinite place, the symbol with first argument `1` is `1`. -/
@[simp]
theorem hilbertSymbol_completion_one_left (w : InfinitePlace K) (c : w.Completionˣ) :
    hilbertSymbol 1 c = 1 := by
  have h := hilbertSymbol_completion_mul_left w 1 1 c
  rwa [one_mul, left_eq_mul] at h

end TauCeti
