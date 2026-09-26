/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Archimedean
public import TauCeti.NumberTheory.HilbertSymbol.IsAlgClosed
public import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak

/-!
# The archimedean Hilbert symbol

The archimedean symbol is the norm-equation Hilbert symbol read over the completion at an infinite
place.  Tau Ceti already computes the symbol over `ℝ` and over algebraically closed fields, so
both halves of the archimedean formula are instances of those computations.  What is new here is
that the computation is stated for *global* units at the *places of a number field*, so that it can
be multiplied over places, and that the bimultiplicativity that multiplication needs is proved at
a real place from the archimedean formula itself.

Bimultiplicativity is read off that formula rather than cited from `hilbertSymbol_comm` and
`hilbertSymbol_mul`, because those carry an `IsNonarchimedeanLocalField` hypothesis on every
theorem about the symbol: they are not available at an archimedean place, and citing them here
would be a type error rather than a shortcut.  At a complex place the symbol is `1` for the same
reason the archimedean classification of a form is by rank alone: every element of `ℂˣ` is a
square.

The file also records the real-place half of the sign prescription of O'Meara 71:19.  Given a
prescribed element `b` that is a nonsquare at a real place,
`exists_hilbertSymbol_eq_neg_one_atRealPlace` turns it into a local non-norm, which is what a
sign-prescription argument needs at each place of its set;
`TauCeti.GlobalNumberFields.exists_fieldUnit_negative_at` supplies the `b` itself.

## Main results

* `TauCeti.hilbertSymbol_unitAtRealPlace_eq_neg_one_iff` and
  `TauCeti.hilbertSymbol_unitAtRealPlace_eq_one_iff`: the archimedean symbol of two global units
  at a real place, in both signs.
* `TauCeti.hilbertSymbol_unitAtRealPlace_mul_left` and
  `TauCeti.hilbertSymbol_unitAtRealPlace_mul_right`: bimultiplicativity of the localized real
  symbol, read off that formula.
* `TauCeti.hilbertSymbol_unitAtComplexEmbedding_eq_one`: the symbol of two global units read
  through the complex embedding of an infinite place is `1`.
* `TauCeti.isSquare_unitAtRealPlace_iff` and `TauCeti.not_isSquare_unitAtRealPlace_iff`: a
  global unit is a square at a real place exactly when it is positive there.
* `TauCeti.exists_hilbertSymbol_eq_neg_one_atRealPlace`: a *prescribed* negative global unit at a
  real place has a negative partner with symbol `-1` there.

## A value-group convention

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, and its `1`
is the *top* of that group, that is, value zero.  So `v.valuation K x = 1` says that `x` is a local
unit at `v`, which every global unit satisfies; an element of order of vanishing `1` is instead
written `WithZero.exp (-1)`, the value of a generator of `v.asIdeal`.  A criterion phrased with the
hypothesis `v.valuation K (a : K) = 1` would therefore be false, and `a = 1` is the counterexample:
its image in the completion is the unit `1`, which is a square.  This is also why a field unit
cannot serve as a nonsquare at a *finite* place of a prescribed set: it is a unit at every place,
so its value at each of them is the top `1`, never `WithZero.exp (-1)`.  The finite-place
nonsquare criterion that does hold is stated in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`; see
`IsDedekindDomain.HeightOneSpectrum.neg_log_valuation_eq_one_iff` for the equivalence between an
order of vanishing `1` and the value `WithZero.exp (-1)`.

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
there.  The archimedean formula is `TauCeti.hilbertSymbol_real`, read through
`TauCeti.unitAtRealPlace`.  Layer 4.4 asks for this statement in global notation, because
`hilbertSymbol_mul` is not available at a real place and the sign prescription has to multiply
these symbols over the archimedean places by hand. -/
@[simp]
theorem hilbertSymbol_unitAtRealPlace_eq_neg_one_iff (w : {w : InfinitePlace K // w.IsReal})
    (a b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 ↔
      embedding_of_isReal w.2 (a : K) < 0 ∧ embedding_of_isReal w.2 (b : K) < 0 := by
  rw [hilbertSymbol_real_eq_neg_one_iff, unitAtRealPlace_apply, unitAtRealPlace_apply]

omit [NumberField K] in
/-- The archimedean symbol at a real place is `1` exactly when one of the two global units is
positive there. -/
@[simp]
theorem hilbertSymbol_unitAtRealPlace_eq_one_iff (w : {w : InfinitePlace K // w.IsReal})
    (a b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 ↔
      0 < embedding_of_isReal w.2 (a : K) ∨ 0 < embedding_of_isReal w.2 (b : K) := by
  rw [hilbertSymbol_real_eq_one_iff, unitAtRealPlace_apply, unitAtRealPlace_apply]

omit [NumberField K] in
/-- **Bimultiplicativity of the localized real symbol, in the first parameter.** This is
`TauCeti.hilbertSymbol_real_mul_left` read at a real place of a number field.

Layer 4.4 pins this to the archimedean formula.  The instance `TauCeti.hilbertSymbol_mul` is
stated over a nonarchimedean local field, and this symbol is taken at a real place, so it cannot
be used here. -/
theorem hilbertSymbol_unitAtRealPlace_mul_left (w : {w : InfinitePlace K // w.IsReal})
    (a a' b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w (a * a')) (unitAtRealPlace w b) =
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) *
        hilbertSymbol (unitAtRealPlace w a') (unitAtRealPlace w b) := by
  rw [(unitAtRealPlace w).map_mul a a', hilbertSymbol_real_mul_left]

omit [NumberField K] in
/-- **Bimultiplicativity of the localized real symbol, in the second parameter.** This is
`TauCeti.hilbertSymbol_real_mul_right` read at a real place of a number field. -/
theorem hilbertSymbol_unitAtRealPlace_mul_right (w : {w : InfinitePlace K // w.IsReal})
    (a b b' : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (b * b')) =
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) *
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b') := by
  rw [(unitAtRealPlace w).map_mul b b', hilbertSymbol_real_mul_right]

omit [NumberField K] in
/-- A global unit is a square at a real place exactly when it is positive there. -/
@[simp]
theorem isSquare_unitAtRealPlace_iff (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    IsSquare (unitAtRealPlace w a) ↔ 0 < embedding_of_isReal w.2 (a : K) := by
  have key : IsSquare (unitAtRealPlace w a) ↔ 0 < (unitAtRealPlace w a : ℝ) := by
    constructor
    · rintro ⟨u, hu⟩
      have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast fun h => u.ne_zero h
      have hpos : 0 < (u : ℝ) * (u : ℝ) := mul_self_pos.2 hu0
      have hval : (unitAtRealPlace w a : ℝ) = (u : ℝ) * (u : ℝ) :=
        congrArg (fun z : ℝˣ => (z : ℝ)) hu
      exact hval ▸ hpos
    · intro h
      have hne : Real.sqrt (unitAtRealPlace w a : ℝ) ≠ 0 := Real.sqrt_pos.2 h |>.ne'
      refine ⟨Units.mk0 _ hne, ?_⟩
      refine Units.ext ?_
      change (unitAtRealPlace w a : ℝ) = ((Units.mk0 _ hne) : ℝˣ) * ((Units.mk0 _ hne) : ℝˣ)
      change (unitAtRealPlace w a : ℝ) = Real.sqrt _ * Real.sqrt _
      exact (Real.mul_self_sqrt h.le).symm
  rw [key, unitAtRealPlace_apply]

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
/-- **The symbol is trivial at a complex place.** For any infinite place `w` of `K` and global
units `a, b`, the symbol of their images through the complex embedding of `w` is `1`.

Layer 4.4 states the archimedean symbol as a formula which is `1` at every complex place.  Every
element of `ℂˣ` is a square, so the symbol is trivial there.  This holds at the complex embedding
of a real place as well, which is why the statement is made for every infinite place rather than
only for the non-real ones. -/
@[simp]
theorem hilbertSymbol_unitAtComplexEmbedding_eq_one (w : InfinitePlace K) (a b : Kˣ) :
    hilbertSymbol (Units.map w.embedding.toMonoidHom a) (Units.map w.embedding.toMonoidHom b) = 1 :=
  hilbertSymbol_eq_one_of_isAlgClosed _ _

omit [NumberField K] in
/-- **A prescribed negative global unit at a real place has a partner with symbol `-1`.**

Given the element `b` whose local nonsquareness a sign-prescription argument presupposes, there is
a global unit `a` whose symbol with `b` at `w` is `-1`, and `a` is negative there.  Both operands
are read through the real place, so that the symbol can be multiplied with the symbols at the
other places of the prescribed set.  This is the step that turns a prescribed nonsquare into a local
non-norm.

`a = -1` works because a real place is local, so `(-1, b) = -1` there exactly when `b` is
negative. -/
theorem exists_hilbertSymbol_eq_neg_one_atRealPlace (w : {w : InfinitePlace K // w.IsReal})
    (b : Kˣ) (hb : embedding_of_isReal w.2 (b : K) < 0) :
    ∃ a : Kˣ, embedding_of_isReal w.2 (a : K) < 0 ∧
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 :=
  ⟨-1, by simp, by
      rw [hilbertSymbol_unitAtRealPlace_eq_neg_one_iff]
      norm_num [hb]⟩

end TauCeti
