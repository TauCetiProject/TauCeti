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
import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.NumberTheory.NumberField.Units.Signature.Integer
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# The archimedean Hilbert symbol, and a nonsquare at a prescribed set of places

TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 4.4, supplies three theorems in order.  This
file proves the second of them, the archimedean symbol, together with the existence input that
the third, the sign prescription of O'Meara 71:19, needs: a single element of `Kˣ` which is a
nonsquare at every place of a prescribed finite set of finite and real places.

The archimedean symbol is the norm-equation Hilbert symbol of Quadratic Form Invariants read
over the completion at an infinite place.  TauCeti already computes the symbol over `ℝ` and over
algebraically closed fields, so both halves of the Layer 4.4 formula are instances of those
computations.  What is new here is that the computation is stated for *global* units at the
places of a *number field*, so that it can be multiplied over places later, and that the
bimultiplicativity that multiplication needs is proved at a real place from the archimedean
formula.  Layer 4.4 is explicit that this is required: `hilbertSymbol_comm` and
`hilbertSymbol_mul` are not available at an archimedean place, since Quadratic Form Invariants'
Layer 6C carries `IsNonarchimedeanLocalField` on every theorem about the symbol, and citing them
here would be a type error rather than a shortcut.  At a complex place the symbol is `1` for the
same reason the archimedean classification of a form is by rank alone: every element of `ℂˣ` is a
square.

The second half of the file is the "not prescribed" form of the sign prescription.  Step 4 of
Layer 4.4 needs, at each place of the prescribed set `T`, a local non-norm, and step 1 needs a `b`
which is a nonsquare at every place of `T`, so that `K(√b)` is a quadratic extension.  O'Meara
71:19 prescribes neither, and Layer 4.4 pins the construction: an element which is a uniformizer
at each finite place of `T` and negative at each real place of `T` is a nonsquare at every place
of `T`.  Weak approximation for units supplies it in one step, because prescribing a valuation
at a finite place and a sign at a real place are both weak approximation data.  The two local
criteria which make such an element a nonsquare are the parity of the normalized valuation at a
finite place and the sign at a real place; both are proved here.

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
* `TauCeti.not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_neg_one`: a global unit of valuation
  exactly `1` at a finite place is a nonsquare in the completion at that place.
* `TauCeti.valuation_eq_exp_neg_one_iff_adicOrd`: the same "valuation exactly `1`" condition in
  the additive `adicOrd` form.
* `TauCeti.exists_hilbertSymbol_eq_neg_one_atRealPlace`: two negative global units at a real place
  have symbol `-1` there, the archimedean half of step 4 of Layer 4.4.
* `TauCeti.exists_fieldUnit_negative_at`: a global unit which is negative at every real place of a
  prescribed finite set, the real-place half of the sign prescription of O'Meara 71:19.
* `TauCeti.isSquare_unitAtFinitePlace_one`: the counterexample that fixes the value-group
  convention recorded below.

## A convention worth recording

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, and its `1`
is the *top* of that group, that is, value zero.  So `v.valuation K x = 1` says that `x` is a local
unit at `v`, which every global unit satisfies; an element of valuation exactly `1` is written
`WithZero.exp (-1)`, the value of a generator of `v.asIdeal`.  The two finite-place statements
above are therefore in `WithZero.exp (-1)` form, and
`not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_one` is the statement with that
hypothesis replaced by `1`, which is refuted by `x = 1`.  This is the same reason a field unit
cannot be made into the `b` of O'Meara 71:19 at a *finite* place of a prescribed set: it is a unit
at every place, so its local value at each of them is the top `1`, never `WithZero.exp (-1)`.
Choosing such a `b` at the finite places of `T` needs an element of `K` rather than of `Kˣ`, and
that is the next Layer 4.4 step.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:18 and 71:19.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.1 and §1.2.
-/

-- Provenance: TauCetiRoadmap/GlobalQuadraticForms/README.md, Layer 4.4.

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
theorem hilbertSymbol_unitAtComplexEmbedding_eq_one (w : InfinitePlace K) (a b : Kˣ) :
    hilbertSymbol (Units.map w.embedding.toMonoidHom a) (Units.map w.embedding.toMonoidHom b) = 1 :=
  hilbertSymbol_eq_one_of_isAlgClosed _ _

/-- **A global unit of valuation exactly `1` at a finite place is a nonsquare in the completion
at that place.**

The value group of `HeightOneSpectrum.valuation` is `WithZero (Multiplicative ℤ)`, normalized so
that its `1` is the *top* of the group, i.e. value zero.  An element of valuation exactly `1` is
therefore written `WithZero.exp (-1)`, and `WithZero.exp (-1 : ℤ)` is the value of a generator of
`v.asIdeal`, not the value of a local unit.  The normalized valuation of the completion is minus the
logarithm of the adic valuation, so the image of such an element has normalized valuation
`ofAdd 1`, which is odd; a square has even normalized valuation.

The hypothesis is deliberately *not* `v.valuation K (a : K) = 1`.  That equation says that `a` is a
local unit at `v`, and every global unit satisfies it, including `1`, whose image in the completion
is a square. -/
theorem not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_neg_one
    (v : HeightOneSpectrum (𝒪 K)) (a : Kˣ)
    (ha : v.valuation K (a : K) = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ))) :
    ¬IsSquare (v.unitAtFinitePlace a) := by
  intro hsq
  have hev : Even (normalizedValuation (v.adicCompletion K) (v.unitAtFinitePlace a)).toAdd :=
    normalizedValuation_even_of_isSquare hsq
  have hz : normalizedValuationWithZero (v.adicCompletion K) (v.unitAtFinitePlace a)
      = ((Multiplicative.ofAdd 1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [unitAtFinitePlace_apply]
    rw [normalizedValuationWithZero_adicCompletion, algebraMap_adicCompletion,
      Function.comp_apply]
    change (Valued.v ((a : K) : v.adicCompletion K))⁻¹ = _
    rw [(valuedAdicCompletion_eq_valuation' (K := K) (v := v) (a : K)).trans ha,
      WithZero.inv_exp, neg_neg, WithZero.exp_eq_coe_ofAdd]
  have hval : normalizedValuation (v.adicCompletion K) (v.unitAtFinitePlace a)
      = (Multiplicative.ofAdd 1 : Multiplicative ℤ) := by
    exact WithZero.coe_injective (by simpa only [normalizedValuationWithZero_coe] using hz)
  rw [hval, toAdd_ofAdd] at hev
  exact Int.not_even_one hev

/-- **"Valuation exactly `1` at `v`" in the `adicOrd` form.**  Reading off the logarithm of the
value is the shape `TauCeti.adicOrd` uses, so this identifies the hypothesis of
`not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_neg_one` with the additive order of vanishing
that the class-group interface records. -/
theorem valuation_eq_exp_neg_one_iff_adicOrd (v : HeightOneSpectrum (𝒪 K)) (x : K) :
    -WithZero.log (v.valuation K x) = 1 ↔
      v.valuation K x = (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h
    have hlog : WithZero.log (v.valuation K x) = -1 := (neg_eq_iff_eq_neg).mp h
    have hx : v.valuation K x ≠ 0 := by
      intro hx0
      rw [hx0] at hlog
      simp at hlog
    calc v.valuation K x = WithZero.exp (WithZero.log (v.valuation K x)) :=
        (WithZero.exp_log hx).symm
      _ = WithZero.exp (-1) := by rw [hlog]
  · intro h
    rw [h, WithZero.log_exp, neg_neg]

omit [NumberField K] in
/-- **A negative global unit at a real place has a partner with symbol `-1`.**  This is the
archimedean half of step 4 of Layer 4.4, in the form it needs: the symbol is produced from two
global units read through the real place, so that it can be multiplied with the symbols at the
other places of the prescribed set. -/
theorem exists_hilbertSymbol_eq_neg_one_atRealPlace (w : {w : InfinitePlace K // w.IsReal}) :
    ∃ a b : Kˣ, embedding_of_isReal w.2 (a : K) < 0 ∧
      embedding_of_isReal w.2 (b : K) < 0 ∧
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = -1 :=
  ⟨-1, -1, by simp, by simp, by
      rw [hilbertSymbol_unitAtRealPlace_eq_neg_one_iff]
      norm_num⟩

/-- **A global unit which is negative at every real place of a prescribed finite set.**

This is the real-place half of the sign prescription of O'Meara 71:19, which Layer 4.4 pins: the
element is prescribed to be negative at each real place of the set `T`, and weak approximation for
field units supplies it in one step, since prescribing a sign at each real place of a finite set is
weak approximation data.  Together with
`not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_neg_one` this is the local non-norm input that
step 4 of Layer 4.4 consumes. -/
theorem exists_fieldUnit_negative_at (T : Finset {w : InfinitePlace K // w.IsReal}) :
    ∃ x : Kˣ, ∀ w ∈ T, embedding_of_isReal w.2 (x : K) < 0 := by
  classical
  obtain ⟨x, -, hxs⟩ :=
    TauCeti.GlobalNumberFields.exists_fieldUnit_valuation_eq_and_signHom_eq (S := ∅)
      (fun _ => 0) (fun w => if w ∈ T then -1 else 1)
  refine ⟨x, fun w hw => ?_⟩
  have hs : TauCeti.GlobalNumberFields.signHom x w = -1 := by
    have h := congrFun hxs w
    simpa [hw] using h
  rwa [TauCeti.GlobalNumberFields.signHom_apply_eq_neg_one_iff] at hs

/-- **The `v.valuation K (a : K) = 1` form of the finite-place criterion is false, and `1` is the
counterexample.**  The neutral element of the value group `WithZero (Multiplicative ℤ)` is its
top, that is, value zero, so `v.valuation K (a : K) = 1` is the statement that `a` is a local unit
at `v`; every global unit satisfies it.  The image of `1` in the completion is a square, so the
criterion with that hypothesis is refuted.  This is why
`not_isSquare_unitAtFinitePlace_of_valuation_eq_exp_neg_one` is stated with
`WithZero.exp (-1)`. -/
theorem isSquare_unitAtFinitePlace_one (v : HeightOneSpectrum (𝒪 K)) :
    IsSquare (v.unitAtFinitePlace (1 : Kˣ)) := by
  refine ⟨1, ?_⟩
  simp

end TauCeti
