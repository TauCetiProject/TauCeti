/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import TauCeti.NumberTheory.NumberField.FinitePlace.Transport

/-!
# The conjugate of a finite place of a CM field

Complex conjugation `x ↦ conj x` of a CM field `E` permutes its finite places: the conjugate
`conj w` of a finite place `w` (`IsDedekindDomain.HeightOneSpectrum.conjPlace`) is its image under
the isomorphism of rings of integers induced by `complexConj E`, and is the unique finite place
with `|conj x|_{conj w} = |x|_w` for `x ∈ E`. Conjugation of finite places is an involution. The
places `w` with `conj w ≠ w` lie above the places of the maximal real subfield `E⁺` that split in
`E`; at them, conjugation of the adeles of `E` exchanges the completions at `w` and at `conj w`.

## Main declarations

* `IsDedekindDomain.HeightOneSpectrum.conjPlace`: the conjugate of a finite place.
* `IsDedekindDomain.HeightOneSpectrum.valuation_conjPlace`: `|conj x|_{conj w} = |x|_w`.
* `IsDedekindDomain.HeightOneSpectrum.eq_conjPlace_iff`: the conjugate place is the only finite
  place with this property.
* `IsDedekindDomain.HeightOneSpectrum.conjPlace_conjPlace`: conjugation of finite places is an
  involution.
-/

public section

open NumberField NumberField.IsCMField

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The **conjugate** `conj w` of a finite place `w` of a CM field: its image under complex
conjugation, the unique finite place with `|conj x|_{conj w} = |x|_w` for `x ∈ E`
(`valuation_conjPlace`, `eq_conjPlace_iff`). -/
noncomputable def conjPlace (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w

/-- The conjugate place carries the valuation of `w` along conjugation:
`|conj x|_{conj w} = |x|_w`. -/
@[simp]
theorem valuation_conjPlace (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.conjPlace.valuation E (complexConj E x) = w.valuation E x :=
  valuation_equivOfRingEquiv_mapRingEquiv _ w x

/-- **The conjugate place is characterised by its valuation**: `w'` is the conjugate of `w`
exactly when `|conj x|_{w'} = |x|_w` for all `x ∈ E`. -/
theorem eq_conjPlace_iff {w w' : HeightOneSpectrum (𝓞 E)} :
    w' = w.conjPlace ↔ ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x :=
  eq_equivOfRingEquiv_mapRingEquiv_iff _

/-- Conjugation of finite places is an involution. -/
@[simp]
theorem conjPlace_conjPlace (w : HeightOneSpectrum (𝓞 E)) : w.conjPlace.conjPlace = w :=
  (eq_conjPlace_iff.2 fun x ↦ by
    rw [← valuation_conjPlace w (complexConj E x), complexConj_apply_apply]).symm

end IsDedekindDomain.HeightOneSpectrum
