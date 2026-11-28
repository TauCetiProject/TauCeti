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
* `IsDedekindDomain.HeightOneSpectrum.valuation_complexConj`: `|conj x|_w = |x|_{conj w}`, and
  `IsDedekindDomain.HeightOneSpectrum.valuation_complexConj_of_conjPlace_eq`: conjugation preserves
  the valuation of a place fixed by conjugation.
* `IsDedekindDomain.HeightOneSpectrum.map_asIdeal_of_conjPlace_eq`: the ideal of a place fixed by
  conjugation is stable under conjugation of the integers.
* `IsDedekindDomain.HeightOneSpectrum.under_conjPlace`: `w` and `conj w` lie over the same place
  of `E⁺`.
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
  RingEquiv.valuation_equivOfRingEquiv _ w x

/-- **The conjugate place is characterised by its valuation**: `w'` is the conjugate of `w`
exactly when `|conj x|_{w'} = |x|_w` for all `x ∈ E`. -/
theorem eq_conjPlace_iff {w w' : HeightOneSpectrum (𝓞 E)} :
    w' = w.conjPlace ↔ ∀ x : E, w'.valuation E (complexConj E x) = w.valuation E x :=
  RingEquiv.eq_equivOfRingEquiv_iff _

/-- Conjugation of finite places is an involution. -/
@[simp]
theorem conjPlace_conjPlace (w : HeightOneSpectrum (𝓞 E)) : w.conjPlace.conjPlace = w :=
  (eq_conjPlace_iff.2 fun x ↦ by
    rw [← valuation_conjPlace w (complexConj E x), complexConj_apply_apply]).symm

/-- `|conj x|_w = |x|_{conj w}`: the valuation at `w` of a conjugate is the valuation at the
conjugate place. -/
theorem valuation_complexConj (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = w.conjPlace.valuation E x := by
  rw [AlgEquiv.coe_toRingEquiv, ← valuation_conjPlace w (complexConj E x),
    complexConj_apply_apply]

/-- At a place with `conj w = w`, complex conjugation preserves the `w`-adic valuation. -/
theorem valuation_complexConj_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : w.conjPlace = w) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x := by
  rw [valuation_complexConj, h]

/-- The ideal of a finite place fixed by conjugation is stable under conjugation of the
integers. -/
theorem map_asIdeal_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)} (h : w.conjPlace = w) :
    w.asIdeal.map (ringOfIntegersComplexConj E) = w.asIdeal := by
  -- `conj w` is the transport of `w` along conjugation of the integers, whose ideal is the image
  -- of that of `w`
  have hw : w.conjPlace =
      equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w :=
    (eq_conjPlace_iff.2 (RingEquiv.valuation_equivOfRingEquiv _ w)).symm
  have := asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w
  rw [← hw, h] at this
  -- `ringOfIntegersComplexConj E` and `RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv`
  -- have the same underlying map, so the two images of `w.asIdeal` agree
  exact this.symm

local notation3 "E⁺" => maximalRealSubfield E

/-- A finite place `w` of a CM field `E` and its conjugate `conj w` lie over the same finite place
of the maximal real subfield `E⁺`. -/
@[simp]
theorem under_conjPlace (w : HeightOneSpectrum (𝓞 E)) :
    under (𝓞 E⁺) w.conjPlace = under (𝓞 E⁺) w := by
  ext r
  simp only [under_asIdeal, Ideal.mem_comap]
  -- membership of an integer in a place is read off its valuation, and `conj` fixes `E⁺`
  have hfix : complexConj E (algebraMap (𝓞 E) E (algebraMap (𝓞 E⁺) (𝓞 E) r)) =
      algebraMap (𝓞 E) E (algebraMap (𝓞 E⁺) (𝓞 E) r) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 E⁺) E⁺ E,
      AlgEquiv.commutes]
  rw [← intValuation_lt_one_iff_mem, ← intValuation_lt_one_iff_mem,
    ← valuation_of_algebraMap (K := E), ← valuation_of_algebraMap (K := E),
    ← valuation_conjPlace w, hfix]

end IsDedekindDomain.HeightOneSpectrum
