/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Transporting localized units and Hilbert symbols along an isomorphism of fields

A ring isomorphism `e : K ≃+* L` of number fields identifies the finite places of `K` with those of
`L` by `HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)` and the real places of
`K` with those of `L` by `NumberField.InfinitePlace.realEquivOfRingEquiv e`. At each pair of
corresponding finite places `v` and `w`, `adicCompletionCongr` extends `e` to a ring isomorphism
`K_v ≃+* L_w` that intertwines `unitAtFinitePlace`, preserves local squares, and preserves the
norm-equation Hilbert symbol. At each real place `w`, `realEquivOfRingEquiv e` intertwines
`unitAtRealPlace` on the nose in `ℝˣ`.

Reindexing along the two place bijections shows that the product of the finite-place Hilbert
symbols `(a_v, b_v)_v` and the product of the real-place Hilbert symbols `(a_w, b_w)_w` are both
invariant under `e`. In particular, global statements expressed through local squareness and
localized Hilbert symbols transfer along `Shrink.ringEquiv K : Shrink.{0} K ≃+* K` from `Type` to
number fields in any universe.

## Main results

* `TauCeti.units_map_adicCompletionCongr_unitAtFinitePlace`: `adicCompletionCongr` intertwines
  `unitAtFinitePlace` with `Units.map e`.
* `TauCeti.isSquare_unitAtFinitePlace_iff_of_ringEquiv`,
  `TauCeti.isSquare_unitAtFinitePlace_equivOfRingEquiv`: local squareness at a finite place is
  preserved along `e`.
* `TauCeti.hilbertSymbol_unitAtFinitePlace_of_ringEquiv`,
  `TauCeti.hilbertSymbol_unitAtFinitePlace_equivOfRingEquiv`: the localized Hilbert symbol at a
  finite place is preserved along `e`.
* `TauCeti.finprod_hilbertSymbol_unitAtFinitePlace_ringEquiv`: the product of the finite-place
  Hilbert symbols is preserved along `e`.
* `TauCeti.unitAtRealPlace_realEquivOfRingEquiv`,
  `TauCeti.unitAtRealPlace_realEquivOfRingEquiv_units_map`: `unitAtRealPlace` at a transported real
  place pulls back along `e.symm`, and is unchanged when both place and unit are transported along
  `e`.
* `TauCeti.prod_hilbertSymbol_unitAtRealPlace_ringEquiv`: the product of the real-place Hilbert
  symbols is preserved along `e`.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace

namespace TauCeti

section FinitePlace

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- Extending a valuation-preserving isomorphism `e : K ≃+* L` to the adic completions intertwines
`unitAtFinitePlace` with `Units.map e`. -/
@[simp]
theorem units_map_adicCompletionCongr_unitAtFinitePlace
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)} {e : K ≃+* L}
    (he : ∀ x, w.valuation L (e x) = v.valuation K x) (a : Kˣ) :
    Units.map (adicCompletionCongr v w e he : v.adicCompletion K →* w.adicCompletion L)
        (v.unitAtFinitePlace a) =
      w.unitAtFinitePlace (Units.map (e : K →* L) a) := by
  ext
  simp

/-- Local squareness at a finite place is preserved under a ring isomorphism `e : K ≃+* L` of
number fields carrying `v` to `w`. -/
theorem isSquare_unitAtFinitePlace_iff_of_ringEquiv (e : K ≃+* L)
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal) (a : Kˣ) :
    IsSquare (w.unitAtFinitePlace (Units.map (e : K →* L) a)) ↔
      IsSquare (v.unitAtFinitePlace a) := by
  have he (x : K) : w.valuation L (e x) = v.valuation K x := by
    simpa using valuation_ringEquivOfRingEquiv (K := K) (K' := L)
      (RingOfIntegers.mapRingEquiv e) hvw x
  let f := Units.mapEquiv (adicCompletionCongr v w e he).toMulEquiv
  have hf : f (v.unitAtFinitePlace a) = w.unitAtFinitePlace (Units.map (e : K →* L) a) :=
    units_map_adicCompletionCongr_unitAtFinitePlace he a
  rw [← hf]
  exact ⟨fun h ↦ by simpa using h.map f.symm, fun h ↦ h.map f⟩

/-- Local squareness at a finite place is preserved when both the place and the unit are
transported along `e : K ≃+* L`. -/
@[simp]
theorem isSquare_unitAtFinitePlace_equivOfRingEquiv (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    IsSquare
        ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v).unitAtFinitePlace
          (Units.map (e : K →* L) a)) ↔
      IsSquare (v.unitAtFinitePlace a) :=
  isSquare_unitAtFinitePlace_iff_of_ringEquiv e
    (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) a

/-- The localized Hilbert symbol at a finite place is preserved under a ring isomorphism
`e : K ≃+* L` of number fields carrying `v` to `w`. -/
theorem hilbertSymbol_unitAtFinitePlace_of_ringEquiv (e : K ≃+* L)
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal) (a b : Kˣ) :
    hilbertSymbol (w.unitAtFinitePlace (Units.map (e : K →* L) a))
        (w.unitAtFinitePlace (Units.map (e : K →* L) b)) =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  have he (x : K) : w.valuation L (e x) = v.valuation K x := by
    simpa using valuation_ringEquivOfRingEquiv (K := K) (K' := L)
      (RingOfIntegers.mapRingEquiv e) hvw x
  rw [← units_map_adicCompletionCongr_unitAtFinitePlace he a,
    ← units_map_adicCompletionCongr_unitAtFinitePlace he b,
    hilbertSymbol_units_map_ringEquiv (adicCompletionCongr v w e he)]

/-- The localized Hilbert symbol at a finite place is preserved when both the place and the units
are transported along `e : K ≃+* L`. -/
@[simp]
theorem hilbertSymbol_unitAtFinitePlace_equivOfRingEquiv (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    hilbertSymbol
        ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v).unitAtFinitePlace
          (Units.map (e : K →* L) a))
        ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v).unitAtFinitePlace
          (Units.map (e : K →* L) b)) =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) :=
  hilbertSymbol_unitAtFinitePlace_of_ringEquiv e
    (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) a b

/-- The product of the localized Hilbert symbols over all finite places is preserved under a ring
isomorphism `e : K ≃+* L` of number fields. -/
theorem finprod_hilbertSymbol_unitAtFinitePlace_ringEquiv (e : K ≃+* L) (a b : Kˣ) :
    (∏ᶠ w : HeightOneSpectrum (𝓞 L),
        hilbertSymbol (w.unitAtFinitePlace (Units.map (e : K →* L) a))
          (w.unitAtFinitePlace (Units.map (e : K →* L) b))) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  rw [← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e))]
  exact finprod_congr fun v ↦ hilbertSymbol_unitAtFinitePlace_equivOfRingEquiv e v a b

end FinitePlace

section RealPlace

variable {K L : Type*} [Field K] [Field L]

/-- Evaluating `unitAtRealPlace` at a real place transported along `e : K ≃+* L` pulls the unit
back along `e.symm`. -/
@[simp]
theorem unitAtRealPlace_realEquivOfRingEquiv (e : K ≃+* L)
    (w : {w : InfinitePlace K // w.IsReal}) (b : Lˣ) :
    unitAtRealPlace (InfinitePlace.realEquivOfRingEquiv e w) b =
      unitAtRealPlace w (Units.map (e.symm : L →* K) b) := by
  ext
  simp

-- Not `@[simp]`: `unitAtRealPlace_realEquivOfRingEquiv` already simplifies the left-hand side.
/-- Transporting both a real place and a global unit along `e : K ≃+* L` leaves `unitAtRealPlace`
unchanged. -/
theorem unitAtRealPlace_realEquivOfRingEquiv_units_map (e : K ≃+* L)
    (w : {w : InfinitePlace K // w.IsReal}) (a : Kˣ) :
    unitAtRealPlace (InfinitePlace.realEquivOfRingEquiv e w) (Units.map (e : K →* L) a) =
      unitAtRealPlace w a := by
  ext
  simp

/-- The product of the localized Hilbert symbols over all real places is preserved under a ring
isomorphism `e : K ≃+* L`. -/
theorem prod_hilbertSymbol_unitAtRealPlace_ringEquiv
    [Fintype {w : InfinitePlace K // w.IsReal}] [Fintype {w : InfinitePlace L // w.IsReal}]
    (e : K ≃+* L) (a b : Kˣ) :
    (∏ w : {w : InfinitePlace L // w.IsReal},
        hilbertSymbol (unitAtRealPlace w (Units.map (e : K →* L) a))
          (unitAtRealPlace w (Units.map (e : K →* L) b))) =
      ∏ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) := by
  rw [← Equiv.prod_comp (InfinitePlace.realEquivOfRingEquiv e)]
  exact Finset.prod_congr rfl fun w _ ↦ by
    rw [unitAtRealPlace_realEquivOfRingEquiv_units_map,
      unitAtRealPlace_realEquivOfRingEquiv_units_map]

end RealPlace

end TauCeti
