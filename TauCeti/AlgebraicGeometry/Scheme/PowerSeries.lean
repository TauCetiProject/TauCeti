/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.Spectrum.Prime.PowerSeries

/-!
# The spectrum of a power series ring

The constant coefficient homomorphism `R⟦X⟧ → R`, that is `X ↦ 0`, embeds `Spec R` into
`Spec R⟦X⟧` as the closed subscheme `X = 0`. Every open subscheme of `Spec R⟦X⟧` containing it is
all of `Spec R⟦X⟧`, since `X` lies in the Jacobson radical of the `X`-adically complete ring
`R⟦X⟧`.

## Main results

* `PowerSeries.range_SpecMap_constantCoeff_subset_iff_eq_top`: an open subscheme of `Spec R⟦X⟧`
  contains the image of `Spec R` under `Spec` of `X ↦ 0` exactly when it is the whole scheme.
-/

public section

open AlgebraicGeometry PowerSeries

universe u

/-- An open subscheme of `Spec R⟦X⟧` contains the image of `Spec R` under `Spec` of the constant
coefficient `R⟦X⟧ → R`, the locus `X = 0`, exactly when it is the whole scheme. -/
theorem PowerSeries.range_SpecMap_constantCoeff_subset_iff_eq_top {R : Type u} [CommRing R]
    {U : (Spec (.of R⟦X⟧)).Opens} :
    Set.range (Spec.map (CommRingCat.ofHom (constantCoeff (R := R)))) ⊆ U ↔ U = ⊤ :=
  -- the points of `Spec` of a ring are those of its prime spectrum (`Spec_carrier`), on which
  -- `Spec.map` is `PrimeSpectrum.comap` (`Spec.map_apply`), both by definition, so this is
  -- `PowerSeries.range_comap_constantCoeff_subset_iff_eq_top` for the open subset `U`; no lemma
  -- carries an open subset across this identification, and Mathlib crosses it by a term in the
  -- same way, in `Scheme.preimage_eq_top_of_closedPoint_mem`
  range_comap_constantCoeff_subset_iff_eq_top
