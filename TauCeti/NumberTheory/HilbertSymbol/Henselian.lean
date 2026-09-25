/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.RingTheory.Henselian.BinaryForm

/-!
# The Hilbert symbol of two units of a Henselian local ring

Let `R` be a Henselian local ring with finite residue field in which `2` is a unit, and let `K` be
a field with an `R`-algebra structure. The Hilbert symbol over `K` of the images of two units of
`R` is `1`: the norm equation `x² - u y² = u'` is already solvable in `R` by Hensel's lemma.

For the ring of integers of a nonarchimedean local field of odd residue characteristic, this is
the statement that the Hilbert symbol is trivial on pairs of units. It is the good-place
computation that makes the Hilbert symbols of two elements of a number field trivial at almost
every finite place.

## Main results

* `TauCeti.hilbertSymbol_units_map_eq_one`: `(u, u')_K = 1` for units `u` and `u'` of `R`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1, the value of the Hilbert
  symbol on two units at an odd prime.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 63:11.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
variable {K : Type*} [Field K] [Algebra R K]

/-- **The Hilbert symbol of two units.** If `R` is a Henselian local ring with finite residue
field in which `2` is a unit, then the Hilbert symbol over an `R`-algebra `K` of the images of two
units of `R` is `1`. -/
@[simp]
theorem hilbertSymbol_units_map_eq_one (h2 : IsUnit (2 : R)) (u u' : Rˣ) :
    hilbertSymbol (Units.map (algebraMap R K : R →* K) u)
      (Units.map (algebraMap R K : R →* K) u') = 1 := by
  obtain ⟨x, y, hxy⟩ :=
    exists_mul_sq_add_mul_sq_eq_of_isUnit h2 isUnit_one (-u).isUnit u'.isUnit
  refine (hilbertSymbol_eq_one_iff _ _).mpr ⟨algebraMap R K x, algebraMap R K y, ?_⟩
  have := congrArg (algebraMap R K) hxy
  simp only [map_add, map_mul, map_pow, map_one, map_neg, Units.val_neg] at this
  simp only [Units.coe_map, MonoidHom.coe_coe]
  linear_combination -this

end TauCeti
