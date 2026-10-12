/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology

/-!
# Hilbert 90 for ideles

For a finite Galois extension `L/K` of number fields, the first cohomology of the idele
module `I_L` vanishes. This supplies the zero term preceding `H¹(Gal(L/K), C_L)` in the
long exact sequence of `Lˣ → I_L → C_L`: the connecting map into `H²(Gal(L/K), Lˣ)` is
injective, so vanishing of `H¹(Gal(L/K), C_L)` is equivalent to injectivity of the map
from relative Brauer classes to idelic cohomology.

At each finite or infinite place the semi-local unit module is coinduced from the units
of a completion. Shapiro's lemma and Mathlib's field Hilbert 90 kill its first cohomology.
The placewise detection theorem for ideles then gives the global vanishing. No cyclicity
hypothesis or global reciprocity law is needed.

## Main results

* `isZero_tateCohomology_one_idelesRep`: Hilbert 90 for ideles, on the Tate carrier.
* `subsingleton_groupCohomology_one_idelesRep`: Hilbert 90 on ordinary cohomology, as an instance.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 2.5 and Corollary 2.6.
* J. Tate, *Global class field theory*, in Cassels–Fröhlich, *Algebraic Number Theory*,
  Chapter VII, §§6–7.

The proof reuses Mathlib's `groupCohomology.H1ofAutOnUnitsUnique` and the semi-local
coinduction and placewise detection constructions of Tau Ceti.
-/

public noncomputable section

open CategoryTheory Limits NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

namespace TauCeti.ClassFieldTheory

/-- **Hilbert 90 for ideles.** The first Tate cohomology of the idele module of a finite Galois
extension of number fields vanishes. -/
theorem isZero_tateCohomology_one_idelesRep : IsZero (tateCohomology (idelesRep K L) 1) := by
  have h (x : tateCohomology (idelesRep K L) 1) : x = 0 := by
    apply eq_zero_of_forall_map_semilocal_eq_zero L 1
    · intro v
      exact (ModuleCat.subsingleton_of_isZero
        (v.isZero_tateCohomology_one_semilocalUnitsRep (L := L))).elim _ _
    · intro v
      exact (ModuleCat.subsingleton_of_isZero
        (v.isZero_tateCohomology_one_infiniteSemilocalUnitsRep (L := L))).elim _ _
  have : Subsingleton (tateCohomology (idelesRep K L) 1) :=
    ⟨fun x y => (h x).trans (h y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **Hilbert 90 for ideles**, on ordinary group cohomology: `H¹(Gal(L/K), I_L) = 0`. -/
instance subsingleton_groupCohomology_one_idelesRep :
    Subsingleton (groupCohomology (idelesRep K L) 1) :=
  ModuleCat.subsingleton_of_isZero <| isZero_tateCohomology_one_idelesRep.of_iso
    ((_root_.TateCohomology.isoGroupCohomology 1).app (idelesRep K L)).symm

end TauCeti.ClassFieldTheory
