/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
public import Mathlib.FieldTheory.SeparableClosure
-- Non-public: the finite Galois splitting field and the class of the cocycle of a splitting are
-- used only in the proof of surjectivity.
import TauCeti.Algebra.CentralSimple.FiniteGalois
import TauCeti.Algebra.CrossedProduct.Splitting.Class

/-!
# Every Brauer class is a crossed-product class

A `TauCeti.GaloisCocycle K` bundles a finite Galois subextension `L` of the separable closure
`Kˢ/K` with a `2`-cocycle of `Gal(L/K)` with values in `Lˣ`. Bundling the extension together with
its instances lets a statement quantify over "some finite Galois splitting field and some cocycle
of its Galois group" without quantifying over instances.

Every Brauer class of `K` is the class of the crossed product of such a bundled cocycle: a
finite-dimensional central simple `K`-algebra `A` is split by a finite Galois subextension of
`Kˢ/K` (`TauCeti.Algebra.exists_finiteGalois_splittingField`), and the crossed product of the
cocycle attached to a splitting has the class of `A`
(`TauCeti.BrauerGroup.crossedProductClass_cocycleOfSplitting`).

## Main definitions

* `TauCeti.GaloisCocycle K`: a finite Galois subextension of `Kˢ/K` with a `2`-cocycle of its
  Galois group.
* `TauCeti.GaloisCocycle.brauerClass`: the Brauer class of its crossed product.

## Main results

* `TauCeti.BrauerGroup.exists_galoisCocycle_brauerClass_eq`: every Brauer class of `K` is the
  class of a bundled Galois cocycle.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

universe u

namespace TauCeti

variable (K : Type u) [Field K]

/-- A **Galois cocycle** of `K`: a finite Galois subextension `L` of the separable closure
`Kˢ/K`, together with a `2`-cocycle of `Gal(L/K)` with values in `Lˣ`. The extension is taken
inside `Kˢ` so that it determines an open subgroup of the absolute Galois group. -/
structure GaloisCocycle where
  /-- The finite Galois subextension `L` of `Kˢ/K`. -/
  extension : IntermediateField K (SeparableClosure K)
  [finiteDimensional : FiniteDimensional K extension]
  [isGalois : IsGalois K extension]
  /-- The `2`-cocycle of `Gal(L/K)`. -/
  cocycle : TwoCocycle K extension

attribute [instance] GaloisCocycle.finiteDimensional GaloisCocycle.isGalois

namespace GaloisCocycle

variable {K}

/-- The **Brauer class of a Galois cocycle**: the class of the crossed product of its cocycle. -/
noncomputable def brauerClass (g : GaloisCocycle K) : BrauerGroup.{u, u} K :=
  BrauerGroup.crossedProductClass g.cocycle

/-- The Brauer class of a Galois cocycle is the crossed-product class of its cocycle. -/
theorem brauerClass_def (g : GaloisCocycle K) :
    g.brauerClass = BrauerGroup.crossedProductClass g.cocycle :=
  (rfl)

/-- The Brauer class of a bundled Galois cocycle is the crossed-product class of its cocycle. -/
@[simp]
theorem brauerClass_mk (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]
    [IsGalois K L] (c : TwoCocycle K L) :
    brauerClass ⟨L, c⟩ = BrauerGroup.crossedProductClass c :=
  (rfl)

end GaloisCocycle

namespace BrauerGroup

variable {K}

/-- **Every Brauer class is obtained from a Galois cocycle**: each class of `Br(K)` is the class
of the crossed product of a `2`-cocycle of a finite Galois subextension of `Kˢ/K`. -/
theorem exists_galoisCocycle_brauerClass_eq (x : BrauerGroup.{u, u} K) :
    ∃ g : GaloisCocycle K, g.brauerClass = x := by
  induction x using BrauerGroup.inductionOn with | h A
  obtain ⟨L, _, _, hL⟩ := Algebra.exists_finiteGalois_splittingField K A
  obtain ⟨c, hc⟩ := exists_crossedProductClass_eq_of_isSplittingField hL
  exact ⟨⟨L, c⟩, hc⟩

end BrauerGroup

end TauCeti
