/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.MonoidAlgebra.Artinian
public import TauCeti.RepresentationTheory.FDRepModuleMonoidAlgebra

/-!
# The dictionary between representations and modules is exact

`TauCeti.fdRepEquivalence` identifies the module-finite `k`-linear representations of a finite
monoid `G` with the finitely generated modules over the monoid algebra `k[G]`. This file compares
the two sides as *exact* categories: the conflations of
`TauCeti.finiteModulesExactStructure (MonoidAlgebra k G)` — the exact structure whose Grothendieck
group is `G₀(k[G])` — are exactly the images of the short exact sequences of `FDRep k G`
(`TauCeti.conflation_map_fdRepEquivalence_functor_iff`). This is the comparison through which the
Grothendieck group of the finitely generated `k[G]`-modules is read as a Grothendieck group of
representations. Both directions come from Mathlib's
`CategoryTheory.ShortExact.shortExact_map_iff`, applied to the dictionary and to the inclusion of
the finitely generated modules. A **group** algebra is the special case of a group `G`, which
nothing here needs.

Short exactness is read in the abelian categories `FDRep k G` and `FGModuleCat k[G]`, so the
coefficients are Noetherian here, that being the hypothesis under which `FGModuleCat` is abelian:
`FDRep k G` gets it from `k` directly and `FGModuleCat k[G]` from
`TauCeti.isNoetherianRing_monoidAlgebra`. The dictionary itself allows the monoid any universe, but
`TauCeti.finiteModulesExactStructure R` is defined only on `FGModuleCat.{u} R` for `R : Type u`, so
the comparison of exact structures is stated for a monoid in the universe of `k`.

## Main statements

* `TauCeti.conflation_map_fdRepEquivalence_functor_iff`: the dictionary matches short exact
  sequences of representations with the conflations of the finitely generated `k[G]`-modules.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

-- `TauCeti.finiteModulesExactStructure` pins the carrier universe of `FGModuleCat R` to the
-- universe of `R`, so the exact structure on `FGModuleCat.{u} k[G]` exists only when
-- `k[G] : Type u`, i.e. for `G` in the universe of `k`. The dictionary itself is universe
-- polymorphic in `G`.
variable (k G : Type u) [CommRing k] [IsNoetherianRing k] [Monoid G] [Finite G]

-- This is deliberately not a `simp` lemma: `TauCeti.finiteModulesExactStructure_conflation_iff` is
-- already one, so `simp` rewrites the left-hand side below before this lemma could fire, and
-- tagging it fails the `simpNF` linter.
/-- **The dictionary is exact.** A short complex of representations is short exact exactly when
its image is a conflation of the exact structure on the finitely generated `k[G]`-modules — the
exact structure whose Grothendieck group is `G₀(k[G])`. The dictionary is an equivalence between
abelian categories, hence exact, and faithful, hence exactness-reflecting. -/
theorem conflation_map_fdRepEquivalence_functor_iff (S : ShortComplex (FDRep k G)) :
    (finiteModulesExactStructure k[G]).Conflation (S.map (fdRepEquivalence k G).functor) ↔
      S.ShortExact :=
  (finiteModulesExactStructure_conflation_iff _ _).trans
    ((ShortExact.shortExact_map_iff (forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G]))).trans
      (ShortExact.shortExact_map_iff (fdRepEquivalence k G).functor))

end TauCeti
