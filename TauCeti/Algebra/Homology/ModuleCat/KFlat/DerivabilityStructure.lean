/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The K-flat left derivability structure on complexes of modules

For a commutative ring `R`, the free–forgetful adjunction `ModuleCat.adj R` on `ModuleCat.{u} R`
has a faithful right adjoint, so its counit `(ModuleCat.adj R).counit` supplies a functorial flat
cover `CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R ⟶ 𝟭 (ModuleCat.{u} R)` of every
`R`-module. Specializing `TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure` shows that
`CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)` has left resolutions of arrows
(`CochainComplex.hasLeftResolutions_arrow_kFlatLocalizerMorphism_moduleCat`), induces an equivalence
on localized categories (`CochainComplex.isLocalizedEquivalence_kFlatLocalizerMorphism_moduleCat`),
and forms a left derivability structure with respect to quasi-isomorphisms
(`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat`).

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

public section

open CategoryTheory

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- The localizer morphism `kFlatLocalizerMorphism (ModuleCat.{u} R)` has left resolutions of
arrows. -/
instance hasLeftResolutions_arrow_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions :=
  have (M : ModuleCat.{u} R) :
      Module.Flat R ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj M) :=
    Module.Flat.finsupp M
  hasLeftResolutions_arrow_kFlatLocalizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

/-- The inclusion of K-flat complexes of `R`-modules induces an equivalence on localized
categories. -/
instance isLocalizedEquivalence_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence :=
  have (M : ModuleCat.{u} R) :
      Module.Flat R ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj M) :=
    Module.Flat.finsupp M
  isLocalizedEquivalence_kFlatLocalizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

/-- The inclusion of K-flat complexes into `CochainComplex (ModuleCat.{u} R) ℤ` is a left
derivability structure with respect to quasi-isomorphisms. -/
instance isLeftDerivabilityStructure_kFlatLocalizerMorphism_moduleCat :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure :=
  have (M : ModuleCat.{u} R) :
      Module.Flat R ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj M) :=
    Module.Flat.finsupp M
  isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

end CochainComplex
