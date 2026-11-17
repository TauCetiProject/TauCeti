/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The K-flat left derivability structure on module complexes

Let `R` be a commutative ring. Applying the functorial K-flat resolution of
`TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure` to the free-forgetful counit
`forget (ModuleCat R) ⋙ ModuleCat.free R ⟶ 𝟭 (ModuleCat R)` shows that the inclusion
`CochainComplex.kFlatLocalizerMorphism (ModuleCat R)` of K-flat complexes into
`CochainComplex (ModuleCat R) ℤ` is a localized equivalence, admits left resolutions of morphisms
and connected left-resolution categories, and forms a left derivability structure with respect to
quasi-isomorphisms.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4).
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

private instance (X : ModuleCat.{u} R) : PreservesFiniteLimits
    (MonoidalCategory.tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
  inferInstanceAs (PreservesFiniteLimits (MonoidalCategory.tensorLeft ((ModuleCat.free R).obj X)))

instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence :=
  isLocalizedEquivalence_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions :=
  hasLeftResolutions_arrow_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

instance (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsConnected ((kFlatLocalizerMorphism (ModuleCat.{u} R)).LeftResolution K) :=
  isConnected_leftResolution_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit K

/-- The inclusion of K-flat complexes of `R`-modules into `CochainComplex (ModuleCat.{u} R) ℤ` is a
left derivability structure with respect to quasi-isomorphisms. -/
instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

end CochainComplex
