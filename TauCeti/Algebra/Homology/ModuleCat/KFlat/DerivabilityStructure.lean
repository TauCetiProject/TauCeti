/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import TauCeti.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The K-flat left derivability structure on complexes of modules

Over a commutative ring `R`, the free-forgetful adjunction `ModuleCat.adj R` furnishes a functorial
epimorphic cover of every `R`-module by a projective (hence flat) `R`-module. Together with
exactness of countable coproducts and sequential colimits in `ModuleCat.{u} R` and preservation of
colimits by tensor products, `CochainComplex.KFlat.isLeftDerivabilityStructure_localizerMorphism`
makes `CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)` a left derivability structure on
unbounded cochain complexes of `R`-modules with respect to quasi-isomorphisms.

## Main results

* `CochainComplex.KFlat.instHasLeftResolutionsArrowLocalizerMorphismModuleCat`,
  `CochainComplex.KFlat.instIsLocalizedEquivalenceLocalizerMorphismModuleCat`,
  `CochainComplex.KFlat.instIsConnectedLeftResolutionLocalizerMorphismModuleCat`,
  `CochainComplex.KFlat.instIsLeftDerivabilityStructureLocalizerMorphismModuleCat`: the K-flat
  localizer morphism on `CochainComplex (ModuleCat.{u} R) ℤ` admits arrow resolutions, induces a
  localized equivalence, has connected resolution categories, and forms a left derivability
  structure.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* Joël Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42.
* [The Stacks Project][stacks], Section 15.60, Lemma 15.60.10 (Tag 06Y4).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R]

private theorem preservesFiniteLimits_tensorLeft_forget_comp_free_obj (X : ModuleCat.{u} R) :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft
      ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R).obj X)) := by
  dsimp only [Functor.comp_obj]
  infer_instance

/-- The K-flat localizer morphism on `CochainComplex (ModuleCat.{u} R) ℤ` admits left resolutions in
the category of arrows. -/
instance instHasLeftResolutionsArrowLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions := by
  have := preservesFiniteLimits_tensorLeft_forget_comp_free_obj (R := R)
  exact hasLeftResolutions_arrow_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

/-- The inclusion of K-flat complexes into all cochain complexes of `R`-modules induces an
equivalence on localized categories with respect to quasi-isomorphisms. -/
instance instIsLocalizedEquivalenceLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence := by
  have := preservesFiniteLimits_tensorLeft_forget_comp_free_obj (R := R)
  exact isLocalizedEquivalence_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

/-- For every cochain complex `K` of `R`-modules, the category of K-flat left resolutions of `K` is
connected. -/
instance instIsConnectedLeftResolutionLocalizerMorphismModuleCat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsConnected ((localizerMorphism (ModuleCat.{u} R)).LeftResolution K) := by
  have := preservesFiniteLimits_tensorLeft_forget_comp_free_obj (R := R)
  exact isConnected_leftResolution_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit K

/-- Over a commutative ring `R`, the inclusion of K-flat cochain complexes into all cochain
complexes of `R`-modules is a left derivability structure with respect to quasi-isomorphisms. -/
instance instIsLeftDerivabilityStructureLocalizerMorphismModuleCat :
    (localizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure := by
  have := preservesFiniteLimits_tensorLeft_forget_comp_free_obj (R := R)
  exact isLeftDerivabilityStructure_localizerMorphism
    (CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free.{u} R)
    (ModuleCat.adj.{u} R).counit

end CochainComplex.KFlat
