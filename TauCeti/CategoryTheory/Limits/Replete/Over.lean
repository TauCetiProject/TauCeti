/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import TauCeti.CategoryTheory.Limits.Replete

/-!
# Repleteness of slices and descent along covers

Slices of a replete category are replete whenever their forgetful functors preserve
epimorphisms. Conversely, if epimorphisms are stable under base change, repleteness of a slice
descends along an epimorphism of base objects. In particular, a category is replete if a slice
over an object covering a terminal object is replete.

These results allow sequential-limit arguments to be applied on slices, and checked after
passing to a cover. They apply to topoi: the forgetful functor from a slice preserves
epimorphisms, and epimorphisms are stable under base change. The preservation hypothesis on
the forgetful functor also follows from the existence of binary products, since that functor
is then a left adjoint.

## Main declarations

* `TauCeti.IsReplete.over`: slices of replete categories are replete.
* `TauCeti.IsReplete.of_over_map_epi`: repleteness descends along an epimorphism of base objects.
* `TauCeti.IsReplete.of_over_epi`: repleteness is detected on a slice over a cover of a
  terminal object.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Lemmas 3.1.2 and 3.1.3.
-/

public section

universe v u

open CategoryTheory Limits

namespace TauCeti.IsReplete

variable {C : Type u} [Category.{v} C]

attribute [local instance] IsCofiltered.isConnected

/-- A slice of a replete category is replete if its forgetful functor preserves epimorphisms.
This preservation holds, in particular, when the category has binary products or pushouts.
No existence of sequential limits is required. -/
instance over [IsReplete C] (U : C) [(Over.forget U).PreservesEpimorphisms] :
    IsReplete (Over U) where
  epi_π_app_zero {F} hF c hc := by
    have hmap (n : ℕ) : Epi ((Over.forget U).map (F.map (homOfLE (Nat.le_succ n)).op)) := by
      have := hF n
      infer_instance
    exact (Over.forget U).epi_of_epi_map
      (epi_π_app_zero hmap (isLimitOfPreserves (Over.forget U) hc))

/-- Repleteness of slices descends along an epimorphism of base objects, provided
epimorphisms are stable under base change and the target slice's forgetful functor preserves
epimorphisms. Pullback preserves limits and is faithful along such an epimorphism. -/
theorem of_over_map_epi [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {U V : C} (f : U ⟶ V) [Epi f] [(Over.forget V).PreservesEpimorphisms]
    [IsReplete (Over U)] : IsReplete (Over V) := by
  have (Z : C) (g : Z ⟶ V) : Epi (pullback.fst g f) :=
    MorphismProperty.pullback_fst (P := MorphismProperty.epimorphisms C) _ _ inferInstance
  have : (Over.pullback f).Faithful := inferInstance
  refine ⟨fun {F} hF {c} hc ↦ ?_⟩
  have hmap (n : ℕ) : Epi ((Over.pullback f).map (F.map (homOfLE (Nat.le_succ n)).op)) := by
    have := hF n
    have hleft : Epi ((Over.forget V).map (F.map (homOfLE (Nat.le_succ n)).op)) :=
      inferInstance
    exact Over.epi_of_epi_left _
      (hk := MorphismProperty.overPullbackMap f _ hleft)
  exact (Over.pullback f).epi_of_epi_map
    (epi_π_app_zero hmap (isLimitOfPreserves (Over.pullback f) hc))

/-- If a slice over an object covering a terminal object is replete, then the category is
replete, provided epimorphisms are stable under base change. -/
theorem of_over_epi [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {U T : C} (hT : IsTerminal T) (f : U ⟶ T) [Epi f] [IsReplete (Over U)] :
    IsReplete C := by
  let e := Over.equivalenceOfIsTerminal hT
  have : (Over.forget T).PreservesEpimorphisms :=
    inferInstanceAs e.functor.PreservesEpimorphisms
  have := of_over_map_epi f
  exact of_equivalence e

end TauCeti.IsReplete
