/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Separated group schemes

A group scheme is separated whenever its identity section is a closed immersion.
Translation by the tautological point carries the base change of the identity section to the
relative diagonal. Over a base with at most one point, every section is closed, so every
group scheme is separated. This includes spectra of fields and Artinian local rings.
Neither finite type nor commutativity is needed.

## References

* The Stacks Project, Tag 047J.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- A group scheme with closed identity section is separated over its base. -/
theorem isSeparated_of_isClosedImmersion_one {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsClosedImmersion η[G].left] : IsSeparated G.hom := by
  have hdiag : lift (𝟙 G) (𝟙 G) =
      ((λ_ G).inv ≫ η[G] ▷ G) ≫ (leftTranslationProd (𝟙 G)).hom := by
    ext <;> simp [leftTranslationProd_hom, MonObj.comp_mul, ← Hom.one_def]
  have : IsClosedImmersion (η[G] ▷ G).left := by
    have hP : MorphismProperty.IsMultiplicative
        (@IsClosedImmersion : MorphismProperty Scheme.{u}) := inferInstance
    have := hP.toContainsIdentities
    have := hP.toIsStableUnderComposition
    rw [Over.whiskerRight_left]
    exact MorphismProperty.pullbackMap (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (inferInstanceAs (IsClosedImmersion η[G].left))
      (MorphismProperty.id_mem _ _) (by simp) (by simp)
  refine ⟨?_⟩
  have hd : Limits.pullback.diagonal G.hom = (lift (𝟙 G) (𝟙 G)).left := by
    ext <;> simp
  rw [hd, hdiag, Over.comp_left, Over.comp_left]
  infer_instance

/-- Every group scheme over a base with at most one point is separated,
without finiteness assumptions. -/
instance isSeparated_of_grpObj {S : Scheme.{u}} [Subsingleton S]
    (G : Over S) [GrpObj G] : IsSeparated G.hom := by
  have : IsClosedImmersion η[G].left :=
    isClosedImmersion_of_comp_eq_id G.hom _ (Over.w η[G])
  exact isSeparated_of_isClosedImmersion_one G

end TauCeti.AlgebraicGeometry
