/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pullback

/-!
# Projective bundles of quotient modules

An epimorphism of quasi-coherent modules `F ⟶ G` on a scheme induces the closed immersion
`projectiveBundle.mapOfEpi : P(G) ⟶ P(F)` over the base. It is contravariantly functorial and
pulls back every integer twist by the canonical isomorphism
`projectiveBundle.mapOfEpiTwistingSheafIso`. The defining equation
`projectiveBundle.mapOfEpiTwistingSheafHom_def` and chart formula
`projectiveBundle.mapOfEpiTwistingSheafHom_comp_π` identify the comparison with the relative
Proj map and its affine chart components.

These constructions use `gradedSymmetricAlgebraDegreeOneIso` and the relative Proj results
`CommMon.isClosedImmersion_relativeProjMap_of_epi_one` and
`isIso_relativeProjTwistingSheafMap_gradedSymmetricAlgebra`.

## References

* [The Stacks Project, Section 27.21](https://stacks.math.columbia.edu/tag/01OA)
* [The Stacks Project, Lemma 27.11.5](https://stacks.math.columbia.edu/tag/01N1)
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle

open _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {F G H : QuasicoherentSheaf S}

section

variable (q : F.obj ⟶ G.obj) [Epi q]

/-- For an epimorphism of quasi-coherent modules, the graded symmetric algebra map satisfies
the irrelevant-ideal containment for the induced morphism of projective bundles. -/
theorem irrelevant_le_map_of_epi :
    ∀ U : S.Opens, IsAffineOpen U →
      HomogeneousIdeal.irrelevant (((gradedSymmetricAlgebra S).obj G).obj.gradedSectionsGrading U) ≤
        (HomogeneousIdeal.irrelevant
          (((gradedSymmetricAlgebra S).obj F).obj.gradedSectionsGrading U)).map
            (CommMon.gradedSectionsGradedHom
              ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom U) :=
  have := F.epi_gradedSymmetricAlgebra_map_one q
  CommMon.irrelevant_le_map_of_epi_one _ (isGeneratedInDegreeOne_gradedSymmetricAlgebra G)

/-- An epimorphism `q : F ⟶ G` induces the morphism `P(G) ⟶ P(F)` on the relative Proj
of the graded symmetric algebras. -/
@[stacks 01OA]
def mapOfEpi : projectiveBundle S G.obj ⟶ projectiveBundle S F.obj :=
  CommMon.relativeProjMap ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom
    (irrelevant_le_map_of_epi q)

/-- The defining equation for `mapOfEpi` exposes its construction by relative Proj. -/
theorem mapOfEpi_def :
    mapOfEpi q = CommMon.relativeProjMap ((gradedSymmetricAlgebra S).map
      (ObjectProperty.homMk q)).hom (irrelevant_le_map_of_epi q) :=
  (rfl)

/-- The map of projective bundles induced by an epimorphism lies over the base. -/
@[reassoc (attr := simp)]
theorem mapOfEpi_projection : mapOfEpi q ≫ projection S F.obj = projection S G.obj :=
  CommMon.relativeProjMap_relativeProjToBase _ _

/-- The map of projective bundles induced by an epimorphism is a closed immersion. -/
instance isClosedImmersion_mapOfEpi : IsClosedImmersion (mapOfEpi q) := by
  have := F.epi_gradedSymmetricAlgebra_map_one q
  exact CommMon.isClosedImmersion_relativeProjMap_of_epi_one _
    (isGeneratedInDegreeOne_gradedSymmetricAlgebra G)

/-- The identity module map induces the identity on the projective bundle. -/
@[simp]
theorem mapOfEpi_id (F : QuasicoherentSheaf S) :
    mapOfEpi (𝟙 F.obj) = 𝟙 (projectiveBundle S F.obj) := by
  have h : ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk (𝟙 F.obj))).hom =
      𝟙 ((gradedSymmetricAlgebra S).obj F).obj := by
    exact (ObjectProperty.ι _).congr_map ((gradedSymmetricAlgebra S).map_id F)
  refine (CommMon.relativeProjMap_congr h (irrelevant_le_map_of_epi (𝟙 F.obj)) ?_).trans
    (CommMon.relativeProjMap_id _)
  exact fun U _ ↦ CommMon.irrelevant_le_map_of_isIso (𝟙 _) U

/-- A composite of epimorphisms induces the composite of the projective bundle maps in
reverse order. -/
@[simp]
theorem mapOfEpi_comp (r : G.obj ⟶ H.obj) [Epi r] :
    mapOfEpi (q ≫ r) = mapOfEpi r ≫ mapOfEpi q := by
  have h : ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk (q ≫ r))).hom =
      ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom ≫
        ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk r)).hom := by
    exact ((gradedSymmetricAlgebra S) ⋙ ObjectProperty.ι _).map_comp
      (ObjectProperty.homMk q) (ObjectProperty.homMk r)
  have hcomp := h ▸ irrelevant_le_map_of_epi (q ≫ r)
  exact (CommMon.relativeProjMap_congr h (irrelevant_le_map_of_epi (q ≫ r)) hcomp).trans
    (CommMon.relativeProjMap_comp _ _ (irrelevant_le_map_of_epi q)
      (irrelevant_le_map_of_epi r) hcomp)

end

/-- A module isomorphism induces an isomorphism of projective bundles. -/
instance isIso_mapOfEpi (q : F.obj ⟶ G.obj) [IsIso q] : IsIso (mapOfEpi q) :=
  ⟨⟨mapOfEpi (inv q), by simp only [← mapOfEpi_comp, IsIso.inv_hom_id, mapOfEpi_id],
    by simp only [← mapOfEpi_comp, IsIso.hom_inv_id, mapOfEpi_id]⟩⟩

/-- The inverse of the projective-bundle map of a module isomorphism is induced by its inverse. -/
@[simp]
theorem inv_mapOfEpi (q : F.obj ⟶ G.obj) [IsIso q] :
    inv (mapOfEpi q) = mapOfEpi (inv q) := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← mapOfEpi_comp, IsIso.inv_hom_id, mapOfEpi_id]

variable (q : F.obj ⟶ G.obj) [Epi q]

/-- The canonical map from the pullback of `𝒪(m)` on `P(F)` to `𝒪(m)` on `P(G)`,
induced by the symmetric algebra map of the epimorphism. -/
def mapOfEpiTwistingSheafHom (m : ℤ) :
    (Scheme.Modules.pullback (mapOfEpi q)).obj (twistingSheaf S F.obj m).obj ⟶
      (twistingSheaf S G.obj m).obj :=
  CommMon.relativeProjTwistingSheafMap ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom
    (irrelevant_le_map_of_epi q) m

/-- The twist comparison followed by identification with the relative Proj twist is the relative
Proj comparison, after identifying the two pullback sources. -/
theorem mapOfEpiTwistingSheafHom_def (m : ℤ) :
    mapOfEpiTwistingSheafHom q m ≫ eqToHom (twistingSheaf_obj S G.obj m) =
      (Scheme.Modules.pullbackCongr (mapOfEpi_def q)).hom.app _ ≫
        (Scheme.Modules.pullback _).map (eqToHom (twistingSheaf_obj S F.obj m)) ≫
          CommMon.relativeProjTwistingSheafMap
            ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom
            (irrelevant_le_map_of_epi q) m := by
  have hF : eqToHom (twistingSheaf_obj S F.obj m) = 𝟙 (twistingSheaf S F.obj m).obj :=
    eqToHom_refl _ _
  have hG : eqToHom (twistingSheaf_obj S G.obj m) = 𝟙 (twistingSheaf S G.obj m).obj :=
    eqToHom_refl _ _
  have hq : (Scheme.Modules.pullbackCongr (mapOfEpi_def q)).hom.app
      (twistingSheaf S F.obj m).obj =
        𝟙 ((Scheme.Modules.pullback (mapOfEpi q)).obj (twistingSheaf S F.obj m).obj) := by
    simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
    exact eqToHom_refl _ _
  simp only [hF, hG, hq]
  -- Apply the category laws as terms so their object arguments can use definitional equality.
  refine (Category.comp_id _).trans ((Category.id_comp _).trans ?_).symm
  exact (congrArg (· ≫ _) ((Scheme.Modules.pullback (mapOfEpi q)).map_id _)).trans
    (Category.id_comp _)

/-- On an affine chart, the twist comparison is the relative Proj chart component. -/
theorem mapOfEpiTwistingSheafHom_comp_π (m : ℤ) (U : S.AffineZariskiSite) :
    mapOfEpiTwistingSheafHom q m ≫ eqToHom (twistingSheaf_obj S G.obj m) ≫
      (((gradedSymmetricAlgebra S).obj G).obj.relativeProjTwistingSheafGlueData m).π U =
    (Scheme.Modules.pullbackCongr (mapOfEpi_def q)).hom.app _ ≫
      (Scheme.Modules.pullback _).map (eqToHom (twistingSheaf_obj S F.obj m)) ≫
        CommMon.relativeProjTwistingSheafMapComponent
          ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom (irrelevant_le_map_of_epi q)
          m U := by
  have h := (reassoc_of% (mapOfEpiTwistingSheafHom_def q m))
    ((((gradedSymmetricAlgebra S).obj G).obj.relativeProjTwistingSheafGlueData m).π U)
  exact h.trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
    (CommMon.relativeProjTwistingSheafMap_comp_π _ (irrelevant_le_map_of_epi q) m U)))

/-- Pullback along the map induced by an epimorphism identifies the integer twists. -/
instance isIso_mapOfEpiTwistingSheafHom (m : ℤ) : IsIso (mapOfEpiTwistingSheafHom q m) :=
  isIso_relativeProjTwistingSheafMap_gradedSymmetricAlgebra F
    ((gradedSymmetricAlgebra S).map (ObjectProperty.homMk q)).hom (irrelevant_le_map_of_epi q) m

/-- The canonical pullback isomorphism for the integer twists along the map induced by an
epimorphism. -/
def mapOfEpiTwistingSheafIso (m : ℤ) :
    (Scheme.Modules.pullback (mapOfEpi q)).obj (twistingSheaf S F.obj m).obj ≅
      (twistingSheaf S G.obj m).obj :=
  asIso (mapOfEpiTwistingSheafHom q m)

/-- The forward map of the canonical pullback isomorphism is the twisting-sheaf map. -/
@[simp]
theorem mapOfEpiTwistingSheafIso_hom (m : ℤ) :
    (mapOfEpiTwistingSheafIso q m).hom = mapOfEpiTwistingSheafHom q m :=
  (rfl)

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
