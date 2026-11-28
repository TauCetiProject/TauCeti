/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Colimit
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.CategoryTheory.Abelian.RightDerived
public import TauCeti.CategoryTheory.Preadditive.FunctorCategory

/-!
# Exact colimits of functors commute with right derived functors

For a diagram `G : T ⥤ C ⥤ D` of additive functors between abelian categories where `C` has
injective resolutions and `D` has exact colimits of shape `T`, the canonical comparison
`colimitRightDerivedComparison G q` is an isomorphism
(`CategoryTheory.Limits.isIso_colimitRightDerivedComparison`), yielding
`CategoryTheory.Limits.colimitRightDerivedIso G q : colimit (rightDerivedDiagram G q) ≅
(colimit G).rightDerived q`.

## Main definitions

* `CategoryTheory.Limits.colimitRightDerivedComparison G q` and
  `CategoryTheory.Limits.colimitRightDerivedIso G q`.

## Main results

* `CategoryTheory.Limits.isIso_colimitRightDerivedComparison`: the comparison is an isomorphism
  when `D` has exact colimits of shape `T`.

## References

* [The Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954) (for filtered colimits
  of `Hom` functors computing local cohomology).
* A. Grothendieck, *Sur quelques points d'algèbre homologique*, Tohoku Math. J. (2) 9 (1957),
  119–221, §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂

section RightDerived

variable {T : Type w} [Category.{w'} T]
  {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasColimitsOfShape T D]

/-- The canonical comparison `colimit (rightDerivedDiagram G q) ⟶ (colimit G).rightDerived q`
assembled from the right derived transformations of `colimit.ι G t : G.obj t ⟶ colimit G`. -/
def colimitRightDerivedComparison (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ) :
    colimit (rightDerivedDiagram G q) ⟶ (colimit G).rightDerived q :=
  colimit.desc (rightDerivedDiagram G q)
    { pt := (colimit G).rightDerived q
      ι :=
        { app t := (colimit.ι G t).rightDerived q
          naturality _ _ w := by
            dsimp; rw [Category.comp_id, ← NatTrans.rightDerived_comp, colimit.w] } }

@[reassoc (attr := simp)]
lemma ι_colimitRightDerivedComparison (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ) (t : T) :
    colimit.ι (rightDerivedDiagram G q) t ≫ colimitRightDerivedComparison G q =
      (colimit.ι G t).rightDerived q :=
  colimit.ι_desc _ t

@[reassoc (attr := simp)]
lemma ι_app_colimitRightDerivedComparison_app (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ)
    (t : T) (X : C) :
    (colimit.ι (rightDerivedDiagram G q) t).app X ≫ (colimitRightDerivedComparison G q).app X =
      ((colimit.ι G t).rightDerived q).app X :=
  NatTrans.congr_app (ι_colimitRightDerivedComparison G q t) X

/-- For an injective resolution `I` of `X`, the objectwise identifications
`I.isoRightDerivedObj (G.obj t) q` assemble into a natural isomorphism of `T`-diagrams in `D`. -/
@[simps!]
private def rightDerivedEvaluationIso (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ)
    {X : C} (I : InjectiveResolution X) :
    rightDerivedDiagram G q ⋙ (evaluation C D).obj X ≅
      I.cocomplex.mapDiagram G ⋙ HomologicalComplex.homologyFunctor D _ q :=
  NatIso.ofComponents (fun t ↦ I.isoRightDerivedObj (G.obj t) q) fun {t t'} w ↦ by
    dsimp; rw [I.rightDerived_app_eq (G.map w) q, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]; simp only [HomologicalComplex.homologyFunctor_map]

variable [HasExactColimitsOfShape T D]

/-- When `D` has exact colimits of shape `T`, the canonical comparison
`colimit (rightDerivedDiagram G q) ⟶ (colimit G).rightDerived q` is an isomorphism in every
degree `q`. -/
instance isIso_colimitRightDerivedComparison (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ) :
    IsIso (colimitRightDerivedComparison G q) := by
  have : ∀ X : C, IsIso ((colimitRightDerivedComparison G q).app X) := fun X ↦ by
    let I := injectiveResolution X
    let hc₁ := isColimitOfPreserves ((evaluation C D).obj X)
      (colimit.isColimit (rightDerivedDiagram G q))
    let _ : (colimit.cocone G).pt.PreservesZeroMorphisms :=
      inferInstanceAs ((colimit G).PreservesZeroMorphisms)
    let c₂' := (Cocone.precompose (rightDerivedEvaluationIso G q I).hom).obj
      ((HomologicalComplex.homologyFunctor D _ q).mapCocone
        (I.cocomplex.mapCocone (colimit.cocone G)))
    let hc₂' := (IsColimit.precomposeHomEquiv (rightDerivedEvaluationIso G q I) _).invFun
      (isColimitOfPreserves (HomologicalComplex.homologyFunctor D _ q)
        (I.cocomplex.isColimitMapCocone (colimit.isColimit G)))
    -- `colimitRightDerivedComparison` followed by `I.isoRightDerivedObj (colimit G) q` is the
    -- unique cocone-point isomorphism between `hc₁` and `hc₂'`.
    have heq : (colimitRightDerivedComparison G q).app X ≫
        (I.isoRightDerivedObj (colimit G) q).hom = (hc₁.coconePointUniqueUpToIso hc₂').hom := by
      refine hc₁.hom_ext fun t ↦ ?_
      have hleg := hc₁.comp_coconePointUniqueUpToIso_hom hc₂' t
      dsimp [c₂'] at hleg ⊢
      rw [hleg, ι_app_colimitRightDerivedComparison_app_assoc,
        I.rightDerived_app_eq (colimit.ι G t) q, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, rightDerivedEvaluationIso_hom_app]
      simp only [HomologicalComplex.homologyFunctor_map]
    have : IsIso ((colimitRightDerivedComparison G q).app X ≫
        (I.isoRightDerivedObj (colimit G) q).hom) :=
      heq.symm ▸ inferInstanceAs (IsIso (hc₁.coconePointUniqueUpToIso hc₂').hom)
    exact IsIso.of_isIso_comp_right _ (I.isoRightDerivedObj (colimit G) q).hom
  exact NatIso.isIso_of_isIso_app _

/-- **Exact colimits of functors commute with right derived functors.** If `G : T ⥤ C ⥤ D` is a
diagram of additive functors and `D` has exact colimits of shape `T`, then the colimit of the
degree-`q` right derived functors of `G` is naturally isomorphic to the degree-`q` right derived
functor of `colimit G`. -/
def colimitRightDerivedIso (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ) :
    colimit (rightDerivedDiagram G q) ≅ (colimit G).rightDerived q :=
  asIso (colimitRightDerivedComparison G q)

@[simp]
lemma colimitRightDerivedIso_hom (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ) :
    (colimitRightDerivedIso G q).hom = colimitRightDerivedComparison G q :=
  (rfl)

@[reassoc (attr := simp)]
lemma rightDerived_ι_colimitRightDerivedIso_inv (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] (q : ℕ)
    (t : T) :
    (colimit.ι G t).rightDerived q ≫ (colimitRightDerivedIso G q).inv =
      colimit.ι (rightDerivedDiagram G q) t := by
  rw [← ι_colimitRightDerivedComparison, ← colimitRightDerivedIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end RightDerived

end CategoryTheory.Limits
