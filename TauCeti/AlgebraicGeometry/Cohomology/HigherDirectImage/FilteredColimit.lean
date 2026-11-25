/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FilteredColimit
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent

/-!
# Higher direct images commute with filtered colimits of quasi-coherent modules

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and `K : J ⥤ X.Modules`
a filtered diagram of quasi-coherent modules with colimit cocone `c`. For every `n`, the higher
direct image `Rⁿ f_*` sends `c` to a colimit cocone in `Y.Modules`
(`AlgebraicGeometry.Scheme.Hom.isColimitMapCoconeHigherDirectImage`): the canonical map
`colim_j Rⁿ f_* K_j ⟶ Rⁿ f_* (colim_j K_j)` is an isomorphism.

By `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isBasis` (a morphism of sheaves of modules is
an isomorphism once it is one on a basis of opens) it suffices to check that the canonical map is
bijective on sections over every affine open `V` of `Y`. Since every `Rⁿ f_* K_j` is
quasi-coherent, sections over `V` commute with their colimit, and the sections of `Rⁿ f_* M` are
`Hⁿ(f⁻¹ V, M)`, naturally in the quasi-coherent module `M`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_naturality`).
As `f⁻¹ V` is quasi-compact and quasi-separated, `Hⁿ(f⁻¹ V, -)` commutes with filtered colimits
of quasi-coherent modules
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyOnFunctor`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isColimitMapCoconeHigherDirectImage`: `Rⁿ f_*` preserves
  filtered colimits of quasi-coherent modules.

## References

* The Stacks Project, Lemma 30.4.5 (tag 01XJ) and Lemma 30.6.1 (tag 07TB).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Scheme.Modules

universe w w' u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

section FilteredColimit

variable {J : Type w} [Category.{w'} J] [EssentiallySmall.{u} J] [IsFiltered J]
  {K : J ⥤ X.Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent) {c : Cocone K} (hc : IsColimit c)

include hK hc in
/-- Over an affine open `V`, the sections of the higher direct images of a filtered colimit
cocone of quasi-coherent modules form a colimit cocone of abelian groups. -/
private def isColimitMapCoconeSectionsHigherDirectImage (n : ℕ) {V : Y.Opens}
    (hV : IsAffineOpen V) :
    IsColimit ((sectionsFunctor V ⋙ forget₂ _ AddCommGrpCat).mapCocone
      ((f.higherDirectImage n).mapCocone c)) := by
  have hM : c.pt.IsQuasicoherent := TauCeti.AlgebraicGeometry.isQuasicoherent_of_isColimit hK hc
  let e (M : X.Modules) [M.IsQuasicoherent] :
      (cohomologyOnFunctor X n (f ⁻¹ᵁ V)).obj M ≅
        (sectionsFunctor V ⋙ forget₂ _ AddCommGrpCat).obj ((f.higherDirectImage n).obj M) :=
    (f.higherDirectImageSectionsAddEquiv M n hV).toAddCommGrpIso
  let α : K ⋙ cohomologyOnFunctor X n (f ⁻¹ᵁ V) ≅
      (K ⋙ f.higherDirectImage n) ⋙ sectionsFunctor V ⋙ forget₂ _ AddCommGrpCat :=
    NatIso.ofComponents (fun j ↦ e (K.obj j)) fun {i j} ψ ↦ by
      ext x
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Functor.comp_map,
        Functor.comp_map, Functor.comp_map, forget₂_map_sectionsFunctor_map]
      -- The components of `e` are the bundled `higherDirectImageSectionsAddEquiv`, and the
      -- cohomology functor acts on morphisms by the abbreviation `cohomologyOnMap`, so this is
      -- the naturality square of `higherDirectImageSectionsAddEquiv`.
      exact f.higherDirectImageSectionsAddEquiv_naturality n (K.map ψ) hV x
  refine IsColimit.equivOfNatIsoOfIso α ((cohomologyOnFunctor X n (f ⁻¹ᵁ V)).mapCocone c)
    ((sectionsFunctor V ⋙ forget₂ _ AddCommGrpCat).mapCocone ((f.higherDirectImage n).mapCocone c))
    (Cocone.ext (e c.pt) fun j ↦ ?_)
    (isColimitMapCoconeCohomologyOnFunctor hK hc (f.isCompact_preimage hV.isCompact)
      (f.isQuasiSeparated_preimage hV.isQuasiSeparated) n)
  have := hK j
  ext x
  -- The components of `e` are the bundled `AddEquiv`s, so the component of this cocone
  -- morphism at `x` unfolds to the naturality square of `higherDirectImageSectionsAddEquiv`.
  change f.higherDirectImageSectionsAddEquiv c.pt n hV (cohomologyOnMap (c.ι.app j) n _
      ((f.higherDirectImageSectionsAddEquiv (K.obj j) n hV).symm x)) =
    ((f.higherDirectImage n).map (c.ι.app j)).app V x
  rw [f.higherDirectImageSectionsAddEquiv_naturality]
  exact congrArg _ (AddEquiv.apply_symm_apply _ x)

include hK hc in
/-- **Higher direct images commute with filtered colimits.** For a quasi-compact quasi-separated
morphism `f : X ⟶ Y` and a filtered essentially small diagram `K` of quasi-coherent modules on `X`
with colimit cocone `c`, the higher direct image `Rⁿ f_*` sends `c` to a colimit cocone:
`Rⁿ f_* (colim_j K_j)` is the colimit of the `Rⁿ f_* K_j`. -/
def isColimitMapCoconeHigherDirectImage (n : ℕ) :
    IsColimit ((f.higherDirectImage n).mapCocone c) := by
  let e := (equivSmallModel.{u} J).symm
  have : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence e.symm
  let D := f.higherDirectImage n
  let K' := e.functor ⋙ K
  have hK' : ∀ j, (K'.obj j).IsQuasicoherent := fun j ↦ hK (e.functor.obj j)
  have hK'' : ∀ j, ((K' ⋙ D).obj j).IsQuasicoherent := fun j ↦
    have := hK' j
    inferInstanceAs ((D.obj (K'.obj j)).IsQuasicoherent)
  refine IsColimit.ofWhiskerEquivalence e ?_
  let hc' := colimit.isColimit (K' ⋙ D)
  let t := (D.mapCocone c).whisker e.functor
  suffices IsIso (hc'.desc t) from IsColimit.ofPointIso hc'
  refine Hom.isIso_of_isBasis _ (B := fun V : Y.affineOpens ↦ V.val)
    (by simpa using Y.isBasis_affineOpens) fun V ↦ ?_
  let E := sectionsFunctor V.val ⋙ forget₂ (ModuleCat Γ(Y, V.val)) AddCommGrpCat
  have h₁ : IsColimit (E.mapCocone (colimit.cocone (K' ⋙ D))) :=
    isColimitOfPreserves (forget₂ (ModuleCat Γ(Y, V.val)) AddCommGrpCat)
      (TauCeti.AlgebraicGeometry.isColimitMapCoconeSectionsFunctor hK'' hc' V.property)
  have h₂ : IsColimit (E.mapCocone t) :=
    IsColimit.whiskerEquivalence
      (f.isColimitMapCoconeSectionsHigherDirectImage hK hc n V.property) e
  have : IsIso (E.map (hc'.desc t)) := by
    have : E.map (hc'.desc t) = (IsColimit.coconePointUniqueUpToIso h₁ h₂).hom :=
      h₁.hom_ext fun j ↦ by
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom, Functor.mapCocone_ι_app,
          Functor.mapCocone_ι_app, ← E.map_comp, hc'.fac]
    rw [this]
    infer_instance
  rwa [Functor.comp_map, forget₂_map_sectionsFunctor_map] at this

end FilteredColimit

end AlgebraicGeometry.Scheme.Hom
