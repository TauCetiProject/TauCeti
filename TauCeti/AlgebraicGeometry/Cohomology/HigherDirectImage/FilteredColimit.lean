/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FilteredColimit
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Higher direct images commute with filtered colimits of quasi-coherent modules

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and `K : J ⥤ X.Modules`
a filtered diagram of quasi-coherent modules with colimit cocone `c`. For every `n`, the higher
direct image `Rⁿ f_*` sends `c` to a colimit cocone in `Y.Modules`
(`AlgebraicGeometry.Scheme.Hom.isColimitMapCoconeHigherDirectImage`): the canonical map
`colim_j Rⁿ f_* K_j ⟶ Rⁿ f_* (colim_j K_j)` is an isomorphism.

Both sides are quasi-coherent, so it suffices to check that the canonical map is bijective on
sections over every affine open `V` of `Y`
(`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app_affineOpens`, a morphism of sheaves of
modules is an isomorphism once it is one on a basis of opens). Over `V` the sections of the
colimit are the colimit of the sections, since sections over an affine open preserve colimits of
quasi-coherent sheaves, and the sections of `Rⁿ f_* M` are `Hⁿ(f⁻¹ V, M)`, naturally in the
quasi-coherent module `M` (`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_map`).
As `f⁻¹ V` is quasi-compact and quasi-separated, `Hⁿ(f⁻¹ V, -)` commutes with filtered colimits
of quasi-coherent modules
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyOnFunctor`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app_affineOpens`: a morphism of sheaves of
  modules on a scheme which is an isomorphism on sections over every affine open is an
  isomorphism;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsAddEquiv_map`: the identification of
  the sections of `Rⁿ f_* M` over an affine open `V` with `Hⁿ(f⁻¹ V, M)` is natural in `M`;
* `AlgebraicGeometry.Scheme.Hom.isColimitMapCoconeHigherDirectImage`: `Rⁿ f_*` preserves
  filtered colimits of quasi-coherent modules.

## References

* The Stacks Project, Lemma 30.4.5 (tag 01XJ) and Lemma 30.6.1 (tag 07TB).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry Scheme.Modules

universe w w' u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- **Isomorphisms of sheaves of modules are detected on affine opens.** A morphism of sheaves of
modules on a scheme which is an isomorphism on sections over every affine open is an
isomorphism, since the affine opens form a basis of the topology. -/
theorem isIso_of_isIso_app_affineOpens {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso (φ.app U)) : IsIso φ := by
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : X.affineOpens ↦ (U : X.Opens))
      (by simpa using X.isBasis_affineOpens) h
  exact Hom.isIso_iff_isIso_app.2 fun U ↦
    inferInstanceAs (IsIso (((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom.app (op U)))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The identification `higherDirectImagePresheafSectionsLinearEquiv` of the sections of the
presheaf `V ↦ Hⁿ(f⁻¹ V, M)` over an affine open with those of `Rⁿ f_* M` is natural in the
quasi-coherent module `M`. -/
lemma higherDirectImagePresheafSectionsLinearEquiv_map {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (ψ : M ⟶ N) (n : ℕ) {V : Y.Opens} (hV : IsAffineOpen V)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    f.higherDirectImagePresheafSectionsLinearEquiv N n hV
        (((f.higherDirectImagePresheaf n).map ψ).app _ x) =
      ((f.higherDirectImage n).map ψ).app V
        (f.higherDirectImagePresheafSectionsLinearEquiv M n hV x) := by
  simp only [higherDirectImagePresheafSectionsLinearEquiv_apply]
  have h₁ := congrArg (fun g ↦ (g.app (op V)).hom x)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.naturality
      ((f.higherDirectImagePresheaf n).map ψ))
  have h₂ := congrArg (fun g ↦ Scheme.Modules.Hom.app g V)
    ((f.higherDirectImagePresheafSheafificationIso n).hom.naturality ψ)
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    Scheme.Modules.Hom.comp_app] at h₁ h₂
  erw [h₁]
  exact ConcreteCategory.congr_hom h₂ _

/-- **Naturality of the sections of higher direct images over affine opens.** The identification
`higherDirectImageSectionsAddEquiv` of the sections of `Rⁿ f_* M` over an affine open `V` with
`Hⁿ(f⁻¹ V, M)` is natural in the quasi-coherent module `M`. -/
lemma higherDirectImageSectionsAddEquiv_map {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (ψ : M ⟶ N) (n : ℕ) {V : Y.Opens} (hV : IsAffineOpen V)
    (x : cohomologyOn M n (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv N n hV (cohomologyOnMap ψ n (f ⁻¹ᵁ V) x) =
      ((f.higherDirectImage n).map ψ).app V (f.higherDirectImageSectionsAddEquiv M n hV x) := by
  obtain ⟨y, rfl⟩ : ∃ y, (f.higherDirectImagePresheafToPresheafIso M n).hom.app (op V) y = x :=
    ⟨_, Iso.inv_hom_id_apply ((f.higherDirectImagePresheafToPresheafIso M n).app _) x⟩
  have h := congrArg (fun g ↦ (g.app (op V)).hom y)
    (f.higherDirectImagePresheafToPresheafIso_naturality ψ n)
  dsimp at h
  have h' : cohomologyOnMap ψ n (f ⁻¹ᵁ V)
      ((f.higherDirectImagePresheafToPresheafIso M n).hom.app (op V) y) =
      (f.higherDirectImagePresheafToPresheafIso N n).hom.app (op V)
        (((f.higherDirectImagePresheaf n).map ψ).app (op V) y) := h.symm
  rw [h', higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  erw [higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app]
  exact f.higherDirectImagePresheafSectionsLinearEquiv_map ψ n hV y

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
      exact f.higherDirectImageSectionsAddEquiv_map (K.map ψ) n hV x
  refine IsColimit.equivOfNatIsoOfIso α ((cohomologyOnFunctor X n (f ⁻¹ᵁ V)).mapCocone c)
    ((sectionsFunctor V ⋙ forget₂ _ AddCommGrpCat).mapCocone ((f.higherDirectImage n).mapCocone c))
    (Cocone.ext (e c.pt) fun j ↦ ?_)
    (isColimitMapCoconeCohomologyOnFunctor hK hc (f.isCompact_preimage hV.isCompact)
      (f.isQuasiSeparated_preimage hV.isQuasiSeparated) n)
  have := hK j
  ext x
  change f.higherDirectImageSectionsAddEquiv c.pt n hV (cohomologyOnMap (c.ι.app j) n _
      ((f.higherDirectImageSectionsAddEquiv (K.obj j) n hV).symm x)) =
    ((f.higherDirectImage n).map (c.ι.app j)).app V x
  rw [f.higherDirectImageSectionsAddEquiv_map]
  erw [AddEquiv.apply_symm_apply]

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
  refine isIso_of_isIso_app_affineOpens _ fun V ↦ ?_
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
  exact this

end FilteredColimit

end AlgebraicGeometry.Scheme.Hom
