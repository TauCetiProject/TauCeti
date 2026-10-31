/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# The functor of points of the total space of a vector bundle

For a finite locally free sheaf `E` on a scheme `X`, the points of the geometric total space
`𝕍(E) = Spec_X (Sym E^∨)` over a scheme `q : T ⟶ X` are the global sections `𝒪_T ⟶ q^* E` of the
pullback of `E` (`totalSpaceHomEquiv`). This file proves that this correspondence is natural in
the scheme over `X`: for a morphism `g : T' ⟶ T` over `X`, the section of `g ≫ t` is the pullback
along `g` of the section of `t` (`totalSpaceHomEquiv_comp`). Together with naturality in the
vector bundle (`totalSpaceHomEquiv_comp_map`), this makes the section correspondence a natural
isomorphism (`totalSpaceHomIso`) between the functor of points of `𝕍(E)` on schemes over `X` and
the presheaf `T ↦ Γ(T, q^* E)` of sections of pulled-back bundles (`pullbackSectionsPresheaf`),
naturally in `E`.

## Main declarations

* `TauCeti.AlgebraicGeometry.totalSpaceHomEquiv_comp`: naturality of the section correspondence
  in the scheme over `X`;
* `TauCeti.AlgebraicGeometry.comp_totalSpaceHomEquiv_symm_apply`: the same statement for the
  point of a section;
* `TauCeti.AlgebraicGeometry.pullbackSectionsPresheaf`: the presheaf `T ↦ Γ(T, q^* E)` on schemes
  over `X`, functorial in `E`;
* `TauCeti.AlgebraicGeometry.totalSpaceHomIso`: the natural isomorphism between the functor of
  points of `𝕍(E)` and `pullbackSectionsPresheaf`, natural in `E`.

## References

These use the convention `V(F) = Spec_X (Sym F)`, in which the total space of `E` is `V(E^∨)`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`.

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.8 and 1.7.9.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **Naturality of the section correspondence in the scheme over `X`.** For a morphism
`g : T' ⟶ T` over `X`, the section of `g ≫ t` is the pullback along `g` of the section of `t`:
the section `𝒪_{T'} ≅ g^* 𝒪_T ⟶ g^* q^* E ≅ (g ≫ q)^* E = q'^* E`, through the identification of
the pulled-back structure sheaf and the composition isomorphism of pullback. -/
theorem totalSpaceHomEquiv_comp (E : FiniteLocallyFreeSheaf X) {T' T : Over X} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceHomEquiv E T' (g ≫ t) =
      (Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map (totalSpaceHomEquiv E T t) ≫
          (Scheme.Modules.pullbackComp g.left T.hom).hom.app E.obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app E.obj := by
  -- Compare linear functionals on `q'^* (E^∨)`, where `q' = g ≫ q`: the universal property of
  -- `Spec_X (Sym E^∨)` turns precomposition with `g` into pullback of linear functionals along `g`,
  -- the base-change map of linear functionals is compatible with composites, and it carries
  -- pulled-back evaluation at a section to evaluation at the pulled-back section.
  obtain ⟨s, rfl⟩ := (totalSpaceHomEquiv E T).symm.surjective t
  rw [Equiv.apply_symm_apply, ← Equiv.eq_symm_apply, totalSpaceHomEquiv_symm_apply,
    totalSpaceHomEquiv_symm_apply]
  -- Compare the linear functionals of both sides. By naturality of the universal property of
  -- `Spec_X (Sym E^∨)`, the left side is the pullback along `g` of the functional of `s`.
  apply (relativeSpecSymmetricAlgebraPullbackHomEquiv
    ((toQuasicoherent X).obj (dual E)) T').injective
  refine (relativeSpecSymmetricAlgebraPullbackHomEquiv_comp _ g _).trans ?_
  refine (congrArg (fun φ ↦ _ ≫ _ ≫ (Scheme.Modules.pullback g.left).map φ ≫ _)
    (Equiv.apply_symm_apply _ _)).trans (Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm)
  -- Evaluation at the pulled-back section, transported to `q'^* E`, is evaluation at the
  -- pulled-back section of `g^* q^* E` after the dual of the transport.
  have hev := Scheme.Modules.dualHomUnitEquiv_symm_comp
    ((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫ (Scheme.Modules.pullback g.left).map s)
    ((Scheme.Modules.pullbackComp g.left T.hom).hom.app E.obj ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app E.obj)
  simp only [Scheme.Modules.dualHomUnitEquiv_symm_apply, Category.assoc] at hev
  rw [hev, pre_map, NatTrans.comp_app]
  simp only [Category.assoc]
  -- The base-change maps of linear functionals are compatible with `Over.w g` and with the
  -- composite `g ≫ q`, and they carry pulled-back evaluation to evaluation.
  rw [pullbackIhomComparison_app_unit_congr_assoc,
    ← Scheme.Hom.pullbackIhomComparison_app_unit_comp_assoc,
    ← Scheme.Hom.pullback_map_evaluation_comp_pullbackObjUnitIso_hom]
  simp only [Functor.map_comp, Category.assoc, toQuasicoherent_obj_obj]

/-- The point of the pulled-back section: precomposing the point of a section `s` of `q^* E` with
`g : T' ⟶ T` over `X` gives the point of the section `𝒪_{T'} ≅ g^* 𝒪_T ⟶ g^* q^* E ≅ q'^* E`. -/
theorem comp_totalSpaceHomEquiv_symm_apply (E : FiniteLocallyFreeSheaf X) {T' T : Over X}
    (g : T' ⟶ T) (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj E.obj) :
    g ≫ (totalSpaceHomEquiv E T).symm s =
      (totalSpaceHomEquiv E T').symm ((Scheme.Modules.pullbackObjUnitIso g.left).inv ≫
        (Scheme.Modules.pullback g.left).map s ≫
          (Scheme.Modules.pullbackComp g.left T.hom).hom.app E.obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g)).hom.app E.obj) := by
  rw [Equiv.eq_symm_apply, totalSpaceHomEquiv_comp, Equiv.apply_symm_apply]

variable (X) in
-- Exposed so that its values are visibly sets of sections `𝒪_T ⟶ q^* E`, as for the points of
-- `𝕍(E)` in `totalSpaceHomEquiv`.
/-- The presheaf of sections of pulled-back vector bundles on schemes over `X`: a finite locally
free sheaf `E` gives the presheaf `T ↦ Γ(T, q^* E) = Hom(𝒪_T, q^* E)` on schemes `q : T ⟶ X` over
`X`, whose restriction along `g : T' ⟶ T` pulls a section back along `g`, and a morphism
`a : E ⟶ F` acts by `q^* a`. -/
@[expose]
def pullbackSectionsPresheaf : FiniteLocallyFreeSheaf X ⥤ (Over X)ᵒᵖ ⥤ Type u where
  obj E :=
    { obj T := 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj E.obj
      map g := TypeCat.ofHom fun s ↦ (Scheme.Modules.pullbackObjUnitIso g.unop.left).inv ≫
        (Scheme.Modules.pullback g.unop.left).map s ≫
          (Scheme.Modules.pullbackComp g.unop.left _).hom.app E.obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g.unop)).hom.app E.obj
      -- The functor laws in `T` are transported from the points of `𝕍(E)` through the bijection
      -- `totalSpaceHomEquiv` and its naturality `totalSpaceHomEquiv_comp`.
      map_id T := by
        refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
        obtain ⟨t, rfl⟩ := (totalSpaceHomEquiv E T.unop).surjective s
        exact (totalSpaceHomEquiv_comp E (𝟙 T.unop) t).symm.trans
          (congrArg _ (Category.id_comp t))
      map_comp f g := by
        refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
        obtain ⟨t, rfl⟩ := (totalSpaceHomEquiv E _).surjective s
        exact (totalSpaceHomEquiv_comp E (g.unop ≫ f.unop) t).symm.trans
          ((congrArg _ (Category.assoc _ _ _)).trans
            ((totalSpaceHomEquiv_comp E g.unop (f.unop ≫ t)).trans
              (congrArg (fun s' ↦ _ ≫ (Scheme.Modules.pullback g.unop.left).map s' ≫ _)
                (totalSpaceHomEquiv_comp E f.unop t)))) }
  map a :=
    { app T := TypeCat.ofHom fun s ↦ s ≫ (Scheme.Modules.pullback T.unop.hom).map a.hom
      naturality T T' g := by
        refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
        obtain ⟨t, rfl⟩ := (totalSpaceHomEquiv _ T.unop).surjective s
        exact (congrArg (· ≫ _) (totalSpaceHomEquiv_comp _ g.unop t)).symm.trans
          ((totalSpaceHomEquiv_comp_map a T'.unop _).symm.trans
            ((congrArg _ (Category.assoc _ _ _)).trans
              ((totalSpaceHomEquiv_comp _ g.unop _).trans
                (congrArg (fun s' ↦ _ ≫ (Scheme.Modules.pullback g.unop.left).map s' ≫ _)
                  (totalSpaceHomEquiv_comp_map a T.unop t))))) }
  map_id E := by
    refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_)
    exact (congrArg (s ≫ ·) ((Scheme.Modules.pullback _).map_id _)).trans (Category.comp_id s)
  map_comp a b := by
    refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_)
    exact (congrArg (s ≫ ·) ((Scheme.Modules.pullback _).map_comp _ _)).trans
      (Category.assoc _ _ _).symm

/-- The presheaf `pullbackSectionsPresheaf X E` restricts a section along `g : T' ⟶ T` over `X`
by pulling it back along `g`, through `𝒪_{T'} ≅ g^* 𝒪_T` and `g^* q^* E ≅ q'^* E`. -/
@[simp]
lemma pullbackSectionsPresheaf_obj_map_apply (E : FiniteLocallyFreeSheaf X) {T T' : (Over X)ᵒᵖ}
    (g : T ⟶ T') (s : 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj E.obj) :
    ((pullbackSectionsPresheaf X).obj E).map g s =
      (Scheme.Modules.pullbackObjUnitIso g.unop.left).inv ≫
        (Scheme.Modules.pullback g.unop.left).map s ≫
          (Scheme.Modules.pullbackComp g.unop.left T.unop.hom).hom.app E.obj ≫
            (Scheme.Modules.pullbackCongr (Over.w g.unop)).hom.app E.obj :=
  (rfl)

/-- A morphism `a : E ⟶ F` acts on sections of `q^* E` by composition with `q^* a`. -/
@[simp]
lemma pullbackSectionsPresheaf_map_app_apply {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F)
    (T : (Over X)ᵒᵖ)
    (s : 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj E.obj) :
    ((pullbackSectionsPresheaf X).map a).app T s =
      s ≫ (Scheme.Modules.pullback T.unop.hom).map a.hom :=
  (rfl)

variable (X) in
/-- **The section-valued universal property of the total space**, natural in the vector bundle
`E` and in the scheme `T` over `X`: morphisms `T ⟶ 𝕍(E) = Spec_X (Sym E^∨)` over `X` correspond to
sections `𝒪_T ⟶ q^* E`. Its components are `totalSpaceHomEquiv`. -/
def totalSpaceHomIso :
    totalSpaceScheme X ⋙ MorphismProperty.Over.forget _ _ X ⋙ yoneda ≅ pullbackSectionsPresheaf X :=
  NatIso.ofComponents (fun E ↦ NatIso.ofComponents
    (fun T ↦ (totalSpaceHomEquiv E T.unop).toIso)
    (fun g ↦ ConcreteCategory.hom_ext _ _ fun t ↦ totalSpaceHomEquiv_comp E g.unop t))
    (fun a ↦ NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun t ↦
      totalSpaceHomEquiv_comp_map a T.unop t))

/-- The components of `totalSpaceHomIso` are `totalSpaceHomEquiv`. -/
lemma totalSpaceHomIso_hom_app_app (E : FiniteLocallyFreeSheaf X) (T : (Over X)ᵒᵖ)
    (t : T.unop ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    ((totalSpaceHomIso X).hom.app E).app T t = totalSpaceHomEquiv E T.unop t :=
  (rfl)

/-- The inverse components of `totalSpaceHomIso` are the inverse of `totalSpaceHomEquiv`. -/
lemma totalSpaceHomIso_inv_app_app (E : FiniteLocallyFreeSheaf X) (T : (Over X)ᵒᵖ)
    (s : 𝟙_ T.unop.left.Modules ⟶ (Scheme.Modules.pullback T.unop.hom).obj E.obj) :
    ((totalSpaceHomIso X).inv.app E).app T s = (totalSpaceHomEquiv E T.unop).symm s :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
