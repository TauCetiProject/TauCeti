/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Fibre products of algebraic spaces

For morphisms `f : F ⟶ H` and `g : G ⟶ H` of algebraic spaces, the fibre product `F ×_H G`,
computed in presheaves on schemes, is again an algebraic space (Stacks, Section 65.7 (02X0)).
Consequently the category `Spaces.AlgSpace` of algebraic spaces has pullbacks, and the inclusion
into presheaves on schemes creates them. Fibre products of algebraic spaces are needed to base
change morphisms of algebraic spaces, and so to define properties of morphisms of algebraic
spaces and of morphisms of algebraic stacks representable by algebraic spaces.

The three conditions of `Spaces.IsAlgebraicSpace` are checked separately.

* Sheaves are closed under limits.
* If `F` and `G` have representable diagonal, so has `F ×_H G`, for any presheaf `H`. The relative
  diagonal `G ⟶ G ×_H G` is representable by schemes
  (`CategoryTheory.Functor.relativelyRepresentable.pullback_diagonal`). The projection
  `F ×_H G ⟶ F` is a base change of `g`, so its relative diagonal is representable as well, and a
  morphism `h_U ⟶ F ×_H G` is representable because its composite with the projection to `F` is.
* For étale atlases `h_U ⟶ F` and `h_V ⟶ G`, the presheaf `h_U ×_H h_V` is represented by a
  scheme `W` because `H` has representable diagonal, and `h_W ⟶ F ×_H G` is an étale atlas: it is
  the composite of base changes of the two atlases.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal.pullback`: a fibre product of presheaves
  with representable diagonal has representable diagonal.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.pullback_lift`: the fibre product of two étale
  atlases over the base is an étale atlas of the fibre product.
* `TauCeti.AlgebraicGeometry.Spaces.isAlgebraicSpace_pullback`: fibre products of algebraic spaces
  are algebraic spaces; the base only needs to be an fppf sheaf with representable diagonal.
* The instance `ObjectProperty.IsClosedUnderLimitsOfShape IsAlgebraicSpace WalkingCospan`, which
  gives `Spaces.AlgSpace` pullbacks created by the inclusion into presheaves.

## References

* [Stacks Project, Section 65.7](https://stacks.math.columbia.edu/tag/02X0)
-/

public section

open CategoryTheory Limits MorphismProperty

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F G H : SchemePresheaf.{u}}

/-- A fibre product `F ×_H G` of presheaves on schemes with representable diagonal has
representable diagonal, whatever the presheaf `H`. -/
theorem RepresentableDiagonal.pullback (hF : RepresentableDiagonal F)
    (hG : RepresentableDiagonal G) (f : F ⟶ H) (g : G ⟶ H) :
    RepresentableDiagonal (pullback f g) := by
  -- A morphism `x : h_U ⟶ F ×_H G` is representable once `x ≫ fst` is and the relative diagonal
  -- of `fst`, a base change of that of `g`, is.
  have : (yoneda.relativelyRepresentable (C := Scheme.{u})).HasOfPostcompProperty
      (yoneda.relativelyRepresentable (C := Scheme.{u})).diagonal :=
    hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have hfst : (yoneda.relativelyRepresentable (C := Scheme.{u})).diagonal (pullback.fst f g) :=
    MorphismProperty.pullback_fst f g
      ((representableDiagonal_iff_diag.1 hG).pullback_diagonal g)
  exact representableDiagonal_iff.2 fun _ x ↦
    HasOfPostcompProperty.of_postcomp x (pullback.fst f g) hfst
      (hF.relativelyRepresentable (x ≫ pullback.fst f g))

/-- **Étale atlases of a fibre product.** Let `a : h_U ⟶ F` and `b : h_V ⟶ G` be étale atlases
and `f : F ⟶ H`, `g : G ⟶ H` morphisms of presheaves on schemes. If a scheme `W` with morphisms
`p : h_W ⟶ h_U` and `q : h_W ⟶ h_V` represents the fibre product of `a ≫ f` and `b ≫ g`, then
the induced morphism `h_W ⟶ F ×_H G` is an étale atlas. -/
theorem EtaleAtlas.pullback_lift {U V W : Scheme.{u}} {a : yoneda.obj U ⟶ F}
    {b : yoneda.obj V ⟶ G} (ha : EtaleAtlas a) (hb : EtaleAtlas b) {f : F ⟶ H} {g : G ⟶ H}
    {p : yoneda.obj W ⟶ yoneda.obj U} {q : yoneda.obj W ⟶ yoneda.obj V}
    (h : IsPullback p q (a ≫ f) (b ≫ g)) :
    EtaleAtlas (pullback.lift (f := f) (g := g) (p ≫ a) (q ≫ b) (by simpa using h.w)) := by
  -- The morphism factors as `h_W ⟶ h_U ×_H G ⟶ F ×_H G`: a base change of `b` along
  -- `h_U ×_H G ⟶ G`, followed by a base change of `a` along `F ×_H G ⟶ F`.
  let c₂ : pullback (a ≫ f) g ⟶ pullback f g :=
    pullback.map (a ≫ f) g f g a (𝟙 G) (𝟙 H) (by simp) (by simp)
  let c₁ : yoneda.obj W ⟶ pullback (a ≫ f) g :=
    pullback.lift p (q ≫ b) (by simpa using h.w)
  have h₂ : IsPullback (pullback.fst (a ≫ f) g) c₂ a (pullback.fst f g) :=
    IsPullback.of_bot (by simpa [c₂] using IsPullback.of_hasPullback (a ≫ f) g) (by simp [c₂])
      (IsPullback.of_hasPullback f g)
  have h₁ : IsPullback q c₁ b (pullback.snd (a ≫ f) g) :=
    IsPullback.of_bot (by simpa [c₁] using h.flip) (by simp [c₁])
      (IsPullback.of_hasPullback (a ≫ f) g).flip
  have hc : pullback.lift (f := f) (g := g) (p ≫ a) (q ≫ b) (by simpa using h.w) = c₁ ≫ c₂ := by
    ext <;> simp [c₁, c₂]
  -- Both relative properties are stable under base change and composition.
  have key (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
      (hPa : P.presheaf a) (hPb : P.presheaf b) : P.presheaf (c₁ ≫ c₂) :=
    have := relative_isStableUnderBaseChange (F := yoneda) P
    comp_mem _ _ _ (of_isPullback h₁ hPb) (of_isPullback h₂ hPa)
  -- Instance search does not recover these parents of the `IsMultiplicative` instances.
  have : IsStableUnderComposition @Etale.{u} :=
    IsMultiplicative.toIsStableUnderComposition
  have : IsStableUnderComposition @Surjective.{u} :=
    IsMultiplicative.toIsStableUnderComposition
  rw [hc]
  exact ⟨key _ ha.etale hb.etale, key _ ha.surjective hb.surjective⟩

/-- **Fibre products of algebraic spaces are algebraic spaces** (Stacks, Section 65.7 (02X0)): for
morphisms `f : F ⟶ H` and `g : G ⟶ H` from algebraic spaces to an fppf sheaf `H` with
representable diagonal, for instance an algebraic space, the fibre product `F ×_H G` in
presheaves on schemes is an algebraic space. -/
@[stacks 02X0]
theorem isAlgebraicSpace_pullback (hF : IsAlgebraicSpace F) (hG : IsAlgebraicSpace G)
    (hH : Presheaf.IsSheaf Scheme.fppfTopology H) (hH' : RepresentableDiagonal H) (f : F ⟶ H)
    (g : G ⟶ H) : IsAlgebraicSpace (pullback f g) where
  isSheaf := ObjectProperty.prop_limit (Presheaf.IsSheaf Scheme.fppfTopology (A := Type u))
    (cospan f g) (by rintro (_ | _ | _); exacts [hH, hF.isSheaf, hG.isSheaf])
  representableDiagonal := hF.representableDiagonal.pullback hG.representableDiagonal f g
  exists_etaleAtlas := by
    obtain ⟨U, a, ha⟩ := hF.exists_etaleAtlas
    obtain ⟨V, b, hb⟩ := hG.exists_etaleAtlas
    obtain ⟨W, q, p, h⟩ := hH'.relativelyRepresentable (a ≫ f) (b ≫ g)
    exact ⟨W, _, ha.pullback_lift hb h⟩

/-- Algebraic spaces are closed under fibre products in presheaves on schemes. Through Mathlib's
instances for full subcategories, `Spaces.AlgSpace` has pullbacks, created by the inclusion
`Spaces.AlgSpace.toPresheaf`. -/
instance : ObjectProperty.IsClosedUnderLimitsOfShape
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) WalkingCospan where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    have hH := h.prop_diag_obj .one
    exact (isAlgebraicSpace_pullback (h.prop_diag_obj _) (h.prop_diag_obj _) hH.isSheaf
      hH.representableDiagonal (h.diag.map WalkingCospan.Hom.inl)
      (h.diag.map WalkingCospan.Hom.inr)).of_iso
      ((HasLimit.isoOfNatIso (diagramIsoCospan h.diag)).symm ≪≫
        limit.isoLimitCone ⟨_, h.isLimit⟩)

end TauCeti.AlgebraicGeometry.Spaces
