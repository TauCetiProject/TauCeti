/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Open
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Effectivity of descent data is local on the base

Let `p : S' ⟶ S` be a surjective, flat and quasi-compact morphism of schemes and let `D` be a
descent datum relative to `p` on a scheme `X ⟶ S'`. For an open `U` of `S`, the preimage of `U` in
`X` is stable under `D` (`TauCeti.DescentDatum.isStable_comp_preimage`), so `D` restricts to it.
This file shows that `D` is effective as soon as each of these restrictions is effective, for `U`
ranging over the affine opens of `S`
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens`). Thus effectivity of
descent data along fpqc morphisms may be checked over the affine opens of the base, where it is
established by algebra, for instance from descent of graded algebras and their projective spectra
over an affine base. This is the gluing step needed for descent data on schemes which are not
affine over the base, such as projective schemes with a descended relatively ample line bundle.

The proof glues the local descents. For affine opens `V ≤ U` of `S`, write `Y U` for a scheme over
`S` whose base change is isomorphic to the restriction of `D` over `U`. The restriction over `V`
factors through the one over `U`, and by full faithfulness of base change along `p`
(`TauCeti.DescentDatum.Hom.descend`) this factorization descends to a morphism `Y V ⟶ Y U` over
`S`. Uniqueness of descended morphisms makes these morphisms functorial, and they are open
immersions identifying `Y V` with the part of `Y U` over `V`, because open immersions satisfy fpqc
descent. So the `Y U` form a relative gluing datum over the directed cover of `S` by its affine
opens (`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`), which glues to a scheme `Y` over `S`.
The isomorphisms over the affine opens glue to a morphism of descent data from the canonical descent
datum on `Y ×_S S'` to `D`, an isomorphism because it is one over each affine open of `S`.

## Main results

* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens`: a descent datum
  relative to a surjective, flat and quasi-compact morphism is effective if its restrictions over
  the affine opens of the base are effective.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'} (D : DescentDatum p X)

section Glue

variable {D} (Y : S.affineOpens → Over S)
  (g : ∀ U : S.affineOpens,
    Hom (baseChange p (Y U)) (D.restrict _ (D.isStable_comp_preimage U.1)))
  [∀ U, IsIso (g U).hom]

/-- The piece over `U`, as a morphism of descent data into `D`: an isomorphism onto the
restriction of `D` to the preimage of `U`. -/
private noncomputable def pieceHom (U : S.affineOpens) : Hom (baseChange p (Y U)) D :=
  (D.restrictHom _ (D.isStable_comp_preimage U.1)).comp (g U)

omit [∀ U, IsIso (g U).hom] in
private theorem pieceHom_hom_left (U : S.affineOpens) :
    (pieceHom Y g U).hom.left = (g U).hom.left ≫ ((X.hom ≫ p) ⁻¹ᵁ U.1).ι := by
  simp only [pieceHom, Hom.comp_hom, Over.comp_left, restrictHom_hom_left]

private instance (U : S.affineOpens) : IsOpenImmersion (pieceHom Y g U).hom.left := by
  have : IsIso (g U).hom.left := (Over.forget S').map_isIso (g U).hom
  rw [pieceHom_hom_left]
  infer_instance

private theorem range_pieceHom (U : S.affineOpens) :
    Set.range (pieceHom Y g U).hom.left = (X.hom ≫ p) ⁻¹' U.1 := by
  have : IsIso (g U).hom.left := (Over.forget S').map_isIso (g U).hom
  rw [pieceHom_hom_left]
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    have h : _ ∈ Set.range ((X.hom ≫ p) ⁻¹ᵁ U.1).ι := ⟨(g U).hom.left y, rfl⟩
    rw [Scheme.Opens.range_ι] at h
    rwa [Scheme.Hom.comp_apply]
  · obtain ⟨y, rfl⟩ : x ∈ Set.range ((X.hom ≫ p) ⁻¹ᵁ U.1).ι := by
      rw [Scheme.Opens.range_ι]
      exact hx
    obtain ⟨y', rfl⟩ := (g U).hom.left.surjective y
    exact ⟨y', Scheme.Hom.comp_apply _ _ _⟩

include g in
/-- Each piece lies over its affine open. -/
private theorem hom_mem [Surjective p] (U : S.affineOpens) (y : (Y U).left) :
    (Y U).hom y ∈ U.1 := by
  obtain ⟨y', rfl⟩ := (pullback.fst (Y U).hom p).surjective y
  have h : (pieceHom Y g U).hom.left y' ∈ (X.hom ≫ p) ⁻¹' U.1 :=
    range_pieceHom Y g U ▸ ⟨y', rfl⟩
  have hw : (pieceHom Y g U).hom.left ≫ X.hom = pullback.snd (Y U).hom p :=
    Over.w (pieceHom Y g U).hom
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hw]
  simp only [Set.mem_preimage, Scheme.Hom.comp_apply] at h
  exact h

include g in
/-- The structure morphism of a piece, which factors through its affine open. -/
private noncomputable def toOpen [Surjective p] (U : S.affineOpens) :
    (Y U).left ⟶ U.1.toScheme :=
  IsOpenImmersion.lift U.1.ι (Y U).hom <| by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hom_mem Y g U y

include g in
@[reassoc (attr := simp)]
private theorem toOpen_ι [Surjective p] (U : S.affineOpens) :
    toOpen Y g U ≫ U.1.ι = (Y U).hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism of descent data `Y V ×_S S' ⟶ Y U ×_S S'` factoring the piece over `V` through
the piece over `U`. -/
private noncomputable def transitionBaseChange {U V : S.affineOpens} (h : V ≤ U) :
    Hom (baseChange p (Y V)) (baseChange p (Y U)) :=
  (g U).inv.comp ((pieceHom Y g V).codRestrict (D.isStable_comp_preimage U.1) (by
    rw [range_pieceHom]
    exact Set.preimage_mono h))

private theorem comp_transitionBaseChange {U V : S.affineOpens} (h : V ≤ U) :
    (pieceHom Y g U).comp (transitionBaseChange Y g h) = pieceHom Y g V := by
  rw [pieceHom, transitionBaseChange, Hom.comp_assoc, ← Hom.comp_assoc (g U), Hom.comp_inv_self,
    Hom.id_comp, Hom.restrictHom_comp_codRestrict]

private theorem eq_transitionBaseChange {U V : S.affineOpens} (h : V ≤ U)
    (φ : Hom (baseChange p (Y V)) (baseChange p (Y U)))
    (hφ : (pieceHom Y g U).comp φ = pieceHom Y g V) :
    φ = transitionBaseChange Y g h := by
  refine Hom.ext (Over.OverMorphism.ext ?_)
  rw [← cancel_mono (pieceHom Y g U).hom.left]
  have h₁ := congrArg (fun f ↦ f.hom.left) hφ
  have h₂ := congrArg (fun f ↦ f.hom.left) (comp_transitionBaseChange Y g h)
  simp only [Hom.comp_hom, Over.comp_left] at h₁ h₂
  rw [h₁, h₂]

variable [Surjective p] [Flat p] [QuasiCompact p]

/-- The transition morphism `Y V ⟶ Y U` over `S`, for affine opens `V ≤ U` of `S`: the descent of
`transitionBaseChange`. -/
private noncomputable def transition {U V : S.affineOpens} (h : V ≤ U) : Y V ⟶ Y U :=
  (transitionBaseChange Y g h).descend

private theorem comp_baseChangeHom_transition {U V : S.affineOpens} (h : V ≤ U) :
    (pieceHom Y g U).comp (baseChangeHom p (transition Y g h)) = pieceHom Y g V := by
  rw [transition, baseChangeHom_descend, comp_transitionBaseChange]

private theorem eq_transition {U V : S.affineOpens} (h : V ≤ U) (φ : Y V ⟶ Y U)
    (hφ : (pieceHom Y g U).comp (baseChangeHom p φ) = pieceHom Y g V) :
    φ = transition Y g h := by
  rw [transition, ← eq_transitionBaseChange Y g h _ hφ, Hom.descend_baseChangeHom]

private theorem transition_refl (U : S.affineOpens) : transition Y g (le_refl U) = 𝟙 (Y U) :=
  (eq_transition Y g _ _ (by rw [baseChangeHom_id, Hom.comp_id])).symm

private theorem transition_trans {U V W : S.affineOpens} (hWV : W ≤ V) (hVU : V ≤ U) :
    transition Y g hWV ≫ transition Y g hVU = transition Y g (hWV.trans hVU) :=
  eq_transition Y g _ _ (by
    rw [baseChangeHom_comp, ← Hom.comp_assoc, comp_baseChangeHom_transition,
      comp_baseChangeHom_transition])

private instance isOpenImmersion_transition {U V : S.affineOpens} (h : V ≤ U) :
    IsOpenImmersion (transition Y g h).left := by
  have : IsOpenImmersion (baseChangeHom p (transition Y g h)).hom.left := by
    have h' := congrArg (fun f ↦ f.hom.left) (comp_baseChangeHom_transition Y g h)
    simp only [Hom.comp_hom, Over.comp_left] at h'
    have : IsOpenImmersion
        ((baseChangeHom p (transition Y g h)).hom.left ≫ (pieceHom Y g U).hom.left) := by
      rw [h']
      infer_instance
    exact IsOpenImmersion.of_comp _ (pieceHom Y g U).hom.left
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_baseChangeHom p (transition Y g h)) ⟨⟨inferInstance, inferInstance⟩,
      inferInstance⟩ this

private theorem range_transition {U V : S.affineOpens} (h : V ≤ U) :
    Set.range (transition Y g h).left = (Y U).hom ⁻¹' V.1 := by
  refine subset_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Over.w]
    exact hom_mem Y g V y
  obtain ⟨y', rfl⟩ := (pullback.fst (Y U).hom p).surjective y
  have hw : (pieceHom Y g U).hom.left ≫ X.hom = pullback.snd (Y U).hom p :=
    Over.w (pieceHom Y g U).hom
  have hmem : (pieceHom Y g U).hom.left y' ∈ Set.range (pieceHom Y g V).hom.left := by
    rw [range_pieceHom, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Category.assoc, hw,
      ← pullback.condition, Scheme.Hom.comp_apply]
    exact hy
  obtain ⟨y'', hy''⟩ := hmem
  have hc := congrArg (fun f ↦ f.hom.left) (comp_baseChangeHom_transition Y g h)
  simp only [Hom.comp_hom, Over.comp_left] at hc
  rw [← hc, Scheme.Hom.comp_apply] at hy''
  obtain rfl := (pieceHom Y g U).hom.left.isOpenEmbedding.injective hy''
  refine ⟨pullback.fst (Y V).hom p y'', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← (isPullback_baseChangeHom p _).w, Scheme.Hom.comp_apply]

/-- The pieces as a diagram of schemes over the affine opens of `S`. -/
private noncomputable def gluingFunctor : S.directedAffineCover.I₀ ⥤ Scheme.{u} where
  obj U := (Y U).left
  map f := (transition Y g (leOfHom f)).left
  map_id U := congrArg CommaMorphism.left (transition_refl Y g U)
  map_comp f f' := (congrArg CommaMorphism.left
    (transition_trans Y g (leOfHom f) (leOfHom f'))).symm

private theorem gluingFunctor_map {V U : S.directedAffineCover.I₀} (f : V ⟶ U) :
    (gluingFunctor Y g).map f = (transition Y g (leOfHom f)).left :=
  (rfl)

private instance {V U : S.directedAffineCover.I₀} (f : V ⟶ U) :
    IsOpenImmersion ((gluingFunctor Y g).map f) := by
  rw [gluingFunctor_map]
  exact isOpenImmersion_transition Y g _

/-- The structure morphisms of the pieces, as a natural transformation to the diagram of affine
opens of `S`. -/
private noncomputable def gluingNatTrans :
    gluingFunctor Y g ⟶ S.directedAffineCover.functorOfLocallyDirected where
  app U := toOpen Y g U
  naturality {V U} f := by
    -- The index type of the cover is only definitionally the type of affine opens, so the
    -- equation is assembled as a term rather than by rewriting.
    refine (cancel_mono (S.directedAffineCover.f U)).mp ?_
    exact ((Category.assoc _ _ _).trans ((congrArg ((gluingFunctor Y g).map f ≫ ·)
      (toOpen_ι Y g U)).trans (Over.w (transition Y g (leOfHom f))))).trans
      ((Category.assoc _ _ _).trans ((congrArg (toOpen Y g V ≫ ·)
        (S.directedAffineCover.trans_map f)).trans (toOpen_ι Y g V))).symm

private theorem preimage_opensRange_homOfLE {U V : S.affineOpens} (h : V ≤ U) :
    toOpen Y g U ⁻¹ᵁ (S.homOfLE h).opensRange = (transition Y g h).left.opensRange := by
  rw [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, toOpen_ι]
  ext y
  simp [range_transition]

/-- The relative gluing datum of the pieces over the directed cover of `S` by its affine opens:
over an inclusion `V ≤ U`, the piece over `V` is the part of the piece over `U` lying over `V`. -/
private noncomputable def gluingData : S.directedAffineCover.RelativeGluingData where
  functor := gluingFunctor Y g
  natTrans := gluingNatTrans Y g
  equifibered {V U} f := by
    refine (IsOpenImmersion.isPullback _ _ _ _ ((gluingNatTrans Y g).naturality f)
      (preimage_opensRange_homOfLE Y g (leOfHom f))).flip

/-- The scheme over `S` glued from the pieces. -/
private noncomputable def glued : Over S :=
  Over.mk (gluingData Y g).toBase

/-- The inclusion of a piece into the glued scheme, over `S`. -/
private noncomputable def ιGlued (U : S.affineOpens) : Y U ⟶ glued Y g :=
  Over.homMk (colimit.ι (gluingData Y g).functor U) <|
    ((gluingData Y g).ι_toBase U).trans (toOpen_ι Y g U)

/-- The base change of the inclusion of a piece, as a morphism of descent data. -/
private noncomputable abbrev ιGluedBaseChange (U : S.affineOpens) :
    Hom (baseChange p (Y U)) (baseChange p (glued Y g)) :=
  baseChangeHom p (ιGlued Y g U)

/-- The preimage of a piece in `glued ×_S S'` is the base change `Y U ×_S S'` of the piece. -/
private noncomputable def coverComparison (U : S.affineOpens) :
    pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g U).left ⟶
      pullback (Y U).hom p :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd _ p) <| by
    rw [← Over.w (ιGlued Y g U), ← Category.assoc, ← pullback.condition, Category.assoc,
      pullback.condition, Category.assoc]

private theorem transition_ιGlued {U V : S.affineOpens} (h : V ≤ U) :
    transition Y g h ≫ ιGlued Y g U = ιGlued Y g V :=
  Over.OverMorphism.ext (colimit.w (gluingData Y g).functor (homOfLE h))

private instance (U : S.affineOpens) : IsOpenImmersion (ιGlued Y g U).left :=
  (gluingData Y g).cover.map_prop U

/-- The comparison `coverComparison` is compatible with the transition morphisms: any morphism
`t` between the preimages of two pieces over the identity of `glued ×_S S'` is the base change of
the transition morphism. -/
private theorem comp_coverComparison {U V : S.affineOpens} (h : V ≤ U)
    (t : pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left ⟶
      pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g U).left)
    (ht : t ≫ pullback.fst _ _ = pullback.fst _ _) :
    t ≫ coverComparison Y g U ≫ (pieceHom Y g U).hom.left =
      coverComparison Y g V ≫ (pieceHom Y g V).hom.left := by
  have hc := congrArg (fun f ↦ f.hom.left) (comp_baseChangeHom_transition Y g h)
  simp only [Hom.comp_hom, Over.comp_left] at hc
  rw [← hc, ← Category.assoc, ← Category.assoc]
  congr 1
  -- The second coordinate of `t` is the transition morphism, because the inclusion of the piece
  -- over `U` into the glued scheme is a monomorphism.
  have hsnd : t ≫ pullback.snd _ (ιGlued Y g U).left =
      pullback.snd _ (ιGlued Y g V).left ≫ (transition Y g h).left := by
    rw [← cancel_mono (ιGlued Y g U).left, Category.assoc, ← pullback.condition,
      reassoc_of% ht, pullback.condition, Category.assoc, ← Over.comp_left, transition_ιGlued]
  refine pullback.hom_ext ?_ ?_
  · simp only [coverComparison, Category.assoc, pullback.lift_fst, hsnd,
      (isPullback_baseChangeHom p (transition Y g h)).w, pullback.lift_fst_assoc]
  · simp [coverComparison, reassoc_of% ht]

/-- The open cover of `glued ×_S S'` by the preimages of the pieces. -/
private noncomputable def cover : ((Over.pullback p).obj (glued Y g)).left.OpenCover :=
  (gluingData Y g).cover.pullback₁ (pullback.fst (glued Y g).hom p)

-- Instance search does not unfold `Precoverage.ZeroHypercover.pullback₁` to find Mathlib's
-- instances for the base change of a locally directed cover, so they are supplied by name.
private noncomputable instance : Category (cover Y g).I₀ :=
  Scheme.Cover.instCategoryI₀Pullback₁ (gluingData Y g).cover _

private noncomputable instance : (cover Y g).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover (gluingData Y g).cover _

/-- The members of `cover` are the preimages of the pieces, by definition of the base change of
a cover. -/
private theorem cover_f (U : S.affineOpens) :
    (cover Y g).f U = pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g U).left :=
  (rfl)

private theorem coverComparison_comp_hom (U : S.affineOpens) :
    (coverComparison Y g U ≫ (pieceHom Y g U).hom.left) ≫ X.hom =
      pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g U).left ≫
        pullback.snd (glued Y g).hom p := by
  simp [Over.w (pieceHom Y g U).hom, coverComparison]

/-- The restriction of the comparison morphism to the preimage of a piece. -/
private noncomputable def toXPiece (U : S.affineOpens) : (cover Y g).X U ⟶ X.left :=
  coverComparison Y g U ≫ (pieceHom Y g U).hom.left

private theorem trans_toXPiece {U V : (cover Y g).I₀} (f : V ⟶ U) :
    (cover Y g).trans f ≫ toXPiece Y g U = toXPiece Y g V :=
  comp_coverComparison Y g (leOfHom f) _
    (((congrArg _ (cover_f Y g U)).symm.trans ((cover Y g).trans_map f)).trans
      (cover_f Y g V))

/-- The comparison morphism `glued ×_S S' ⟶ X` over `S'`, glued from the pieces. -/
private noncomputable def toX : (Over.pullback p).obj (glued Y g) ⟶ X :=
  (cover Y g).glueMorphismsOverOfLocallyDirected
    (toXPiece Y g) (trans_toXPiece Y g)
    (fun U ↦ (coverComparison_comp_hom Y g U).trans
      (congrArg (· ≫ pullback.snd (glued Y g).hom p) (cover_f Y g U)).symm)

private theorem f_toX (U : (cover Y g).I₀) :
    (cover Y g).f U ≫ (toX Y g).left = toXPiece Y g U := by
  unfold toX
  exact Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left (cover Y g)
    (toXPiece Y g) _ _ U

private theorem fst_toX (U : S.affineOpens) :
    pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g U).left ≫ (toX Y g).left =
      coverComparison Y g U ≫ (pieceHom Y g U).hom.left :=
  (congrArg (· ≫ (toX Y g).left) (cover_f Y g U)).symm.trans (f_toX Y g U)

/-- On the base change of the piece over `U`, the comparison morphism is the piece itself. -/
@[reassoc]
private theorem ιGluedBaseChange_toX (U : S.affineOpens) :
    (ιGluedBaseChange Y g U).hom.left ≫ (toX Y g).left = (pieceHom Y g U).hom.left := by
  -- The base change of the piece factors through the preimage of the piece in `glued ×_S S'`,
  -- on which `coverComparison` is a retraction of this factorization.
  have hd : pullback.lift (ιGluedBaseChange Y g U).hom.left (pullback.fst _ _)
      (isPullback_baseChangeHom p (ιGlued Y g U)).w ≫ coverComparison Y g U = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_ <;> simp [coverComparison]
  rw [← pullback.lift_fst (ιGluedBaseChange Y g U).hom.left (pullback.fst _ _)
    (isPullback_baseChangeHom p (ιGlued Y g U)).w, Category.assoc, fst_toX, reassoc_of% hd]

private instance (U : S.affineOpens) :
    IsOpenImmersion (ιGluedBaseChange Y g U).hom.left :=
  MorphismProperty.of_isPullback (isPullback_baseChangeHom p (ιGlued Y g U)).flip
    (inferInstanceAs (IsOpenImmersion (ιGlued Y g U).left))

variable {Y g} in
/-- A point of the glued scheme lies in the piece over `U` exactly when it lies over `U`. -/
private theorem mem_range_ιGlued_iff {U : S.affineOpens} {y : (glued Y g).left} :
    y ∈ Set.range (ιGlued Y g U).left ↔ (glued Y g).hom y ∈ U.1 := by
  -- The index type of the cover is only definitionally the type of affine opens, so the
  -- characterization of the pieces is combined by `Iff.trans` rather than by rewriting.
  exact (Set.ext_iff.mp ((gluingData Y g).preimage_toBase_eq_range_ι U) y).symm.trans
    (Set.ext_iff.mp (Scheme.Opens.range_ι U.1) _)

variable {Y g} in
/-- A point of `glued ×_S S'` lies in the base change of the piece over `U` exactly when it lies
over `U`. -/
private theorem mem_range_ιGluedBaseChange_iff {U : S.affineOpens}
    {z : ((Over.pullback p).obj (glued Y g)).left} :
    z ∈ Set.range (ιGluedBaseChange Y g U).hom.left ↔
      p (pullback.snd (glued Y g).hom p z) ∈ U.1 := by
  have h : (ιGluedBaseChange Y g U).hom.left = pullback.map _ _ _ _
      (ιGlued Y g U).left (𝟙 S') (𝟙 S) (by simp) (by simp) := by
    refine pullback.hom_ext ?_ ?_ <;> simp [ιGluedBaseChange]
  rw [h, Scheme.Pullback.range_map, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    mem_range_ιGlued_iff, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact and_iff_left ⟨_, rfl⟩

/-- The map of action spaces `S' ×_S (Y U ×_S S') ⟶ S' ×_S (glued ×_S S')` induced by the base
change of the inclusion of a piece. -/
private noncomputable abbrev actionMap (U : S.affineOpens) :
    pullback p (((Over.pullback p).obj (Y U)).hom ≫ p) ⟶
      pullback p (((Over.pullback p).obj (glued Y g)).hom ≫ p) :=
  pullback.map p _ p _ (𝟙 S') (ιGluedBaseChange Y g U).hom.left (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
private theorem actionMap_fst (U : S.affineOpens) :
    actionMap Y g U ≫ pullback.fst p (pullback.snd (glued Y g).hom p ≫ p) =
      pullback.fst p (pullback.snd (Y U).hom p ≫ p) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
private theorem actionMap_snd (U : S.affineOpens) :
    actionMap Y g U ≫ pullback.snd p (pullback.snd (glued Y g).hom p ≫ p) =
      pullback.snd p (pullback.snd (Y U).hom p ≫ p) ≫ (ιGluedBaseChange Y g U).hom.left :=
  pullback.lift_snd _ _ _

private theorem isPullback_actionMap (U : S.affineOpens) :
    IsPullback (actionMap Y g U) (pullback.snd p _) (pullback.snd p _)
      (ιGluedBaseChange Y g U).hom.left :=
  IsPullback.of_right
    (by simpa using IsPullback.of_hasPullback p (((Over.pullback p).obj (Y U)).hom ≫ p))
    (actionMap_snd Y g U) (IsPullback.of_hasPullback p _)

private instance (U : S.affineOpens) : IsOpenImmersion (actionMap Y g U) :=
  MorphismProperty.of_isPullback (isPullback_actionMap Y g U).flip inferInstance

/-- The action spaces of the base changes of the pieces cover the action space of the base change
of the glued scheme. -/
private theorem exists_mem_range_actionMap
    (z : ↥(pullback p (((Over.pullback p).obj (glued Y g)).hom ≫ p))) :
    ∃ U : S.affineOpens, z ∈ Set.range (actionMap Y g U) := by
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp ((iSup_affineOpens_eq_top S).ge
    (Set.mem_univ (p (pullback.snd (glued Y g).hom p
      (pullback.snd p (((Over.pullback p).obj (glued Y g)).hom ≫ p) z)))))
  refine ⟨U, ?_⟩
  rw [Scheme.Pullback.range_map]
  exact ⟨⟨_, rfl⟩, mem_range_ιGluedBaseChange_iff.mpr hU⟩

/-- The comparison morphism is a morphism of descent data from the canonical descent datum on
`glued ×_S S'` to `D`. -/
private noncomputable def toXHom : Hom (baseChange p (glued Y g)) D where
  hom := toX Y g
  map_act := by
    refine Scheme.hom_ext_of_forall _ _ fun z ↦ ?_
    obtain ⟨U, hU⟩ := exists_mem_range_actionMap Y g z
    refine ⟨(actionMap Y g U).opensRange, hU, ?_⟩
    rw [← cancel_epi (actionMap Y g U).isoOpensRange.hom]
    simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
    have h : actionMap Y g U ≫ pullback.map p _ p (X.hom ≫ p) (𝟙 S') (toX Y g).left (𝟙 S)
        (by simp) (by simp) =
        pullback.map p _ p (X.hom ≫ p) (𝟙 S') (pieceHom Y g U).hom.left (𝟙 S) (by simp)
          (by simp) :=
      pullback.hom_ext (by simp) (by
        simp only [Category.assoc, pullback.map, pullback.lift_snd]
        exact (actionMap_snd_assoc Y g U _).trans
          (congrArg _ (ιGluedBaseChange_toX Y g U)))
    rw [reassoc_of% h, (pieceHom Y g U).map_act, (ιGluedBaseChange Y g U).map_act_assoc,
      ιGluedBaseChange_toX]

private theorem preimage_toX (U : S.affineOpens) :
    (toX Y g).left ⁻¹ᵁ ((X.hom ≫ p) ⁻¹ᵁ U.1).ι.opensRange =
      (ιGluedBaseChange Y g U).hom.left.opensRange := by
  have hw : (toX Y g).left ≫ X.hom = pullback.snd (glued Y g).hom p := Over.w (toX Y g)
  ext z
  rw [Scheme.Opens.opensRange_ι, SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage,
    Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, ← Set.mem_range,
    mem_range_ιGluedBaseChange_iff, ← Scheme.Hom.comp_apply, ← Category.assoc, hw,
    Scheme.Hom.comp_apply]

private instance isIso_toX : IsIso (toX Y g).left := by
  have hW : ⨆ U : S.affineOpens, (X.hom ≫ p) ⁻¹ᵁ U.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hW
    fun U ↦ ?_
  have hrange : Set.range (pieceHom Y g U).hom.left = Set.range ((X.hom ≫ p) ⁻¹ᵁ U.1).ι := by
    rw [range_pieceHom, Scheme.Opens.range_ι]
    rfl
  let eU := IsOpenImmersion.isoOfRangeEq (pieceHom Y g U).hom.left ((X.hom ≫ p) ⁻¹ᵁ U.1).ι
    hrange
  have hpb : IsPullback eU.hom (ιGluedBaseChange Y g U).hom.left
      ((X.hom ≫ p) ⁻¹ᵁ U.1).ι (toX Y g).left :=
    IsOpenImmersion.isPullback _ _ _ _
      (by rw [ιGluedBaseChange_toX, IsOpenImmersion.isoOfRangeEq_hom_fac])
      (preimage_toX Y g U)
  let i := hpb.isoIsPullback _ _ (isPullback_morphismRestrict (toX Y g).left _)
  have h : (toX Y g).left ∣_ ((X.hom ≫ p) ⁻¹ᵁ U.1) = i.inv ≫ eU.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoIsPullback_hom_fst]
  rw [MorphismProperty.isomorphisms.iff, h]
  infer_instance

end Glue

variable {D} in
/-- **Effectivity of descent data is local on the base.** Let `p : S' ⟶ S` be surjective, flat
and quasi-compact, and let `D` be a descent datum relative to `p` on `X ⟶ S'`. If, for every affine
open `U` of `S`, the restriction of `D` to the preimage of `U` in `X` is effective, then `D` is
effective: there are a scheme `Y` over `S` and an isomorphism from the canonical descent datum on
`Y ×_S S'` to `D`. -/
theorem exists_baseChange_hom_isIso_of_forall_affineOpens [Surjective p] [Flat p]
    [QuasiCompact p]
    (h : ∀ U : S.affineOpens, ∃ (Y : Over S)
      (g : Hom (baseChange p Y) (D.restrict _ (D.isStable_comp_preimage U.1))), IsIso g.hom) :
    ∃ (Y : Over S) (g : Hom (baseChange p Y) D), IsIso g.hom := by
  choose Y g hg using h
  have : IsIso ((Over.forget S').map (toXHom Y g).hom) := isIso_toX Y g
  exact ⟨glued Y g, toXHom Y g, isIso_of_reflects_iso _ (Over.forget S')⟩

end TauCeti.DescentDatum
