/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Open
public import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Gluing effective descent data

Let `p : S' ⟶ S` be a surjective, flat and quasi-compact morphism of schemes and let `D` be a
descent datum relative to `p` on a scheme `X ⟶ S'`. This file shows that effectivity of `D` is
local on `X` for its stable opens: if `X` is covered by opens `U i`, each stable under `D`, such
that each restriction `D.restrict (U i)` is effective, then `D` is effective
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_iSup_eq_top`). For an open `U` of `S`, the
preimage of `U` in `X` is stable (`TauCeti.DescentDatum.isStable_comp_preimage`), so in particular
effectivity of descent data along fpqc morphisms may be checked over the affine opens of the base
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens`), where it is
established by algebra. Stable covers which do not come from the base arise for schemes with a
compatibly descended relatively ample line bundle, from the stable quasi-affine opens where
invariant sections of the powers of the line bundle do not vanish.

The proof glues the local descents. The stable opens `V` of `X` contained in some `U i` are closed
under intersection, and the restriction of `D` to each of them is effective
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_restrict_of_le`). Write `Y V` for a scheme over
`S` whose base change is isomorphic to `D.restrict V`. For `V ≤ W` the inclusion of `V` factors
through `W`, and by full faithfulness of base change along `p` (`TauCeti.DescentDatum.Hom.descend`)
this factorization descends to a morphism `Y V ⟶ Y W` over `S`. Uniqueness of descended morphisms
makes these morphisms functorial, and they are open immersions because open immersions satisfy
fpqc descent. Since the points of `Y W` are images of points of its base change, the images of
`Y V₁` and `Y V₂` in `Y W` meet in the image of `Y (V₁ ⊓ V₂)`, so the `Y V` form a locally
directed diagram of open immersions (`AlgebraicGeometry.Scheme.IsLocallyDirected`), whose colimit
is a scheme `Y` over `S`. The isomorphisms over the `V` glue to a morphism of descent data from the
canonical descent datum on `Y ×_S S'` to `D`, an isomorphism because it is one over each `U i`.

## Main results

* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_iSup_eq_top`: a descent datum relative to a
  surjective, flat and quasi-compact morphism is effective if its restrictions to the members of a
  cover of `X` by stable opens are effective.
* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens`: a descent datum
  relative to a surjective, flat and quasi-compact morphism is effective if its restrictions over
  the affine opens of the base are effective.
* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens_pullbackAlong`: a descent
  datum relative to a surjective, flat and quasi-compact morphism is effective if its base changes
  to the affine opens of the base are effective.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1 and §7.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'} (D : DescentDatum p X)

section Glue

/-! The pieces are indexed by a meet-semilattice `J`, through a map `𝒱` to the stable opens of `X`
preserving intersections, with a descent `Y V` of the restriction of `D` to each `𝒱 V`. -/

variable {D} {J : Type u} [SemilatticeInf J] {𝒱 : InfHom J X.left.Opens}
  {h𝒱 : ∀ V, D.IsStable (𝒱 V)} (Y : J → Over S)
  (g : ∀ V, Hom (baseChange p (Y V)) (D.restrict (𝒱 V) (h𝒱 V))) [∀ V, IsIso (g V).hom]

/-- The piece over `V`, as a morphism of descent data into `D`: an isomorphism onto the
restriction of `D` to `V`. -/
private noncomputable def pieceHom (V : J) : Hom (baseChange p (Y V)) D :=
  (D.restrictHom (𝒱 V) (h𝒱 V)).comp (g V)

omit [∀ V, IsIso (g V).hom] in
private theorem pieceHom_hom_left (V : J) :
    (pieceHom Y g V).hom.left = (g V).hom.left ≫ (𝒱 V).ι := by
  simp only [pieceHom, Hom.comp_hom, Over.comp_left, restrictHom_hom_left]

private instance (V : J) : IsOpenImmersion (pieceHom Y g V).hom.left := by
  have : IsIso (g V).hom.left := (Over.forget S').map_isIso (g V).hom
  rw [pieceHom_hom_left]
  infer_instance

private theorem range_pieceHom (V : J) :
    Set.range (pieceHom Y g V).hom.left = (𝒱 V : Set X.left) := by
  have : IsIso (g V).hom.left := (Over.forget S').map_isIso (g V).hom
  rw [pieceHom_hom_left, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]

/-- The morphism of descent data `Y V ×_S S' ⟶ Y W ×_S S'` factoring the piece over `V` through
the piece over `W`. -/
private noncomputable def transitionBaseChange {V W : J} (h : V ≤ W) :
    Hom (baseChange p (Y V)) (baseChange p (Y W)) :=
  (g W).inv.comp ((pieceHom Y g V).codRestrict (h𝒱 W) (by
    rw [range_pieceHom]
    exact SetLike.coe_subset_coe.mpr (OrderHomClass.mono 𝒱 h)))

private theorem comp_transitionBaseChange {V W : J} (h : V ≤ W) :
    (pieceHom Y g W).comp (transitionBaseChange Y g h) = pieceHom Y g V := by
  rw [pieceHom, transitionBaseChange, Hom.comp_assoc, ← Hom.comp_assoc (g W), Hom.comp_inv_self,
    Hom.id_comp, Hom.restrictHom_comp_codRestrict]

private theorem eq_transitionBaseChange {V W : J} (h : V ≤ W)
    (φ : Hom (baseChange p (Y V)) (baseChange p (Y W)))
    (hφ : (pieceHom Y g W).comp φ = pieceHom Y g V) :
    φ = transitionBaseChange Y g h := by
  refine Hom.ext (Over.OverMorphism.ext ?_)
  rw [← cancel_mono (pieceHom Y g W).hom.left]
  have h₁ := congrArg (fun f ↦ f.hom.left) hφ
  have h₂ := congrArg (fun f ↦ f.hom.left) (comp_transitionBaseChange Y g h)
  simp only [Hom.comp_hom, Over.comp_left] at h₁ h₂
  rw [h₁, h₂]

variable [Surjective p] [Flat p] [QuasiCompact p]

/-- The transition morphism `Y V ⟶ Y W` over `S`, for pieces `V ≤ W`: the descent of
`transitionBaseChange`. -/
private noncomputable def transition {V W : J} (h : V ≤ W) : Y V ⟶ Y W :=
  (transitionBaseChange Y g h).descend

private theorem comp_baseChangeHom_transition {V W : J} (h : V ≤ W) :
    (pieceHom Y g W).comp (baseChangeHom p (transition Y g h)) = pieceHom Y g V := by
  rw [transition, baseChangeHom_descend, comp_transitionBaseChange]

private theorem comp_baseChangeHom_transition_left {V W : J} (h : V ≤ W) :
    (baseChangeHom p (transition Y g h)).hom.left ≫ (pieceHom Y g W).hom.left =
      (pieceHom Y g V).hom.left := by
  simpa only [Hom.comp_hom, Over.comp_left] using
    congrArg (fun f ↦ f.hom.left) (comp_baseChangeHom_transition Y g h)

private theorem eq_transition {V W : J} (h : V ≤ W) (φ : Y V ⟶ Y W)
    (hφ : (pieceHom Y g W).comp (baseChangeHom p φ) = pieceHom Y g V) :
    φ = transition Y g h := by
  rw [transition, ← eq_transitionBaseChange Y g h _ hφ, Hom.descend_baseChangeHom]

private theorem transition_refl (V : J) : transition Y g (le_refl V) = 𝟙 (Y V) :=
  (eq_transition Y g _ _ (by rw [baseChangeHom_id, Hom.comp_id])).symm

private theorem transition_trans {V W Z : J} (hVW : V ≤ W) (hWZ : W ≤ Z) :
    transition Y g hVW ≫ transition Y g hWZ = transition Y g (hVW.trans hWZ) :=
  eq_transition Y g _ _ (by
    rw [baseChangeHom_comp, ← Hom.comp_assoc, comp_baseChangeHom_transition,
      comp_baseChangeHom_transition])

private instance isOpenImmersion_transition {V W : J} (h : V ≤ W) :
    IsOpenImmersion (transition Y g h).left := by
  have : IsOpenImmersion (baseChangeHom p (transition Y g h)).hom.left := by
    have : IsOpenImmersion
        ((baseChangeHom p (transition Y g h)).hom.left ≫ (pieceHom Y g W).hom.left) := by
      rw [comp_baseChangeHom_transition_left]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pieceHom Y g W).hom.left
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_baseChangeHom p (transition Y g h)) ⟨⟨inferInstance, inferInstance⟩,
      inferInstance⟩ this

/-- The base change of the transition morphism `Y V ⟶ Y W` is the part of `Y W ×_S S'` mapping
into `V`. -/
private theorem range_baseChangeHom_transition {V W : J} (h : V ≤ W) :
    Set.range (baseChangeHom p (transition Y g h)).hom.left =
      (pieceHom Y g W).hom.left ⁻¹' 𝒱 V := by
  refine subset_antisymm ?_ fun z hz ↦ ?_
  · rintro _ ⟨z, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, comp_baseChangeHom_transition_left,
      ← range_pieceHom Y g V]
    exact ⟨z, rfl⟩
  rw [Set.mem_preimage, ← range_pieceHom Y g V] at hz
  obtain ⟨z', hz'⟩ := hz
  rw [← comp_baseChangeHom_transition_left Y g h, Scheme.Hom.comp_apply] at hz'
  exact ⟨z', (pieceHom Y g W).hom.left.isOpenEmbedding.injective hz'⟩

/-- A point of `Y W` lies in the image of `Y V` exactly when the points of `Y W ×_S S'` over it
map into `V`. -/
private theorem preimage_range_transition {V W : J} (h : V ≤ W) :
    pullback.fst (Y W).hom p ⁻¹' Set.range (transition Y g h).left =
      (pieceHom Y g W).hom.left ⁻¹' 𝒱 V := by
  have := Scheme.image_preimage_eq_of_isPullback
    (isPullback_baseChangeHom p (transition Y g h)).flip Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at this
  rw [← this, range_baseChangeHom_transition]

private theorem range_transition_inter_subset {V₁ V₂ W : J} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W)
    (h : V₁ ⊓ V₂ ≤ W) :
    Set.range (transition Y g h₁).left ∩ Set.range (transition Y g h₂).left ⊆
      Set.range (transition Y g h).left := by
  rintro y ⟨hy₁, hy₂⟩
  obtain ⟨z, rfl⟩ := (pullback.fst (Y W).hom p).surjective y
  rw [← Set.mem_preimage, preimage_range_transition] at hy₁ hy₂ ⊢
  rw [Set.mem_preimage, map_inf]
  exact ⟨hy₁, hy₂⟩

/-- The pieces as a diagram of schemes over `J`. -/
private noncomputable def gluingFunctor : J ⥤ Scheme.{u} where
  obj V := (Y V).left
  map f := (transition Y g (leOfHom f)).left
  map_id V := congrArg CommaMorphism.left (transition_refl Y g V)
  map_comp f f' := (congrArg CommaMorphism.left
    (transition_trans Y g (leOfHom f) (leOfHom f')).symm)

private theorem gluingFunctor_map {V W : J} (f : V ⟶ W) :
    (gluingFunctor Y g).map f = (transition Y g (leOfHom f)).left :=
  (rfl)

private instance {V W : J} (f : V ⟶ W) : IsOpenImmersion ((gluingFunctor Y g).map f) := by
  rw [gluingFunctor_map]
  exact isOpenImmersion_transition Y g _

private instance : (gluingFunctor Y g ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.IsLocallyDirected.isLocallyDirected_of_range_inter_subset _ fun fi fj ↦ by
    simp only [gluingFunctor_map]
    exact range_transition_inter_subset Y g _ _ _

/-- The structure morphism of the colimit of the pieces, glued from those of the pieces. -/
private noncomputable def toBase : colimit (gluingFunctor Y g) ⟶ S :=
  colimit.desc _
    { pt := S
      ι :=
        { app V := (Y V).hom
          naturality _ _ f := (Over.w (transition Y g (leOfHom f))).trans
            (Category.comp_id _).symm } }

/-- The scheme over `S` glued from the pieces. -/
private noncomputable def glued : Over S :=
  Over.mk (toBase Y g)

/-- The inclusion of a piece into the glued scheme, over `S`. -/
private noncomputable def ιGlued (V : J) : Y V ⟶ glued Y g :=
  Over.homMk (colimit.ι (gluingFunctor Y g) V) (colimit.ι_desc _ _)

/-- The base change of the inclusion of a piece, as a morphism of descent data. -/
private noncomputable abbrev ιGluedBaseChange (V : J) :
    Hom (baseChange p (Y V)) (baseChange p (glued Y g)) :=
  baseChangeHom p (ιGlued Y g V)

/-- The preimage of a piece in `glued ×_S S'` is the base change `Y V ×_S S'` of the piece. -/
private noncomputable def coverComparison (V : J) :
    pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left ⟶
      pullback (Y V).hom p :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.snd _ p) <| by
    rw [← Over.w (ιGlued Y g V), ← Category.assoc, ← pullback.condition, Category.assoc,
      pullback.condition, Category.assoc]

private theorem transition_ιGlued {V W : J} (h : V ≤ W) :
    transition Y g h ≫ ιGlued Y g W = ιGlued Y g V :=
  Over.OverMorphism.ext (colimit.w (gluingFunctor Y g) (homOfLE h))

private instance (V : J) : IsOpenImmersion (ιGlued Y g V).left :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (gluingFunctor Y g) V))

/-- The comparison `coverComparison` is compatible with the transition morphisms: any morphism
`t` between the preimages of two pieces over the identity of `glued ×_S S'` is the base change of
the transition morphism. -/
private theorem comp_coverComparison {V W : J} (h : V ≤ W)
    (t : pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left ⟶
      pullback (pullback.fst (glued Y g).hom p) (ιGlued Y g W).left)
    (ht : t ≫ pullback.fst _ _ = pullback.fst _ _) :
    t ≫ coverComparison Y g W ≫ (pieceHom Y g W).hom.left =
      coverComparison Y g V ≫ (pieceHom Y g V).hom.left := by
  rw [← comp_baseChangeHom_transition_left Y g h, ← Category.assoc, ← Category.assoc]
  congr 1
  -- The second coordinate of `t` is the transition morphism, because the inclusion of the piece
  -- over `W` into the glued scheme is a monomorphism.
  have hsnd : t ≫ pullback.snd _ (ιGlued Y g W).left =
      pullback.snd _ (ιGlued Y g V).left ≫ (transition Y g h).left := by
    rw [← cancel_mono (ιGlued Y g W).left, Category.assoc, ← pullback.condition,
      reassoc_of% ht, pullback.condition, Category.assoc, ← Over.comp_left, transition_ιGlued]
  refine pullback.hom_ext ?_ ?_
  · simp only [coverComparison, Category.assoc, pullback.lift_fst, hsnd,
      (isPullback_baseChangeHom p (transition Y g h)).w, pullback.lift_fst_assoc]
  · simp [coverComparison, reassoc_of% ht]

/-- The open cover of `glued ×_S S'` by the preimages of the pieces. -/
private noncomputable def cover : ((Over.pullback p).obj (glued Y g)).left.OpenCover :=
  (Scheme.IsLocallyDirected.openCover (gluingFunctor Y g)).pullback₁
    (pullback.fst (glued Y g).hom p)

-- Instance search does not unfold `Precoverage.ZeroHypercover.pullback₁` to find Mathlib's
-- instances for the base change of a locally directed cover, so they are supplied by name.
private noncomputable instance : Category (cover Y g).I₀ :=
  Scheme.Cover.instCategoryI₀Pullback₁ (Scheme.IsLocallyDirected.openCover (gluingFunctor Y g)) _

private noncomputable instance : (cover Y g).LocallyDirected :=
  Scheme.Cover.locallyDirectedPullbackCover
    (Scheme.IsLocallyDirected.openCover (gluingFunctor Y g)) _

/-- The members of `cover` are the preimages of the pieces, by definition of the base change of
a cover. -/
private theorem cover_f (V : J) :
    (cover Y g).f V = pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left :=
  (rfl)

private theorem coverComparison_comp_hom (V : J) :
    (coverComparison Y g V ≫ (pieceHom Y g V).hom.left) ≫ X.hom =
      pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left ≫
        pullback.snd (glued Y g).hom p := by
  simp [Over.w (pieceHom Y g V).hom, coverComparison]

/-- The restriction of the comparison morphism to the preimage of a piece. -/
private noncomputable def toXPiece (V : J) : (cover Y g).X V ⟶ X.left :=
  coverComparison Y g V ≫ (pieceHom Y g V).hom.left

private theorem trans_toXPiece {V W : (cover Y g).I₀} (f : V ⟶ W) :
    (cover Y g).trans f ≫ toXPiece Y g W = toXPiece Y g V :=
  comp_coverComparison Y g (leOfHom f) _
    (((congrArg _ (cover_f Y g W)).symm.trans ((cover Y g).trans_map f)).trans
      (cover_f Y g V))

/-- The comparison morphism `glued ×_S S' ⟶ X` over `S'`, glued from the pieces. -/
private noncomputable def toX : (Over.pullback p).obj (glued Y g) ⟶ X :=
  (cover Y g).glueMorphismsOverOfLocallyDirected
    (toXPiece Y g) (trans_toXPiece Y g)
    (fun V ↦ (coverComparison_comp_hom Y g V).trans
      (congrArg (· ≫ pullback.snd (glued Y g).hom p) (cover_f Y g V)).symm)

private theorem f_toX (V : (cover Y g).I₀) :
    (cover Y g).f V ≫ (toX Y g).left = toXPiece Y g V := by
  unfold toX
  exact Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left (cover Y g)
    (toXPiece Y g) _ _ V

private theorem fst_toX (V : J) :
    pullback.fst (pullback.fst (glued Y g).hom p) (ιGlued Y g V).left ≫ (toX Y g).left =
      coverComparison Y g V ≫ (pieceHom Y g V).hom.left :=
  (congrArg (· ≫ (toX Y g).left) (cover_f Y g V)).symm.trans (f_toX Y g V)

/-- On the base change of the piece over `V`, the comparison morphism is the piece itself. -/
@[reassoc]
private theorem ιGluedBaseChange_toX (V : J) :
    (ιGluedBaseChange Y g V).hom.left ≫ (toX Y g).left = (pieceHom Y g V).hom.left := by
  -- The base change of the piece factors through the preimage of the piece in `glued ×_S S'`,
  -- on which `coverComparison` is a retraction of this factorization.
  have hd : pullback.lift (ιGluedBaseChange Y g V).hom.left (pullback.fst _ _)
      (isPullback_baseChangeHom p (ιGlued Y g V)).w ≫ coverComparison Y g V = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_ <;> simp [coverComparison]
  rw [← pullback.lift_fst (ιGluedBaseChange Y g V).hom.left (pullback.fst _ _)
    (isPullback_baseChangeHom p (ιGlued Y g V)).w, Category.assoc, fst_toX, reassoc_of% hd]

private instance (V : J) :
    IsOpenImmersion (ιGluedBaseChange Y g V).hom.left :=
  MorphismProperty.of_isPullback (isPullback_baseChangeHom p (ιGlued Y g V)).flip
    (inferInstanceAs (IsOpenImmersion (ιGlued Y g V).left))

/-- Every point of `glued ×_S S'` lies in the base change of some piece. -/
private theorem exists_mem_range_ιGluedBaseChange (z : ((Over.pullback p).obj (glued Y g)).left) :
    ∃ V : J, z ∈ Set.range (ιGluedBaseChange Y g V).hom.left := by
  obtain ⟨V, y, hy⟩ :=
    Scheme.IsLocallyDirected.ι_jointly_surjective (gluingFunctor Y g) (pullback.fst _ p z)
  have := Scheme.image_preimage_eq_of_isPullback
    (isPullback_baseChangeHom p (ιGlued Y g V)).flip Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at this
  refine ⟨V, ?_⟩
  rw [this]
  exact ⟨y, hy⟩

variable {Y g} in
/-- A point of `glued ×_S S'` lies in the base change of the piece over `V` exactly when the
comparison morphism maps it into `V`. -/
private theorem mem_range_ιGluedBaseChange_iff {V : J}
    {z : ((Over.pullback p).obj (glued Y g)).left} :
    z ∈ Set.range (ιGluedBaseChange Y g V).hom.left ↔ (toX Y g).left z ∈ 𝒱 V := by
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, ιGluedBaseChange_toX, ← SetLike.mem_coe, ← range_pieceHom Y g V]
    exact ⟨z, rfl⟩
  -- The point lies in the base change of some piece `W`, and then in that of `V ⊓ W`.
  obtain ⟨W, z, rfl⟩ := exists_mem_range_ιGluedBaseChange Y g z
  rw [← Scheme.Hom.comp_apply, ιGluedBaseChange_toX] at hz
  have hW : (pieceHom Y g W).hom.left z ∈ 𝒱 W := by
    rw [← SetLike.mem_coe, ← range_pieceHom Y g W]
    exact ⟨z, rfl⟩
  have hz' : z ∈ Set.range (baseChangeHom p (transition Y g (inf_le_right : V ⊓ W ≤ W))).hom.left
    := by
    rw [range_baseChangeHom_transition, Set.mem_preimage, map_inf]
    exact ⟨hz, hW⟩
  obtain ⟨z', rfl⟩ := hz'
  refine ⟨(baseChangeHom p (transition Y g (inf_le_left : V ⊓ W ≤ V))).hom.left z', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
    ← Hom.comp_hom, ← Hom.comp_hom, ← baseChangeHom_comp, ← baseChangeHom_comp, transition_ιGlued,
    transition_ιGlued]

/-- The map of action spaces `S' ×_S (Y V ×_S S') ⟶ S' ×_S (glued ×_S S')` induced by the base
change of the inclusion of a piece. -/
private noncomputable abbrev actionMap (V : J) :
    pullback p (((Over.pullback p).obj (Y V)).hom ≫ p) ⟶
      pullback p (((Over.pullback p).obj (glued Y g)).hom ≫ p) :=
  pullback.map p _ p _ (𝟙 S') (ιGluedBaseChange Y g V).hom.left (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
private theorem actionMap_fst (V : J) :
    actionMap Y g V ≫ pullback.fst p (pullback.snd (glued Y g).hom p ≫ p) =
      pullback.fst p (pullback.snd (Y V).hom p ≫ p) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
private theorem actionMap_snd (V : J) :
    actionMap Y g V ≫ pullback.snd p (pullback.snd (glued Y g).hom p ≫ p) =
      pullback.snd p (pullback.snd (Y V).hom p ≫ p) ≫ (ιGluedBaseChange Y g V).hom.left :=
  pullback.lift_snd _ _ _

private theorem isPullback_actionMap (V : J) :
    IsPullback (actionMap Y g V) (pullback.snd p _) (pullback.snd p _)
      (ιGluedBaseChange Y g V).hom.left :=
  IsPullback.of_right
    (by simpa using IsPullback.of_hasPullback p (((Over.pullback p).obj (Y V)).hom ≫ p))
    (actionMap_snd Y g V) (IsPullback.of_hasPullback p _)

private instance (V : J) : IsOpenImmersion (actionMap Y g V) :=
  MorphismProperty.of_isPullback (isPullback_actionMap Y g V).flip inferInstance

/-- The action spaces of the base changes of the pieces cover the action space of the base change
of the glued scheme. -/
private theorem exists_mem_range_actionMap
    (z : ↥(pullback p (((Over.pullback p).obj (glued Y g)).hom ≫ p))) :
    ∃ V : J, z ∈ Set.range (actionMap Y g V) := by
  obtain ⟨V, hV⟩ := exists_mem_range_ιGluedBaseChange Y g
    (pullback.snd p (((Over.pullback p).obj (glued Y g)).hom ≫ p) z)
  refine ⟨V, ?_⟩
  rw [Scheme.Pullback.range_map]
  exact ⟨⟨_, rfl⟩, hV⟩

/-- The comparison morphism is a morphism of descent data from the canonical descent datum on
`glued ×_S S'` to `D`. -/
private noncomputable def toXHom : Hom (baseChange p (glued Y g)) D where
  hom := toX Y g
  map_act := by
    refine Scheme.hom_ext_of_forall _ _ fun z ↦ ?_
    obtain ⟨V, hV⟩ := exists_mem_range_actionMap Y g z
    refine ⟨(actionMap Y g V).opensRange, hV, ?_⟩
    rw [← cancel_epi (actionMap Y g V).isoOpensRange.hom]
    simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
    have h : actionMap Y g V ≫ pullback.map p _ p (X.hom ≫ p) (𝟙 S') (toX Y g).left (𝟙 S)
        (by simp) (by simp) =
        pullback.map p _ p (X.hom ≫ p) (𝟙 S') (pieceHom Y g V).hom.left (𝟙 S) (by simp)
          (by simp) :=
      pullback.hom_ext (by simp) (by
        simp only [Category.assoc, pullback.map, pullback.lift_snd]
        exact (actionMap_snd_assoc Y g V _).trans
          (congrArg _ (ιGluedBaseChange_toX Y g V)))
    rw [reassoc_of% h, (pieceHom Y g V).map_act, (ιGluedBaseChange Y g V).map_act_assoc,
      ιGluedBaseChange_toX]

private theorem preimage_toX (V : J) :
    (toX Y g).left ⁻¹ᵁ (𝒱 V).ι.opensRange = (ιGluedBaseChange Y g V).hom.left.opensRange := by
  ext z
  rw [Scheme.Opens.opensRange_ι, SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage,
    Scheme.Hom.mem_opensRange, ← Set.mem_range, mem_range_ιGluedBaseChange_iff]

private theorem isIso_toX (hW : ⨆ V, 𝒱 V = ⊤) : IsIso (toX Y g).left := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hW
    fun V ↦ ?_
  have hrange : Set.range (pieceHom Y g V).hom.left = Set.range (𝒱 V).ι := by
    rw [range_pieceHom, Scheme.Opens.range_ι]
  let eV := IsOpenImmersion.isoOfRangeEq (pieceHom Y g V).hom.left (𝒱 V).ι hrange
  have hpb : IsPullback eV.hom (ιGluedBaseChange Y g V).hom.left (𝒱 V).ι (toX Y g).left :=
    IsOpenImmersion.isPullback _ _ _ _
      (by rw [ιGluedBaseChange_toX, IsOpenImmersion.isoOfRangeEq_hom_fac])
      (preimage_toX Y g V)
  let i := hpb.isoIsPullback _ _ (isPullback_morphismRestrict (toX Y g).left _)
  have h : (toX Y g).left ∣_ 𝒱 V = i.inv ≫ eV.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoIsPullback_hom_fst]
  rw [MorphismProperty.isomorphisms.iff, h]
  infer_instance

end Glue

variable {D} in
/-- **Effectivity of descent data is local for stable open covers.** Let `p : S' ⟶ S` be
surjective, flat and quasi-compact, let `D` be a descent datum relative to `p` on `X ⟶ S'`, and
let `U i` be opens of `X`, stable under `D`, which cover `X`. If the restriction of `D` to each
`U i` is effective, then `D` is effective: there are a scheme `Y` over `S` and an isomorphism from
the canonical descent datum on `Y ×_S S'` to `D`. -/
theorem exists_baseChange_hom_isIso_of_iSup_eq_top [Surjective p] [Flat p] [QuasiCompact p]
    {ι : Sort*} (U : ι → X.left.Opens) (hU : ⨆ i, U i = ⊤) (hs : ∀ i, D.IsStable (U i))
    (h : ∀ i, ∃ (Y : Over S) (g : Hom (baseChange p Y) (D.restrict (U i) (hs i))), IsIso g.hom) :
    ∃ (Y : Over S) (g : Hom (baseChange p Y) D), IsIso g.hom := by
  -- The pieces are the stable opens contained in some `U i`, which are closed under intersection.
  let J := {V : X.left.Opens // D.IsStable V ∧ ∃ i, V ≤ U i}
  let : SemilatticeInf J := Subtype.semilatticeInf fun _ _ hV hW ↦
    ⟨hV.1.inf hW.1, hV.2.imp fun _ h ↦ inf_le_left.trans h⟩
  let 𝒱 : InfHom J X.left.Opens := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  have hW : ⨆ V, 𝒱 V = ⊤ :=
    eq_top_iff.mpr (hU.ge.trans (iSup_le fun i ↦ le_iSup_of_le ⟨U i, hs i, i, le_rfl⟩ le_rfl))
  -- Every stable open contained in some `U i` is effective.
  have h' (V : J) :
      ∃ (Y : Over S) (g : Hom (baseChange p Y) (D.restrict (𝒱 V) V.property.1)),
        IsIso g.hom := by
    obtain ⟨i, hi⟩ := V.property.2
    obtain ⟨Y, g, hg⟩ := h i
    obtain ⟨V₀, g', hg'⟩ :=
      D.exists_baseChange_hom_isIso_restrict_of_le (hs i) V.property.1 hi g
    exact ⟨_, g', hg'⟩
  choose Y g hg using h'
  have : IsIso ((Over.forget S').map (toXHom Y g).hom) := isIso_toX Y g hW
  exact ⟨glued Y g, toXHom Y g, isIso_of_reflects_iso _ (Over.forget S')⟩

variable {D} in
/-- **Effectivity of descent data is local on the base.** Let `p : S' ⟶ S` be surjective, flat
and quasi-compact, and let `D` be a descent datum relative to `p` on `X ⟶ S'`. If, for every affine
open `U` of `S`, the restriction of `D` to the preimage of `U` in `X` is effective, then `D` is
effective: there are a scheme `Y` over `S` and an isomorphism from the canonical descent datum on
`Y ×_S S'` to `D`. -/
theorem exists_baseChange_hom_isIso_of_forall_affineOpens [Surjective p] [Flat p]
    [QuasiCompact p]
    (h : ∀ U : S.affineOpens, ∃ (Y : Over S)
      (g : Hom (baseChange p Y) (D.restrict _ (D.isStable_comp_preimage U.val))), IsIso g.hom) :
    ∃ (Y : Over S) (g : Hom (baseChange p Y) D), IsIso g.hom :=
  exists_baseChange_hom_isIso_of_iSup_eq_top (fun U : S.affineOpens ↦ (X.hom ≫ p) ⁻¹ᵁ U.val)
    (by rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top])
    (fun U ↦ D.isStable_comp_preimage U.val) h

variable {D} in
/-- **Effectivity of descent data is local on the base**, in terms of base change. Let
`p : S' ⟶ S` be surjective, flat and quasi-compact, and let `D` be a descent datum relative to `p`
on `X ⟶ S'`. If, for every affine open `U` of `S`, the base change `D.pullbackAlong U.ι` of `D` to
`U`, relative to `U ×_S S' ⟶ U`, is effective, then `D` is effective. -/
theorem exists_baseChange_hom_isIso_of_forall_affineOpens_pullbackAlong [Surjective p] [Flat p]
    [QuasiCompact p]
    (h : ∀ U : S.affineOpens, ∃ (Y₀ : Over U.val.toScheme)
      (f : Hom (baseChange (pullback.fst U.val.ι p) Y₀) (D.pullbackAlong U.val.ι)), IsIso f.hom) :
    ∃ (Y : Over S) (g : Hom (baseChange p Y) D), IsIso g.hom := by
  refine exists_baseChange_hom_isIso_of_forall_affineOpens fun U ↦ ?_
  obtain ⟨Y₀, f, hf⟩ := h U
  obtain ⟨g, hg, -⟩ := f.exists_baseChange_hom_isIso_restrict_of_pullbackAlong
  exact ⟨_, g, hg⟩

end TauCeti.DescentDatum
