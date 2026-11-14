/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Base change between small étale sites and the small étale pseudofunctor

Every morphism of schemes `f : X ⟶ Y` induces a base-change functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` sending an étale `Y`-scheme `V ⟶ Y` to
`V ×_Y X ⟶ X`. On underlying `X`-schemes it agrees with `CategoryTheory.Over.pullback f`, so it
preserves finite limits, is representably flat, preserves jointly surjective étale families and
covering sieves, and is therefore continuous for the small étale topologies on `Y.Etale` and
`X.Etale`.

When `f : X ⟶ Y` is itself étale, post-composition with `f` defines a faithful left adjoint
`f.etaleMap : X.Etale ⥤ Y.Etale` to `f.smallEtaleBaseChange`, which is both continuous and
cocontinuous for the small étale topologies; if `f` is also a monomorphism (for instance an open
immersion), `f.etaleMap` is full as well and the adjunction unit identifies
`f.etaleMap ⋙ f.smallEtaleBaseChange` with `𝟭 X.Etale`. When `X` is empty, `X.Etale` is
equivalent to the terminal category `Discrete PUnit` and `f.smallEtaleBaseChange` is isomorphic to
the constant functor at `𝟙 X`.

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the unit isomorphism
`X.smallEtaleBaseChangeId : (𝟙 X).smallEtaleBaseChange ≅ 𝟭 X.Etale` and composition isomorphism
`f.smallEtaleBaseChangeComp g : (f ≫ g).smallEtaleBaseChange ≅
  g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange` satisfy the coherence laws of a contravariant
pseudofunctor, packaged as
`AlgebraicGeometry.Scheme.smallEtalePseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}`.
Any commutative square `gX ≫ f = f' ≫ g` induces a natural isomorphism
`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq` between iterated base-change functors
(specializing to `f.smallEtaleBaseChangePullback g` on a fibre product), compatible with
identities, symmetry, and pasting of squares.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange`: base change `Y.Etale ⥤ X.Etale` along
  `f : X ⟶ Y`.
* `AlgebraicGeometry.Scheme.Hom.etaleMap` and
  `AlgebraicGeometry.Scheme.Hom.etaleMapBaseChangeAdj`: for an étale morphism `f : X ⟶ Y`,
  post-composition `X.Etale ⥤ Y.Etale` and its adjunction `f.etaleMap ⊣ f.smallEtaleBaseChange`.
* `AlgebraicGeometry.Scheme.etaleEquivOfIsEmpty`: equivalence `X.Etale ≌ Discrete PUnit` when `X`
  is empty.
* `AlgebraicGeometry.Scheme.smallEtaleBaseChangeId`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCongr`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeComp`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleEquivOfIsIso`: identity, congruence, and composition
  isomorphisms for `smallEtaleBaseChange`, and the induced equivalence along an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq` and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangePullback`: base-change comparison isomorphisms
  for a commutative square and for a canonical pullback square.
* `AlgebraicGeometry.Scheme.smallEtalePseudofunctor`: the contravariant pseudofunctor
  `LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}` sending `X` to `X.Etale` and `f.op` to
  `f.smallEtaleBaseChange`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.preservesFiniteLimits_smallEtaleBaseChange` and
  `AlgebraicGeometry.Scheme.Hom.representablyFlat_smallEtaleBaseChange`: `f.smallEtaleBaseChange`
  preserves finite limits and is representably flat.
* `AlgebraicGeometry.Scheme.Hom.isPullback_smallEtaleBaseChange_map` and
  `AlgebraicGeometry.Scheme.Hom.range_smallEtaleBaseChange_map_left`: base change of a `Y.Etale`
  morphism is a scheme pullback square, so its set-theoretic range is the preimage of the original
  range; in particular jointly surjective étale families remain jointly surjective.
* `AlgebraicGeometry.Scheme.Hom.coverPreserving_smallEtaleBaseChange` and
  `AlgebraicGeometry.Scheme.Hom.isContinuous_smallEtaleBaseChange`: `f.smallEtaleBaseChange` is
  cover-preserving and continuous for `smallEtaleTopology`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_associativity`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_id_comp`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_comp_id`: pseudofunctorial coherence of
  `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`.

## References

* The Stacks Project, [Tag 021I](https://stacks.math.columbia.edu/tag/021I) and
  [Tag 021J](https://stacks.math.columbia.edu/tag/021J), the small étale site and functoriality.
-/

@[expose] public section

open CategoryTheory Bicategory Limits MorphismProperty Opposite

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The underlying morphism of the identity in `X.Etale` is the identity on `V.left`. -/
@[simp]
theorem id_left {X : Scheme.{u}} (V : X.Etale) : (𝟙 V : V ⟶ V).left = 𝟙 V.left :=
  rfl

/-- Composition in `X.Etale` composes the underlying morphisms of schemes. -/
@[simp]
theorem comp_left {X : Scheme.{u}} {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).left = f.left ≫ g.left :=
  rfl

/-- Two morphisms in `X.Etale` are equal if their underlying scheme morphisms are equal. -/
@[ext]
theorem hom_ext {X : Scheme.{u}} {U V : X.Etale} {f g : U ⟶ V} (h : f.left = g.left) :
    f = g :=
  MorphismProperty.Over.Hom.ext h

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

section Basic

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
noncomputable def smallEtaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- On underlying schemes over `X`, `f.smallEtaleBaseChange` agrees with
`CategoryTheory.Over.pullback f`. -/
noncomputable def smallEtaleBaseChangeCompForgetIso :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  MorphismProperty.Over.pullbackCompForgetIso f

/-- The underlying scheme of `f.smallEtaleBaseChange.obj V` is `pullback V.hom f`. -/
@[simp]
theorem smallEtaleBaseChange_obj_left (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).left = pullback V.hom f :=
  rfl

/-- The structure morphism of `f.smallEtaleBaseChange.obj V` over `X` is `pullback.snd V.hom f`. -/
@[simp]
theorem smallEtaleBaseChange_obj_hom (V : Y.Etale) :
    dsimp% (f.smallEtaleBaseChange.obj V).hom = pullback.snd V.hom f :=
  rfl

/-- The underlying morphism of `f.smallEtaleBaseChange.map φ` is `pullback.lift` of the composite
first projection with `φ.left` and the second projection. -/
theorem smallEtaleBaseChange_map_left {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% (f.smallEtaleBaseChange.map φ).left =
      pullback.lift (pullback.fst W.hom f ≫ φ.left) (pullback.snd W.hom f)
        (by simp [pullback.condition]) :=
  rfl

/-- Composing `(f.smallEtaleBaseChange.map φ).left` with `pullback.fst` intertwines the first
projections with `φ.left`. -/
@[simp]
theorem smallEtaleBaseChange_map_left_fst {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% (f.smallEtaleBaseChange.map φ).left ≫ pullback.fst V.hom f =
      pullback.fst W.hom f ≫ φ.left := by
  simp [smallEtaleBaseChange_map_left]

/-- Composing `(f.smallEtaleBaseChange.map φ).left` with `pullback.snd` recovers `pullback.snd`. -/
@[simp]
theorem smallEtaleBaseChange_map_left_snd {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% (f.smallEtaleBaseChange.map φ).left ≫ pullback.snd V.hom f = pullback.snd W.hom f := by
  simp [smallEtaleBaseChange_map_left]

/-- For `V : Y.Etale`, the projections from `(f.smallEtaleBaseChange.obj V).left` form a pullback
square over `Y`. -/
theorem isPullback_smallEtaleBaseChange_obj (V : Y.Etale) :
    IsPullback (pullback.fst V.hom f) (f.smallEtaleBaseChange.obj V).hom V.hom f :=
  IsPullback.of_hasPullback V.hom f

/-- For any morphism `φ : W ⟶ V` in `Y.Etale`, `(f.smallEtaleBaseChange.map φ).left` fits into a
pullback square with `φ.left` along the first projections to `W.left` and `V.left`. -/
theorem isPullback_smallEtaleBaseChange_map {W V : Y.Etale} (φ : W ⟶ V) :
    IsPullback (f.smallEtaleBaseChange.map φ).left (pullback.fst W.hom f)
      (pullback.fst V.hom f) φ.left := by
  refine IsPullback.of_right ?_ (f.smallEtaleBaseChange_map_left_fst φ)
    (IsPullback.of_hasPullback V.hom f).flip
  simpa [MorphismProperty.Over.w φ] using (IsPullback.of_hasPullback W.hom f).flip

/-- The set-theoretic range of `(f.smallEtaleBaseChange.map φ).left` is the preimage of the range
of `φ.left` under `pullback.fst V.hom f`. -/
@[simp]
theorem range_smallEtaleBaseChange_map_left {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% Set.range (f.smallEtaleBaseChange.map φ).left =
      pullback.fst V.hom f ⁻¹' Set.range φ.left := by
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨pullback.fst W.hom f q, ((Scheme.Hom.comp_apply _ _ q).symm.trans
      (congr($(f.smallEtaleBaseChange_map_left_fst φ) q)).symm).trans
      (Scheme.Hom.comp_apply _ _ q)⟩
  · rintro ⟨w, hw⟩
    -- Lift `(p, w)` into the fibre product of `(f.smallEtaleBaseChange.obj V).left` and `W.left`
    -- over `V.left`, which is isomorphic to `(f.smallEtaleBaseChange.obj W).left`.
    have hpb := f.isPullback_smallEtaleBaseChange_map φ
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst V.hom f) (g := φ.left) p w hw.symm
    have hinv : hpb.isoPullback.inv ≫ (f.smallEtaleBaseChange.map φ).left =
        pullback.fst (pullback.fst V.hom f) φ.left :=
      hpb.isoPullback.inv_comp_eq.mpr hpb.isoPullback_hom_fst.symm
    exact ⟨hpb.isoPullback.inv z, (Scheme.Hom.comp_apply _ _ z).symm.trans
      ((congr($hinv z)).trans hz₁)⟩

/-- Base change along `f` commutes with set-theoretic unions of ranges of étale `Y`-morphisms. -/
theorem iUnion_range_smallEtaleBaseChange_map_left {V : Y.Etale} {ι : Type*} {Z : ι → Y.Etale}
    (g : ∀ i, Z i ⟶ V) :
    (⋃ i, Set.range (f.smallEtaleBaseChange.map (g i)).left) =
      pullback.fst V.hom f ⁻¹' (⋃ i, Set.range (g i).left) :=
  (Set.iUnion_congr fun i ↦ f.range_smallEtaleBaseChange_map_left (g i)).trans
    Set.preimage_iUnion.symm

/-- Base change along `f` preserves jointly surjective families in `Y.Etale`. -/
theorem iUnion_range_smallEtaleBaseChange_map_left_of_eq_univ {V : Y.Etale} {ι : Type*}
    {Z : ι → Y.Etale} (g : ∀ i, Z i ⟶ V) (hg : ⋃ i, Set.range (g i).left = Set.univ) :
    ⋃ i, Set.range (f.smallEtaleBaseChange.map (g i)).left = Set.univ :=
  (f.iUnion_range_smallEtaleBaseChange_map_left g).trans
    ((congrArg (pullback.fst V.hom f ⁻¹' ·) hg).trans Set.preimage_univ)

/-- `f.smallEtaleBaseChange` preserves finite limits, since `Etale.forget X` is fully faithful and
preserves (hence reflects) finite limits while `CategoryTheory.Over.pullback f` is a right
adjoint. -/
noncomputable instance preservesFiniteLimits_smallEtaleBaseChange :
    PreservesFiniteLimits f.smallEtaleBaseChange := by
  constructor
  intro J _ _
  have : PreservesLimitsOfShape J (f.smallEtaleBaseChange ⋙ Etale.forget X) :=
    preservesLimitsOfShape_of_natIso f.smallEtaleBaseChangeCompForgetIso.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves f.smallEtaleBaseChange (Etale.forget X)

/-- `f.smallEtaleBaseChange` is representably flat, as `Y.Etale` has finite limits and
`f.smallEtaleBaseChange` preserves them. -/
instance representablyFlat_smallEtaleBaseChange : RepresentablyFlat f.smallEtaleBaseChange :=
  flat_of_preservesFiniteLimits f.smallEtaleBaseChange

/-- `f.smallEtaleBaseChange` sends covering sieves of `Y.smallEtaleTopology` to covering sieves of
`X.smallEtaleTopology`. -/
theorem coverPreserving_smallEtaleBaseChange :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology f.smallEtaleBaseChange where
  cover_preserve {U S} hS := by
    obtain ⟨ι, Z, g, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
    exact f.iUnion_range_smallEtaleBaseChange_map_left_of_eq_univ g
      ((ofArrows_mem_smallEtaleTopology_iff g).mp hS)

/-- `f.smallEtaleBaseChange` is continuous for the small étale topologies on `Y.Etale` and
`X.Etale`, so precomposition with `f.smallEtaleBaseChange` pushes étale sheaves on `X` forward to
étale sheaves on `Y`. -/
instance isContinuous_smallEtaleBaseChange :
    f.smallEtaleBaseChange.IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact f.coverPreserving_smallEtaleBaseChange

end Basic

/-! ### Left adjoint along an étale morphism and open-immersion specialization -/

section EtaleMorphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- When `f : X ⟶ Y` is étale, post-composition with `f` sends schemes étale over `X` to schemes
étale over `Y`. -/
def etaleMap : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ ‹Etale f›

/-- On underlying schemes over `Y`, `f.etaleMap` agrees with `CategoryTheory.Over.map f`. -/
def etaleMapCompForgetIso :
    f.etaleMap ⋙ Etale.forget Y ≅ Etale.forget X ⋙ CategoryTheory.Over.map f :=
  Iso.refl _

/-- `f.etaleMap` leaves the underlying scheme unchanged. -/
@[simp]
theorem etaleMap_obj_left (W : X.Etale) : (f.etaleMap.obj W).left = W.left :=
  rfl

/-- `f.etaleMap` composes the structure morphism with `f`. -/
@[simp]
theorem etaleMap_obj_hom (W : X.Etale) : dsimp% (f.etaleMap.obj W).hom = W.hom ≫ f :=
  rfl

/-- `f.etaleMap` leaves underlying scheme morphisms unchanged. -/
@[simp]
theorem etaleMap_map_left {W₁ W₂ : X.Etale} (φ : W₁ ⟶ W₂) :
    (f.etaleMap.map φ).left = φ.left :=
  rfl

/-- For an étale morphism `f : X ⟶ Y`, post-composition `f.etaleMap` is left adjoint to base change
`f.smallEtaleBaseChange`. -/
noncomputable def etaleMapBaseChangeAdj : f.etaleMap ⊣ f.smallEtaleBaseChange :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f ‹Etale f› trivial

/-- The counit of `f.etaleMapBaseChangeAdj` at `V : Y.Etale` has underlying morphism
`pullback.fst V.hom f`. -/
@[simp]
theorem etaleMapBaseChangeAdj_counit_app_left (V : Y.Etale) :
    dsimp% (f.etaleMapBaseChangeAdj.counit.app V).left = pullback.fst V.hom f :=
  rfl

/-- Composing the unit of `f.etaleMapBaseChangeAdj` at `W : X.Etale` with `pullback.fst` is the
identity on `W.left`. -/
@[simp]
theorem etaleMapBaseChangeAdj_unit_app_left_fst (W : X.Etale) :
    dsimp% (f.etaleMapBaseChangeAdj.unit.app W).left ≫ pullback.fst (W.hom ≫ f) f = 𝟙 W.left :=
  pullback.lift_fst _ _ _

/-- Composing the unit of `f.etaleMapBaseChangeAdj` at `W : X.Etale` with `pullback.snd` is
`W.hom`. -/
@[simp]
theorem etaleMapBaseChangeAdj_unit_app_left_snd (W : X.Etale) :
    dsimp% (f.etaleMapBaseChangeAdj.unit.app W).left ≫ pullback.snd (W.hom ≫ f) f = W.hom :=
  pullback.lift_snd _ _ _

/-- `f.etaleMap` is a left adjoint when `f` is étale. -/
instance isLeftAdjoint_etaleMap : f.etaleMap.IsLeftAdjoint :=
  f.etaleMapBaseChangeAdj.isLeftAdjoint

/-- `f.smallEtaleBaseChange` is a right adjoint when `f` is étale. -/
instance isRightAdjoint_smallEtaleBaseChange_of_etale : f.smallEtaleBaseChange.IsRightAdjoint :=
  f.etaleMapBaseChangeAdj.isRightAdjoint

/-- For an étale morphism `f : X ⟶ Y`, `f.etaleMap` preserves covering sieves of the small étale
topology. -/
theorem coverPreserving_etaleMap :
    CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology f.etaleMap where
  cover_preserve {U S} hS := by
    obtain ⟨ι, Z, g, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
    exact (ofArrows_mem_smallEtaleTopology_iff g).mp hS

/-- For an étale morphism `f : X ⟶ Y`, `f.etaleMap` is cocontinuous for the small étale topologies,
since its right adjoint `f.smallEtaleBaseChange` is cover-preserving. -/
instance isCocontinuous_etaleMap :
    f.etaleMap.IsCocontinuous X.smallEtaleTopology Y.smallEtaleTopology :=
  (Adjunction.isCocontinuous_iff_coverPreserving X.smallEtaleTopology Y.smallEtaleTopology
    f.etaleMapBaseChangeAdj).mpr f.coverPreserving_smallEtaleBaseChange

/-- For an étale morphism `f : X ⟶ Y`, `f.etaleMap` preserves compatible families for
`Y.smallEtaleTopology`. -/
theorem compatiblePreserving_etaleMap :
    CompatiblePreserving Y.smallEtaleTopology f.etaleMap where
  compatible {F Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    -- Any `Y`-scheme `W` étale over `Y` mapping to `f.etaleMap.obj Y₁` lifts to `X.Etale` via
    -- `f₁.left ≫ Y₁.hom`, because `f₁.left` and `Y₁.hom` are both étale.
    let φ₁ : W.left ⟶ Y₁.left := f₁.left
    let φ₂ : W.left ⟶ Y₂.left := f₂.left
    have : Etale φ₁ := inferInstanceAs (Etale f₁.left)
    have : Etale (Y₁.hom : Y₁.left ⟶ X) := Y₁.prop
    have hleft : φ₂ ≫ (g₂.left : Y₂.left ⟶ Z.left) = φ₁ ≫ (g₁.left : Y₁.left ⟶ Z.left) :=
      (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h.symm
    have hw₂ : φ₂ ≫ (Y₂.hom : Y₂.left ⟶ X) = φ₁ ≫ (Y₁.hom : Y₁.left ⟶ X) :=
      (congrArg (φ₂ ≫ ·) (MorphismProperty.Over.w g₂).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (Z.hom : Z.left ⟶ X)) hleft).trans
            ((Category.assoc _ _ _).trans (congrArg (φ₁ ≫ ·) (MorphismProperty.Over.w g₁)))))
    let W' : X.Etale := Etale.mk (φ₁ ≫ (Y₁.hom : Y₁.left ⟶ X))
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk φ₁
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk φ₂ hw₂
    let e : f.etaleMap.obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl W.left)
      ((Category.id_comp (W.hom : W.left ⟶ Y)).trans
        ((MorphismProperty.Over.w f₁).symm.trans (Category.assoc _ _ _).symm))
    have he₁ : f₁ = e.inv ≫ f.etaleMap.map g₁' := by
      ext1; exact (Category.id_comp φ₁).symm
    have he₂ : f₂ = e.inv ≫ f.etaleMap.map g₂' := by
      ext1; exact (Category.id_comp φ₂).symm
    have hcompat := congrArg (F.obj.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂
        (by ext1; exact (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h))
    simpa only [Functor.comp_map, Functor.op_map, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Quiver.Hom.unop_op, ← he₁, ← he₂] using hcompat

/-- For an étale morphism `f : X ⟶ Y`, `f.etaleMap` is continuous for the small étale topologies,
so precomposition with `f.etaleMap` restricts étale sheaves on `Y` to `X`. -/
instance isContinuous_etaleMap :
    f.etaleMap.IsContinuous X.smallEtaleTopology Y.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving f.compatiblePreserving_etaleMap f.coverPreserving_etaleMap

/-- For any étale morphism `f : X ⟶ Y`, `f.etaleMap` is faithful. -/
instance faithful_etaleMap : f.etaleMap.Faithful where
  map_injective h := by
    ext1
    exact (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h

/-- When `f : X ⟶ Y` is an étale monomorphism (for instance an open immersion), `f.etaleMap` is
full: any `Y`-morphism between `X`-schemes automatically commutes over `X`. -/
instance full_etaleMap [Mono f] : f.etaleMap.Full where
  map_surjective {W₁ W₂} φ :=
    ⟨MorphismProperty.Over.homMk (φ.left : W₁.left ⟶ W₂.left)
      ((cancel_mono f).mp ((Category.assoc _ _ _).trans (MorphismProperty.Over.w φ))),
      by ext1; rfl⟩

/-- When `f : X ⟶ Y` is an étale monomorphism (such as an open immersion `j : U ⟶ Y`), restricting
`f.etaleMap.obj W` back along `f` canonically recovers `W`: the unit of `f.etaleMapBaseChangeAdj`
is an isomorphism. -/
instance isIso_etaleMapBaseChangeAdj_unit [Mono f] : IsIso f.etaleMapBaseChangeAdj.unit :=
  f.etaleMapBaseChangeAdj.unit_isIso_of_L_fully_faithful

/-- For an étale monomorphism `f : X ⟶ Y` (in particular any open immersion `j : U ⟶ Y`), viewing
an étale `X`-scheme over `Y` and pulling back along `f` is naturally isomorphic to the identity
functor on `X.Etale`. -/
noncomputable def etaleMapCompSmallEtaleBaseChangeIso [Mono f] :
    f.etaleMap ⋙ f.smallEtaleBaseChange ≅ 𝟭 X.Etale :=
  (asIso f.etaleMapBaseChangeAdj.unit).symm

end EtaleMorphism

end AlgebraicGeometry.Scheme.Hom

/-! ### Empty-scheme specialization -/

namespace AlgebraicGeometry.Scheme

section IsEmpty

/-- Every scheme étale over an empty scheme is itself empty. -/
instance isEmpty_etale_left {X : Scheme.{u}} [IsEmpty X] (W : X.Etale) : IsEmpty W.left :=
  Function.isEmpty (β := X) W.hom

/-- Between any two schemes étale over an empty scheme `X`, there is a unique `X`-morphism. -/
noncomputable instance uniqueEtaleHomOfIsEmpty {X : Scheme.{u}} [IsEmpty X] (W₁ W₂ : X.Etale) :
    Unique (W₁ ⟶ W₂) where
  default := MorphismProperty.Over.homMk (isInitialOfIsEmpty.to W₂.left)
    (isInitialOfIsEmpty.hom_ext _ _)
  uniq φ := by
    ext1
    exact isInitialOfIsEmpty.hom_ext _ _

/-- When `X` is an empty scheme, `X.Etale` is equivalent to the terminal category
`Discrete PUnit`. -/
noncomputable def etaleEquivOfIsEmpty (X : Scheme.{u}) [IsEmpty X] :
    X.Etale ≌ Discrete PUnit.{1} where
  functor := (Functor.const _).obj ⟨⟨⟩⟩
  inverse := (Functor.const _).obj (Etale.mk (𝟙 X))
  unitIso := NatIso.ofComponents (fun _ ↦ { hom := default, inv := default })
  counitIso := Iso.refl _

/-- Base change along `f : X ⟶ Y` into an empty scheme `X` is naturally isomorphic to the constant
functor at `Etale.mk (𝟙 X)`. -/
noncomputable def Hom.smallEtaleBaseChangeIsoConstOfIsEmpty {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsEmpty X] :
    f.smallEtaleBaseChange ≅ (Functor.const Y.Etale).obj (Etale.mk (𝟙 X)) :=
  NatIso.ofComponents (fun _ ↦ { hom := default, inv := default })

end IsEmpty

/-! ### Identity, congruence, composition, and square comparisons -/

section PullbackHelpers

/-- Underlying scheme morphism of `f.smallEtaleBaseChange.map` on morphisms over `Y`. -/
private noncomputable def pullbackBaseChangeMap {A₁ A₂ X Y : Scheme.{u}} (v₁ : A₁ ⟶ Y)
    (v₂ : A₂ ⟶ Y) (f : X ⟶ Y) (φ : A₁ ⟶ A₂) (hφ : φ ≫ v₂ = v₁) :
    pullback v₁ f ⟶ pullback v₂ f :=
  pullback.lift (pullback.fst v₁ f ≫ φ) (pullback.snd v₁ f)
    (by rw [Category.assoc, hφ, pullback.condition])

/-- Underlying scheme isomorphism of `X.smallEtaleBaseChangeId.app`. -/
private noncomputable def pullbackIdIso {A X : Scheme.{u}} (v : A ⟶ X) :
    pullback v (𝟙 X) ≅ A where
  hom := pullback.fst v (𝟙 X)
  inv := pullback.lift (𝟙 A) v (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · simpa using (pullback.condition (f := v) (g := 𝟙 X)).trans (Category.comp_id _)
  inv_hom_id := by simp

/-- Underlying scheme isomorphism of `(f.smallEtaleBaseChangeComp g).app`. -/
private noncomputable def pullbackCompIso {A X Y Z : Scheme.{u}} (v : A ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback v (f ≫ g) ≅ pullback (pullback.snd v g) f :=
  pullback.congrHom rfl rfl ≪≫ (pullbackLeftPullbackSndIso v g f).symm

/-- Underlying scheme isomorphism of `(f.smallEtaleBaseChangeComp' g fg hfg).app`. -/
private noncomputable def pullbackComp'Iso {A X Y Z : Scheme.{u}} (v : A ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    pullback v fg ≅ pullback (pullback.snd v g) f :=
  pullback.congrHom rfl hfg.symm ≪≫ pullbackCompIso v f g

/-- Underlying scheme isomorphism of `(smallEtaleBaseChangeCommSq w).app`. -/
private noncomputable def pullbackCommSqIso {A X' X Y' Y : Scheme.{u}} (v : A ⟶ Y)
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    pullback (pullback.snd v f) gX ≅ pullback (pullback.snd v g) f' :=
  (pullbackCompIso v gX f).symm ≪≫ pullback.congrHom rfl w ≪≫ pullbackCompIso v f' g

/-- Two morphisms into an iterated fibre product `pullback (pullback.snd v g) f` are equal as soon
as they agree after composing with `pullback.fst _ f ≫ pullback.fst v g` and with
`pullback.snd _ f`. -/
private theorem pullback_snd_hom_ext {W A X Y Z : Scheme.{u}} {v : A ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    {u₁ u₂ : W ⟶ pullback (pullback.snd v g) f}
    (hfst : u₁ ≫ pullback.fst (pullback.snd v g) f ≫ pullback.fst v g =
      u₂ ≫ pullback.fst (pullback.snd v g) f ≫ pullback.fst v g)
    (hsnd : u₁ ≫ pullback.snd (pullback.snd v g) f =
      u₂ ≫ pullback.snd (pullback.snd v g) f) :
    u₁ = u₂ := by
  have aux (u : W ⟶ pullback (pullback.snd v g) f) :
      (u ≫ pullback.fst (pullback.snd v g) f) ≫ pullback.snd v g =
        (u ≫ pullback.snd (pullback.snd v g) f) ≫ f := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) hsnd
  · simpa only [Category.assoc] using hfst
  · rw [aux u₁, aux u₂, hsnd]

/-- Two morphisms into a twice-iterated fibre product
`pullback (pullback.snd (pullback.snd v h) g) f` are equal as soon as they agree after composing
with the three first projections to `A` and with the outer second projection to `W`. -/
private theorem pullback_snd_snd_hom_ext {U A W X Y Z : Scheme.{u}} {v : A ⟶ Z}
    {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {u₁ u₂ : U ⟶ pullback (pullback.snd (pullback.snd v h) g) f}
    (hfst : u₁ ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f ≫
        pullback.fst (pullback.snd v h) g ≫ pullback.fst v h =
      u₂ ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f ≫
        pullback.fst (pullback.snd v h) g ≫ pullback.fst v h)
    (hsnd : u₁ ≫ pullback.snd (pullback.snd (pullback.snd v h) g) f =
      u₂ ≫ pullback.snd (pullback.snd (pullback.snd v h) g) f) :
    u₁ = u₂ := by
  have aux (u : U ⟶ pullback (pullback.snd (pullback.snd v h) g) f) :
      (u ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f ≫
          pullback.fst (pullback.snd v h) g) ≫ pullback.snd v h =
        (u ≫ pullback.snd (pullback.snd (pullback.snd v h) g) f) ≫ f ≫ g := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, Category.assoc,
      pullback.condition_assoc, ← Category.assoc]
  refine pullback_snd_hom_ext (pullback.hom_ext ?_ ?_) hsnd
  · simpa only [Category.assoc] using hfst
  · rw [aux u₁, aux u₂, hsnd]

end PullbackHelpers

/-- Base change along `𝟙 X` is naturally isomorphic to the identity functor on `X.Etale`, with
forward component at `V : X.Etale` given by the first projection `V ×_X X ⟶ V`. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    Hom.smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk
      { hom := pullback.fst V.hom (𝟙 X)
        inv := pullback.lift (𝟙 V.left) V.hom (by simp)
        hom_inv_id := by
          apply pullback.hom_ext
          · simp
          · simpa using (pullback.condition (f := V.hom) (g := 𝟙 X)).trans (Category.comp_id _)
        inv_hom_id := by simp }
      (by simp [pullback.condition]))
    (fun φ ↦ Etale.hom_ext (Hom.smallEtaleBaseChange_map_left_fst (𝟙 X) φ))

/-- On underlying schemes, the forward component of `X.smallEtaleBaseChangeId` at `V` is the first
projection `pullback.fst V.hom (𝟙 X)`. -/
@[simp]
theorem smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (V : X.Etale) :
    dsimp% ((X.smallEtaleBaseChangeId).hom.app V).left = pullback.fst V.hom (𝟙 X) :=
  rfl

/-- Composing the inverse component of `X.smallEtaleBaseChangeId` at `V` with `pullback.fst` gives
`𝟙 V.left`. -/
@[simp]
theorem smallEtaleBaseChangeId_inv_app_left_fst (X : Scheme.{u}) (V : X.Etale) :
    dsimp% ((X.smallEtaleBaseChangeId).inv.app V).left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left :=
  pullback.lift_fst _ _ _

/-- Composing the inverse component of `X.smallEtaleBaseChangeId` at `V` with `pullback.snd` gives
`V.hom`. -/
@[simp]
theorem smallEtaleBaseChangeId_inv_app_left_snd (X : Scheme.{u}) (V : X.Etale) :
    dsimp% ((X.smallEtaleBaseChangeId).inv.app V).left ≫ pullback.snd V.hom (𝟙 X) = V.hom :=
  pullback.lift_snd _ _ _

namespace Hom

/-- Equal morphisms `f = f'` induce naturally isomorphic base-change functors on small étale
sites. -/
noncomputable def smallEtaleBaseChangeCongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') :
    f.smallEtaleBaseChange ≅ f'.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr h

/-- `smallEtaleBaseChangeCongr` at `rfl` is the identity natural isomorphism. -/
@[simp]
theorem smallEtaleBaseChangeCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleBaseChangeCongr (rfl : f = f) = Iso.refl f.smallEtaleBaseChange := by
  ext V : 3
  ext1
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullback.congrHom (f₁ := v) (g₁ := f) rfl rfl).hom = 𝟙 (pullback v f) := by
    intro A v
    simp
  exact key V.hom

/-- Composing the forward component of `smallEtaleBaseChangeCongr h` with `pullback.fst` recovers
`pullback.fst`. -/
@[simp]
theorem smallEtaleBaseChangeCongr_hom_app_left_fst {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ pullback.fst V.hom f' =
      pullback.fst V.hom f :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h V

/-- Composing the forward component of `smallEtaleBaseChangeCongr h` with `pullback.snd` recovers
`pullback.snd`. -/
@[simp]
theorem smallEtaleBaseChangeCongr_hom_app_left_snd {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ pullback.snd V.hom f' =
      pullback.snd V.hom f := by
  subst h
  simp

/-- Composing the inverse component of `smallEtaleBaseChangeCongr h` with `pullback.fst` recovers
`pullback.fst`. -/
@[simp]
theorem smallEtaleBaseChangeCongr_inv_app_left_fst {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ pullback.fst V.hom f =
      pullback.fst V.hom f' := by
  subst h
  simp

/-- Composing the inverse component of `smallEtaleBaseChangeCongr h` with `pullback.snd` recovers
`pullback.snd`. -/
@[simp]
theorem smallEtaleBaseChangeCongr_inv_app_left_snd {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ pullback.snd V.hom f =
      pullback.snd V.hom f' := by
  subst h
  simp

/-- `smallEtaleBaseChangeCongr` commutes with symmetry of equalities. -/
theorem smallEtaleBaseChangeCongr_symm {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') :
    smallEtaleBaseChangeCongr h.symm = (smallEtaleBaseChangeCongr h).symm := by
  subst h
  simp

/-- `smallEtaleBaseChangeCongr` sends transitivity of equalities to composition of natural
isomorphisms. -/
theorem smallEtaleBaseChangeCongr_trans {X Y : Scheme.{u}} {f₁ f₂ f₃ : X ⟶ Y}
    (h₁ : f₁ = f₂) (h₂ : f₂ = f₃) :
    smallEtaleBaseChangeCongr (h₁.trans h₂) =
      smallEtaleBaseChangeCongr h₁ ≪≫ smallEtaleBaseChangeCongr h₂ := by
  subst h₁ h₂
  simp

/-- Base change along a composite `f ≫ g` (`X ⟶ Y ⟶ Z`) is naturally isomorphic to base change
along `g` followed by base change along `f`, via fibre-product pasting
`V ×_Z X ≅ (V ×_Z Y) ×_Y X`. -/
noncomputable def smallEtaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleBaseChange (f ≫ g) ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp f g

/-- Composing the forward component of `f.smallEtaleBaseChangeComp g` at `V : Z.Etale` with the two
first projections recovers `pullback.fst V.hom (f ≫ g)`. -/
@[simp]
theorem smallEtaleBaseChangeComp_hom_app_left_fst_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst f g V

/-- Composing the forward component of `f.smallEtaleBaseChangeComp g` at `V : Z.Etale` with the
outer second projection recovers `pullback.snd V.hom (f ≫ g)`. -/
@[simp]
theorem smallEtaleBaseChangeComp_hom_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g).hom.app V).left ≫ pullback.snd (pullback.snd V.hom g) f =
      pullback.snd V.hom (f ≫ g) := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Z),
      (pullbackCompIso v f g).hom ≫ pullback.snd (pullback.snd v g) f = pullback.snd v (f ≫ g) := by
    intro A v
    simp [pullbackCompIso]
  exact key V.hom

/-- Composing the inverse component of `f.smallEtaleBaseChangeComp g` at `V : Z.Etale` with
`pullback.fst V.hom (f ≫ g)` gives the composite of the two first projections. -/
@[simp]
theorem smallEtaleBaseChangeComp_inv_app_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g).inv.app V).left ≫ pullback.fst V.hom (f ≫ g) =
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Z),
      (pullbackCompIso v f g).inv ≫ pullback.fst v (f ≫ g) =
        pullback.fst (pullback.snd v g) f ≫ pullback.fst v g := by
    intro A v
    simp [pullbackCompIso]
  exact key V.hom

/-- Composing the inverse component of `f.smallEtaleBaseChangeComp g` at `V : Z.Etale` with
`pullback.snd V.hom (f ≫ g)` gives `pullback.snd (pullback.snd V.hom g) f`. -/
@[simp]
theorem smallEtaleBaseChangeComp_inv_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g).inv.app V).left ≫ pullback.snd V.hom (f ≫ g) =
      pullback.snd (pullback.snd V.hom g) f := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Z),
      (pullbackCompIso v f g).inv ≫ pullback.snd v (f ≫ g) =
        pullback.snd (pullback.snd v g) f := by
    intro A v
    simp [pullbackCompIso]
  exact key V.hom

/-- Flexible composition comparison `fg.smallEtaleBaseChange ≅
  g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange` along an arbitrary factorization
`f ≫ g = fg`. -/
noncomputable def smallEtaleBaseChangeComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    fg.smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  smallEtaleBaseChangeCongr hfg.symm ≪≫ f.smallEtaleBaseChangeComp g

/-- At the syntactic composite `f ≫ g`, `smallEtaleBaseChangeComp'` agrees with
`smallEtaleBaseChangeComp`. -/
@[simp]
theorem smallEtaleBaseChangeComp'_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.smallEtaleBaseChangeComp' g (f ≫ g) rfl = f.smallEtaleBaseChangeComp g := by
  simp [smallEtaleBaseChangeComp']

/-- Composing the forward component of `f.smallEtaleBaseChangeComp' g fg hfg` at `V : Z.Etale` with
the two first projections recovers `pullback.fst V.hom fg`. -/
@[simp]
theorem smallEtaleBaseChangeComp'_hom_app_left_fst_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp' g fg hfg).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom fg := by
  subst hfg
  simp

/-- Composing the forward component of `f.smallEtaleBaseChangeComp' g fg hfg` at `V : Z.Etale` with
the outer second projection recovers `pullback.snd V.hom fg`. -/
@[simp]
theorem smallEtaleBaseChangeComp'_hom_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp' g fg hfg).hom.app V).left ≫
        pullback.snd (pullback.snd V.hom g) f =
      pullback.snd V.hom fg := by
  subst hfg
  simp

/-- Base change along an isomorphism `f : X ⟶ Y` is an equivalence `Y.Etale ≌ X.Etale`, with
quasi-inverse `(inv f).smallEtaleBaseChange`. -/
noncomputable def smallEtaleEquivOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Y.Etale ≌ X.Etale :=
  CategoryTheory.Equivalence.mk f.smallEtaleBaseChange (inv f).smallEtaleBaseChange
    ((Y.smallEtaleBaseChangeId).symm ≪≫
      (inv f).smallEtaleBaseChangeComp' f (𝟙 Y) (IsIso.inv_hom_id f))
    ((f.smallEtaleBaseChangeComp' (inv f) (𝟙 X) (IsIso.hom_inv_id f)).symm ≪≫
      X.smallEtaleBaseChangeId)

/-- Base change along an isomorphism `f : X ⟶ Y` is an equivalence of categories. -/
noncomputable instance isEquivalence_smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : f.smallEtaleBaseChange.IsEquivalence :=
  f.smallEtaleEquivOfIsIso.isEquivalence_functor

/-! ### Pseudofunctorial coherence laws -/

/-- Componentwise associativity of `smallEtaleBaseChangeComp'` across any composable triple
`W --f--> X --g--> Y --h--> Z` and arbitrary factorizations. -/
@[reassoc]
theorem smallEtaleBaseChangeComp'_associativity {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh)
    (V : Z.Etale) :
    (f.smallEtaleBaseChangeComp' gh fgh hfgh').hom.app V ≫
        f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp' h gh hgh).hom.app V) =
      (fg.smallEtaleBaseChangeComp' h fgh hfgh).hom.app V ≫
        (f.smallEtaleBaseChangeComp' g fg hfg).hom.app (h.smallEtaleBaseChange.obj V) := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Z),
      (pullbackComp'Iso v f gh fgh hfgh').hom ≫
        pullbackBaseChangeMap (pullback.snd v gh) (pullback.snd (pullback.snd v h) g) f
          (pullbackComp'Iso v g h gh hgh).hom
          (by subst hgh; simp [pullbackComp'Iso, pullbackCompIso]) =
      (pullbackComp'Iso v fg h fgh hfgh).hom ≫
        (pullbackComp'Iso (pullback.snd v h) f g fg hfg).hom := by
    intro A v
    subst hfg hgh hfgh
    refine pullback_snd_snd_hom_ext ?_ ?_ <;>
      simp [pullbackComp'Iso, pullbackCompIso, pullbackBaseChangeMap]
  exact Etale.hom_ext (key V.hom)

/-- Associativity pentagon for `smallEtaleBaseChangeComp` across `W --f--> X --g--> Y --h--> Z`. -/
@[reassoc]
theorem smallEtaleBaseChange_associativity {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (V : Z.Etale) :
    (smallEtaleBaseChangeCongr (Category.assoc f g h)).hom.app V ≫
        (f.smallEtaleBaseChangeComp (g ≫ h)).hom.app V ≫
        f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp h).hom.app V) =
      (smallEtaleBaseChangeComp (f ≫ g) h).hom.app V ≫
        (f.smallEtaleBaseChangeComp g).hom.app (h.smallEtaleBaseChange.obj V) := by
  simpa [smallEtaleBaseChangeComp'] using
    smallEtaleBaseChangeComp'_associativity f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h)
      rfl rfl rfl (Category.assoc f g h).symm V

/-- Right-unit coherence for `smallEtaleBaseChangeComp'` along `f ≫ 𝟙 Y = f`. -/
@[reassoc]
theorem smallEtaleBaseChangeComp'_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : f ≫ 𝟙 Y = f)
    (V : Y.Etale) :
    (f.smallEtaleBaseChangeComp' (𝟙 Y) f hf).hom.app V ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).hom.app V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackComp'Iso v f (𝟙 Y) f hf).hom ≫
        pullbackBaseChangeMap (pullback.snd v (𝟙 Y)) v f (pullbackIdIso v).hom
          (by simpa [pullbackIdIso] using pullback.condition (f := v) (g := 𝟙 Y)) =
      𝟙 (pullback v f) := by
    intro A v
    apply pullback.hom_ext <;>
      simp [pullbackComp'Iso, pullbackCompIso, pullbackIdIso, pullbackBaseChangeMap]
  exact Etale.hom_ext (key V.hom)

/-- Right-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChangeComp (𝟙 Y)).hom.app V ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).hom.app V) =
      (smallEtaleBaseChangeCongr (Category.comp_id f)).hom.app V := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCompIso v f (𝟙 Y)).hom ≫
        pullbackBaseChangeMap (pullback.snd v (𝟙 Y)) v f (pullbackIdIso v).hom
          (by simpa [pullbackIdIso] using pullback.condition (f := v) (g := 𝟙 Y)) =
      (pullback.congrHom (f₁ := v) (g₁ := f ≫ 𝟙 Y) rfl (Category.comp_id f)).hom := by
    intro A v
    apply pullback.hom_ext <;>
      simp [pullbackCompIso, pullbackIdIso, pullbackBaseChangeMap]
  exact Etale.hom_ext (key V.hom)

/-- Left-unit coherence for `smallEtaleBaseChangeComp'` along `𝟙 X ≫ f = f`. -/
@[reassoc]
theorem smallEtaleBaseChangeComp'_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : 𝟙 X ≫ f = f)
    (V : Y.Etale) :
    (smallEtaleBaseChangeComp' (𝟙 X) f f hf).hom.app V ≫
        (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackComp'Iso v (𝟙 X) f f hf).hom ≫ (pullbackIdIso (pullback.snd v f)).hom =
      𝟙 (pullback v f) := by
    intro A v
    apply pullback.hom_ext
    · simp [pullbackComp'Iso, pullbackCompIso, pullbackIdIso]
    · simp only [pullbackIdIso, Category.assoc, pullback.condition]
      simp [pullbackComp'Iso, pullbackCompIso]
  exact Etale.hom_ext (key V.hom)

/-- Left-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeComp (𝟙 X) f).hom.app V ≫
        (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) =
      (smallEtaleBaseChangeCongr (Category.id_comp f)).hom.app V := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCompIso v (𝟙 X) f).hom ≫ (pullbackIdIso (pullback.snd v f)).hom =
      (pullback.congrHom (f₁ := v) (g₁ := 𝟙 X ≫ f) rfl (Category.id_comp f)).hom := by
    intro A v
    apply pullback.hom_ext
    · simp [pullbackCompIso, pullbackIdIso]
    · simp only [pullbackIdIso, Category.assoc, pullback.condition]
      simp [pullbackCompIso]
  exact Etale.hom_ext (key V.hom)

/-! ### Base-change comparison across commutative and Cartesian squares -/

/-- Any commutative square `gX ≫ f = f' ≫ g` of schemes induces a canonical natural isomorphism
between the iterated base-change functors `f.smallEtaleBaseChange ⋙ gX.smallEtaleBaseChange` and
`g.smallEtaleBaseChange ⋙ f'.smallEtaleBaseChange`. -/
noncomputable def smallEtaleBaseChangeCommSq {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    f.smallEtaleBaseChange ⋙ gX.smallEtaleBaseChange ≅
      g.smallEtaleBaseChange ⋙ f'.smallEtaleBaseChange :=
  (gX.smallEtaleBaseChangeComp f).symm ≪≫ smallEtaleBaseChangeCongr w ≪≫
    f'.smallEtaleBaseChangeComp g

/-- Composing the forward component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the two
first projections recovers the two first projections on the opposite path of the square. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_hom_app_left_fst_fst {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f' ≫ pullback.fst V.hom g =
      pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v w).hom ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g =
        pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f := by
    intro A v
    simp [pullbackCommSqIso, pullbackCompIso]
  exact key V.hom

/-- Composing the forward component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
outer second projection to `X'` recovers the outer second projection on the opposite path. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_hom_app_left_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).hom.app V).left ≫
        pullback.snd (pullback.snd V.hom g) f' =
      pullback.snd (pullback.snd V.hom f) gX := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v w).hom ≫ pullback.snd (pullback.snd v g) f' =
        pullback.snd (pullback.snd v f) gX := by
    intro A v
    simp [pullbackCommSqIso, pullbackCompIso]
  exact key V.hom

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the two
first projections recovers the two first projections on the opposite path of the square. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_fst_fst {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f =
      pullback.fst (pullback.snd V.hom g) f' ≫ pullback.fst V.hom g := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v w).inv ≫ pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f =
        pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g := by
    intro A v
    simp [pullbackCommSqIso, pullbackCompIso]
  exact key V.hom

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
outer second projection to `X'` recovers the outer second projection on the opposite path. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.snd (pullback.snd V.hom f) gX =
      pullback.snd (pullback.snd V.hom g) f' := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v w).inv ≫ pullback.snd (pullback.snd v f) gX =
        pullback.snd (pullback.snd v g) f' := by
    intro A v
    simp [pullbackCommSqIso, pullbackCompIso]
  exact key V.hom

/-- Transposing a commutative square inverts `smallEtaleBaseChangeCommSq`. -/
theorem smallEtaleBaseChangeCommSq_symm {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    (smallEtaleBaseChangeCommSq w).symm = smallEtaleBaseChangeCommSq w.symm := by
  ext V : 3
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v w).inv = (pullbackCommSqIso v w.symm).hom := by
    intro A v
    refine pullback_snd_hom_ext ?_ ?_ <;>
      simp [pullbackCommSqIso, pullbackCompIso]
  exact Etale.hom_ext (key V.hom)

/-- Along the trivial identity-base-change square `𝟙 X ≫ f = f ≫ 𝟙 Y`,
`smallEtaleBaseChangeCommSq` reduces to the left and right unit comparisons
`X.smallEtaleBaseChangeId` and `Y.smallEtaleBaseChangeId`. -/
theorem smallEtaleBaseChangeCommSq_id_app {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeCommSq
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app V =
      (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).inv.app V) := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCommSqIso v ((Category.id_comp f).trans (Category.comp_id f).symm)).hom =
        (pullbackIdIso (pullback.snd v f)).hom ≫
          pullbackBaseChangeMap v (pullback.snd v (𝟙 Y)) f (pullbackIdIso v).inv
            (by simp [pullbackIdIso]) := by
    intro A v
    refine pullback_snd_hom_ext ?_ ?_
    · simp [pullbackCommSqIso, pullbackCompIso, pullbackIdIso, pullbackBaseChangeMap]
    · simp only [pullbackIdIso, pullbackBaseChangeMap, Category.assoc, pullback.lift_snd]
      rw [pullback.condition]
      simp [pullbackCommSqIso, pullbackCompIso]
  exact Etale.hom_ext (key V.hom)

/-- Pasting two composable commutative squares `gX' ≫ gX ≫ f = ...` (`X'' ⟶ X' ⟶ X` over
`Y'' ⟶ Y' ⟶ Y`) commutes with `smallEtaleBaseChangeCommSq` via `smallEtaleBaseChangeComp`. -/
@[reassoc]
theorem smallEtaleBaseChangeCommSq_paste {X'' X' X Y'' Y' Y : Scheme.{u}}
    {gX' : X'' ⟶ X'} {gX : X' ⟶ X} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g' : Y'' ⟶ Y'} {g : Y' ⟶ Y} (w₁ : gX ≫ f = f' ≫ g) (w₂ : gX' ≫ f' = f'' ≫ g')
    (V : Y.Etale) :
    (gX'.smallEtaleBaseChangeComp gX).hom.app (f.smallEtaleBaseChange.obj V) ≫
        gX'.smallEtaleBaseChange.map ((smallEtaleBaseChangeCommSq w₁).hom.app V) ≫
        (smallEtaleBaseChangeCommSq w₂).hom.app (g.smallEtaleBaseChange.obj V) ≫
        f''.smallEtaleBaseChange.map ((g'.smallEtaleBaseChangeComp g).inv.app V) =
      (smallEtaleBaseChangeCommSq
        (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc])).hom.app V := by
  have key : ∀ {A : Scheme.{u}} (v : A ⟶ Y),
      (pullbackCompIso (pullback.snd v f) gX' gX).hom ≫
        pullbackBaseChangeMap (pullback.snd (pullback.snd v f) gX)
          (pullback.snd (pullback.snd v g) f') gX' (pullbackCommSqIso v w₁).hom
          (by simp [pullbackCommSqIso, pullbackCompIso]) ≫
        (pullbackCommSqIso (pullback.snd v g) w₂).hom ≫
        pullbackBaseChangeMap (pullback.snd (pullback.snd v g) g')
          (pullback.snd v (g' ≫ g)) f'' (pullbackCompIso v g' g).inv
          (by simp [pullbackCompIso]) =
      (pullbackCommSqIso v
        (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc])).hom := by
    intro A v
    refine pullback_snd_hom_ext ?_ ?_ <;>
      simp [pullbackCommSqIso, pullbackCompIso, pullbackBaseChangeMap]
  exact Etale.hom_ext (key V.hom)

/-- Base-change comparison across the canonical pullback square of `f : X ⟶ Y` and `g : Y' ⟶ Y`:
pulling an étale `Y`-scheme back along `f` and then `pullback.fst f g` is canonically isomorphic to
pulling it back along `g` and then `pullback.snd f g`. -/
noncomputable abbrev smallEtaleBaseChangePullback {X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    f.smallEtaleBaseChange ⋙ smallEtaleBaseChange (pullback.fst f g) ≅
      g.smallEtaleBaseChange ⋙ smallEtaleBaseChange (pullback.snd f g) :=
  smallEtaleBaseChangeCommSq pullback.condition

end Hom

/-! ### The contravariant small étale pseudofunctor -/

/-- The contravariant pseudofunctor `LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}` sending each
scheme `X` to its category `X.Etale` of étale `X`-schemes and each morphism `f : X ⟶ Y` to
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`. -/
noncomputable def smallEtalePseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkCatPseudofunctor
    (obj := fun X ↦ Cat.of X.unop.Etale)
    (fun f ↦ f.unop.smallEtaleBaseChange)
    (fun X ↦ X.unop.smallEtaleBaseChangeId)
    (fun f g fg hfg ↦ g.unop.smallEtaleBaseChangeComp' f.unop fg.unop (Quiver.Hom.op_inj hfg))
    (fun _ _ _ _ _ _ hfg hgh hfgh hfgh' V ↦
      Hom.smallEtaleBaseChangeComp'_associativity _ _ _ _ _ _
        (Quiver.Hom.op_inj hgh) (Quiver.Hom.op_inj hfg)
        (Quiver.Hom.op_inj hfgh') (Quiver.Hom.op_inj hfgh) V)
    (fun _ hf V ↦ Hom.smallEtaleBaseChangeComp'_comp_id _ (Quiver.Hom.op_inj hf) V)
    (fun _ hf V ↦ Hom.smallEtaleBaseChangeComp'_id_comp _ (Quiver.Hom.op_inj hf) V)

/-- `smallEtalePseudofunctor` evaluates on `X` to `Cat.of X.as.unop.Etale`. -/
@[simp]
theorem smallEtalePseudofunctor_obj (X : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    smallEtalePseudofunctor.obj X = Cat.of X.as.unop.Etale :=
  rfl

/-- `smallEtalePseudofunctor` sends a `1`-morphism `f` to `f.as.unop.smallEtaleBaseChange`. -/
@[simp]
theorem smallEtalePseudofunctor_map_toFunctor {X Y : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (smallEtalePseudofunctor.map f).toFunctor = f.as.unop.smallEtaleBaseChange :=
  rfl

/-- The forward unit comparison of `smallEtalePseudofunctor` at `X` is
`X.as.unop.smallEtaleBaseChangeId`. -/
@[simp]
theorem smallEtalePseudofunctor_mapId_hom_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).hom.toNatTrans.app V =
      (X.as.unop.smallEtaleBaseChangeId).hom.app V :=
  rfl

/-- The inverse unit comparison of `smallEtalePseudofunctor` at `X` is
`(X.as.unop.smallEtaleBaseChangeId).inv`. -/
@[simp]
theorem smallEtalePseudofunctor_mapId_inv_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).inv.toNatTrans.app V =
      (X.as.unop.smallEtaleBaseChangeId).inv.app V :=
  rfl

/-- The forward composition comparison of `smallEtalePseudofunctor` at `f, g` agrees with
`smallEtaleBaseChangeComp`. -/
@[simp]
theorem smallEtalePseudofunctor_mapComp_hom_toNatTrans_app {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapComp f g).hom.toNatTrans.app V =
      ((g.as.unop.smallEtaleBaseChangeComp f.as.unop).hom.app V) := by
  dsimp only [smallEtalePseudofunctor,
    LocallyDiscrete.mkCatPseudofunctor_mapComp_hom_toNatTrans_app]
  exact congrArg (fun e ↦ e.hom.app V) (Hom.smallEtaleBaseChangeComp'_rfl g.as.unop f.as.unop)

/-- The inverse composition comparison of `smallEtalePseudofunctor` at `f, g` agrees with
`(smallEtaleBaseChangeComp _ _).inv`. -/
@[simp]
theorem smallEtalePseudofunctor_mapComp_inv_toNatTrans_app {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapComp f g).inv.toNatTrans.app V =
      ((g.as.unop.smallEtaleBaseChangeComp f.as.unop).inv.app V) := by
  dsimp only [smallEtalePseudofunctor,
    LocallyDiscrete.mkCatPseudofunctor_mapComp_inv_toNatTrans_app]
  exact congrArg (fun e ↦ e.inv.app V) (Hom.smallEtaleBaseChangeComp'_rfl g.as.unop f.as.unop)

end AlgebraicGeometry.Scheme
