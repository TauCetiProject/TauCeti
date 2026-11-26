/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.Over.Basic
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change between small étale sites

For a morphism of schemes `f : X ⟶ Y`, the base-change functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`, its unit, congruence and composition isomorphisms
`smallEtaleBaseChangeId`, `smallEtaleBaseChangeCongr` and `smallEtaleBaseChangeComp`, and, for étale
`f`, the post-composition functor `f.smallEtaleMap` and the adjunction
`f.smallEtaleMapBaseChangeAdj : f.smallEtaleMap ⊣ f.smallEtaleBaseChange` are defined in
`TauCeti/AlgebraicGeometry/Sites/Etale/Over/Basic.lean`; finite-limit preservation and continuity of
`f.smallEtaleBaseChange` are in `TauCeti/AlgebraicGeometry/Sites/Etale/Pullback.lean`. This file
develops further API for these functors.

Base change of a morphism of `Y.Etale` is a pullback square of schemes, so its set-theoretic range
is the preimage of the original range and jointly surjective étale families stay jointly
surjective. When `f` is surjective, `f.smallEtaleBaseChange` is faithful.

When `f : X ⟶ Y` is étale, `f.smallEtaleMap` is faithful and preserves compatible families for any
Grothendieck topology on `Y.Etale`; if `f` is also a monomorphism (for instance an open immersion),
`f.smallEtaleMap` is full as well and the adjunction unit identifies
`f.smallEtaleMap ⋙ f.smallEtaleBaseChange` with `𝟭 X.Etale`. The essential image of
`f.smallEtaleMap` is closed under morphisms into it (`smallEtaleMap_essImage`). When `X` is empty,
`f.smallEtaleBaseChange` is isomorphic to the constant functor at `Etale.mk (𝟙 X)`.

We also give projection lemmas for `smallEtaleBaseChangeCongr` and for `smallEtaleBaseChangeComp`
along an arbitrary factorization `fg = f ≫ g`, and the induced equivalence
`f.smallEtaleEquivOfIsIso` along an isomorphism. The pseudofunctorial coherence laws,
commutative-square comparisons, and `smallEtalePseudofunctor` are proved in
`TauCeti/AlgebraicGeometry/Sites/Etale/Pseudofunctor.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.smallEtaleMapCompSmallEtaleBaseChangeIso`: for an étale
  monomorphism `f`, the isomorphism `f.smallEtaleMap ⋙ f.smallEtaleBaseChange ≅ 𝟭 X.Etale`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeIsoConstOfIsEmpty`: base change from an empty
  scheme is constant.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleEquivOfIsIso`: the equivalence `Y.Etale ≌ X.Etale`
  induced by base change along an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPullback_smallEtaleBaseChange_map` and
  `AlgebraicGeometry.Scheme.Hom.range_smallEtaleBaseChange_map_left`: base change of a `Y.Etale`
  morphism is a scheme pullback square, so its set-theoretic range is the preimage of the original
  range; in particular jointly surjective étale families remain jointly surjective.
* `AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleBaseChange`: `f.smallEtaleBaseChange` is
  faithful when `f` is surjective.
* `AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleMap` and
  `AlgebraicGeometry.Scheme.Hom.full_smallEtaleMap`: `f.smallEtaleMap` is faithful for étale `f`,
  and full when `f` is moreover a monomorphism.

## References

* The Stacks Project, [Tag 021I](https://stacks.math.columbia.edu/tag/021I) and
  [Tag 021J](https://stacks.math.columbia.edu/tag/021J), the small étale site and functoriality.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.Hom

section Basic

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Composing `(f.smallEtaleBaseChange.map φ).left` with `pullback.fst` intertwines the first
projections with `φ.left`. -/
theorem smallEtaleBaseChange_map_left_fst {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% (f.smallEtaleBaseChange.map φ).left ≫ pullback.fst V.hom f =
      pullback.fst W.hom f ≫ φ.left :=
  pullback.lift_fst _ _ _

/-- Composing `(f.smallEtaleBaseChange.map φ).left` with `pullback.snd` recovers `pullback.snd`. -/
theorem smallEtaleBaseChange_map_left_snd {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% (f.smallEtaleBaseChange.map φ).left ≫ pullback.snd V.hom f = pullback.snd W.hom f :=
  pullback.lift_snd _ _ _

/-- Two morphisms in `X.Etale` into `f.smallEtaleBaseChange.obj V` are equal if they agree after
composing with the first projection `pullback.fst V.hom f`; equality after `pullback.snd V.hom f`
holds automatically since both are morphisms over `X`. -/
theorem smallEtaleBaseChange_hom_ext {V : Y.Etale} {A : X.Etale}
    {φ ψ : A ⟶ f.smallEtaleBaseChange.obj V}
    (h : dsimp% φ.left ≫ pullback.fst V.hom f = dsimp% ψ.left ≫ pullback.fst V.hom f) :
    φ = ψ := by
  apply Etale.hom_ext
  exact pullback.hom_ext h ((MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm)

/-- Two morphisms in `X.Etale` into the iterated base change
`f.smallEtaleBaseChange.obj (g.smallEtaleBaseChange.obj V)` are equal if they agree after
composing with the composite first projection
`pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g`; equality after the second
projections holds automatically since both are morphisms over `X`. -/
theorem smallEtaleBaseChange_comp_hom_ext {Z : Scheme.{u}} (g : Y ⟶ Z) {V : Z.Etale} {A : X.Etale}
    {φ ψ : A ⟶ f.smallEtaleBaseChange.obj (g.smallEtaleBaseChange.obj V)}
    (h : dsimp% φ.left ≫ pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      dsimp% ψ.left ≫ pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g) :
    φ = ψ := by
  apply f.smallEtaleBaseChange_hom_ext
  apply pullback.hom_ext
  · exact ((Category.assoc _ _ _).trans h).trans (Category.assoc _ _ _).symm
  · calc (φ.left ≫ pullback.fst (pullback.snd V.hom g) f) ≫ pullback.snd V.hom g
        = φ.left ≫ pullback.snd (pullback.snd V.hom g) f ≫ f :=
            (Category.assoc _ _ _).trans (congrArg (φ.left ≫ ·) pullback.condition)
      _ = A.hom ≫ f :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (MorphismProperty.Over.w φ))
      _ = ψ.left ≫ pullback.snd (pullback.snd V.hom g) f ≫ f :=
            (congrArg (· ≫ f) (MorphismProperty.Over.w ψ)).symm.trans (Category.assoc _ _ _)
      _ = (ψ.left ≫ pullback.fst (pullback.snd V.hom g) f) ≫ pullback.snd V.hom g :=
            (congrArg (ψ.left ≫ ·) pullback.condition.symm).trans (Category.assoc _ _ _).symm

/-- For `V : Y.Etale`, the projections from `(f.smallEtaleBaseChange.obj V).left` form a pullback
square over `Y`. -/
theorem isPullback_smallEtaleBaseChange_obj (V : Y.Etale) :
    IsPullback (pullback.fst V.hom f) (f.smallEtaleBaseChange.obj V).hom V.hom f :=
  IsPullback.of_hasPullback V.hom f

/-- For any morphism `φ : W ⟶ V` in `Y.Etale`, `(f.smallEtaleBaseChange.map φ).left` fits into a
pullback square with `φ.left` along the first projections to `W.left` and `V.left`. -/
theorem isPullback_smallEtaleBaseChange_map {W V : Y.Etale} (φ : W ⟶ V) :
    IsPullback (f.smallEtaleBaseChange.map φ).left (pullback.fst W.hom f)
      (pullback.fst V.hom f) φ.left :=
  CategoryTheory.Over.isPullback_pullback_map_left f ((Etale.forget Y).map φ)

/-- The set-theoretic range of `(f.smallEtaleBaseChange.map φ).left` is the preimage of the range
of `φ.left` under `pullback.fst V.hom f`. -/
theorem range_smallEtaleBaseChange_map_left {W V : Y.Etale} (φ : W ⟶ V) :
    dsimp% Set.range (f.smallEtaleBaseChange.map φ).left =
      pullback.fst V.hom f ⁻¹' Set.range φ.left := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (f.isPullback_smallEtaleBaseChange_map φ).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h

/-- Base change along `f` commutes with set-theoretic unions of ranges of étale `Y`-morphisms. -/
theorem iUnion_range_smallEtaleBaseChange_map_left {V : Y.Etale} {ι : Type*} {Z : ι → Y.Etale}
    (g : ∀ i, Z i ⟶ V) :
    (⋃ i, Set.range (f.smallEtaleBaseChange.map (g i)).left) =
      pullback.fst V.hom f ⁻¹' (⋃ i, Set.range (g i).left) :=
  (Set.iUnion_congr fun i ↦ f.range_smallEtaleBaseChange_map_left (g i)).trans
    Set.preimage_iUnion.symm

/-- Base change along `f` preserves jointly surjective families in `Y.Etale`. -/
theorem iUnion_range_smallEtaleBaseChange_map_left_eq_univ {V : Y.Etale} {ι : Type*}
    {Z : ι → Y.Etale} (g : ∀ i, Z i ⟶ V) (hg : ⋃ i, Set.range (g i).left = Set.univ) :
    ⋃ i, Set.range (f.smallEtaleBaseChange.map (g i)).left = Set.univ :=
  (f.iUnion_range_smallEtaleBaseChange_map_left g).trans
    ((congrArg (pullback.fst V.hom f ⁻¹' ·) hg).trans Set.preimage_univ)

/-- Base change along a surjective morphism `f : X ⟶ Y` is faithful on schemes étale over `Y`. -/
instance faithful_smallEtaleBaseChange [Surjective f] : f.smallEtaleBaseChange.Faithful where
  map_injective {A B} g₁ g₂ h := by
    ext1
    have : Surjective (pullback.fst (A.hom : A.left ⟶ Y) f) :=
      MorphismProperty.of_isPullback (P := @Surjective)
        (IsPullback.of_hasPullback (A.hom : A.left ⟶ Y) f).flip ‹Surjective f›
    refine ext_of_surjective_of_formallyUnramified B.hom
      ((MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm)
      (pullback.fst (A.hom : A.left ⟶ Y) f) ?_
    have hleft : (f.smallEtaleBaseChange.map g₁).left = (f.smallEtaleBaseChange.map g₂).left :=
      congrArg (·.left) h
    have h₁ : (f.smallEtaleBaseChange.map g₁).left ≫ pullback.fst B.hom f =
        pullback.fst A.hom f ≫ g₁.left := f.smallEtaleBaseChange_map_left_fst g₁
    have h₂ : (f.smallEtaleBaseChange.map g₂).left ≫ pullback.fst B.hom f =
        pullback.fst A.hom f ≫ g₂.left := f.smallEtaleBaseChange_map_left_fst g₂
    exact h₁.symm.trans ((congrArg (· ≫ pullback.fst B.hom f) hleft).trans h₂)

end Basic

/-! ### Left adjoint along an étale morphism and open-immersion specialization -/

section EtaleMorphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- On underlying schemes over `Y`, `f.smallEtaleMap` agrees with `CategoryTheory.Over.map f`. -/
noncomputable def smallEtaleMapCompForgetIso :
    f.smallEtaleMap ⋙ Etale.forget Y ≅ Etale.forget X ⋙ CategoryTheory.Over.map f :=
  Iso.refl _

/-- The forward component of `f.smallEtaleMapCompForgetIso` at `W` is the identity on `W.left`. -/
@[simp]
theorem smallEtaleMapCompForgetIso_hom_app_left (W : X.Etale) :
    (f.smallEtaleMapCompForgetIso.hom.app W).left = 𝟙 W.left :=
  (rfl)

/-- The inverse component of `f.smallEtaleMapCompForgetIso` at `W` is the identity on `W.left`. -/
@[simp]
theorem smallEtaleMapCompForgetIso_inv_app_left (W : X.Etale) :
    (f.smallEtaleMapCompForgetIso.inv.app W).left = 𝟙 W.left :=
  (rfl)

/-- `f.smallEtaleMap` is a left adjoint when `f` is étale. -/
instance isLeftAdjoint_smallEtaleMap : f.smallEtaleMap.IsLeftAdjoint :=
  f.smallEtaleMapBaseChangeAdj.isLeftAdjoint

/-- `f.smallEtaleBaseChange` is a right adjoint when `f` is étale. -/
instance isRightAdjoint_smallEtaleBaseChange_of_etale : f.smallEtaleBaseChange.IsRightAdjoint :=
  f.smallEtaleMapBaseChangeAdj.isRightAdjoint

/-- For an étale morphism `f : X ⟶ Y`, `f.smallEtaleMap` preserves compatible families for any
Grothendieck topology `K` on `Y.Etale`. Adapted from Mathlib's
`CategoryTheory.GrothendieckTopology.over_map_compatiblePreserving`. -/
theorem compatiblePreserving_smallEtaleMap (K : GrothendieckTopology Y.Etale) :
    CompatiblePreserving K f.smallEtaleMap where
  compatible {F Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    -- Any `Y`-scheme `W` étale over `Y` mapping to `f.smallEtaleMap.obj Y₁` lifts to `X.Etale` via
    -- `f₁.left ≫ Y₁.hom`, because `f₁.left` and `Y₁.hom` are both étale.
    let φ₁ : W.left ⟶ Y₁.left := f₁.left
    let φ₂ : W.left ⟶ Y₂.left := f₂.left
    let y₁ : Y₁.left ⟶ X := Y₁.hom
    let y₂ : Y₂.left ⟶ X := Y₂.hom
    let z : Z.left ⟶ X := Z.hom
    let γ₁ : Y₁.left ⟶ Z.left := g₁.left
    let γ₂ : Y₂.left ⟶ Z.left := g₂.left
    have : Etale φ₁ := inferInstanceAs (Etale f₁.left)
    have : Etale y₁ := Y₁.prop
    have hleft : φ₂ ≫ γ₂ = φ₁ ≫ γ₁ :=
      (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h.symm
    have hg₁w : γ₁ ≫ z = y₁ := MorphismProperty.Over.w g₁
    have hg₂w : γ₂ ≫ z = y₂ := MorphismProperty.Over.w g₂
    have hw₂ : φ₂ ≫ y₂ = φ₁ ≫ y₁ := by
      rw [← hg₂w, ← Category.assoc, hleft, Category.assoc, hg₁w]
    let W' : X.Etale := Etale.mk (φ₁ ≫ y₁)
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk φ₁
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk φ₂ hw₂
    let e : f.smallEtaleMap.obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl W.left) <|
      (Category.id_comp W.hom).trans ((MorphismProperty.Over.w f₁).symm.trans
        (Category.assoc φ₁ y₁ f).symm)
    have he₁ : f₁ = e.inv ≫ f.smallEtaleMap.map g₁' := by
      ext1; exact (Category.id_comp φ₁).symm
    have he₂ : f₂ = e.inv ≫ f.smallEtaleMap.map g₂' := by
      ext1; exact (Category.id_comp φ₂).symm
    have hcompat := congrArg (F.obj.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂
        (by ext1; exact (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h))
    simpa only [Functor.comp_map, Functor.op_map, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Quiver.Hom.unop_op, ← he₁, ← he₂] using hcompat

/-- For any étale morphism `f : X ⟶ Y`, `f.smallEtaleMap` is faithful. -/
instance faithful_smallEtaleMap : f.smallEtaleMap.Faithful where
  map_injective h := by
    ext1
    exact (Etale.forget Y ⋙ CategoryTheory.Over.forget Y).congr_map h

/-- When `f : X ⟶ Y` is an étale monomorphism (for instance an open immersion), `f.smallEtaleMap`
is full: any `Y`-morphism between `X`-schemes automatically commutes over `X`. -/
instance full_smallEtaleMap [Mono f] : f.smallEtaleMap.Full where
  map_surjective {W₁ W₂} φ :=
    ⟨MorphismProperty.Over.homMk (φ.left : W₁.left ⟶ W₂.left)
      ((cancel_mono f).mp ((Category.assoc _ _ _).trans (MorphismProperty.Over.w φ))),
      by ext1; rfl⟩

/-- An étale `Y`-scheme admitting a `Y`-morphism to an étale `X`-scheme lies in the essential image
of postcomposition with the étale morphism `f : X ⟶ Y`. -/
lemma smallEtaleMap_essImage {V : Y.Etale} {W : X.Etale} (g : V ⟶ f.smallEtaleMap.obj W) :
    f.smallEtaleMap.essImage V := by
  have hg : (g.left ≫ W.hom) ≫ f = V.hom :=
    (Category.assoc _ _ _).trans (MorphismProperty.Over.w g)
  have : Etale ((g.left ≫ W.hom) ≫ f) := by rw [hg]; infer_instance
  have : Etale (g.left ≫ W.hom) := Etale.of_comp _ f
  exact ⟨Etale.mk (g.left ≫ W.hom),
    ⟨MorphismProperty.Over.isoMk (Iso.refl V.left) ((Category.id_comp _).trans hg.symm)⟩⟩

/-- When `f : X ⟶ Y` is an étale monomorphism (such as an open immersion `j : U ⟶ Y`), restricting
`f.smallEtaleMap.obj W` back along `f` canonically recovers `W`: the unit of
`f.smallEtaleMapBaseChangeAdj` is an isomorphism. -/
instance isIso_smallEtaleMapBaseChangeAdj_unit [Mono f] :
    IsIso f.smallEtaleMapBaseChangeAdj.unit :=
  f.smallEtaleMapBaseChangeAdj.unit_isIso_of_L_fully_faithful

/-- For an étale monomorphism `f : X ⟶ Y` (in particular any open immersion `j : U ⟶ Y`), viewing
an étale `X`-scheme over `Y` and pulling back along `f` is naturally isomorphic to the identity
functor on `X.Etale`. -/
noncomputable def smallEtaleMapCompSmallEtaleBaseChangeIso [Mono f] :
    f.smallEtaleMap ⋙ f.smallEtaleBaseChange ≅ 𝟭 X.Etale :=
  (asIso f.smallEtaleMapBaseChangeAdj.unit).symm

/-- The inverse of `f.smallEtaleMapCompSmallEtaleBaseChangeIso` is the adjunction unit
`f.smallEtaleMapBaseChangeAdj.unit`. -/
@[simp]
theorem smallEtaleMapCompSmallEtaleBaseChangeIso_inv [Mono f] :
    f.smallEtaleMapCompSmallEtaleBaseChangeIso.inv = f.smallEtaleMapBaseChangeAdj.unit :=
  (rfl)

/-- On underlying schemes, the forward component of `f.smallEtaleMapCompSmallEtaleBaseChangeIso` at
`W : X.Etale` is the first projection `pullback.fst (W.hom ≫ f) f`. -/
@[simp]
theorem smallEtaleMapCompSmallEtaleBaseChangeIso_hom_app_left [Mono f] (W : X.Etale) :
    dsimp% (f.smallEtaleMapCompSmallEtaleBaseChangeIso.hom.app W).left =
      pullback.fst (W.hom ≫ f) f := by
  have : IsIso (f.smallEtaleMapBaseChangeAdj.unit.app W).left :=
    (Etale.forget X ⋙ CategoryTheory.Over.forget X).map_isIso
      (f.smallEtaleMapBaseChangeAdj.unit.app W)
  have h := congrArg (·.left) (f.smallEtaleMapCompSmallEtaleBaseChangeIso.inv_hom_id_app W)
  simp only [Etale.comp_left, Etale.id_left, smallEtaleMapCompSmallEtaleBaseChangeIso_inv] at h
  have hu : (f.smallEtaleMapBaseChangeAdj.unit.app W).left ≫ pullback.fst (W.hom ≫ f) f =
      𝟙 W.left :=
    (congrArg ((f.smallEtaleMapBaseChangeAdj.unit.app W).left ≫ ·)
      (f.smallEtaleMapBaseChangeAdj_counit_app_left (f.smallEtaleMap.obj W))).symm.trans
        (congrArg (·.left) (f.smallEtaleMapBaseChangeAdj.left_triangle_components W))
  exact (cancel_epi (f.smallEtaleMapBaseChangeAdj.unit.app W).left).mp (h.trans hu.symm)

end EtaleMorphism

/-! ### Empty-scheme specialization -/

section IsEmpty

/-- Base change along `f : X ⟶ Y` from an empty scheme `X` is naturally isomorphic to the constant
functor at `Etale.mk (𝟙 X)`. -/
noncomputable def smallEtaleBaseChangeIsoConstOfIsEmpty {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsEmpty X] :
    f.smallEtaleBaseChange ≅ (Functor.const Y.Etale).obj (Etale.mk (𝟙 X)) :=
  NatIso.ofComponents (fun _ ↦ { hom := default, inv := default })

end IsEmpty

/-! ### Identity, congruence, composition, and equivalences along isomorphisms -/

/-- Composing the forward component of `smallEtaleBaseChangeCongr h` with `pullback.fst` recovers
`pullback.fst`. -/
theorem smallEtaleBaseChangeCongr_hom_app_left_fst {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ pullback.fst V.hom f' =
      pullback.fst V.hom f :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h V

/-- Composing the forward component of `smallEtaleBaseChangeCongr h` with `pullback.snd` recovers
`pullback.snd`. -/
theorem smallEtaleBaseChangeCongr_hom_app_left_snd {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ pullback.snd V.hom f' =
      pullback.snd V.hom f :=
  MorphismProperty.Over.w ((smallEtaleBaseChangeCongr h).hom.app V)

/-- `smallEtaleBaseChangeCongr` at `rfl` is the identity natural isomorphism. -/
@[simp]
theorem smallEtaleBaseChangeCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleBaseChangeCongr (rfl : f = f) = Iso.refl f.smallEtaleBaseChange := by
  ext V : 3
  apply f.smallEtaleBaseChange_hom_ext
  exact (smallEtaleBaseChangeCongr_hom_app_left_fst rfl V).trans (Category.id_comp _).symm

/-- Composing the inverse component of `smallEtaleBaseChangeCongr h` with `pullback.fst` recovers
`pullback.fst`. -/
theorem smallEtaleBaseChangeCongr_inv_app_left_fst {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ pullback.fst V.hom f =
      pullback.fst V.hom f' := by
  have hi := congrArg (·.left ≫ pullback.fst V.hom f')
    ((smallEtaleBaseChangeCongr h).inv_hom_id_app V)
  exact (congrArg (((smallEtaleBaseChangeCongr h).inv.app V).left ≫ ·)
    (smallEtaleBaseChangeCongr_hom_app_left_fst h V).symm).trans
      (((Category.assoc _ _ _).symm.trans hi).trans (Category.id_comp _))

/-- Composing the inverse component of `smallEtaleBaseChangeCongr h` with `pullback.snd` recovers
`pullback.snd`. -/
theorem smallEtaleBaseChangeCongr_inv_app_left_snd {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (h : f = f') (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ pullback.snd V.hom f =
      pullback.snd V.hom f' :=
  MorphismProperty.Over.w ((smallEtaleBaseChangeCongr h).inv.app V)

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

/-- For an arbitrary factorization `fg = f ≫ g`, `f.smallEtaleBaseChangeComp g fg hfg` factors as
`smallEtaleBaseChangeCongr hfg` followed by `f.smallEtaleBaseChangeComp g`. -/
theorem smallEtaleBaseChangeComp_eq_congr_trans {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    f.smallEtaleBaseChangeComp g fg hfg =
      smallEtaleBaseChangeCongr hfg ≪≫ f.smallEtaleBaseChangeComp g := by
  subst hfg
  simp

/-- Composing the forward component of `f.smallEtaleBaseChangeComp g fg hfg` at `V : Z.Etale` with
the two first projections recovers `pullback.fst V.hom fg`. -/
@[simp]
theorem smallEtaleBaseChangeComp_hom_app_left_fst_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g fg hfg).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom fg := by
  subst hfg
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g V

/-- Composing the forward component of `f.smallEtaleBaseChangeComp g fg hfg` at `V : Z.Etale` with
the outer second projection recovers `pullback.snd V.hom fg`. -/
@[simp]
theorem smallEtaleBaseChangeComp_hom_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g fg hfg).hom.app V).left ≫
        pullback.snd (pullback.snd V.hom g) f =
      pullback.snd V.hom fg :=
  MorphismProperty.Over.w ((f.smallEtaleBaseChangeComp g fg hfg).hom.app V)

/-- Composing the forward component of `f.smallEtaleBaseChangeComp g fg hfg` at `V : Z.Etale` with
the middle projection `pullback.fst _ f ≫ pullback.snd V.hom g` recovers
`pullback.snd V.hom fg ≫ f`. -/
@[simp]
theorem smallEtaleBaseChangeComp_hom_app_left_fst_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g fg hfg).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.snd V.hom g =
      pullback.snd V.hom fg ≫ f :=
  (congrArg (((f.smallEtaleBaseChangeComp g fg hfg).hom.app V).left ≫ ·)
    pullback.condition).trans <|
    (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ f) (f.smallEtaleBaseChangeComp_hom_app_left_snd g fg hfg V)

/-- Composing the inverse component of `f.smallEtaleBaseChangeComp g fg hfg` at `V : Z.Etale` with
`pullback.fst V.hom fg` gives the composite of the two first projections. -/
@[simp]
theorem smallEtaleBaseChangeComp_inv_app_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g fg hfg).inv.app V).left ≫ pullback.fst V.hom fg =
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g := by
  have h : ((f.smallEtaleBaseChangeComp g fg hfg).inv.app V).left ≫
      (((f.smallEtaleBaseChangeComp g fg hfg).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g) =
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g := by
    have hi := congrArg (·.left ≫ pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g)
      ((f.smallEtaleBaseChangeComp g fg hfg).inv_hom_id_app V)
    exact ((Category.assoc _ _ _).symm.trans hi).trans (Category.id_comp _)
  exact (congrArg (((f.smallEtaleBaseChangeComp g fg hfg).inv.app V).left ≫ ·)
    (f.smallEtaleBaseChangeComp_hom_app_left_fst_fst g fg hfg V).symm).trans h

/-- Composing the inverse component of `f.smallEtaleBaseChangeComp g fg hfg` at `V : Z.Etale` with
`pullback.snd V.hom fg` gives `pullback.snd (pullback.snd V.hom g) f`. -/
@[simp]
theorem smallEtaleBaseChangeComp_inv_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    dsimp% ((f.smallEtaleBaseChangeComp g fg hfg).inv.app V).left ≫ pullback.snd V.hom fg =
      pullback.snd (pullback.snd V.hom g) f :=
  MorphismProperty.Over.w ((f.smallEtaleBaseChangeComp g fg hfg).inv.app V)

-- Exposed so that `f.smallEtaleEquivOfIsIso.functor` and `.inverse` unfold to
-- `f.smallEtaleBaseChange` and `(inv f).smallEtaleBaseChange` in the dependent types of
-- `.unitIso` and `.counitIso`.
/-- Base change along an isomorphism `f : X ⟶ Y` is an equivalence `Y.Etale ≌ X.Etale`, with
quasi-inverse `(inv f).smallEtaleBaseChange`. -/
@[expose]
noncomputable def smallEtaleEquivOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Y.Etale ≌ X.Etale where
  functor := f.smallEtaleBaseChange
  inverse := (inv f).smallEtaleBaseChange
  unitIso := (smallEtaleBaseChangeId Y).symm ≪≫
    (inv f).smallEtaleBaseChangeComp f (𝟙 Y) (IsIso.inv_hom_id f).symm
  counitIso := (f.smallEtaleBaseChangeComp (inv f) (𝟙 X) (IsIso.hom_inv_id f).symm).symm ≪≫
    (smallEtaleBaseChangeId X)
  functor_unitIso_comp V := by
    apply f.smallEtaleBaseChange_hom_ext
    let v : V.left ⟶ Y := V.hom
    let u₁ : V.left ⟶ pullback v (𝟙 Y) := ((smallEtaleBaseChangeId Y).inv.app V).left
    let u₂ : pullback v (𝟙 Y) ⟶ pullback (pullback.snd v f) (inv f) :=
      (((inv f).smallEtaleBaseChangeComp f (𝟙 Y) (IsIso.inv_hom_id f).symm).hom.app V).left
    let m : pullback v f ⟶ pullback (pullback.snd (pullback.snd v f) (inv f)) f :=
      (f.smallEtaleBaseChange.map
        ((smallEtaleBaseChangeId Y).inv.app V ≫
          ((inv f).smallEtaleBaseChangeComp f (𝟙 Y) (IsIso.inv_hom_id f).symm).hom.app V)).left
    let ci : pullback (pullback.snd (pullback.snd v f) (inv f)) f ⟶
        pullback (pullback.snd v f) (𝟙 X) :=
      ((f.smallEtaleBaseChangeComp (inv f) (𝟙 X) (IsIso.hom_inv_id f).symm).inv.app
        (f.smallEtaleBaseChange.obj V)).left
    let idX : pullback (pullback.snd v f) (𝟙 X) ⟶ pullback v f :=
      ((smallEtaleBaseChangeId X).hom.app (f.smallEtaleBaseChange.obj V)).left
    have hu₁ : u₁ ≫ pullback.fst v (𝟙 Y) = 𝟙 V.left :=
      (congrArg (· ≫ pullback.fst v (𝟙 Y)) (smallEtaleBaseChangeId_inv_app_left Y V)).trans
        (pullback.lift_fst _ _ _)
    have hu₂ : u₂ ≫ pullback.fst (pullback.snd v f) (inv f) ≫ pullback.fst v f =
        pullback.fst v (𝟙 Y) :=
      (inv f).smallEtaleBaseChangeComp_hom_app_left_fst_fst f (𝟙 Y) (IsIso.inv_hom_id f).symm V
    have hm : m ≫ pullback.fst (pullback.snd (pullback.snd v f) (inv f)) f =
        pullback.fst v f ≫ u₁ ≫ u₂ :=
      f.smallEtaleBaseChange_map_left_fst _
    have hci : ci ≫ pullback.fst (pullback.snd v f) (𝟙 X) =
        pullback.fst (pullback.snd (pullback.snd v f) (inv f)) f ≫
          pullback.fst (pullback.snd v f) (inv f) :=
      f.smallEtaleBaseChangeComp_inv_app_left_fst (inv f) (𝟙 X) (IsIso.hom_inv_id f).symm
        (f.smallEtaleBaseChange.obj V)
    have hidX : idX = pullback.fst (pullback.snd v f) (𝟙 X) :=
      smallEtaleBaseChangeId_hom_app_left X (f.smallEtaleBaseChange.obj V)
    -- Rewrite the composite of `.left` projections on `pullback`-typed factors so `simp` and
    -- `reassoc_of%` can reassociate compositions without unfolding `smallEtaleBaseChange`.
    change (m ≫ ci ≫ idX) ≫ pullback.fst v f = 𝟙 (pullback v f) ≫ pullback.fst v f
    simp [hidX, reassoc_of% hci, reassoc_of% hm, hu₂, hu₁]

/-- The forward functor of `f.smallEtaleEquivOfIsIso` is `f.smallEtaleBaseChange`. -/
@[simp]
theorem smallEtaleEquivOfIsIso_functor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    f.smallEtaleEquivOfIsIso.functor = f.smallEtaleBaseChange :=
  rfl

/-- The inverse functor of `f.smallEtaleEquivOfIsIso` is `(inv f).smallEtaleBaseChange`. -/
@[simp]
theorem smallEtaleEquivOfIsIso_inverse {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    f.smallEtaleEquivOfIsIso.inverse = (inv f).smallEtaleBaseChange :=
  rfl

/-- The unit isomorphism of `f.smallEtaleEquivOfIsIso` compares `𝟙 Y` with `inv f ≫ f`. -/
@[simp]
theorem smallEtaleEquivOfIsIso_unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    f.smallEtaleEquivOfIsIso.unitIso =
      (smallEtaleBaseChangeId Y).symm ≪≫
        (inv f).smallEtaleBaseChangeComp f (𝟙 Y) (IsIso.inv_hom_id f).symm :=
  rfl

/-- The counit isomorphism of `f.smallEtaleEquivOfIsIso` compares `f ≫ inv f` with `𝟙 X`. -/
@[simp]
theorem smallEtaleEquivOfIsIso_counitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    f.smallEtaleEquivOfIsIso.counitIso =
      (f.smallEtaleBaseChangeComp (inv f) (𝟙 X) (IsIso.hom_inv_id f).symm).symm ≪≫
        (smallEtaleBaseChangeId X) :=
  rfl

/-- Base change along an isomorphism `f : X ⟶ Y` is an equivalence of categories. -/
noncomputable instance isEquivalence_smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : f.smallEtaleBaseChange.IsEquivalence :=
  f.smallEtaleEquivOfIsIso.isEquivalence_functor

end AlgebraicGeometry.Scheme.Hom
