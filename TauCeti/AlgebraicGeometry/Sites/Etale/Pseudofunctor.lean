/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.BaseChange
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Pseudofunctorial coherence and square comparisons for small étale base change

This file establishes the pseudofunctorial coherence laws for the base-change functors
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` constructed in
`TauCeti/AlgebraicGeometry/Sites/Etale/BaseChange.lean`, together with base-change comparison
isomorphisms across commutative and Cartesian squares and the resulting contravariant
pseudofunctor on schemes.

Specifically, for composable morphisms `W --f--> X --g--> Y --h--> Z`, the unit and composition
isomorphisms `X.smallEtaleBaseChangeId` and `f.smallEtaleBaseChangeComp g` satisfy the associativity
pentagon (`smallEtaleBaseChangeComp_associativity`, `smallEtaleBaseChange_associativity`) and the
left and right unit laws (`smallEtaleBaseChangeComp_id_comp`, `smallEtaleBaseChange_id_comp`,
`smallEtaleBaseChangeComp_comp_id`, `smallEtaleBaseChange_comp_id`). These are packaged via
`CategoryTheory.LocallyDiscrete.mkCatPseudofunctor` as the contravariant pseudofunctor
`TauCeti.AlgebraicGeometry.Scheme.smallEtalePseudofunctor :
  LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}`.

Any commutative square `gX ≫ f = f' ≫ g` induces a natural isomorphism
`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq` between the two iterated base-change
functors (specializing to `f.smallEtaleBaseChangePullback g` on a canonical fibre product),
compatible with identities, transposition, and pasting of squares.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq` and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangePullback`: base-change comparison isomorphisms
  for a commutative square and for a canonical pullback square.
* `TauCeti.AlgebraicGeometry.Scheme.smallEtalePseudofunctor`: the contravariant pseudofunctor
  `LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}` sending `X` to `X.Etale` and `f.op` to
  `f.smallEtaleBaseChange`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_associativity`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_id_comp`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange_comp_id`: pseudofunctorial coherence of
  `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq_symm`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq_id_hom_app`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSq_paste`: compatibility of
  `smallEtaleBaseChangeCommSq` with transposition, identity squares, and pasting.

## References

* The Stacks Project, [Tag 021I](https://stacks.math.columbia.edu/tag/021I) and
  [Tag 021J](https://stacks.math.columbia.edu/tag/021J), the small étale site and functoriality.
-/

public section

open CategoryTheory Bicategory Limits MorphismProperty Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-! ### Pseudofunctorial coherence laws -/

/-- Componentwise associativity of `smallEtaleBaseChangeComp` across any composable triple
`W --f--> X --g--> Y --h--> Z` and arbitrary factorizations. -/
@[reassoc]
theorem smallEtaleBaseChangeComp_associativity {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh)
    (V : Z.Etale) :
    (f.smallEtaleBaseChangeComp gh fgh hfgh').hom.app V ≫
        f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V) =
      (fg.smallEtaleBaseChangeComp h fgh hfgh).hom.app V ≫
        (f.smallEtaleBaseChangeComp g fg hfg).hom.app (h.smallEtaleBaseChange.obj V) := by
  apply Etale.hom_ext
  let v : V.left ⟶ Z := V.hom
  let a₁ : pullback v fgh ⟶ pullback (pullback.snd v gh) f :=
    ((f.smallEtaleBaseChangeComp gh fgh hfgh').hom.app V).left
  let a₂ : pullback v gh ⟶ pullback (pullback.snd v h) g :=
    ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V).left
  let m : pullback (pullback.snd v gh) f ⟶ pullback (pullback.snd (pullback.snd v h) g) f :=
    (f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V)).left
  let b₁ : pullback v fgh ⟶ pullback (pullback.snd v h) fg :=
    ((fg.smallEtaleBaseChangeComp h fgh hfgh).hom.app V).left
  let b₂ : pullback (pullback.snd v h) fg ⟶ pullback (pullback.snd (pullback.snd v h) g) f :=
    ((f.smallEtaleBaseChangeComp g fg hfg).hom.app (h.smallEtaleBaseChange.obj V)).left
  have ha₁_fst : a₁ ≫ pullback.fst (pullback.snd v gh) f ≫ pullback.fst v gh =
      pullback.fst v fgh :=
    f.smallEtaleBaseChangeComp_hom_app_left_fst_fst gh fgh hfgh' V
  have ha₁_snd : a₁ ≫ pullback.snd (pullback.snd v gh) f = pullback.snd v fgh :=
    f.smallEtaleBaseChangeComp_hom_app_left_snd gh fgh hfgh' V
  have ha₂_fst : a₂ ≫ pullback.fst (pullback.snd v h) g ≫ pullback.fst v h = pullback.fst v gh :=
    g.smallEtaleBaseChangeComp_hom_app_left_fst_fst h gh hgh V
  have ha₂_snd : a₂ ≫ pullback.snd (pullback.snd v h) g = pullback.snd v gh :=
    g.smallEtaleBaseChangeComp_hom_app_left_snd h gh hgh V
  have hm_fst : m ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f =
      pullback.fst (pullback.snd v gh) f ≫ a₂ :=
    f.smallEtaleBaseChange_map_left_fst ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V)
  have hm_snd : m ≫ pullback.snd (pullback.snd (pullback.snd v h) g) f =
      pullback.snd (pullback.snd v gh) f :=
    f.smallEtaleBaseChange_map_left_snd ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V)
  have hb₁_fst : b₁ ≫ pullback.fst (pullback.snd v h) fg ≫ pullback.fst v h = pullback.fst v fgh :=
    fg.smallEtaleBaseChangeComp_hom_app_left_fst_fst h fgh hfgh V
  have hb₁_snd : b₁ ≫ pullback.snd (pullback.snd v h) fg = pullback.snd v fgh :=
    fg.smallEtaleBaseChangeComp_hom_app_left_snd h fgh hfgh V
  have hb₂_fst : b₂ ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f ≫
      pullback.fst (pullback.snd v h) g = pullback.fst (pullback.snd v h) fg :=
    f.smallEtaleBaseChangeComp_hom_app_left_fst_fst g fg hfg (h.smallEtaleBaseChange.obj V)
  have hb₂_snd : b₂ ≫ pullback.snd (pullback.snd (pullback.snd v h) g) f =
      pullback.snd (pullback.snd v h) fg :=
    f.smallEtaleBaseChangeComp_hom_app_left_snd g fg hfg (h.smallEtaleBaseChange.obj V)
  change a₁ ≫ m = b₁ ≫ b₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, reassoc_of% hm_fst, ha₂_fst, ha₁_fst,
          Category.assoc, Category.assoc, Category.assoc, reassoc_of% hb₂_fst, hb₁_fst]
      · rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition,
          reassoc_of% hm_fst, reassoc_of% ha₂_snd, pullback.condition_assoc, reassoc_of% ha₁_snd,
          Category.assoc, Category.assoc, Category.assoc, pullback.condition,
          pullback.condition_assoc, reassoc_of% hb₂_snd, reassoc_of% hb₁_snd]
    · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hm_snd,
        reassoc_of% ha₁_snd, Category.assoc, Category.assoc, pullback.condition,
        reassoc_of% hb₂_snd, reassoc_of% hb₁_snd]
  · rw [Category.assoc, hm_snd, ha₁_snd, Category.assoc, hb₂_snd, hb₁_snd]

/-- Associativity pentagon for `smallEtaleBaseChangeComp` across `W --f--> X --g--> Y --h--> Z`. -/
@[reassoc]
theorem smallEtaleBaseChange_associativity {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (V : Z.Etale) :
    (smallEtaleBaseChangeCongr (Category.assoc f g h)).hom.app V ≫
        (f.smallEtaleBaseChangeComp (g ≫ h)).hom.app V ≫
        f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp h).hom.app V) =
      (smallEtaleBaseChangeComp (f ≫ g) h).hom.app V ≫
        (f.smallEtaleBaseChangeComp g).hom.app (h.smallEtaleBaseChange.obj V) := by
  have h' := smallEtaleBaseChangeComp_associativity f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h)
    rfl rfl rfl (Category.assoc f g h) V
  rw [smallEtaleBaseChangeComp_eq_congr_trans f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)] at h'
  simpa [Category.assoc] using h'

/-- Right-unit coherence for `smallEtaleBaseChangeComp` along `f = f ≫ 𝟙 Y`. -/
@[reassoc]
theorem smallEtaleBaseChangeComp_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : f = f ≫ 𝟙 Y)
    (V : Y.Etale) :
    (f.smallEtaleBaseChangeComp (𝟙 Y) f hf).hom.app V ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).hom.app V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  apply Etale.hom_ext
  let v : V.left ⟶ Y := V.hom
  let a : pullback v f ⟶ pullback (pullback.snd v (𝟙 Y)) f :=
    ((f.smallEtaleBaseChangeComp (𝟙 Y) f hf).hom.app V).left
  let m : pullback (pullback.snd v (𝟙 Y)) f ⟶ pullback v f :=
    (f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).hom.app V)).left
  have ha_fst : a ≫ pullback.fst (pullback.snd v (𝟙 Y)) f ≫ pullback.fst v (𝟙 Y) =
      pullback.fst v f :=
    f.smallEtaleBaseChangeComp_hom_app_left_fst_fst (𝟙 Y) f hf V
  have ha_snd : a ≫ pullback.snd (pullback.snd v (𝟙 Y)) f = pullback.snd v f :=
    f.smallEtaleBaseChangeComp_hom_app_left_snd (𝟙 Y) f hf V
  have hm_fst : m ≫ pullback.fst v f =
      pullback.fst (pullback.snd v (𝟙 Y)) f ≫ pullback.fst v (𝟙 Y) := by
    simpa [Y.smallEtaleBaseChangeId_hom_app_left V] using
      f.smallEtaleBaseChange_map_left_fst ((Y.smallEtaleBaseChangeId).hom.app V)
  have hm_snd : m ≫ pullback.snd v f = pullback.snd (pullback.snd v (𝟙 Y)) f :=
    f.smallEtaleBaseChange_map_left_snd ((Y.smallEtaleBaseChangeId).hom.app V)
  change a ≫ m = 𝟙 (pullback v f)
  apply pullback.hom_ext
  · rw [Category.assoc, hm_fst, ha_fst, Category.id_comp]
  · rw [Category.assoc, hm_snd, ha_snd, Category.id_comp]

/-- Right-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChangeComp (𝟙 Y)).hom.app V ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).hom.app V) =
      (smallEtaleBaseChangeCongr (Category.comp_id f)).hom.app V := by
  have h := smallEtaleBaseChangeComp_comp_id f (Category.comp_id f).symm V
  rw [smallEtaleBaseChangeComp_eq_congr_trans f (𝟙 Y) f (Category.comp_id f).symm,
    smallEtaleBaseChangeCongr_symm (Category.comp_id f)] at h
  have h' := congrArg ((smallEtaleBaseChangeCongr (Category.comp_id f)).hom.app V ≫ ·) h
  simpa [Category.assoc] using h'

/-- Left-unit coherence for `smallEtaleBaseChangeComp` along `f = 𝟙 X ≫ f`. -/
@[reassoc]
theorem smallEtaleBaseChangeComp_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : f = 𝟙 X ≫ f)
    (V : Y.Etale) :
    (smallEtaleBaseChangeComp (𝟙 X) f f hf).hom.app V ≫
        (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  apply Etale.hom_ext
  let v : V.left ⟶ Y := V.hom
  let a : pullback v f ⟶ pullback (pullback.snd v f) (𝟙 X) :=
    ((smallEtaleBaseChangeComp (𝟙 X) f f hf).hom.app V).left
  have ha_fst : a ≫ pullback.fst (pullback.snd v f) (𝟙 X) ≫ pullback.fst v f =
      pullback.fst v f :=
    smallEtaleBaseChangeComp_hom_app_left_fst_fst (𝟙 X) f f hf V
  have ha_snd : a ≫ pullback.snd (pullback.snd v f) (𝟙 X) = pullback.snd v f :=
    smallEtaleBaseChangeComp_hom_app_left_snd (𝟙 X) f f hf V
  rw [Etale.comp_left, Etale.id_left, X.smallEtaleBaseChangeId_hom_app_left]
  change a ≫ pullback.fst (pullback.snd v f) (𝟙 X) = 𝟙 (pullback v f)
  apply pullback.hom_ext
  · rw [Category.assoc, ha_fst, Category.id_comp]
  · rw [Category.assoc, pullback.condition, Category.comp_id, ha_snd, Category.id_comp]

/-- Left-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeComp (𝟙 X) f).hom.app V ≫
        (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) =
      (smallEtaleBaseChangeCongr (Category.id_comp f)).hom.app V := by
  have h := smallEtaleBaseChangeComp_id_comp f (Category.id_comp f).symm V
  rw [smallEtaleBaseChangeComp_eq_congr_trans (𝟙 X) f f (Category.id_comp f).symm,
    smallEtaleBaseChangeCongr_symm (Category.id_comp f)] at h
  have h' := congrArg ((smallEtaleBaseChangeCongr (Category.id_comp f)).hom.app V ≫ ·) h
  simpa [Category.assoc] using h'

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

/-- `smallEtaleBaseChangeCommSq w` factors through `(gX.smallEtaleBaseChangeComp f).symm`,
`smallEtaleBaseChangeCongr w`, and `f'.smallEtaleBaseChangeComp g`. -/
theorem smallEtaleBaseChangeCommSq_def {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    smallEtaleBaseChangeCommSq w =
      (gX.smallEtaleBaseChangeComp f).symm ≪≫ smallEtaleBaseChangeCongr w ≪≫
        f'.smallEtaleBaseChangeComp g :=
  (rfl)

/-- Composing the forward component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the two
first projections recovers the two first projections on the opposite path of the square. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_hom_app_left_fst_fst {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f' ≫ pullback.fst V.hom g =
      pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f := by
  let v : V.left ⟶ Y := V.hom
  let a : pullback (pullback.snd v f) gX ⟶ pullback v (gX ≫ f) :=
    ((gX.smallEtaleBaseChangeComp f).inv.app V).left
  let b : pullback v (gX ≫ f) ⟶ pullback v (f' ≫ g) :=
    ((smallEtaleBaseChangeCongr w).hom.app V).left
  let c : pullback v (f' ≫ g) ⟶ pullback (pullback.snd v g) f' :=
    ((f'.smallEtaleBaseChangeComp g).hom.app V).left
  have ha : a ≫ pullback.fst v (gX ≫ f) =
      pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f :=
    gX.smallEtaleBaseChangeComp_inv_app_left_fst f (gX ≫ f) rfl V
  have hb : b ≫ pullback.fst v (f' ≫ g) = pullback.fst v (gX ≫ f) :=
    smallEtaleBaseChangeCongr_hom_app_left_fst w V
  have hc : c ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g =
      pullback.fst v (f' ≫ g) :=
    f'.smallEtaleBaseChangeComp_hom_app_left_fst_fst g (f' ≫ g) rfl V
  change (a ≫ b ≫ c) ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g =
    pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f
  rw [Category.assoc, Category.assoc, hc, hb, ha]

/-- Composing the forward component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
outer second projection to `X'` recovers the outer second projection on the opposite path. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_hom_app_left_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).hom.app V).left ≫
        pullback.snd (pullback.snd V.hom g) f' =
      pullback.snd (pullback.snd V.hom f) gX :=
  MorphismProperty.Over.w ((smallEtaleBaseChangeCommSq w).hom.app V)

/-- Composing the forward component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
middle projection `pullback.fst _ f' ≫ pullback.snd V.hom g` recovers
`pullback.snd _ gX ≫ f'`. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_hom_app_left_fst_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) f' ≫ pullback.snd V.hom g =
      pullback.snd (pullback.snd V.hom f) gX ≫ f' := by
  let v : V.left ⟶ Y := V.hom
  let a : pullback (pullback.snd v f) gX ⟶ pullback (pullback.snd v g) f' :=
    ((smallEtaleBaseChangeCommSq w).hom.app V).left
  have ha : a ≫ pullback.snd (pullback.snd v g) f' = pullback.snd (pullback.snd v f) gX :=
    smallEtaleBaseChangeCommSq_hom_app_left_snd w V
  change a ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.snd v g =
    pullback.snd (pullback.snd v f) gX ≫ f'
  rw [pullback.condition, ← Category.assoc, ha]

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the two
first projections recovers the two first projections on the opposite path of the square. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_fst_fst {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f =
      pullback.fst (pullback.snd V.hom g) f' ≫ pullback.fst V.hom g := by
  let v : V.left ⟶ Y := V.hom
  let a : pullback (pullback.snd v g) f' ⟶ pullback v (f' ≫ g) :=
    ((f'.smallEtaleBaseChangeComp g).inv.app V).left
  let b : pullback v (f' ≫ g) ⟶ pullback v (gX ≫ f) :=
    ((smallEtaleBaseChangeCongr w).inv.app V).left
  let c : pullback v (gX ≫ f) ⟶ pullback (pullback.snd v f) gX :=
    ((gX.smallEtaleBaseChangeComp f).hom.app V).left
  have ha : a ≫ pullback.fst v (f' ≫ g) =
      pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g :=
    f'.smallEtaleBaseChangeComp_inv_app_left_fst g (f' ≫ g) rfl V
  have hb : b ≫ pullback.fst v (gX ≫ f) = pullback.fst v (f' ≫ g) :=
    smallEtaleBaseChangeCongr_inv_app_left_fst w V
  have hc : c ≫ pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f =
      pullback.fst v (gX ≫ f) :=
    gX.smallEtaleBaseChangeComp_hom_app_left_fst_fst f (gX ≫ f) rfl V
  change ((a ≫ b) ≫ c) ≫ pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f =
    pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g
  rw [Category.assoc, hc, Category.assoc, hb, ha]

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
outer second projection to `X'` recovers the outer second projection on the opposite path. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.snd (pullback.snd V.hom f) gX =
      pullback.snd (pullback.snd V.hom g) f' :=
  MorphismProperty.Over.w ((smallEtaleBaseChangeCommSq w).inv.app V)

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the
middle projection `pullback.fst _ gX ≫ pullback.snd V.hom f` recovers
`pullback.snd _ f' ≫ gX`. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_fst_snd {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.fst (pullback.snd V.hom f) gX ≫ pullback.snd V.hom f =
      pullback.snd (pullback.snd V.hom g) f' ≫ gX := by
  let v : V.left ⟶ Y := V.hom
  let a : pullback (pullback.snd v g) f' ⟶ pullback (pullback.snd v f) gX :=
    ((smallEtaleBaseChangeCommSq w).inv.app V).left
  have ha : a ≫ pullback.snd (pullback.snd v f) gX = pullback.snd (pullback.snd v g) f' :=
    smallEtaleBaseChangeCommSq_inv_app_left_snd w V
  change a ≫ pullback.fst (pullback.snd v f) gX ≫ pullback.snd v f =
    pullback.snd (pullback.snd v g) f' ≫ gX
  rw [pullback.condition, ← Category.assoc, ha]

/-- Transposing a commutative square inverts `smallEtaleBaseChangeCommSq`. -/
theorem smallEtaleBaseChangeCommSq_symm {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    (smallEtaleBaseChangeCommSq w).symm = smallEtaleBaseChangeCommSq w.symm := by
  simp [smallEtaleBaseChangeCommSq, ← smallEtaleBaseChangeCongr_symm]

/-- Along the trivial identity-base-change square `𝟙 X ≫ f = f ≫ 𝟙 Y`,
`smallEtaleBaseChangeCommSq` reduces to the left and right unit comparisons
`X.smallEtaleBaseChangeId` and `Y.smallEtaleBaseChangeId`. -/
theorem smallEtaleBaseChangeCommSq_id_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeCommSq
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app V =
      (X.smallEtaleBaseChangeId).hom.app (f.smallEtaleBaseChange.obj V) ≫
        f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).inv.app V) := by
  rw [smallEtaleBaseChangeCommSq_def,
    smallEtaleBaseChangeCongr_trans (Category.id_comp f) (Category.comp_id f).symm,
    smallEtaleBaseChangeCongr_symm (Category.comp_id f)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← smallEtaleBaseChange_id_comp_assoc f V, Iso.inv_hom_id_app_assoc]
  congr 1
  have h := congrArg
    ((smallEtaleBaseChangeCongr (Category.comp_id f)).inv.app V ≫ · ≫
      f.smallEtaleBaseChange.map ((Y.smallEtaleBaseChangeId).inv.app V))
    (smallEtaleBaseChange_comp_id f V)
  simpa [← Functor.map_comp, Category.assoc] using h

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
  apply Etale.hom_ext
  let v : V.left ⟶ Y := V.hom
  let a₁ : pullback (pullback.snd v f) (gX' ≫ gX) ⟶
      pullback (pullback.snd (pullback.snd v f) gX) gX' :=
    ((gX'.smallEtaleBaseChangeComp gX).hom.app (f.smallEtaleBaseChange.obj V)).left
  let a₂ : pullback (pullback.snd (pullback.snd v f) gX) gX' ⟶
      pullback (pullback.snd (pullback.snd v g) f') gX' :=
    (gX'.smallEtaleBaseChange.map ((smallEtaleBaseChangeCommSq w₁).hom.app V)).left
  let a₃ : pullback (pullback.snd (pullback.snd v g) f') gX' ⟶
      pullback (pullback.snd (pullback.snd v g) g') f'' :=
    ((smallEtaleBaseChangeCommSq w₂).hom.app (g.smallEtaleBaseChange.obj V)).left
  let a₄ : pullback (pullback.snd (pullback.snd v g) g') f'' ⟶
      pullback (pullback.snd v (g' ≫ g)) f'' :=
    (f''.smallEtaleBaseChange.map ((g'.smallEtaleBaseChangeComp g).inv.app V)).left
  let c₁ : pullback (pullback.snd v f) gX ⟶ pullback (pullback.snd v g) f' :=
    ((smallEtaleBaseChangeCommSq w₁).hom.app V).left
  let c₂ : pullback (pullback.snd v g) g' ⟶ pullback v (g' ≫ g) :=
    ((g'.smallEtaleBaseChangeComp g).inv.app V).left
  let b : pullback (pullback.snd v f) (gX' ≫ gX) ⟶
      pullback (pullback.snd v (g' ≫ g)) f'' :=
    ((smallEtaleBaseChangeCommSq
      (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc])).hom.app V).left
  have ha₁_fst : a₁ ≫ pullback.fst (pullback.snd (pullback.snd v f) gX) gX' ≫
      pullback.fst (pullback.snd v f) gX = pullback.fst (pullback.snd v f) (gX' ≫ gX) :=
    gX'.smallEtaleBaseChangeComp_hom_app_left_fst_fst gX (gX' ≫ gX) rfl
      (f.smallEtaleBaseChange.obj V)
  have ha₁_snd : a₁ ≫ pullback.snd (pullback.snd (pullback.snd v f) gX) gX' =
      pullback.snd (pullback.snd v f) (gX' ≫ gX) :=
    gX'.smallEtaleBaseChangeComp_hom_app_left_snd gX (gX' ≫ gX) rfl
      (f.smallEtaleBaseChange.obj V)
  have ha₂_fst : a₂ ≫ pullback.fst (pullback.snd (pullback.snd v g) f') gX' =
      pullback.fst (pullback.snd (pullback.snd v f) gX) gX' ≫ c₁ :=
    gX'.smallEtaleBaseChange_map_left_fst ((smallEtaleBaseChangeCommSq w₁).hom.app V)
  have ha₂_snd : a₂ ≫ pullback.snd (pullback.snd (pullback.snd v g) f') gX' =
      pullback.snd (pullback.snd (pullback.snd v f) gX) gX' :=
    gX'.smallEtaleBaseChange_map_left_snd ((smallEtaleBaseChangeCommSq w₁).hom.app V)
  have ha₃_fst : a₃ ≫ pullback.fst (pullback.snd (pullback.snd v g) g') f'' ≫
      pullback.fst (pullback.snd v g) g' =
      pullback.fst (pullback.snd (pullback.snd v g) f') gX' ≫
        pullback.fst (pullback.snd v g) f' :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst w₂ (g.smallEtaleBaseChange.obj V)
  have ha₃_snd : a₃ ≫ pullback.snd (pullback.snd (pullback.snd v g) g') f'' =
      pullback.snd (pullback.snd (pullback.snd v g) f') gX' :=
    smallEtaleBaseChangeCommSq_hom_app_left_snd w₂ (g.smallEtaleBaseChange.obj V)
  have ha₄_fst : a₄ ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' =
      pullback.fst (pullback.snd (pullback.snd v g) g') f'' ≫ c₂ :=
    f''.smallEtaleBaseChange_map_left_fst ((g'.smallEtaleBaseChangeComp g).inv.app V)
  have ha₄_snd : a₄ ≫ pullback.snd (pullback.snd v (g' ≫ g)) f'' =
      pullback.snd (pullback.snd (pullback.snd v g) g') f'' :=
    f''.smallEtaleBaseChange_map_left_snd ((g'.smallEtaleBaseChangeComp g).inv.app V)
  have hc₁ : c₁ ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g =
      pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst w₁ V
  have hc₂ : c₂ ≫ pullback.fst v (g' ≫ g) =
      pullback.fst (pullback.snd v g) g' ≫ pullback.fst v g :=
    g'.smallEtaleBaseChangeComp_inv_app_left_fst g (g' ≫ g) rfl V
  have hb_fst : b ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' ≫ pullback.fst v (g' ≫ g) =
      pullback.fst (pullback.snd v f) (gX' ≫ gX) ≫ pullback.fst v f :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst
      (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc]) V
  have hb_snd : b ≫ pullback.snd (pullback.snd v (g' ≫ g)) f'' =
      pullback.snd (pullback.snd v f) (gX' ≫ gX) :=
    smallEtaleBaseChangeCommSq_hom_app_left_snd
      (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc]) V
  change a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, reassoc_of% ha₄_fst,
        hc₂, reassoc_of% ha₃_fst, reassoc_of% ha₂_fst, hc₁, reassoc_of% ha₁_fst,
        Category.assoc, hb_fst]
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition,
        reassoc_of% ha₄_snd, reassoc_of% ha₃_snd, reassoc_of% ha₂_snd, reassoc_of% ha₁_snd,
        Category.assoc, pullback.condition, reassoc_of% hb_snd]
  · rw [Category.assoc, Category.assoc, Category.assoc, ha₄_snd, ha₃_snd, ha₂_snd, ha₁_snd, hb_snd]

/-- Base-change comparison across the canonical pullback square of `f : X ⟶ Y` and `g : Y' ⟶ Y`:
pulling an étale `Y`-scheme back along `f` and then `pullback.fst f g` is canonically isomorphic to
pulling it back along `g` and then `pullback.snd f g`. -/
noncomputable abbrev smallEtaleBaseChangePullback {X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    f.smallEtaleBaseChange ⋙ smallEtaleBaseChange (pullback.fst f g) ≅
      g.smallEtaleBaseChange ⋙ smallEtaleBaseChange (pullback.snd f g) :=
  smallEtaleBaseChangeCommSq pullback.condition

end AlgebraicGeometry.Scheme.Hom

/-! ### The contravariant small étale pseudofunctor -/

namespace TauCeti.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry

-- Exposed so that `smallEtalePseudofunctor.obj X` and `.map f` unfold to `Cat.of X.as.unop.Etale`
-- and `f.as.unop.smallEtaleBaseChange` for consumers stating componentwise 2-morphism equations.
/-- The contravariant pseudofunctor `LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}` sending each
scheme `X` to its category `X.Etale` of étale `X`-schemes and each morphism `f : X ⟶ Y` to
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`, built via
`CategoryTheory.LocallyDiscrete.mkCatPseudofunctor`. -/
@[expose]
noncomputable def smallEtalePseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkCatPseudofunctor
    (obj := fun X ↦ Cat.of X.unop.Etale)
    (fun f ↦ f.unop.smallEtaleBaseChange)
    (fun X ↦ X.unop.smallEtaleBaseChangeId)
    (fun f g fg hfg ↦ g.unop.smallEtaleBaseChangeComp f.unop fg.unop (Quiver.Hom.op_inj hfg).symm)
    (fun _ _ _ _ _ _ hfg hgh hfgh hfgh' V ↦
      Scheme.Hom.smallEtaleBaseChangeComp_associativity _ _ _ _ _ _
        (Quiver.Hom.op_inj hgh).symm (Quiver.Hom.op_inj hfg).symm
        (Quiver.Hom.op_inj hfgh').symm (Quiver.Hom.op_inj hfgh).symm V)
    (fun _ hf V ↦ Scheme.Hom.smallEtaleBaseChangeComp_comp_id _ (Quiver.Hom.op_inj hf).symm V)
    (fun _ hf V ↦ Scheme.Hom.smallEtaleBaseChangeComp_id_comp _ (Quiver.Hom.op_inj hf).symm V)

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
      ((g.as.unop.smallEtaleBaseChangeComp f.as.unop).hom.app V) :=
  rfl

/-- The inverse composition comparison of `smallEtalePseudofunctor` at `f, g` agrees with
`(smallEtaleBaseChangeComp _ _).inv`. -/
@[simp]
theorem smallEtalePseudofunctor_mapComp_inv_toNatTrans_app {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapComp f g).inv.toNatTrans.app V =
      ((g.as.unop.smallEtaleBaseChangeComp f.as.unop).inv.app V) :=
  rfl

end TauCeti.AlgebraicGeometry.Scheme
