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
`TauCeti/AlgebraicGeometry/Sites/Etale/Over.lean`, together with base-change comparison
isomorphisms across commutative and Cartesian squares and the resulting contravariant
pseudofunctor on schemes.

Specifically, for composable morphisms `W --f--> X --g--> Y --h--> Z`, the unit and composition
isomorphisms `smallEtaleBaseChangeId X` and `f.smallEtaleBaseChangeComp g` satisfy the
associativity pentagon (`smallEtaleBaseChangeComp_associativity`,
`smallEtaleBaseChange_associativity`) and the left and right unit laws
(`smallEtaleBaseChangeComp_id_comp`, `smallEtaleBaseChange_id_comp`,
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
  rw [← cancel_mono ((f.smallEtaleBaseChangeComp g fg hfg).inv.app (h.smallEtaleBaseChange.obj V) ≫
    (fg.smallEtaleBaseChangeComp h fgh hfgh).inv.app V)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  apply fgh.smallEtaleBaseChange_hom_ext
  let v : V.left ⟶ Z := V.hom
  let a₁ : pullback v fgh ⟶ pullback (pullback.snd v gh) f :=
    ((f.smallEtaleBaseChangeComp gh fgh hfgh').hom.app V).left
  let a₂ : pullback v gh ⟶ pullback (pullback.snd v h) g :=
    ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V).left
  let m : pullback (pullback.snd v gh) f ⟶ pullback (pullback.snd (pullback.snd v h) g) f :=
    (f.smallEtaleBaseChange.map ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V)).left
  let b₂i : pullback (pullback.snd (pullback.snd v h) g) f ⟶ pullback (pullback.snd v h) fg :=
    ((f.smallEtaleBaseChangeComp g fg hfg).inv.app (h.smallEtaleBaseChange.obj V)).left
  let b₁i : pullback (pullback.snd v h) fg ⟶ pullback v fgh :=
    ((fg.smallEtaleBaseChangeComp h fgh hfgh).inv.app V).left
  have ha₁ : a₁ ≫ pullback.fst (pullback.snd v gh) f ≫ pullback.fst v gh = pullback.fst v fgh :=
    f.smallEtaleBaseChangeComp_hom_app_left_fst_fst gh fgh hfgh' V
  have ha₂ : a₂ ≫ pullback.fst (pullback.snd v h) g ≫ pullback.fst v h = pullback.fst v gh :=
    g.smallEtaleBaseChangeComp_hom_app_left_fst_fst h gh hgh V
  have hm : m ≫ pullback.fst (pullback.snd (pullback.snd v h) g) f =
      pullback.fst (pullback.snd v gh) f ≫ a₂ :=
    f.smallEtaleBaseChange_map_left_fst ((g.smallEtaleBaseChangeComp h gh hgh).hom.app V)
  have hb₂i : b₂i ≫ pullback.fst (pullback.snd v h) fg =
      pullback.fst (pullback.snd (pullback.snd v h) g) f ≫ pullback.fst (pullback.snd v h) g :=
    f.smallEtaleBaseChangeComp_inv_app_left_fst g fg hfg (h.smallEtaleBaseChange.obj V)
  have hb₁i : b₁i ≫ pullback.fst v fgh = pullback.fst (pullback.snd v h) fg ≫ pullback.fst v h :=
    fg.smallEtaleBaseChangeComp_inv_app_left_fst h fgh hfgh V
  -- Rewrite the composite of `.left` projections on `pullback`-typed factors so `simp` and
  -- `reassoc_of%` can reassociate compositions without unfolding `smallEtaleBaseChange`.
  change (a₁ ≫ m ≫ b₂i ≫ b₁i) ≫ pullback.fst v fgh = 𝟙 (pullback v fgh) ≫ pullback.fst v fgh
  simp [hb₁i, reassoc_of% hb₂i, reassoc_of% hm, ha₂, ha₁]

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
        f.smallEtaleBaseChange.map ((smallEtaleBaseChangeId Y).hom.app V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  apply f.smallEtaleBaseChange_hom_ext
  exact ((Category.assoc _ _ _).trans <|
    (congrArg (((f.smallEtaleBaseChangeComp (𝟙 Y) f hf).hom.app V).left ≫ ·) <|
      (f.smallEtaleBaseChange_map_left_fst ((smallEtaleBaseChangeId Y).hom.app V)).trans <|
        congrArg (pullback.fst (pullback.snd V.hom (𝟙 Y)) f ≫ ·)
          (smallEtaleBaseChangeId_hom_app_left Y V)).trans <|
      f.smallEtaleBaseChangeComp_hom_app_left_fst_fst (𝟙 Y) f hf V).trans (Category.id_comp _).symm

/-- Right-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChangeComp (𝟙 Y)).hom.app V ≫
        f.smallEtaleBaseChange.map ((smallEtaleBaseChangeId Y).hom.app V) =
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
        (smallEtaleBaseChangeId X).hom.app (f.smallEtaleBaseChange.obj V) =
      𝟙 (f.smallEtaleBaseChange.obj V) := by
  apply f.smallEtaleBaseChange_hom_ext
  exact ((Category.assoc _ _ _).trans <|
    (congrArg (((smallEtaleBaseChangeComp (𝟙 X) f f hf).hom.app V).left ≫ · ≫
        pullback.fst V.hom f)
      (smallEtaleBaseChangeId_hom_app_left X (f.smallEtaleBaseChange.obj V))).trans <|
      smallEtaleBaseChangeComp_hom_app_left_fst_fst (𝟙 X) f f hf V).trans (Category.id_comp _).symm

/-- Left-unit coherence for `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
@[reassoc]
theorem smallEtaleBaseChange_id_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeComp (𝟙 X) f).hom.app V ≫
        (smallEtaleBaseChangeId X).hom.app (f.smallEtaleBaseChange.obj V) =
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
      pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f :=
  (Category.assoc _ _ _).trans <|
    (congrArg (((gX.smallEtaleBaseChangeComp f).inv.app V).left ≫ ·) <|
      (Category.assoc _ _ _).trans <|
        (congrArg (((smallEtaleBaseChangeCongr w).hom.app V).left ≫ ·)
          (f'.smallEtaleBaseChangeComp_hom_app_left_fst_fst g (f' ≫ g) rfl V)).trans <|
          smallEtaleBaseChangeCongr_hom_app_left_fst w V).trans <|
      gX.smallEtaleBaseChangeComp_inv_app_left_fst f (gX ≫ f) rfl V

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
      pullback.snd (pullback.snd V.hom f) gX ≫ f' :=
  (congrArg (((smallEtaleBaseChangeCommSq w).hom.app V).left ≫ ·) pullback.condition).trans <|
    (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ f') (smallEtaleBaseChangeCommSq_hom_app_left_snd w V)

/-- Composing the inverse component of `smallEtaleBaseChangeCommSq w` at `V : Y.Etale` with the two
first projections recovers the two first projections on the opposite path of the square. -/
@[simp]
theorem smallEtaleBaseChangeCommSq_inv_app_left_fst_fst {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) (V : Y.Etale) :
    dsimp% ((smallEtaleBaseChangeCommSq w).inv.app V).left ≫
        pullback.fst (pullback.snd V.hom f) gX ≫ pullback.fst V.hom f =
      pullback.fst (pullback.snd V.hom g) f' ≫ pullback.fst V.hom g :=
  (Category.assoc _ _ _).trans <|
    (congrArg ((((f'.smallEtaleBaseChangeComp g).inv.app V).left ≫
        ((smallEtaleBaseChangeCongr w).inv.app V).left) ≫ ·)
      (gX.smallEtaleBaseChangeComp_hom_app_left_fst_fst f (gX ≫ f) rfl V)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (((f'.smallEtaleBaseChangeComp g).inv.app V).left ≫ ·)
          (smallEtaleBaseChangeCongr_inv_app_left_fst w V)).trans <|
          f'.smallEtaleBaseChangeComp_inv_app_left_fst g (f' ≫ g) rfl V

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
      pullback.snd (pullback.snd V.hom g) f' ≫ gX :=
  (congrArg (((smallEtaleBaseChangeCommSq w).inv.app V).left ≫ ·) pullback.condition).trans <|
    (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ gX) (smallEtaleBaseChangeCommSq_inv_app_left_snd w V)

/-- Transposing a commutative square inverts `smallEtaleBaseChangeCommSq`. -/
theorem smallEtaleBaseChangeCommSq_symm {X' X Y' Y : Scheme.{u}}
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (w : gX ≫ f = f' ≫ g) :
    (smallEtaleBaseChangeCommSq w).symm = smallEtaleBaseChangeCommSq w.symm := by
  simp [smallEtaleBaseChangeCommSq, ← smallEtaleBaseChangeCongr_symm]

/-- Along the trivial identity-base-change square `𝟙 X ≫ f = f ≫ 𝟙 Y`,
`smallEtaleBaseChangeCommSq` reduces to the left and right unit comparisons
`smallEtaleBaseChangeId X` and `smallEtaleBaseChangeId Y`. -/
theorem smallEtaleBaseChangeCommSq_id_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (smallEtaleBaseChangeCommSq
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app V =
      (smallEtaleBaseChangeId X).hom.app (f.smallEtaleBaseChange.obj V) ≫
        f.smallEtaleBaseChange.map ((smallEtaleBaseChangeId Y).inv.app V) := by
  rw [smallEtaleBaseChangeCommSq_def,
    smallEtaleBaseChangeCongr_trans (Category.id_comp f) (Category.comp_id f).symm,
    smallEtaleBaseChangeCongr_symm (Category.comp_id f)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← smallEtaleBaseChange_id_comp_assoc f V, Iso.inv_hom_id_app_assoc]
  congr 1
  have h := congrArg
    ((smallEtaleBaseChangeCongr (Category.comp_id f)).inv.app V ≫ · ≫
      f.smallEtaleBaseChange.map ((smallEtaleBaseChangeId Y).inv.app V))
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
  apply f''.smallEtaleBaseChange_comp_hom_ext (g' ≫ g)
  let v : V.left ⟶ Y := V.hom
  let c₁ : pullback (pullback.snd v f) (gX' ≫ gX) ⟶
      pullback (pullback.snd (pullback.snd v f) gX) gX' :=
    ((gX'.smallEtaleBaseChangeComp gX).hom.app (f.smallEtaleBaseChange.obj V)).left
  let s₁ : pullback (pullback.snd v f) gX ⟶ pullback (pullback.snd v g) f' :=
    ((smallEtaleBaseChangeCommSq w₁).hom.app V).left
  let m₁ : pullback (pullback.snd (pullback.snd v f) gX) gX' ⟶
      pullback (pullback.snd (pullback.snd v g) f') gX' :=
    (gX'.smallEtaleBaseChange.map ((smallEtaleBaseChangeCommSq w₁).hom.app V)).left
  let s₂ : pullback (pullback.snd (pullback.snd v g) f') gX' ⟶
      pullback (pullback.snd (pullback.snd v g) g') f'' :=
    ((smallEtaleBaseChangeCommSq w₂).hom.app (g.smallEtaleBaseChange.obj V)).left
  let ci : pullback (pullback.snd v g) g' ⟶ pullback v (g' ≫ g) :=
    ((g'.smallEtaleBaseChangeComp g).inv.app V).left
  let m₂ : pullback (pullback.snd (pullback.snd v g) g') f'' ⟶
      pullback (pullback.snd v (g' ≫ g)) f'' :=
    (f''.smallEtaleBaseChange.map ((g'.smallEtaleBaseChangeComp g).inv.app V)).left
  let s₁₂ : pullback (pullback.snd v f) (gX' ≫ gX) ⟶ pullback (pullback.snd v (g' ≫ g)) f'' :=
    ((smallEtaleBaseChangeCommSq
      (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc])).hom.app V).left
  have hc₁ : c₁ ≫ pullback.fst (pullback.snd (pullback.snd v f) gX) gX' ≫
      pullback.fst (pullback.snd v f) gX = pullback.fst (pullback.snd v f) (gX' ≫ gX) :=
    gX'.smallEtaleBaseChangeComp_hom_app_left_fst_fst gX (gX' ≫ gX) rfl
      (f.smallEtaleBaseChange.obj V)
  have hs₁ : s₁ ≫ pullback.fst (pullback.snd v g) f' ≫ pullback.fst v g =
      pullback.fst (pullback.snd v f) gX ≫ pullback.fst v f :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst w₁ V
  have hm₁ : m₁ ≫ pullback.fst (pullback.snd (pullback.snd v g) f') gX' =
      pullback.fst (pullback.snd (pullback.snd v f) gX) gX' ≫ s₁ :=
    gX'.smallEtaleBaseChange_map_left_fst ((smallEtaleBaseChangeCommSq w₁).hom.app V)
  have hs₂ : s₂ ≫ pullback.fst (pullback.snd (pullback.snd v g) g') f'' ≫
      pullback.fst (pullback.snd v g) g' =
      pullback.fst (pullback.snd (pullback.snd v g) f') gX' ≫ pullback.fst (pullback.snd v g) f' :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst w₂ (g.smallEtaleBaseChange.obj V)
  have hci : ci ≫ pullback.fst v (g' ≫ g) =
      pullback.fst (pullback.snd v g) g' ≫ pullback.fst v g :=
    g'.smallEtaleBaseChangeComp_inv_app_left_fst g (g' ≫ g) rfl V
  have hm₂ : m₂ ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' =
      pullback.fst (pullback.snd (pullback.snd v g) g') f'' ≫ ci :=
    f''.smallEtaleBaseChange_map_left_fst ((g'.smallEtaleBaseChangeComp g).inv.app V)
  have hs₁₂ : s₁₂ ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' ≫ pullback.fst v (g' ≫ g) =
      pullback.fst (pullback.snd v f) (gX' ≫ gX) ≫ pullback.fst v f :=
    smallEtaleBaseChangeCommSq_hom_app_left_fst_fst
      (by rw [Category.assoc, w₁, ← Category.assoc, w₂, Category.assoc]) V
  -- Rewrite the composite of `.left` projections on `pullback`-typed factors so `simp` and
  -- `reassoc_of%` can reassociate compositions without unfolding `smallEtaleBaseChange`.
  change (c₁ ≫ m₁ ≫ s₂ ≫ m₂) ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' ≫
      pullback.fst v (g' ≫ g) =
    s₁₂ ≫ pullback.fst (pullback.snd v (g' ≫ g)) f'' ≫ pullback.fst v (g' ≫ g)
  simp [hs₁₂, reassoc_of% hm₂, hci, reassoc_of% hs₂, reassoc_of% hm₁, hs₁, reassoc_of% hc₁]

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
    (fun X ↦ Scheme.Hom.smallEtaleBaseChangeId X.unop)
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
`smallEtaleBaseChangeId X.as.unop`. -/
@[simp]
theorem smallEtalePseudofunctor_mapId_hom_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).hom.toNatTrans.app V =
      (Scheme.Hom.smallEtaleBaseChangeId X.as.unop).hom.app V :=
  rfl

/-- The inverse unit comparison of `smallEtalePseudofunctor` at `X` is
`(smallEtaleBaseChangeId X.as.unop).inv`. -/
@[simp]
theorem smallEtalePseudofunctor_mapId_inv_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).inv.toNatTrans.app V =
      (Scheme.Hom.smallEtaleBaseChangeId X.as.unop).inv.app V :=
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
