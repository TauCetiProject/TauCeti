/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Products and base-change factorizations in a slice category

The pullback of two sections over the same base has equal projections to that base.
Consequently a product chart followed by multiplication in a monoid object evaluates as the
product of its two sections. This is useful for restricting group operations to a subscheme
covered by sections.

Multiplicative morphisms between slices over different bases preserve products of points; when
the target is a group object they preserve identities, and between group objects they preserve
inversion. These statements require only a category with pullbacks.

This file also records `CategoryTheory.Over.exists_pullback_snd_comp_eq_of_pullback`: if
the base change of `f : X ⊗ Y ⟶ Z` in `Over S` along `y ≫ Y.hom` factors through the second
projection in `Over R`, then the restriction of `f.left` to the fibre of
`pullback.snd X.hom Y.hom` over `y : R ⟶ Y.left` factors through the projection to `R`.

`CategoryTheory.Over.mapPullbackAdj_homEquiv_symm_smul` identifies the transpose of an action
on base-changed points with the action on their transposes.

Finally, `CategoryTheory.Over.mapGrpPullbackComp` lifts Mathlib's `Over.pullbackComp` to group
objects: base change of group objects along `f ≫ g` is base change along `g` followed by base change
along `f`. `CategoryTheory.Over.mapGrpPullbackCompOfEq` restates it for any `b` with `f ≫ g = b`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace TauCeti.CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

/-- On a product of two section charts, multiplication after a map to a monoid object is the
product of the resulting sections, pulled back from the base. -/
@[reassoc]
theorem pullback_map_comp_mul_left {D G : Over S} [MonObj G] (i : D ⟶ G)
    (a b : 𝟙_ (Over S) ⟶ D) :
    pullback.map (a.left ≫ D.hom) (b.left ≫ D.hom) D.hom D.hom a.left b.left (𝟙 S)
      (Category.comp_id _) (Category.comp_id _) ≫ ((i ⊗ₘ i) ≫ μ[G]).left =
      pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) ≫ ((a ≫ i) * (b ≫ i)).left := by
  have hsb (a : 𝟙_ (Over S) ⟶ D) : a.left ≫ D.hom = 𝟙 S := Over.w a
  have hab : pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) =
      pullback.snd (a.left ≫ D.hom) (b.left ≫ D.hom) := by
    have h := pullback.condition (f := a.left ≫ D.hom) (g := b.left ≫ D.hom)
    simp only [hsb] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
  rw [Hom.mul_def]
  simp only [Over.comp_left, Over.lift_left, Over.tensorHom_left]
  refine (Category.assoc _ _ _).symm.trans ?_
  conv_rhs => rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ (μ[G]).left)
  apply pullback.hom_ext
  · simp [pullback.map, Category.assoc]
  · simp [pullback.map, Category.assoc, hab]

end TauCeti.CategoryTheory.Over

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

open scoped Obj

/-- The transpose along `Over.map p ⊣ Over.pullback p` of `g • y`, for points `g` and `y` of the
base changes of `M` and `Y`, is the action of the transpose of `g` on the transpose of `y`. -/
lemma mapPullbackAdj_homEquiv_symm_smul
    {S' : C} (p : S' ⟶ S) {M Y : Over S} [MonObj M] [ModObj M Y]
    {T : Over S'} (g : T ⟶ (Over.pullback p).obj M) (y : T ⟶ (Over.pullback p).obj Y) :
    letI := (Over.pullback p).modObjObj M Y
    ((Over.mapPullbackAdj p).homEquiv _ _).symm (g • y) =
      ((Over.mapPullbackAdj p).homEquiv _ _).symm g •
        ((Over.mapPullbackAdj p).homEquiv _ _).symm y := by
  let := (Over.pullback p).modObjObj M Y
  have h : ((Over.mapPullbackAdj p).homEquiv _ _).symm
      (lift g y ≫ Functor.LaxMonoidal.μ (Over.pullback p) M Y) =
        lift (((Over.mapPullbackAdj p).homEquiv _ _).symm g)
          (((Over.mapPullbackAdj p).homEquiv _ _).symm y) := by
    ext1
    · rw [lift_fst, ← Adjunction.homEquiv_naturality_right_symm, Category.assoc,
        Functor.Monoidal.μ_fst, lift_fst]
    · rw [lift_snd, ← Adjunction.homEquiv_naturality_right_symm, Category.assoc,
        Functor.Monoidal.μ_snd, lift_snd]
  rw [Hom.smul_def, Hom.smul_def, Functor.modObjObj_smul, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm, h]

/-! ### Multiplicative morphisms between slices over different bases -/

section MulLeftComp

open MonoidalCategory

variable {S' : C} {f : S' ⟶ S} {G : Over S} {G' : Over S'} {g : G'.left ⟶ G.left}
  (w : g ≫ G.hom = G'.hom ≫ f)

/-- **A multiplicative morphism of monoid objects preserves products of points.** If
`g : G' ⟶ G` lies over `f : S' ⟶ S` and is compatible with multiplication, then it carries the
product of two points of `G'` with values in an object `T` over `S'` to the product of their images,
as points of `G` with values in `T` over `f`. -/
theorem mul_left_comp_of_mul_left_comp [MonObj G] [MonObj G']
    (hμ : μ[G'].left ≫ g = Limits.pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
    {T : Over S'} (a b : T ⟶ G') :
    (a * b).left ≫ g =
      Limits.pullback.lift (a.left ≫ g) (b.left ≫ g) (by simp [w]) ≫ μ[G].left := by
  rw [Hom.mul_def, Over.comp_left, Category.assoc, hμ, ← Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext <;> simp

/-- **A multiplicative morphism of monoid objects is multiplicative on points.** If
`g : G' ⟶ G` lies over `f : S' ⟶ S` and is compatible with multiplication, then composing with
`g` carries points of `G'` with values in an object `T` over `S'` to points of `G`
with values in `T` over `f`, and this map preserves products. -/
theorem homMk_mul_left_comp_of_mul_left_comp [MonObj G] [MonObj G']
    (hμ : μ[G'].left ≫ g = Limits.pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
    {T : Over S'} (a b : T ⟶ G') :
    (Over.homMk ((a * b).left ≫ g) (by simp [w]) : Over.mk (T.hom ≫ f) ⟶ G) =
      (Over.homMk (a.left ≫ g) (by simp [w]) : Over.mk (T.hom ≫ f) ⟶ G) *
        (Over.homMk (b.left ≫ g) (by simp [w]) : Over.mk (T.hom ≫ f) ⟶ G) := by
  apply Over.OverMorphism.ext
  simp only [Over.homMk_left, Hom.mul_def, Over.comp_left, Over.lift_left]
  exact mul_left_comp_of_mul_left_comp w hμ a b

/-- **A multiplicative morphism from a monoid object to a group object preserves the identity.**
If `g : G' ⟶ G` lies over `f : S' ⟶ S`, where `G'` is a monoid object and `G` a group object, and
`g` is compatible with multiplication, then it carries the identity section of `G'` to the base
change along `f` of that of `G`. -/
theorem one_left_comp_of_mul_left_comp [GrpObj G] [MonObj G']
    (hμ : μ[G'].left ≫ g = Limits.pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left) :
    η[G'].left ≫ g = f ≫ η[G].left := by
  -- the image of the identity is an idempotent in the group of points of `G` over `f`
  have h := homMk_mul_left_comp_of_mul_left_comp w hμ (1 : 𝟙_ (Over S') ⟶ G') 1
  simp only [_root_.mul_one] at h
  simpa [Hom.one_def] using congr($(mul_eq_left.mp h.symm).left)

/-- **A multiplicative morphism of group objects preserves inversion.** If `g : G' ⟶ G` lies over
`f : S' ⟶ S` and is compatible with multiplication, then it intertwines the inversions of `G'` and
`G`. -/
theorem inv_left_comp_of_mul_left_comp [GrpObj G] [GrpObj G']
    (hμ : μ[G'].left ≫ g = Limits.pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left) :
    ι[G'].left ≫ g = g ≫ ι[G].left := by
  -- `g` and `ι ≫ g` are mutually inverse points of `G` with values in `G'` over `G'.hom ≫ f`
  have h := homMk_mul_left_comp_of_mul_left_comp w hμ (𝟙 G') (𝟙 G')⁻¹
  simp only [_root_.mul_inv_cancel] at h
  have h1 :
      (Over.homMk ((1 : G' ⟶ G').left ≫ g) (by simp [w]) : Over.mk (G'.hom ≫ f) ⟶ G) = 1 := by
    ext
    simp [Hom.one_def, one_left_comp_of_mul_left_comp w hμ]
  simpa [Hom.inv_def] using congr($(eq_inv_of_mul_eq_one_right (h.symm.trans h1)).left)

end MulLeftComp

/-- If the base change of `f : X ⊗ Y ⟶ Z` in `Over S` along `y ≫ Y.hom` factors through the second
projection in `Over R`, then the restriction of `f.left` to the pullback of
`pullback.snd X.hom Y.hom` along `y : R ⟶ Y.left` factors through the projection to `R`. -/
theorem exists_pullback_snd_comp_eq_of_pullback {R : C} {X Y Z : Over S} (f : X ⊗ Y ⟶ Z)
    (y : R ⟶ Y.left)
    {gR : (Over.pullback (y ≫ Y.hom)).obj Y ⟶ (Over.pullback (y ≫ Y.hom)).obj Z}
    (hgR : Functor.LaxMonoidal.μ (Over.pullback (y ≫ Y.hom)) X Y ≫
      (Over.pullback (y ≫ Y.hom)).map f = snd _ _ ≫ gR) :
    ∃ h : R ⟶ Z.left,
      pullback.fst (pullback.snd X.hom Y.hom) y ≫ f.left =
        pullback.snd (pullback.snd X.hom Y.hom) y ≫ h := by
  let c := pullback.snd X.hom Y.hom
  let s := y ≫ Y.hom
  let F : Over S ⥤ Over R := Over.pullback s
  let wX : Limits.pullback c y ⟶ (F.obj X).left :=
    pullback.lift (pullback.fst c y ≫ pullback.fst X.hom Y.hom) (pullback.snd c y)
      (by rw [Category.assoc, pullback.condition, pullback.condition_assoc])
  let yR : R ⟶ (F.obj Y).left := pullback.lift y (𝟙 R) (by simp [s])
  let φ : Limits.pullback c y ⟶ Limits.pullback (F.obj X).hom (F.obj Y).hom :=
    pullback.lift wX (pullback.snd c y ≫ yR) (by simp [F, wX, yR])
  have hμ : φ ≫ (Functor.LaxMonoidal.μ F X Y).left ≫ pullback.fst (X ⊗ Y).hom s =
      pullback.fst c y := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, μ_pullback_left_fst_fst X Y]
      simp [φ, F, wX]
    · rw [Category.assoc, Category.assoc, μ_pullback_left_fst_snd X Y]
      simp [φ, F, yR, c, pullback.condition]
  have hmap : (F.map f).left ≫ pullback.fst Z.hom s = pullback.fst (X ⊗ Y).hom s ≫ f.left := by
    simp [F]
  refine ⟨yR ≫ gR.left ≫ pullback.fst Z.hom s, ?_⟩
  calc pullback.fst c y ≫ f.left
    _ = φ ≫ (Functor.LaxMonoidal.μ F X Y ≫ F.map f).left ≫ pullback.fst Z.hom s := by
      rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc _ _ f.left, ← Category.assoc φ, hμ]
    _ = pullback.snd c y ≫ yR ≫ gR.left ≫ pullback.fst Z.hom s := by
      rw [hgR, Over.comp_left]
      simp [φ, F, s, Category.assoc]

/-- Base change of group objects along a composite `f ≫ g` is base change along `g` followed by
base change along `f`: the lift of `Over.pullbackComp` to group objects. -/
noncomputable def mapGrpPullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Over.pullback (f ≫ g)).mapGrp ≅ (Over.pullback g).mapGrp ⋙ (Over.pullback f).mapGrp :=
  Functor.mapGrpNatIso (Over.pullbackComp f g) ≪≫ Functor.mapGrpCompIso

/-- The morphism in `Over X` underlying a component of `mapGrpPullbackComp` is the corresponding
component of `Over.pullbackComp`. -/
@[simp]
theorem mapGrpPullbackComp_hom_app_hom_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Grp (Over Z)) :
    ((mapGrpPullbackComp f g).hom.app G).hom.hom = (Over.pullbackComp f g).hom.app G.X := by
  -- `Functor.mapGrpCompIso` has identity components, which remain composed on the right.
  simp only [mapGrpPullbackComp, Iso.trans_hom, NatTrans.comp_app, Grp.comp', Mon.comp_hom',
    Functor.mapGrpNatIso_hom_app_hom_hom, Functor.mapGrpCompIso_hom_app_hom_hom]
  exact Category.comp_id _

/-- The morphism in `Over X` underlying a component of the inverse of `mapGrpPullbackComp` is the
corresponding component of the inverse of `Over.pullbackComp`. -/
@[simp]
theorem mapGrpPullbackComp_inv_app_hom_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Grp (Over Z)) :
    ((mapGrpPullbackComp f g).inv.app G).hom.hom = (Over.pullbackComp f g).inv.app G.X := by
  -- `Functor.mapGrpCompIso` has identity components, which remain composed on the left.
  simp only [mapGrpPullbackComp, Iso.trans_inv, NatTrans.comp_app, Grp.comp', Mon.comp_hom',
    Functor.mapGrpCompIso_inv_app_hom_hom, Functor.mapGrpNatIso_inv_app_hom_hom]
  exact Category.id_comp _

/-- Base change of group objects along `a : Y ⟶ Z` followed by base change along `f : X ⟶ Y` is
base change along any `b : X ⟶ Z` with `f ≫ a = b`. For instance, when `Z` is terminal, this
compares base changes of group objects over `Z` along the unique maps to `Z`. -/
noncomputable def mapGrpPullbackCompOfEq {X Y Z : C} (f : X ⟶ Y) {a : Y ⟶ Z} {b : X ⟶ Z}
    (h : f ≫ a = b) :
    (Over.pullback a).mapGrp ⋙ (Over.pullback f).mapGrp ≅ (Over.pullback b).mapGrp :=
  (mapGrpPullbackComp f a).symm ≪≫ Functor.mapGrpNatIso (eqToIso (by congr 1))

/-- The morphism in `Over X` underlying a component of `mapGrpPullbackCompOfEq` is the
corresponding component of the inverse of `Over.pullbackComp`, followed by the identification of
`Over.pullback (f ≫ a)` with `Over.pullback b`. -/
@[simp]
theorem mapGrpPullbackCompOfEq_hom_app_hom_hom {X Y Z : C} (f : X ⟶ Y) {a : Y ⟶ Z} {b : X ⟶ Z}
    (h : f ≫ a = b) (G : Grp (Over Z)) :
    ((mapGrpPullbackCompOfEq f h).hom.app G).hom.hom =
      (Over.pullbackComp f a).inv.app G.X ≫
        (eqToHom (by subst h; rfl) :
          (Over.pullback (f ≫ a)).obj G.X ⟶ (Over.pullback b).obj G.X) := by
  subst h
  simp only [mapGrpPullbackCompOfEq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Grp.comp', Mon.comp_hom', mapGrpPullbackComp_inv_app_hom_hom,
    Functor.mapGrpNatIso_hom_app_hom_hom, eqToIso.hom, eqToHom_refl, NatTrans.id_app]
  -- Both sides are now `(Over.pullbackComp f a).inv.app G.X ≫ 𝟙 _`, up to the unfolding of
  -- `((Over.pullback (f ≫ a)).mapGrp.obj G).X` to `(Over.pullback (f ≫ a)).obj G.X`.
  rfl

/-- The morphism in `Over X` underlying a component of the inverse of `mapGrpPullbackCompOfEq` is
the identification of `Over.pullback b` with `Over.pullback (f ≫ a)`, followed by the
corresponding component of `Over.pullbackComp`. -/
@[simp]
theorem mapGrpPullbackCompOfEq_inv_app_hom_hom {X Y Z : C} (f : X ⟶ Y) {a : Y ⟶ Z} {b : X ⟶ Z}
    (h : f ≫ a = b) (G : Grp (Over Z)) :
    ((mapGrpPullbackCompOfEq f h).inv.app G).hom.hom =
      (eqToHom (by subst h; rfl) :
          (Over.pullback b).obj G.X ⟶ (Over.pullback (f ≫ a)).obj G.X) ≫
        (Over.pullbackComp f a).hom.app G.X := by
  subst h
  simp only [mapGrpPullbackCompOfEq, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Grp.comp', Mon.comp_hom', mapGrpPullbackComp_hom_app_hom_hom,
    Functor.mapGrpNatIso_inv_app_hom_hom, eqToIso.inv, eqToHom_refl, NatTrans.id_app]
  -- Both sides are now `𝟙 _ ≫ (Over.pullbackComp f a).hom.app G.X`, up to the unfolding of
  -- `((Over.pullback (f ≫ a)).mapGrp.obj G).X` to `(Over.pullback (f ≫ a)).obj G.X`.
  rfl

end CategoryTheory.Over
