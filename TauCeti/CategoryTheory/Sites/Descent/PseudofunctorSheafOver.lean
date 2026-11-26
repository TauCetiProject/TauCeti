/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Over.Basic
public import TauCeti.CategoryTheory.Sites.PseudofunctorSheafOver

/-!
# Sheaves on slices form a stack

Let `(C, J)` be a site. Mathlib's pseudofunctor `J.pseudofunctorOver A`
(`CategoryTheory.GrothendieckTopology.pseudofunctorOver`) sends `U : C` to the category of sheaves
on the slice site `J.over U` with values in `A`, and a morphism `V ⟶ U` to the pullback of
sheaves. This file proves that for sheaves of types it is a stack for `J`
(`CategoryTheory.GrothendieckTopology.isStack_pseudofunctorOver`): morphisms of sheaves glue along
a covering, and every descent datum of sheaves along a covering is effective. This is the stack of
sheaves on which stacks of torsors and quotient stacks are built.

The proof constructs an inverse to the functor from sheaves to descent data. Let `f i : X i ⟶ S`
be a family of morphisms and `D` a descent datum of sheaves along `f`. A *glued section* of `D`
over `T : Over S` (`pseudofunctorOver.GlueSection`) is a family of sections of the sheaves
`D.obj i` over the objects `Z` of `Over (X i)` with a morphism `Z.left ⟶ T.left` over `S`, natural
in `Z` and compatible with the gluing morphisms of `D`.

* Glued sections form a sheaf on `J.over S`, for every family `f`
  (`pseudofunctorOver.isSheaf_gluePresheaf`): this is the glued sheaf `pseudofunctorOver.glue`.
* The restriction of the glued sheaf to `X i` is `D.obj i` (`pseudofunctorOver.glueRestrictIso`),
  so the descent datum of the glued sheaf is `D` (`pseudofunctorOver.glueCompToDescentDataIso`).
* When the family `f` generates a covering sieve, every sheaf on `J.over S` is the glued sheaf of
  its descent datum (`pseudofunctorOver.toDescentDataCompGlueIso`), by the sheaf condition along
  the morphisms `(Over.map (f i)).obj Z ⟶ T`.

Together these give the equivalence `pseudofunctorOver.descentDataEquivalence` between sheaves on
`J.over S` and descent data of sheaves along a covering family `f`. For a family indexed by a type
in the universe `t`, it holds for sheaves with values in `Type (max t u v w)`. The families of
morphisms of a covering sieve are indexed by its arrows, in `Type (max u v)`, so the stack property
holds for sheaves with values in `Type (max u v w)`. For the big site `Over S` of a scheme
`S : Scheme.{u}`, whose objects are in `Type (u + 1)` and morphisms in `Type u`, this covers
sheaves with values in `Type (u + 1)`, for which an instance is provided.

The pseudofunctor `pseudofunctorOver` is Joël Riou's, and the descent data and stacks are
Mathlib's `Pseudofunctor.DescentData` and `Pseudofunctor.IsStack`, by Joël Riou and Christian
Merten.

## References

* [The Stacks Project, Lemmas 7.26.1 and 7.26.4, Tags 04TQ and 04TR][stacks-project], for the
  stack of sheaves of sets on the slices of a site.
-/

public section

universe w' w t v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat TypeCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace pseudofunctorOver

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

variable (D : (J.pseudofunctorOver (Type (max t u v w))).DescentData f)

/-- The sheaf `D.obj i` of a descent datum, as a sheaf on the slice site `J.over (X i)`: the
objects of the category of its presheaf are then those of `Over (X i)` on the nose, which the
statements below use. -/
abbrev sheafObj (i : ι) : Sheaf (J.over (X i)) (Type (max t u v w)) := D.obj i

/-- A *glued section* over `T : Over S` of a descent datum `D` of sheaves along `f` is a family
of sections of the sheaves `D.obj i` over the objects `Z` of `Over (X i)` together with a
morphism `g : Z.left ⟶ T.left` over `S`, natural in `Z` and compatible with the gluing morphisms
of `D`. These are the sections over `T` of the glued sheaf of `D` (`pseudofunctorOver.glue`). -/
@[ext]
structure GlueSection (T : Over S) : Type (max t u v w) where
  /-- The section of `D.obj i` over `Z` attached to `g : Z.left ⟶ T.left`. -/
  val (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T.left) (hg : g ≫ T.hom = Z.hom ≫ f i) :
    (sheafObj D i).obj.obj (op Z)
  /-- The sections are natural in `Z`. -/
  map_val ⦃i : ι⦄ ⦃Z Z' : Over (X i)⦄ (a : Z' ⟶ Z) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) :
    (sheafObj D i).obj.map a.op (val i Z g hg) = val i Z' (a.left ≫ g) (by simp [hg])
  /-- The sections are compatible with the gluing morphisms of `D`. -/
  hom_val ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (Z : Over Y) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ q) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op Z) (val i₁ ((Over.map f₁).obj Z) g (by simp [hg, ← hf₁])) =
      val i₂ ((Over.map f₂).obj Z) g (by simp [hg, ← hf₂])

omit [Category.{v} C] in
/-- Two successive restrictions of a section of a presheaf of types are one restriction. -/
private lemma map_map_eq {E : Type*} [Category* E] {P : Eᵒᵖ ⥤ Type*} {Z Z' Z'' : E} (a : Z' ⟶ Z)
    (b : Z'' ⟶ Z') (c : Z'' ⟶ Z) (h : b ≫ a = c) (x : P.obj (op Z)) :
    P.map b.op (P.map a.op x) = P.map c.op x := by
  subst h
  simp

variable {D} in
/-- The gluing morphisms of a descent datum of sheaves commute with the restrictions along a
morphism `b : Y' ⟶ Y`, up to the identifications of the objects of the slices involved. -/
private lemma hom_app_map {Y Y' : C} (b : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (f₁' : Y' ⟶ X i₁) (f₂' : Y' ⟶ X i₂) (hf₁' : f₁' ≫ f i₁ = q') (hf₂' : f₂' ≫ f i₂ = q')
    (h₁ : b ≫ f₁ = f₁') (h₂ : b ≫ f₂ = f₂') {W : Over Y} {W' : Over Y'} (c : W'.left ⟶ W.left)
    (hc : c ≫ W.hom = W'.hom ≫ b) (x : (sheafObj D i₁).obj.obj (op ((Over.map f₁).obj W))) :
    (sheafObj D i₂).obj.map (Over.homMk c (by simp [← h₂, reassoc_of% hc]) :
        (Over.map f₂').obj W' ⟶ (Over.map f₂).obj W).op
      ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x) =
      (D.hom q' f₁' f₂' hf₁' hf₂').hom.app (op W')
        ((sheafObj D i₁).obj.map (Over.homMk c (by simp [← h₁, reassoc_of% hc]) :
          (Over.map f₁').obj W' ⟶ (Over.map f₁).obj W).op x) := by
  subst h₁ h₂
  have hq : b ≫ q = q' := by rw [← hf₁', ← hf₁, Category.assoc]
  let c' : (Over.map b).obj W' ⟶ W := Over.homMk c (by simpa using hc)
  -- The morphism `D.hom q' _ _` is the pullback of `D.hom q f₁ f₂` along `b`, whose components
  -- are those of `D.hom q f₁ f₂` up to the identifications `Over.homMk (𝟙 _)`.
  have key := pseudofunctorOver_pullHom_hom_app_apply (D.hom q f₁ f₂ hf₁ hf₂) b (b ≫ f₁)
    (b ≫ f₂) rfl rfl W' ((sheafObj D i₁).obj.map (Over.homMk c (by simp [reassoc_of% hc]) :
      (Over.map (b ≫ f₁)).obj W' ⟶ (Over.map f₁).obj W).op x)
  rw [D.pullHom_hom b q q' hq f₁ f₂ hf₁ hf₂ (b ≫ f₁) (b ≫ f₂) rfl rfl] at key
  let e₁ : (Over.map f₁).obj ((Over.map b).obj W') ⟶ (Over.map (b ≫ f₁)).obj W' :=
    Over.homMk (𝟙 _) (by simp)
  let e₂ : (Over.map (b ≫ f₂)).obj W' ⟶ (Over.map f₂).obj ((Over.map b).obj W') :=
    Over.homMk (𝟙 _) (by simp)
  refine Eq.trans ?_ key.symm
  calc _ = (sheafObj D i₂).obj.map e₂.op ((sheafObj D i₂).obj.map ((Over.map f₂).map c').op
          ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x)) :=
        (map_map_eq _ _ _ (by ext; simp [c', e₂]) _).symm
    _ = (sheafObj D i₂).obj.map e₂.op ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op ((Over.map b).obj W'))
          ((sheafObj D i₁).obj.map ((Over.map f₁).map c').op x)) :=
        congrArg (fun z ↦ (sheafObj D i₂).obj.map e₂.op z)
          (NatTrans.naturality_apply (D.hom q f₁ f₂ hf₁ hf₂).hom c'.op x).symm
    _ = (sheafObj D i₂).obj.map e₂.op ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (op ((Over.map b).obj W'))
          ((sheafObj D i₁).obj.map e₁.op ((sheafObj D i₁).obj.map
            (Over.homMk c (by simp [reassoc_of% hc]) :
              (Over.map (b ≫ f₁)).obj W' ⟶ (Over.map f₁).obj W).op x))) := by
        rw [map_map_eq _ _ ((Over.map f₁).map c') (by ext; simp [c', e₁])]

namespace GlueSection

variable {D} {T : Over S}

/-- The section `s.val i Z g hg` depends on `g` only through its value. -/
lemma val_congr (s : GlueSection D T) {i : ι} {Z : Over (X i)} {g g' : Z.left ⟶ T.left}
    (h : g = g') (hg : g ≫ T.hom = Z.hom ≫ f i) :
    s.val i Z g hg = s.val i Z g' (h ▸ hg) := by
  subst h
  rfl

/-- The restriction of a glued section along a morphism `r : T' ⟶ T` of `Over S`. -/
def restrict (s : GlueSection D T) {T' : Over S} (r : T' ⟶ T) : GlueSection D T' where
  val i Z g hg := s.val i Z (g ≫ r.left) (by simp [hg])
  map_val i Z Z' a g hg := by
    rw [s.map_val]
    exact s.val_congr (by simp) _
  hom_val Y q i₁ i₂ f₁ f₂ hf₁ hf₂ Z g hg :=
    s.hom_val q f₁ f₂ hf₁ hf₂ Z (g ≫ r.left) (by simp [hg])

@[simp]
lemma restrict_val (s : GlueSection D T) {T' : Over S} (r : T' ⟶ T) (i : ι) (Z : Over (X i))
    (g : Z.left ⟶ T'.left) (hg : g ≫ T'.hom = Z.hom ≫ f i) :
    (s.restrict r).val i Z g hg = s.val i Z (g ≫ r.left) (by simp [hg]) := (rfl)

end GlueSection

/-- The presheaf on `Over S` of glued sections of `D`. -/
-- Exposed so that the sections of the glued presheaf are glued sections by definition: the
-- statements below take their values `s.val i Z g hg`.
@[expose]
def gluePresheaf : (Over S)ᵒᵖ ⥤ Type (max t u v w) where
  obj T := GlueSection D T.unop
  map r := ↾fun s ↦ s.restrict r.unop
  map_id T := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext s
    ext i Z g hg
    exact s.val_congr (by simp) _
  map_comp r r' := by
    ext s : 3
    ext i Z g hg
    exact s.val_congr (by simp) _

@[simp]
lemma gluePresheaf_map_val {T T' : (Over S)ᵒᵖ} (r : T ⟶ T') (s : (gluePresheaf D).obj T) (i : ι)
    (Z : Over (X i)) (g : Z.left ⟶ T'.unop.left) (hg : g ≫ T'.unop.hom = Z.hom ≫ f i) :
    ((gluePresheaf D).map r s).val i Z g hg = s.val i Z (g ≫ r.unop.left) (by simp [hg]) := (rfl)

section IsSheaf

variable {D} {T : Over S} {R : Sieve T} (hR : R ∈ J.over S T)
  {x : Presieve.FamilyOfElements (gluePresheaf D) R.arrows} (hx : x.Compatible)

include hR in
private lemma isSheafFor_aux (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) :
    Presieve.IsSheafFor ((sheafObj D i).obj)
      ((R.pullback (Over.homMk g (by simpa using hg) : (Over.map (f i)).obj Z ⟶ T)).functorPullback
        (Over.map (f i))).arrows :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (D.obj i).property _
    ((Over.map (f i)).cover_lift (J.over (X i)) (J.over S) ((J.over S).pullback_stable _ hR))

include hx in
private lemma val_eq_val {T' T'' : Over S} (r : T' ⟶ T) (hr : R r) (u : T'' ⟶ T') (r' : T'' ⟶ T)
    (hr' : R r') (e : r' = u ≫ r) (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T''.left)
    (hg : g ≫ T''.hom = Z.hom ≫ f i) :
    (x r' hr').val i Z g hg = (x r hr).val i Z (g ≫ u.left) (by simp [hg]) := by
  subst e
  rw [hx.to_sieveCompatible]
  rfl

/-- The family on the sieve on `Z` whose amalgamation is the value at `(i, Z, g)`. -/
private def amalgFamily (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) :
    Presieve.FamilyOfElements ((sheafObj D i).obj)
      ((R.pullback (Over.homMk g (by simpa using hg) : (Over.map (f i)).obj Z ⟶ T)).functorPullback
        (Over.map (f i))).arrows :=
  fun Z' a ha ↦ (x _ ha).val i Z' (𝟙 _) (by simp)

include hx in
private lemma amalgFamily_compatible (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) : (amalgFamily (x := x) i Z g hg).Compatible := by
  intro Z₁ Z₂ W b₁ b₂ a₁ a₂ h₁ h₂ e
  have := congrArg (fun s : GlueSection D _ ↦ s.val i W (𝟙 _) (by simp))
    (hx ((Over.map (f i)).map b₁) ((Over.map (f i)).map b₂) h₁ h₂ (by
      simp only [← Category.assoc, ← Functor.map_comp, e]))
  simp only [gluePresheaf_map_val] at this
  calc _ = (x _ h₁).val i W (b₁.left ≫ 𝟙 _) _ := (x _ h₁).map_val b₁ _ _
    _ = _ := (GlueSection.val_congr _ (by simp) _).trans this
    _ = (x _ h₂).val i W (b₂.left ≫ 𝟙 _) (by simp) := GlueSection.val_congr _ (by simp) _
    _ = _ := ((x _ h₂).map_val b₂ _ _).symm

/-- The value at `(i, Z, g)` of the amalgamation of a compatible family of glued sections. -/
private noncomputable def amalgVal (i : ι) (Z : Over (X i)) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) : (sheafObj D i).obj.obj (op Z) :=
  (isSheafFor_aux hR i Z g hg).amalgamate _ (amalgFamily_compatible hx i Z g hg)

private lemma amalgVal_congr {i : ι} {Z : Over (X i)} {g g' : Z.left ⟶ T.left} (h : g = g')
    (hg : g ≫ T.hom = Z.hom ≫ f i) :
    amalgVal hR hx i Z g hg = amalgVal hR hx i Z g' (h ▸ hg) := by
  subst h
  rfl

private lemma map_amalgVal {i : ι} {Z Z' : Over (X i)} (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) (a : Z' ⟶ Z)
    (ha : R ((Over.map (f i)).map a ≫ Over.homMk g (by simpa using hg))) :
    (sheafObj D i).obj.map a.op (amalgVal hR hx i Z g hg) = (x _ ha).val i Z' (𝟙 _) (by simp) :=
  (isSheafFor_aux hR i Z g hg).valid_glue _ _ ha

private lemma amalgVal_eq {T' : Over S} (r : T' ⟶ T) (hr : R r) (i : ι) (Z : Over (X i))
    (g : Z.left ⟶ T'.left) (hg : g ≫ T'.hom = Z.hom ≫ f i) :
    amalgVal hR hx i Z (g ≫ r.left) (by simp [hg]) = (x r hr).val i Z g hg := by
  refine (isSheafFor_aux hR i Z (g ≫ r.left) (by simp [hg])).isSeparatedFor.ext
    (fun Z' a ha ↦ ?_)
  rw [map_amalgVal hR hx _ _ a ha, (x r hr).map_val]
  refine (val_eq_val hx r hr (Over.homMk (a.left ≫ g) (by simp [hg])) _ ha
    (by ext; simp) i Z' (𝟙 _) (by simp)).trans (GlueSection.val_congr _ (by simp) _)

private lemma amalgVal_map {i : ι} {Z Z' : Over (X i)} (a : Z' ⟶ Z) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) :
    (sheafObj D i).obj.map a.op (amalgVal hR hx i Z g hg) =
      amalgVal hR hx i Z' (a.left ≫ g) (by simp [hg]) := by
  refine (isSheafFor_aux hR i Z' (a.left ≫ g) (by simp [hg])).isSeparatedFor.ext
    (fun Z'' b hb ↦ ?_)
  have e : (Over.map (f i)).map b ≫ Over.homMk (a.left ≫ g) (by simp [hg]) =
      (Over.map (f i)).map (b ≫ a) ≫ Over.homMk g (by simpa using hg) := by
    ext
    simp
  have hb' : R ((Over.map (f i)).map (b ≫ a) ≫ Over.homMk g (by simpa using hg)) := e ▸ hb
  rw [← Functor.map_comp_apply, ← op_comp, map_amalgVal hR hx _ _ _ hb',
    map_amalgVal hR hx _ _ _ hb]
  exact (val_eq_val hx _ hb (𝟙 _) _ hb' (by simp [e]) i Z'' (𝟙 _) (by simp)).trans
    (GlueSection.val_congr _ (by simp) _)

private lemma amalgVal_hom {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (Z : Over Y) (g : Z.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ q) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op Z)
      (amalgVal hR hx i₁ ((Over.map f₁).obj Z) g (by simp [hg, ← hf₁])) =
      amalgVal hR hx i₂ ((Over.map f₂).obj Z) g (by simp [hg, ← hf₂]) := by
  have hcov := (Over.map q).cover_lift (J.over Y) (J.over S)
    ((J.over S).pullback_stable (Over.homMk g (by simpa using hg) : (Over.map q).obj Z ⟶ T) hR)
  refine ((isSheaf_iff_isSheaf_of_type _ _).1
    ((((J.pseudofunctorOver _).map f₂.op.toLoc).toFunctor.obj (D.obj i₂)).property)
    _ hcov).isSeparatedFor.ext (fun Z' b hb ↦ ?_)
  have h₁ := (amalgVal_map hR hx ((Over.map f₁).map b) g (by simp [hg, ← hf₁])).trans
    ((amalgVal_congr hR hx (by simp) _).trans
      (amalgVal_eq hR hx _ hb i₁ ((Over.map f₁).obj Z') (𝟙 _) (by simp [← hf₁])))
  have h₂ := (amalgVal_map hR hx ((Over.map f₂).map b) g (by simp [hg, ← hf₂])).trans
    ((amalgVal_congr hR hx (by simp) _).trans
      (amalgVal_eq hR hx _ hb i₂ ((Over.map f₂).obj Z') (𝟙 _) (by simp [← hf₂])))
  refine (NatTrans.naturality_apply (D.hom q f₁ f₂ hf₁ hf₂).hom b.op _).symm.trans ?_
  exact (congrArg _ h₁).trans (((x _ hb).hom_val q f₁ f₂ hf₁ hf₂ Z' (𝟙 _) (by simp)).trans
    h₂.symm)

/-- The amalgamation of a compatible family of glued sections. -/
private noncomputable def amalgamation : GlueSection D T where
  val := amalgVal hR hx
  map_val _ _ _ a g hg := amalgVal_map hR hx a g hg
  hom_val _ q _ _ f₁ f₂ hf₁ hf₂ Z g hg := amalgVal_hom hR hx q f₁ f₂ hf₁ hf₂ Z g hg

end IsSheaf

/-- The glued sections of a descent datum of sheaves form a sheaf, for any family `f`. -/
theorem isSheaf_gluePresheaf : Presheaf.IsSheaf (J.over S) (gluePresheaf D) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR x hx
  refine ⟨amalgamation hR hx, fun T' r hr ↦ ?_, fun t ht ↦ ?_⟩
  · refine GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun g ↦ funext fun hg ↦ ?_)
    exact amalgVal_eq hR hx r hr i Z g hg
  · refine GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun g ↦ funext fun hg ↦ ?_)
    refine (isSheafFor_aux hR i Z g hg).isSeparatedFor.ext (fun Z' a ha ↦ ?_)
    refine (t.map_val a g hg).trans (Eq.trans ?_ (map_amalgVal hR hx g hg a ha).symm)
    rw [← ht _ ha, gluePresheaf_map_val]
    exact GlueSection.val_congr _ (by simp) _

variable {D}

private lemma map_homMk_id {i : ι} {Z : Over (X i)} (h) (x : (sheafObj D i).obj.obj (op Z)) :
    (sheafObj D i).obj.map (Over.homMk (𝟙 Z.left) h : Z ⟶ Z).op x = x := by
  rw [show (Over.homMk (𝟙 Z.left) h : Z ⟶ Z) = 𝟙 Z by ext; simp]
  simp

private lemma hom_app_of_eq {Y : C} (q : Y ⟶ S) {i : ι} (f₁ f₂ : Y ⟶ X i) (hf₁ : f₁ ≫ f i = q)
    (hf₂ : f₂ ≫ f i = q) (h : f₁ = f₂) (W : Over Y)
    (x : (sheafObj D i).obj.obj (op ((Over.map f₁).obj W))) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) x =
      (sheafObj D i).obj.map (Over.homMk (𝟙 W.left) (by simp [h]) :
        (Over.map f₂).obj W ⟶ (Over.map f₁).obj W).op x := by
  subst h
  have h := congrArg (fun φ : ((J.pseudofunctorOver _).map f₁.op.toLoc).toFunctor.obj (D.obj i) ⟶
    ((J.pseudofunctorOver _).map f₁.op.toLoc).toFunctor.obj (D.obj i) ↦ φ.hom.app (op W) x)
    (D.hom_self q f₁ hf₁)
  exact h.trans (map_homMk_id _ x).symm

variable (D) in
/-- The value at `(j, Z', g)` of the glued section over `(Over.map (f i)).obj Z` determined by
an element `d` of `D.obj i` over `Z`: the image of `d` under the gluing morphism of `D` over
`Z'.left` for the morphisms `g ≫ Z.hom` and `Z'.hom`. -/
private def transportVal {i : ι} {Z : Over (X i)} (d : (sheafObj D i).obj.obj (op Z)) (j : ι)
    (Z' : Over (X j)) (g : Z'.left ⟶ Z.left) (hg : g ≫ Z.hom ≫ f i = Z'.hom ≫ f j) :
    (sheafObj D j).obj.obj (op Z') :=
  (sheafObj D j).obj.map (Over.homMk (𝟙 Z'.left) (by simp) :
      Z' ⟶ (Over.map Z'.hom).obj (Over.mk (𝟙 Z'.left))).op
    ((D.hom (Z'.hom ≫ f j) (g ≫ Z.hom) Z'.hom (by simpa using hg) rfl).hom.app
      (op (Over.mk (𝟙 Z'.left)))
      ((sheafObj D i).obj.map (Over.homMk g (by simp) :
        (Over.map (g ≫ Z.hom)).obj (Over.mk (𝟙 Z'.left)) ⟶ Z).op d))

private lemma transportVal_map {i : ι} {Z : Over (X i)} (d : (sheafObj D i).obj.obj (op Z)) {j : ι}
    {Z' Z'' : Over (X j)} (a : Z'' ⟶ Z') (g : Z'.left ⟶ Z.left)
    (hg : g ≫ Z.hom ≫ f i = Z'.hom ≫ f j) :
    (sheafObj D j).obj.map a.op (transportVal D d j Z' g hg) =
      transportVal D d j Z'' (a.left ≫ g) (by simp [hg]) := by
  have key := hom_app_map a.left (Z'.hom ≫ f j) (Z''.hom ≫ f j) (g ≫ Z.hom) Z'.hom
    (by simpa using hg) rfl ((a.left ≫ g) ≫ Z.hom) Z''.hom (by simp [hg]) rfl
    (by simp) (Over.w a) (W := Over.mk (𝟙 Z'.left)) (W' := Over.mk (𝟙 Z''.left)) a.left (by simp)
    ((sheafObj D i).obj.map (Over.homMk g (by simp) :
        (Over.map (g ≫ Z.hom)).obj (Over.mk (𝟙 Z'.left)) ⟶ Z).op d)
  let m : Z'' ⟶ (Over.map Z'.hom).obj (Over.mk (𝟙 Z'.left)) := Over.homMk a.left (by simp)
  refine (map_map_eq _ _ m (by ext; simp [m]) _).trans ?_
  refine (map_map_eq (Over.homMk a.left (by simp) : (Over.map Z''.hom).obj (Over.mk (𝟙 Z''.left)) ⟶
      (Over.map Z'.hom).obj (Over.mk (𝟙 Z'.left))) (Over.homMk (𝟙 Z''.left) (by simp) :
      Z'' ⟶ (Over.map Z''.hom).obj (Over.mk (𝟙 Z''.left))) m (by ext; simp [m]) _).symm.trans ?_
  refine congrArg _ (key.trans (congrArg _ ?_))
  exact map_map_eq _ _ _ (by ext; simp) d

private lemma hom_app_congr {Y : C} {M N : (J.pseudofunctorOver (Type w')).obj (.mk (op Y))}
    {φ ψ : M ⟶ N} (h : φ = ψ) (W : (Over Y)ᵒᵖ) (x : M.obj.obj W) :
    φ.hom.app W x = ψ.hom.app W x := by
  rw [h]

private lemma transportVal_hom {i : ι} {Z : Over (X i)} (d : (sheafObj D i).obj.obj (op Z)) {Y : C}
    (q : Y ⟶ S) {j₁ j₂ : ι} (f₁ : Y ⟶ X j₁) (f₂ : Y ⟶ X j₂) (hf₁ : f₁ ≫ f j₁ = q)
    (hf₂ : f₂ ≫ f j₂ = q) (W : Over Y) (g : W.left ⟶ Z.left) (hg : g ≫ Z.hom ≫ f i = W.hom ≫ q) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W)
      (transportVal D d j₁ ((Over.map f₁).obj W) g (by simp [hg, ← hf₁])) =
      transportVal D d j₂ ((Over.map f₂).obj W) g (by simp [hg, ← hf₂]) := by
  let V : Over W.left := Over.mk (𝟙 W.left)
  let y := (sheafObj D i).obj.map (Over.homMk g (by simp [V]) :
    (Over.map (g ≫ Z.hom)).obj V ⟶ Z).op d
  let κ : W ⟶ (Over.map W.hom).obj V := Over.homMk (𝟙 _) (by simp [V])
  let ε₁ : (Over.map f₁).obj ((Over.map W.hom).obj V) ⟶ (Over.map (W.hom ≫ f₁)).obj V :=
    Over.homMk (𝟙 _) (by simp [V])
  let e₂ : (Over.map (W.hom ≫ f₂)).obj V ⟶ (Over.map f₂).obj ((Over.map W.hom).obj V) :=
    Over.homMk (𝟙 _) (by simp [V])
  let k₂ : (Over.map f₂).obj W ⟶ (Over.map (W.hom ≫ f₂)).obj V := Over.homMk (𝟙 _) (by simp [V])
  let H₁ := D.hom ((W.hom ≫ f₁) ≫ f j₁) (g ≫ Z.hom) (W.hom ≫ f₁) (by simp [hg, ← hf₁]) rfl
  let u := (sheafObj D j₁).obj.map ε₁.op (H₁.hom.app (op V) y)
  have key := hom_app_map W.hom q (W.hom ≫ q) f₁ f₂ hf₁ hf₂ (W.hom ≫ f₁) (W.hom ≫ f₂)
    (by simp [hf₁]) (by simp [hf₂]) rfl rfl (W := (Over.map W.hom).obj V) (W' := V) (𝟙 _)
    (by simp [V]) u
  have hw : (sheafObj D j₁).obj.map (Over.homMk (𝟙 _) (by simp [V]) :
      (Over.map (W.hom ≫ f₁)).obj V ⟶ (Over.map f₁).obj ((Over.map W.hom).obj V)).op u =
      H₁.hom.app (op V) y :=
    (map_map_eq _ _ (Over.homMk (𝟙 _) (by simp)) (by ext; simp [ε₁]) _).trans
      (map_homMk_id _ _)
  have hcomp := hom_app_congr (D.hom_comp_hom ((W.hom ≫ f₁) ≫ f j₁) (W.hom ≫ q) (g ≫ Z.hom)
    (W.hom ≫ f₁) (W.hom ≫ f₂) (by simp [hg, ← hf₁]) rfl (by simp [hf₁]) (by simp [hf₂]))
    (op V) y
  have hq := hom_app_congr (D.hom_congr ((W.hom ≫ f₁) ≫ f j₁) ((W.hom ≫ f₂) ≫ f j₂)
    (g ≫ Z.hom) (W.hom ≫ f₂) (by simp [hg, ← hf₁]) (by simp [hf₁, hf₂]) (by simp [hf₁, hf₂]))
    (op V) y
  refine (congrArg (fun z ↦ (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) z)
    (map_map_eq ε₁ ((Over.map f₁).map κ) _ (by ext; simp [ε₁, κ]) _).symm).trans ?_
  refine (NatTrans.naturality_apply (D.hom q f₁ f₂ hf₁ hf₂).hom κ.op u).trans ?_
  refine (map_map_eq e₂ k₂ ((Over.map f₂).map κ) (by ext; simp [e₂, k₂, κ]) _).symm.trans ?_
  exact congrArg (fun z ↦ (sheafObj D j₂).obj.map k₂.op z)
    (key.trans ((congrArg _ hw).trans (hcomp.trans hq)))

private lemma transportVal_self {i : ι} {Z : Over (X i)} (d : (sheafObj D i).obj.obj (op Z)) :
    transportVal D d i Z (𝟙 Z.left) (by simp) = d := by
  refine (congrArg (fun z ↦ (sheafObj D i).obj.map (Over.homMk (𝟙 Z.left) (by simp) :
      Z ⟶ (Over.map Z.hom).obj (Over.mk (𝟙 Z.left))).op z)
    (hom_app_of_eq _ _ _ _ _ (by simp) _ _)).trans ?_
  rw [map_map_eq _ _ (Over.homMk (𝟙 Z.left) (by simp) :
      (Over.map Z.hom).obj (Over.mk (𝟙 Z.left)) ⟶ Z)
    (by ext; simp), map_map_eq _ _ (Over.homMk (𝟙 Z.left) (by simp) : Z ⟶ Z) (by ext; simp),
    map_homMk_id]

variable (D) in
/-- The glued section over `(Over.map (f i)).obj Z` determined by an element of `D.obj i`
over `Z`. -/
private def transport {i : ι} {Z : Over (X i)} (d : (sheafObj D i).obj.obj (op Z)) :
    GlueSection D ((Over.map (f i)).obj Z) where
  val := transportVal D d
  map_val _ _ _ a g hg := transportVal_map d a g hg
  hom_val _ q _ _ f₁ f₂ hf₁ hf₂ W g hg := transportVal_hom d q f₁ f₂ hf₁ hf₂ W g hg

/-- A glued section over `(Over.map (f i)).obj Z` is the transport of its value at
`(i, Z, 𝟙 Z.left)`. -/
private lemma transport_val_id {i : ι} {Z : Over (X i)}
    (s : GlueSection D ((Over.map (f i)).obj Z)) :
    transport D (s.val i Z (𝟙 _) (by simp)) = s := by
  ext j Z' g hg
  let V : Over Z'.left := Over.mk (𝟙 Z'.left)
  have h₁ := s.map_val (Over.homMk g (by simp [V]) : (Over.map (g ≫ Z.hom)).obj V ⟶ Z) (𝟙 _)
    (by simp)
  have h₂ := s.hom_val (Z'.hom ≫ f j) (g ≫ Z.hom) Z'.hom (by simpa using hg) rfl V (g ≫ 𝟙 _)
    (by simpa [V] using hg)
  have h₃ := s.map_val (Over.homMk (𝟙 Z'.left) (by simp [V]) :
    Z' ⟶ (Over.map Z'.hom).obj V) (g ≫ 𝟙 _) (by simpa [V] using hg)
  exact (congrArg (fun z ↦ (sheafObj D j).obj.map (Over.homMk (𝟙 Z'.left) (by simp [V]) :
    Z' ⟶ (Over.map Z'.hom).obj V).op z) ((congrArg _ h₁).trans h₂)).trans
      (h₃.trans (s.val_congr (by simp) _))

variable (D) in
/-- A glued section over `(Over.map (f i)).obj Z` is determined by its value at
`(i, Z, 𝟙 Z.left)`, and every element of `D.obj i` over `Z` is such a value. -/
def restrictEquiv (i : ι) (Z : Over (X i)) :
    GlueSection D ((Over.map (f i)).obj Z) ≃ (sheafObj D i).obj.obj (op Z) where
  toFun s := s.val i Z (𝟙 _) (by simp)
  invFun := transport D
  left_inv := transport_val_id
  right_inv := transportVal_self

@[simp]
lemma restrictEquiv_apply (i : ι) (Z : Over (X i)) (s : GlueSection D ((Over.map (f i)).obj Z)) :
    restrictEquiv D i Z s = s.val i Z (𝟙 _) (by simp) := (rfl)

namespace GlueSection

variable {D' : (J.pseudofunctorOver (Type (max t u v w))).DescentData f} {T : Over S}

/-- The image of a glued section under a morphism of descent data. -/
def map (φ : D ⟶ D') (s : GlueSection D T) : GlueSection D' T where
  val i Z g hg := (φ.hom i).hom.app (op Z) (s.val i Z g hg)
  map_val i Z Z' a g hg :=
    (NatTrans.naturality_apply (φ.hom i).hom a.op _).symm.trans (congrArg _ (s.map_val a g hg))
  hom_val Y q i₁ i₂ f₁ f₂ hf₁ hf₂ W g hg :=
    (hom_app_congr (φ.comm q f₁ f₂ hf₁ hf₂) (op W) (s.val i₁ ((Over.map f₁).obj W) g
      (by simp [hg, ← hf₁]))).trans (congrArg _ (s.hom_val q f₁ f₂ hf₁ hf₂ W g hg))

@[simp]
lemma val_map (φ : D ⟶ D') (s : GlueSection D T) (i : ι) (Z : Over (X i))
    (g : Z.left ⟶ T.left) (hg : g ≫ T.hom = Z.hom ≫ f i) :
    (s.map φ).val i Z g hg = (φ.hom i).hom.app (op Z) (s.val i Z g hg) := (rfl)

end GlueSection

variable (J f) in
/-- Glued sections, as a functor from descent data to presheaves on `Over S`. -/
-- Exposed, like `gluePresheaf`, so that the objects of the image are glued presheaves.
@[expose, simps]
def gluePresheafFunctor : (J.pseudofunctorOver (Type (max t u v w))).DescentData f ⥤
    (Over S)ᵒᵖ ⥤ Type (max t u v w) where
  obj := gluePresheaf
  map φ := { app T := ↾(GlueSection.map φ) }

variable (J f) in
/-- **The glued sheaf of a descent datum**: the sheaf on `J.over S` of glued sections. -/
-- Exposed, like `gluePresheaf`, so that the sections of the glued sheaf are glued sections.
@[expose, simps! obj_obj map_hom]
def glue : (J.pseudofunctorOver (Type (max t u v w))).DescentData f ⥤
    Sheaf (J.over S) (Type (max t u v w)) :=
  ObjectProperty.lift _ (gluePresheafFunctor J f) isSheaf_gluePresheaf

variable (D) in
/-- The restriction of the glued sheaf of `D` to `X i` is `D.obj i`. -/
def glueRestrictIso (i : ι) :
    ((J.pseudofunctorOver _).map (f i).op.toLoc).toFunctor.obj ((glue J f).obj D) ≅ D.obj i :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Z ↦ (restrictEquiv D i Z.unop).toIso)
    (fun {Z Z'} a ↦ by
      ext s
      exact (s.val_congr (by simp) _).trans (s.map_val a.unop (𝟙 _) (by simp)).symm))

@[simp]
lemma glueRestrictIso_hom_hom_app_apply (i : ι) (Z : (Over (X i))ᵒᵖ)
    (s : GlueSection D ((Over.map (f i)).obj Z.unop)) :
    (glueRestrictIso D i).hom.hom.app Z s = s.val i Z.unop (𝟙 _) (by simp) := (rfl)

variable (D) in
/-- The descent datum of the glued sheaf of `D` is `D`. -/
def toDescentDataGlueIso :
    ((J.pseudofunctorOver _).toDescentData f).obj ((glue J f).obj D) ≅ D :=
  DescentData.isoMk (fun i ↦ glueRestrictIso D i) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
    apply ObjectProperty.hom_ext
    ext W s
    refine (s.hom_val q f₁ f₂ hf₁ hf₂ W.unop (𝟙 _) (by simp [hf₁])).trans ?_
    have h := congrArg (fun k ↦ k s) (pseudofunctorOver_toDescentData_obj_hom_hom_app f
      ((glue J f).obj D) q f₁ f₂ hf₁ hf₂ W.unop)
    have h' := (gluePresheaf_map_val D (Over.homMk (𝟙 W.unop.left) (by simp [hf₁, hf₂]) :
      (Over.map (f i₂)).obj ((Over.map f₂).obj W.unop) ⟶
        (Over.map (f i₁)).obj ((Over.map f₁).obj W.unop)).op s i₂ ((Over.map f₂).obj W.unop)
      (𝟙 W.unop.left) (by simp)).trans (s.val_congr (g' := 𝟙 W.unop.left) (by simp) _)
    exact h'.symm.trans
      (congrArg (fun z : GlueSection D ((Over.map (f i₂)).obj ((Over.map f₂).obj W.unop)) ↦
        z.val i₂ ((Over.map f₂).obj W.unop) (𝟙 W.unop.left) (by simp)) h).symm)

@[simp]
lemma toDescentDataGlueIso_hom_hom (i : ι) :
    (toDescentDataGlueIso D).hom.hom i = (glueRestrictIso D i).hom := (rfl)

@[simp]
lemma toDescentDataGlueIso_inv_hom (i : ι) :
    (toDescentDataGlueIso D).inv.hom i = (glueRestrictIso D i).inv := (rfl)

section Unit

variable (M : Sheaf (J.over S) (Type (max t u v w)))

/-- The glued section of the descent datum of `M` determined by a section of `M`: its value
at `(i, Z, g)` is the restriction of the section along `g`. -/
def toGlueSection {T : Over S} (m : M.obj.obj (op T)) :
    GlueSection (((J.pseudofunctorOver _).toDescentData f).obj M) T where
  val i Z g hg := M.obj.map (Over.homMk g (by simpa using hg) : (Over.map (f i)).obj Z ⟶ T).op m
  map_val i Z Z' a g hg := map_map_eq (Over.homMk g (by simpa using hg) :
    (Over.map (f i)).obj Z ⟶ T) ((Over.map (f i)).map a) (Over.homMk (a.left ≫ g) (by simp [hg]))
    (by ext; simp) m
  hom_val Y q i₁ i₂ f₁ f₂ hf₁ hf₂ W g hg :=
    (congrArg (fun k ↦ k (M.obj.map (Over.homMk g (by simp [hg, ← hf₁]) :
      (Over.map (f i₁)).obj ((Over.map f₁).obj W) ⟶ T).op m))
      (pseudofunctorOver_toDescentData_obj_hom_hom_app f M q f₁ f₂ hf₁ hf₂ W)).trans
      (map_map_eq (Over.homMk g (by simp [hg, ← hf₁]) :
        (Over.map (f i₁)).obj ((Over.map f₁).obj W) ⟶ T)
        (Over.homMk (𝟙 W.left) (by simp [hf₁, hf₂]) : (Over.map (f i₂)).obj ((Over.map f₂).obj W) ⟶
          (Over.map (f i₁)).obj ((Over.map f₁).obj W))
        (Over.homMk g (by simp [hg, ← hf₂]) : (Over.map (f i₂)).obj ((Over.map f₂).obj W) ⟶ T)
        (by ext; simp) m)

@[simp]
lemma toGlueSection_val {T : Over S} (m : M.obj.obj (op T)) (i : ι) (Z : Over (X i))
    (g : Z.left ⟶ T.left) (hg : g ≫ T.hom = Z.hom ≫ f i) :
    (toGlueSection (f := f) M m).val i Z g hg =
      M.obj.map (Over.homMk g (by simpa using hg) : (Over.map (f i)).obj Z ⟶ T).op m := (rfl)

/-- The comparison morphism from a sheaf `M` on `J.over S` to the glued presheaf of its
descent datum, sending a section to the family of its restrictions. -/
def toGlue : M.obj ⟶ gluePresheaf (((J.pseudofunctorOver _).toDescentData f).obj M) where
  app T := ↾(toGlueSection M)
  naturality T T' r := by
    ext m
    refine GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun g ↦ funext fun hg ↦ ?_)
    exact (map_map_eq r.unop (Over.homMk g (by simpa using hg) : (Over.map (f i)).obj Z ⟶ T'.unop)
      (Over.homMk (g ≫ r.unop.left) (by simp [hg]) : (Over.map (f i)).obj Z ⟶ T.unop)
      (by ext; simp) m)

@[simp]
lemma toGlue_app_apply {T : (Over S)ᵒᵖ} (m : M.obj.obj T) :
    (toGlue (f := f) M).app T m = toGlueSection M m := (rfl)

variable {M} in
/-- The values of a glued section of the descent datum of `M` are compatible sections of `M`
over the objects `(Over.map (f i)).obj Z`. -/
private lemma GlueSection.map_val_eq_map_val {T : Over S}
    (s : GlueSection (((J.pseudofunctorOver _).toDescentData f).obj M) T)
    {i j : ι} {Z : Over (X i)} {Z' : Over (X j)} (g : Z.left ⟶ T.left) (g' : Z'.left ⟶ T.left)
    (hg : g ≫ T.hom = Z.hom ≫ f i) (hg' : g' ≫ T.hom = Z'.hom ≫ f j) {W : Over S}
    (a : W ⟶ (Over.map (f i)).obj Z) (a' : W ⟶ (Over.map (f j)).obj Z')
    (h : a.left ≫ g = a'.left ≫ g') :
    M.obj.map a.op (s.val i Z g hg) = M.obj.map a'.op (s.val j Z' g' hg') := by
  let V : Over W.left := Over.mk (𝟙 W.left)
  have hf₁ : (a.left ≫ Z.hom) ≫ f i = W.hom := by simpa using Over.w a
  have hf₂ : (a'.left ≫ Z'.hom) ≫ f j = W.hom := by simpa using Over.w a'
  have hf₁' : a.left ≫ Z.hom ≫ f i = W.hom := by simpa using Over.w a
  let ε : W ⟶ (Over.map (f i)).obj ((Over.map (a.left ≫ Z.hom)).obj V) :=
    Over.homMk (𝟙 _) (by simp [V, hf₁])
  let ε' : W ⟶ (Over.map (f j)).obj ((Over.map (a'.left ≫ Z'.hom)).obj V) :=
    Over.homMk (𝟙 _) (by simp [V, hf₂])
  have e₁ := s.map_val (Over.homMk a.left (by simp [V]) :
    (Over.map (a.left ≫ Z.hom)).obj V ⟶ Z) g hg
  have e₂ := s.hom_val W.hom (a.left ≫ Z.hom) (a'.left ≫ Z'.hom) hf₁ hf₂ V (a.left ≫ g)
    (by simp [V, hg, hf₁'])
  have e₃ := s.map_val (Over.homMk a'.left (by simp [V]) :
    (Over.map (a'.left ≫ Z'.hom)).obj V ⟶ Z') g' hg'
  have e₄ := congrArg (fun k ↦ k (s.val i ((Over.map (a.left ≫ Z.hom)).obj V) (a.left ≫ g)
    (by simp [V, hg, hf₁'])))
    (pseudofunctorOver_toDescentData_obj_hom_hom_app f M W.hom (a.left ≫ Z.hom)
      (a'.left ≫ Z'.hom) hf₁ hf₂ V)
  refine (map_map_eq ((Over.map (f i)).map (Over.homMk a.left (by simp [V]) :
    (Over.map (a.left ≫ Z.hom)).obj V ⟶ Z)) ε a (by ext; simp [ε]) _).symm.trans ?_
  refine (congrArg (fun z ↦ M.obj.map ε.op z) e₁).trans ?_
  refine (map_map_eq (Over.homMk (𝟙 _) (by simp [V, hf₁, hf₂]) :
    (Over.map (f j)).obj ((Over.map (a'.left ≫ Z'.hom)).obj V) ⟶
      (Over.map (f i)).obj ((Over.map (a.left ≫ Z.hom)).obj V)) ε' ε (by ext; simp [ε, ε'])
    _).symm.trans ?_
  refine (congrArg (fun z ↦ M.obj.map ε'.op z) (e₄.symm.trans (e₂.trans
    ((s.val_congr h _).trans e₃.symm)))).trans ?_
  exact map_map_eq ((Over.map (f j)).map (Over.homMk a'.left (by simp [V]) :
    (Over.map (a'.left ≫ Z'.hom)).obj V ⟶ Z')) ε' a' (by ext; simp [ε']) _

variable {M} in
/-- When the family `f` generates a covering sieve, every section of `M` over `T` is
determined by its restrictions along the morphisms `(Over.map (f i)).obj Z ⟶ T`, and every
glued section comes from a section of `M`. -/
lemma bijective_toGlue_app (hf : Sieve.ofArrows X f ∈ J S) (T : (Over S)ᵒᵖ) :
    Function.Bijective ((toGlue (f := f) M).app T) := by
  obtain ⟨T⟩ := T
  let K := Σ i : ι, Σ Z : Over (X i), {g : Z.left ⟶ T.left // g ≫ T.hom = Z.hom ≫ f i}
  let ρ : ∀ k : K, (Over.map (f k.fst)).obj k.snd.fst ⟶ T :=
    fun k ↦ Over.homMk k.snd.snd.val (by simpa using k.snd.snd.property)
  -- The morphisms `ρ k` are all the morphisms to `T` from the objects `(Over.map (f i)).obj Z`;
  -- their underlying morphisms cover `T.left`, since the family `f` covers `S`.
  have hcov : Sieve.ofArrows (fun k ↦ ((Over.map (f k.fst)).obj k.snd.fst).left)
      (fun k ↦ (ρ k).left) ∈ J T.left := by
    refine J.superset_covering (fun W h hh ↦ ?_) (J.pullback_stable T.hom hf)
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    exact Sieve.ofArrows_mk _ _ (⟨i, Over.mk a, h, ha⟩ : K)
  have hM := ((isSheaf_iff_isSheaf_of_type _ _).1 M.property).isSheafFor_ofArrows_over ρ hcov
  refine ⟨fun m m' h ↦ hM.isSeparatedFor.ext ?_, fun s ↦ ?_⟩
  · rintro _ _ ⟨k⟩
    exact congrArg (fun s : GlueSection _ T ↦
      s.val k.fst k.snd.fst k.snd.snd.val k.snd.snd.property) h
  · obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hM
      (fun k ↦ s.val k.fst k.snd.fst k.snd.snd.val k.snd.snd.property)
      (fun k k' W a a' h ↦ s.map_val_eq_map_val _ _ _ _ a a' (congrArg Over.Hom.left h))
    exact ⟨t, GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun g ↦ funext fun hg ↦
      ht ⟨i, Z, g, hg⟩)⟩

end Unit

/-- For a covering family, the comparison morphism `toGlue M` is an isomorphism. -/
lemma isIso_toGlue (hf : Sieve.ofArrows X f ∈ J S) (M : Sheaf (J.over S) (Type (max t u v w))) :
    IsIso (toGlue (f := f) M) := by
  have (T : (Over S)ᵒᵖ) : IsIso ((toGlue (f := f) M).app T) :=
    (isIso_iff_bijective _).2 (bijective_toGlue_app hf T)
  exact NatIso.isIso_of_isIso_app _

variable (J f) in
/-- The descent datum of the glued sheaf is the given descent datum, naturally. -/
def glueCompToDescentDataIso :
    glue J f ⋙ (J.pseudofunctorOver (Type (max t u v w))).toDescentData f ≅ 𝟭 _ :=
  NatIso.ofComponents toDescentDataGlueIso (fun φ ↦ by
    ext i : 1
    apply ObjectProperty.hom_ext
    ext Z s
    rfl)

@[simp]
lemma glueCompToDescentDataIso_hom_app
    (D : (J.pseudofunctorOver (Type (max t u v w))).DescentData f) :
    (glueCompToDescentDataIso J f).hom.app D = (toDescentDataGlueIso D).hom := (rfl)

@[simp]
lemma glueCompToDescentDataIso_inv_app
    (D : (J.pseudofunctorOver (Type (max t u v w))).DescentData f) :
    (glueCompToDescentDataIso J f).inv.app D = (toDescentDataGlueIso D).inv := (rfl)

variable (f) in
/-- For a covering family, a sheaf on `J.over S` is the glued sheaf of its descent datum,
naturally. -/
noncomputable def toDescentDataCompGlueIso (hf : Sieve.ofArrows X f ∈ J S) :
    𝟭 _ ≅ (J.pseudofunctorOver (Type (max t u v w))).toDescentData f ⋙ glue J f :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (@asIso _ _ _ _ (toGlue (f := f) M) (isIso_toGlue hf M))) (fun φ ↦ by
    apply ObjectProperty.hom_ext
    ext T m
    refine GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun g ↦ funext fun hg ↦ ?_)
    exact (NatTrans.naturality_apply φ.hom _ m).symm)

@[simp]
lemma toDescentDataCompGlueIso_hom_app_hom (hf : Sieve.ofArrows X f ∈ J S)
    (M : Sheaf (J.over S) (Type (max t u v w))) :
    ((toDescentDataCompGlueIso f hf).hom.app M).hom = toGlue (f := f) M := (rfl)

variable (f) in
/-- **Descent of sheaves.** For a family `f` generating a covering sieve, sheaves on `J.over S`
are equivalent to descent data of sheaves along `f`. -/
noncomputable def descentDataEquivalence (hf : Sieve.ofArrows X f ∈ J S) :
    (J.pseudofunctorOver (Type (max t u v w))).obj (.mk (op S)) ≌
      (J.pseudofunctorOver (Type (max t u v w))).DescentData f :=
  Equivalence.mk _ (glue J f) (toDescentDataCompGlueIso f hf) (glueCompToDescentDataIso J f)

@[simp]
lemma descentDataEquivalence_functor (hf : Sieve.ofArrows X f ∈ J S) :
    (descentDataEquivalence f hf).functor =
      (J.pseudofunctorOver (Type (max t u v w))).toDescentData f := (rfl)

@[simp]
lemma descentDataEquivalence_inverse (hf : Sieve.ofArrows X f ∈ J S) :
    (descentDataEquivalence f hf).inverse = glue J f := (rfl)

end pseudofunctorOver

variable (J)

/-- **Sheaves on slices form a stack** (Stacks Project, Lemmas 7.26.1 and 7.26.4, Tags 04TQ and
04TR, for sheaves of sets): the pseudofunctor `U ↦ Sh(J.over U)` of sheaves of types on the slice
sites is a stack for `J`. Morphisms of sheaves glue along a covering sieve, and every descent
datum of sheaves along a covering sieve is effective. -/
theorem isStack_pseudofunctorOver : (J.pseudofunctorOver (Type (max u v w))).IsStack J :=
  IsStack.of_isStackFor fun _ R hR ↦ ⟨(pseudofunctorOver.descentDataEquivalence _
    (by rwa [Sieve.ofArrows_category])).isEquivalence_functor⟩

/-- `isStack_pseudofunctorOver` for sheaves with values in `Type (max u v)`, as an instance:
for the big site of a scheme `S : Scheme.{u}`, this is the stack of sheaves of types in
`Type (u + 1)`. The universe of `isStack_pseudofunctorOver` cannot be inferred from
`Type (max u v)` by instance search. -/
instance : (J.pseudofunctorOver (Type (max u v))).IsStack J :=
  isStack_pseudofunctorOver.{0} J

end CategoryTheory.GrothendieckTopology

