/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.PseudofunctorSheafOver
public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Over

/-!
# The stack of torsors

Let `G` be a sheaf of groups on a site `(C, J)`. This file proves that the pseudofunctor of
torsors `CategoryTheory.Sheaf.torsorPseudofunctor G`, whose fibre over `U` is the groupoid of
torsors under the restriction `G.over U` of `G` to the slice site `J.over U`
(`TauCeti.CategoryTheory.Sites.NonabelianCohomology.Over`), is a stack for `J`
(`CategoryTheory.Sheaf.isStack_torsorPseudofunctor`), and indeed a gerbe
(`CategoryTheory.Sheaf.isGerbe_torsorPseudofunctor`): its fibres are groupoids, the trivial torsor
is an object over every `U`, and any two torsors over `U` are isomorphic over the arrows of a
covering sieve. This is the stack `BG` of torsors under `G`.

The proof deduces the descent of torsors from the descent of sheaves on slices
(`GrothendieckTopology.isStack_pseudofunctorOver`). Let `f i : X i ⟶ S` be a family generating a
covering sieve and `D` a descent datum of torsors along `f`. Forgetting the actions gives a
descent datum of sheaves (`torsorPseudofunctor.toSheafDescentData`), whose glued sheaf
(`GrothendieckTopology.pseudofunctorOver.glue`) has as sections over `T` the glued sections, that
is the compatible families of sections of the `D.obj i`.

* The sections of `G` over `T.left` act on the glued sections componentwise
  (`torsorPseudofunctor.smulGlueSection`), because the gluing morphisms of `D` are equivariant.
* The glued sections are locally nonempty, because the torsors `D.obj i` are, and the action is
  simply transitive: the differences of two glued sections at the components glue to a section of
  `G`, as `G` is a sheaf. So the glued sheaf is a torsor (`torsorPseudofunctor.glueTorsor`), whose
  descent datum is `D` (`torsorPseudofunctor.toDescentDataGlueTorsorIso`).
* Morphisms of torsors glue: a morphism of descent data of torsors glues to a morphism of the
  underlying sheaves, which is equivariant because it is so after restriction to the `X i` and a
  section of a sheaf is determined by its restrictions to the `X i`.

As for sheaves on slices, the descent holds along families indexed by a type in the universe `t`
for sheaves of groups with values in `Type (max t u v w)`, and the stack property for sheaves of
groups with values in `Type (max u v w)`. For the big site `Over S` of a scheme `S : Scheme.{u}`,
whose objects are in `Type (u + 1)` and morphisms in `Type u`, this covers the sheaves of groups
with values in `Type (u + 1)`, for which instances are provided.

## Main declarations

* `CategoryTheory.Sheaf.torsorPseudofunctor.glueTorsor`: the torsor glued from a descent datum of
  torsors along a covering family.
* `CategoryTheory.Sheaf.torsorPseudofunctor.isEquivalence_toDescentData`: descent of torsors
  along a covering family.
* `CategoryTheory.Sheaf.isStack_torsorPseudofunctor`: torsors form a stack.
* `CategoryTheory.Sheaf.isGerbe_torsorPseudofunctor`: the stack of torsors is a gerbe, with an
  instance for sheaves of groups with values in `Type (max u v)`.

The descent data, prestacks and stacks are Mathlib's `Pseudofunctor.DescentData`,
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`, by Joël Riou and Christian Merten.

## References

* [Jean Giraud, *Cohomologie non abélienne*][giraud1971], Chapitre III, for the stack of torsors
  under a sheaf of groups.
-/

public section

universe w t v u

namespace CategoryTheory.Sheaf

open Opposite Bicategory Pseudofunctor GrothendieckTopology pseudofunctorOver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace torsorPseudofunctor

variable {G : Sheaf J GrpCat.{max t u v w}} {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

variable (f) in
/-- The descent datum of sheaves underlying a descent datum of torsors. -/
abbrev toSheafDescentData : (torsorPseudofunctor G).DescentData f ⥤
    (J.pseudofunctorOver (Type (max t u v w))).DescentData f :=
  (torsorPseudofunctorForget G).mapDescentData f

/-- The gluing morphisms of the descent datum of sheaves underlying a descent datum of torsors
are those of the torsors. -/
lemma toSheafDescentData_obj_hom (D : (torsorPseudofunctor G).DescentData f) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((toSheafDescentData f).obj D).hom q f₁ f₂ hf₁ hf₂ = (D.hom q f₁ f₂ hf₁ hf₂).hom := by
  rw [StrongTrans.mapDescentData_obj_hom, StrongTrans.mapPullHom_def]
  rfl

section Glue

variable (D : (torsorPseudofunctor G).DescentData f)

-- The values of a glued section of the descent datum of sheaves underlying `D` are typed by its
-- objects, which are the sheaves of the torsors `D.obj i` only by definition, and the sections of
-- `G.over (X i)` over `Z` are those of `G` over `Z.left` only by definition. Instance search does
-- not see through these identifications, so below the values and the group elements are retyped
-- with `show` before the action of the torsor `torsorObj D i` is applied to them, and
-- `Sheaf.over_obj_map_apply` identifies restrictions of sections of `G.over (X i)` with those of
-- `G`.

/-- The torsor `D.obj i` of a descent datum, as a torsor under `G.over (X i)`: its group of
sections over `Z` is then that of `G.over (X i)` on the nose, which the statements below use. -/
abbrev torsorObj (i : ι) : Torsor (G.over (X i)) := D.obj i

/-- The action of a section `g` of `G` over `T.left` on a glued section of the descent datum of
sheaves underlying `D`: componentwise, by the restrictions of `g`. -/
def smulGlueSection {T : Over S} (g : (G.over S).obj.obj (op T))
    (s : GlueSection ((toSheafDescentData f).obj D) T) :
    GlueSection ((toSheafDescentData f).obj D) T where
  val i Z h hh := (show (G.over (X i)).obj.obj (op Z) from G.obj.map h.op g) •
    (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh)
  map_val i Z Z' a h hh := by
    refine ((torsorObj D i).map_smul a.op _ _).trans
      (congrArg₂ (fun (y : (G.over (X i)).obj.obj (op Z'))
        (x : (torsorObj D i).sheaf.obj.obj (op Z')) ↦ y • x) ?_ (s.map_val a h hh))
    exact (over_obj_map_apply G a.op _).trans (Functor.map_comp_apply G.obj h.op a.left.op g).symm
  hom_val Y q i₁ i₂ f₁ f₂ hf₁ hf₂ Z h hh := by
    have e := s.hom_val q f₁ f₂ hf₁ hf₂ Z h hh
    rw [toSheafDescentData_obj_hom] at e ⊢
    exact ((D.hom q f₁ f₂ hf₁ hf₂).map_smul (op Z) _ _).trans
      (congrArg (fun x : (torsorObj D i₂).sheaf.obj.obj (op ((Over.map f₂).obj Z)) ↦
        (show (G.over (X i₂)).obj.obj (op ((Over.map f₂).obj Z)) from G.obj.map h.op g) • x) e)

/-- The action of a section of `G` on a glued section is componentwise. -/
lemma smulGlueSection_val {T : Over S} (g : (G.over S).obj.obj (op T))
    (s : GlueSection ((toSheafDescentData f).obj D) T) (i : ι) (Z : Over (X i))
    (h : Z.left ⟶ T.left) (hh : h ≫ T.hom = Z.hom ≫ f i) :
    (show (torsorObj D i).sheaf.obj.obj (op Z) from (smulGlueSection D g s).val i Z h hh) =
      (show (G.over (X i)).obj.obj (op Z) from G.obj.map h.op g) •
        (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh) :=
  (rfl)

/-- The action of the sections of `G` over `T.left` on the glued sections over `T`, by
`smulGlueSection`. The body is exposed so that the action is `smulGlueSection` by definition. -/
@[implicit_reducible, expose]
def glueMulAction (T : Over S) :
    MulAction ((G.over S).obj.obj (op T)) (GlueSection ((toSheafDescentData f).obj D) T) where
  smul := smulGlueSection D
  one_smul s := GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun h ↦ funext fun hh ↦ by
    refine (smulGlueSection_val D 1 s i Z h hh).trans ?_
    refine (congrArg (fun y : (G.over (X i)).obj.obj (op Z) ↦
      y • (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh))
        (map_one (G.obj.map h.op).hom)).trans ?_
    exact one_smul _ _)
  mul_smul g g' s := GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun h ↦
    funext fun hh ↦ by
    refine (smulGlueSection_val D (g * g') s i Z h hh).trans ?_
    refine (congrArg (fun y : (G.over (X i)).obj.obj (op Z) ↦
      y • (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh))
        (map_mul (G.obj.map h.op).hom g g')).trans ?_
    exact mul_smul _ _ _)

variable {D}

/-- A relation `e • s = t` between the values of two glued sections at `(i, Z, h)` restricts
along a morphism `b : Z₂ ⟶ Z` of `Over (X i)`. -/
private lemma smul_val_map {T : Over S} {s t : GlueSection ((toSheafDescentData f).obj D) T}
    {i : ι} {Z Z₂ : Over (X i)} (b : Z₂ ⟶ Z) (h : Z.left ⟶ T.left)
    (hh : h ≫ T.hom = Z.hom ≫ f i) (e : (G.over (X i)).obj.obj (op Z))
    (H : e • (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh) =
      t.val i Z h hh) :
    (show (G.over (X i)).obj.obj (op Z₂) from (G.over (X i)).obj.map b.op e) •
        (show (torsorObj D i).sheaf.obj.obj (op Z₂) from s.val i Z₂ (b.left ≫ h) (by simp [hh])) =
      t.val i Z₂ (b.left ≫ h) (by simp [hh]) := by
  rw [← s.map_val b h hh, ← t.map_val b h hh, ← H]
  exact ((torsorObj D i).map_smul b.op e _).symm

/-- A relation `e • s = t` between the values of two glued sections is transported by the gluing
morphisms of `D`, which are equivariant. -/
private lemma smul_val_hom {T : Over S} {s t : GlueSection ((toSheafDescentData f).obj D) T}
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (W : Over Y) (h : W.left ⟶ T.left) (hh : h ≫ T.hom = W.hom ≫ q)
    (e : G.obj.obj (op W.left))
    (H : (show (G.over (X i₁)).obj.obj (op ((Over.map f₁).obj W)) from e) •
      (show (torsorObj D i₁).sheaf.obj.obj (op ((Over.map f₁).obj W)) from
        s.val i₁ ((Over.map f₁).obj W) h (by simp [hh, ← hf₁])) =
      t.val i₁ ((Over.map f₁).obj W) h (by simp [hh, ← hf₁])) :
    (show (G.over (X i₂)).obj.obj (op ((Over.map f₂).obj W)) from e) •
      (show (torsorObj D i₂).sheaf.obj.obj (op ((Over.map f₂).obj W)) from
        s.val i₂ ((Over.map f₂).obj W) h (by simp [hh, ← hf₂])) =
      t.val i₂ ((Over.map f₂).obj W) h (by simp [hh, ← hf₂]) := by
  rw [← s.hom_val q f₁ f₂ hf₁ hf₂ W h hh, ← t.hom_val q f₁ f₂ hf₁ hf₂ W h hh, ← H,
    toSheafDescentData_obj_hom]
  exact ((D.hom q f₁ f₂ hf₁ hf₂).map_smul (op W) e _).symm

/-- The differences of the values of two glued sections are compatible: for `c : Z'.left ⟶ Z.left`
with `c ≫ h = h'`, the restriction along `c` of the difference at `(i, Z, h)` is the difference at
`(i', Z', h')`. -/
private lemma map_diff_val {T : Over S} (s t : GlueSection ((toSheafDescentData f).obj D) T)
    {i i' : ι} (Z : Over (X i)) (Z' : Over (X i')) (h : Z.left ⟶ T.left)
    (h' : Z'.left ⟶ T.left) (hh : h ≫ T.hom = Z.hom ≫ f i) (hh' : h' ≫ T.hom = Z'.hom ≫ f i')
    (c : Z'.left ⟶ Z.left) (hc : c ≫ h = h') :
    G.obj.map c.op ((torsorObj D i).diff (U := op Z) (t.val i Z h hh) (s.val i Z h hh)) =
      (torsorObj D i').diff (U := op Z') (t.val i' Z' h' hh') (s.val i' Z' h' hh') := by
  subst hc
  let W : Over Z'.left := Over.mk (𝟙 _)
  have hA := smul_val_map (b := (Over.homMk c (by simp [W]) : (Over.map (c ≫ Z.hom)).obj W ⟶ Z))
    h hh _ (Torsor.diff_smul_self (torsorObj D i) (U := op Z) (t.val i Z h hh) (s.val i Z h hh))
  have hB := smul_val_hom (D := D) (s := s) (t := t) ((c ≫ h) ≫ T.hom) (c ≫ Z.hom) Z'.hom
    (by simp [hh]) hh'.symm W (c ≫ h) (by simp [W]) _ hA
  -- The difference at `(Over.map Z'.hom).obj W` restricts, along a morphism `b` from `Z'` whose
  -- underlying morphism of `C` is an identity, to the difference at `Z'`.
  let b : Z' ⟶ (Over.map Z'.hom).obj W := Over.homMk (𝟙 Z'.left) (by simp [W])
  refine (over_obj_map_apply_of_left_eq_id G b rfl _).symm.trans
    ((congrArg ((G.over (X i')).obj.map b.op) ((torsorObj D i').eq_diff_of_smul_eq hB)).trans
      (((torsorObj D i').map_diff b.op _ _).trans ?_))
  exact congrArg₂ (torsorObj D i').diff
    ((t.map_val b (c ≫ h) _).trans (t.val_congr (Category.id_comp _) _))
    ((s.map_val b (c ≫ h) _).trans (s.val_congr (Category.id_comp _) _))

variable (D)

/-- For a covering family, the glued sections are locally nonempty: over the objects of `Over S`
lying over some `X i`, they are the sections of `D.obj i`, which are locally nonempty. -/
lemma coversTop_glue (hf : Sieve.ofArrows X f ∈ J S) :
    (J.over S).CoversTop fun T : {T : Over S //
      Nonempty (GlueSection ((toSheafDescentData f).obj D) T)} ↦ T.val := by
  intro T
  rw [mem_over_iff]
  refine J.transitive (J.pullback_stable T.hom hf) _ fun Y k hk ↦ ?_
  rw [Sieve.pullback_apply] at hk
  obtain ⟨i, m, hm⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  have hZ := (torsorObj D i).coversTop (Over.mk m)
  rw [mem_over_iff] at hZ
  refine J.superset_covering ?_ hZ
  intro Y' l hl
  rw [Sieve.overEquiv_iff] at hl
  obtain ⟨⟨Z₁, ⟨x⟩⟩, ⟨b⟩⟩ := hl
  rw [Sieve.pullback_apply, Sieve.overEquiv_iff]
  exact ⟨⟨(Over.map (f i)).obj (Over.mk (l ≫ m)),
    ⟨(restrictEquiv _ i _).symm ((torsorObj D i).sheaf.obj.map b.op x)⟩⟩,
    ⟨Over.homMk (𝟙 _) (by simp [hm])⟩⟩

/-- For a covering family, the action of `G` on the glued sections over `T` is free: a section of
`G` over `T.left` fixing a glued section fixes its values, so its restrictions to the arrows of
the pullback of the covering sieve are trivial, and it is trivial since `G` is separated. -/
lemma smulGlueSection_left_injective (hf : Sieve.ofArrows X f ∈ J S) {T : Over S}
    (s : GlueSection ((toSheafDescentData f).obj D) T) :
    Function.Injective fun g : (G.over S).obj.obj (op T) ↦ smulGlueSection D g s := by
  have hG := (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget GrpCat)).obj G).property _
    (J.pullback_stable T.hom hf)
  intro g g' he
  refine hG.isSeparatedFor.ext fun Y k hk ↦ ?_
  rw [Sieve.pullback_apply] at hk
  obtain ⟨i, m, hm⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  have := congrArg (fun z : GlueSection ((toSheafDescentData f).obj D) T ↦
    (show (torsorObj D i).sheaf.obj.obj (op (Over.mk m)) from z.val i (Over.mk m) k hm)) he
  exact (torsorObj D i).smul_left_injective _ this

/-- For a covering family, the action of `G` on the glued sections over `T` is transitive: two
glued sections differ, at each `(i, Z, h)`, by a unique section of `G` over `Z.left`, and these
differences glue to a section of `G` over `T.left` by the sheaf condition for the pullback of the
covering sieve. -/
lemma exists_smulGlueSection_eq (hf : Sieve.ofArrows X f ∈ J S) {T : Over S}
    (s t : GlueSection ((toSheafDescentData f).obj D) T) :
    ∃ g : (G.over S).obj.obj (op T), smulGlueSection D g s = t := by
  have hG := (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget GrpCat)).obj G).property _
    (J.pullback_stable T.hom hf)
  choose idx mor fac using fun (Y : C) (k : Y ⟶ T.left)
    (hk : ((Sieve.ofArrows X f).pullback T.hom).arrows k) ↦
      (Sieve.mem_ofArrows_iff X f (k ≫ T.hom)).1 hk
  let x : Presieve.FamilyOfElements (G.obj ⋙ forget GrpCat)
      ((Sieve.ofArrows X f).pullback T.hom).arrows := fun Y k hk ↦
    (torsorObj D (idx Y k hk)).diff (U := op (Over.mk (mor Y k hk)))
      (t.val _ (Over.mk (mor Y k hk)) k (fac Y k hk))
      (s.val _ (Over.mk (mor Y k hk)) k (fac Y k hk))
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ comm
    have hh : (g₁ ≫ k₁) ≫ T.hom = (Over.mk (g₁ ≫ mor Y₁ k₁ hk₁)).hom ≫ f (idx Y₁ k₁ hk₁) := by
      simp [fac Y₁ k₁ hk₁]
    exact (map_diff_val s t (Over.mk (mor Y₁ k₁ hk₁)) (Over.mk (g₁ ≫ mor Y₁ k₁ hk₁)) _ _ _ hh
      g₁ rfl).trans (map_diff_val s t (Over.mk (mor Y₂ k₂ hk₂))
        (Over.mk (g₁ ≫ mor Y₁ k₁ hk₁)) _ _ _ hh g₂ comm.symm).symm
  refine ⟨hG.amalgamate x hx,
    GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun h ↦ funext fun hh ↦ ?_)⟩
  have hk : ((Sieve.ofArrows X f).pullback T.hom).arrows h := by
    rw [Sieve.pullback_apply, hh]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk X f i) _
  have E : G.obj.map h.op (hG.amalgamate x hx) =
      (torsorObj D i).diff (U := op Z) (t.val i Z h hh) (s.val i Z h hh) := by
    refine (hG.valid_glue hx h hk).trans ?_
    refine Eq.trans ?_ (map_diff_val s t (Over.mk (mor _ h hk)) Z h h (fac _ h hk) hh (𝟙 _)
      (Category.id_comp h))
    exact (Functor.map_id_apply G.obj _ _).symm
  exact (smulGlueSection_val D _ s i Z h hh).trans
    ((congrArg (fun y : (G.over (X i)).obj.obj (op Z) ↦
      y • (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z h hh)) E).trans
        (Torsor.diff_smul_self _ _ _))

/-- **The glued torsor** of a descent datum `D` of torsors along a covering family: the glued
sheaf of the underlying descent datum of sheaves (`pseudofunctorOver.glue`), on which the
sections of `G` act componentwise.

The body is exposed so that the sections of the glued torsor are glued sections by definition,
as the statements of `glueTorsor_sheaf`, `glueTorsor_smul` and of the components of
`toDescentDataGlueTorsorIso` need. -/
@[expose] def glueTorsor (hf : Sieve.ofArrows X f ∈ J S) : Torsor (G.over S) where
  sheaf := (glue J f).obj ((toSheafDescentData f).obj D)
  mulAction T := glueMulAction D T.unop
  map_smul T T' r g s := GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun h ↦
    funext fun hh ↦ by
    have e : (show (G.over (X i)).obj.obj (op Z) from G.obj.map (h ≫ r.unop.left).op g) =
        (show (G.over (X i)).obj.obj (op Z) from G.obj.map h.op (G.obj.map r.unop.left.op g)) :=
      Functor.map_comp_apply G.obj r.unop.left.op h.op g
    refine (gluePresheaf_map_val _ r (smulGlueSection D g s) i Z h hh).trans
      ((smulGlueSection_val D g s i Z (h ≫ r.unop.left) (by simp [hh])).trans
        ((congrArg (fun y : (G.over (X i)).obj.obj (op Z) ↦ y •
          (show (torsorObj D i).sheaf.obj.obj (op Z) from
            s.val i Z (h ≫ r.unop.left) (by simp [hh]))) e).trans ?_))
    refine Eq.trans ?_ (smulGlueSection_val D _ ((gluePresheaf _).map r s) i Z h hh).symm
    exact congrArg (fun x : (torsorObj D i).sheaf.obj.obj (op Z) ↦
      (show (G.over (X i)).obj.obj (op Z) from G.obj.map h.op (G.obj.map r.unop.left.op g)) • x)
        (gluePresheaf_map_val _ r s i Z h hh).symm)
  coversTop := coversTop_glue D hf
  bijective T := ⟨fun ⟨g, s⟩ ⟨g', s'⟩ he ↦ by
      obtain ⟨he₁, rfl⟩ := Prod.ext_iff.1 he
      exact Prod.ext (smulGlueSection_left_injective D hf s he₁) rfl,
    fun ⟨t, s⟩ ↦ let ⟨g, hg⟩ := exists_smulGlueSection_eq D hf s t; ⟨(g, s), Prod.ext hg rfl⟩⟩

/-- The sheaf of the glued torsor is the glued sheaf of the underlying descent datum of sheaves. -/
@[simp]
lemma glueTorsor_sheaf (hf : Sieve.ofArrows X f ∈ J S) :
    (glueTorsor D hf).sheaf = (glue J f).obj ((toSheafDescentData f).obj D) :=
  (rfl)

/-- The sections of `G` act on the sections of the glued torsor by `smulGlueSection`. -/
lemma glueTorsor_smul (hf : Sieve.ofArrows X f ∈ J S) {T : Over S}
    (g : (G.over S).obj.obj (op T)) (s : (glueTorsor D hf).sheaf.obj.obj (op T)) :
    g • s = smulGlueSection D g s :=
  (rfl)

end Glue

/-- A family of morphisms of torsors between the objects of two descent data whose underlying
morphisms of sheaves are the components of a morphism of the underlying descent data of sheaves
is compatible with the gluing morphisms. -/
private lemma comm_of_hom_eq {D₁ D₂ : (torsorPseudofunctor G).DescentData f}
    (φ : ∀ i, D₁.obj i ⟶ D₂.obj i)
    (ψ : (toSheafDescentData f).obj D₁ ⟶ (toSheafDescentData f).obj D₂)
    (h : ∀ i, ψ.hom i = (φ i).hom) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((torsorPseudofunctor G).map f₁.op.toLoc).toFunctor.map (φ i₁) ≫ D₂.hom q f₁ f₂ hf₁ hf₂ =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫ ((torsorPseudofunctor G).map f₂.op.toLoc).toFunctor.map (φ i₂) :=
  Torsor.hom_ext (by
    have := ψ.comm q f₁ f₂ hf₁ hf₂
    rw [h, h, toSheafDescentData_obj_hom, toSheafDescentData_obj_hom] at this
    exact this)

variable (D : (torsorPseudofunctor G).DescentData f) (hf : Sieve.ofArrows X f ∈ J S)

/-- The descent datum of the glued torsor of `D` is `D`. -/
def toDescentDataGlueTorsorIso :
    ((torsorPseudofunctor G).toDescentData f).obj (glueTorsor D hf) ≅ D :=
  DescentData.isoMk (fun i ↦ Torsor.isoMk (glueRestrictIso ((toSheafDescentData f).obj D) i)
    (fun ⟨Z⟩ g s ↦ by
      refine (glueRestrictIso_hom_hom_app_apply i (op Z) _).trans
        ((smulGlueSection_val D (show (G.over S).obj.obj (op ((Over.map (f i)).obj Z)) from g) s
          i Z (𝟙 _) (by simp)).trans (Eq.trans ?_
          (congrArg (fun x : (torsorObj D i).sheaf.obj.obj (op Z) ↦
            (show (G.over (X i)).obj.obj (op Z) from g) • x)
            (glueRestrictIso_hom_hom_app_apply i (op Z) s).symm)))
      refine congrArg (fun y : (G.over (X i)).obj.obj (op Z) ↦ y •
        (show (torsorObj D i).sheaf.obj.obj (op Z) from s.val i Z (𝟙 _) (by simp))) ?_
      exact Functor.map_id_apply G.obj _ g))
    (comm_of_hom_eq _ (((torsorPseudofunctorForget G).toDescentDataCompMapDescentDataIso f).hom.app
      (glueTorsor D hf) ≫ (toDescentDataGlueIso ((toSheafDescentData f).obj D)).hom)
      (fun i ↦ (DescentData.comp_hom _ _ i).trans ((Category.id_comp _).trans
        (toDescentDataGlueIso_hom_hom (D := (toSheafDescentData f).obj D) i))))

/-- The components of `toDescentDataGlueTorsorIso` lie over the isomorphisms
`pseudofunctorOver.glueRestrictIso` of the glued sheaf. -/
@[simp]
lemma toDescentDataGlueTorsorIso_hom_hom_hom (i : ι) :
    ((toDescentDataGlueTorsorIso D hf).hom.hom i).hom =
      (glueRestrictIso ((toSheafDescentData f).obj D) i).hom :=
  (rfl)

/-- For a covering family, the functor from torsors under `G.over S` to descent data of torsors is
faithful, because the functor from sheaves to descent data of sheaves is. -/
lemma faithful_toDescentData (hf : Sieve.ofArrows X f ∈ J S) :
    ((torsorPseudofunctor G).toDescentData f).Faithful where
  map_injective {_ _} {φ φ'} h := by
    have := isStack_pseudofunctorOver.{max t w} J
    have := (J.pseudofunctorOver (Type (max t u v w))).isEquivalence_toDescentData f hf
    exact Torsor.hom_ext (((J.pseudofunctorOver _).toDescentData f).map_injective
      (DescentData.hom_ext fun i ↦ congrArg (fun χ ↦ (χ.hom i).hom) h))

/-- For a covering family, the functor from torsors under `G.over S` to descent data of torsors is
full: a morphism of descent data of torsors glues to a morphism of the underlying sheaves, which
is equivariant because it is so after restriction to the `X i`. -/
lemma full_toDescentData (hf : Sieve.ofArrows X f ∈ J S) :
    ((torsorPseudofunctor G).toDescentData f).Full where
  map_surjective {P Q} Φ := by
    -- `P'` and `Q'` are `P` and `Q` typed as torsors, so that instance search finds their
    -- actions; as in the section `Glue`, group elements are retyped with `show`.
    let P' : Torsor (G.over S) := P
    let Q' : Torsor (G.over S) := Q
    let e := (torsorPseudofunctorForget G).toDescentDataCompMapDescentDataIso f
    have := isStack_pseudofunctorOver.{max t w} J
    have := (J.pseudofunctorOver (Type (max t u v w))).isEquivalence_toDescentData f hf
    let ψ₀ : P'.sheaf ⟶ Q'.sheaf := ((J.pseudofunctorOver _).toDescentData f).preimage
      (e.inv.app P ≫ (toSheafDescentData f).map Φ ≫ e.hom.app Q)
    have hψ₀ (i : ι) : ((J.pseudofunctorOver _).map (f i).op.toLoc).toFunctor.map ψ₀ =
        (Φ.hom i).hom :=
      (congrArg (fun χ ↦ χ.hom i) (((J.pseudofunctorOver _).toDescentData f).map_preimage
        (e.inv.app P ≫ (toSheafDescentData f).map Φ ≫ e.hom.app Q))).trans
        ((DescentData.comp_hom (e.inv.app P) ((toSheafDescentData f).map Φ ≫ e.hom.app Q) i).trans
          ((Category.id_comp _).trans ((DescentData.comp_hom ((toSheafDescentData f).map Φ)
            (e.hom.app Q) i).trans (Category.comp_id _))))
    refine ⟨⟨ψ₀, fun T g p ↦ (bijective_toGlue_app (M := Q'.sheaf) hf T).1 ?_⟩,
      DescentData.hom_ext fun i ↦ Torsor.hom_ext (hψ₀ i)⟩
    refine GlueSection.ext (funext fun i ↦ funext fun Z ↦ funext fun h ↦ funext fun hh ↦ ?_)
    let c : (Over.map (f i)).obj Z ⟶ T.unop := Over.homMk h (by simpa using hh)
    have key (x : P'.sheaf.obj.obj (op ((Over.map (f i)).obj Z))) :
        ψ₀.hom.app (op ((Over.map (f i)).obj Z)) x = (Φ.hom i).hom.hom.app (op Z) x :=
      congrArg (fun χ : (J.overMapPullback _ (f i)).obj P'.sheaf ⟶
        (J.overMapPullback _ (f i)).obj Q'.sheaf ↦ χ.hom.app (op Z) x) (hψ₀ i)
    let y : (G.over (X i)).obj.obj (op Z) := (G.over S).obj.map c.op g
    rw [toGlue_app_apply, toGlue_app_apply, toGlueSection_val, toGlueSection_val]
    refine (NatTrans.naturality_apply ψ₀.hom c.op _).symm.trans
      ((congrArg (ψ₀.hom.app (op ((Over.map (f i)).obj Z))) (P'.map_smul c.op g p)).trans
        ((key _).trans (((Φ.hom i).map_smul (op Z) y _).trans ?_)))
    refine (congrArg (fun x : Q'.sheaf.obj.obj (op ((Over.map (f i)).obj Z)) ↦
      (show (G.over S).obj.obj (op ((Over.map (f i)).obj Z)) from y) • x)
        (key _).symm).trans ?_
    refine (congrArg (fun x : Q'.sheaf.obj.obj (op ((Over.map (f i)).obj Z)) ↦
      (show (G.over S).obj.obj (op ((Over.map (f i)).obj Z)) from y) • x)
        (NatTrans.naturality_apply ψ₀.hom c.op p)).trans ?_
    exact (Q'.map_smul c.op g _).symm

/-- **Descent of torsors.** For a family `f` generating a covering sieve, the functor from torsors
under `G.over S` to descent data of torsors along `f` is an equivalence: every descent datum of
torsors is effective, with the glued torsor `torsorPseudofunctor.glueTorsor`. -/
theorem isEquivalence_toDescentData (hf : Sieve.ofArrows X f ∈ J S) :
    ((torsorPseudofunctor G).toDescentData f).IsEquivalence :=
  have := faithful_toDescentData (G := G) hf
  have := full_toDescentData (G := G) hf
  { essSurj := ⟨fun D ↦ ⟨glueTorsor D hf, ⟨toDescentDataGlueTorsorIso D hf⟩⟩⟩ }

end torsorPseudofunctor

variable (G : Sheaf J GrpCat.{max u v w})

/-- **Torsors form a stack** (Giraud, *Cohomologie non abélienne*, Chapitre III): the
pseudofunctor `U ↦ Torsor (G.over U)` of torsors under the restrictions of a sheaf of groups `G`
to the slice sites is a stack for `J`. Morphisms of torsors glue along a covering sieve, and every
descent datum of torsors along a covering sieve is effective: the underlying descent datum of
sheaves is effective (`GrothendieckTopology.isStack_pseudofunctorOver`), and the action of `G`,
its simple transitivity and the local nonemptiness descend to the glued sheaf. -/
theorem isStack_torsorPseudofunctor : (torsorPseudofunctor G).IsStack J :=
  IsStack.of_isStackFor fun _ R hR ↦ ⟨torsorPseudofunctor.isEquivalence_toDescentData (G := G)
    (f := fun (f : R.arrows.category) ↦ f.obj.hom) (by rwa [Sieve.ofArrows_category])⟩

/-- **The stack of torsors is a gerbe**: it is a stack (`isStack_torsorPseudofunctor`), its fibres
are groupoids (`Torsor.isIso_hom`), the trivial torsor is an object over every `U`, and any two
torsors over `U` become isomorphic, to the trivial torsor, over the arrows `V ⟶ U` over which both
have a section, which form a covering sieve. -/
theorem isGerbe_torsorPseudofunctor : (torsorPseudofunctor G).IsGerbe J where
  toIsStack := isStack_torsorPseudofunctor G
  isGroupoid _ := inferInstance
  exists_covering_nonempty U := ⟨⊤, J.top_mem U, fun V _ _ ↦ ⟨Torsor.trivial (G.over V)⟩⟩
  exists_covering_iso {U} P Q := by
    -- `P` and `Q` typed as torsors, so that their fields are found by elaboration.
    let P' : Torsor (G.over U) := P
    let Q' : Torsor (G.over U) := Q
    refine ⟨Sieve.overEquiv (Over.mk (𝟙 U)) (Sieve.ofObjects _ _ ⊓ Sieve.ofObjects _ _),
      ((J.over U).intersection_covering (P'.coversTop (Over.mk (𝟙 U)))
        (Q'.coversTop (Over.mk (𝟙 U)))),
      fun V a ha ↦ ?_⟩
    rw [Sieve.overEquiv_iff] at ha
    obtain ⟨⟨⟨Z₁, ⟨p⟩⟩, ⟨b₁⟩⟩, ⟨⟨Z₂, ⟨q⟩⟩, ⟨b₂⟩⟩⟩ := ha
    let c : (Over.map a).obj (Over.mk (𝟙 V)) ⟶ Over.mk (a ≫ (Over.mk (𝟙 U)).hom) :=
      Over.homMk (𝟙 V) (by simp)
    obtain ⟨eP⟩ := Torsor.nonempty_trivial_iso_of_isTerminal
      ((Torsor.overMapPullback a).obj P') Over.mkIdTerminal (P'.sheaf.obj.map (c ≫ b₁).op p)
    obtain ⟨eQ⟩ := Torsor.nonempty_trivial_iso_of_isTerminal
      ((Torsor.overMapPullback a).obj Q') Over.mkIdTerminal (Q'.sheaf.obj.map (c ≫ b₂).op q)
    exact ⟨eP.symm ≪≫ eQ⟩

/-- `isGerbe_torsorPseudofunctor` for sheaves of groups with values in `Type (max u v)`, as an
instance, which also makes the pseudofunctor of torsors a stack: for the big site of a scheme
`S : Scheme.{u}`, these are the sheaves of groups with values in `Type (u + 1)`. The universe of
`isGerbe_torsorPseudofunctor` cannot be inferred from `Type (max u v)` by instance search. -/
instance (G : Sheaf J GrpCat.{max u v}) : (torsorPseudofunctor G).IsGerbe J :=
  isGerbe_torsorPseudofunctor.{0} G

end CategoryTheory.Sheaf
