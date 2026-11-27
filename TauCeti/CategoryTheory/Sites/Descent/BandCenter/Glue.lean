/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import TauCeti.CategoryTheory.Bicategory.Functor.Cat
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Cover
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Gluing central sections: the sheaf of intrinsic central sections of a prestack

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` and `ZF(U)` its
group of intrinsic central sections over `U` (`CategoryTheory.Pseudofunctor.IntrinsicBandSections`).
For a covering sieve `R` of `U` and a compatible family `z` on `R`
(`IntrinsicBandSections.IsCompatible`), the descended centre unit
`IntrinsicBandSections.coverCenter` lives over `U` only. Pulling `R` back along an arbitrary arrow
`a : V ⟶ U` and descending the family `h ↦ z_(h ≫ a)` gives a unit `c_(R, z, a)` of the
categorical centre of the fibre over `V` (`IntrinsicBandSections.coverCenterAt`). These units are
compatible with pullback along every arrow `g : W ⟶ V`, whether or not `g ≫ a` lies in `R`
(`IntrinsicBandSections.coverCenterAt_compatible`); the proof transports the local formula along
the composition isomorphisms of `F` (`Pseudofunctor.map_map_eq_catCenter_app`). So they form a
central section `glue(R, z) ∈ ZF(U)` (`IntrinsicBandSections.glue`), the unique one restricting to
`z_i` along every arrow `i` of `R` (`IntrinsicBandSections.restrict_glue`,
`IntrinsicBandSections.glue_unique`).

Consequently the presheaf of abelian groups `U ↦ Additive ZF(U)`
(`IntrinsicBandSections.presheaf`) is a sheaf for `J` (`IntrinsicBandSections.isSheaf_of_prestack`).
Neither groupoid fibres, gerbe locality nor commutativity of the automorphism groups is needed. This
is the varying-base conclusion of the Stacks Project, Lemma 8.11.8 (0CJY), with morphism sheaves as
in Definition 8.4.1 (026F).

## Main definitions

* `IntrinsicBandSections.coverCenterAt`: the descended centre unit over an arbitrary `a : V ⟶ U`.
* `IntrinsicBandSections.glue`: the glued central section.
* `IntrinsicBandSections.presheaf`: the presheaf of abelian groups `U ↦ Additive ZF(U)`.
* `IntrinsicBandSections.sheaf`: `IntrinsicBandSections.presheaf` as an object of
  `Sheaf J AddCommGrpCat`.

## Main results

* `IntrinsicBandSections.coverCenterAt_unique`, `IntrinsicBandSections.coverCenterAt_compatible`,
  `IntrinsicBandSections.coverCenterAt_of_mem`.
* `IntrinsicBandSections.restrict_glue`, `IntrinsicBandSections.glue_unique`,
  `IntrinsicBandSections.glue_restrict`.
* `IntrinsicBandSections.isSheaf_of_prestack`: `U ↦ Additive ZF(U)` is a sheaf for `J`.
* `IntrinsicBandSections.sheaf_obj`, `IntrinsicBandSections.sheaf_obj_obj`,
  `IntrinsicBandSections.sheaf_obj_map_apply`: the sections and restrictions of `sheaf`.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
* [The Stacks Project, Definition 8.4.1 (026F)](https://stacks.math.columbia.edu/tag/026F)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

variable {U : C} {R : Sieve U} {z w : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left}

/-- Values of a family on a sieve at two equal arrows agree. -/
theorem congr_categoryMk {Y : C} {q q' : Y ⟶ U} (h : q = q') (hq : R.arrows q)
    (hq' : R.arrows q') :
    z (Presieve.categoryMk R.arrows q hq) = z (Presieve.categoryMk R.arrows q' hq') := by
  subst h
  rfl

/-- The family `h ↦ z_(h ≫ a)` on the pullback of `R` along `a : V ⟶ U`. -/
def pullbackFamily (z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left)
    {V : C} (a : V ⟶ U) (i : (R.pullback a).arrows.category) :
    IntrinsicBandSections F i.obj.left :=
  z (Presieve.categoryMk R.arrows (i.obj.hom ≫ a) i.property)

/-- Unfolding of `IntrinsicBandSections.pullbackFamily`. -/
@[simp]
theorem pullbackFamily_apply {V : C} (a : V ⟶ U) (i : (R.pullback a).arrows.category) :
    pullbackFamily z a i = z (Presieve.categoryMk R.arrows (i.obj.hom ≫ a) i.property) :=
  (rfl)

/-- The pulled-back family of a compatible family is compatible. -/
theorem IsCompatible.pullback (hz : IsCompatible z) {V : C} (a : V ⟶ U) :
    IsCompatible (pullbackFamily z a) := (isCompatible_iff _).2 fun i j g ↦
  (isCompatible_iff z).1 hz (ObjectProperty.homMk (Over.homMk g.hom.left (by
      simp only [Presieve.categoryMk, Over.mk_hom, ← Category.assoc, Over.w g.hom])) :
    Presieve.categoryMk R.arrows (i.obj.hom ≫ a) i.property ⟶
      Presieve.categoryMk R.arrows (j.obj.hom ≫ a) j.property)

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- **The descended centre unit over `a : V ⟶ U`**: descend the family `h ↦ z_(h ≫ a)` along the
pullback of the covering sieve `R` along `a`. -/
noncomputable def coverCenterAt (hR : R ∈ J U) (hz : IsCompatible z) {V : C} (a : V ⟶ U) :
    (CatCenter (F.obj (.mk (op V))))ˣ :=
  coverCenter (J.pullback_stable a hR) (hz.pullback a)

/-- Pulled back along an arrow `h : X ⟶ V` of the pullback sieve, `c_(R, z, a)` is the component
at the identity of `z_(h ≫ a)`. -/
theorem map_coverCenterAt_app (hR : R ∈ J U) (hz : IsCompatible z) {V : C} (a : V ⟶ U)
    (x : F.obj (.mk (op V))) (i : (R.pullback a).arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.map ((coverCenterAt hR hz a).val.app x) =
      ((z (Presieve.categoryMk R.arrows (i.obj.hom ≫ a) i.property)).val i.obj.left
        (𝟙 _)).val.app ((F.map i.obj.hom.op.toLoc).toFunctor.obj x) := by
  rw [coverCenterAt, map_coverCenter_app, pullbackFamily_apply]

/-- **Uniqueness of `c_(R, z, a)`.** A unit of the categorical centre over `V` whose pullback along
every arrow `h` of the pullback sieve at every object `x` is the component of `z_(h ≫ a)` at the
identity is `c_(R, z, a)`. -/
theorem coverCenterAt_unique (hR : R ∈ J U) (hz : IsCompatible z) {V : C} (a : V ⟶ U)
    (c : (CatCenter (F.obj (.mk (op V))))ˣ)
    (hc : ∀ (x : F.obj (.mk (op V))) (i : (R.pullback a).arrows.category),
      (F.map i.obj.hom.op.toLoc).toFunctor.map (c.val.app x) =
        ((z (Presieve.categoryMk R.arrows (i.obj.hom ≫ a) i.property)).val i.obj.left
          (𝟙 _)).val.app ((F.map i.obj.hom.op.toLoc).toFunctor.obj x)) :
    c = coverCenterAt hR hz a :=
  coverCenter_unique _ _ c fun x i ↦ by rw [pullbackFamily_apply]; exact hc x i

/-- The identity family gives the identity centre unit over every `a`. -/
@[simp]
theorem coverCenterAt_one (hR : R ∈ J U) {V : C} (a : V ⟶ U) :
    coverCenterAt (F := F) hR isCompatible_one a = 1 :=
  coverCenter_one _

/-- The inverse family gives the inverse centre unit over every `a`. -/
@[simp]
theorem coverCenterAt_inv (hR : R ∈ J U) (hz : IsCompatible z) {V : C} (a : V ⟶ U) :
    coverCenterAt hR hz.inv a = (coverCenterAt hR hz a)⁻¹ :=
  coverCenter_inv _ (hz.pullback a)

/-- The product family gives the product centre unit over every `a`. -/
@[simp]
theorem coverCenterAt_mul (hR : R ∈ J U) (hz : IsCompatible z) (hw : IsCompatible w) {V : C}
    (a : V ⟶ U) :
    coverCenterAt hR (hz.mul hw) a = coverCenterAt hR hz a * coverCenterAt hR hw a :=
  coverCenter_mul _ (hz.pullback a) (hw.pullback a)

/-- The restrictions of a section `s ∈ ZF(U)` give its component `s(V, a)` over every `a`. -/
@[simp]
theorem coverCenterAt_restrict (hR : R ∈ J U) (s : IntrinsicBandSections F U) {V : C}
    (a : V ⟶ U) :
    coverCenterAt hR (isCompatible_restrict s) a = s.val V a :=
  (coverCenterAt_unique hR _ a _ fun x i ↦ by simp [map_app]).symm

/-- **Compatibility with pullback along any arrow.** For every `g : W ⟶ V`, whether or not
`g ≫ a` lies in `R`, `g^*` carries `c_(R, z, a)` at `x` to `c_(R, z, g ≫ a)` at `g^* x`. -/
theorem coverCenterAt_compatible (hR : R ∈ J U) (hz : IsCompatible z) {V W : C} (a : V ⟶ U)
    (g : W ⟶ V) (x : F.obj (.mk (op V))) :
    (F.map g.op.toLoc).toFunctor.map ((coverCenterAt hR hz a).val.app x) =
      (coverCenterAt hR hz (g ≫ a)).val.app ((F.map g.op.toLoc).toFunctor.obj x) := by
  refine IsPrestack.hom_ext (J.pullback_stable (g ≫ a) hR) fun X h hh ↦ ?_
  have hh' : (R.pullback a).arrows (h ≫ g) := by simpa using hh
  have h₁ := map_coverCenterAt_app hR hz a x (Presieve.categoryMk _ (h ≫ g) hh')
  have h₂ := map_coverCenterAt_app hR hz (g ≫ a) ((F.map g.op.toLoc).toFunctor.obj x)
    (Presieve.categoryMk _ h hh)
  rw [map_map_eq_catCenter_app F g.op.toLoc h.op.toLoc (h ≫ g).op.toLoc rfl _ _ h₁]
  refine Eq.trans ?_ h₂.symm
  exact congrArg (fun s : IntrinsicBandSections F X ↦ (s.val X (𝟙 X)).val.app
      ((F.map h.op.toLoc).toFunctor.obj ((F.map g.op.toLoc).toFunctor.obj x)))
    (congr_categoryMk (Category.assoc h g a) _ _)

/-- **Value on the arrows of `R`.** For `i` in `R` and any `a : V ⟶ V_i`,
`c_(R, z, a ≫ i) = z_i(V, a)`. -/
theorem coverCenterAt_of_mem (hR : R ∈ J U) (hz : IsCompatible z) (i : R.arrows.category)
    {V : C} (a : V ⟶ i.obj.left) :
    coverCenterAt hR hz (a ≫ i.obj.hom) = (z i).val V a := by
  refine (coverCenterAt_unique hR hz _ _ fun x j ↦ ?_).symm
  rw [map_app, hz.val_eq (j.obj.hom ≫ a ≫ i.obj.hom) i (j.obj.hom ≫ a) (Category.assoc _ _ _)]

/-- **The glued central section** of a compatible family on a covering sieve of a prestack: its
component at `a : V ⟶ U` is `c_(R, z, a)`. -/
noncomputable def glue (hR : R ∈ J U) (hz : IsCompatible z) : IntrinsicBandSections F U :=
  ofCompatible (fun _ a ↦ coverCenterAt hR hz a) ((isPullbackCompatible_iff _).2 fun _ _ a g x ↦
    coverCenterAt_compatible hR hz a g x)

@[simp]
theorem val_glue (hR : R ∈ J U) (hz : IsCompatible z) (V : C) (a : V ⟶ U) :
    (glue hR hz).val V a = coverCenterAt hR hz a :=
  val_ofCompatible _ _ V a

/-- The glued section restricts to `z_i` along every arrow `i` of `R`. -/
@[simp]
theorem restrict_glue (hR : R ∈ J U) (hz : IsCompatible z) (i : R.arrows.category) :
    restrict i.obj.hom (glue hR hz) = z i := by
  ext W b x
  rw [val_restrict, val_glue, coverCenterAt_of_mem]

/-- **Uniqueness of the glued section.** A section restricting to `z_i` along every arrow `i` of
`R` is the glued section. -/
theorem glue_unique (hR : R ∈ J U) (hz : IsCompatible z) {s : IntrinsicBandSections F U}
    (hs : ∀ i : R.arrows.category, restrict i.obj.hom s = z i) :
    s = glue hR hz :=
  eq_of_restrict_eq hR fun _ f hf ↦
    (hs (Presieve.categoryMk _ f hf)).trans (restrict_glue hR hz (Presieve.categoryMk _ f hf)).symm

/-- Gluing the restrictions of a section `s ∈ ZF(U)` gives `s`. -/
@[simp]
theorem glue_restrict (hR : R ∈ J U) (s : IntrinsicBandSections F U) :
    glue hR (isCompatible_restrict s) = s :=
  (glue_unique hR _ fun _ ↦ rfl).symm

/-- Gluing the identity family gives the identity section. -/
@[simp]
theorem glue_one (hR : R ∈ J U) : glue (F := F) hR isCompatible_one = 1 :=
  (glue_unique hR _ fun _ ↦ map_one _).symm

/-- Gluing the inverse family gives the inverse section. -/
@[simp]
theorem glue_inv (hR : R ∈ J U) (hz : IsCompatible z) : glue hR hz.inv = (glue hR hz)⁻¹ :=
  (glue_unique hR _ fun i ↦ by rw [map_inv, restrict_glue]).symm

/-- Gluing the product family gives the product section. -/
@[simp]
theorem glue_mul (hR : R ∈ J U) (hz : IsCompatible z) (hw : IsCompatible w) :
    glue hR (hz.mul hw) = glue hR hz * glue hR hw :=
  (glue_unique hR _ fun i ↦ by rw [map_mul, restrict_glue, restrict_glue]).symm

variable (F) in
/-- The presheaf of abelian groups `U ↦ Additive ZF(U)`, with restriction along `f : V ⟶ U` as
transition map. -/
@[expose, simps obj]
def presheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u v u' v'} where
  obj U := .of (Additive (IntrinsicBandSections F U.unop))
  map f := AddCommGrpCat.ofHom (restrict f.unop).toAdditive
  map_id _ := AddCommGrpCat.ext fun s ↦ congrArg Additive.ofMul (restrict_id s.toMul)
  map_comp f g := AddCommGrpCat.ext fun s ↦
    congrArg Additive.ofMul (restrict_comp f.unop g.unop s.toMul).symm

/-- The restriction map of `presheaf F` along `f` is `restrict f.unop` through the `Additive`
wrapper. -/
@[simp]
theorem presheaf_map_apply {V W : Cᵒᵖ} (f : V ⟶ W) (s : (presheaf F).obj V) :
    (presheaf F).map f s = Additive.ofMul (restrict f.unop (Additive.toMul s)) :=
  rfl

/-- **The intrinsic central sections of a prestack form a sheaf**: `U ↦ Additive ZF(U)` is a sheaf
of abelian groups for `J`. No groupoid, gerbe or commutativity hypothesis is needed. -/
theorem isSheaf_of_prestack : Presheaf.IsSheaf J (presheaf F) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  -- Applying `forget AddCommGrpCat` to a map is applying the underlying function, so each
  -- restriction map below is described by `presheaf_map_apply`; `Additive.ofMul` and
  -- `Additive.toMul` then move equations of sections across the `Additive` wrapper.
  intro U R hR x hx
  replace hx := hx.to_sieveCompatible
  let y : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left :=
    fun i ↦ (x i.obj.hom i.property).toMul
  have congr_x {V : C} {f f' : V ⟶ U} (e : f = f') (hf : R f) (hf' : R f') :
      x f hf = x f' hf' := by
    subst e
    rfl
  have hy : IsCompatible y := (isCompatible_iff _).2 fun i j g ↦ by
    have h := hx j.obj.hom g.hom.left j.property
    rw [congr_x (Over.w g.hom) _ i.property] at h
    exact congrArg Additive.toMul (h.trans (presheaf_map_apply _ _)).symm
  refine ⟨Additive.ofMul (glue hR hy), fun V f hf ↦ ?_, fun t ht ↦ ?_⟩
  · exact (presheaf_map_apply _ _).trans
      (congrArg Additive.ofMul (restrict_glue hR hy (Presieve.categoryMk _ f hf)))
  · exact congrArg Additive.ofMul (glue_unique hR hy fun i ↦
      congrArg Additive.toMul ((presheaf_map_apply _ _).symm.trans (ht i.obj.hom i.property)))

/-! ### The sheaf of intrinsic central sections -/

section Sheaf

variable (F) (J : GrothendieckTopology C) [F.IsPrestack J]

/-- **The sheaf of intrinsic central sections** of a prestack: `U ↦ Additive ZF(U)`, with
restriction along `f : V ⟶ U` as transition map. -/
@[expose]
def sheaf : Sheaf J AddCommGrpCat.{max u v u' v'} :=
  ⟨presheaf F, isSheaf_of_prestack⟩

/-- The underlying presheaf of `sheaf F J` is `presheaf F`. -/
theorem sheaf_obj : (sheaf F J).obj = presheaf F :=
  rfl

theorem sheaf_obj_obj (U : C) :
    (sheaf F J).obj.obj (op U) = AddCommGrpCat.of (Additive (IntrinsicBandSections F U)) :=
  rfl

/-- The restriction maps of `sheaf F J` are `restrict` through the `Additive` wrapper. -/
theorem sheaf_obj_map_apply {U V : C} (f : V ⟶ U) (s : Additive (IntrinsicBandSections F U)) :
    (sheaf F J).obj.map f.op s = Additive.ofMul (restrict f (Additive.toMul s)) :=
  rfl

end Sheaf

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
