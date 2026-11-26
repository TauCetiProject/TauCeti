/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Basic

/-!
# Descending central sections along a covering sieve

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `ZF(U)` its group of intrinsic central
sections over `U` (`CategoryTheory.Pseudofunctor.IntrinsicBandSections`). Let `R` be a sieve on
`U` and `z` a **compatible family** on `R`: a section `z_i ∈ ZF(V_i)` for every arrow
`i : V_i ⟶ U` of `R`, with `r_g(z_j) = z_i` for every morphism `g : i ⟶ j` of the category of
arrows of `R` (`IntrinsicBandSections.IsCompatible`).

For an object `x` over `U`, the evaluated automorphisms `ev_(𝟙, i^* x)(z_i)` of the pullbacks
`i^* x` commute with the gluing isomorphisms of the canonical descent datum of `x`
(`IntrinsicBandSections.map_localAut_hom_comp_hom`): over a common refinement
`q = f₁ ≫ i₁ = f₂ ≫ i₂` both pulled-back components are the component of `z_q`, and that component
is natural. So they form an automorphism of the descent datum (`IntrinsicBandSections.coverIso`).
No cover or prestack hypothesis is needed for this.

When `R` covers `U` and `F` is a prestack, the canonical descent functor is fully faithful, and
lifting gives an automorphism `coverAut(R, z, x)` of `x`, the unique one restricting to
`ev_(𝟙, i^* x)(z_i)` along every `i` (`IntrinsicBandSections.coverAut`,
`IntrinsicBandSections.coverAut_unique`). It is natural in `x`
(`IntrinsicBandSections.coverAut_naturality`), so these automorphisms form a unit `c_R(z)` of the
categorical centre of the fibre over `U` (`IntrinsicBandSections.coverCenter`), again unique with
its local components (`IntrinsicBandSections.coverCenter_unique`). The restrictions of a section
`s ∈ ZF(U)` descend to its component `s(U, 𝟙)`. The same descent argument shows that `ZF` is
separated for the topology (`IntrinsicBandSections.eq_of_restrict_eq`). This is the gluing step,
on the fixed base `U`, of the varying-base part of the Stacks Project, Lemma 8.11.8 (06NY).

## Main definitions

* `IntrinsicBandSections.IsCompatible`: compatible families of central sections on a sieve.
* `IntrinsicBandSections.coverIso`: the automorphism of the canonical descent datum of `x`.
* `IntrinsicBandSections.coverAut`: the descended automorphism of `x`.
* `IntrinsicBandSections.coverCenter`: the descended unit of the categorical centre.

## Main results

* `IntrinsicBandSections.map_localAut_hom_comp_hom`: the local evaluations commute with the gluing
  isomorphisms.
* `IntrinsicBandSections.coverIso_one`, `IntrinsicBandSections.coverIso_inv`,
  `IntrinsicBandSections.coverIso_mul`: the identity family, inverse and product families.
* `IntrinsicBandSections.map_coverAut_hom`, `IntrinsicBandSections.coverAut_unique`: the local
  components and uniqueness of the descended automorphism.
* `IntrinsicBandSections.coverAut_naturality`: the descended automorphisms are natural.
* `IntrinsicBandSections.coverAut_one`, `IntrinsicBandSections.coverAut_inv`,
  `IntrinsicBandSections.coverAut_mul`, `IntrinsicBandSections.coverAut_restrict`: the identity
  family, inverse and product families, and restrictions of a global section.
* `IntrinsicBandSections.coverCenter_app`, `IntrinsicBandSections.map_coverCenter_app`,
  `IntrinsicBandSections.coverCenter_unique`, `IntrinsicBandSections.coverCenter_one`,
  `IntrinsicBandSections.coverCenter_inv`, `IntrinsicBandSections.coverCenter_mul`,
  `IntrinsicBandSections.coverCenter_restrict`.
* `IntrinsicBandSections.eq_of_restrict_eq`: sections agreeing on a covering sieve are equal.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
* [The Stacks Project, Definition 8.4.1 (026F)](https://stacks.math.columbia.edu/tag/026F)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {U : C}

/-- A family of central sections `z_i ∈ ZF(V_i)`, one for every arrow `i : V_i ⟶ U` of a sieve
`R`, is **compatible** when `r_g(z_j) = z_i` for every morphism `g : i ⟶ j` of the category of
arrows of `R` (compare `Presieve.FamilyOfElements.SieveCompatible`). -/
def IsCompatible {R : Sieve U} (z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left) :
    Prop :=
  ∀ ⦃i j : R.arrows.category⦄ (g : i ⟶ j), restrict g.hom.left (z j) = z i

/-- Unfolding of `IntrinsicBandSections.IsCompatible`. -/
theorem isCompatible_iff {R : Sieve U}
    (z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left) :
    IsCompatible z ↔ ∀ ⦃i j : R.arrows.category⦄ (g : i ⟶ j), restrict g.hom.left (z j) = z i :=
  Iff.rfl

/-- Every family on the empty sieve is compatible. -/
theorem isCompatible_bot
    (z : ∀ i : (⊥ : Sieve U).arrows.category, IntrinsicBandSections F i.obj.left) :
    IsCompatible z :=
  fun i ↦ i.property.elim

variable {R : Sieve U} {z w : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left}

/-- The identity family is compatible. -/
theorem isCompatible_one : IsCompatible (F := F) (R := R) fun _ ↦ 1 :=
  fun _ _ _ ↦ map_one _

/-- The pointwise inverse of a compatible family is compatible. -/
theorem IsCompatible.inv (hz : IsCompatible z) : IsCompatible fun i ↦ (z i)⁻¹ :=
  fun _ _ g ↦ by rw [map_inv, hz g]

/-- The pointwise product of two compatible families is compatible. -/
theorem IsCompatible.mul (hz : IsCompatible z) (hw : IsCompatible w) :
    IsCompatible fun i ↦ z i * w i :=
  fun _ _ g ↦ by rw [map_mul, hz g, hw g]

/-- The restrictions `r_i(s)` of a section `s ∈ ZF(U)` along the arrows of `R` are compatible. -/
theorem isCompatible_restrict (s : IntrinsicBandSections F U) :
    IsCompatible (R := R) fun i ↦ restrict i.obj.hom s :=
  fun _ _ g ↦ by rw [restrict_comp, Over.w g.hom]

/-- For a compatible family, the component of `z_i` at `f : Y ⟶ V_i` is the component at the
identity of the section `z_q` at the composite arrow `q = f ≫ i` of `R`. -/
theorem IsCompatible.val_eq (hz : IsCompatible z) {Y : C} (q : Y ⟶ U) (i : R.arrows.category)
    (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) :
    (z i).val Y f =
      (z (Presieve.categoryMk R.arrows q (hf ▸ R.downward_closed i.property f))).val Y (𝟙 Y) := by
  have h := congrArg (fun s ↦ s.val Y (𝟙 Y))
    (hz (ObjectProperty.homMk (Over.homMk f hf) :
      Presieve.categoryMk R.arrows q (hf ▸ R.downward_closed i.property f) ⟶ i))
  simpa using h

/-- The local automorphism `ev_(𝟙, i^* x)(z_i)` of the pullback of `x` along an arrow `i` of
`R`. -/
abbrev localAut (z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left)
    (x : F.obj (.mk (op U))) (i : R.arrows.category) :
    Aut ((F.map i.obj.hom.op.toLoc).toFunctor.obj x) :=
  evaluation (𝟙 i.obj.left) _ (z i)

/-- Pulled back along `f : Y ⟶ V_i`, the local evaluation at `i` is the component at the
identity of `z_q` for the composite arrow `q = f ≫ i`. -/
theorem IsCompatible.map_localAut_hom (hz : IsCompatible z) (x : F.obj (.mk (op U))) {Y : C}
    (q : Y ⟶ U) (i : R.arrows.category) (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) :
    (F.map f.op.toLoc).toFunctor.map (localAut z x i).asIso.hom =
      ((z (Presieve.categoryMk R.arrows q (hf ▸ R.downward_closed i.property f))).val Y
        (𝟙 Y)).val.app
          ((F.map f.op.toLoc).toFunctor.obj ((F.map i.obj.hom.op.toLoc).toFunctor.obj x)) := by
  rw [evaluation_asIso_hom, map_app, Category.comp_id, hz.val_eq q i f hf]

/-- **The local evaluations commute with the gluing isomorphisms** of the canonical descent datum
of `x`, for a compatible family on any sieve. -/
theorem map_localAut_hom_comp_hom (hz : IsCompatible z) (x : F.obj (.mk (op U))) ⦃Y : C⦄
    (q : Y ⟶ U) ⦃i₁ i₂ : R.arrows.category⦄ (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q) :
    (F.map f₁.op.toLoc).toFunctor.map (localAut z x i₁).asIso.hom ≫
        ((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj x).hom q f₁ f₂ hf₁ hf₂ =
      ((F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj x).hom q f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (localAut z x i₂).asIso.hom := by
  -- The target of the gluing morphism is `(ofObj x).obj i₂`, which is `i₂^* x` only up to
  -- unfolding, so the second rewrite is done by `whisker_eq`.
  exact (eq_whisker (hz.map_localAut_hom x q i₁ f₁ hf₁) _).trans
    ((CatCenter.naturality _ _).symm.trans
      (whisker_eq _ (hz.map_localAut_hom x q i₂ f₂ hf₂).symm))

/-- The automorphism of the canonical descent datum of `x` on `R` with components the local
evaluations `ev_(𝟙, i^* x)(z_i)`. -/
def coverIso (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    (F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj x ≅
      (F.toDescentData fun i : R.arrows.category ↦ i.obj.hom).obj x :=
  DescentData.isoMk (fun i ↦ (localAut z x i).asIso)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ map_localAut_hom_comp_hom hz x q f₁ f₂ hf₁ hf₂)

@[simp]
theorem coverIso_hom_hom (hz : IsCompatible z) (x : F.obj (.mk (op U))) (i : R.arrows.category) :
    (coverIso hz x).hom.hom i = (localAut z x i).asIso.hom :=
  (rfl)

@[simp]
theorem coverIso_inv_hom (hz : IsCompatible z) (x : F.obj (.mk (op U))) (i : R.arrows.category) :
    (coverIso hz x).inv.hom i = (localAut z x i).asIso.inv :=
  (rfl)

/-- The identity family gives the identity automorphism of the descent datum. -/
@[simp]
theorem coverIso_one (x : F.obj (.mk (op U))) :
    coverIso (F := F) (R := R) isCompatible_one x = Iso.refl _ := by
  ext i
  simp only [coverIso_hom_hom, map_one, Aut.one_asIso, Iso.refl_hom, DescentData.id_hom]
  -- The two sides now differ only in the object `((F.toDescentData _).obj x).obj i`, which is
  -- `i^* x` by unfolding, so `rfl` closes the goal.
  rfl

/-- The inverse family gives the inverse automorphism of the descent datum. -/
@[simp]
theorem coverIso_inv (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    coverIso hz.inv x = (coverIso hz x).symm := by
  ext i
  simp only [coverIso_hom_hom, Iso.symm_hom, coverIso_inv_hom, map_inv, Aut.inv_asIso]
  -- The two sides now differ only in the object `((F.toDescentData _).obj x).obj i`, which is
  -- `i^* x` by unfolding, so `rfl` closes the goal.
  rfl

/-- The product family gives the composite automorphism of the descent datum. -/
@[simp]
theorem coverIso_mul (hz : IsCompatible z) (hw : IsCompatible w) (x : F.obj (.mk (op U))) :
    coverIso (hz.mul hw) x = coverIso hw x ≪≫ coverIso hz x := by
  ext i
  simp only [coverIso_hom_hom, Iso.trans_hom, DescentData.comp_hom, map_mul, Aut.mul_asIso]
  -- The two sides now differ only in the object `((F.toDescentData _).obj x).obj i`, which is
  -- `i^* x` by unfolding, so `rfl` closes the goal.
  rfl

variable {J : GrothendieckTopology C} [F.IsPrestack J]

/-- **The descended automorphism.** For a covering sieve `R` of a prestack and a compatible family
`z`, the automorphism of `x` obtained by lifting `coverIso` through the fully faithful canonical
descent functor. -/
noncomputable def coverAut (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    Aut x :=
  .of ((F.isPrestackFor' R hR).fullyFaithful.preimageIso (coverIso hz x))

/-- Pulling the descended automorphism back along an arrow `i` of `R` gives the local evaluation
`ev_(𝟙, i^* x)(z_i)`. -/
@[simp]
theorem map_coverAut_hom (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U)))
    (i : R.arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.map (coverAut hR hz x).asIso.hom =
      (localAut z x i).asIso.hom := by
  have h := congrArg (fun φ ↦ DescentData.Hom.hom φ i)
    ((F.isPrestackFor' R hR).fullyFaithful.map_preimage (coverIso hz x).hom)
  rw [toDescentData_map_hom, coverIso_hom_hom] at h
  exact h

/-- The descended automorphism restricts to the local evaluations, as automorphisms. -/
theorem mapAut_coverAut (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U)))
    (i : R.arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.mapAut x (coverAut hR hz x) = localAut z x i :=
  Aut.ext (Iso.ext (map_coverAut_hom hR hz x i))

/-- **Uniqueness.** An automorphism of `x` restricting to the local evaluations along every arrow
of `R` is the descended automorphism. -/
theorem coverAut_unique (hR : R ∈ J U) (hz : IsCompatible z) {x : F.obj (.mk (op U))} (a : Aut x)
    (ha : ∀ i : R.arrows.category,
      (F.map i.obj.hom.op.toLoc).toFunctor.mapAut x a = localAut z x i) :
    a = coverAut hR hz x := by
  refine Aut.ext (Iso.ext ((F.isPrestackFor' R hR).fullyFaithful.map_injective ?_))
  refine DescentData.hom_ext fun i ↦ ?_
  have h := congrArg (fun c : Aut _ ↦ c.asIso.hom) (ha i)
  rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom] at h
  rw [toDescentData_map_hom, toDescentData_map_hom, h, map_coverAut_hom]

/-- **Naturality.** Every morphism `f : x ⟶ y` over `U` intertwines the descended automorphisms. -/
@[reassoc]
theorem coverAut_naturality (hR : R ∈ J U) (hz : IsCompatible z) {x y : F.obj (.mk (op U))}
    (f : x ⟶ y) :
    f ≫ (coverAut hR hz y).asIso.hom = (coverAut hR hz x).asIso.hom ≫ f := by
  refine (F.isPrestackFor' R hR).fullyFaithful.map_injective (DescentData.hom_ext fun i ↦ ?_)
  simp only [Functor.map_comp, DescentData.comp_hom, toDescentData_map_hom, map_coverAut_hom]
  exact evaluation_naturality _ _ _

/-- The identity family descends to the identity automorphism. -/
@[simp]
theorem coverAut_one (hR : R ∈ J U) (x : F.obj (.mk (op U))) :
    coverAut (F := F) hR isCompatible_one x = 1 :=
  (coverAut_unique hR isCompatible_one 1 fun i ↦ by simp).symm

/-- The inverse family descends to the inverse automorphism. -/
@[simp]
theorem coverAut_inv (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    coverAut hR hz.inv x = (coverAut hR hz x)⁻¹ :=
  (coverAut_unique hR hz.inv _ fun i ↦ by
    rw [map_inv, mapAut_coverAut]
    exact (map_inv (evaluation _ _) (z i)).symm).symm

/-- The product family descends to the product automorphism. -/
@[simp]
theorem coverAut_mul (hR : R ∈ J U) (hz : IsCompatible z) (hw : IsCompatible w)
    (x : F.obj (.mk (op U))) :
    coverAut hR (hz.mul hw) x = coverAut hR hz x * coverAut hR hw x :=
  (coverAut_unique hR (hz.mul hw) _ fun i ↦ by
    rw [map_mul, mapAut_coverAut, mapAut_coverAut]
    exact (map_mul (evaluation _ _) (z i) (w i)).symm).symm

/-- The restrictions of a section `s ∈ ZF(U)` descend to its evaluation `ev_(𝟙, x)(s)`. -/
@[simp]
theorem coverAut_restrict (hR : R ∈ J U) (s : IntrinsicBandSections F U)
    (x : F.obj (.mk (op U))) :
    coverAut hR (isCompatible_restrict s) x = evaluation (𝟙 U) x s :=
  (coverAut_unique hR (isCompatible_restrict s) _ fun i ↦ by simp).symm

/-- **The descended centre unit.** For a covering sieve `R` of a prestack and a compatible family
`z`, the unit of the categorical centre of the fibre over `U` with component `coverAut(R, z, x)`
at every `x`. -/
noncomputable def coverCenter (hR : R ∈ J U) (hz : IsCompatible z) :
    (CatCenter (F.obj (.mk (op U))))ˣ :=
  (Aut.unitsEndEquivAut (𝟭 _)).symm
    (.of (NatIso.ofComponents (fun x ↦ (coverAut hR hz x).asIso)
      fun f ↦ coverAut_naturality hR hz f))

/-- The component of the descended centre unit at `x` is the descended automorphism of `x`. -/
@[simp]
theorem coverCenter_app (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    (coverCenter hR hz).val.app x = (coverAut hR hz x).asIso.hom :=
  (rfl)

/-- The component of the inverse of the descended centre unit at `x` is the inverse of the
descended automorphism of `x`. -/
@[simp]
theorem coverCenter_inv_app (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U))) :
    (coverCenter hR hz)⁻¹.val.app x = (coverAut hR hz x).asIso.inv :=
  (rfl)

/-- Pulling the descended centre unit back along an arrow `i` of `R` gives the component of `z_i`
at the identity. -/
theorem map_coverCenter_app (hR : R ∈ J U) (hz : IsCompatible z) (x : F.obj (.mk (op U)))
    (i : R.arrows.category) :
    (F.map i.obj.hom.op.toLoc).toFunctor.map ((coverCenter hR hz).val.app x) =
      ((z i).val i.obj.left (𝟙 _)).val.app ((F.map i.obj.hom.op.toLoc).toFunctor.obj x) := by
  rw [coverCenter_app, map_coverAut_hom, evaluation_asIso_hom]

/-- **Uniqueness of the descended centre unit.** A unit of the categorical centre whose pullback
along every arrow `i` of `R` at every object `x` is the component of `z_i` at the identity is the
descended centre unit. -/
theorem coverCenter_unique (hR : R ∈ J U) (hz : IsCompatible z)
    (a : (CatCenter (F.obj (.mk (op U))))ˣ)
    (ha : ∀ (x : F.obj (.mk (op U))) (i : R.arrows.category),
      (F.map i.obj.hom.op.toLoc).toFunctor.map (a.val.app x) =
        ((z i).val i.obj.left (𝟙 _)).val.app ((F.map i.obj.hom.op.toLoc).toFunctor.obj x)) :
    a = coverCenter hR hz := by
  refine Units.ext (CatCenter.ext _ _ fun x ↦ ?_)
  have h := coverAut_unique hR hz (.of ((Aut.unitsEndEquivAut (𝟭 _) a).asIso.app x)) fun i ↦
    Aut.ext (Iso.ext (by
      rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom]
      exact (ha x i).trans (evaluation_asIso_hom _ _ _).symm))
  rw [coverCenter_app]
  exact congrArg (fun b : Aut x ↦ b.asIso.hom) h

/-- The identity family descends to the identity centre unit. -/
@[simp]
theorem coverCenter_one (hR : R ∈ J U) : coverCenter (F := F) hR isCompatible_one = 1 :=
  (coverCenter_unique hR isCompatible_one 1 fun x i ↦ by simp).symm

/-- The inverse family descends to the inverse centre unit. -/
@[simp]
theorem coverCenter_inv (hR : R ∈ J U) (hz : IsCompatible z) :
    coverCenter hR hz.inv = (coverCenter hR hz)⁻¹ := by
  refine Units.ext (CatCenter.ext _ _ fun x ↦ ?_)
  simp [hz]

/-- The product family descends to the product centre unit. -/
@[simp]
theorem coverCenter_mul (hR : R ∈ J U) (hz : IsCompatible z) (hw : IsCompatible w) :
    coverCenter hR (hz.mul hw) = coverCenter hR hz * coverCenter hR hw := by
  refine Units.ext (CatCenter.ext _ _ fun x ↦ ?_)
  simp [hz, hw, CatCenter.mul_app']

/-- The restrictions of a section `s ∈ ZF(U)` descend to its component `s(U, 𝟙)`. -/
@[simp]
theorem coverCenter_restrict (hR : R ∈ J U) (s : IntrinsicBandSections F U) :
    coverCenter hR (isCompatible_restrict s) = s.val U (𝟙 U) := by
  refine Units.ext (CatCenter.ext _ _ fun x ↦ ?_)
  rw [coverCenter_app, coverAut_restrict, evaluation_asIso_hom]

/-- **Separation.** Two central sections over `U` whose restrictions along every arrow of a
covering sieve agree are equal. No gerbe, groupoid or commutativity hypothesis is needed. -/
theorem eq_of_restrict_eq (hR : R ∈ J U) {s t : IntrinsicBandSections F U}
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → restrict f s = restrict f t) : s = t := by
  ext V a x
  have hR' : R.pullback a ∈ J V := J.pullback_stable a hR
  refine (F.isPrestackFor' _ hR').fullyFaithful.map_injective (DescentData.hom_ext fun i ↦ ?_)
  have hi := congrArg (fun r : IntrinsicBandSections F i.obj.left ↦
    (r.val i.obj.left (𝟙 _)).val.app ((F.map i.obj.hom.op.toLoc).toFunctor.obj x))
    (h (i.obj.hom ≫ a) i.property)
  simp only [val_restrict, Category.id_comp] at hi
  simp only [toDescentData_map_hom, map_app]
  exact hi

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
