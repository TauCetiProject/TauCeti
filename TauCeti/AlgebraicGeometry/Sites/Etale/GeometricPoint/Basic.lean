/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.CategoryTheory.Sites.Point.Category
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# The category of geometric points of a scheme

A geometric point of a scheme `S` is a separably closed field `Ω` together with a morphism
`Spec Ω ⟶ S`. A morphism from `(Ω₁, s₁)` to `(Ω₂, s₂)` is a morphism `φ : Spec Ω₁ ⟶ Spec Ω₂` with
`φ ≫ s₂ = s₁` (Stacks, Tag 04FN). This file defines the category
`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint S` of geometric points, its ring-homomorphism
interface (`homOfRingHom`, `Hom.ringHom`, `homOfRingHom_ringHom`, `isoOfRingEquiv`,
`Hom.isIso_iff_ringHom_surjective`), and the covariant functor
`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toPointFunctor` to Mathlib's category of points of
the small étale site, sending `s` to `AlgebraicGeometry.Scheme.pointSmallEtale s.hom`.

The direction is Mathlib's: a morphism of points `Φ₁ ⟶ Φ₂` is a natural transformation
`Φ₂.fiber ⟶ Φ₁.fiber`. The fibre of `pointSmallEtale s` at an étale `U ⟶ S` is the set of lifts of
`s` to `U`, and `φ` sends a lift `u` of `s₂` to the lift `φ ≫ u` of `s₁`. The stalk at `s` is the
fibre functor of this point on sheaves, so stalks are contravariant in the geometric point: `φ`
induces a map from stalks at `s₂` to stalks at `s₁`.

Every morphism of geometric points induces an isomorphism of points
(`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.isIso_toPointFunctor_map`), packaged as
`stalkIso`, so stalks do not change under extension of the separably closed field; in particular
algebraically closed points have the same stalks as separably closed ones. This rests on the fact
that the residue field extensions of an étale morphism are finite separable, so their embeddings
into an extension of a separably closed field `Ω₂` all land in `Ω₂`
(`AlgebraicGeometry.Scheme.Hom.bijective_comp_of_formallyUnramified`).

For a point `x` of `S`, `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPoint x` is the
geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` through the separable closure of the residue field. These are
exactly the geometric points of Mathlib's
`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'`, so they form a
conservative family of points of the small étale site. Automorphisms of a geometric point `s` act
on stalks via `stalkAction` and `stalkActionApp`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint S`: the category of geometric points of `S`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.homOfRingHom`, `Hom.ringHom`, `isoOfRingEquiv`,
  `Hom.isIso_iff_ringHom_surjective`: ring-homomorphism characterization of morphisms and
  isomorphisms of geometric points.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toPointFunctor S`: the functor to points of
  the small étale site of `S`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.isIso_toPointFunctor_map`, `stalkIso`: every
  morphism of geometric points induces an isomorphism of points, hence isomorphisms of stalks.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPoint x`: the geometric point through the
  separable closure of the residue field at `x`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkAction s`, `stalkActionApp s F`: the
  right action of the automorphisms of `s` on the stalks at `s`, naturally in the sheaf.

## References

* The Stacks Project, [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN) (geometric points) and
  [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) (stalks of étale sheaves).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §3.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme

/-- A geometric point of a scheme `S`: a separably closed field `Ω` with a morphism
`Spec Ω ⟶ S`. -/
structure GeometricPoint (S : Scheme.{u}) where
  /-- The separably closed field of the geometric point. -/
  Ω : Type u
  [field : Field Ω]
  [isSepClosed : IsSepClosed Ω]
  /-- The morphism `Spec Ω ⟶ S`. -/
  hom : Spec (.of Ω) ⟶ S

namespace GeometricPoint

attribute [instance] field isSepClosed

section Category

variable {S : Scheme.{u}}

/-- A morphism of geometric points `(Ω₁, s₁) ⟶ (Ω₂, s₂)`: a morphism `Spec Ω₁ ⟶ Spec Ω₂` over
`S`. -/
@[ext]
structure Hom (s₁ s₂ : GeometricPoint S) where
  /-- The underlying morphism of spectra. -/
  hom : Spec (.of s₁.Ω) ⟶ Spec (.of s₂.Ω)
  w : hom ≫ s₂.hom = s₁.hom := by cat_disch

attribute [reassoc (attr := simp)] Hom.w

noncomputable instance : Category (GeometricPoint S) where
  Hom := Hom
  id s := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by simp⟩

@[ext]
lemma hom_ext {s₁ s₂ : GeometricPoint S} {f g : s₁ ⟶ s₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (s : GeometricPoint S) : Hom.hom (𝟙 s) = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {s₁ s₂ s₃ : GeometricPoint S} (f : s₁ ⟶ s₂) (g : s₂ ⟶ s₃) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The morphism of geometric points given by a morphism of spectra over `S`. -/
@[expose, simps]
def homMk {s₁ s₂ : GeometricPoint S} (φ : Spec (.of s₁.Ω) ⟶ Spec (.of s₂.Ω))
    (w : φ ≫ s₂.hom = s₁.hom := by cat_disch) : s₁ ⟶ s₂ :=
  ⟨φ, w⟩

/-- The isomorphism of geometric points given by an isomorphism of spectra over `S`. -/
noncomputable def isoMk {s₁ s₂ : GeometricPoint S} (e : Spec (.of s₁.Ω) ≅ Spec (.of s₂.Ω))
    (w : e.hom ≫ s₂.hom = s₁.hom := by cat_disch) : s₁ ≅ s₂ where
  hom := homMk e.hom w
  inv := homMk e.inv (by rw [Iso.inv_comp_eq, w])
  hom_inv_id := by ext1; simp
  inv_hom_id := by ext1; simp

@[simp]
lemma isoMk_hom_hom {s₁ s₂ : GeometricPoint S} (e : Spec (.of s₁.Ω) ≅ Spec (.of s₂.Ω))
    (w : e.hom ≫ s₂.hom = s₁.hom) : (isoMk e w).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom {s₁ s₂ : GeometricPoint S} (e : Spec (.of s₁.Ω) ≅ Spec (.of s₂.Ω))
    (w : e.hom ≫ s₂.hom = s₁.hom) : (isoMk e w).inv.hom = e.inv :=
  (rfl)

/-- Bundle a morphism `s : Spec (.of Ω) ⟶ S` from a separably closed field `Ω` as an object of
`GeometricPoint S`. -/
abbrev of {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) : GeometricPoint S :=
  ⟨Ω, s⟩

/-- The geometric point of `S` obtained by extending a morphism `a : Spec (.of R) ⟶ S` to a
separably closed `R`-algebra `Ω`. -/
noncomputable abbrev ofOver {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ S)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] : GeometricPoint S :=
  .of (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ a)

/-- Construct a morphism of geometric points `s₁ ⟶ s₂` from a ring homomorphism
`ι : s₂.Ω →+* s₁.Ω` compatible with the morphisms into `S`. -/
noncomputable def homOfRingHom {s₁ s₂ : GeometricPoint S} (ι : s₂.Ω →+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom ι) ≫ s₂.hom = s₁.hom) : s₁ ⟶ s₂ :=
  homMk (Spec.map (CommRingCat.ofHom ι)) w

/-- The underlying scheme morphism of `homOfRingHom ι w` is `Spec.map (CommRingCat.ofHom ι)`. -/
@[simp]
theorem homOfRingHom_hom {s₁ s₂ : GeometricPoint S} (ι : s₂.Ω →+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom ι) ≫ s₂.hom = s₁.hom) :
    (homOfRingHom ι w).hom = Spec.map (CommRingCat.ofHom ι) :=
  (rfl)

/-- The field homomorphism `s₂.Ω →+* s₁.Ω` whose spectrum is the morphism `f : s₁ ⟶ s₂`
of geometric points. -/
noncomputable def Hom.ringHom {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    s₂.Ω →+* s₁.Ω :=
  (Scheme.Spec.preimage f.hom).unop.hom

/-- The spectrum of `f.ringHom` recovers `f.hom`. -/
@[simp]
theorem Hom.SpecMap_ringHom {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    Spec.map (CommRingCat.ofHom f.ringHom) = f.hom :=
  Scheme.Spec.map_preimage f.hom

/-- The spectrum of `f.ringHom` is compatible with the morphisms into `S`. -/
theorem Hom.SpecMap_ringHom_comp {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    Spec.map (CommRingCat.ofHom f.ringHom) ≫ s₂.hom = s₁.hom := by
  rw [Hom.SpecMap_ringHom, f.w]

/-- `Hom.ringHom` is injective on morphisms of geometric points. -/
theorem Hom.ringHom_injective {s₁ s₂ : GeometricPoint S} :
    Function.Injective (Hom.ringHom (s₁ := s₁) (s₂ := s₂)) := by
  intro f g h
  ext : 1
  rw [← Hom.SpecMap_ringHom f, ← Hom.SpecMap_ringHom g, h]

/-- Extracting the ring homomorphism from `homOfRingHom ι w` recovers `ι`. -/
@[simp]
theorem Hom.ringHom_homOfRingHom {s₁ s₂ : GeometricPoint S} (ι : s₂.Ω →+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom ι) ≫ s₂.hom = s₁.hom) :
    (homOfRingHom ι w).ringHom = ι :=
  TauCeti.AlgebraicGeometry.ringHom_eq_of_SpecMap_eq (by
    rw [Hom.SpecMap_ringHom, homOfRingHom_hom])

/-- Reconstructing a morphism of geometric points from its underlying ring homomorphism recovers the
morphism. -/
@[simp]
theorem homOfRingHom_ringHom {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    homOfRingHom f.ringHom f.SpecMap_ringHom_comp = f :=
  Hom.ringHom_injective (Hom.ringHom_homOfRingHom _ _)

/-- The ring homomorphism of the identity morphism is the identity ring homomorphism. -/
@[simp]
theorem Hom.ringHom_id (s : GeometricPoint S) :
    Hom.ringHom (𝟙 s) = RingHom.id s.Ω :=
  TauCeti.AlgebraicGeometry.ringHom_eq_of_SpecMap_eq
    (by rw [Hom.SpecMap_ringHom, id_hom, CommRingCat.ofHom_id, Spec.map_id])

/-- The ring homomorphism of a composite `f ≫ g` of morphisms of geometric points is
`f.ringHom.comp g.ringHom`. -/
@[simp]
theorem Hom.ringHom_comp {s₁ s₂ s₃ : GeometricPoint S} (f : s₁ ⟶ s₂) (g : s₂ ⟶ s₃) :
    (f ≫ g).ringHom = f.ringHom.comp g.ringHom :=
  TauCeti.AlgebraicGeometry.ringHom_eq_of_SpecMap_eq (by
    rw [Hom.SpecMap_ringHom, comp_hom, CommRingCat.ofHom_comp, Spec.map_comp,
      Hom.SpecMap_ringHom, Hom.SpecMap_ringHom])

/-- A morphism of geometric points lies over a single scheme-theoretic point of `S`. -/
theorem Hom.hom_default_eq {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    s₁.hom default = s₂.hom default := by
  rw [← f.w, Scheme.Hom.comp_apply, Subsingleton.elim (f.hom default) default]

/-- Construct an isomorphism of geometric points `s₁ ≅ s₂` from a ring isomorphism
`e : s₂.Ω ≃+* s₁.Ω` compatible with the morphisms into `S`. -/
noncomputable def isoOfRingEquiv {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    s₁ ≅ s₂ :=
  isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) w

/-- The forward scheme morphism of `isoOfRingEquiv e w` is `Spec.map (CommRingCat.ofHom e)`. -/
@[simp]
theorem isoOfRingEquiv_hom_hom {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    (isoOfRingEquiv e w).hom.hom = Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) :=
  isoMk_hom_hom _ w

/-- The inverse scheme morphism of `isoOfRingEquiv e w` is
`Spec.map (CommRingCat.ofHom e.symm)`. -/
@[simp]
theorem isoOfRingEquiv_inv_hom {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    (isoOfRingEquiv e w).inv.hom =
      Spec.map (CommRingCat.ofHom (e.symm : s₁.Ω →+* s₂.Ω)) :=
  isoMk_inv_hom _ w

/-- A morphism of geometric points is an isomorphism if and only if its underlying field
homomorphism is surjective (equivalently, bijective). -/
theorem Hom.isIso_iff_ringHom_surjective {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    IsIso f ↔ Function.Surjective f.ringHom := by
  constructor
  · intro _ x
    refine ⟨(inv f).ringHom x, ?_⟩
    have h := congrArg (fun g : s₁.Ω →+* s₁.Ω ↦ g x) (Hom.ringHom_comp f (inv f))
    simpa using h.symm
  · intro hsurj
    let e : s₂.Ω ≃+* s₁.Ω := RingEquiv.ofBijective f.ringHom ⟨f.ringHom.injective, hsurj⟩
    have he : (e : s₂.Ω →+* s₁.Ω) = f.ringHom := RingHom.ext fun _ ↦ rfl
    have hw : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom := by
      rw [he, Hom.SpecMap_ringHom, f.w]
    have hf : f = (isoOfRingEquiv e hw).hom := by
      ext : 1
      rw [isoOfRingEquiv_hom_hom, he, Hom.SpecMap_ringHom]
    rw [hf]
    infer_instance

variable (S) in
/-- The functor sending a geometric point `(Ω, s)` of `S` to the scheme `Spec Ω`. -/
@[expose, simps]
noncomputable def forget : GeometricPoint S ⥤ Scheme.{u} where
  obj s := Spec (.of s.Ω)
  map f := f.hom

/-- Two automorphisms in `(Aut s)ᵐᵒᵖ` are equal when their underlying morphisms of spectra are. -/
@[ext]
lemma autOp_ext {s : GeometricPoint S} {φ ψ : (Aut s)ᵐᵒᵖ}
    (h : φ.unop.asIso.hom.hom = ψ.unop.asIso.hom.hom) : φ = ψ :=
  MulOpposite.unop_injective (Aut.ext (Iso.ext (hom_ext h)))

end Category

section ToPoint

variable {S : Scheme.{u}}

variable (S) in
/-- The functor from geometric points of `S` to points of the small étale site of `S`, sending
`s` to `AlgebraicGeometry.Scheme.pointSmallEtale s.hom`. A morphism `φ : s₁ ⟶ s₂` sends a lift
`u` of `s₂` to an étale `S`-scheme to the lift `φ ≫ u` of `s₁`. -/
@[expose, simps obj]
noncomputable def toPointFunctor : GeometricPoint S ⥤ (Scheme.smallEtaleTopology S).Point where
  obj s := Scheme.pointSmallEtale s.hom
  map φ := ⟨Functor.whiskerLeft (Scheme.Etale.forget S)
    (coyoneda.map (Over.homMk φ.hom φ.w : Over.mk _ ⟶ Over.mk _).op)⟩
  map_id _ := by ext U u; exact Over.OverMorphism.ext (Category.id_comp _)
  map_comp _ _ := by ext U u; exact Over.OverMorphism.ext (Category.assoc _ _ _)

@[simp]
lemma toPointFunctor_map_hom_app_left {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂)
    (U : S.Etale) (u : Over.mk s₂.hom ⟶ (Scheme.Etale.forget S).obj U) :
    (((toPointFunctor S).map φ).hom.app U u : Over.mk s₁.hom ⟶ _).left = φ.hom ≫ u.left :=
  rfl

/-- On lifts to an étale `S`-scheme `U`, `(toPointFunctor S).map φ` acts by precomposition with
`φ`. -/
@[simp]
theorem toPointFunctor_map_hom_app_apply {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) (U : S.Etale)
    (u : (Scheme.pointSmallEtale s₂.hom).fiber.obj U) :
    ((toPointFunctor S).map φ).hom.app U u =
      (Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫ u :=
  (rfl)

/-- On germs, the stalk map `((toPointFunctor S).map φ).sheafFiber` induced by a morphism
`φ : s₁ ⟶ s₂` of geometric points sends the germ at `(U, u)` to the germ at `(U, φ ≫ u)`. -/
@[reassoc, elementwise]
theorem toPresheafFiber_toPointFunctor_map_sheafFiber_app
    {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) (U : S.Etale)
    (u : (Scheme.pointSmallEtale s₂.hom).fiber.obj U) :
    (Scheme.pointSmallEtale s₂.hom).toPresheafFiber U u F.obj ≫
        ((toPointFunctor S).map φ).sheafFiber.app F =
      (Scheme.pointSmallEtale s₁.hom).toPresheafFiber U
        ((Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫ u) F.obj := by
  rw [Functor.whiskerLeft_app, GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact ((toPointFunctor S).obj s₂).toPresheafFiber_presheafFiberDesc _ _ U u

/-- **Stalks do not change under extension of the separably closed field.** Every morphism of
geometric points induces an isomorphism of points of the small étale site. -/
instance isIso_toPointFunctor_map {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    IsIso ((toPointFunctor S).map φ) := by
  rw [GrothendieckTopology.Point.isIso_iff_isIso_hom, NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  have : Etale U.hom := U.prop
  -- Identify lifts in `Over S` with lifts of the underlying morphisms of schemes.
  let e (s : GeometricPoint S) (t : Spec (.of s.Ω) ⟶ S) (ht : s.hom = t) :
      (Over.mk s.hom ⟶ (Scheme.Etale.forget S).obj U) ≃
        {u : Spec (.of s.Ω) ⟶ U.left // u ≫ U.hom = t} :=
    { toFun u := ⟨u.left, (Over.w u).trans ht⟩
      invFun u := Over.homMk u.val (u.property.trans ht.symm)
      left_inv _ := by cat_disch
      right_inv _ := rfl }
  exact (e s₁ _ φ.w.symm).symm.bijective.comp
    ((U.hom.bijective_comp_of_formallyUnramified φ.hom s₂.hom).comp (e s₂ _ rfl).bijective)

section StalkIso

variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The natural isomorphism of stalk functors induced by a morphism `φ : s₁ ⟶ s₂` of geometric
points: stalks do not change under extension of the separably closed field. -/
noncomputable def stalkIso {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    ((toPointFunctor S).obj s₂).sheafFiber (A := A) ≅
      ((toPointFunctor S).obj s₁).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso (asIso ((toPointFunctor S).map φ)).symm A

/-- The forward direction of `stalkIso φ` is `((toPointFunctor S).map φ).sheafFiber`. -/
@[simp]
theorem stalkIso_hom {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    (stalkIso φ (A := A)).hom = ((toPointFunctor S).map φ).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso_hom _ A

/-- The inverse direction of `stalkIso φ` is `(inv ((toPointFunctor S).map φ)).sheafFiber`. -/
@[simp]
theorem stalkIso_inv {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    (stalkIso φ (A := A)).inv = (inv ((toPointFunctor S).map φ)).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso_inv _ A

/-- The stalk isomorphism induced by the identity morphism of geometric points is the identity. -/
@[simp]
theorem stalkIso_id (s : GeometricPoint S) :
    stalkIso (𝟙 s) (A := A) = Iso.refl _ := by
  ext1
  simp only [stalkIso_hom, CategoryTheory.Functor.map_id,
    GrothendieckTopology.Point.Hom.sheafFiber_id, Iso.refl_hom]

/-- Stalk isomorphisms are contravariantly functorial in morphisms of geometric points. -/
@[simp]
theorem stalkIso_comp {s₁ s₂ s₃ : GeometricPoint S} (φ : s₁ ⟶ s₂) (ψ : s₂ ⟶ s₃) :
    stalkIso (φ ≫ ψ) (A := A) = (stalkIso ψ).trans (stalkIso φ) := by
  ext1
  simp only [stalkIso_hom, CategoryTheory.Functor.map_comp,
    GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.trans_hom]

/-- The stalk isomorphism induced by the inverse of an isomorphism of geometric points is the
symmetric isomorphism. -/
@[simp]
theorem stalkIso_inv_eq {s₁ s₂ : GeometricPoint S} (e : s₁ ≅ s₂) :
    stalkIso e.inv (A := A) = (stalkIso e.hom).symm := by
  ext1
  rw [Iso.symm_hom, ← Category.id_comp (stalkIso e.hom).inv, Iso.eq_comp_inv]
  have h := congrArg Iso.hom (stalkIso_comp (A := A) e.hom e.inv)
  simpa using h.symm

end StalkIso

end ToPoint

section ResidueField

variable {S : Scheme.{u}}

/-- The geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` over a point `x` of `S`, through the separable closure
of the residue field at `x`. -/
noncomputable abbrev ofPoint (x : S) : GeometricPoint S where
  Ω := SeparableClosure (S.residueField x)
  hom := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) _)) ≫ S.fromSpecResidueField x

lemma ofPoint_hom (x : S) : (ofPoint x).hom =
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) (SeparableClosure _))) ≫
      S.fromSpecResidueField x :=
  rfl

/-- The geometric point `ofPoint x` lies over `x`. -/
lemma ofPoint_hom_apply (x : S) (y : Spec (.of (ofPoint x).Ω)) : (ofPoint x).hom y = x := by
  rw [ofPoint_hom, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end ResidueField

section Stalk

variable {S : Scheme.{u}} (A : Type u') [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The automorphisms of a geometric point act on its stalks**, naturally in the sheaf: `φ`
acts through the stalk map of the isomorphism of points `(toPointFunctor S).map φ`. Stalks are
contravariant in the geometric point, so this is a right action, a homomorphism from the opposite
group. -/
noncomputable def stalkAction (s : GeometricPoint S) :
    (Aut s)ᵐᵒᵖ →* Aut (((toPointFunctor S).obj s).sheafFiber (A := A)) where
  toFun φ := .of (asIso ((toPointFunctor S).map φ.unop.asIso.hom).sheafFiber)
  map_one' := by
    ext1
    ext1
    simp
  map_mul' φ ψ := by
    ext1
    ext1
    simp

@[simp]
lemma stalkAction_apply (s : GeometricPoint S) (φ : (Aut s)ᵐᵒᵖ) :
    (stalkAction A s φ).asIso.hom = ((toPointFunctor S).map φ.unop.asIso.hom).sheafFiber :=
  (rfl)

/-- Evaluation of `stalkAction` at an étale sheaf `F`: the right action of `Aut s` (equivalently
the left action of `(Aut s)ᵐᵒᵖ`) by automorphisms of the stalk
`(pointSmallEtale s.hom).sheafFiber.obj F`. -/
noncomputable def stalkActionApp (s : GeometricPoint S)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (Aut s)ᵐᵒᵖ →* Aut ((Scheme.pointSmallEtale s.hom).sheafFiber.obj F) :=
  (Functor.mapAut (X := ((toPointFunctor S).obj s).sheafFiber)
    ((CategoryTheory.evaluation (Sheaf (Scheme.smallEtaleTopology S) A) A).obj F)).comp
    (stalkAction A s)

/-- The underlying morphism of `stalkActionApp A s F (MulOpposite.op e)` is
`((toPointFunctor S).map e.asIso.hom).sheafFiber.app F`. -/
@[simp]
theorem stalkActionApp_asIso_hom (s : GeometricPoint S)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) (e : Aut s) :
    (stalkActionApp A s F (MulOpposite.op e)).asIso.hom =
      ((toPointFunctor S).map e.asIso.hom).sheafFiber.app F := by
  dsimp only [stalkActionApp]
  exact congrArg (fun α ↦ α.app F) (stalkAction_apply A s (MulOpposite.op e))

/-- The right action of `Aut s` (equivalently the left action of `(Aut s)ᵐᵒᵖ`) on stalks is
natural in the sheaf. -/
@[reassoc]
theorem stalkActionApp_naturality (s : GeometricPoint S)
    {F G : Sheaf (Scheme.smallEtaleTopology S) A} (f : F ⟶ G) (e : (Aut s)ᵐᵒᵖ) :
    (stalkActionApp A s F e).asIso.hom ≫ (Scheme.pointSmallEtale s.hom).sheafFiber.map f =
      (Scheme.pointSmallEtale s.hom).sheafFiber.map f ≫ (stalkActionApp A s G e).asIso.hom := by
  dsimp only [stalkActionApp]
  exact ((stalkAction A s e).asIso.hom.naturality f).symm

end Stalk

end GeometricPoint

end TauCeti.AlgebraicGeometry.Scheme
