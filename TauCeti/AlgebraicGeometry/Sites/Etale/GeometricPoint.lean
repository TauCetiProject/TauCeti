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

/-!
# The category of geometric points of a scheme

A geometric point of a scheme `S` is a separably closed field `Ω` together with a morphism
`Spec Ω ⟶ S`. A morphism from `(Ω₁, s₁)` to `(Ω₂, s₂)` is a morphism `φ : Spec Ω₁ ⟶ Spec Ω₂` with
`φ ≫ s₂ = s₁` (Stacks, Tag 04FN). This file defines the category
`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint S` of geometric points and the covariant functor
`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toPointFunctor` to Mathlib's category of points of
the small étale site, sending `s` to `AlgebraicGeometry.Scheme.pointSmallEtale s.hom`.

The direction is Mathlib's: a morphism of points `Φ₁ ⟶ Φ₂` is a natural transformation
`Φ₂.fiber ⟶ Φ₁.fiber`. The fibre of `pointSmallEtale s` at an étale `U ⟶ S` is the set of lifts of
`s` to `U`, and `φ` sends a lift `u` of `s₂` to the lift `φ ≫ u` of `s₁`. The stalk at `s` is the
fibre functor of this point on sheaves, so stalks are contravariant in the geometric point: `φ`
induces a map from stalks at `s₂` to stalks at `s₁`.

Every morphism of geometric points induces an isomorphism of points
(`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.isIso_toPointFunctor_map`), so stalks do not
change under extension of the separably closed field; in particular algebraically closed points
have the same stalks as separably closed ones. This rests on the fact that the residue field
extensions of an étale morphism are finite separable, so their embeddings into an extension of a
separably closed field `Ω₂` all land in `Ω₂`
(`AlgebraicGeometry.Scheme.Hom.bijective_comp_of_formallyUnramified`).

For a point `x` of `S`, `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPoint x` is the
geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` through the separable closure of the residue field. These are
exactly the geometric points of Mathlib's
`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'`, so they form a
conservative family of points of the small étale site. Their automorphisms are the spectra of the
elements of the absolute Galois group `Gal(κ(x)ˢᵉᵖ/κ(x))`
(`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPointAutMulEquiv`). Since `Spec` reverses
composition, `σ ↦ Spec σ` reverses multiplication, and letting `σ` act on stalks at `ofPoint x`
through the stalk map of `Spec σ` is a left action of the Galois group.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint S`: the category of geometric points of `S`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toPointFunctor S`: the functor to points of
  the small étale site of `S`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.isIso_toPointFunctor_map`: every morphism of
  geometric points induces an isomorphism of points, hence isomorphisms of stalks.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPoint x`: the geometric point through the
  separable closure of the residue field at `x`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPointAutMulEquiv x`: the automorphism group
  of `ofPoint x` is the opposite of the absolute Galois group of `κ(x)`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkAction s`: the right action of the
  automorphisms of `s` on the stalks at `s`, naturally in the sheaf.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.galoisStalkAction x`: the left action of
  `Gal(κ(x)ˢᵉᵖ/κ(x))` on the stalks at `ofPoint x`.

## References

* The Stacks Project, Tag 04FN (geometric points) and Tag 03PO (stalks of étale sheaves).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §3.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

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

/-- A ring endomorphism `g` of `κ(x)ˢᵉᵖ` defines an endomorphism `Spec g` of the geometric point
`ofPoint x` exactly when it fixes `κ(x)`. -/
lemma SpecMap_comp_ofPoint_hom_eq_iff (x : S)
    (g : CommRingCat.of (ofPoint x).Ω ⟶ .of (ofPoint x).Ω) :
    Spec.map g ≫ (ofPoint x).hom = (ofPoint x).hom ↔
      CommRingCat.ofHom (algebraMap (S.residueField x) (SeparableClosure _)) ≫ g =
        CommRingCat.ofHom (algebraMap (S.residueField x) (SeparableClosure _)) := by
  rw [ofPoint_hom, ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj]

/-- The automorphism `Spec σ` of the geometric point `ofPoint x` given by an element `σ` of the
absolute Galois group of `κ(x)`. -/
noncomputable def ofPointIsoOfAlgEquiv (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) : ofPoint x ≅ ofPoint x :=
  isoMk (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op)
    ((SpecMap_comp_ofPoint_hom_eq_iff x _).mpr (CommRingCat.hom_ext (RingHom.ext σ.commutes)))

@[simp]
lemma ofPointIsoOfAlgEquiv_hom_hom (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointIsoOfAlgEquiv x σ).hom.hom =
      Spec.map (CommRingCat.ofHom (σ : (ofPoint x).Ω →+* (ofPoint x).Ω)) :=
  (rfl)

@[simp]
lemma ofPointIsoOfAlgEquiv_inv_hom (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointIsoOfAlgEquiv x σ).inv.hom =
      Spec.map (CommRingCat.ofHom (σ.symm : (ofPoint x).Ω →+* (ofPoint x).Ω)) :=
  (rfl)

/-- The ring endomorphism of `κ(x)ˢᵉᵖ` underlying an endomorphism of the geometric point
`ofPoint x` fixes `κ(x)`. -/
lemma algebraMap_comp_preimage_hom (x : S) (f : ofPoint x ⟶ ofPoint x) :
    CommRingCat.ofHom (algebraMap (S.residueField x) (SeparableClosure _)) ≫ Spec.preimage f.hom =
      CommRingCat.ofHom (algebraMap (S.residueField x) (SeparableClosure _)) := by
  rw [← SpecMap_comp_ofPoint_hom_eq_iff, Spec.map_preimage, Hom.w]

/-- The element of the absolute Galois group of `κ(x)` underlying an automorphism of the geometric
point `ofPoint x`: the ring automorphism of `κ(x)ˢᵉᵖ` whose spectrum it is. -/
noncomputable def ofPointAutToAlgEquiv (x : S) (φ : Aut (ofPoint x)) :
    SeparableClosure (S.residueField x) ≃ₐ[S.residueField x] SeparableClosure (S.residueField x) :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.Spec.preimageIso ((forget S).mapIso φ.asIso)).unop.commRingCatIsoToRingEquiv)
    fun r ↦ congr(($(algebraMap_comp_preimage_hom x φ.asIso.hom)).hom r)

@[simp]
lemma ofPointAutToAlgEquiv_apply (x : S) (φ : Aut (ofPoint x)) (r : SeparableClosure _) :
    ofPointAutToAlgEquiv x φ r = (Spec.preimage φ.asIso.hom.hom).hom r :=
  (rfl)

lemma ofHom_ofPointAutToAlgEquiv (x : S) (φ : Aut (ofPoint x)) :
    CommRingCat.ofHom (ofPointAutToAlgEquiv x φ : (ofPoint x).Ω →+* (ofPoint x).Ω) =
      Spec.preimage φ.asIso.hom.hom :=
  (rfl)

/-- **The automorphisms of `ofPoint x` are the Galois automorphisms.** Every automorphism of the
geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` is `Spec σ` for a unique `σ ∈ Gal(κ(x)ˢᵉᵖ/κ(x))`. Since
`Spec (σ * τ) = Spec σ ≫ Spec τ` and `Aut` multiplies in the order of function composition, this is
an isomorphism with the opposite group. -/
noncomputable def ofPointAutMulEquiv (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) ≃* (Aut (ofPoint x))ᵐᵒᵖ where
  toFun σ := .op (.of (ofPointIsoOfAlgEquiv x σ))
  invFun φ := ofPointAutToAlgEquiv x φ.unop
  left_inv σ := by
    ext r
    simp [ofPointIsoOfAlgEquiv_hom_hom]
  right_inv φ := by
    ext1
    rw [MulOpposite.unop_op, ofPointIsoOfAlgEquiv_hom_hom, ofHom_ofPointAutToAlgEquiv,
      Spec.map_preimage]
  map_mul' σ τ := by
    ext1
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Aut.mul_asIso, Iso.trans_hom, comp_hom,
      ofPointIsoOfAlgEquiv_hom_hom, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (AlgEquiv.mul_apply σ τ)))

@[simp]
lemma ofPointAutMulEquiv_apply (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointAutMulEquiv x σ).unop.asIso = ofPointIsoOfAlgEquiv x σ :=
  (rfl)

@[simp]
lemma ofPointAutMulEquiv_symm_apply (x : S) (φ : (Aut (ofPoint x))ᵐᵒᵖ) :
    (ofPointAutMulEquiv x).symm φ = ofPointAutToAlgEquiv x φ.unop :=
  (rfl)

section Stalk

variable (A : Type*) [Category* A] [HasColimitsOfSize.{u, u} A]

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

/-- **The Galois action on stalks at `ofPoint x`.** An element `σ` of `Gal(κ(x)ˢᵉᵖ/κ(x))` acts on
the stalks at `ofPoint x`, naturally in the sheaf, through the stalk map of `Spec σ`. Since `Spec`
reverses composition this is a left action. -/
noncomputable def galoisStalkAction (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) →*
      Aut (((toPointFunctor S).obj (ofPoint x)).sheafFiber (A := A)) :=
  (stalkAction A (ofPoint x)).comp (ofPointAutMulEquiv x).toMonoidHom

@[simp]
lemma galoisStalkAction_apply (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (galoisStalkAction A x σ).asIso.hom =
      ((toPointFunctor S).map (ofPointIsoOfAlgEquiv x σ).hom).sheafFiber :=
  (rfl)

end Stalk

end GeometricPoint

end TauCeti.AlgebraicGeometry.Scheme
