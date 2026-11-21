/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint
public import TauCeti.FieldTheory.IsSepClosed

/-!
# Extensions, functoriality, and Galois actions of geometric points

This file extends `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint` (defined in
`TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint`) with:

* **Constructors and ring-homomorphism characterization**: `of`, `ofOver`, `homOfRingHom`,
  `Hom.ringHom`, `isoOfRingEquiv`, and `Hom.isIso_iff_surjective_ringHom` (a morphism of
  geometric points is an isomorphism if and only if its underlying field homomorphism is
  surjective).
* **Pushforward along scheme morphisms**: the functor `GeometricPoint.map f` along `f : X ⟶ Y`,
  with `mapId` and `mapComp`.
* **Stalk isomorphisms and algebraic closures**: `stalkIso` packaged from
  `GrothendieckTopology.Point.sheafFiberIso`, together with `ofAlgClosure` and
  `ofSepToAlgClosure`, showing that `Spec kbar ⟶ Spec ksep` is an isomorphism in
  `GeometricPoint S` if and only if the base field is perfect while always inducing an isomorphism
  of étale stalks.
* **Galois actions over an arbitrary affine base**: `homOfAlgHom`, `isoOfAlgEquiv`,
  `autOfAlgEquiv`, `galStalkAut` (the left action of `Ω ≃ₐ[R] Ω` on stalks at `ofOver a Ω`), and
  `galMulEquivAutOp` (`(Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ` when `a` is a monomorphism).

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §§3–4.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section Category

variable {S : Scheme.{u}}

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

/-- Extracting the ring homomorphism from `homOfRingHom ι w` recovers `ι`. -/
@[simp]
theorem Hom.ringHom_homOfRingHom {s₁ s₂ : GeometricPoint S} (ι : s₂.Ω →+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom ι) ≫ s₂.hom = s₁.hom) :
    (homOfRingHom ι w).ringHom = ι := by
  have h : CommRingCat.ofHom (homOfRingHom ι w).ringHom = CommRingCat.ofHom ι :=
    Spec.map_injective (by rw [Hom.SpecMap_ringHom, homOfRingHom_hom])
  exact congrArg CommRingCat.Hom.hom h

/-- The ring homomorphism of the identity morphism is the identity ring homomorphism. -/
@[simp]
theorem Hom.ringHom_id (s : GeometricPoint S) :
    Hom.ringHom (𝟙 s) = RingHom.id s.Ω := by
  have h : CommRingCat.ofHom (Hom.ringHom (𝟙 s)) = CommRingCat.ofHom (RingHom.id s.Ω) :=
    Spec.map_injective (by rw [Hom.SpecMap_ringHom, id_hom, CommRingCat.ofHom_id, Spec.map_id])
  exact congrArg CommRingCat.Hom.hom h

/-- The ring homomorphism of a composite `f ≫ g` of morphisms of geometric points is
`f.ringHom.comp g.ringHom`. -/
@[simp]
theorem Hom.ringHom_comp {s₁ s₂ s₃ : GeometricPoint S} (f : s₁ ⟶ s₂) (g : s₂ ⟶ s₃) :
    (f ≫ g).ringHom = f.ringHom.comp g.ringHom := by
  have h : CommRingCat.ofHom (f ≫ g).ringHom =
      CommRingCat.ofHom (f.ringHom.comp g.ringHom) :=
    Spec.map_injective (by
      rw [Hom.SpecMap_ringHom, comp_hom, CommRingCat.ofHom_comp, Spec.map_comp,
        Hom.SpecMap_ringHom, Hom.SpecMap_ringHom])
  exact congrArg CommRingCat.Hom.hom h

/-- A morphism of geometric points lies over a single scheme-theoretic point of `S`. -/
theorem Hom.hom_default_eq {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
    s₁.hom default = s₂.hom default := by
  rw [← f.w, Scheme.Hom.comp_apply, Subsingleton.elim (f.hom default) default]

/-- Construct an isomorphism of geometric points `s₁ ≅ s₂` from a ring isomorphism
`e : s₂.Ω ≃+* s₁.Ω` compatible with the morphisms into `S`. -/
noncomputable def isoOfRingEquiv {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    s₁ ≅ s₂ where
  hom := homOfRingHom (e : s₂.Ω →+* s₁.Ω) w
  inv := homOfRingHom (e.symm : s₁.Ω →+* s₂.Ω) <| by
    rw [← w, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (e.symm : s₁.Ω →+* s₂.Ω).comp (e : s₂.Ω →+* s₁.Ω) = RingHom.id _ :=
      RingHom.ext e.symm_apply_apply
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  hom_inv_id := by
    ext : 1
    rw [comp_hom, homOfRingHom_hom, homOfRingHom_hom, id_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have h : (e : s₂.Ω →+* s₁.Ω).comp (e.symm : s₁.Ω →+* s₂.Ω) = RingHom.id _ :=
      RingHom.ext e.apply_symm_apply
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    ext : 1
    rw [comp_hom, homOfRingHom_hom, homOfRingHom_hom, id_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have h : (e.symm : s₁.Ω →+* s₂.Ω).comp (e : s₂.Ω →+* s₁.Ω) = RingHom.id _ :=
      RingHom.ext e.symm_apply_apply
    rw [h, CommRingCat.ofHom_id, Spec.map_id]

/-- The forward scheme morphism of `isoOfRingEquiv e w` is `Spec.map (CommRingCat.ofHom e)`. -/
@[simp]
theorem isoOfRingEquiv_hom_hom {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    (isoOfRingEquiv e w).hom.hom = Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) :=
  (rfl)

/-- The inverse scheme morphism of `isoOfRingEquiv e w` is
`Spec.map (CommRingCat.ofHom e.symm)`. -/
@[simp]
theorem isoOfRingEquiv_inv_hom {s₁ s₂ : GeometricPoint S} (e : s₂.Ω ≃+* s₁.Ω)
    (w : Spec.map (CommRingCat.ofHom (e : s₂.Ω →+* s₁.Ω)) ≫ s₂.hom = s₁.hom) :
    (isoOfRingEquiv e w).inv.hom =
      Spec.map (CommRingCat.ofHom (e.symm : s₁.Ω →+* s₂.Ω)) :=
  (rfl)

/-- A morphism of geometric points is an isomorphism if and only if its underlying field
homomorphism is surjective (equivalently, bijective). -/
theorem Hom.isIso_iff_surjective_ringHom {s₁ s₂ : GeometricPoint S} (f : s₁ ⟶ s₂) :
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

/-- The canonical isomorphism between `ofOver (𝟙 (Spec (.of R))) Ω` and
`of (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))`, witnessing the right identity law. -/
noncomputable def ofOverIdIso (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] :
    ofOver (𝟙 (Spec (.of R))) Ω ≅ of (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) where
  hom := ⟨𝟙 _, by simp⟩
  inv := ⟨𝟙 _, by simp⟩

/-- The forward scheme morphism of `ofOverIdIso R Ω` is the identity. -/
@[simp]
theorem ofOverIdIso_hom_hom (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] :
    (ofOverIdIso R Ω).hom.hom = 𝟙 (Spec (.of Ω)) :=
  (rfl)

/-- The inverse scheme morphism of `ofOverIdIso R Ω` is the identity. -/
@[simp]
theorem ofOverIdIso_inv_hom (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] :
    (ofOverIdIso R Ω).inv.hom = 𝟙 (Spec (.of Ω)) :=
  (rfl)

end Category

section Map

-- Exposed so `((map f).obj s).Ω` and `((map f).obj s).hom` unfold in statements of `mapId`
-- and `mapComp`.
/-- Pushforward of geometric points along a scheme morphism `f : X ⟶ Y`, sending `s` to
`s.hom ≫ f`. -/
@[expose, simps obj_hom map_hom]
noncomputable def map {X Y : Scheme.{u}} (f : X ⟶ Y) : GeometricPoint X ⥤ GeometricPoint Y where
  obj s := ⟨s.Ω, s.hom ≫ f⟩
  map φ := ⟨φ.hom, by rw [← Category.assoc, φ.w]⟩

/-- Pushforward along `𝟙 X` is naturally isomorphic to the identity functor. -/
noncomputable def mapId (X : Scheme.{u}) : map (𝟙 X) ≅ 𝟭 (GeometricPoint X) :=
  NatIso.ofComponents
    (fun s ↦
      { hom := ⟨𝟙 (Spec (.of s.Ω)), (Category.id_comp _).trans (Category.comp_id _).symm⟩
        inv := ⟨𝟙 (Spec (.of s.Ω)), (Category.id_comp _).trans (Category.comp_id _)⟩ })
    (fun _ ↦ by ext : 1; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_hom_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (rfl)

/-- The inverse component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_inv_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (rfl)

/-- Pushforward along a composite `f ≫ g` is naturally isomorphic to the composite of the
pushforwards. -/
noncomputable def mapComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents
    (fun s ↦
      { hom := ⟨𝟙 (Spec (.of s.Ω)), (Category.id_comp _).trans (Category.assoc _ _ _)⟩
        inv := ⟨𝟙 (Spec (.of s.Ω)), (Category.id_comp _).trans (Category.assoc _ _ _).symm⟩ })
    (fun _ ↦ by ext : 1; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The component of `mapComp f g` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapComp_hom_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (rfl)

/-- The inverse component of `mapComp f g` at `s` has the identity as underlying scheme
morphism. -/
@[simp]
theorem mapComp_inv_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (rfl)

end Map

section ToPoint

variable {S : Scheme.{u}}

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
  change (Scheme.pointSmallEtale s₂.hom).toPresheafFiber U u F.obj ≫
      ((toPointFunctor S).map φ).presheafFiber.app F.obj = _
  rw [GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact colimit.ι_desc _ _

section StalkIso

variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The natural isomorphism of stalk functors induced by a morphism `φ : s₁ ⟶ s₂` of geometric
points: stalks do not change under extension of the separably closed field. -/
noncomputable def stalkIso {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    (Scheme.pointSmallEtale s₂.hom).sheafFiber (A := A) ≅
      (Scheme.pointSmallEtale s₁.hom).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso (asIso ((toPointFunctor S).map φ)).symm A

/-- The forward direction of `stalkIso φ` is `((toPointFunctor S).map φ).sheafFiber`. -/
@[simp]
theorem stalkIso_hom {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂) :
    (stalkIso φ (A := A)).hom = ((toPointFunctor S).map φ).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberIso_hom _ A

/-- On germs, `stalkIso φ` sends the germ at `(U, u)` to the germ at `(U, φ ≫ u)`. -/
@[reassoc, elementwise]
theorem toPresheafFiber_stalkIso_hom_app {s₁ s₂ : GeometricPoint S} (φ : s₁ ⟶ s₂)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) (U : S.Etale)
    (u : (Scheme.pointSmallEtale s₂.hom).fiber.obj U) :
    (Scheme.pointSmallEtale s₂.hom).toPresheafFiber U u F.obj ≫ (stalkIso φ).hom.app F =
      (Scheme.pointSmallEtale s₁.hom).toPresheafFiber U
        ((Over.homMk φ.hom φ.w : Over.mk s₁.hom ⟶ Over.mk s₂.hom) ≫ u) F.obj := by
  rw [stalkIso_hom]
  exact toPresheafFiber_toPointFunctor_map_sheafFiber_app φ F U u

end StalkIso

/-- The canonical morphism from the algebraically closed geometric point over `s` to `s`,
exhibiting that algebraically closed points give the same stalks as separably closed ones. -/
noncomputable def ofAlgClosure (s : GeometricPoint S) :
    ofOver s.hom (AlgebraicClosure s.Ω) ⟶ s :=
  homOfRingHom (algebraMap s.Ω (AlgebraicClosure s.Ω)) rfl

/-- `ofAlgClosure s` is an isomorphism in `GeometricPoint S` if and only if `s.Ω` is already
algebraically closed (whereas `(toPointFunctor S).map (ofAlgClosure s)` is always an isomorphism
by `isIso_toPointFunctor_map`). -/
theorem isIso_ofAlgClosure_iff (s : GeometricPoint S) :
    IsIso (ofAlgClosure s) ↔ IsAlgClosed s.Ω := by
  rw [Hom.isIso_iff_surjective_ringHom, ofAlgClosure, Hom.ringHom_homOfRingHom,
    ← IsAlgClosed.iff_surjective_algebraMap s.Ω (AlgebraicClosure s.Ω)]

/-- For a separably closed separable extension `Ω` of a field `K`, `ofAlgClosure (ofOver a Ω)` is
an isomorphism in `GeometricPoint S` if and only if `K` is perfect. -/
theorem isIso_ofAlgClosure_ofOver_iff_perfectField {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω] :
    IsIso (ofAlgClosure (ofOver a Ω)) ↔ PerfectField K := by
  rw [isIso_ofAlgClosure_iff]
  exact IsSepClosed.isAlgClosed_iff_perfectField K Ω

/-- The canonical morphism from `ofOver a (AlgebraicClosure K)` to `ofOver a (SeparableClosure K)`.
It is an isomorphism in `GeometricPoint S` if and only if `K` is perfect
(`isIso_ofSepToAlgClosure_iff_perfectField`), while its image under `toPointFunctor S` is always
an isomorphism (`isIso_toPointFunctor_map`). -/
noncomputable def ofSepToAlgClosure {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    ofOver a (AlgebraicClosure K) ⟶ ofOver a (SeparableClosure K) :=
  homOfRingHom (algebraMap (SeparableClosure K) (AlgebraicClosure K)) <| by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]

/-- `ofSepToAlgClosure a` is an isomorphism in `GeometricPoint S` if and only if `K` is perfect. -/
theorem isIso_ofSepToAlgClosure_iff_perfectField {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) :
    IsIso (ofSepToAlgClosure a) ↔ PerfectField K := by
  rw [Hom.isIso_iff_surjective_ringHom, ofSepToAlgClosure, Hom.ringHom_homOfRingHom]
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K) (A := AlgebraicClosure K)
  rw [← IsAlgClosed.iff_surjective_algebraMap (SeparableClosure K) (AlgebraicClosure K),
    IsSepClosed.isAlgClosed_iff_perfectField K (SeparableClosure K)]

end ToPoint

section Actions

variable {S : Scheme.{u}}

section AutAction

variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- Evaluation of `stalkAction` at an étale sheaf `F`: an action of `(Aut s)ᵐᵒᵖ` by
automorphisms of the stalk `(pointSmallEtale s.hom).sheafFiber.obj F`. -/
noncomputable def stalkActionApp (s : GeometricPoint S)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (Aut s)ᵐᵒᵖ →* Aut ((Scheme.pointSmallEtale s.hom).sheafFiber.obj F) where
  toFun e := Aut.of ((stalkAction A s e).asIso.app F)
  map_one' := by ext : 2; rw [map_one]; rfl
  map_mul' e₁ e₂ := by ext : 2; rw [map_mul]; rfl

/-- The underlying morphism of `stalkActionApp s F (MulOpposite.op e)` is
`((toPointFunctor S).map e.asIso.hom).sheafFiber.app F`. -/
@[simp]
theorem stalkActionApp_asIso_hom (s : GeometricPoint S)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) (e : Aut s) :
    (stalkActionApp s F (MulOpposite.op e)).asIso.hom =
      ((toPointFunctor S).map e.asIso.hom).sheafFiber.app F :=
  congrArg (fun α ↦ α.app F) (stalkAction_apply A s (MulOpposite.op e))

/-- The action of `Aut s` on stalks is natural in the sheaf. -/
@[reassoc]
theorem stalkActionApp_naturality (s : GeometricPoint S)
    {F G : Sheaf (Scheme.smallEtaleTopology S) A} (f : F ⟶ G) (e : (Aut s)ᵐᵒᵖ) :
    (stalkActionApp s F e).asIso.hom ≫ (Scheme.pointSmallEtale s.hom).sheafFiber.map f =
      (Scheme.pointSmallEtale s.hom).sheafFiber.map f ≫ (stalkActionApp s G e).asIso.hom :=
  ((stalkAction A s e).asIso.hom.naturality f).symm

end AutAction

section Galois

variable {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ S)
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- An `R`-algebra endomorphism `σ : Ω →ₐ[R] Ω` induces an endomorphism `Spec σ` of `ofOver a Ω`
in `GeometricPoint S`. -/
noncomputable def homOfAlgHom (σ : Ω →ₐ[R] Ω) : ofOver a Ω ⟶ ofOver a Ω :=
  homOfRingHom σ.toRingHom <| by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : σ.toRingHom.comp (algebraMap R Ω) = algebraMap R Ω := RingHom.ext σ.commutes
    rw [h]

/-- The underlying scheme morphism of `homOfAlgHom a Ω σ` is `Spec.map (CommRingCat.ofHom σ)`. -/
@[simp]
theorem homOfAlgHom_hom (σ : Ω →ₐ[R] Ω) :
    (homOfAlgHom a Ω σ).hom = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  (rfl)

/-- The identity `R`-algebra endomorphism induces the identity of `ofOver a Ω`. -/
@[simp]
theorem homOfAlgHom_id : homOfAlgHom a Ω (AlgHom.id R Ω) = 𝟙 (ofOver a Ω) := by
  ext : 1
  simp [homOfAlgHom_hom]

/-- Composition of `R`-algebra endomorphisms maps covariantly to composition in
`GeometricPoint S`: `Spec (σ ∘ τ) = Spec σ ≫ Spec τ`. -/
@[simp]
theorem homOfAlgHom_comp (σ τ : Ω →ₐ[R] Ω) :
    homOfAlgHom a Ω (σ.comp τ) = homOfAlgHom a Ω σ ≫ homOfAlgHom a Ω τ := by
  ext : 1
  rw [comp_hom, homOfAlgHom_hom, homOfAlgHom_hom, homOfAlgHom_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- An automorphism `σ : Ω ≃ₐ[R] Ω` induces an automorphism `Spec σ` of `ofOver a Ω` in
`GeometricPoint S`. -/
noncomputable def isoOfAlgEquiv (σ : Ω ≃ₐ[R] Ω) : ofOver a Ω ≅ ofOver a Ω :=
  isoOfRingEquiv σ.toRingEquiv <| by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (σ.toRingEquiv : Ω →+* Ω).comp (algebraMap R Ω) = algebraMap R Ω :=
      RingHom.ext σ.commutes
    rw [h]

/-- The forward morphism of `isoOfAlgEquiv a Ω σ` is `homOfAlgHom a Ω σ`. -/
@[simp]
theorem isoOfAlgEquiv_hom (σ : Ω ≃ₐ[R] Ω) :
    (isoOfAlgEquiv a Ω σ).hom = homOfAlgHom a Ω σ.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_hom_hom, homOfAlgHom_hom]
  rfl

/-- The inverse morphism of `isoOfAlgEquiv a Ω σ` is `homOfAlgHom a Ω σ.symm`. -/
@[simp]
theorem isoOfAlgEquiv_inv (σ : Ω ≃ₐ[R] Ω) :
    (isoOfAlgEquiv a Ω σ).inv = homOfAlgHom a Ω σ.symm.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_inv_hom, homOfAlgHom_hom]
  rfl

/-- The group homomorphism `(Ω ≃ₐ[R] Ω) →* (Aut (ofOver a Ω))ᵐᵒᵖ` sending `σ` to `Spec σ`.
Because `Spec (σ * τ) = Spec σ ≫ Spec τ` while multiplication in `Aut` composes right-to-left,
this lands in the opposite group `(Aut (ofOver a Ω))ᵐᵒᵖ`. -/
noncomputable def autOfAlgEquiv : (Ω ≃ₐ[R] Ω) →* (Aut (ofOver a Ω))ᵐᵒᵖ where
  toFun σ := MulOpposite.op (Aut.of (isoOfAlgEquiv a Ω σ))
  map_one' := MulOpposite.unop_injective (by
    ext : 2
    simp only [MulOpposite.unop_op, MulOpposite.unop_one, Aut.one_asIso, Iso.refl_hom]
    exact (isoOfAlgEquiv_hom a Ω 1).trans (homOfAlgHom_id a Ω))
  map_mul' σ τ := MulOpposite.unop_injective (by
    ext : 2
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Aut.mul_asIso, Iso.trans_hom,
      isoOfAlgEquiv_hom, ← homOfAlgHom_comp]
    rfl)

/-- Unwrapping `autOfAlgEquiv a Ω σ` gives `isoOfAlgEquiv a Ω σ`. -/
@[simp]
theorem unop_autOfAlgEquiv (σ : Ω ≃ₐ[R] Ω) :
    (autOfAlgEquiv a Ω σ).unop.asIso = isoOfAlgEquiv a Ω σ :=
  (rfl)

/-- **The Galois action on stalks.** For a geometric point `ofOver a Ω` factoring through
`a : Spec (.of R) ⟶ S`, every `σ : Ω ≃ₐ[R] Ω` acts naturally on the stalk functor by the stalk
map of `Spec σ`. This is a group homomorphism into `Aut (pointSmallEtale _).sheafFiber`, so on
concrete stalks it defines a left action of `Ω ≃ₐ[R] Ω`. -/
noncomputable def galStalkAut {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A] :
    (Ω ≃ₐ[R] Ω) →* Aut ((Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber (A := A)) :=
  (stalkAction A (ofOver a Ω)).comp (autOfAlgEquiv a Ω)

/-- The natural transformation attached to `σ : Ω ≃ₐ[R] Ω` by `galStalkAut` is
`((toPointFunctor S).map (homOfAlgHom a Ω σ)).sheafFiber`. -/
@[simp]
theorem galStalkAut_asIso_hom {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (σ : Ω ≃ₐ[R] Ω) :
    (galStalkAut a Ω (A := A) σ).asIso.hom =
      ((toPointFunctor S).map (homOfAlgHom a Ω σ.toAlgHom)).sheafFiber :=
  (stalkAction_apply A (ofOver a Ω) (autOfAlgEquiv a Ω σ)).trans (by
    simp only [unop_autOfAlgEquiv, isoOfAlgEquiv_hom])

/-- The inverse natural transformation attached to `σ : Ω ≃ₐ[R] Ω` by `galStalkAut` is
`((toPointFunctor S).map (homOfAlgHom a Ω σ.symm)).sheafFiber`. -/
@[simp]
theorem galStalkAut_asIso_inv {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (σ : Ω ≃ₐ[R] Ω) :
    (galStalkAut a Ω (A := A) σ).asIso.inv =
      ((toPointFunctor S).map (homOfAlgHom a Ω σ.symm.toAlgHom)).sheafFiber := by
  change ((galStalkAut a Ω (A := A) σ)⁻¹).asIso.hom = _
  rw [← map_inv, galStalkAut_asIso_hom]
  rfl

/-- On germs, `galStalkAut a Ω σ` sends the germ at `(U, u)` to the germ at `(U, Spec σ ≫ u)`. -/
@[reassoc, elementwise]
theorem toPresheafFiber_galStalkAut_hom_app
    {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (σ : Ω ≃ₐ[R] Ω) (F : Sheaf (Scheme.smallEtaleTopology S) A) (U : S.Etale)
    (u : (Scheme.pointSmallEtale (ofOver a Ω).hom).fiber.obj U) :
    (Scheme.pointSmallEtale (ofOver a Ω).hom).toPresheafFiber U u F.obj ≫
        (galStalkAut a Ω σ).asIso.hom.app F =
      (Scheme.pointSmallEtale (ofOver a Ω).hom).toPresheafFiber U
        ((Over.homMk (homOfAlgHom a Ω σ.toAlgHom).hom (homOfAlgHom a Ω σ.toAlgHom).w :
          Over.mk (ofOver a Ω).hom ⟶ Over.mk (ofOver a Ω).hom) ≫ u)
        F.obj := by
  rw [galStalkAut_asIso_hom]
  exact toPresheafFiber_toPointFunctor_map_sheafFiber_app (homOfAlgHom a Ω σ.toAlgHom) F U u

/-- On stalks of sheaves of sets, `galStalkAut` is a left action of `Ω ≃ₐ[R] Ω`:
`(σ * τ) • z = σ • (τ • z)`. -/
theorem galStalkAut_mul_app_apply (σ τ : Ω ≃ₐ[R] Ω)
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber.obj F) :
    (galStalkAut a Ω (σ * τ)).asIso.hom.app F z =
      (galStalkAut a Ω σ).asIso.hom.app F ((galStalkAut a Ω τ).asIso.hom.app F z) := by
  rw [map_mul]
  rfl

/-- The map `autOfAlgEquiv a Ω` from `Ω ≃ₐ[R] Ω` into `(Aut (ofOver a Ω))ᵐᵒᵖ` is always
injective. -/
theorem injective_autOfAlgEquiv : Function.Injective (autOfAlgEquiv a Ω) := by
  intro σ τ h
  have h' : (isoOfAlgEquiv a Ω σ).hom = (isoOfAlgEquiv a Ω τ).hom :=
    congrArg (fun e : (Aut (ofOver a Ω))ᵐᵒᵖ ↦ e.unop.asIso.hom) h
  have hring := congrArg Hom.ringHom h'
  simp only [isoOfAlgEquiv_hom, homOfAlgHom, Hom.ringHom_homOfRingHom] at hring
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun hring x

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, every automorphism of `ofOver a Ω` in
`GeometricPoint S` comes from an `R`-algebra automorphism of `Ω`. -/
theorem surjective_autOfAlgEquiv [Mono a] : Function.Surjective (autOfAlgEquiv a Ω) := by
  intro e
  let f : ofOver a Ω ⟶ ofOver a Ω := e.unop.asIso.hom
  let g : ofOver a Ω ⟶ ofOver a Ω := e.unop.asIso.inv
  have hcomm (h : ofOver a Ω ⟶ ofOver a Ω) :
      h.ringHom.comp (algebraMap R Ω) = algebraMap R Ω := by
    have hspec : Spec.map (CommRingCat.ofHom (h.ringHom.comp (algebraMap R Ω))) ≫ a =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ a := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Hom.SpecMap_ringHom]
      exact h.w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono a).mp hspec))
  let fAlg : Ω →ₐ[R] Ω := { f.ringHom with commutes' := DFunLike.congr_fun (hcomm f) }
  let gAlg : Ω →ₐ[R] Ω := { g.ringHom with commutes' := DFunLike.congr_fun (hcomm g) }
  let σ : Ω ≃ₐ[R] Ω := AlgEquiv.ofAlgHom fAlg gAlg
    (AlgHom.ext fun x ↦ by
      have := congrArg (fun k : Ω →+* Ω ↦ k x) (Hom.ringHom_comp f g)
      simpa [f, g, fAlg, gAlg] using this.symm)
    (AlgHom.ext fun x ↦ by
      have := congrArg (fun k : Ω →+* Ω ↦ k x) (Hom.ringHom_comp g f)
      simpa [f, g, fAlg, gAlg] using this.symm)
  refine ⟨σ, MulOpposite.unop_injective ?_⟩
  ext : 3
  simp only [unop_autOfAlgEquiv, isoOfAlgEquiv_hom, homOfAlgHom_hom]
  have hσ : σ.toAlgHom.toRingHom = f.ringHom := RingHom.ext fun _ ↦ rfl
  rw [hσ, Hom.SpecMap_ringHom]

/-- **Automorphisms of a geometric point over a monomorphism.** When `a : Spec (.of R) ⟶ S` is a
monomorphism (for instance `𝟙 (Spec (.of R))` or `S.fromSpecResidueField x`), the automorphisms
of `ofOver a Ω` in `GeometricPoint S` are precisely the `Spec σ` for `σ : Ω ≃ₐ[R] Ω`. -/
noncomputable def galMulEquivAutOp [Mono a] :
    (Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ :=
  MulEquiv.ofBijective (autOfAlgEquiv a Ω)
    ⟨injective_autOfAlgEquiv a Ω, surjective_autOfAlgEquiv a Ω⟩

/-- The forward direction of `galMulEquivAutOp` is `autOfAlgEquiv`. -/
@[simp]
theorem galMulEquivAutOp_apply [Mono a] (σ : Ω ≃ₐ[R] Ω) :
    galMulEquivAutOp a Ω σ = autOfAlgEquiv a Ω σ :=
  (rfl)

end Galois

end Actions

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
