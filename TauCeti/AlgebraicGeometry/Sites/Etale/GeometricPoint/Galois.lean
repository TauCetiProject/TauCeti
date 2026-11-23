/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Basic

/-!
# Galois actions on étale stalks at geometric points

For a geometric point `ofOver a Ω` factoring through `a : Spec (.of R) ⟶ S`, every `R`-algebra
endomorphism `σ : Ω →ₐ[R] Ω` induces an endomorphism `homOfAlgHom a Ω σ` in `GeometricPoint S`.
When `σ : Ω ≃ₐ[R] Ω` is an automorphism, `isoOfAlgEquiv a Ω σ` is an automorphism in
`GeometricPoint S` (`autOfAlgEquiv a Ω`), giving a left action `galStalkAut a Ω` of `Ω ≃ₐ[R] Ω` on
the stalk functor `(Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber`.

When `a : Spec (.of R) ⟶ S` is a monomorphism (such as `𝟙 (Spec (.of R))` or
`S.fromSpecResidueField x`), `autOfAlgEquiv a Ω` is an isomorphism of groups
`galMulEquivAutOp a Ω : (Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ`, with explicit inverse
`autToAlgEquiv a Ω`. Specializing to `a = S.fromSpecResidueField x` and
`Ω = SeparableClosure (S.residueField x)` recovers the residue-field Galois action
`galoisStalkAction` and automorphism identification `ofPointAutMulEquiv`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.homOfAlgHom`, `isoOfAlgEquiv`,
  `autOfAlgEquiv`, `autToAlgEquiv`: conversion between `Ω ≃ₐ[R] Ω` and `Aut (ofOver a Ω)`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.galStalkAut`: the left action of `Ω ≃ₐ[R] Ω`
  on the stalk functor at `ofOver a Ω`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.galMulEquivAutOp`: group isomorphism
  `(Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ` when `a` is a monomorphism.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPointIsoOfAlgEquiv`,
  `ofPointAutToAlgEquiv`, `ofPointAutMulEquiv`, `galoisStalkAction`: residue-field
  specializations at `ofPoint x`.

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §§3–4.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

/-- Compatibility of `Spec σ` with `Spec (algebraMap R Ω)` for an `R`-algebra endomorphism `σ`. -/
theorem SpecMap_ofHom_comp_algebraMap {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω]
    (σ : Ω →ₐ[R] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom) (RingHom.ext fun r ↦ σ.commutes r)

section Galois

variable {S : Scheme.{u}} {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ S)
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- An `R`-algebra endomorphism `σ : Ω →ₐ[R] Ω` induces an endomorphism `Spec σ` of `ofOver a Ω`
in `GeometricPoint S`. -/
noncomputable def homOfAlgHom (σ : Ω →ₐ[R] Ω) : ofOver a Ω ⟶ ofOver a Ω :=
  homOfRingHom σ.toRingHom <| by
    rw [← Category.assoc, SpecMap_ofHom_comp_algebraMap]

/-- The underlying scheme morphism of `homOfAlgHom a Ω σ` is `Spec.map (CommRingCat.ofHom σ)`. -/
@[simp]
theorem homOfAlgHom_hom (σ : Ω →ₐ[R] Ω) :
    (homOfAlgHom a Ω σ).hom = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  homOfRingHom_hom _ _

/-- The underlying ring homomorphism of `homOfAlgHom a Ω σ` is `σ.toRingHom`. -/
@[simp]
theorem Hom.ringHom_homOfAlgHom (σ : Ω →ₐ[R] Ω) :
    (homOfAlgHom a Ω σ).ringHom = σ.toRingHom :=
  Hom.ringHom_homOfRingHom _ _

/-- The identity `R`-algebra endomorphism induces the identity of `ofOver a Ω`. -/
@[simp]
theorem homOfAlgHom_id : homOfAlgHom a Ω (AlgHom.id R Ω) = 𝟙 (ofOver a Ω) := by
  ext : 1
  simp [homOfAlgHom_hom]

/-- Since `Spec` reverses composition of ring homomorphisms (`Spec (σ ∘ τ) = Spec σ ≫ Spec τ`),
`homOfAlgHom` sends `σ.comp τ` to `homOfAlgHom a Ω σ ≫ homOfAlgHom a Ω τ`. -/
@[simp]
theorem homOfAlgHom_comp (σ τ : Ω →ₐ[R] Ω) :
    homOfAlgHom a Ω (σ.comp τ) = homOfAlgHom a Ω σ ≫ homOfAlgHom a Ω τ := by
  ext : 1
  rw [comp_hom, homOfAlgHom_hom, homOfAlgHom_hom, homOfAlgHom_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]

/-- An automorphism `σ : Ω ≃ₐ[R] Ω` induces an automorphism `Spec σ` of `ofOver a Ω` in
`GeometricPoint S`. -/
noncomputable def isoOfAlgEquiv (σ : Ω ≃ₐ[R] Ω) : ofOver a Ω ≅ ofOver a Ω :=
  isoOfRingEquiv σ.toRingEquiv <| by
    rw [← Category.assoc, AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom,
      ← AlgHom.toRingHom_eq_coe, SpecMap_ofHom_comp_algebraMap]

/-- The forward morphism of `isoOfAlgEquiv a Ω σ` is `homOfAlgHom a Ω σ`. -/
@[simp]
theorem isoOfAlgEquiv_hom (σ : Ω ≃ₐ[R] Ω) :
    (isoOfAlgEquiv a Ω σ).hom = homOfAlgHom a Ω σ.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_hom_hom, homOfAlgHom_hom, AlgEquiv.toRingEquiv_toRingHom,
    ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.toRingHom_eq_coe]

/-- The inverse morphism of `isoOfAlgEquiv a Ω σ` is `homOfAlgHom a Ω σ.symm`. -/
@[simp]
theorem isoOfAlgEquiv_inv (σ : Ω ≃ₐ[R] Ω) :
    (isoOfAlgEquiv a Ω σ).inv = homOfAlgHom a Ω σ.symm.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_inv_hom, homOfAlgHom_hom, ← AlgEquiv.symm_toRingEquiv,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.toRingHom_eq_coe]

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
    have hmul : (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom :=
      AlgHom.ext fun x ↦ AlgEquiv.mul_apply σ τ x
    rw [hmul])

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
  rw [← Iso.symm_hom, ← Aut.inv_asIso, ← map_inv, galStalkAut_asIso_hom, AlgEquiv.aut_inv]

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
  rw [map_mul, sheafFiber_aut_mul_app_apply]

/-- When `a` is a monomorphism, the ring endomorphism underlying an endomorphism of `ofOver a Ω`
fixes `R`. -/
theorem algebraMap_comp_ringHom [Mono a] (f : ofOver a Ω ⟶ ofOver a Ω) :
    f.ringHom.comp (algebraMap R Ω) = algebraMap R Ω := by
  apply Hom.ringHom_eq_of_SpecMap_eq
  rw [← cancel_mono a, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Hom.SpecMap_ringHom]
  exact f.w

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, an automorphism of `ofOver a Ω` in
`GeometricPoint S` yields an `R`-algebra automorphism of `Ω`. -/
noncomputable def autToAlgEquiv [Mono a] (φ : Aut (ofOver a Ω)) : Ω ≃ₐ[R] Ω :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.Spec.preimageIso ((forget S).mapIso φ.asIso)).unop.commRingCatIsoToRingEquiv)
    fun r ↦ by
      have h : ((Scheme.Spec.preimageIso
          ((forget S).mapIso φ.asIso)).unop.commRingCatIsoToRingEquiv : Ω →+* Ω) =
          φ.asIso.hom.ringHom := by
        apply Hom.ringHom_eq_of_SpecMap_eq
        rw [Hom.SpecMap_ringHom]
        exact Scheme.Spec.map_preimage ((forget S).mapIso φ.asIso).hom
      simpa [← RingEquiv.coe_toRingHom, h] using
        DFunLike.congr_fun (algebraMap_comp_ringHom a Ω φ.asIso.hom) r

/-- The ring homomorphism underlying `autToAlgEquiv a Ω φ` is `φ.asIso.hom.ringHom`. -/
@[simp]
theorem autToAlgEquiv_toRingHom [Mono a] (φ : Aut (ofOver a Ω)) :
    (autToAlgEquiv a Ω φ : Ω →+* Ω) = φ.asIso.hom.ringHom := by
  apply Hom.ringHom_eq_of_SpecMap_eq
  rw [Hom.SpecMap_ringHom]
  exact Scheme.Spec.map_preimage ((forget S).mapIso φ.asIso).hom

/-- Evaluating `autToAlgEquiv a Ω φ` at `r` applies `φ.asIso.hom.ringHom`. -/
@[simp]
theorem autToAlgEquiv_apply [Mono a] (φ : Aut (ofOver a Ω)) (r : Ω) :
    autToAlgEquiv a Ω φ r = φ.asIso.hom.ringHom r :=
  DFunLike.congr_fun (autToAlgEquiv_toRingHom a Ω φ) r

/-- The map `autOfAlgEquiv a Ω` from `Ω ≃ₐ[R] Ω` into `(Aut (ofOver a Ω))ᵐᵒᵖ` is always
injective. -/
theorem autOfAlgEquiv_injective : Function.Injective (autOfAlgEquiv a Ω) := by
  intro σ τ h
  have h' : (isoOfAlgEquiv a Ω σ).hom = (isoOfAlgEquiv a Ω τ).hom :=
    congrArg (fun e : (Aut (ofOver a Ω))ᵐᵒᵖ ↦ e.unop.asIso.hom) h
  have hring := congrArg Hom.ringHom h'
  simp only [isoOfAlgEquiv_hom, Hom.ringHom_homOfAlgHom] at hring
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun hring x

/-- **Automorphisms of a geometric point over a monomorphism.** When `a : Spec (.of R) ⟶ S` is a
monomorphism (for instance `𝟙 (Spec (.of R))` or `S.fromSpecResidueField x`), the automorphisms
of `ofOver a Ω` in `GeometricPoint S` are precisely the `Spec σ` for `σ : Ω ≃ₐ[R] Ω`. -/
noncomputable def galMulEquivAutOp [Mono a] :
    (Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ where
  toFun := autOfAlgEquiv a Ω
  invFun φ := autToAlgEquiv a Ω φ.unop
  left_inv σ := by
    ext r
    simp [autToAlgEquiv_apply]
  right_inv φ := by
    apply MulOpposite.unop_injective
    ext : 3
    simp only [unop_autOfAlgEquiv, isoOfAlgEquiv_hom, homOfAlgHom_hom,
      AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, autToAlgEquiv_toRingHom,
      Hom.SpecMap_ringHom]
  map_mul' := (autOfAlgEquiv a Ω).map_mul

/-- The forward direction of `galMulEquivAutOp` is `autOfAlgEquiv`. -/
@[simp]
theorem galMulEquivAutOp_apply [Mono a] (σ : Ω ≃ₐ[R] Ω) :
    galMulEquivAutOp a Ω σ = autOfAlgEquiv a Ω σ :=
  (rfl)

/-- The inverse direction of `galMulEquivAutOp` is `autToAlgEquiv`. -/
@[simp]
theorem galMulEquivAutOp_symm_apply [Mono a] (e : (Aut (ofOver a Ω))ᵐᵒᵖ) :
    (galMulEquivAutOp a Ω).symm e = autToAlgEquiv a Ω e.unop :=
  (rfl)

/-- The ring homomorphism underlying `(galMulEquivAutOp a Ω).symm e` is `e.unop.asIso.hom.ringHom`.
-/
theorem galMulEquivAutOp_symm_toRingHom [Mono a] (e : (Aut (ofOver a Ω))ᵐᵒᵖ) :
    ((galMulEquivAutOp a Ω).symm e : Ω →+* Ω) = e.unop.asIso.hom.ringHom :=
  autToAlgEquiv_toRingHom a Ω e.unop

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, every automorphism of `ofOver a Ω` in
`GeometricPoint S` comes from an `R`-algebra automorphism of `Ω`. -/
theorem autOfAlgEquiv_surjective [Mono a] : Function.Surjective (autOfAlgEquiv a Ω) :=
  (galMulEquivAutOp a Ω).surjective

end Galois

section ResidueFieldGalois

variable {S : Scheme.{u}}

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
  @isoOfAlgEquiv S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
    (SeparableClosure (S.residueField x)) inferInstance inferInstance inferInstance σ

@[simp]
lemma ofPointIsoOfAlgEquiv_hom_hom (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointIsoOfAlgEquiv x σ).hom.hom =
      Spec.map (CommRingCat.ofHom (σ : (ofPoint x).Ω →+* (ofPoint x).Ω)) := by
  rw [ofPointIsoOfAlgEquiv, @isoOfAlgEquiv_hom S (S.residueField x) Field.toCommRing
    (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
    inferInstance inferInstance inferInstance, homOfAlgHom_hom, AlgHom.toRingHom_eq_coe,
    AlgEquiv.toAlgHom_toRingHom]

@[simp]
lemma ofPointIsoOfAlgEquiv_inv_hom (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointIsoOfAlgEquiv x σ).inv.hom =
      Spec.map (CommRingCat.ofHom (σ.symm : (ofPoint x).Ω →+* (ofPoint x).Ω)) := by
  rw [ofPointIsoOfAlgEquiv, @isoOfAlgEquiv_inv S (S.residueField x) Field.toCommRing
    (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
    inferInstance inferInstance inferInstance, homOfAlgHom_hom, AlgHom.toRingHom_eq_coe,
    AlgEquiv.toAlgHom_toRingHom]

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
  @autToAlgEquiv S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
    (SeparableClosure (S.residueField x)) inferInstance inferInstance inferInstance inferInstance φ

lemma ofHom_ofPointAutToAlgEquiv (x : S) (φ : Aut (ofPoint x)) :
    CommRingCat.ofHom (ofPointAutToAlgEquiv x φ : (ofPoint x).Ω →+* (ofPoint x).Ω) =
      Spec.preimage φ.asIso.hom.hom := by
  rw [← Spec.map_inj, Spec.map_preimage, ofPointAutToAlgEquiv,
    @autToAlgEquiv_toRingHom S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
      (SeparableClosure (S.residueField x))
      inferInstance inferInstance inferInstance inferInstance φ,
    Hom.SpecMap_ringHom]

@[simp]
lemma ofPointAutToAlgEquiv_apply (x : S) (φ : Aut (ofPoint x)) (r : SeparableClosure _) :
    ofPointAutToAlgEquiv x φ r = (Spec.preimage φ.asIso.hom.hom).hom r :=
  DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (ofHom_ofPointAutToAlgEquiv x φ)) r

/-- **The automorphisms of `ofPoint x` are the Galois automorphisms.** Every automorphism of the
geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` is `Spec σ` for a unique `σ ∈ Gal(κ(x)ˢᵉᵖ/κ(x))`. Since
`Spec (σ * τ) = Spec σ ≫ Spec τ` and `Aut` multiplies in the order of function composition, this is
an isomorphism with the opposite group. -/
noncomputable def ofPointAutMulEquiv (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) ≃* (Aut (ofPoint x))ᵐᵒᵖ :=
  @galMulEquivAutOp S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
    (SeparableClosure (S.residueField x)) inferInstance inferInstance inferInstance inferInstance

@[simp]
lemma ofPointAutMulEquiv_apply (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointAutMulEquiv x σ).unop.asIso = ofPointIsoOfAlgEquiv x σ := by
  rw [ofPointAutMulEquiv, @galMulEquivAutOp_apply S (S.residueField x) Field.toCommRing
    (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
    inferInstance inferInstance inferInstance inferInstance,
    @unop_autOfAlgEquiv S (S.residueField x) Field.toCommRing
      (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
      inferInstance inferInstance inferInstance,
    ofPointIsoOfAlgEquiv]

@[simp]
lemma ofPointAutMulEquiv_symm_apply (x : S) (φ : (Aut (ofPoint x))ᵐᵒᵖ) :
    (ofPointAutMulEquiv x).symm φ = ofPointAutToAlgEquiv x φ.unop := by
  rw [ofPointAutMulEquiv, @galMulEquivAutOp_symm_apply S (S.residueField x) Field.toCommRing
    (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
    inferInstance inferInstance inferInstance inferInstance,
    ofPointAutToAlgEquiv]

/-- **The Galois action on stalks at `ofPoint x`.** An element `σ` of `Gal(κ(x)ˢᵉᵖ/κ(x))` acts on
the stalks at `ofPoint x`, naturally in the sheaf, through the stalk map of `Spec σ`. Since `Spec`
reverses composition this is a left action. -/
noncomputable def galoisStalkAction (A : Type u') [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) →*
      Aut (((toPointFunctor S).obj (ofPoint x)).sheafFiber (A := A)) :=
  @galStalkAut S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
    (SeparableClosure (S.residueField x)) inferInstance inferInstance inferInstance A _ _

@[simp]
lemma galoisStalkAction_apply (A : Type u') [Category.{w} A] [HasColimitsOfSize.{u, u} A] (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (galoisStalkAction A x σ).asIso.hom =
      ((toPointFunctor S).map (ofPointIsoOfAlgEquiv x σ).hom).sheafFiber :=
  (@galStalkAut_asIso_hom S (S.residueField x) Field.toCommRing
    (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
    inferInstance inferInstance inferInstance A _ _ σ).trans
    (congrArg (fun φ ↦ ((toPointFunctor S).map φ).sheafFiber)
      (@isoOfAlgEquiv_hom S (S.residueField x) Field.toCommRing
        (S.fromSpecResidueField x) (SeparableClosure (S.residueField x))
        inferInstance inferInstance inferInstance σ).symm)

end ResidueFieldGalois

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
