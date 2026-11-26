/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Basic
import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.CategoryTheory.Aut.Basic

/-!
# Galois actions on étale stalks at geometric points

For a geometric point `ofOver a Ω` factoring through `a : Spec (.of R) ⟶ S`, every `R`-algebra
homomorphism `σ : Ω₂ →ₐ[R] Ω₁` induces a morphism `homOfAlgHom a σ : ofOver a Ω₁ ⟶ ofOver a Ω₂`
in `GeometricPoint S`, and every `R`-algebra isomorphism `σ : Ω₂ ≃ₐ[R] Ω₁` induces an isomorphism
`isoOfAlgEquiv a σ : ofOver a Ω₁ ≅ ofOver a Ω₂`. On a single `Ω`, `autOfAlgEquiv a Ω` gives a
left action `ofOverGaloisStalkAction a Ω` of `Ω ≃ₐ[R] Ω` on the stalk functor
`(Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber`.

When `a : Spec (.of R) ⟶ S` is a monomorphism (such as `𝟙 (Spec (.of R))` or
`S.fromSpecResidueField x`), `autOfAlgEquiv a Ω` is an isomorphism of groups
`ofOverAutMulEquiv a Ω : (Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ`, with explicit inverse
`autToAlgEquiv a Ω`. Specializing to `a = S.fromSpecResidueField x` and
`Ω = SeparableClosure (S.residueField x)` recovers the residue-field Galois action
`galoisStalkAction` and automorphism identification `ofPointAutMulEquiv`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.homOfAlgHom`, `isoOfAlgEquiv`,
  `autOfAlgEquiv`, `autToAlgEquiv`: conversion between `R`-algebra maps / automorphisms and
  morphisms / automorphisms in `GeometricPoint S`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofOverGaloisStalkAction`: the left action of
  `Ω ≃ₐ[R] Ω` on the stalk functor at `ofOver a Ω`.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofOverAutMulEquiv`: group isomorphism
  `(Ω ≃ₐ[R] Ω) ≃* (Aut (ofOver a Ω))ᵐᵒᵖ` when `a` is a monomorphism.
* `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofPointAutMulEquiv`,
  `galoisStalkAction`: residue-field specializations at `ofPoint x`.

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §§3–4.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section Galois

variable {S : Scheme.{u}} {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ S)

section Maps

variable {Ω₁ Ω₂ Ω₃ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Algebra R Ω₁]
  [Field Ω₂] [IsSepClosed Ω₂] [Algebra R Ω₂] [Field Ω₃] [IsSepClosed Ω₃] [Algebra R Ω₃]

/-- An `R`-algebra homomorphism `σ : Ω₂ →ₐ[R] Ω₁` induces a morphism `Spec σ` from
`ofOver a Ω₁` to `ofOver a Ω₂` in `GeometricPoint S`. -/
noncomputable def homOfAlgHom (σ : Ω₂ →ₐ[R] Ω₁) : ofOver a Ω₁ ⟶ ofOver a Ω₂ :=
  homOfRingHom σ.toRingHom <| by
    rw [AlgHom.toRingHom_eq_coe, Spec.map_algHom_comp_map_algebraMap_assoc]

/-- The underlying scheme morphism of `homOfAlgHom a σ` is `Spec.map (CommRingCat.ofHom σ)`. -/
@[simp]
theorem homOfAlgHom_hom (σ : Ω₂ →ₐ[R] Ω₁) :
    (homOfAlgHom a σ).hom = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  homOfRingHom_hom _ _

/-- The underlying ring homomorphism of `homOfAlgHom a σ` is `σ.toRingHom`. -/
@[simp]
theorem Hom.ringHom_homOfAlgHom (σ : Ω₂ →ₐ[R] Ω₁) :
    (homOfAlgHom a σ).ringHom = σ.toRingHom :=
  Hom.ringHom_homOfRingHom _ _

/-- The identity `R`-algebra endomorphism induces the identity of `ofOver a Ω`. -/
@[simp]
theorem homOfAlgHom_id (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] :
    homOfAlgHom a (AlgHom.id R Ω) = 𝟙 (ofOver a Ω) := by
  ext : 1
  simp [homOfAlgHom_hom]

/-- Since `Spec` reverses composition of ring homomorphisms (`Spec (σ ∘ τ) = Spec σ ≫ Spec τ`),
`homOfAlgHom` sends `σ.comp τ` to `homOfAlgHom a σ ≫ homOfAlgHom a τ`. -/
@[simp]
theorem homOfAlgHom_comp (σ : Ω₂ →ₐ[R] Ω₁) (τ : Ω₃ →ₐ[R] Ω₂) :
    homOfAlgHom a (σ.comp τ) = homOfAlgHom a σ ≫ homOfAlgHom a τ := by
  ext : 1
  rw [comp_hom, homOfAlgHom_hom, homOfAlgHom_hom, homOfAlgHom_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]

/-- An `R`-algebra isomorphism `σ : Ω₂ ≃ₐ[R] Ω₁` induces an isomorphism `Spec σ` from
`ofOver a Ω₁` to `ofOver a Ω₂` in `GeometricPoint S`. -/
noncomputable def isoOfAlgEquiv (σ : Ω₂ ≃ₐ[R] Ω₁) : ofOver a Ω₁ ≅ ofOver a Ω₂ :=
  isoOfRingEquiv σ.toRingEquiv <| by
    rw [← Category.assoc, AlgEquiv.toRingEquiv_toRingHom,
      Spec.map_algHom_comp_map_algebraMap]

/-- The forward morphism of `isoOfAlgEquiv a σ` is `homOfAlgHom a σ`. -/
@[simp]
theorem isoOfAlgEquiv_hom (σ : Ω₂ ≃ₐ[R] Ω₁) :
    (isoOfAlgEquiv a σ).hom = homOfAlgHom a σ.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_hom_hom, homOfAlgHom_hom, AlgEquiv.toRingEquiv_toRingHom,
    ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.toRingHom_eq_coe]

/-- The inverse morphism of `isoOfAlgEquiv a σ` is `homOfAlgHom a σ.symm`. -/
@[simp]
theorem isoOfAlgEquiv_inv (σ : Ω₂ ≃ₐ[R] Ω₁) :
    (isoOfAlgEquiv a σ).inv = homOfAlgHom a σ.symm.toAlgHom := by
  ext : 1
  rw [isoOfAlgEquiv, isoOfRingEquiv_inv_hom, homOfAlgHom_hom, ← AlgEquiv.symm_toRingEquiv,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.toRingHom_eq_coe]

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, `Spec g : Spec Ω₁ ⟶ Spec Ω₂` is a morphism
`ofOver a Ω₁ ⟶ ofOver a Ω₂` in `GeometricPoint S` if and only if `g` is `R`-linear. -/
theorem SpecMap_comp_ofOver_iff [Mono a] (g : Ω₂ →+* Ω₁) :
    Spec.map (CommRingCat.ofHom g) ≫ (ofOver a Ω₂).hom = (ofOver a Ω₁).hom ↔
      g.comp (algebraMap R Ω₂) = algebraMap R Ω₁ := by
  dsimp only
  rw [← Category.assoc, cancel_mono a, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact ⟨fun h ↦ TauCeti.AlgebraicGeometry.ringHom_eq_of_SpecMap_eq h,
    fun h ↦ congrArg (Spec.map ∘ CommRingCat.ofHom) h⟩

/-- When `a` is a monomorphism, the ring homomorphism underlying a morphism
`ofOver a Ω₁ ⟶ ofOver a Ω₂` is `R`-linear. -/
theorem Hom.ringHom_comp_algebraMap [Mono a] (f : ofOver a Ω₁ ⟶ ofOver a Ω₂) :
    f.ringHom.comp (algebraMap R Ω₂) = algebraMap R Ω₁ :=
  (SpecMap_comp_ofOver_iff a f.ringHom).mp f.SpecMap_ringHom_comp

end Maps

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

/-- The group homomorphism `(Ω ≃ₐ[R] Ω) →* (Aut (ofOver a Ω))ᵐᵒᵖ` sending `σ` to `Spec σ`.
Because `Spec (σ * τ) = Spec σ ≫ Spec τ` while multiplication in `Aut` composes right-to-left,
this lands in the opposite group `(Aut (ofOver a Ω))ᵐᵒᵖ`. -/
noncomputable def autOfAlgEquiv : (Ω ≃ₐ[R] Ω) →* (Aut (ofOver a Ω))ᵐᵒᵖ where
  toFun σ := MulOpposite.op (Aut.of (isoOfAlgEquiv a σ))
  map_one' := MulOpposite.unop_injective (by
    ext : 2
    simp only [MulOpposite.unop_op, MulOpposite.unop_one, Aut.one_asIso, Iso.refl_hom]
    exact (isoOfAlgEquiv_hom a 1).trans (homOfAlgHom_id a Ω))
  map_mul' σ τ := MulOpposite.unop_injective (by
    ext : 2
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Aut.mul_asIso, Iso.trans_hom,
      isoOfAlgEquiv_hom, ← homOfAlgHom_comp]
    have hmul : (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom :=
      AlgHom.ext fun x ↦ AlgEquiv.mul_apply σ τ x
    rw [hmul])

/-- Unwrapping `autOfAlgEquiv a Ω σ` gives `isoOfAlgEquiv a σ`. -/
@[simp]
theorem unop_autOfAlgEquiv (σ : Ω ≃ₐ[R] Ω) :
    (autOfAlgEquiv a Ω σ).unop.asIso = isoOfAlgEquiv a σ :=
  (rfl)

/-- **The Galois action on stalks.** For a geometric point `ofOver a Ω` factoring through
`a : Spec (.of R) ⟶ S`, every `σ : Ω ≃ₐ[R] Ω` acts naturally on the stalk functor by the stalk
map of `Spec σ`. This is a group homomorphism into `Aut (pointSmallEtale _).sheafFiber`, so on
concrete stalks it defines a left action of `Ω ≃ₐ[R] Ω`. -/
noncomputable def ofOverGaloisStalkAction {A : Type u'} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] :
    (Ω ≃ₐ[R] Ω) →* Aut ((Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber (A := A)) :=
  (stalkAction A (ofOver a Ω)).comp (autOfAlgEquiv a Ω)

/-- The natural transformation attached to `σ : Ω ≃ₐ[R] Ω` by `ofOverGaloisStalkAction` is
`((toPointFunctor S).map (homOfAlgHom a σ)).sheafFiber`. -/
@[simp]
theorem ofOverGaloisStalkAction_asIso_hom {A : Type u'} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] (σ : Ω ≃ₐ[R] Ω) :
    (ofOverGaloisStalkAction a Ω (A := A) σ).asIso.hom =
      ((toPointFunctor S).map (homOfAlgHom a σ.toAlgHom)).sheafFiber :=
  (stalkAction_apply A (ofOver a Ω) (autOfAlgEquiv a Ω σ)).trans (by
    simp only [unop_autOfAlgEquiv, isoOfAlgEquiv_hom])

/-- The inverse natural transformation attached to `σ : Ω ≃ₐ[R] Ω` by `ofOverGaloisStalkAction`
is `((toPointFunctor S).map (homOfAlgHom a σ.symm)).sheafFiber`. -/
@[simp]
theorem ofOverGaloisStalkAction_asIso_inv {A : Type u'} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] (σ : Ω ≃ₐ[R] Ω) :
    (ofOverGaloisStalkAction a Ω (A := A) σ).asIso.inv =
      ((toPointFunctor S).map (homOfAlgHom a σ.symm.toAlgHom)).sheafFiber := by
  rw [← Iso.symm_hom, ← Aut.inv_asIso, ← map_inv, ofOverGaloisStalkAction_asIso_hom,
    AlgEquiv.aut_inv]

/-- On stalks of sheaves of sets, `ofOverGaloisStalkAction` is a left action of `Ω ≃ₐ[R] Ω`:
`(σ * τ) • z = σ • (τ • z)`. -/
theorem ofOverGaloisStalkAction_mul_app_apply (σ τ : Ω ≃ₐ[R] Ω)
    (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (z : (Scheme.pointSmallEtale (ofOver a Ω).hom).sheafFiber.obj F) :
    (ofOverGaloisStalkAction a Ω (σ * τ)).asIso.hom.app F z =
      (ofOverGaloisStalkAction a Ω σ).asIso.hom.app F
        ((ofOverGaloisStalkAction a Ω τ).asIso.hom.app F z) := by
  rw [map_mul, Aut.functor_mul_asIso_hom_app_apply]

private theorem autToRingEquiv_toRingHom (φ : Aut (ofOver a Ω)) :
    ((Scheme.Spec.preimageIso
        ((forget S).mapIso φ.asIso)).unop.commRingCatIsoToRingEquiv : Ω →+* Ω) =
      φ.asIso.hom.ringHom := by
  apply TauCeti.AlgebraicGeometry.ringHom_eq_of_SpecMap_eq
  rw [Hom.SpecMap_ringHom]
  exact Scheme.Spec.map_preimage ((forget S).mapIso φ.asIso).hom

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, an automorphism of `ofOver a Ω` in
`GeometricPoint S` yields an `R`-algebra automorphism of `Ω`. -/
noncomputable def autToAlgEquiv [Mono a] (φ : Aut (ofOver a Ω)) : Ω ≃ₐ[R] Ω :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.Spec.preimageIso ((forget S).mapIso φ.asIso)).unop.commRingCatIsoToRingEquiv)
    fun r ↦ by
      rw [← RingEquiv.coe_toRingHom, autToRingEquiv_toRingHom]
      exact DFunLike.congr_fun (φ.asIso.hom.ringHom_comp_algebraMap a) r

/-- The ring homomorphism underlying `autToAlgEquiv a Ω φ` is `φ.asIso.hom.ringHom`. -/
@[simp]
theorem autToAlgEquiv_toRingHom [Mono a] (φ : Aut (ofOver a Ω)) :
    (autToAlgEquiv a Ω φ : Ω →+* Ω) = φ.asIso.hom.ringHom :=
  autToRingEquiv_toRingHom a Ω φ

/-- Evaluating `autToAlgEquiv a Ω φ` at `r` applies `φ.asIso.hom.ringHom`. -/
@[simp]
theorem autToAlgEquiv_apply [Mono a] (φ : Aut (ofOver a Ω)) (r : Ω) :
    autToAlgEquiv a Ω φ r = φ.asIso.hom.ringHom r :=
  DFunLike.congr_fun (autToAlgEquiv_toRingHom a Ω φ) r

/-- The map `autOfAlgEquiv a Ω` from `Ω ≃ₐ[R] Ω` into `(Aut (ofOver a Ω))ᵐᵒᵖ` is always
injective. -/
theorem autOfAlgEquiv_injective : Function.Injective (autOfAlgEquiv a Ω) := by
  intro σ τ h
  have h' : (isoOfAlgEquiv a (Ω₁ := Ω) (Ω₂ := Ω) σ).hom =
      (isoOfAlgEquiv a (Ω₁ := Ω) (Ω₂ := Ω) τ).hom :=
    congrArg (fun e : (Aut (ofOver a Ω))ᵐᵒᵖ ↦ e.unop.asIso.hom) h
  have hring := congrArg Hom.ringHom h'
  simp only [isoOfAlgEquiv_hom, Hom.ringHom_homOfAlgHom] at hring
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun hring x

/-- **Automorphisms of a geometric point over a monomorphism.** When `a : Spec (.of R) ⟶ S` is a
monomorphism (for instance `𝟙 (Spec (.of R))` or `S.fromSpecResidueField x`), the automorphisms
of `ofOver a Ω` in `GeometricPoint S` are precisely the `Spec σ` for `σ : Ω ≃ₐ[R] Ω`. -/
noncomputable def ofOverAutMulEquiv [Mono a] :
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

/-- The forward direction of `ofOverAutMulEquiv` is `autOfAlgEquiv`. -/
@[simp]
theorem ofOverAutMulEquiv_apply [Mono a] (σ : Ω ≃ₐ[R] Ω) :
    ofOverAutMulEquiv a Ω σ = autOfAlgEquiv a Ω σ :=
  (rfl)

/-- The inverse direction of `ofOverAutMulEquiv` is `autToAlgEquiv`. -/
@[simp]
theorem ofOverAutMulEquiv_symm_apply [Mono a] (e : (Aut (ofOver a Ω))ᵐᵒᵖ) :
    (ofOverAutMulEquiv a Ω).symm e = autToAlgEquiv a Ω e.unop :=
  (rfl)

/-- The ring homomorphism underlying `(ofOverAutMulEquiv a Ω).symm e` is `e.unop.asIso.hom.ringHom`.
-/
theorem ofOverAutMulEquiv_symm_toRingHom [Mono a] (e : (Aut (ofOver a Ω))ᵐᵒᵖ) :
    ((ofOverAutMulEquiv a Ω).symm e : Ω →+* Ω) = e.unop.asIso.hom.ringHom :=
  autToAlgEquiv_toRingHom a Ω e.unop

/-- When `a : Spec (.of R) ⟶ S` is a monomorphism, every automorphism of `ofOver a Ω` in
`GeometricPoint S` comes from an `R`-algebra automorphism of `Ω`. -/
theorem autOfAlgEquiv_surjective [Mono a] : Function.Surjective (autOfAlgEquiv a Ω) :=
  (ofOverAutMulEquiv a Ω).surjective

end Galois

section ResidueFieldGalois

variable {S : Scheme.{u}}

/-- **The automorphisms of `ofPoint x` are the Galois automorphisms.** Every automorphism of the
geometric point `Spec κ(x)ˢᵉᵖ ⟶ S` is `Spec σ` for a unique `σ ∈ Gal(κ(x)ˢᵉᵖ/κ(x))`. Since
`Spec (σ * τ) = Spec σ ≫ Spec τ` and `Aut` multiplies in the order of function composition, this is
an isomorphism with the opposite group. -/
noncomputable def ofPointAutMulEquiv (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) ≃* (Aut (ofPoint x))ᵐᵒᵖ :=
  -- `S.residueField x` is a `CommRingCat`, so unifying `a` directly with `S.fromSpecResidueField x`
  -- assigns `[CommRing R] := (S.residueField x).str` before typeclass synthesis runs, breaking
  -- `Algebra _ (SeparableClosure _)`. Binding `a` under `letI` locks in `Field.toCommRing`.
  letI : CommRing (S.residueField x) := Field.toCommRing
  let a : Spec (.of (S.residueField x)) ⟶ S := S.fromSpecResidueField x
  ofOverAutMulEquiv a (SeparableClosure (S.residueField x))

@[simp]
lemma ofPointAutMulEquiv_apply (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (ofPointAutMulEquiv x σ).unop.asIso =
      -- Pass `Field.toCommRing` explicitly so `[CommRing R]` matches `SeparableClosure.instAlgebra`
      -- (binding an auxiliary `let a` here would pollute the `@[simp]` right-hand side).
      @isoOfAlgEquiv S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
        (SeparableClosure (S.residueField x)) (SeparableClosure (S.residueField x))
        _ _ _ _ _ _ σ := by
  let _ : CommRing (S.residueField x) := Field.toCommRing
  rw [ofPointAutMulEquiv, ofOverAutMulEquiv_apply, unop_autOfAlgEquiv]

@[simp]
lemma ofPointAutMulEquiv_symm_apply (x : S) (φ : (Aut (ofPoint x))ᵐᵒᵖ) :
    (ofPointAutMulEquiv x).symm φ =
      -- Pass `Field.toCommRing` explicitly for the same `CommRingCat.commRing` mismatch.
      @autToAlgEquiv S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
        (SeparableClosure (S.residueField x)) _ _ _ _ φ.unop := by
  let _ : CommRing (S.residueField x) := Field.toCommRing
  rw [ofPointAutMulEquiv, ofOverAutMulEquiv_symm_apply]

/-- **The Galois action on stalks at `ofPoint x`.** An element `σ` of `Gal(κ(x)ˢᵉᵖ/κ(x))` acts on
the stalks at `ofPoint x`, naturally in the sheaf, through the stalk map of `Spec σ`. Since `Spec`
reverses composition this is a left action. -/
noncomputable def galoisStalkAction (A : Type u') [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (x : S) :
    (SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) →*
      Aut (((toPointFunctor S).obj (ofPoint x)).sheafFiber (A := A)) :=
  -- Binding `a` under `letI : CommRing (S.residueField x) := Field.toCommRing` resolves the
  -- `CommRingCat.commRing` vs `Field.toCommRing` diamond for `Algebra _ (SeparableClosure _)`.
  letI : CommRing (S.residueField x) := Field.toCommRing
  let a : Spec (.of (S.residueField x)) ⟶ S := S.fromSpecResidueField x
  ofOverGaloisStalkAction a (SeparableClosure (S.residueField x))

@[simp]
lemma galoisStalkAction_apply (A : Type u') [Category.{w} A] [HasColimitsOfSize.{u, u} A] (x : S)
    (σ : SeparableClosure (S.residueField x) ≃ₐ[S.residueField x]
      SeparableClosure (S.residueField x)) :
    (galoisStalkAction A x σ).asIso.hom =
      ((toPointFunctor S).map
        -- Pass `Field.toCommRing` explicitly to match `SeparableClosure.instAlgebra` in `@[simp]`.
        (@homOfAlgHom S (S.residueField x) Field.toCommRing (S.fromSpecResidueField x)
          (SeparableClosure (S.residueField x)) (SeparableClosure (S.residueField x))
          _ _ _ _ _ _ σ.toAlgHom)).sheafFiber :=
  letI : CommRing (S.residueField x) := Field.toCommRing
  let a : Spec (.of (S.residueField x)) ⟶ S := S.fromSpecResidueField x
  ofOverGaloisStalkAction_asIso_hom a (SeparableClosure (S.residueField x)) σ

end ResidueFieldGalois

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
