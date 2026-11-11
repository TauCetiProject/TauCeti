/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import TauCeti.RingTheory.Henselization.IndEtale
public import TauCeti.RingTheory.Henselization.Local

/-!
# Henselizations of the local rings of a scheme

The henselization `𝒪ʰ_{X,x}` of the local ring of a scheme `X` at a point `x` is the
henselization of `𝒪_{X,x}` along its maximal ideal. It comes with a local homomorphism
`𝒪_{X,x} → 𝒪ʰ_{X,x}` and hence a morphism `Spec 𝒪ʰ_{X,x} ⟶ X`, and it is ind-étale over the
sections of every affine open containing `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.henselization X x`: the henselization `𝒪ʰ_{X,x}` of the local ring
  of `X` at `x`, along its maximal ideal.
* `AlgebraicGeometry.Scheme.toHenselization X x`: the structure map `𝒪_{X,x} → 𝒪ʰ_{X,x}`.
* `AlgebraicGeometry.Scheme.fromSpecHenselization X x`: the canonical morphism
  `Spec 𝒪ʰ_{X,x} ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.indEtale_henselization`: `𝒪ʰ_{X,x}` is ind-étale over the sections
  of every affine open containing `x`.
* `AlgebraicGeometry.Scheme.fromSpecHenselization_closedPoint`: `Spec 𝒪ʰ_{X,x} ⟶ X` sends the
  closed point to `x`.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The henselization `𝒪ʰ_{X,x}` of the local ring `𝒪_{X,x}` of a scheme at a point, along its
maximal ideal. -/
noncomputable abbrev henselization (X : Scheme.{u}) (x : X) : CommRingCat.{u} :=
  .of (TauCeti.Henselization.algebra (maximalIdeal (X.presheaf.stalk x)))

/-- The structure map `𝒪_{X,x} → 𝒪ʰ_{X,x}`. -/
noncomputable abbrev toHenselization (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ⟶ henselization X x :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (TauCeti.Henselization.algebra (maximalIdeal (X.presheaf.stalk x))))

/-- The structure map `𝒪_{X,x} → 𝒪ʰ_{X,x}` is a local homomorphism. -/
instance (X : Scheme.{u}) (x : X) : IsLocalHom (toHenselization X x).hom :=
  TauCeti.Henselization.isLocalHom_algebraMap _

/-- The sections of `X` over an open `W` act on the henselization at a point of `W` through the
local ring at that point. -/
noncomputable instance (W : X.Opens) (x : W) : Algebra Γ(X, W) (henselization X x) :=
  (X.presheaf.germ W x x.2 ≫ toHenselization X x).hom.toAlgebra

/-- The action of `Γ(X, W)` on `𝒪ʰ_{X,x}` factors through the local ring `𝒪_{X,x}`. -/
instance (W : X.Opens) (x : W) :
    IsScalarTower Γ(X, W) (X.presheaf.stalk x) (henselization X x) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The henselization `𝒪ʰ_{X,x}` is ind-étale over the ring of sections of every affine open
containing `x`: it is the henselization of a localization of that ring. -/
theorem indEtale_henselization {W : X.Opens} (hW : IsAffineOpen W) (x : W) :
    TauCeti.Algebra.IndEtale Γ(X, W) (henselization X x) :=
  have := hW.isLocalization_stalk x
  have : TauCeti.Algebra.IndEtale Γ(X, W) (X.presheaf.stalk x) :=
    .of_isLocalization (hW.primeIdealOf x).asIdeal.primeCompl
  have : TauCeti.Algebra.IndEtale (X.presheaf.stalk x) (henselization X x) :=
    TauCeti.Henselization.indEtale _
  .comp (S := X.presheaf.stalk x) _

/-- The canonical morphism `Spec 𝒪ʰ_{X,x} ⟶ X`, through `Spec 𝒪_{X,x}`. -/
noncomputable def fromSpecHenselization (X : Scheme.{u}) (x : X) :
    Spec (henselization X x) ⟶ X :=
  Spec.map (toHenselization X x) ≫ X.fromSpecStalk x

/-- The canonical morphism `Spec 𝒪ʰ_{X,x} ⟶ X` is `Spec 𝒪ʰ_{X,x} ⟶ Spec 𝒪_{X,x} ⟶ X`. -/
theorem fromSpecHenselization_def (X : Scheme.{u}) (x : X) :
    fromSpecHenselization X x = Spec.map (toHenselization X x) ≫ X.fromSpecStalk x :=
  (rfl)

/-- The canonical morphism `Spec 𝒪ʰ_{X,x} ⟶ X` sends the closed point to `x`. -/
@[simp]
theorem fromSpecHenselization_closedPoint (X : Scheme.{u}) (x : X) :
    fromSpecHenselization X x (closedPoint (henselization X x)) = x := by
  rw [fromSpecHenselization_def]
  exact (congrArg (X.fromSpecStalk x) Spec_closedPoint).trans fromSpecStalk_closedPoint

end AlgebraicGeometry.Scheme
