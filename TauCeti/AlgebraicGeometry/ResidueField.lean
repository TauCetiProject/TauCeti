/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Residue fields of schemes: invertible natural numbers, geometric points, and spectra

This file records how the condition `(N : κ(x)) ≠ 0`, that a natural number `N` is invertible in
the residue field at a point `x`, carries over between schemes. It is the form in which "`N` is
invertible on the base" enters the theory of level structures on elliptic curves.

It also provides the geometric point `Spec κ(x)ᵃˡᵍ ⟶ X` over a point `x`, through which such
conditions are checked after base change to an algebraically closed field.

## Main definitions

* `AlgebraicGeometry.Scheme.fromSpecAlgebraicClosure X x`: the morphism `Spec κ(x)ᵃˡᵍ ⟶ X` from
  the spectrum of an algebraic closure of the residue field at `x`, whose image is `{x}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.natCast_residueField_ne_zero`: if `N` is invertible in the residue
  field at `f x`, then it is invertible in the residue field at `x`, for any morphism `f`.
* `AlgebraicGeometry.Spec.natCast_residueField_ne_zero`: if `N` is invertible in a field `K`, then
  it is invertible in the residue field of `Spec K`.
* `RingHom.isIso_SpecMap_residueFieldMap_iff`: for a ring map `φ : R →+* S` and a prime
  `x` of `S`, the residue field map of `Spec S ⟶ Spec R` at `x` is an isomorphism iff the map of
  residue fields `κ(φ⁻¹ x) → κ(x)` is bijective. This translates conditions on residue fields
  between schemes and rings, for instance for étale neighbourhoods built from algebras.
* `AlgebraicGeometry.Scheme.residueField_hom_ext`: on a quasi-affine scheme, a ring map out of the
  residue field `κ(x)` is determined by its values on global functions evaluated at `x`.
* `AlgebraicGeometry.Scheme.toSpecΓ_apply_asIdeal`: the point of `Spec Γ(X, ⊤)` under `x` is the
  prime ideal of global functions vanishing at `x`.

The residue field map `f.residueFieldMap x` has source `κ(f x)`. When `f x` is known to equal a
point `y` only propositionally, for instance when `f` is an automorphism fixing `x`, it is
composed with `Scheme.residueFieldCongr` to give a map `κ(y) ⟶ κ(x)`. The lemmas
`Scheme.Hom.residueFieldCongr_inv_residueFieldMap_comp` and its companions compute such composites
without the casts that a direct rewrite of `f x` to `y` would produce.

The proofs of the first two results only use that a ring homomorphism between fields, such as
Mathlib's `Scheme.Hom.residueFieldMap`, preserves natural number casts and is injective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If `N` is invertible in the residue field at `f x`, it is invertible in the residue field
at `x`. -/
theorem Scheme.Hom.natCast_residueField_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {N : ℕ}
    (hN : (N : Y.residueField (f x)) ≠ 0) : (N : X.residueField x) ≠ 0 := by
  rw [← map_natCast (f.residueFieldMap x).hom]
  exact (map_ne_zero _).mpr hN

/-- If `N` is invertible in a field `K`, it is invertible in the residue field of `Spec K`. -/
theorem Spec.natCast_residueField_ne_zero {K : Type u} [Field K] {N : ℕ} (hN : (N : K) ≠ 0)
    (s : Spec (.of K)) : (N : (Spec (.of K)).residueField s) ≠ 0 := by
  rw [← map_natCast ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec (.of K)).presheaf.germ ⊤ s trivial ≫ (Spec (.of K)).residue s).hom]
  exact (map_ne_zero _).mpr hN

section residueFieldCongr

variable {X Y Z : Scheme.{u}}

/-- The residue field map of a composite, with sources identified along `f x = y` and `g y = z`,
is the composite of the residue field maps. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) {x : X}
    {y : Y} {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (Z.residueFieldCongr hfg).inv ≫ (f ≫ g).residueFieldMap x =
      ((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y) ≫
        (Y.residueFieldCongr hf).inv ≫ f.residueFieldMap x := by
  subst hf hg
  simp

/-- Equal morphisms have equal residue field maps, with sources identified along `f x = y`. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_congr {f f' : X ⟶ Y} (e : f = f')
    {x : X} {y : Y} (h : f x = y) (h' : f' x = y) :
    (Y.residueFieldCongr h).inv ≫ f.residueFieldMap x =
      (Y.residueFieldCongr h').inv ≫ f'.residueFieldMap x := by
  subst e
  rfl

/-- The residue field map of the identity, with source identified along `x = x'`, is the
identification `κ(x') ≅ κ(x)`. -/
theorem Scheme.residueFieldCongr_inv_residueFieldMap_id {x x' : X} (h : (𝟙 X : X ⟶ X) x = x') :
    (X.residueFieldCongr h).inv ≫ (𝟙 X : X ⟶ X).residueFieldMap x =
      (X.residueFieldCongr (h.symm : x' = x)).hom := by
  subst h
  simp

/-- The residue field map at `x`, with source identified along `f x = y`, sends the value at `y`
of a global function `a` to the value at `x` of its pullback `f^*(a)`. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_Γevaluation (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (a : Γ(Y, ⊤)) :
    ((Y.residueFieldCongr h).inv ≫ f.residueFieldMap x) (Y.Γevaluation y a) =
      X.Γevaluation x (f.appTop a) := by
  subst h
  simp [Scheme.Γevaluation_naturality_apply]

end residueFieldCongr

/-- The point of `Spec Γ(X, ⊤)` under `x` is the prime ideal of global functions vanishing at
`x`. -/
theorem Scheme.toSpecΓ_apply_asIdeal (X : Scheme.{u}) (x : X) :
    (X.toSpecΓ x).asIdeal = RingHom.ker (X.Γevaluation x).hom := by
  ext a
  -- By `Scheme.toSpecΓ_apply`, the point is the preimage of the maximal ideal of the stalk under
  -- the germ map, and `Γevaluation` is the germ map followed by the residue map.
  exact (IsLocalRing.residue_eq_zero_iff (X.presheaf.Γgerm x a)).symm

/-- A ring map out of a residue field of `Spec R` is determined by its values on the elements
of `R`. -/
theorem Spec.residueField_hom_ext {R : CommRingCat.{u}} {p : Spec R} {K : CommRingCat.{u}}
    {α β : (Spec R).residueField p ⟶ K}
    (h : (Spec R).Γevaluation p ≫ α = (Spec R).Γevaluation p ≫ β) : α = β := by
  rw [← cancel_epi (Scheme.Spec.residueFieldIso R p).inv]
  -- The residue field is `p.asIdeal.ResidueField`, whose ring maps are determined on `R`.
  have h' := congr((Scheme.ΓSpecIso R).inv ≫ $h)
  ext1
  refine @Ideal.ResidueField.ringHom_ext _ _ _ _ _ p.isPrime _ _ ?_
  ext a
  have e : (Scheme.Spec.residueFieldIso R p).inv (algebraMap R _ a) =
      (Spec R).Γevaluation p ((Scheme.ΓSpecIso R).inv a) :=
    congr($(Scheme.Spec.algebraMap_residueFieldIso_inv R p).hom a)
  simpa [e] using congr($(h').hom a)

/-- On a quasi-affine scheme, a ring map out of the residue field `κ(x)` is determined by its
values on global functions evaluated at `x`. -/
theorem Scheme.residueField_hom_ext {X : Scheme.{u}} [X.IsQuasiAffine] {x : X}
    {K : CommRingCat.{u}} {α β : X.residueField x ⟶ K}
    (h : X.Γevaluation x ≫ α = X.Γevaluation x ≫ β) : α = β := by
  -- `X ⟶ Spec Γ(X, ⊤)` is an open immersion, so it induces an isomorphism of residue fields.
  have h₁ := Scheme.Γevaluation_naturality X.toSpecΓ x
  rw [Scheme.toSpecΓ_appTop] at h₁
  rw [← cancel_epi (X.toSpecΓ.residueFieldMap x)]
  refine Spec.residueField_hom_ext ?_
  rw [reassoc_of% h₁, reassoc_of% h₁, h]

/-- The geometric point of `X` over `x`: the morphism `Spec κ(x)ᵃˡᵍ ⟶ X` from the spectrum of an
algebraic closure of the residue field at `x`, through `X.fromSpecResidueField x`. -/
noncomputable def Scheme.fromSpecAlgebraicClosure (X : Scheme.{u}) (x : X) :
    Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x

/-- The geometric point over `x` factors through `X.fromSpecResidueField x`. -/
theorem Scheme.fromSpecAlgebraicClosure_def (X : Scheme.{u}) (x : X) :
    X.fromSpecAlgebraicClosure x =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫
        X.fromSpecResidueField x :=
  (rfl)

/-- Every point of `Spec κ(x)ᵃˡᵍ` maps to `x` under the geometric point over `x`. -/
@[simp]
theorem Scheme.fromSpecAlgebraicClosure_apply (X : Scheme.{u}) (x : X)
    (p : Spec (.of (AlgebraicClosure (X.residueField x)))) :
    X.fromSpecAlgebraicClosure x p = x :=
  Scheme.fromSpecResidueField_apply x _

/-- The geometric point over `x` has image exactly `{x}`. -/
@[simp]
theorem Scheme.range_fromSpecAlgebraicClosure (X : Scheme.{u}) (x : X) :
    Set.range (X.fromSpecAlgebraicClosure x) = {x} :=
  Set.range_eq_singleton (X.fromSpecAlgebraicClosure_apply x)

end AlgebraicGeometry

namespace RingHom

open AlgebraicGeometry

universe u

/-- For a ring map `φ : R →+* S` and a point `x` of `Spec S`, the residue field map of
`Spec.map φ` at `x` is an isomorphism iff the induced map `κ(p) → κ(x)` is bijective, where
`p = φ⁻¹ x` is the image point. -/
theorem isIso_SpecMap_residueFieldMap_iff {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : Spec (.of S)) (p : Ideal R) [p.IsPrime] (hp : p = x.asIdeal.comap φ) :
    haveI := x.isPrime
    IsIso ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap x) ↔
      Function.Bijective (Ideal.ResidueField.map p x.asIdeal φ hp) := by
  have := x.isPrime
  -- The residue field isomorphisms of `Spec R` are indexed by the image point, which is
  -- `x.asIdeal.comap φ` by `Spec.map_apply`.
  have hp' : p = ((Spec.map (CommRingCat.ofHom φ)) x).asIdeal :=
    hp.trans (congrArg PrimeSpectrum.asIdeal (Spec.map_apply (CommRingCat.ofHom φ) x)).symm
  subst hp'
  -- Up to the residue field isomorphisms, the residue field map is `Ideal.ResidueField.map`.
  have key : (Spec.map (CommRingCat.ofHom φ)).residueFieldMap x =
      (Scheme.Spec.residueFieldIso (.of R) _).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map _ x.asIdeal φ hp) ≫
        (Scheme.Spec.residueFieldIso (.of S) x).inv := by
    ext y
    obtain ⟨a, rfl⟩ := (Spec (.of R)).residue_surjective _ y
    have h := congr($(Scheme.residue_residueFieldMap (Spec.map (CommRingCat.ofHom φ)) x) a)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h.trans (congrArg (IsLocalRing.residue _)
      (Scheme.localRingHom_comp_stalkIso_apply (CommRingCat.ofHom φ) x a).symm)
  rw [key, isIso_comp_left_iff, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

end RingHom
