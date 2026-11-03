/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Residue fields of schemes: invertible natural numbers, geometric points, and spectra

This file records how the condition `(N : κ(x)) ≠ 0`, that a natural number `N` is invertible in
the residue field at a point `x`, carries over between schemes. It is the form in which "`N` is
invertible on the base" enters the theory of level structures on elliptic curves.

It also provides the geometric point `Spec κ(x)ᵃˡᵍ ⟶ X` over a point `x`, through which such
conditions are checked after base change to an algebraically closed field, and computes the
canonical morphism `Spec κ(x) ⟶ X` on the opens containing `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.fromSpecAlgebraicClosure X x`: the morphism `Spec κ(x)ᵃˡᵍ ⟶ X` from
  the spectrum of an algebraic closure of the residue field at `x`, whose image is `{x}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.natCast_residueField_ne_zero`: if `N` is invertible in the residue
  field at `f x`, then it is invertible in the residue field at `x`, for any morphism `f`.
* `AlgebraicGeometry.Spec.natCast_residueField_ne_zero`: if `N` is invertible in a field `K`, then
  it is invertible in the residue field of `Spec K`.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_closedPoint_mem`: the closed point of
  `Spec κ(x)` lies over every open containing `x`.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_preimage_eq_top`: the inverse image of an open
  containing `x` under `Spec κ(x) ⟶ X` is everything.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_appLE`: on an open containing `x`, the morphism
  `Spec κ(x) ⟶ X` sends a function to its value at `x`.
* `AlgebraicGeometry.Scheme.residueFieldSectionsIso`: for an open `V` containing `x`, the functions
  on the inverse image of `V` in `Spec κ(x)` are `κ(x)`, and `Spec κ(x) ⟶ X` acts on sections over
  `V` by evaluation at `x` (`Scheme.fromSpecResidueField_app_residueFieldSectionsIso_hom`).
* `RingHom.isIso_SpecMap_residueFieldMap_iff`: for a ring map `φ : R →+* S` and a prime
  `x` of `S`, the residue field map of `Spec S ⟶ Spec R` at `x` is an isomorphism iff the map of
  residue fields `κ(φ⁻¹ x) → κ(x)` is bijective. This translates conditions on residue fields
  between schemes and rings, for instance for étale neighbourhoods built from algebras.

The two results on natural numbers only use that a ring homomorphism between fields, such as
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

section FromSpecResidueField

variable {X : Scheme.{u}} (x : X)

/-- The closed point of `Spec κ(x)` maps to `x`, so it lies over every open containing `x`. -/
lemma Scheme.fromSpecResidueField_closedPoint_mem {V : X.Opens} (hx : x ∈ V) :
    X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) ∈ V := by
  convert hx using 1
  exact Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x))

/-- The inverse image of an open containing `x` under `Spec κ(x) ⟶ X` is everything. -/
lemma Scheme.fromSpecResidueField_preimage_eq_top {V : X.Opens} (hx : x ∈ V) :
    X.fromSpecResidueField x ⁻¹ᵁ V = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem _ (fromSpecResidueField_closedPoint_mem x hx)

/-- On an open `V` containing `x`, the morphism `Spec κ(x) ⟶ X` sends a function to its value at
`x`, as a global function on `Spec κ(x)`. -/
lemma Scheme.fromSpecResidueField_appLE {V : X.Opens} (hx : x ∈ V)
    (h : (⊤ : (Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ V) :
    (X.fromSpecResidueField x).appLE V ⊤ h =
      X.evaluation V x hx ≫ (Scheme.ΓSpecIso (X.residueField x)).inv := by
  have hV := fromSpecResidueField_closedPoint_mem x hx
  have : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  -- `Spec κ(x) ⟶ X` is `Spec κ(x) ⟶ Spec 𝒪_{X,x} ⟶ X`, whose action on sections near the
  -- closed point is computed by Mathlib's `Scheme.germ_stalkClosedPointTo`.
  rw [Iso.eq_comp_inv, ← X.germ_residue x hx,
    ← Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) V hV]
  refine Eq.trans ?_ (Scheme.germ_stalkClosedPointTo
    (Spec.map (X.residue x) ≫ X.fromSpecStalk x) V hV).symm
  rw [Scheme.Hom.appLE, Category.assoc, Iso.trans_hom, Functor.mapIso_hom]
  congr 2

/-- For an open `V` containing `x`, the functions on `ι⁻¹ V = Spec κ(x)` are `κ(x)`, where
`ι : Spec κ(x) ⟶ X`. -/
noncomputable def Scheme.residueFieldSectionsIso {V : X.Opens} (hx : x ∈ V) :
    Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ V) ≅ X.residueField x :=
  ((Spec (X.residueField x)).presheaf.mapIso
    (eqToIso (fromSpecResidueField_preimage_eq_top x hx)).op).symm ≪≫
    Scheme.ΓSpecIso (X.residueField x)

/-- The inverse of `Scheme.residueFieldSectionsIso` is restriction from `⊤` to `ι⁻¹ V`. -/
lemma Scheme.residueFieldSectionsIso_inv {V : X.Opens} (hx : x ∈ V) :
    (X.residueFieldSectionsIso x hx).inv = (Scheme.ΓSpecIso (X.residueField x)).inv ≫
      (Spec (X.residueField x)).presheaf.map (homOfLE le_top).op := by
  rw [residueFieldSectionsIso, Iso.trans_inv]
  rfl

/-- The identifications `Scheme.residueFieldSectionsIso` commute with restriction. -/
@[reassoc (attr := simp)]
lemma Scheme.residueFieldSectionsIso_map {U V : X.Opens} (hU : x ∈ U) (hV : x ∈ V)
    (j : X.fromSpecResidueField x ⁻¹ᵁ U ⟶ X.fromSpecResidueField x ⁻¹ᵁ V) :
    (Spec (X.residueField x)).presheaf.map j.op ≫ (X.residueFieldSectionsIso x hU).hom =
      (X.residueFieldSectionsIso x hV).hom := by
  rw [residueFieldSectionsIso, residueFieldSectionsIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc]
  rfl

/-- On an open `V` containing `x`, the morphism `ι : Spec κ(x) ⟶ X` acts on sections by
evaluation at `x`. -/
@[reassoc (attr := simp)]
lemma Scheme.fromSpecResidueField_app_residueFieldSectionsIso_hom {V : X.Opens} (hx : x ∈ V) :
    (X.fromSpecResidueField x).app V ≫ (X.residueFieldSectionsIso x hx).hom =
      X.evaluation V x hx := by
  rw [← Iso.eq_comp_inv, residueFieldSectionsIso_inv, ← Category.assoc,
    ← fromSpecResidueField_appLE x hx (fromSpecResidueField_preimage_eq_top x hx).ge,
    Scheme.Hom.appLE_map]
  rfl

end FromSpecResidueField

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
