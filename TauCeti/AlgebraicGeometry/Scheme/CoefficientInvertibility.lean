/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Invertible coefficient orders on schemes

An integer coefficient order is invertible on a scheme when it is a unit in every local
ring. We give equivalent tests using global sections, affine opens, residue characteristics,
and the existence of the structure morphism to `Spec ℤ[1/n]`. These tests impose no
Noetherian or quasi-compactness assumptions and apply also to the empty scheme.

Invertibility pulls back along every scheme morphism and is detected by surjective
morphisms. Divisors of an invertible order are again invertible, as required when changing
torsion coefficients. The localization is universe-lifted so that its spectrum has the
same universe as the scheme.

## References

* The Stacks Project, Section 59.28, *Kummer theory* (tag 03PK), for the invertibility
  hypothesis on torsion orders.
* Mathlib's `RingedSpace.isUnit_of_isUnit_germ` and the universal property of localization
  supply the local-to-global and factorization constructions.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- A natural number is invertible on a scheme if it is a unit in every local ring. -/
def IsUnitNatCast : Prop :=
  ∀ x : X, IsUnit (n : X.presheaf.stalk x)

/-- Invertibility of an order is equivalent to its being a unit in every stalk. -/
theorem isUnitNatCast_iff_forall_isUnit_stalk :
    X.IsUnitNatCast n ↔ ∀ x : X, IsUnit (n : X.presheaf.stalk x) :=
  Iff.rfl

/-- An invertible order is a unit in the stalk at every point. -/
theorem IsUnitNatCast.isUnit_stalk {X : Scheme.{u}} {n : ℕ} (h : X.IsUnitNatCast n)
    (x : X) : IsUnit (n : X.presheaf.stalk x) :=
  (X.isUnitNatCast_iff_forall_isUnit_stalk n).mp h x

/-- Invertibility of an order is equivalent to its being a unit in global sections. -/
theorem isUnitNatCast_iff_isUnit : X.IsUnitNatCast n ↔ IsUnit (n : Γ(X, ⊤)) := by
  constructor
  · intro h
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ n
    intro x hx
    simpa using h x
  · intro h x
    simpa using h.map (X.presheaf.germ ⊤ x trivial).hom

/-- An invertible order is a unit in the sections over every open. -/
theorem IsUnitNatCast.isUnit {X : Scheme.{u}} {n : ℕ} (h : X.IsUnitNatCast n)
    (U : X.Opens) : IsUnit (n : Γ(X, U)) := by
  simpa using ((X.isUnitNatCast_iff_isUnit n).mp h).map
    (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

/-- It suffices to test invertibility on the rings of sections of affine opens. -/
theorem isUnitNatCast_iff_forall_isUnit_affineOpens :
    X.IsUnitNatCast n ↔ ∀ U : X.affineOpens, IsUnit (n : Γ(X, U.1)) := by
  constructor
  · exact fun h U ↦ h.isUnit U.1
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    simpa using (h ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom

/-- Residue fields detect whether an order is invertible, including in residue characteristic
zero. -/
theorem isUnitNatCast_iff_forall_residueField_ne_zero :
    X.IsUnitNatCast n ↔ ∀ x : X, (n : X.residueField x) ≠ 0 := by
  unfold IsUnitNatCast
  apply forall_congr'
  intro x
  simpa only [map_natCast] using
    ((X.evaluation_ne_zero_iff_mem_basicOpen x trivial (n : Γ(X, ⊤))).trans
      (X.mem_basicOpen (n : Γ(X, ⊤)) x trivial)).symm

/-- The residue characteristic must not divide the order. For characteristic zero this
condition says precisely that the order is nonzero. -/
theorem isUnitNatCast_iff_forall_ringChar_not_dvd :
    X.IsUnitNatCast n ↔ ∀ x : X, ¬ringChar (X.residueField x) ∣ n := by
  simp only [isUnitNatCast_iff_forall_residueField_ne_zero, ne_eq, ringChar.spec]

/-- On an affine spectrum, invertibility is the usual ring-theoretic condition. -/
@[simp]
theorem isUnitNatCast_Spec_iff (R : CommRingCat.{u}) :
    (Spec R).IsUnitNatCast n ↔ IsUnit (n : R) := by
  rw [isUnitNatCast_iff_isUnit]
  exact ⟨fun h ↦ by simpa using h.map (ΓSpecIso R).hom.hom,
    fun h ↦ by simpa using h.map (ΓSpecIso R).inv.hom⟩

variable {X n}

/-- Invertibility of an order is preserved by arbitrary scheme pullback. -/
theorem IsUnitNatCast.comap {Y : Scheme.{u}} (h : X.IsUnitNatCast n) (f : Y ⟶ X) :
    Y.IsUnitNatCast n := by
  intro y
  simpa using (h (f y)).map (f.stalkMap y).hom

/-- A surjective morphism detects invertibility of an order; no flatness is needed. -/
theorem isUnitNatCast_iff_of_surjective {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Function.Surjective f) : Y.IsUnitNatCast n ↔ X.IsUnitNatCast n := by
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := hf x
    exact (isUnit_map_iff (f.stalkMap y).hom _).mp (by simpa using h y)
  · exact fun h ↦ h.comap f

/-- Every divisor of an invertible order is invertible. -/
theorem IsUnitNatCast.of_dvd {m : ℕ} (h : X.IsUnitNatCast n) (hmn : m ∣ n) :
    X.IsUnitNatCast m := by
  intro x
  exact isUnit_of_dvd_unit (map_dvd (Nat.castRingHom _) hmn) (h x)

/-- A product of orders is invertible exactly when both factors are. -/
@[simp]
theorem isUnitNatCast_mul_iff (m n : ℕ) :
    X.IsUnitNatCast (m * n) ↔ X.IsUnitNatCast m ∧ X.IsUnitNatCast n := by
  simp only [isUnitNatCast_iff_isUnit, Nat.cast_mul, IsUnit.mul_iff]

/-- The order one is invertible on every scheme, including the empty scheme. -/
@[simp]
theorem isUnitNatCast_one : X.IsUnitNatCast 1 := by
  intro x
  simp

variable (X n)

/-- The canonical morphism to `Spec ℤ[1/n]` when `n` is invertible on `X`. -/
noncomputable def toSpecIntLocalization (h : X.IsUnitNatCast n) :
    X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ))) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom <|
    IsLocalization.Away.lift (n : ULift.{u} ℤ)
      (g := (Int.castRingHom Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom)
      (by simpa using (X.isUnitNatCast_iff_isUnit n).mp h))

/-- There is at most one morphism to `Spec ℤ[1/n]`. -/
instance subsingleton_hom_Spec_intLocalization :
    Subsingleton (X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
  refine ⟨fun f g ↦ ext_of_isAffine ?_⟩
  rw [← cancel_epi (ΓSpecIso (.of (Localization.Away (n : ULift.{u} ℤ)))).inv]
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (n : ULift.{u} ℤ))
  exact congrArg CommRingCat.Hom.hom
    (CommRingCat.isInitial.hom_ext (CommRingCat.ofHom _) (CommRingCat.ofHom _))

/-- An order is invertible exactly when the scheme admits its unique structure morphism
to `Spec ℤ[1/n]`; its composite to `Spec ℤ` is necessarily the structure morphism. -/
theorem isUnitNatCast_iff_nonempty_hom_Spec_intLocalization :
    X.IsUnitNatCast n ↔
      Nonempty (X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
  constructor
  · exact fun h ↦ ⟨X.toSpecIntLocalization n h⟩
  · rintro ⟨f⟩
    apply IsUnitNatCast.comap (f := f)
    rw [isUnitNatCast_Spec_iff]
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
      (n : ULift.{u} ℤ)) (n : ULift.{u} ℤ)

end AlgebraicGeometry.Scheme
