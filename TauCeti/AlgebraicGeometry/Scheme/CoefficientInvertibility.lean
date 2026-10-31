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
def IsInvertibleOn : Prop :=
  ∀ x : X, IsUnit (n : X.presheaf.stalk x)

/-- Invertibility of an order is equivalent to its being a unit in global sections. -/
theorem isInvertibleOn_iff_isUnit : X.IsInvertibleOn n ↔ IsUnit (n : Γ(X, ⊤)) := by
  constructor
  · intro h
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ n
    intro x hx
    simpa using h x
  · intro h x
    simpa using h.map (X.presheaf.germ ⊤ x trivial).hom

/-- An invertible order is a unit in the sections over every open. -/
theorem IsInvertibleOn.isUnit {X : Scheme.{u}} {n : ℕ} (h : X.IsInvertibleOn n)
    (U : X.Opens) : IsUnit (n : Γ(X, U)) := by
  simpa using ((X.isInvertibleOn_iff_isUnit n).mp h).map
    (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

/-- It suffices to test invertibility on the rings of sections of affine opens. -/
theorem isInvertibleOn_iff_forall_affineOpens :
    X.IsInvertibleOn n ↔ ∀ U : X.affineOpens, IsUnit (n : Γ(X, U.1)) := by
  constructor
  · exact fun h U ↦ h.isUnit U.1
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    simpa using (h ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom

/-- Residue fields detect whether an order is invertible, including in residue characteristic
zero. -/
theorem isInvertibleOn_iff_forall_residueField_ne_zero :
    X.IsInvertibleOn n ↔ ∀ x : X, (n : X.residueField x) ≠ 0 := by
  unfold IsInvertibleOn
  apply forall_congr'
  intro x
  simpa only [map_natCast] using
    ((X.evaluation_ne_zero_iff_mem_basicOpen x trivial (n : Γ(X, ⊤))).trans
      (X.mem_basicOpen (n : Γ(X, ⊤)) x trivial)).symm

/-- The residue characteristic must not divide the order. For characteristic zero this
condition says precisely that the order is nonzero. -/
theorem isInvertibleOn_iff_forall_ringChar_not_dvd :
    X.IsInvertibleOn n ↔ ∀ x : X, ¬ringChar (X.residueField x) ∣ n := by
  simp only [isInvertibleOn_iff_forall_residueField_ne_zero, ne_eq, ringChar.spec]

/-- On an affine spectrum, invertibility is the usual ring-theoretic condition. -/
@[simp]
theorem isInvertibleOn_Spec_iff (R : CommRingCat.{u}) :
    (Spec R).IsInvertibleOn n ↔ IsUnit (n : R) := by
  rw [isInvertibleOn_iff_isUnit]
  exact ⟨fun h ↦ by simpa using h.map (ΓSpecIso R).hom.hom,
    fun h ↦ by simpa using h.map (ΓSpecIso R).inv.hom⟩

variable {X n}

/-- Invertibility of an order is preserved by arbitrary scheme pullback. -/
theorem IsInvertibleOn.comap {Y : Scheme.{u}} (h : X.IsInvertibleOn n) (f : Y ⟶ X) :
    Y.IsInvertibleOn n := by
  intro y
  simpa using (h (f y)).map (f.stalkMap y).hom

/-- A surjective morphism detects invertibility of an order; no flatness is needed. -/
theorem isInvertibleOn_iff_of_surjective {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Function.Surjective f) : Y.IsInvertibleOn n ↔ X.IsInvertibleOn n := by
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := hf x
    exact (isUnit_map_iff (f.stalkMap y).hom _).mp (by simpa using h y)
  · exact fun h ↦ h.comap f

/-- Every divisor of an invertible order is invertible. -/
theorem IsInvertibleOn.of_dvd {m : ℕ} (h : X.IsInvertibleOn n) (hmn : m ∣ n) :
    X.IsInvertibleOn m := by
  intro x
  exact isUnit_of_dvd_unit (map_dvd (Nat.castRingHom _) hmn) (h x)

/-- A product of orders is invertible exactly when both factors are. -/
@[simp]
theorem isInvertibleOn_mul_iff (m n : ℕ) :
    X.IsInvertibleOn (m * n) ↔ X.IsInvertibleOn m ∧ X.IsInvertibleOn n := by
  simp only [isInvertibleOn_iff_isUnit, Nat.cast_mul, IsUnit.mul_iff]

/-- The order one is invertible on every scheme, including the empty scheme. -/
@[simp]
theorem isInvertibleOn_one : X.IsInvertibleOn 1 := by
  intro x
  simp

variable (X n)

/-- The canonical morphism to `Spec ℤ[1/n]` when `n` is invertible on `X`. -/
noncomputable def toSpecIntLocalization (h : X.IsInvertibleOn n) :
    X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ))) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom <|
    IsLocalization.Away.lift (n : ULift.{u} ℤ)
      (g := (Int.castRingHom Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom)
      (by simpa using (X.isInvertibleOn_iff_isUnit n).mp h))

/-- There is at most one morphism to `Spec ℤ[1/n]`. -/
instance subsingleton_hom_spec_intLocalization :
    Subsingleton (X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
  refine ⟨fun f g ↦ ext_of_isAffine ?_⟩
  rw [← cancel_epi (ΓSpecIso (.of (Localization.Away (n : ULift.{u} ℤ)))).inv]
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (n : ULift.{u} ℤ))
  exact congrArg CommRingCat.Hom.hom
    (CommRingCat.isInitial.hom_ext (CommRingCat.ofHom _) (CommRingCat.ofHom _))

/-- An order is invertible exactly when the scheme admits its unique structure morphism
to `Spec ℤ[1/n]`; its composite to `Spec ℤ` is necessarily the structure morphism. -/
theorem isInvertibleOn_iff_nonempty_hom_spec_intLocalization :
    X.IsInvertibleOn n ↔
      Nonempty (X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
  constructor
  · exact fun h ↦ ⟨X.toSpecIntLocalization n h⟩
  · rintro ⟨f⟩
    apply IsInvertibleOn.comap (f := f)
    rw [isInvertibleOn_Spec_iff]
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
      (n : ULift.{u} ℤ)) (n : ULift.{u} ℤ)

end AlgebraicGeometry.Scheme
