/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Invertible coefficient orders on schemes

A coefficient order is invertible on a scheme when it is a unit in every local
ring. The class `Scheme.IsInvertibleOn` records this condition for torsion coefficients.
We give equivalent tests using global sections, affine opens, residue characteristics,
and the existence of the structure morphism to `Spec ℤ[1/n]`. On a nonempty scheme
over a field, invertibility is equivalent to the order being nonzero in that field.
The local tests impose no Noetherian or quasi-compactness assumptions and apply also
to the empty scheme.

Invertibility pulls back along every scheme morphism, is detected by surjective
morphisms, and can be checked on any open cover. Divisors of an invertible order are
again invertible, as required when changing torsion coefficients. The localization is
universe-lifted so that its spectrum has the same universe as the scheme.

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

variable (n : ℕ) (X : Scheme.{u})

/-- A coefficient order is invertible on a scheme if it is a unit in every local ring.
Equivalently, it is a unit in every residue field. -/
class IsInvertibleOn : Prop where
  /-- The coefficient order is a unit in every local ring. -/
  isUnit_stalk : ∀ x : X, IsUnit (n : X.presheaf.stalk x)

/-- Invertibility of an order is equivalent to its being a unit in every stalk. -/
theorem isInvertibleOn_iff_forall_isUnit_stalk :
    IsInvertibleOn n X ↔ ∀ x : X, IsUnit (n : X.presheaf.stalk x) :=
  ⟨fun h ↦ h.isUnit_stalk, fun h ↦ ⟨h⟩⟩

/-- Invertibility of an order is equivalent to its being a unit in global sections. -/
theorem isInvertibleOn_iff_isUnit : IsInvertibleOn n X ↔ IsUnit (n : Γ(X, ⊤)) := by
  rw [isInvertibleOn_iff_forall_isUnit_stalk]
  constructor
  · intro h
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ n
    intro x hx
    simpa using h x
  · intro h x
    simpa using h.map (X.presheaf.germ ⊤ x trivial).hom

/-- An invertible order is a unit in the sections over every open. -/
theorem IsInvertibleOn.isUnit [IsInvertibleOn n X] (U : X.Opens) :
    IsUnit (n : Γ(X, U)) := by
  simpa using ((isInvertibleOn_iff_isUnit n X).mp inferInstance).map
    (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

/-- It suffices to test invertibility on the rings of sections of affine opens. -/
theorem isInvertibleOn_iff_forall_isUnit_affineOpens :
    IsInvertibleOn n X ↔ ∀ U : X.affineOpens, IsUnit (n : Γ(X, U.val)) := by
  constructor
  · intro h U
    exact h.isUnit n X U.val
  · intro h
    constructor
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    simpa using (h ⟨U, hU⟩).map (X.presheaf.germ U x hxU).hom

/-- Residue fields detect invertibility, including in residue characteristic zero. -/
theorem isInvertibleOn_iff_forall_residueField_ne_zero :
    IsInvertibleOn n X ↔ ∀ x : X, (n : X.residueField x) ≠ 0 := by
  rw [isInvertibleOn_iff_forall_isUnit_stalk]
  apply forall_congr'
  intro x
  simpa only [map_natCast] using
    ((X.evaluation_ne_zero_iff_mem_basicOpen x trivial (n : Γ(X, ⊤))).trans
      (X.mem_basicOpen (n : Γ(X, ⊤)) x trivial)).symm

/-- The residue characteristic must not divide the order. For characteristic zero this
condition says precisely that the order is nonzero. -/
theorem isInvertibleOn_iff_forall_ringChar_not_dvd :
    IsInvertibleOn n X ↔ ∀ x : X, ¬ringChar (X.residueField x) ∣ n := by
  simp only [isInvertibleOn_iff_forall_residueField_ne_zero, ne_eq, ringChar.spec]

/-- On an affine spectrum, invertibility is the usual ring-theoretic condition. -/
@[simp]
theorem isInvertibleOn_Spec_iff (R : CommRingCat.{u}) :
    IsInvertibleOn n (Spec R) ↔ IsUnit (n : R) := by
  rw [isInvertibleOn_iff_isUnit]
  exact ⟨fun h ↦ by simpa using h.map (ΓSpecIso R).hom.hom,
    fun h ↦ by simpa using h.map (ΓSpecIso R).inv.hom⟩

variable {n X}

/-- Invertibility of an order is preserved by arbitrary scheme pullback. -/
theorem IsInvertibleOn.of_hom {Y : Scheme.{u}} (f : Y ⟶ X) [IsInvertibleOn n X] :
    IsInvertibleOn n Y := by
  constructor
  intro y
  simpa using (IsInvertibleOn.isUnit_stalk (n := n) (f y)).map (f.stalkMap y).hom

/-- A jointly surjective family of morphisms detects invertibility of an order;
no flatness is needed. -/
theorem isInvertibleOn_of_jointlySurjective {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) (hf : ∀ x, ∃ i y, f i y = x)
    [∀ i, IsInvertibleOn n (Y i)] : IsInvertibleOn n X := by
  constructor
  intro x
  obtain ⟨i, y, rfl⟩ := hf x
  exact (isUnit_map_iff ((f i).stalkMap y).hom _).mp
    (by simpa using IsInvertibleOn.isUnit_stalk (n := n) y)

/-- A surjective morphism detects invertibility of an order; no flatness is needed. -/
theorem isInvertibleOn_iff_of_surjective {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Function.Surjective f) : IsInvertibleOn n Y ↔ IsInvertibleOn n X := by
  constructor
  · intro h
    let : ∀ _ : Unit, IsInvertibleOn n Y := fun _ ↦ h
    exact isInvertibleOn_of_jointlySurjective (fun _ : Unit ↦ f) (fun x ↦ ⟨(), hf x⟩)
  · intro h
    exact IsInvertibleOn.of_hom f

/-- Every divisor of an invertible order is invertible. -/
theorem IsInvertibleOn.of_dvd {m : ℕ} [IsInvertibleOn n X] (hmn : m ∣ n) :
    IsInvertibleOn m X := by
  constructor
  intro x
  exact isUnit_of_dvd_unit (map_dvd (Nat.castRingHom _) hmn)
    (IsInvertibleOn.isUnit_stalk (n := n) x)

variable (n X)

/-- A product of orders is invertible exactly when both factors are. -/
@[simp]
theorem isInvertibleOn_mul_iff (m n : ℕ) :
    IsInvertibleOn (m * n) X ↔ IsInvertibleOn m X ∧ IsInvertibleOn n X := by
  simp only [isInvertibleOn_iff_isUnit, Nat.cast_mul, IsUnit.mul_iff]

/-- The order one is invertible on every scheme, including the empty scheme. -/
@[simp]
instance isInvertibleOn_one : IsInvertibleOn 1 X where
  isUnit_stalk x := by simp

/-- Every order is invertible on the empty scheme. -/
instance isInvertibleOn_of_isEmpty [IsEmpty X] : IsInvertibleOn n X where
  isUnit_stalk x := isEmptyElim x

/-- Zero is invertible precisely on the empty scheme. -/
@[simp]
theorem isInvertibleOn_zero_iff : IsInvertibleOn 0 X ↔ IsEmpty X := by
  constructor
  · intro h
    exact ⟨fun x ↦ ((isInvertibleOn_iff_forall_residueField_ne_zero 0 X).mp h x)
      (Nat.cast_zero)⟩
  · intro h
    infer_instance

/-- Restriction to an open subscheme preserves invertibility. -/
instance isInvertibleOn_toScheme (U : X.Opens) [IsInvertibleOn n X] :
    IsInvertibleOn n U.toScheme :=
  IsInvertibleOn.of_hom U.ι

/-- Invertibility can be tested on any family of opens covering the scheme. -/
theorem isInvertibleOn_iff_of_iSup_eq_top {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) : IsInvertibleOn n X ↔ ∀ i, IsInvertibleOn n (U i).toScheme := by
  constructor
  · intro h i
    infer_instance
  · intro h
    let : ∀ i, IsInvertibleOn n (U i).toScheme := h
    apply isInvertibleOn_of_jointlySurjective (fun i ↦ (U i).ι)
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, ⟨x, hi⟩, Scheme.Opens.ι_apply (U i) _⟩

/-- On a nonempty scheme over a field, an order is invertible exactly when its image
in the field is nonzero. Nonemptiness is essential: every order is invertible on the
empty scheme. -/
theorem isInvertibleOn_iff_ne_zero {k : Type u} [Field k] [Nonempty X]
    (f : X ⟶ Spec (.of k)) : IsInvertibleOn n X ↔ (n : k) ≠ 0 := by
  rw [isInvertibleOn_iff_of_surjective f (Function.surjective_to_subsingleton f),
    isInvertibleOn_Spec_iff, isUnit_iff_ne_zero]

/-- Over a field of characteristic `p`, invertibility on a nonempty scheme is equivalent
to nondivisibility by `p`, also when `p = 0`. -/
theorem isInvertibleOn_iff_not_dvd {k : Type u} [Field k] [Nonempty X]
    (f : X ⟶ Spec (.of k)) (p : ℕ) [CharP k p] : IsInvertibleOn n X ↔ ¬p ∣ n := by
  rw [isInvertibleOn_iff_ne_zero n X f, ne_eq, CharP.cast_eq_zero_iff k p]

/-- The canonical morphism to `Spec ℤ[1/n]` when `n` is invertible on `X`. -/
noncomputable def toSpecIntLocalization [IsInvertibleOn n X] :
    X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ))) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom <|
    IsLocalization.Away.lift (n : ULift.{u} ℤ)
      (g := (Int.castRingHom Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom)
      (by simpa using (isInvertibleOn_iff_isUnit n X).mp inferInstance))

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
theorem isInvertibleOn_iff_nonempty_hom_Spec_intLocalization :
    IsInvertibleOn n X ↔
      Nonempty (X ⟶ Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
  constructor
  · intro h
    exact ⟨X.toSpecIntLocalization n⟩
  · rintro ⟨f⟩
    have : IsInvertibleOn n (Spec (.of (Localization.Away (n : ULift.{u} ℤ)))) := by
      rw [isInvertibleOn_Spec_iff]
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away
        (n : ULift.{u} ℤ)) (n : ULift.{u} ℤ)
    exact IsInvertibleOn.of_hom f

end AlgebraicGeometry.Scheme
