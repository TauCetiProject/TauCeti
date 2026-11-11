/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Numerical quotients of a sesquilinear map

For a possibly nonsymmetric sesquilinear map `b : L →ₛₗ[ρ] M →ₛₗ[σ] P`, its left radical and
right radical need not agree—indeed, its two arguments need not even have the same type. This file
defines the two radicals separately, quotients each argument by the appropriate radical, and
descends `b` to a nondegenerate pairing between the resulting quotients. A biadditive pairing of
additive groups can be fed to this construction through `AddMonoidHom.toIntLinearMap₂`.

The intermediate pairings with only one argument quotiented are also provided.  Quotienting the
left argument makes the pairing left-separating, while quotienting the right argument makes it
right-separating; no assertion is made about the other side until both quotients are taken.

## Main definitions

* `TauCeti.leftRadical` and `TauCeti.rightRadical`: the two radicals of a sesquilinear map.
* `TauCeti.LeftNumericalQuotient` and `TauCeti.RightNumericalQuotient`: the corresponding
  quotient modules.
* `TauCeti.leftNumericalPairing` and `TauCeti.rightNumericalPairing`: the one-sided quotient
  pairings.
* `TauCeti.numericalPairing`: the pairing between both numerical quotients.

## Main results

* `TauCeti.leftNumericalPairing_separatingLeft` and
  `TauCeti.rightNumericalPairing_separatingRight`: the precise one-sided nondegeneracy results.
* `TauCeti.numericalPairing_nondegenerate`: the pairing between both quotients has zero left and
  right radicals.

The quotient construction uses Mathlib's asymmetric `LinearMap.liftQ₂`, so the two arguments may
be modules over different commutative rings, each semilinear along its own ring homomorphism into
the scalars of the target. The terminology and the warning that the two radicals remain distinct
follow Dancso–Licata, *Koszul algebras and flow lattices*, Section 3.1.
-/

public section

namespace TauCeti

universe u₁ u₂ u₃

variable {R R₁ R₂ : Type*} {L : Type u₁} {M : Type u₂} {P : Type u₃}

section Radicals

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid L] [Module R₁ L] [AddCommMonoid M] [Module R₂ M]
variable [AddCommMonoid P] [Module R P]
variable {ρ : R₁ →+* R} {σ : R₂ →+* R}
variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P)

/-- The **left radical** of a sesquilinear map: the elements in the first argument which pair to
zero with every element of the second argument. -/
def leftRadical : Submodule R₁ L :=
  b.ker

/-- The **right radical** of a sesquilinear map: the elements in the second argument which pair to
zero with every element of the first argument. -/
def rightRadical : Submodule R₂ M :=
  b.flip.ker

/-- Membership in the left radical means pairing to zero against every second argument. -/
@[simp]
theorem mem_leftRadical_iff (x : L) : x ∈ leftRadical b ↔ ∀ y : M, b x y = 0 := by
  simp [leftRadical, LinearMap.ext_iff]

/-- Membership in the right radical means pairing to zero against every first argument. -/
@[simp]
theorem mem_rightRadical_iff (y : M) : y ∈ rightRadical b ↔ ∀ x : L, b x y = 0 := by
  simp [rightRadical, LinearMap.ext_iff]

/-- A sesquilinear map is left-separating exactly when its left radical is trivial. -/
theorem separatingLeft_iff_leftRadical_eq_bot :
    b.SeparatingLeft ↔ leftRadical b = ⊥ := by
  rw [leftRadical]
  exact LinearMap.separatingLeft_iff_ker_eq_bot

/-- A sesquilinear map is right-separating exactly when its right radical is trivial. -/
theorem separatingRight_iff_rightRadical_eq_bot :
    b.SeparatingRight ↔ rightRadical b = ⊥ := by
  rw [rightRadical]
  exact LinearMap.separatingRight_iff_flip_ker_eq_bot

end Radicals

section Quotients

variable [CommRing R] [CommRing R₁] [CommRing R₂]
variable [AddCommGroup L] [Module R₁ L] [AddCommGroup M] [Module R₂ M]
variable [AddCommGroup P] [Module R P]
variable {ρ : R₁ →+* R} {σ : R₂ →+* R}
variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P)

/-- The quotient of the first argument by the left radical. -/
abbrev LeftNumericalQuotient := L ⧸ leftRadical b

/-- The quotient of the second argument by the right radical. -/
abbrev RightNumericalQuotient := M ⧸ rightRadical b

/-- The quotient map from the first argument to its left numerical quotient. -/
def leftNumericalQuotientMk : L →ₗ[R₁] LeftNumericalQuotient b :=
  (leftRadical b).mkQ

/-- The quotient map from the second argument to its right numerical quotient. -/
def rightNumericalQuotientMk : M →ₗ[R₂] RightNumericalQuotient b :=
  (rightRadical b).mkQ

/-- The left numerical quotient map sends an element to its quotient class. -/
theorem leftNumericalQuotientMk_apply (x : L) :
    leftNumericalQuotientMk b x = Submodule.Quotient.mk x :=
  Submodule.mkQ_apply (leftRadical b) x

/-- The right numerical quotient map sends an element to its quotient class. -/
theorem rightNumericalQuotientMk_apply (y : M) :
    rightNumericalQuotientMk b y = Submodule.Quotient.mk y :=
  Submodule.mkQ_apply (rightRadical b) y

/-- The kernel of the left numerical quotient map is the left radical. -/
@[simp]
theorem ker_leftNumericalQuotientMk : (leftNumericalQuotientMk b).ker = leftRadical b :=
  (leftRadical b).ker_mkQ

/-- The kernel of the right numerical quotient map is the right radical. -/
@[simp]
theorem ker_rightNumericalQuotientMk : (rightNumericalQuotientMk b).ker = rightRadical b :=
  (rightRadical b).ker_mkQ

/-- The left numerical quotient map is surjective. -/
theorem leftNumericalQuotientMk_surjective :
    Function.Surjective (leftNumericalQuotientMk b) :=
  (leftRadical b).mkQ_surjective

/-- The right numerical quotient map is surjective. -/
theorem rightNumericalQuotientMk_surjective :
    Function.Surjective (rightNumericalQuotientMk b) :=
  (rightRadical b).mkQ_surjective

/-- A class in the left numerical quotient vanishes exactly when its representative lies in the
left radical. -/
@[simp]
theorem leftNumericalQuotientMk_eq_zero_iff (x : L) :
    leftNumericalQuotientMk b x = 0 ↔ x ∈ leftRadical b := by
  rw [← LinearMap.mem_ker, ker_leftNumericalQuotientMk]

/-- A class in the right numerical quotient vanishes exactly when its representative lies in the
right radical. -/
@[simp]
theorem rightNumericalQuotientMk_eq_zero_iff (y : M) :
    rightNumericalQuotientMk b y = 0 ↔ y ∈ rightRadical b := by
  rw [← LinearMap.mem_ker, ker_rightNumericalQuotientMk]

/-- Two elements have the same left numerical class exactly when their difference lies in the
left radical. -/
@[simp]
theorem leftNumericalQuotientMk_eq_iff (x x' : L) :
    leftNumericalQuotientMk b x = leftNumericalQuotientMk b x' ↔
      x - x' ∈ leftRadical b := by
  rw [← sub_eq_zero, ← map_sub, leftNumericalQuotientMk_eq_zero_iff]

/-- Two elements have the same right numerical class exactly when their difference lies in the
right radical. -/
@[simp]
theorem rightNumericalQuotientMk_eq_iff (y y' : M) :
    rightNumericalQuotientMk b y = rightNumericalQuotientMk b y' ↔
      y - y' ∈ rightRadical b := by
  rw [← sub_eq_zero, ← map_sub, rightNumericalQuotientMk_eq_zero_iff]

/-- Quotienting only the first argument by the left radical gives a pairing on the left numerical
quotient and the original second argument. -/
def leftNumericalPairing : LeftNumericalQuotient b →ₛₗ[ρ] M →ₛₗ[σ] P :=
  (leftRadical b).liftQ b le_rfl

/-- Quotienting only the second argument by the right radical gives a pairing on the original
first argument and the right numerical quotient. -/
def rightNumericalPairing : L →ₛₗ[ρ] RightNumericalQuotient b →ₛₗ[σ] P :=
  ((rightRadical b).liftQ b.flip le_rfl).flip

/-- The left quotient pairing is represented by the original pairing. -/
@[simp]
theorem leftNumericalPairing_mk (x : L) (y : M) :
    leftNumericalPairing b (leftNumericalQuotientMk b x) y = b x y :=
  (rfl)

/-- The right quotient pairing is represented by the original pairing. -/
@[simp]
theorem rightNumericalPairing_mk (x : L) (y : M) :
    rightNumericalPairing b x (rightNumericalQuotientMk b y) = b x y :=
  (rfl)

/-- The left quotient pairing is the unique sesquilinear map which agrees with the original pairing
on representatives of the left quotient. -/
theorem leftNumericalPairing_unique
    (c : LeftNumericalQuotient b →ₛₗ[ρ] M →ₛₗ[σ] P)
    (hc : ∀ x y, c (leftNumericalQuotientMk b x) y = b x y) :
    c = leftNumericalPairing b := by
  apply LinearMap.ext₂
  intro q y
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  rw [hc, leftNumericalPairing_mk]

/-- The right quotient pairing is the unique sesquilinear map which agrees with the original pairing
on representatives of the right quotient. -/
theorem rightNumericalPairing_unique
    (c : L →ₛₗ[ρ] RightNumericalQuotient b →ₛₗ[σ] P)
    (hc : ∀ x y, c x (rightNumericalQuotientMk b y) = b x y) :
    c = rightNumericalPairing b := by
  apply LinearMap.ext₂
  intro x q
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  rw [hc, rightNumericalPairing_mk]

/-- Quotienting the first argument by the left radical makes the pairing left-separating. -/
theorem leftNumericalPairing_separatingLeft : (leftNumericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  simpa using hq

/-- Quotienting the second argument by the right radical makes the pairing right-separating. -/
theorem rightNumericalPairing_separatingRight : (rightNumericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  simpa using hq

/-- The pairing descended through both the left and right radicals. -/
def numericalPairing :
    LeftNumericalQuotient b →ₛₗ[ρ] RightNumericalQuotient b →ₛₗ[σ] P :=
  b.liftQ₂ (leftRadical b) (rightRadical b) le_rfl le_rfl

/-- The numerical pairing is represented by the original pairing. -/
@[simp]
theorem numericalPairing_mk (x : L) (y : M) :
    numericalPairing b (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) =
      b x y :=
  (rfl)

/-- The numerical pairing is the unique sesquilinear map between the two quotients which agrees with
the original pairing on representatives. -/
theorem numericalPairing_unique
    (c : LeftNumericalQuotient b →ₛₗ[ρ] RightNumericalQuotient b →ₛₗ[σ] P)
    (hc : ∀ x y, c (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) = b x y) :
    c = numericalPairing b := by
  apply LinearMap.ext₂
  intro q r
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b r
  rw [hc, numericalPairing_mk]

/-- The numerical pairing has trivial left radical. -/
theorem numericalPairing_separatingLeft : (numericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  simpa using fun y ↦ hq (rightNumericalQuotientMk b y)

/-- The numerical pairing has trivial right radical. -/
theorem numericalPairing_separatingRight : (numericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  simpa using fun x ↦ hq (leftNumericalQuotientMk b x)

/-- Quotienting both arguments by their respective radicals produces a nondegenerate pairing. -/
theorem numericalPairing_nondegenerate : (numericalPairing b).Nondegenerate :=
  ⟨numericalPairing_separatingLeft b, numericalPairing_separatingRight b⟩

/-- The left radical of the numerical pairing is trivial. -/
@[simp]
theorem leftRadical_numericalPairing : leftRadical (numericalPairing b) = ⊥ :=
  (separatingLeft_iff_leftRadical_eq_bot (numericalPairing b)).mp
    (numericalPairing_separatingLeft b)

/-- The right radical of the numerical pairing is trivial. -/
@[simp]
theorem rightRadical_numericalPairing : rightRadical (numericalPairing b) = ⊥ :=
  (separatingRight_iff_rightRadical_eq_bot (numericalPairing b)).mp
    (numericalPairing_separatingRight b)

end Quotients

end TauCeti
