/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Filtered.Action
public import TauCeti.Algebra.Lie.Derivation.Action
public import TauCeti.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Filtration-raising actions on coefficient algebra quotients

A filtration-raising Lie action induces nilpotent representations on the quotient rings
of a filtered coefficient algebra. These representations intertwine the quotient-ring
transitions. No derivation assumption is needed for these linear representations; under
that assumption, they also satisfy the Leibniz rule.

The construction transports the module representation along Mathlib's
`Submodule.Quotient.restrictScalarsEquiv`, using `LinearEquiv.conjAlgEquiv`.

Adapted from `Mei/Algebra/Lie/Filtered/Algebra.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.AlgFiltration

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]
  [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toSubmodule R)]

section Quotient

variable [DirectSum.Decomposition ℒ]

/-- The finite-order Lie representation on the original coefficient quotient ring. -/
def quotientLieAction (k : ℕ) : L →ₗ⁅R⁆ Module.End R (A ⧸ F.ideal (k + 1)) :=
  ((Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).conjAlgEquiv R).toLieEquiv
    |>.toLieHom.comp
    (PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k)

/-- The quotient representation is the scalar-restricted one, transported by conjugation. -/
theorem quotientLieAction_eq_conjAlgEquiv (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x =
      (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1)) :
        (A ⧸ F.toSubmodule R (k + 1)) ≃ₗ[R] A ⧸ F.ideal (k + 1)).conjAlgEquiv R
        (PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k x) :=
  (rfl)

/-- Evaluation transports the scalar-restricted quotient representation by conjugation. -/
theorem quotientLieAction_apply (k : ℕ) (x : L) (q : A ⧸ F.ideal (k + 1)) :
    F.quotientLieAction d ℒ k x q =
      (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1)))
        (PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R)
          (F.toSubmodule_antitone R) k x
          ((Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).symm q)) := (rfl)

/-- Quotient representatives are acted on by the original Lie action. -/
@[simp]
theorem quotientLieAction_mk (k : ℕ) (x : L) (a : A) :
    F.quotientLieAction d ℒ k x (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ⁅x, a⁆ := by
  rw [quotientLieAction_apply, ← Ideal.Quotient.mk_eq_mk]
  exact congrArg _ (PositiveDegrees.quotientLieAction_mk d ℒ (F.toSubmodule R)
    (F.toSubmodule_antitone R) k x a)

/-- The finite-order operator retains the Leibniz rule. -/
theorem quotientLieAction_mul [IsDerivationAction L A]
    (k : ℕ) (x : L) (a b : A ⧸ F.ideal (k + 1)) :
    F.quotientLieAction d ℒ k x (a * b) =
      a * F.quotientLieAction d ℒ k x b + F.quotientLieAction d ℒ k x a * b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, quotientLieAction_mk]
  simp only [IsDerivationAction.lie_mul, map_add, map_mul, quotientLieAction_mk]

/-- At order `k`, every acting endomorphism has `(k + 1)`st power zero. -/
@[simp]
theorem quotientLieAction_pow_eq_zero (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x ^ (k + 1) = 0 := by
  rw [quotientLieAction_eq_conjAlgEquiv]
  exact (map_pow _ _ _).symm.trans <| (congrArg _ <|
    PositiveDegrees.quotientLieAction_pow_eq_zero d ℒ (F.toSubmodule R)
      (F.toSubmodule_antitone R) (F.toSubmodule_zero R) k x).trans (map_zero _)

/-- Every finite-order acting endomorphism is nilpotent. -/
theorem isNilpotent_quotientLieAction (k : ℕ) (x : L) :
    IsNilpotent (F.quotientLieAction d ℒ k x) :=
  ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩

/-- Quotient-ring transitions intertwine the coefficient representations. -/
@[simp]
theorem factor_quotientLieAction {k l : ℕ} (h : k ≤ l) (x : L)
    (q : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.quotientLieAction d ℒ l x q) =
        F.quotientLieAction d ℒ k x
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end Quotient

section Truncated

variable [GradedLieAlgebra ℒ]

/-- The representation of the order-`k` Lie truncation on the matching coefficient quotient. -/
def truncatedLieAction (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ Module.End R (A ⧸ F.ideal (k + 1)) :=
  ((Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).conjAlgEquiv R).toLieEquiv
    |>.toLieHom.comp
    (PositiveDegrees.truncatedLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R)
      (F.toSubmodule_zero R) k)

/-- The truncated representation is the scalar-restricted one, transported by conjugation. -/
theorem truncatedLieAction_eq_conjAlgEquiv (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedLieAction d ℒ k x =
      (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1)) :
        (A ⧸ F.toSubmodule R (k + 1)) ≃ₗ[R] A ⧸ F.ideal (k + 1)).conjAlgEquiv R
        (PositiveDegrees.truncatedLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R)
          (F.toSubmodule_zero R) k x) :=
  (rfl)

/-- The truncated representation agrees with the quotient action on Lie representatives. -/
@[simp]
theorem truncatedLieAction_mk (k : ℕ) (x : L) :
    F.truncatedLieAction d ℒ k (LieSubmodule.Quotient.mk x) =
      F.quotientLieAction d ℒ k x := by
  rw [truncatedLieAction_eq_conjAlgEquiv, PositiveDegrees.truncatedLieAction_mk,
    quotientLieAction_eq_conjAlgEquiv]

/-- The finite-order operator on a truncated Lie element retains the Leibniz rule. -/
theorem truncatedLieAction_mul [IsDerivationAction L A]
    (k : ℕ) (x : d.truncatedLie ℒ k) (a b : A ⧸ F.ideal (k + 1)) :
    F.truncatedLieAction d ℒ k x (a * b) =
      a * F.truncatedLieAction d ℒ k x b + F.truncatedLieAction d ℒ k x a * b := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedLieAction_mk]
  exact F.quotientLieAction_mul d ℒ k x a b

/-- At order `k`, every truncated-Lie endomorphism has `(k + 1)`st power zero. -/
@[simp]
theorem truncatedLieAction_pow_eq_zero (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedLieAction d ℒ k x ^ (k + 1) = 0 := by
  rw [truncatedLieAction_eq_conjAlgEquiv]
  exact (map_pow _ _ _).symm.trans <| (congrArg _ <|
    PositiveDegrees.truncatedLieAction_pow_eq_zero d ℒ (F.toSubmodule R)
      (F.toSubmodule_antitone R) (F.toSubmodule_zero R) k x).trans (map_zero _)

/-- Every truncated-Lie endomorphism on a finite coefficient quotient is nilpotent. -/
theorem isNilpotent_truncatedLieAction (k : ℕ) (x : d.truncatedLie ℒ k) :
    IsNilpotent (F.truncatedLieAction d ℒ k x) :=
  ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩

/-- Lie and coefficient truncations intertwine the coefficient representations. -/
@[simp]
theorem factor_truncatedLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (q : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.truncatedLieAction d ℒ l x q) =
        F.truncatedLieAction d ℒ k (d.truncationMap ℒ h x)
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) q) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncatedLieAction_mk, PositiveDegrees.truncationMap_mk]
  exact F.factor_quotientLieAction d ℒ h x q

end Truncated

end TauCeti.AlgFiltration
