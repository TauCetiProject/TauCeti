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
  [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toSubmodule R)]

/-- The finite-order Lie representation on the original coefficient quotient ring. -/
@[expose]
def quotientLieAction (k : ℕ) : L →ₗ⁅R⁆ Module.End R (A ⧸ F.ideal (k + 1)) :=
  let e := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
  (e.conjAlgEquiv R).toLieEquiv.toLieHom.comp
    (PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k)

/-- Quotient representatives are acted on by the original Lie action. -/
@[simp]
theorem quotientLieAction_mk (k : ℕ) (x : L) (a : A) :
    F.quotientLieAction d ℒ k x (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ⁅x, a⁆ := by
  change Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
    ((PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k x)
      (Submodule.Quotient.mk a)) = _
  rw [PositiveDegrees.quotientLieAction_mk]
  rfl

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
theorem quotientLieAction_pow_eq_zero (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x ^ (k + 1) = 0 := by
  let E := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
  let Q : Module.End R (A ⧸ (F.ideal (k + 1)).restrictScalars R) :=
    PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k x
  change (E.conjAlgEquiv R Q ^ (k + 1)) = 0
  calc
    E.conjAlgEquiv R Q ^ (k + 1) = E.conjAlgEquiv R (Q ^ (k + 1)) := by
      rw [map_pow]
    _ = E.conjAlgEquiv R 0 := congrArg _ (PositiveDegrees.quotientLieAction_pow_eq_zero
      d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) (F.toSubmodule_zero R) k x)
    _ = 0 := map_zero _

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

end TauCeti.AlgFiltration
