/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Filtered.Algebra
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Exponentiating finite-order coefficient actions

Each element of a positively graded Lie algebra acting by filtration-raising derivations
exponentiates to an algebra automorphism of every finite coefficient quotient. The inverse
is obtained by negating the Lie element. Quotient transitions intertwine these automorphisms and
their inverses, and the action depends only on the corresponding Lie truncation. The coefficient
algebra may be noncommutative, and the original derivations need not be nilpotent. The
coefficient algebra must be a `ℚ`-module, `[Module ℚ A]`, to divide by factorials; the base ring
`R` can be any commutative ring independently of this rational structure.

`AlgFiltration.quotientExpLieAction` and `AlgFiltration.truncatedExpLieAction` are obtained by
applying `Module.End.expAlgEquiv` to `AlgFiltration.quotientLieAction` and
`AlgFiltration.truncatedLieAction`. Compatibility with quotient transitions is naturality of the
exponential, `Module.End.map_exp`, applied to the transition map.

Adapted from `Mei/Algebra/Lie/Filtered/Exponential.lean` in
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
  [IsFiltrationRaising d ℒ (F.toSubmodule R)] [IsDerivationAction L A]

section Decomposition

variable [DirectSum.Decomposition ℒ]

-- Division by factorials uses the coefficient algebra's rational structure. The base ring `R`
-- may be an arbitrary commutative ring, independently of this rational module structure.
variable [Module ℚ A]

/-- The exponential of the order-`k` coefficient representation, as an algebra automorphism. -/
noncomputable def quotientExpLieAction (k : ℕ) (x : L) :
    (A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1)) :=
  (F.quotientLieAction d ℒ k x).expAlgEquiv (F.quotientLieAction_mul d ℒ k x)
    (F.isNilpotent_quotientLieAction d ℒ k x)

/-- The quotient exponential has the finite endomorphism exponential as its underlying map. -/
@[simp]
theorem quotientExpLieAction_toLinearMap (k : ℕ) (x : L) :
    (F.quotientExpLieAction d ℒ k x : _ →ₗ[R] _) =
      IsNilpotent.exp (F.quotientLieAction d ℒ k x) :=
  Module.End.expAlgEquiv_toLinearMap _ _ _

/-- Evaluation of the finite-order exponential is the finite endomorphism exponential. -/
theorem quotientExpLieAction_apply (k : ℕ) (x : L) (a : A ⧸ F.ideal (k + 1)) :
    F.quotientExpLieAction d ℒ k x a = IsNilpotent.exp (F.quotientLieAction d ℒ k x) a :=
  Module.End.expAlgEquiv_apply _ _ _ a

/-- Negating the Lie element gives the inverse coefficient automorphism. -/
@[simp]
theorem quotientExpLieAction_neg (k : ℕ) (x : L) :
    F.quotientExpLieAction d ℒ k (-x) = (F.quotientExpLieAction d ℒ k x).symm := by
  simp only [quotientExpLieAction, map_neg]
  exact (Module.End.expAlgEquiv_symm _ _ _).symm

/-- The inverse finite-order exponential evaluates as the exponential of the negated action. -/
theorem quotientExpLieAction_symm_apply (k : ℕ) (x : L) (a : A ⧸ F.ideal (k + 1)) :
    (F.quotientExpLieAction d ℒ k x).symm a =
      IsNilpotent.exp (-F.quotientLieAction d ℒ k x) a :=
  Module.End.expAlgEquiv_symm_apply _ _ _ a

/-- The zero Lie element acts as the identity automorphism. -/
@[simp]
theorem quotientExpLieAction_zero (k : ℕ) :
    F.quotientExpLieAction d ℒ k 0 = AlgEquiv.refl := by
  simp [quotientExpLieAction]

/-- Coefficient truncations intertwine the finite-order exponentials. -/
@[simp]
theorem factor_quotientExpLieAction {k l : ℕ} (h : k ≤ l) (x : L)
    (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.quotientExpLieAction d ℒ l x a) =
        F.quotientExpLieAction d ℒ k x
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  rw [quotientExpLieAction_apply, quotientExpLieAction_apply]
  exact Module.End.map_exp _ (F.isNilpotent_quotientLieAction d ℒ l x)
    (F.isNilpotent_quotientLieAction d ℒ k x) _ (F.factor_quotientLieAction d ℒ h x) a

/-- Coefficient truncations intertwine the inverse finite-order exponentials. -/
@[simp]
theorem factor_quotientExpLieAction_symm {k l : ℕ} (h : k ≤ l) (x : L)
    (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      ((F.quotientExpLieAction d ℒ l x).symm a) =
        (F.quotientExpLieAction d ℒ k x).symm
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  rw [← quotientExpLieAction_neg F d ℒ l x, ← quotientExpLieAction_neg F d ℒ k x]
  exact F.factor_quotientExpLieAction d ℒ h (-x) a

end Decomposition

section Truncated

variable [GradedLieAlgebra ℒ] [Module ℚ A]

/-- Exponentiate an element of the Lie truncation on the matching coefficient quotient. -/
noncomputable def truncatedExpLieAction (k : ℕ) (x : d.truncatedLie ℒ k) :
    (A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1)) :=
  (F.truncatedLieAction d ℒ k x).expAlgEquiv (F.truncatedLieAction_mul d ℒ k x)
    (F.isNilpotent_truncatedLieAction d ℒ k x)

/-- The truncated exponential has the finite endomorphism exponential as its underlying map. -/
@[simp]
theorem truncatedExpLieAction_toLinearMap (k : ℕ) (x : d.truncatedLie ℒ k) :
    (F.truncatedExpLieAction d ℒ k x : _ →ₗ[R] _) =
      IsNilpotent.exp (F.truncatedLieAction d ℒ k x) :=
  Module.End.expAlgEquiv_toLinearMap _ _ _

/-- The truncated exponential evaluates as the finite endomorphism exponential. -/
theorem truncatedExpLieAction_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : A ⧸ F.ideal (k + 1)) :
    F.truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (F.truncatedLieAction d ℒ k x) a :=
  Module.End.expAlgEquiv_apply _ _ _ a

/-- On Lie representatives, the truncated exponential is the quotient exponential. -/
@[simp]
theorem truncatedExpLieAction_mk (k : ℕ) (x : L) :
    F.truncatedExpLieAction d ℒ k (LieSubmodule.Quotient.mk x) =
      F.quotientExpLieAction d ℒ k x := by
  simp [truncatedExpLieAction, quotientExpLieAction]

/-- Zero in the Lie truncation acts as the identity automorphism. -/
@[simp]
theorem truncatedExpLieAction_zero (k : ℕ) :
    F.truncatedExpLieAction d ℒ k 0 = AlgEquiv.refl := by
  rw [← map_zero (d.degreeIdeal ℒ k).mkQ, LieIdeal.mkQ_apply, truncatedExpLieAction_mk,
    quotientExpLieAction_zero]

/-- Negation in the Lie truncation inverts the coefficient automorphism. -/
@[simp]
theorem truncatedExpLieAction_neg (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedExpLieAction d ℒ k (-x) = (F.truncatedExpLieAction d ℒ k x).symm := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [← map_neg, LieIdeal.mkQ_apply, LieIdeal.mkQ_apply]
  simp only [truncatedExpLieAction_mk, quotientExpLieAction_neg]

/-- The inverse truncated exponential evaluates as the exponential of the negated action. -/
theorem truncatedExpLieAction_symm_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : A ⧸ F.ideal (k + 1)) :
    (F.truncatedExpLieAction d ℒ k x).symm a =
      IsNilpotent.exp (-F.truncatedLieAction d ℒ k x) a :=
  Module.End.expAlgEquiv_symm_apply _ _ _ a

/-- Lie truncation and coefficient truncation intertwine the exponential actions. -/
@[simp]
theorem factor_truncatedExpLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.truncatedExpLieAction d ℒ l x a) =
        F.truncatedExpLieAction d ℒ k (d.truncationMap ℒ h x)
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, truncatedExpLieAction_mk, PositiveDegrees.truncationMap_mk]
  exact F.factor_quotientExpLieAction d ℒ h x a

/-- Lie truncation and coefficient truncation intertwine the inverse exponential actions. -/
@[simp]
theorem factor_truncatedExpLieAction_symm {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      ((F.truncatedExpLieAction d ℒ l x).symm a) =
        (F.truncatedExpLieAction d ℒ k (d.truncationMap ℒ h x)).symm
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  rw [← truncatedExpLieAction_neg F d ℒ l x, ← truncatedExpLieAction_neg, ← map_neg]
  exact F.factor_truncatedExpLieAction d ℒ h (-x) a

end Truncated

end TauCeti.AlgFiltration
