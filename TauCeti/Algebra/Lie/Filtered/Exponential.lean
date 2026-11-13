/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Filtered.Algebra
public import TauCeti.Algebra.Lie.Derivation.Action
public import TauCeti.LinearAlgebra.End.Exp

/-!
# Exponentiating finite-order coefficient actions

Each element of a positively graded Lie algebra acting by filtration-raising derivations
exponentiates to an algebra automorphism of every finite coefficient quotient. The inverse
is obtained by negating the Lie element. Quotient transitions intertwine these automorphisms,
and the action depends only on the corresponding Lie truncation. The coefficient algebra
may be noncommutative, and the original derivations need not be nilpotent.

The construction uses the existing nilpotent quotient representation and
`Module.End.expAlgEquiv`. Truncation compatibility is Mathlib's
`Module.End.commute_exp_left_of_commute`, applied to the quotient transition.

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

variable [Algebra ℚ A]

/-- The exponential of the order-`k` coefficient representation, as an algebra automorphism. -/
noncomputable def quotientExpLieAction (k : ℕ) (x : L) :
    (A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1)) :=
  (F.quotientLieAction d ℒ k x).expAlgEquiv (F.quotientLieAction_mul d ℒ k x)
    ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩

/-- Evaluation of the finite-order exponential is the finite endomorphism exponential. -/
@[simp]
theorem quotientExpLieAction_apply (k : ℕ) (x : L) (a : A ⧸ F.ideal (k + 1)) :
    F.quotientExpLieAction d ℒ k x a = IsNilpotent.exp (F.quotientLieAction d ℒ k x) a :=
  Module.End.expAlgEquiv_apply _ _ _ a

/-- Negating the Lie element gives the inverse coefficient automorphism. -/
@[simp]
theorem quotientExpLieAction_neg (k : ℕ) (x : L) :
    F.quotientExpLieAction d ℒ k (-x) = (F.quotientExpLieAction d ℒ k x).symm := by
  ext a
  apply (F.quotientExpLieAction d ℒ k x).injective
  rw [AlgEquiv.apply_symm_apply, quotientExpLieAction_apply,
    quotientExpLieAction_apply, map_neg]
  exact LinearMap.congr_fun
    (IsNilpotent.exp_mul_exp_neg_self
      ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩) a

/-- The zero Lie element acts as the identity automorphism. -/
@[simp]
theorem quotientExpLieAction_zero (k : ℕ) :
    F.quotientExpLieAction d ℒ k 0 = AlgEquiv.refl := by
  ext a
  simp [IsNilpotent.exp_zero]

/-- Coefficient truncations intertwine the finite-order exponentials. -/
theorem factor_quotientExpLieAction {k l : ℕ} (h : k ≤ l) (x : L)
    (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.quotientExpLieAction d ℒ l x a) =
        F.quotientExpLieAction d ℒ k x
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  let f := (Ideal.Quotient.factorₐ R (F.antitone (Nat.add_le_add_right h 1))).toLinearMap
  have hc : (F.quotientLieAction d ℒ k x).comp f =
      f.comp (F.quotientLieAction d ℒ l x) := by
    ext q
    exact (F.factor_quotientLieAction d ℒ h x q).symm
  simpa only [f, quotientExpLieAction_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply] using
    (LinearMap.congr_fun (Module.End.commute_exp_left_of_commute
      ⟨l + 1, F.quotientLieAction_pow_eq_zero d ℒ l x⟩
      ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩ hc) a).symm

end Decomposition

section Truncated

variable [GradedLieAlgebra ℒ] [Algebra ℚ A]

/-- Lie elements with equal order-`k` truncations induce the same coefficient automorphism. -/
theorem quotientExpLieAction_eq_of_mk_eq (k : ℕ) {x y : L}
    (h : (d.degreeIdeal ℒ k).mkQ x = (d.degreeIdeal ℒ k).mkQ y) :
    F.quotientExpLieAction d ℒ k x = F.quotientExpLieAction d ℒ k y := by
  have hm := congrArg (PositiveDegrees.truncatedLieAction d ℒ (F.toSubmodule R)
    (F.toSubmodule_antitone R) (F.toSubmodule_zero R) k) h
  simp only [LieIdeal.mkQ_apply, PositiveDegrees.truncatedLieAction_mk] at hm
  have he : F.quotientLieAction d ℒ k x = F.quotientLieAction d ℒ k y := by
    let E := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
    let Q : L →ₗ⁅R⁆ Module.End R (A ⧸ (F.ideal (k + 1)).restrictScalars R) :=
      PositiveDegrees.quotientLieAction d ℒ (F.toSubmodule R) (F.toSubmodule_antitone R) k
    have hmQ : Q x = Q y := hm
    have hq (z : L) : F.quotientLieAction d ℒ k z = E.conjAlgEquiv R (Q z) := (rfl)
    apply (E.conjAlgEquiv R).symm.injective
    rw [hq x, hq y, (E.conjAlgEquiv R).symm_apply_apply (Q x),
      (E.conjAlgEquiv R).symm_apply_apply (Q y)]
    exact hmQ
  ext a
  simp only [quotientExpLieAction_apply, he]

/-- Exponentiate an element of the Lie truncation on the matching coefficient quotient. -/
noncomputable def truncatedExpLieAction (k : ℕ) : d.truncatedLie ℒ k →
    ((A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1))) :=
  Quotient.lift (F.quotientExpLieAction d ℒ k) (fun _ _ h =>
    F.quotientExpLieAction_eq_of_mk_eq d ℒ k (Quotient.sound h))

/-- On Lie representatives, the truncated exponential is the quotient exponential. -/
@[simp]
theorem truncatedExpLieAction_mk (k : ℕ) (x : L) :
    F.truncatedExpLieAction d ℒ k (LieSubmodule.Quotient.mk x) =
      F.quotientExpLieAction d ℒ k x := (rfl)

/-- Zero in the Lie truncation acts as the identity automorphism. -/
@[simp]
theorem truncatedExpLieAction_zero (k : ℕ) :
    F.truncatedExpLieAction d ℒ k 0 = AlgEquiv.refl := by
  simpa only [Submodule.Quotient.mk_zero] using
    (F.truncatedExpLieAction_mk d ℒ k (0 : L)).trans (F.quotientExpLieAction_zero d ℒ k)

/-- Negation in the Lie truncation inverts the coefficient automorphism. -/
@[simp]
theorem truncatedExpLieAction_neg (k : ℕ) (x : d.truncatedLie ℒ k) :
    F.truncatedExpLieAction d ℒ k (-x) = (F.truncatedExpLieAction d ℒ k x).symm := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [← map_neg, LieIdeal.mkQ_apply, LieIdeal.mkQ_apply]
  simp only [truncatedExpLieAction_mk, quotientExpLieAction_neg]

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

end Truncated

end TauCeti.AlgFiltration
