/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.FiniteEtaleSplit
import Mathlib.NumberTheory.Padics.Complex
import TauCeti.RingTheory.AdjoinRoot.Separable

/-!
# Tests for rings without nonsplit finite étale covers

Separably closed fields, such as `ℂ_[p]`, their finite products, and the zero ring have no
nonsplit finite étale covers; `ℚ` has one, `ℚ[X] ⧸ (X ^ 2 - 2)`. Over a nonzero ring the zero
algebra is totally split but has no section, so the section criterion must be restricted to
faithfully flat algebras.
-/

open Polynomial

namespace TauCeti

/-- *test_isSepClosed*: for a field the condition is separable closedness. -/
example (K : Type) [Field K] : IsFiniteEtaleSplit K ↔ IsSepClosed K :=
  isFiniteEtaleSplit_iff_isSepClosed K

/-- *test_Cp*: `ℂ_[p]` is algebraically closed, so it has no nonsplit finite étale covers. -/
example (p : ℕ) [Fact p.Prime] : IsFiniteEtaleSplit ℂ_[p] :=
  inferInstance

/-- *test_zero*: the zero ring has no nonsplit finite étale covers. -/
example : IsFiniteEtaleSplit (ZMod 1) :=
  inferInstance

/-- *test_pi*: a product of separably closed fields has no nonsplit finite étale covers, although
its finite étale algebras may have different ranks over the two factors. -/
example (K₁ K₂ : Type) [Field K₁] [Field K₂] [IsSepClosed K₁] [IsSepClosed K₂] :
    IsFiniteEtaleSplit (K₁ × K₂) :=
  inferInstance

/-- *test_not_rat*: `X ^ 2 - 2` is separable over `ℚ` without a rational root. -/
example : ¬ IsFiniteEtaleSplit ℚ := by
  intro _
  have hs : (X ^ 2 - C (2 : ℚ)).Separable := separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  obtain ⟨r, hr⟩ := IsFiniteEtaleSplit.exists_root (monic_X_pow_sub_C _ (by norm_num))
    (by rw [natDegree_X_pow_sub_C]; norm_num) (separable_iff_isUnit_mk_derivative.mp hs)
  have hr' : r ^ 2 - 2 = 0 := by simpa using hr
  have h2 : IsSquare ((2 : ℕ) : ℚ) := ⟨r, by push_cast; linear_combination -hr'⟩
  exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp h2)

/-- *test_zero_algebra_has_no_section*: over a nonzero ring the zero algebra is totally split
but has no section. -/
example (R : Type) [CommRing R] [Nontrivial R] :
    Algebra.IsTotallySplit R (Fin 0 → R) ∧ IsEmpty ((Fin 0 → R) →ₐ[R] R) :=
  ⟨.of_subsingleton R _, ⟨fun σ ↦ one_ne_zero <|
    (map_one σ).symm.trans ((congrArg σ (Subsingleton.elim 1 0)).trans (map_zero σ))⟩⟩

/-- *test_exists_root*: a monic polynomial of positive degree whose derivative is a unit modulo it
has a root. -/
example (R : Type) [CommRing R] [IsFiniteEtaleSplit R] (P : R[X]) (hP : P.Monic)
    (hd : 0 < P.natDegree) (hu : IsUnit (AdjoinRoot.mk P (derivative P))) : ∃ r, P.IsRoot r :=
  IsFiniteEtaleSplit.exists_root hP hd hu

end TauCeti
