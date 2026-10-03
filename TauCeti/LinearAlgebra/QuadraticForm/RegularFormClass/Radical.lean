/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The regular quotient class of a quadratic form

The quotient of a quadratic space by its radical is regular when `2` is invertible.
Its isometry class, together with the dimension of the radical, determines the original
finite-dimensional quadratic space up to isometry. This makes the regular isometry-class API
available for singular forms without choosing a complement to the radical.

The quotient is Mathlib's `QuadraticMap.lift`. The decomposition into a radical and a regular
space is the first part of T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), I §4.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The isometry class of the regular quadratic form on the quotient by the radical. -/
noncomputable def regularQuotientClass (Q : QuadraticForm K V) : RegularFormClass K :=
  formClass (Q.lift Q.radical le_rfl) Q.nondegenerate_lift_radical

/-- The regular quotient class is the class of Mathlib's quotient form. -/
theorem regularQuotientClass_def (Q : QuadraticForm K V) :
    regularQuotientClass Q = formClass (Q.lift Q.radical le_rfl) Q.nondegenerate_lift_radical :=
  (rfl)

/-- The regular quotient rank and radical dimension add up to the dimension of the space. -/
theorem rank_regularQuotientClass_add_finrank_radical (Q : QuadraticForm K V) :
    RegularFormClass.rank (regularQuotientClass Q) + Module.finrank K Q.radical =
      Module.finrank K V := by
  rw [regularQuotientClass_def, rank_formClass]
  exact Q.radical.finrank_quotient_add_finrank

/-- A regular form has its usual isometry class as its regular quotient class. -/
@[simp]
theorem regularQuotientClass_eq_formClass (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    regularQuotientClass Q = formClass Q hQ := by
  rw [regularQuotientClass_def, formClass_eq_iff]
  refine ⟨{
    toLinearEquiv := Q.radical.quotEquivOfEqBot hQ.radical_eq_bot
    map_app' := ?_ }⟩
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The zero form has trivial regular quotient class, in every finite dimension. -/
@[simp]
theorem regularQuotientClass_zero :
    regularQuotientClass (0 : QuadraticForm K V) = 0 := by
  apply RegularFormClass.rank_eq_zero_iff.mp
  have h := rank_regularQuotientClass_add_finrank_radical (0 : QuadraticForm K V)
  have hr : (0 : QuadraticForm K V).radical = ⊤ := by
    ext x
    simp [QuadraticMap.mem_radical_iff']
  rw [hr, finrank_top] at h
  omega

/-- Isometry preserves the class of the regular quotient. -/
theorem regularQuotientClass_eq_of_equivalent {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (h : Q.Equivalent Q') : regularQuotientClass Q = regularQuotientClass Q' := by
  rw [regularQuotientClass_def, regularQuotientClass_def, formClass_eq_iff]
  exact h.lift_radical

/-- The regular quotient class of an orthogonal product is the sum of the quotient classes. -/
@[simp]
theorem regularQuotientClass_prod (Q : QuadraticForm K V) (Q' : QuadraticForm K W) :
    regularQuotientClass (Q.prod Q') = regularQuotientClass Q + regularQuotientClass Q' := by
  rw [regularQuotientClass_def, regularQuotientClass_def, regularQuotientClass_def,
    ← formClass_prod, formClass_eq_iff]
  let f := Q.radical.mkQ.prodMap Q'.radical.mkQ
  have hf : Function.Surjective f :=
    Q.radical.mkQ_surjective.prodMap Q'.radical.mkQ_surjective
  have hr : (Q.prod Q').radical = f.ker := by
    simp [f, QuadraticMap.radical_prod, LinearMap.ker_prodMap, Submodule.ker_mkQ]
  refine ⟨{
    toLinearEquiv := (Submodule.quotEquivOfEq _ _ hr).trans (f.quotKerEquivOfSurjective hf)
    map_app' := ?_ }⟩
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp [f]

/-- Adjoining a zero summand preserves the regular quotient class, also for singular forms. -/
theorem regularQuotientClass_zero_prod (Q : QuadraticForm K W) :
    regularQuotientClass ((0 : QuadraticForm K V).prod Q) = regularQuotientClass Q := by
  rw [regularQuotientClass_prod, regularQuotientClass_zero, zero_add]

/-- Two quadratic forms are isometric exactly when their radical dimensions and regular
quotient classes agree. No regularity is required of either original form. -/
theorem equivalent_iff_finrank_radical_eq_and_regularQuotientClass_eq
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W) :
    Q.Equivalent Q' ↔ Module.finrank K Q.radical = Module.finrank K Q'.radical ∧
      regularQuotientClass Q = regularQuotientClass Q' := by
  refine ⟨fun h => ⟨h.rank_radical_eq, regularQuotientClass_eq_of_equivalent h⟩, ?_⟩
  rintro ⟨hdim, hclass⟩
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim
  have he : (0 : QuadraticForm K Q.radical).Equivalent (0 : QuadraticForm K Q'.radical) :=
    ⟨{ toLinearEquiv := e, map_app' := fun _ => by simp }⟩
  rw [regularQuotientClass_def, regularQuotientClass_def, formClass_eq_iff] at hclass
  exact Q.equivalent_zero_prod_lift_radical.trans
    ((he.prod hclass).trans Q'.equivalent_zero_prod_lift_radical.symm)

end TauCeti
