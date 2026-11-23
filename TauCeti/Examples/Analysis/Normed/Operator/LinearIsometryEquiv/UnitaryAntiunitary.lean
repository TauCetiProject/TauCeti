/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.UnitaryAntiunitary

/-!
# Checks for the unitary–antiunitary group

On `ℂ` complex conjugation is an odd element of `UA(ℂ)` which fixes the only ray without being a
scalar, so `PUA(ℂ)` does not act faithfully on rays and the ray map does not determine the grade:
the hypothesis `1 < Module.rank ℂ H` of `TauCeti.unitaryAntiunitary.ker_toPermHom` cannot be
dropped. On `ℂ²` that hypothesis holds, and the kernel of the ray action is the scalar circle.
-/

public section

open scoped LinearAlgebra.Projectivization

open TauCeti unitaryAntiunitary

/-- Complex conjugation is an odd element of `UA(ℂ)`. -/
example : grade ℂ (ofConjLinearIsometryEquiv ℂ (starₗᵢ ℂ)) = Multiplicative.ofAdd 1 := by
  simp

/-- Complex conjugation fixes the only ray of `ℂ`. -/
example (p : ℙ ℂ ℂ) : ofConjLinearIsometryEquiv ℂ (starₗᵢ ℂ) • p = p := by
  induction p using Projectivization.ind with | _ v hv =>
  rw [smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨star v / v, by simp [div_mul_cancel₀ _ hv]⟩

/-- Complex conjugation is not a scalar of `UA(ℂ)`. -/
example : ofConjLinearIsometryEquiv ℂ (starₗᵢ ℂ) ∉ (scalar ℂ).range := by
  rintro ⟨z, hz⟩
  have h := congrArg (grade ℂ) hz
  rw [grade_scalar, grade_ofConjLinearIsometryEquiv] at h
  exact absurd h (by decide)

/-- On `ℂ²` the kernel of the action of `UA(ℂ²)` on rays is the scalar circle. -/
example : (MulAction.toPermHom (unitaryAntiunitary (EuclideanSpace ℂ (Fin 2)))
    (ℙ ℂ (EuclideanSpace ℂ (Fin 2)))).ker = (scalar (EuclideanSpace ℂ (Fin 2))).range :=
  ker_toPermHom (Module.one_lt_rank_of_one_lt_finrank (by simp))
