/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Scalar representation over algebraically closed fields

Every nonzero quadratic form over an algebraically closed field represents every scalar.
For a finite-dimensional nondegenerate form, a scalar is represented exactly when it is zero or
its space has positive dimension. These results apply in every characteristic and justify
omitting complex places from local-to-global scalar-representation predicates.

The classification and isotropy results in characteristic different from two hold more generally
over separably closed fields and live in `TauCeti.LinearAlgebra.QuadraticForm.SepClosed`.
-/

public section
noncomputable section

open QuadraticMap

namespace QuadraticForm

/-- A nonzero quadratic form over an algebraically closed field represents every scalar. -/
theorem represents_of_ne_zero_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} (hQ : Q ≠ 0) (a : K) : QuadraticMap.Represents Q a := by
  obtain ⟨v, hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra! h
    exact hQ (QuadraticMap.ext h)
  obtain ⟨t, ht⟩ := IsAlgClosed.isSquare (a / Q v)
  exact (QuadraticMap.represents_iff Q a).2
    ⟨t • v, by rw [QuadraticMap.map_smul, ← ht, smul_eq_mul, div_mul_cancel₀ _ hv]⟩

/-- A regular quadratic form on a space of positive rank over an algebraically closed field
represents every scalar. The positive-rank hypothesis supplies nontriviality directly, so no
finite-dimensionality typeclass assumption is needed. -/
theorem represents_of_finrank_pos_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (hW : 0 < Module.finrank K W) (a : K) :
    Q.Represents a := by
  let _ : Nontrivial W := Module.nontrivial_of_finrank_pos hW
  exact Q.represents_of_ne_zero_of_isAlgClosed hQ.ne_zero a

/-- A regular quadratic form over an algebraically closed field represents a scalar exactly when
the scalar is zero or the underlying space has positive dimension. -/
@[simp]
theorem represents_iff_eq_zero_or_finrank_pos_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (a : K) :
    Q.Represents a ↔ a = 0 ∨ 0 < Module.finrank K W := by
  constructor
  · rw [QuadraticMap.represents_iff, Set.mem_range]
    rintro ⟨x, hx⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr <| Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, fun h ↦ by
        subst x
        exact ha (by simpa using hx.symm)⟩
  · rintro (rfl | hW)
    · exact QuadraticMap.represents_zero Q
    · exact Q.represents_of_finrank_pos_of_isAlgClosed hQ hW a

end QuadraticForm
