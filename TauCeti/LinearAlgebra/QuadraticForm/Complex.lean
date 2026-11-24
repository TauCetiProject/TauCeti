/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.LinearCombination

/-!
# Scalar representation and isotropy over algebraically closed fields

Every nonzero quadratic form over an algebraically closed field represents every scalar, and every
quadratic form on a space of dimension at least two is isotropic. For a finite-dimensional
nondegenerate form, a scalar is represented exactly when it is zero or its space has positive
dimension. These results apply in every characteristic and justify omitting complex places from
local-to-global scalar-representation predicates.

In characteristic different from two, classification and isotropy hold more generally over
separably closed fields (`TauCeti.LinearAlgebra.QuadraticForm.SepClosed`); in characteristic two,
isotropy in dimension two genuinely requires algebraic rather than separable closedness, since
`X² + t Y²` is anisotropic over the separable closure of `𝔽₂(t)`.
-/

public section
noncomputable section

open Polynomial QuadraticMap

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

/-- Every quadratic form on a space of dimension at least two over an algebraically closed field
(of arbitrary characteristic) is isotropic. -/
theorem not_anisotropic_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) (h : 2 ≤ Module.finrank K W) : ¬ Q.Anisotropic := by
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  intro hQ
  let b := Module.finBasis K W
  let e₀ : W := b ⟨0, by omega⟩
  let e₁ : W := b ⟨1, by omega⟩
  have he₀ : e₀ ≠ 0 := b.ne_zero _
  have ha : Q e₀ ≠ 0 := fun h0 ↦ he₀ (hQ e₀ h0)
  let p : K[X] := C (Q e₀) * X ^ 2 + C (polar Q e₀ e₁) * X + C (Q e₁)
  have hp : p.degree = 2 := by
    dsimp only [p]
    compute_degree!
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p (by rw [hp]; decide)
  have hval : Q (t • e₀ + e₁) = 0 := by
    rw [Polynomial.IsRoot.def] at ht
    simp only [p, eval_add, eval_mul, eval_pow, eval_C, eval_X] at ht
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, smul_eq_mul, smul_eq_mul]
    linear_combination ht
  have hzero := hQ (t • e₀ + e₁) hval
  have h1 : b.repr (t • e₀ + e₁) ⟨1, by omega⟩ = 0 := by rw [hzero, map_zero, Finsupp.zero_apply]
  simp [e₀, e₁, b.repr_self] at h1

end QuadraticForm
