/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Coordinate
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Dimension

/-!
# Cartan coordinates of componentwise vertex projectives

The idempotent graded dimension of `Z e_j` has diagonal coefficients in degrees zero and
two, and edge coefficients in degree one. These are the coordinates of the graded Cartan
map for the public algebra, including its isolated-vertex dual-number factors.

The computation uses the generic graded-ideal/corner comparison and the actual signed
corner dimensions. See Huerfano--Khovanov, *A category for the adjoint representation*,
Section 3, equation (15), for the corner gradings and Section 6.1, equation (36),
for the Cartan-polynomial convention. The generic coordinate construction is in
`TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Coordinate`.
-/

public section
noncomputable section

namespace TauCeti

universe u w
variable (k : Type w) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "A" => zigzagAlgebraIntegerGrade k G

open scoped Classical in
/-- The internal-degree coefficients of a vertex projective's idempotent graded dimension. -/
theorem coeff_smulGradedDimension_zigzagAlgebraGradedProjective (i j : V) (d : ℤ) :
    ((zigzagAlgebraGradedProjective k G j).smulGradedDimension (e i)).coeff d =
      if i = j then if d = 0 ∨ d = 2 then 1 else 0
      else if G.Adj i j ∧ d = 1 then 1 else 0 := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  rw [GradedModuleCat.coeff_smulGradedDimension_ofIdeal_span_singleton
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
    (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G j)]
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    congrArg (Nat.cast : ℕ → ℤ)
      (finrank_cornerSubmodule_zigzagAlgebra_inf_integerGrade k G i j d)

open scoped Classical in
/-- The vertex-projective Cartan coordinate is `1 + q²` on the diagonal and `q` on an edge. -/
theorem smulGradedDimension_zigzagAlgebraGradedProjective (i j : V) :
    (zigzagAlgebraGradedProjective k G j).smulGradedDimension (e i) =
      if i = j then 1 + LaurentPolynomial.T 2
      else if G.Adj i j then LaurentPolynomial.T 1 else 0 := by
  apply LaurentPolynomial.ext
  intro d
  rw [coeff_smulGradedDimension_zigzagAlgebraGradedProjective]
  have hc1 : (1 : LaurentPolynomial ℤ).coeff d = if d = 0 then 1 else 0 := by
    simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, eq_comm]
  have hcT (n : ℤ) : (LaurentPolynomial.T n : LaurentPolynomial ℤ).coeff d =
      if d = n then 1 else 0 := by
    simpa only [eq_comm] using (LaurentPolynomial.T_apply (R := ℤ) d n)
  by_cases hij : i = j
  · subst j
    have hcadd : (1 + LaurentPolynomial.T 2 : LaurentPolynomial ℤ).coeff d =
        (if d = 0 then 1 else 0) + if d = 2 then 1 else 0 := by
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hc1, hcT]
    have hrhs : (if i = i then (1 + LaurentPolynomial.T 2 : LaurentPolynomial ℤ)
        else if G.Adj i i then LaurentPolynomial.T 1 else 0) = 1 + LaurentPolynomial.T 2 := by
      rw [ite_eq_left rfl]
    rw [hrhs, hcadd]
    by_cases h0 : d = 0
    · subst d
      simp
    · by_cases h2 : d = 2
      · subst d
        simp
      · simp [h0, h2]
  · rw [ite_eq_right hij]
    by_cases h : G.Adj i j
    · rw [ite_eq_right hij, ite_eq_left h, hcT]
      simp only [h, true_and]
    · rw [ite_eq_right hij, ite_eq_right h]
      simp only [h, false_and, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

open scoped Classical in
/-- The graded Cartan map has diagonal coordinate `1 + q²`, edge coordinate `q`, and zero
otherwise, for the public algebra even at isolated vertices. -/
theorem gradedIdempotentCoordinate_gradedCartanMap_zigzagAlgebraGradedProjectiveClass
    (i j : V) :
    gradedIdempotentCoordinate (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
        (gradedCartanMap A (zigzagAlgebraGradedProjectiveClass k G j)) =
      if i = j then 1 + LaurentPolynomial.T 2
      else if G.Adj i j then LaurentPolynomial.T 1 else 0 := by
  rw [zigzagAlgebraGradedProjectiveClass_def, gradedCartanMap_of,
    gradedIdempotentCoordinate_of, smulGradedDimension_zigzagAlgebraGradedProjective]

end TauCeti
