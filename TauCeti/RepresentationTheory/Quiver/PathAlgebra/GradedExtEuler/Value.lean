/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Admissible
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic

import Mathlib.Tactic.LinearCombination

/-!
# The q-Euler values of graded quiver vertex simples

For the path-length grading on a path algebra, the first-arrow resolution computes

`χ_q(Sᵢ, Y) = gdim(eᵢ Y) - q⁻¹ ∑_{a : i ⟶ j} gdim(eⱼ Y)`.

In particular, `χ_q(Sᵢ, Sⱼ) = δᵢⱼ - q⁻¹ # {a : i ⟶ j}`. The inverse power of `q`
comes from the shift by one of the source projectives in the arrow kernel: the form is
q-antilinear in its first variable. The general formula needs a finite quiver with finitely many
arrows and a finite-dimensional target. The simple-pair specialization uses finite-dimensionality
of the path algebra to obtain finite arrow sets and finite-dimensional vertex simples.

These are object-level values, computed with explicit Euler-admissibility witnesses. They
supply the entries for comparing the graded categorical pairing with the graded quiver form.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the first-arrow resolution and Euler form.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the
  q-antilinear/q-linear convention.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe u v w t

section Projective

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- A vertex projective evaluates the q-Euler characteristic at its idempotent graded
dimension, for any finite-dimensional graded target. -/
@[simp]
theorem gradedExtEuler_gradedVertexProjective (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y]
    (h : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexProjective k Q i) Y) :
    gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h =
      Y.smulGradedDimension (vertexIdempotent k i) := by
  let _ := integerGradedAlgebra k Q
  -- Generalize the witness before rewriting its source object, which occurs in its type.
  revert h
  rw [gradedVertexProjective_def]
  intro h
  exact gradedExtEuler_ofIdeal_span_singleton
    (vertexIdempotent_mul_self i : IsIdempotentElem (vertexIdempotent k i : pathAlgebra k Q))
    (vertexIdempotent_mem_integerGrade_zero k Q i)
    (isHomogeneous_span_vertexIdempotent k Q i) Y h

end Projective

section Values

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- The q-Euler value of the arrow kernel is `q⁻¹` times the sum of the idempotent graded
dimensions at the targets of the arrows. Each arrow is counted separately. -/
theorem gradedExtEuler_gradedArrowSum (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y]
    (h : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedArrowSum k Q i) Y) :
    gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h =
      T (-1) * ∑ a : (j : Q) × (i ⟶ j), Y.smulGradedDimension (vertexIdempotent k a.1) := by
  classical
  let _ := integerGradedAlgebra k Q
  let hP (j : Q) := isGradedEulerAdmissible_gradedVertexProjective.{u, v, w, t} k Q j Y
  have hshift (j : Q) : IsGradedEulerAdmissible.{t} k
      (GradedModuleCat.shift (integerGrade k Q))
      ((gradedVertexProjective k Q j).shiftObj 1) Y := by
    simpa only [GradedModuleCat.shift_functor_obj] using (hP j).shiftSource
  rw [gradedExtEuler_directSumObj _ _ Y h (fun a ↦ hshift a.1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hval := gradedExtEuler_shiftSource (hP a.1)
  rw [gradedExtEuler_gradedVertexProjective k Q a.1 Y (hP a.1)] at hval
  simpa only [GradedModuleCat.shift_functor_obj] using hval

/-- **The graded first-arrow Euler formula.** Pairing a vertex simple against a finite-dimensional
graded module subtracts the shifted outgoing-arrow coordinates from its own vertex coordinate. -/
theorem gradedExtEuler_gradedVertexSimple (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y]
    (h : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) Y) :
    gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h =
      Y.smulGradedDimension (vertexIdempotent k i) -
        T (-1) * ∑ a : (j : Q) × (i ⟶ j), Y.smulGradedDimension (vertexIdempotent k a.1) := by
  let _ := integerGradedAlgebra k Q
  let hA := isGradedEulerAdmissible_gradedArrowSum.{u, v, w, t} k Q i Y
  have hs := shortExact_gradedVertexSimpleResolution k Q i
  rw [gradedVertexSimpleResolution_def] at hs
  have hadd := gradedExtEuler_shortExact₁ hs Y hA h
  have hval := gradedExtEuler_gradedVertexProjective k Q i Y (hA.of_shortExact₂' hs h)
  rw [gradedExtEuler_gradedArrowSum] at hadd
  linear_combination hval - hadd

end Values

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- **The q-Euler matrix entries in the graded vertex-simple basis** are
`δᵢⱼ - q⁻¹ # {arrows i ⟶ j}`. Rows are source vertices and columns are target vertices. -/
@[simp]
theorem gradedExtEuler_gradedVertexSimple_gradedVertexSimple
    [FiniteDimensional k (pathAlgebra k Q)] [DecidableEq Q] (i j : Q)
    (h : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) (gradedVertexSimple k Q j)) :
    gradedExtEuler k (GradedModuleCat.shift (integerGrade k Q)) h =
      (if i = j then 1 else 0) - T (-1) * (Nat.card (i ⟶ j) : LaurentPolynomial ℤ) := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  let _ (a b : Q) : Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance a b
  let _ (a b : Q) := Fintype.ofFinite (a ⟶ b)
  let _ : Module.Finite (pathAlgebra k Q) (gradedVertexSimple k Q j) :=
    gradedFiniteModules_iff.1 (gradedFiniteModules_gradedVertexSimple k Q j)
  let _ : Module.Finite k (gradedVertexSimple k Q j) := Module.Finite.trans (pathAlgebra k Q) _
  have hdim (l : Q) :
      (gradedVertexSimple k Q j).smulGradedDimension (vertexIdempotent k l) =
        if l = j then 1 else 0 := by
    simpa only [gradedVertexSimple_def] using smulGradedDimension_gradedIdempotentHead
      (fun _ ↦ integerGrade_eq_bot_of_neg k Q)
      (completeOrthogonalIdempotents_vertexIdempotent k Q).toOrthogonalIdempotents
      (vertexIdempotent_mem_integerGrade_zero k Q)
      (integerGrade_zero_eq_span_range_vertexIdempotent k Q).le l j (vertexIdempotent_ne_zero j)
  rw [gradedExtEuler_gradedVertexSimple]
  simp_rw [hdim]
  have hsum : (∑ a : (l : Q) × (i ⟶ l),
      (if a.1 = j then 1 else 0 : LaurentPolynomial ℤ)) = Nat.card (i ⟶ j) := by
    have hinner (l : Q) :
        (∑ _a : i ⟶ l, (if l = j then 1 else 0 : LaurentPolynomial ℤ)) =
          if l = j then Fintype.card (i ⟶ l) else 0 := by
      by_cases hl : l = j <;> simp [hl]
    rw [Fintype.sum_sigma]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  rw [hsum]

end TauCeti.PathAlgebra
