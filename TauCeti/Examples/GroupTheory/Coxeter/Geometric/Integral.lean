/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Geometric.Integral

/-!
# Integral geometric realizations in rank one and two

Run `CoxeterSystem.reflectionRepresentation` over `ℤ` on three matrices. In rank one the matrix
`[2]` gives `s₀ e₀ = -e₀`, while `[1]` fails the Gram hypothesis and its reflection would send `1`
to `0`. For `A₂` the matrix `!![2, -1; -1, 2]` gives `s₀ e₁ = e₀ + e₁`. For the infinite dihedral
group, a Coxeter matrix on `Fin 2` with off-diagonal entry `0` (standing for `∞`), the degenerate
matrix `!![2, -2; -2, 2]` is allowed, and `s₀ s₁` sends `e₀` to `3 e₀ + 2 e₁`. Each Gram hypothesis
is checked in its own example; the reflection examples take it as a hypothesis, which by proof
irrelevance loses nothing.
-/

public section

open Real

/-- The matrix `[2]` satisfies the Gram hypothesis in rank one. -/
example (i j : Fin 1) :
    algebraMap ℤ ℝ (!![2] i j) =
      2 * (CoxeterMatrix.A 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  fin_cases i; fin_cases j
  simp

/-- In rank one the integral simple reflection `s₀` of `[2]` sends `e₀` to `-e₀`. -/
example (hA : ∀ i j : Fin 1, algebraMap ℤ ℝ (!![2] i j) =
      2 * (CoxeterMatrix.A 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    (CoxeterMatrix.A 1).toCoxeterSystem.reflectionRepresentation (algebraMap ℤ ℝ).injective_int
        hA ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) (Finsupp.single 0 1) =
      -Finsupp.single 0 1 :=
  CoxeterSystem.reflectionRepresentation_simple_single_self _ _ hA 0

/-- The matrix `[1]` fails the Gram hypothesis of rank one. -/
example :
    ¬ ∀ i j : Fin 1, algebraMap ℤ ℝ (!![1] i j) =
      2 * (CoxeterMatrix.A 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  intro h
  have := h 0 0
  simp at this

/-- The purported reflection of `[1]` sends the basis vector to `0`. -/
example :
    Module.preReflection (Finsupp.single 0 1) (Finsupp.linearCombination ℤ (!![1] 0))
      (Finsupp.single (0 : Fin 1) (1 : ℤ)) = 0 := by
  simp [Module.preReflection_apply]

/-- The Cartan matrix `!![2, -1; -1, 2]` satisfies the Gram hypothesis of `A₂`. -/
example (i j : Fin 2) :
    algebraMap ℤ ℝ (!![2, -1; -1, 2] i j) =
      2 * (CoxeterMatrix.I 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.I, cos_pi_div_three]

/-- In `A₂` the integral simple reflection `s₀` sends `e₁` to `e₀ + e₁`. -/
example (hA : ∀ i j : Fin 2, algebraMap ℤ ℝ (!![2, -1; -1, 2] i j) =
      2 * (CoxeterMatrix.I 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    (CoxeterMatrix.I 1).toCoxeterSystem.reflectionRepresentation (algebraMap ℤ ℝ).injective_int
        hA ((CoxeterMatrix.I 1).toCoxeterSystem.simple 0) (Finsupp.single 1 1) =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  rw [CoxeterSystem.reflectionRepresentation_simple_apply]
  simp [sub_eq_add_neg, add_comm]

/-- The degenerate matrix `!![2, -2; -2, 2]` satisfies the Gram hypothesis of the infinite
dihedral group, the Coxeter matrix on `Fin 2` whose off-diagonal entry is `0`, standing for `∞`. -/
example (M : CoxeterMatrix (Fin 2)) (hM : M 0 1 = 0) (i j : Fin 2) :
    algebraMap ℤ ℝ (!![2, -2; -2, 2] i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  have hM' : M 1 0 = 0 := M.symmetric 0 1 ▸ hM
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.geometricForm_single_single, hM, hM']

/-- For the degenerate infinite dihedral matrix `!![2, -2; -2, 2]`, the element `s₀ s₁` sends
`e₀` to `3 e₀ + 2 e₁`; no determinant condition is needed for the realization. -/
example (M : CoxeterMatrix (Fin 2))
    (hA : ∀ i j : Fin 2, algebraMap ℤ ℝ (!![2, -2; -2, 2] i j) =
      2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    M.toCoxeterSystem.reflectionRepresentation (algebraMap ℤ ℝ).injective_int hA
        (M.toCoxeterSystem.simple 0 * M.toCoxeterSystem.simple 1) (Finsupp.single 0 1) =
      Finsupp.single 0 3 + Finsupp.single 1 2 := by
  rw [map_mul, mul_apply_eq_comp, CoxeterSystem.reflectionRepresentation_simple_apply,
    CoxeterSystem.reflectionRepresentation_simple_apply]
  ext k
  fin_cases k <;> simp
