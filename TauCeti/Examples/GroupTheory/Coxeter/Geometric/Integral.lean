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
`[2]` gives `x ↦ -x`, while `[1]` fails the Gram hypothesis and its reflection would send `1` to
`0`. For `A₂` the matrix `!![2, -1; -1, 2]` gives `s₀ e₁ = e₀ + e₁`. For the infinite dihedral
group the degenerate matrix `!![2, -2; -2, 2]` is allowed, and `s₀ s₁` sends `e₀` to `3 e₀ + 2 e₁`.
-/

public section

open Real

namespace TauCeti

/-- The Coxeter matrix of the infinite dihedral group, whose off-diagonal entry `0` stands for
`∞`. -/
def infiniteDihedralCoxeterMatrix : CoxeterMatrix (Fin 2) where
  M := Matrix.of fun i j ↦ if i = j then 1 else 0
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

/-- The matrix `[2]` satisfies the Gram hypothesis in rank one. -/
theorem rankOne_gram (i j : Fin 1) :
    algebraMap ℤ ℝ (!![2] i j) =
      2 * (CoxeterMatrix.A 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  fin_cases i; fin_cases j
  simp

/-- In rank one the integral reflection of `[2]` is `x ↦ -x`, matching `c (-1) = -1 = ρ(s) c(1)`
for the real reflection. -/
example :
    (CoxeterMatrix.A 1).toCoxeterSystem.reflectionRepresentation (algebraMap ℤ ℝ).injective_int
        rankOne_gram ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) (Finsupp.single 0 1) =
      -Finsupp.single 0 1 := by
  rw [CoxeterSystem.reflectionRepresentation_simple]
  exact Module.preReflection_apply_self (by simp)

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
theorem a₂_gram (i j : Fin 2) :
    algebraMap ℤ ℝ (!![2, -1; -1, 2] i j) =
      2 * (CoxeterMatrix.I 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.I, cos_pi_div_three]

/-- In `A₂` the integral simple reflection `s₀` sends `e₁` to `e₀ + e₁`. -/
example :
    (CoxeterMatrix.I 1).toCoxeterSystem.reflectionRepresentation (algebraMap ℤ ℝ).injective_int
        a₂_gram ((CoxeterMatrix.I 1).toCoxeterSystem.simple 0) (Finsupp.single 1 1) =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
  rw [CoxeterSystem.reflectionRepresentation_simple_apply]
  simp [sub_eq_add_neg, add_comm]

/-- The degenerate matrix `!![2, -2; -2, 2]` satisfies the Gram hypothesis of the infinite
dihedral group. -/
theorem infiniteDihedral_gram (i j : Fin 2) :
    algebraMap ℤ ℝ (!![2, -2; -2, 2] i j) =
      2 * infiniteDihedralCoxeterMatrix.geometricForm (Finsupp.single i 1)
        (Finsupp.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [infiniteDihedralCoxeterMatrix]

/-- For the degenerate infinite dihedral matrix `!![2, -2; -2, 2]`, the element `s₀ s₁` sends
`e₀` to `3 e₀ + 2 e₁`; no determinant condition is needed for the realization. -/
example :
    infiniteDihedralCoxeterMatrix.toCoxeterSystem.reflectionRepresentation
        (algebraMap ℤ ℝ).injective_int infiniteDihedral_gram
        (infiniteDihedralCoxeterMatrix.toCoxeterSystem.simple 0 *
          infiniteDihedralCoxeterMatrix.toCoxeterSystem.simple 1) (Finsupp.single 0 1) =
      Finsupp.single 0 3 + Finsupp.single 1 2 := by
  rw [map_mul, mul_apply_eq_comp, CoxeterSystem.reflectionRepresentation_simple_apply,
    CoxeterSystem.reflectionRepresentation_simple_apply]
  ext k
  fin_cases k <;> simp

end TauCeti
