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
matrix `!![2, -2; -2, 2]` is allowed, and `s₀ s₁` sends `e₀` to `3 e₀ + 2 e₁`. We also check that
`(CoxeterMatrix.I 1).integralGramMatrix` recovers `!![2, -1; -1, 2]`, that reducing the rank-one
integral representation modulo `2` makes `s₀` act trivially, and that transporting `A₂` to
`Fin 2 → ℤ` along `Pi.basisFun` sends `1 ⊗ₜ Pi.single i 1` to `eᵢ` after extending scalars to `ℝ`.
Each Gram hypothesis is checked in its own example; the reflection examples take it as a hypothesis,
which by proof irrelevance loses nothing.
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

/-- The canonical integer Gram matrix of `A₂` is `!![2, -1; -1, 2]`. -/
example : (CoxeterMatrix.I 1).integralGramMatrix = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.integralGramMatrix_apply, CoxeterMatrix.I]

/-- Reducing the rank-one integral geometric representation modulo `2` makes `s₀` act as the
identity, showing that modular reductions of a faithful integral representation need not remain
faithful. -/
example (hA : ∀ i j : Fin 1, algebraMap ℤ ℝ (!![2] i j) =
      2 * (CoxeterMatrix.A 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) :
    (CoxeterMatrix.A 1).toCoxeterSystem.mapReflectionRepresentation
        (algebraMap ℤ ℝ).injective_int hA (Int.castRingHom (ZMod 2))
        ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) = 1 := by
  refine Finsupp.lhom_ext fun i a ↦ ?_
  rw [CoxeterSystem.mapReflectionRepresentation_simple_apply, one_apply_eq_self]
  clear hA
  refine Finsupp.ext fun j ↦ ?_
  fin_cases i
  fin_cases j
  simp only [Fin.zero_eta, Fin.isValue, Int.coe_castRingHom, Finsupp.linearCombination_single,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Int.cast_ofNat,
    smul_eq_mul, Finsupp.smul_single, mul_one, Finsupp.coe_sub, Pi.sub_apply,
    Finsupp.single_eq_same, sub_eq_self]
  revert a
  decide

open TensorProduct in
/-- Transporting `A₂` to `Fin 2 → ℤ` along `Pi.basisFun ℤ (Fin 2)` and extending scalars to `ℝ`
sends `1 ⊗ₜ Pi.single i 1` to the `i`-th real simple root `Finsupp.single i 1`. -/
example (hA : ∀ i j : Fin 2, algebraMap ℤ ℝ (!![2, -1; -1, 2] i j) =
      2 * (CoxeterMatrix.I 1).geometricForm (Finsupp.single i 1) (Finsupp.single j 1))
    (i : Fin 2) :
    (CoxeterMatrix.I 1).toCoxeterSystem.baseChangeRealReflectionRepresentationOfBasisEquiv
        (algebraMap ℤ ℝ).injective_int hA (Pi.basisFun ℤ (Fin 2))
        ((1 : ℝ) ⊗ₜ[ℤ] Pi.basisFun ℤ (Fin 2) i) =
      Finsupp.single i 1 := by
  rw [CoxeterSystem.baseChangeRealReflectionRepresentationOfBasisEquiv_one_tmul,
    Module.Basis.repr_self, Finsupp.mapRange_single, map_one]

