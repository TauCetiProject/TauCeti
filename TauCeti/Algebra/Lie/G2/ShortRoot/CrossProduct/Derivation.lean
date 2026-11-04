/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Weight support of cross-product derivations

When two is regular, a derivation of the seven-dimensional short-root cross product has
no matrix entries between opposite nonzero weights. These are exactly the off-diagonal
positions whose
integral weight difference is not a root of the named G₂ datum. Thus cross-product
preservation excludes the six doubled short roots from the adjoint weights of any
subgroup preserving this tensor, including the short-root G₂ carrier.

The computation extends the three positive-weight calculations in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Simple` to both signs, without assuming
that a matrix is homogeneous. Coefficients may lie in any commutative ring
in which two is regular, including the integers.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*,
  Forum of Mathematics Pi **3** (2015), §6.
-/

public section

namespace TauCeti.G2ShortRoot

open DynkinType

variable {R : Type*} [CommRing R]

/-- Expand one entry of the cross-product Leibniz equation. -/
local macro "cross_entry_norm" : tactic =>
  `(tactic| (simp [Matrix.mul_apply, Fin.sum_univ_succ,
    ConstantMultiplication.imageStructureMatrix_def, crossOperator_def]
    <;> ring))

/-- If two is regular, a derivation of the short-root cross product has zero entries
between opposite nonzero weights. -/
theorem crossDerivation_apply_rev_eq_zero (h2 : IsRegular (2 : R))
    {X : Matrix (Fin 7) (Fin 7) R}
    (hX : ∀ c, X * (crossOperator c).map (Int.cast : ℤ → R) =
      ConstantMultiplication.imageStructureMatrix ℤ 7 crossOperator X c +
        (crossOperator c).map (Int.cast : ℤ → R) * X)
    (i : Fin 7) (hi : i ≠ 3) : X i i.rev = 0 := by
  -- Each of the six coordinates is forced by a single entry of the Leibniz equation.
  have h06 : X 0 6 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 4) 1) 6
  have h15 : X 1 5 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 2) 1) 6
  have h24 : X 2 4 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 1) 0) 4
  have h42 : X 4 2 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 2) 1) 0
  have h51 : X 5 1 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 1) 2) 0
  have h60 : X 6 0 = 0 := by
    apply h2.left
    linear_combination (norm := cross_entry_norm) -congrFun (congrFun (hX 0) 4) 1
  fin_cases i <;> simp_all

/-- When two is regular, every nonzero off-diagonal entry of a cross-product derivation
has a root as its integral weight difference. Weights are not reduced modulo the characteristic. -/
theorem crossDerivation_apply_eq_zero_of_not_root (h2 : IsRegular (2 : R))
    {X : Matrix (Fin 7) (Fin 7) R}
    (hX : ∀ c, X * (crossOperator c).map (Int.cast : ℤ → R) =
      ConstantMultiplication.imageStructureMatrix ℤ 7 crossOperator X c +
        (crossOperator c).map (Int.cast : ℤ → R) * X)
    (i j : Fin 7) (hij : i ≠ j)
    (hroot : weight i - weight j ∉ Set.range g2Root) : X i j = 0 := by
  have hrev : j = i.rev := by
    have hcases : ∀ i j : Fin 7, i ≠ j → weight i - weight j ∉ Set.range g2Root →
        j = i.rev := by
      simp only [Set.mem_range, g2Root_apply]
      decide +kernel
    exact hcases i j hij hroot
  subst j
  exact crossDerivation_apply_rev_eq_zero h2 hX i (by intro h; subst i; exact hij rfl)

end TauCeti.G2ShortRoot
