/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DividedPowerDerivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.RaisingDerivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.LoweringDerivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.SpecialIsogeny

/-!
# The pinned data of type F4 preserves the invariant multiplication

The eight numbered simple root elements `1 + u X + u² X⁽²⁾` of the twenty-six-dimensional module
of type `F₄`, and every point of its weight torus, are multiplicative for the invariant symmetric
multiplication, over every commutative ring.

For a root element this is the exponential of the fact that its logarithm differentiates the
multiplication: expanding the multiplicativity equation in the parameter leaves four coefficient
conditions, of which the first is the derivation property and the remaining three follow from it
together with the divided-power relations. For a torus point the equation is diagonal and reduces
to the additivity of weights along a nonzero structure constant, which holds because the
multiplication is a morphism of modules.

Nothing here transports the multiplicativity to a group of matrix-valued points, and nothing shows
that the pinned matrices exhaust any such group.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_rootMatrix`: each numbered simple root generator differentiates
  the multiplication.
* `TauCeti.F4ShortRoot.preservesMultiplication_rootElementMatrix`: **every numbered simple root
  element is multiplicative for the multiplication.**
* `TauCeti.F4ShortRoot.preservesMultiplication_weightTorusMatrix`: **every point of the weight
  torus is multiplicative for the multiplication.**

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §2.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

universe u

variable {R : Type u} [CommRing R]

/-- **Every numbered simple root generator of the twenty-six-dimensional module of type `F₄`
differentiates the invariant symmetric multiplication.** -/
theorem isDerivation_rootMatrix (k : Fin 4 ⊕ Fin 4) : IsDerivation (rootMatrix k) := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl]
      exact isDerivation_raisingMatrix i
  | inr i =>
      rw [rootMatrix_inr]
      exact isDerivation_loweringMatrix i

/-- **Every numbered simple root element is multiplicative for the invariant multiplication**,
over every commutative ring. -/
theorem preservesMultiplication_rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : R) :
    PreservesMultiplication (rootElementMatrix k u) := by
  rw [rootElementMatrix_def]
  exact preservesMultiplication_one_add_smul_add_smul (isDerivation_rootMatrix k)
    (rootMatrix_mul_self k) (rootDividedSquareMatrix_mul_rootMatrix k)
    (rootMatrix_mul_rootDividedSquareMatrix k) (rootDividedSquareMatrix_mul_self k) u

/-! ## The weight torus -/

/-- Weights add along a nonzero structure constant of the invariant multiplication. -/
private theorem weight_of_multiplicationOperator_ne_zero :
    ∀ k : Fin 26, ∀ p : Fin 26 × Fin 26, multiplicationOperator k p.1 p.2 = 0 ∨
      ∀ i : Fin 4,
        f4ShortRootWeight p.1 i = f4ShortRootWeight k i + f4ShortRootWeight p.2 i := by
  simp only [multiplicationOperator_apply]
  decide +kernel

/-- **A diagonal matrix is multiplicative for the invariant multiplication** when its entries are
multiplicative along every nonzero structure constant. -/
theorem preservesMultiplication_diagonal {d : Fin 26 → R}
    (hd : ∀ k m n : Fin 26, multiplicationOperator k m n ≠ 0 → d m = d k * d n) :
    PreservesMultiplication (Matrix.diagonal d) := by
  rw [preservesMultiplication_def]
  intro k
  have hcol : (fun a => Matrix.diagonal d a k) = d k • fun a => if a = k then (1 : R) else 0 := by
    funext a
    rw [Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero]
  rw [hcol, multiplicationBy_smul, multiplicationBy_single]
  ext m n
  rw [Matrix.diagonal_mul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul,
    Matrix.map_apply]
  by_cases hz : multiplicationOperator k m n = 0
  · rw [hz, Int.cast_zero]
    ring
  · rw [hd k m n hz]
    ring

/-- **Every point of the weight torus is multiplicative for the invariant multiplication**: the
weights add along a nonzero structure constant. -/
theorem preservesMultiplication_weightTorusMatrix (s : Fin 4 → Rˣ) :
    PreservesMultiplication
      (Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : R)) := by
  refine preservesMultiplication_diagonal fun k m n hz => ?_
  have hw : f4ShortRootWeight m = f4ShortRootWeight k + f4ShortRootWeight n :=
    funext ((weight_of_multiplicationOperator_ne_zero k (m, n)).resolve_left hz)
  rw [hw, torusCharacter_add, Units.val_mul]

end TauCeti.F4ShortRoot
