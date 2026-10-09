/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.MatrixProd
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
public import TauCeti.RepresentationTheory.Spin.Structure

/-!
# The Spin group of a four-dimensional hyperbolic space

Let `K` be a field of characteristic different from two. The standard hyperbolic quadratic space
of dimension four is the dual product on `M* × M`, for `M = Fin 2 → K`. Its canonical
polarization gives a product-of-matrix-algebras model

```text
  Cl⁺(M* × M) ≃ M₂(K) × M₂(K).
```

The general rank-four comparison between Spin and the reverse-unitary carrier then identifies its
Spin group with `SL₂(K) × SL₂(K)`. In particular this supplies the split rational model after
specializing `K` to `ℚ`.

## Main definitions and results

* `TauCeti.hyperbolicFourEvenEquivMatrixProd` identifies the even Clifford algebra with two
  two-by-two matrix algebras.
* `TauCeti.hyperbolicFourEvenEquivMatrixProd_apply` relates it to the canonical half-spin
  matrix-product model.
* `TauCeti.hyperbolicFourSpinEquivSpecialLinearProd` identifies the Spin group with
  `SL₂(K) × SL₂(K)`.
* The accompanying coercion theorems expose the forward and inverse maps through the chosen even
  Clifford algebra model.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

namespace TauCeti

open Module CliffordAlgebra

universe u

variable (K : Type u) [Field K]

private theorem hyperbolicFour_finrank :
    finrank K (SplitEvenSpace K 2) = 2 * 2 := by
  simp [SplitEvenSpace]

private theorem nondegenerate_hyperbolicFour :
    (splitEvenForm K 2).Nondegenerate :=
  (splitEvenPolarization K 2).nondegenerate_of_line_eq_bot
    (splitEvenPolarization_line K 2)

private theorem hyperbolicFour_W_ne_bot :
    (splitEvenPolarization K 2).W ≠ ⊥ :=
  Submodule.finrank_eq_zero.not.1 <| by
    rw [(splitEvenPolarization K 2).finrank_W_eq_of_finrank_eq_two_mul
      (hyperbolicFour_finrank K)]
    norm_num

variable [Invertible (2 : K)]

/-- The even Clifford algebra of the four-dimensional hyperbolic space is a product of two
two-by-two matrix algebras. The two factors are its actions on the half-spin summands of the
canonical hyperbolic polarization. -/
noncomputable def hyperbolicFourEvenEquivMatrixProd :
    even (splitEvenForm K 2) ≃ₐ[K]
      Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K := by
  simpa using (splitEvenPolarization K 2).evenCliffordEquivProdMatrix
    (hyperbolicFour_W_ne_bot K) (hyperbolicFour_finrank K)

/-- The hyperbolic even-Clifford equivalence applies the matrix-product model of the canonical
polarization. The latter's application theorem identifies its two coordinates with the matrices
of the two half-spin actions. -/
@[simp]
theorem hyperbolicFourEvenEquivMatrixProd_apply
    (x : even (splitEvenForm K 2)) :
    hyperbolicFourEvenEquivMatrixProd K x =
      (splitEvenPolarization K 2).evenCliffordEquivProdMatrix (l := 2)
        (Submodule.finrank_eq_zero.not.1 <| by
          rw [(splitEvenPolarization K 2).finrank_W_eq_of_finrank_eq_two_mul
            (by simp [SplitEvenSpace] : finrank K (SplitEvenSpace K 2) = 2 * 2)]
          norm_num)
        (by simp [SplitEvenSpace]) x := by
  simp [hyperbolicFourEvenEquivMatrixProd]

/-- The Spin group of the four-dimensional hyperbolic space is the product of two special linear
groups of degree two. -/
noncomputable def hyperbolicFourSpinEquivSpecialLinearProd :
    spinGroup (splitEvenForm K 2) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
  spinGroupEquivSpecialLinearProdOfAlgEquiv (splitEvenForm K 2)
    (nondegenerate_hyperbolicFour K) ((hyperbolicFour_finrank K).trans (by norm_num))
      (hyperbolicFourEvenEquivMatrixProd K)

/-- The hyperbolic four-dimensional Spin equivalence evaluates the chosen even-Clifford
matrix-product model on the underlying Spin element. -/
@[simp]
theorem coe_hyperbolicFourSpinEquivSpecialLinearProd_apply
    (s : spinGroup (splitEvenForm K 2)) :
    (((hyperbolicFourSpinEquivSpecialLinearProd K s).1 : Matrix (Fin 2) (Fin 2) K),
      ((hyperbolicFourSpinEquivSpecialLinearProd K s).2 : Matrix (Fin 2) (Fin 2) K)) =
      hyperbolicFourEvenEquivMatrixProd K
        (evenUnitaryGroupEvenPart (splitEvenForm K 2)
          (spinGroupToEvenUnitary (splitEvenForm K 2) s)) := by
  exact coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_apply _ _ _ _ _

/-- The inverse hyperbolic four-dimensional Spin equivalence recovers the Clifford value through
the inverse even-Clifford matrix-product model. -/
@[simp]
theorem coe_hyperbolicFourSpinEquivSpecialLinearProd_symm_apply
    (g : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) :
    ((hyperbolicFourSpinEquivSpecialLinearProd K).symm g :
        CliffordAlgebra (splitEvenForm K 2)) =
      ((hyperbolicFourEvenEquivMatrixProd K).symm
        ((g.1 : Matrix (Fin 2) (Fin 2) K), (g.2 : Matrix (Fin 2) (Fin 2) K)) :
          CliffordAlgebra (splitEvenForm K 2)) := by
  exact coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_symm_apply _ _ _ _ _

end TauCeti

end
