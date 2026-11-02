/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm

/-!
# Integral support of the numbered E₇ root matrices

The raising and lowering matrices of the 56-dimensional minuscule representation have
entries only where the difference of the two integral weights is their signed simple root.
This common support criterion supplies both the specialized carrier and the generated
subgroup's adjoint-weight proofs, before any change of coefficient ring.

## Main declarations

* `TauCeti.E7Minuscule.rootMatrix_apply_eq_zero_of_weight_sub_ne`: the integral support
  criterion for a numbered raising or lowering matrix.
-/

public section

namespace TauCeti.E7Minuscule

open DynkinType

/-- A raising or lowering matrix entry vanishes unless its minuscule weight difference is the
corresponding signed simple root. -/
theorem rootMatrix_apply_eq_zero_of_weight_sub_ne (k : Fin 7 ⊕ Fin 7) (a b : Fin 56)
    (h : e7MinusculeWeight a - e7MinusculeWeight b ≠ E7.rootGeneratorWeight valid_E7 k) :
    Sum.elim raisingMatrix loweringMatrix k a b = 0 := by
  -- E₇ symmetry identifies the table's Cartan columns with the numbered root rows.
  rcases k with i | i
  · have hroot : (E7.rootGeneratorWeight valid_E7 (.inl i) : Fin 7 → ℤ) =
        fun j : Fin 7 ↦ weightTable.cartanMatrix j i := by
      funext (j : Fin 7)
      rw [weightTable_cartanMatrix, (CartanMatrix.E_isSymm 7).apply]
      simpa only [rank_E7, cartanMatrix_E7] using
        E7.rootGeneratorWeight_inl valid_E7 i j
    have hz := weightTable.raisingMatrix_apply_eq_zero_of_weight_sub_ne i a b
      (by
        rw [weightTable_weight]
        intro hab
        exact h (hab.trans hroot.symm))
    simpa only [Sum.elim_inl, raisingMatrix_apply, weightTable.raisingMatrix_apply,
      weightTable_weight, weightTable_reflection] using hz
  · have hroot : (E7.rootGeneratorWeight valid_E7 (.inr i) : Fin 7 → ℤ) =
        -fun j : Fin 7 ↦ weightTable.cartanMatrix j i := by
      funext (j : Fin 7)
      rw [Pi.neg_apply, weightTable_cartanMatrix, (CartanMatrix.E_isSymm 7).apply]
      simpa only [rank_E7, cartanMatrix_E7] using
        E7.rootGeneratorWeight_inr valid_E7 i j
    have hz := weightTable.loweringMatrix_apply_eq_zero_of_weight_sub_ne i a b
      (by
        rw [weightTable_weight]
        intro hab
        exact h (hab.trans hroot.symm))
    simpa only [Sum.elim_inr, loweringMatrix_apply, weightTable.loweringMatrix_apply,
      weightTable_weight, weightTable_reflection] using hz

end TauCeti.E7Minuscule
