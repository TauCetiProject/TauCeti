/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.LieContainment
import Mathlib.Algebra.Lie.CartanCriterion

/-!
# Semisimple affine groups are linearly reductive in characteristic zero

A semisimple affine group over a field of characteristic zero has semisimple Lie algebra.
Consequently every finite-dimensional rational representation is completely reducible.
Neither conclusion requires the ground field to be algebraically closed or the group to split.

On the geometric fibre, comparison of group and Lie radicals identifies the Lie radical with
the Lie algebra of the identity subgroup. Cartan's criterion gives a nondegenerate Killing
form, which descends along the field extension. The complete-reducibility criterion in
`Representation.CompleteReducibility` then applies to the group over its original field.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.isKilling_lieAlgebra`: the tangent Lie algebra of a
  semisimple group has nondegenerate Killing form in characteristic zero.
* `TauCeti.semisimpleCommHopfAlgProperty.linearlyReductive`: semisimple affine groups in
  characteristic zero are linearly reductive.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 22.

The proof combines `FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical`
with Mathlib's Cartan criterion and the existing comodule form of Weyl's theorem.
-/

public section

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The tangent Lie algebra of a semisimple affine group in characteristic zero has
nondegenerate Killing form, over any ground field. -/
theorem isKilling_lieAlgebra (hH : semisimpleCommHopfAlgProperty k H) :
    LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : ConnectedSpace (PrimeSpectrum G) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  have hrad :=
    ((semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH).2.2
  have hlie : (FiniteTypeCommHopfAlgCat.isNormal_solvableRadicalDefiningIdeal G).lieIdeal
      (B := K) = ⊥ := by
    ext d
    rw [← LieIdeal.mem_toLieSubalgebra,
      HopfIdeal.IsNormal.lieIdeal_toLieSubalgebra, hrad,
      HopfIdeal.lieSubalgebra_augmentation]
    simp only [LieSubalgebra.mem_bot, LieSubmodule.mem_bot]
  let _ : LieAlgebra.HasTrivialRadical K
      (Derivation K G (Bialgebra.CounitAlgebra K G K)) :=
    ⟨(FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical G).symm.trans
      hlie⟩
  exact (isKilling_lie_baseChange_iff (k := k) (K := K) (H := H)).mp inferInstance

/-- **Semisimple affine groups are linearly reductive in characteristic zero.** Every
finite-dimensional rational representation is completely reducible, without a splitting or
algebraic-closedness assumption on the field. -/
theorem linearlyReductive (hH : semisimpleCommHopfAlgProperty k H) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let _ := hH.isKilling_lieAlgebra
  exact linearlyReductiveCommHopfAlgProperty.of_geometricallyConnected_of_isKilling
    hH.geometricallyConnected

end TauCeti.semisimpleCommHopfAlgProperty
