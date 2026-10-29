/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.LieContainment
import Mathlib.Algebra.Lie.CartanCriterion

/-!
# Recognizing semisimple affine groups by their Lie algebras

A smooth geometrically connected affine group of finite type whose Lie algebra has a
nondegenerate Killing form is semisimple, over any field. In characteristic zero the converse
holds, so this gives a Lie-algebra criterion for group-theoretic semisimplicity without a
splitting or algebraic-closedness hypothesis. Geometric connectedness is essential: the Lie
algebra cannot detect an extra finite étale component group.

The sufficient criterion eliminates every connected smooth solvable normal subgroup of the
geometric fibre. Its tangent ideal lies in the ambient Lie radical, which vanishes by
Mathlib's Killing-form criterion; the connected zero-tangent theorem then makes the subgroup
trivial. The converse uses `Solvable.Radical.LieContainment` to identify the group and Lie
radicals, followed by Cartan's criterion. These results permit recognition from explicit
tangent matrix calculations.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* Mathlib's `Algebra.Lie.CartanCriterion`: Cartan's criterion.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A smooth geometrically connected finite-type affine group with nondegenerate Killing
form on its tangent Lie algebra is semisimple, in any characteristic. -/
theorem semisimpleCommHopfAlgProperty.of_isKilling
    [LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k))]
    (hsmooth : Algebra.Smooth k H)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    semisimpleCommHopfAlgProperty k H := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let _ : LieAlgebra.IsKilling K
      (Derivation K G (Bialgebra.CounitAlgebra K G K)) :=
    (isKilling_lie_baseChange_iff (k := k) (K := K) (H := H)).mpr inferInstance
  rw [semisimpleCommHopfAlgProperty_iff]
  refine ⟨hsmooth, hconnected, ?_⟩
  intro I hnormal hconn hsm hsolv
  exact HopfIdeal.IsSolvableRadicalCandidate.eq_augmentation_of_hasTrivialRadical
    (.mk hnormal hconn hsm hsolv)

variable [CharZero k]

/-- The tangent Lie algebra of a semisimple affine group in characteristic zero has
nondegenerate Killing form, over any ground field. -/
theorem semisimpleCommHopfAlgProperty.isKilling_lieAlgebra
    (hH : semisimpleCommHopfAlgProperty k H) :
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

/-- In characteristic zero, a geometrically connected finite-type affine group is
semisimple exactly when its tangent Lie algebra has nondegenerate Killing form.
Smoothness is automatic by Cartier's theorem. -/
theorem semisimpleCommHopfAlgProperty_iff_isKilling_lieAlgebra
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    semisimpleCommHopfAlgProperty k H ↔
      LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  refine ⟨semisimpleCommHopfAlgProperty.isKilling_lieAlgebra, fun h ↦ ?_⟩
  let _ := h
  exact semisimpleCommHopfAlgProperty.of_isKilling
    ((smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj))
    hconnected

end TauCeti
