/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Lie
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import Mathlib.Algebra.CharP.Algebra

/-!
# Semisimplicity under extension of characteristic-zero fields

Semisimplicity of a finite-type affine group over a field of characteristic zero is preserved
and reflected by every field extension. Neither field needs to be algebraically closed, the
extension need not be algebraic, and the group need not split. In particular, one can establish
semisimplicity on a split model over an extension and descend to the original group.

The Lie-algebra criterion in `Semisimple.Lie` reduces the assertion to invariance of the
nondegeneracy of the Killing form under scalar extension. Geometric connectedness is also
preserved and reflected by field extension. Smoothness is automatic by Cartier's theorem.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.baseChange`: preservation of semisimplicity.
* `TauCeti.semisimpleCommHopfAlgProperty.of_baseChange`: descent of semisimplicity.
* `TauCeti.semisimpleCommHopfAlgProperty.baseChange_iff`: the scalar-extension criterion,
  without a separate connectedness hypothesis.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.

The tangent comparison is `TauCeti.isKilling_lie_baseChange_iff`; the group-theoretic
comparison is `TauCeti.semisimpleCommHopfAlgProperty_iff_isKilling_lieAlgebra`.
-/

public section

open scoped TensorProduct

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A semisimple affine group in characteristic zero remains semisimple after any extension
of the ground field, including transcendental extensions. -/
theorem baseChange (hH : semisimpleCommHopfAlgProperty k H) :
    semisimpleCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) := by
  let _ : LieAlgebra.IsKilling K
      (Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) :=
    (isKilling_lie_baseChange_iff (k := k) (K := K) (H := H)).mpr hH.isKilling_lieAlgebra
  let _ : Algebra.Smooth k H := hH.smooth
  exact semisimpleCommHopfAlgProperty.of_isKilling (Algebra.Smooth.baseChange k H K)
    (geometricallyConnectedCommHopfAlgProperty.baseChange k K H.obj hH.geometricallyConnected)

/-- Semisimplicity descends along any extension of characteristic-zero fields. No smoothness,
connectedness, or splitting hypothesis on the original group needs to be supplied. -/
theorem of_baseChange
    (hH : semisimpleCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)) :
    semisimpleCommHopfAlgProperty k H := by
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let _ : LieAlgebra.IsKilling k (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
    (isKilling_lie_baseChange_iff (k := k) (K := K) (H := H)).mp hH.isKilling_lieAlgebra
  exact semisimpleCommHopfAlgProperty.of_isKilling
    ((smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj))
    (geometricallyConnectedCommHopfAlgProperty.of_baseChange k K H.obj hH.geometricallyConnected)

-- The defining simp lemma `semisimpleCommHopfAlgProperty_iff` already expands the left-hand side,
-- so adding this equivalence to the simp set would violate simpNF.
/-- In characteristic zero, a finite-type affine group is semisimple exactly when it becomes
semisimple after a field extension. The extension may be arbitrary. -/
theorem baseChange_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    semisimpleCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) ↔
      semisimpleCommHopfAlgProperty k H :=
  ⟨of_baseChange, baseChange⟩

end TauCeti.semisimpleCommHopfAlgProperty
