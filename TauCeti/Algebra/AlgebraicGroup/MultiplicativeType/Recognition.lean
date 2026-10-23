/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.BaseChange
import TauCeti.Algebra.Coalgebra.BaseChange

/-!
# Recognizing groups of multiplicative type from geometric points

For a geometrically reduced finite-type affine group, being of multiplicative type is
equivalent to commutativity together with semisimplicity of every point of its geometric
fibre. The original field need not be perfect.

The statement uses `geometricallySemisimplePointsCommHopfAlgProperty`, testing points
with values in the algebraic closure on the original group's finite-dimensional representations.
This is the usual geometric criterion:
after passage to an algebraic closure, commuting semisimple points give a diagonalizable group.
The reducedness assumption keeps infinitesimal groups visible; without it even `αₚ` would
pass the point test.

The recognition argument uses
`DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint`.

## References

* T. A. Springer, *Linear Algebraic Groups*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §§12.c and 12.d.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

variable {k : Type u} [Field k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k H]

/-- A geometrically reduced finite-type affine group is of multiplicative type exactly when
it is commutative and every algebraic-closure-valued point is semisimple.
Connectedness is not required. -/
theorem multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints :
    multiplicativeTypeCommHopfAlgProperty k H ↔
      Coalgebra.IsCocomm k H ∧
        geometricallySemisimplePointsCommHopfAlgProperty k H.obj := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  have hrecognition :=
    DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint G
  rw [multiplicativeTypeCommHopfAlgProperty_iff, hrecognition,
    geometricallySemisimplePointsCommHopfAlgProperty_iff]
  let e := AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := K)
  constructor
  · rintro ⟨hc, hss⟩
    refine ⟨Coalgebra.IsCocomm.of_baseChange (K := K) (h := hc), fun g ↦ ?_⟩
    exact (HopfAlgebra.isSemisimplePoint_baseChangePointsMulEquiv_iff g).mp (hss (e g))
  · rintro ⟨hc, hss⟩
    let _ := hc
    refine ⟨inferInstance, fun g ↦ ?_⟩
    have h := (HopfAlgebra.isSemisimplePoint_baseChangePointsMulEquiv_iff (e.symm g)).mpr
      (hss (e.symm g))
    exact e.apply_symm_apply g ▸ h

end TauCeti
