/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Recognition
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.Coalgebra.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange

/-!
# Recognizing groups of multiplicative type and tori from geometric points

For a geometrically reduced finite-type affine group, being of multiplicative type is
equivalent to commutativity together with semisimplicity of every point of its geometric
fibre. Adding geometric connectedness characterizes tori. Neither result requires the
original field to be perfect or the torus to split there.

The points in the statements are base-valued points of the geometric fibre, and semisimplicity
is tested on its finite-dimensional representations. This is the usual geometric criterion:
after passage to an algebraic closure, commuting semisimple points give a diagonalizable group.
The reducedness assumption keeps infinitesimal groups visible; without it even `αₚ` would
pass the point test.

The recognition argument uses
`DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint`.
The torus criterion uses the existing connected and geometrically reduced multiplicative-type
characterization in `TauCeti.Algebra.AlgebraicGroup.Torus.Characterization`.

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
it is commutative and every algebraic-closure-valued point of its geometric fibre is semisimple.
Connectedness is not required. -/
theorem multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_forall_isSemisimplePoint :
    multiplicativeTypeCommHopfAlgProperty k H ↔
      Coalgebra.IsCocomm k H ∧
        ∀ g : WithConv
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H →ₐ[AlgebraicClosure k]
            AlgebraicClosure k), HopfAlgebra.IsSemisimplePoint g := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  have hrecognition :=
    DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint G
  rw [multiplicativeTypeCommHopfAlgProperty_iff, hrecognition]
  constructor
  · rintro ⟨hc, hss⟩
    exact ⟨Coalgebra.IsCocomm.of_baseChange (K := K) (h := hc), hss⟩
  · rintro ⟨hc, hss⟩
    let _ := hc
    exact ⟨inferInstance, hss⟩

open torusCommHopfAlgProperty in
/-- A smooth geometrically connected affine group is a torus exactly when it is commutative
and all points of its geometric fibre are semisimple. More generally, geometric reducedness
suffices in place of smoothness. -/
theorem torusCommHopfAlgProperty_iff_isCocomm_and_forall_isSemisimplePoint
    (hconn : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    torusCommHopfAlgProperty k H ↔
      Coalgebra.IsCocomm k H ∧
        ∀ g : WithConv
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H →ₐ[AlgebraicClosure k]
            AlgebraicClosure k), HopfAlgebra.IsSemisimplePoint g := by
  rw [iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced,
    multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_forall_isSemisimplePoint]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, hconn, ?_⟩⟩
  apply geometricallyReducedCommHopfAlgProperty.of_baseChange (AlgebraicClosure k) H.obj
  exact (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (AlgebraicClosure k) (CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mpr
      inferInstance

end TauCeti
