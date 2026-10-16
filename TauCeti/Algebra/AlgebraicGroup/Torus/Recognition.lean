/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Recognition
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange

/-!
# Recognizing tori from semisimple geometric points

A geometrically reduced, geometrically connected affine group of finite type is a torus
exactly when it is commutative and every geometric point is semisimple. This combines the
multiplicative-type recognition criterion with the connected and geometrically reduced
multiplicative-type characterization of tori. No perfectness or splitting assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12.c and 12.d.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

variable {k : Type u} [Field k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k H]

open torusCommHopfAlgProperty in
/-- A smooth geometrically connected affine group is a torus exactly when it is commutative
and all points of its geometric fibre are semisimple. More generally, geometric reducedness
suffices in place of smoothness. -/
theorem torusCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints
    (hconn : geometricallyConnectedCommHopfAlgProperty k H.obj) :
    torusCommHopfAlgProperty k H ↔
      Coalgebra.IsCocomm k H ∧
        geometricallySemisimplePointsCommHopfAlgProperty k H.obj := by
  rw [iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced,
    multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, hconn, ?_⟩⟩
  apply geometricallyReducedCommHopfAlgProperty.of_baseChange (AlgebraicClosure k) H.obj
  exact (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (AlgebraicClosure k) (CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mpr
      inferInstance

end TauCeti
