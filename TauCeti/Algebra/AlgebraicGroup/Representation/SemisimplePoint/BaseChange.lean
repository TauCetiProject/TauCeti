/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.Faithful
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding

/-!
# Semisimple points under base change

For a finite-type affine group and a perfect extension field, the base-change adjunction on
points preserves and reflects semisimplicity. Reflection tests the base-changed original
comodules; preservation uses a faithful finite-dimensional comodule, whose base change is
faithful. This identifies the geometric-point predicate with semisimplicity of points on the
geometric fibre without requiring the original field to be perfect.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u

variable {k H K : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Algebra.FiniteType k H] [Field K] [Algebra k K] [PerfectField K]

/-- Semisimplicity of points is invariant under the base-change adjunction to a perfect
extension field. No perfectness of the original field or reducedness of the group is needed. -/
@[simp]
theorem isSemisimplePoint_baseChangePointsMulEquiv_iff
    (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint (AlgHom.baseChangePointsMulEquiv (K := K) g) ↔
      IsSemisimplePoint g := by
  constructor
  · intro hg
    rw [isSemisimplePoint_iff_forall_isSemisimple_endOfPoint]
    intro M
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    rw [← Comodule.basePointsRepresentation_baseChangePointsMulEquiv (M := M) g]
    have h := (isSemisimplePoint_iff_forall_isSemisimple_basePointsRepresentation _).mp hg
      (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M))
    -- The bundled comodule reconstructs its additive group from its module. Transport
    -- along the identity linear equivalence to avoid identifying those group instances.
    exact (@LinearEquiv.isSemisimple_iff K
      (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)) _
      (FGComoduleCat.instAddCommGroupCarrier _) _
      (Comodule.basePointsRepresentation (H := K ⊗[k] H)
        (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M))
        (AlgHom.baseChangePointsMulEquiv (K := K) g))
      (K ⊗[k] M) _ _
      (Comodule.basePointsRepresentation (H := K ⊗[k] H) (K ⊗[k] M)
        (AlgHom.baseChangePointsMulEquiv (K := K) g))
      (LinearEquiv.refl K _) (by ext x; rfl)).mp h
  · intro hg
    obtain ⟨M, d, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom
      (k := k) (H := H)
    let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
    let _ : Module.Free k M := Module.Free.of_basis b
    let _ : Module.Finite k M := Module.Finite.of_basis b
    have hM : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
      (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    let MK := FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)
    apply (isSemisimplePoint_iff_isSemisimple_pointsAction_of_isFaithful
      MK (Comodule.IsFaithful.baseChange (K := K) hM) _).mpr
    rw [isSemisimple_pointsAction_iff_basePointsRepresentation]
    rw [Comodule.basePointsRepresentation_baseChangePointsMulEquiv]
    have h := (isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mp hg
      (FGComoduleCat.of (R := k) (C := H) M)
    -- Use the identity equivalence for the additive group reconstructed by `MK`.
    exact (@LinearEquiv.isSemisimple_iff K
      (K ⊗[k] (FGComoduleCat.of (R := k) (C := H) M)) _ _ _
      (Comodule.endOfPoint (FGComoduleCat.of (R := k) (C := H) M) g.ofConv)
      MK (FGComoduleCat.instAddCommGroupCarrier MK) _ (Comodule.endOfPoint M g.ofConv)
      (LinearEquiv.refl K _) (by ext x; rfl)).mp h

end TauCeti.HopfAlgebra
