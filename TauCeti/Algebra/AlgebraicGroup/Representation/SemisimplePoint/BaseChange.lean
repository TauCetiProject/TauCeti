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

omit [PerfectField K] in
/-- Semisimplicity of an endomorphism of a bundled finite-dimensional comodule agrees with
semisimplicity on the underlying unbundled comodule. The bundled object reconstructs its additive
group from its module structure, so the two statements use different additive group instances. -/
private theorem isSemisimple_fgComoduleCatOf_iff {C N : Type u} [AddCommMonoid C] [Module K C]
    [Coalgebra K C] [AddCommGroup N] [Module K N] [Comodule K C N] [Module.Finite K N]
    (f : Module.End K N) :
    @Module.End.IsSemisimple K (FGComoduleCat.of (R := K) (C := C) N) _
        (FGComoduleCat.instAddCommGroupCarrier _) _ f ↔ f.IsSemisimple :=
  @LinearEquiv.isSemisimple_iff K (FGComoduleCat.of (R := K) (C := C) N) _
    (FGComoduleCat.instAddCommGroupCarrier _) _ f N _ _ f (LinearEquiv.refl K N) rfl

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
    exact hg.isSemisimple_basePointsRepresentation (M := K ⊗[k] M)
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
    rw [isSemisimple_pointsAction_iff_basePointsRepresentation,
      Comodule.basePointsRepresentation_baseChangePointsMulEquiv]
    exact (isSemisimple_fgComoduleCatOf_iff (C := K ⊗[k] H) _).mpr <|
      (isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mp hg
        (FGComoduleCat.of (R := k) (C := H) M)

end TauCeti.HopfAlgebra
