/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The special orthogonal group inside the orthogonal group

The orthogonal group `O(Q)` and the special orthogonal group `SO(Q)` both carry the subspace
topology from the linear automorphism group, whose topology records an automorphism and its
inverse. In this topology the determinant `O(Q) →* Rˣ` is continuous, so its kernel `SO(Q)` is
closed in `O(Q)` over a `T1` ring, and the inclusion `SO(Q) →* O(Q)` is a closed embedding.

When the polar form is left-separating on a finite free module over a domain, every orthogonal
determinant squares to one, so the determinant takes only finitely many values and `SO(Q)` has
finite index in `O(Q)`. Being closed of finite index, it is then also open, and the inclusion is
an open embedding. In particular, for a nondegenerate form over `ℝ` or `ℚ_p`, a compact or open
subgroup of `O(Q)` pulls back to a compact or open subgroup of `SO(Q)`.

Over a Hausdorff topological field with `2` invertible, `SO(Q)` is moreover closed in the linear
automorphism group of a finite-dimensional space, hence locally compact when the field is.

## Main results

* `QuadraticMap.continuous_orthogonalDet`: the determinant on `O(Q)` is continuous.
* `QuadraticMap.isClosed_specialOrthogonalWithin` and
  `QuadraticMap.isClosedEmbedding_specialOrthogonalToOrthogonal`: `SO(Q)` is closed in `O(Q)`.
* `QuadraticMap.isOpen_specialOrthogonalWithin` and
  `QuadraticMap.isOpenEmbedding_specialOrthogonalToOrthogonal`: `SO(Q)` is open in `O(Q)` when
  the polar form is left-separating.
* `TauCeti.QuadraticMap.isClosed_specialOrthogonalGroup`: `SO(Q)` is closed in the linear
  automorphism group.
* `TauCeti.QuadraticMap.instLocallyCompactSpaceSpecialOrthogonalGroup`: `SO(Q)` is locally compact
  over a locally compact field.
-/

public section

namespace TauCeti

namespace QuadraticMap

section Ring

variable {R M N : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N] (Q : QuadraticMap R M N)

/-- The determinant `O(Q) →* Rˣ` is continuous. -/
@[fun_prop]
theorem _root_.QuadraticMap.continuous_orthogonalDet :
    Continuous (_root_.QuadraticMap.orthogonalDet Q) :=
  (continuous_linearEquiv_det.comp continuous_subtype_val).congr fun g ↦
    (_root_.QuadraticMap.orthogonalDet_apply g).symm

variable [T1Space R]

/-- The determinant kernel `SO(Q)` is closed in `O(Q)`. -/
theorem _root_.QuadraticMap.isClosed_specialOrthogonalWithin :
    IsClosed (_root_.QuadraticMap.specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have h : (_root_.QuadraticMap.specialOrthogonalWithin Q : Set (orthogonalGroup Q)) =
      (fun g ↦ (_root_.QuadraticMap.orthogonalDet Q g : R)) ⁻¹' {1} := by
    ext g
    simp [Units.ext_iff]
  rw [h]
  exact isClosed_singleton.preimage
    (Units.continuous_val.comp (_root_.QuadraticMap.continuous_orthogonalDet Q))

/-- The inclusion `SO(Q) →* O(Q)` is a closed embedding. -/
theorem _root_.QuadraticMap.isClosedEmbedding_specialOrthogonalToOrthogonal :
    Topology.IsClosedEmbedding (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) where
  toIsEmbedding := .of_comp (_root_.QuadraticMap.continuous_specialOrthogonalToOrthogonal Q)
    continuous_subtype_val <| by
      convert Topology.IsEmbedding.subtypeVal using 1
      ext g
      simp
  isClosed_range := by
    rw [← MonoidHom.coe_range, _root_.QuadraticMap.range_specialOrthogonalToOrthogonal]
    exact _root_.QuadraticMap.isClosed_specialOrthogonalWithin Q

end Ring

section Domain

variable {R M : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R] [IsTopologicalRing R]
  [T1Space R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {Q : QuadraticForm R M}

/-- If the polar form is left-separating on a finite free module over a domain, then `SO(Q)` is
open in `O(Q)`, being a closed subgroup of finite index. -/
theorem _root_.QuadraticMap.isOpen_specialOrthogonalWithin (hQ : Q.polarBilin.SeparatingLeft) :
    IsOpen (_root_.QuadraticMap.specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have := finiteIndex_specialOrthogonalWithin hQ
  exact (_root_.QuadraticMap.specialOrthogonalWithin Q).isOpen_of_isClosed_of_finiteIndex
    (_root_.QuadraticMap.isClosed_specialOrthogonalWithin Q)

/-- If the polar form is left-separating on a finite free module over a domain, then the inclusion
`SO(Q) →* O(Q)` is an open embedding. -/
theorem _root_.QuadraticMap.isOpenEmbedding_specialOrthogonalToOrthogonal
    (hQ : Q.polarBilin.SeparatingLeft) :
    Topology.IsOpenEmbedding (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) where
  toIsEmbedding := (_root_.QuadraticMap.isClosedEmbedding_specialOrthogonalToOrthogonal Q).1
  isOpen_range := by
    rw [← MonoidHom.coe_range, _root_.QuadraticMap.range_specialOrthogonalToOrthogonal]
    exact _root_.QuadraticMap.isOpen_specialOrthogonalWithin hQ

end Domain

section Field

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The special orthogonal group of a finite-dimensional quadratic space over a Hausdorff
topological field in which `2` is invertible is closed in the linear automorphism group. -/
theorem isClosed_specialOrthogonalGroup :
    IsClosed (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  have h : (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) =
      (orthogonalGroup Q : Set (V ≃ₗ[K] V)) ∩
        (fun g : V ≃ₗ[K] V ↦ (LinearEquiv.det g : K)) ⁻¹' {1} := by
    ext g
    simp [Units.ext_iff]
  rw [h]
  exact (isClosed_orthogonalGroup Q).inter <| isClosed_singleton.preimage
    (Units.continuous_val.comp continuous_linearEquiv_det)

/-- The special orthogonal group of a finite-dimensional quadratic space over a Hausdorff locally
compact topological field in which `2` is invertible is locally compact. -/
instance instLocallyCompactSpaceSpecialOrthogonalGroup [LocallyCompactSpace K] :
    LocallyCompactSpace (specialOrthogonalGroup Q) :=
  (isClosed_specialOrthogonalGroup Q).locallyCompactSpace

end Field

end QuadraticMap

end TauCeti
