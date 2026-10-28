/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.ClosedFactors
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Commutative
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# The unique maximal torus of a commutative affine group

Let `H` be the coordinate Hopf algebra of a reduced commutative affine group of finite type over
an algebraically closed field. Its closed semisimple factor, cut out by the kernel of the regular
semisimple projection `semisimplePartBialgHom`, contains every reduced closed subgroup all of
whose points are semisimple, and in particular every torus. When the group is connected, the
semisimple factor is itself a torus, so it is the unique maximal torus.

In coordinates, containment of closed subgroups is reverse inclusion of Hopf ideals: the
statements below say that the kernel of the semisimple projection lies in every Hopf ideal
cutting out such a subgroup.

These results build on the regular projection `semisimplePartBialgHom`, its closed factor from
`TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.ClosedFactors`, and the
diagonalizability criterion
`DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint`.

Reducedness of the smaller subgroup cannot be dropped. In characteristic `p`, the subgroup `αₚ`
of the additive group has only the identity point, which is semisimple, while the semisimple
factor of the additive group is trivial.

## Main declarations

* `TauCeti.HopfAlgebra.Point.ker_semisimplePartBialgHom_le_of_isSemisimplePoint`: a reduced closed
  subgroup whose points are semisimple lies in the semisimple factor.
* `TauCeti.HopfAlgebra.Point.ker_semisimplePartBialgHom_le_of_torus`: every torus lies in the
  semisimple factor.
* `TauCeti.HopfAlgebra.Point.isMaximalTorus_ker_semisimplePartBialgHom`: for a connected group, the
  semisimple factor is a maximal torus.
* `TauCeti.HopfAlgebra.Point.isMaximalTorus_iff_eq_ker_semisimplePartBialgHom`: for a connected
  group, it is the only maximal torus.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §4.7.
* T. A. Springer, *Linear Algebraic Groups*, §3.1 and §6.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.HopfAlgebra.Point

universe u

variable (k H : Type u) [Field k] [IsAlgClosed k] [CommRing H]
  [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Coalgebra.IsCocomm k H]

/-- **The semisimple factor contains every reduced closed subgroup of semisimple points.** If a
Hopf ideal `J` is radical and every base-field point of the quotient `H ⧸ J` is semisimple, then
`J` contains the kernel of the regular semisimple projection. -/
theorem ker_semisimplePartBialgHom_le_of_isSemisimplePoint {J : HopfIdeal k H}
    (hJ : J.toIdeal.IsRadical)
    (hss : ∀ g : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) J →ₐ[k] k),
      IsSemisimplePoint g) :
    HopfIdeal.ker (semisimplePartBialgHom k H) ≤ J := by
  have _ : IsReduced (H ⧸ J.toIdeal) := (Ideal.isRadical_iff_quotient_reduced _).mp hJ
  intro x hx
  rw [HopfIdeal.mem_ker] at hx
  rw [← HopfIdeal.mem_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun f ↦ ?_
  -- The ambient point `f ∘ mk` is semisimple, hence fixed by the semisimple projection, which
  -- kills `x`.
  have hg := (mapDomain_semisimplePartBialgHom_eq_self_iff _).mpr
    ((hss (toConv f)).mapDomain (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom)
  have hx' := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv x) hg
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    hx, map_zero] at hx'
  rw [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk] at hx'
  rw [← hx', map_zero]

/-- **Every torus lies in the semisimple factor.** A Hopf ideal cutting out a torus contains the
kernel of the regular semisimple projection. -/
theorem ker_semisimplePartBialgHom_le_of_torus {J : HopfIdeal k H}
    (hJ : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J)) :
    HopfIdeal.ker (semisimplePartBialgHom k H) ≤ J := by
  have _ := hJ.geometricallyReduced.isReduced
  refine ker_semisimplePartBialgHom_le_of_isSemisimplePoint k H
    ((Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance) ?_
  exact ((DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint
    _).mp ((hJ.split k).groupLikeSpanned k _)).2

/-- **The semisimple factor of a connected commutative affine group is a maximal torus.** -/
theorem isMaximalTorus_ker_semisimplePartBialgHom
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom k H)) :=
  (HopfIdeal.isMaximalTorus_iff k _ _).mpr ⟨torusCommHopfAlgProperty_semisimpleFactor k H hH,
    fun _ hJ _ ↦ ker_semisimplePartBialgHom_le_of_torus k H hJ⟩

/-- **A connected commutative affine group has a unique maximal torus**, its semisimple factor. -/
theorem isMaximalTorus_iff_eq_ker_semisimplePartBialgHom
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (J : HopfIdeal k H) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J ↔
      J = HopfIdeal.ker (semisimplePartBialgHom k H) := by
  refine ⟨fun hJ ↦ ?_, fun h ↦ h ▸ isMaximalTorus_ker_semisimplePartBialgHom k H hH⟩
  obtain ⟨hT, hmax⟩ := (HopfIdeal.isMaximalTorus_iff k (_root_.CommHopfAlgCat.of k H) J).mp hJ
  have hle := ker_semisimplePartBialgHom_le_of_torus k H hT
  exact le_antisymm (hmax _ (torusCommHopfAlgProperty_semisimpleFactor k H hH) hle) hle

end TauCeti.HopfAlgebra.Point
