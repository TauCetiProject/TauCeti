/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Center
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Simple
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Proper normal subgroups of the symplectic group

Over a field, every proper reduced closed normal subgroup of the standard symplectic group
is central. In characteristic zero this applies to every closed normal subgroup by Cartier's
theorem. In positive rank the scheme-theoretic center is the group of square roots of unity
(`TauCeti.Symplectic.centerCoordinateIsoGroupAlgebra`).

Over the algebraic closure the group of points of a proper normal subgroup is proper and normal.
The symplectic group over this infinite field is perfect. Its action on projective space shows
that this point subgroup is central. Such matrices are scalar and stay central after every
change of value algebra. Geometric points separate functions on the reduced subgroup, giving
containment of the whole subgroup scheme in the center.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 24, the symplectic groups.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 8.
-/

public section

open WithConv

namespace TauCeti.Symplectic

universe u

variable {k : Type u} [Field k] {m : ℕ} {I : HopfIdeal k (coordinateHopfAlgebra k m)}

/-- Every proper reduced closed normal subgroup of the symplectic group over a field is
scheme-theoretically central. -/
theorem isCentral_of_isNormal_of_isReduced
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I)]
    (hn : I.IsNormal) (hp : I ≠ ⊥) : I.IsCentral := by
  classical
  let K := AlgebraicClosure k
  let H := coordinateHopfAlgebra k m
  let _ : IsReduced H := isReduced_of_smooth k H
  let S := CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K)
  let e := pointsMulEquiv k m (A := K)
  have hS := CommHopfAlgCat.quotientPointsSubgroup_normal H I hn (CommAlgCat.of k K)
  let _ : (S.map e.toMonoidHom).Normal := hS.map _ e.surjective
  have hpS : S ≠ ⊤ := by
    intro ht
    apply hp
    have : IsReduced (CommHopfAlgCat.quotient H (⊥ : HopfIdeal k H)) :=
      (Ideal.isRadical_iff_quotient_reduced (⊥ : Ideal H)).mp (Ideal.isRadical_bot (R := H))
    exact le_bot_iff.mp (HopfIdeal.le_of_quotientPointsSubgroup_le (K := K) (J := ⊥) (I := I)
      (le_top.trans ht.ge))
  have hpM : S.map e.toMonoidHom ≠ ⊤ := fun ht ↦
    hpS (Subgroup.map_injective e.injective (ht.trans (Subgroup.map_equiv_top e).symm))
  obtain ⟨a, ha⟩ := ({0, 1, -1} : Finset K).exists_notMem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  have hperfect := GLSymplecticFin.commutator_eq_top (m := m) ha.1
    (fun h ↦ (sq_eq_one_iff.mp h).elim ha.2.1 ha.2.2)
  have hcenter := GLSymplecticFin.le_center_of_normal_of_ne_top hperfect _ hpM
  apply (CommHopfAlgCat.centerDefiningIdeal_le_iff H I).mp
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro g hg
  apply (CommHopfAlgCat.mem_centerPointsSubgroup_iff H (CommAlgCat.of k K) g).mpr
  exact (isCentralPoint_iff_mem_center_pointsMulEquiv m g).mpr
    (hcenter (Subgroup.mem_map_of_mem e.toMonoidHom hg))

/-- In characteristic zero every proper closed normal subgroup of the symplectic group is
scheme-theoretically central. -/
theorem isCentral_of_isNormal_of_charZero [CharZero k] (hn : I.IsNormal) (hp : I ≠ ⊥) :
    I.IsCentral := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I
  let _ : Algebra.Smooth k Q :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k Q)
  let _ : IsReduced Q := isReduced_of_smooth k Q
  exact isCentral_of_isNormal_of_isReduced hn hp

end TauCeti.Symplectic
