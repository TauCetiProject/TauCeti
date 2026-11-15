/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Centralizer
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# Scheme centralizers and internal Jordan decomposition

For a finite-type affine group in characteristic zero whose Lie algebra has nondegenerate
Killing form, the centralizer of an element is the scheme-theoretic intersection of the
centralizers of its internal nilpotent and semisimple parts. We prove equality of the defining
Hopf ideals, not only equality of `k`-points. Consequently the comparison holds on points
valued in arbitrary commutative algebras, including nonreduced ones.

The proof uses equivariance of the internal Jordan decomposition for the actual adjoint point
automorphisms. Cartier's theorem makes the closed subgroups reduced, so geometric points
separate their defining ideals.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §15.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.4.
-/

public section

namespace TauCeti

open WithConv
open TauCeti.LieAlgebra

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [_root_.LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

attribute [local instance] Derivation.adjointComodule

/-- The centralizer of an element is the scheme-theoretic intersection of the centralizers
of its internal Jordan parts. A join of Hopf ideals represents an intersection of subgroups. -/
theorem centralizerHopfIdeal_eq_sup_jordanParts
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x = centralizerHopfIdeal H (nilpotentPart k x) ⊔
      centralizerHopfIdeal H (semisimplePart k x) := by
  let G := _root_.CommHopfAlgCat.of k H
  let : IsReduced (G ⧸ (centralizerHopfIdeal H x).toIdeal) :=
    HopfAlgebra.isReduced_of_charZero k _
  let : IsReduced (G ⧸ (centralizerHopfIdeal H (nilpotentPart k x) ⊔
      centralizerHopfIdeal H (semisimplePart k x)).toIdeal) :=
    HopfAlgebra.isReduced_of_charZero k _
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (H := G) (K := k)
  rw [CommHopfAlgCat.quotientPointsSubgroup_sup]
  ext g
  let c := Derivation.cotangentDualLieEquiv (R := k) (H := H)
  let E := c.trans ((Derivation.adDerivationLieEquiv k
    (Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g)).trans c.symm)
  simp only [Subgroup.mem_inf]
  rw [mem_quotientPointsSubgroup_centralizerHopfIdeal_iff x g,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff (nilpotentPart k x) g,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff (semisimplePart k x) g]
  simpa only [E, c, LieEquiv.trans_apply] using E.apply_eq_self_iff_jordanParts x

end TauCeti
