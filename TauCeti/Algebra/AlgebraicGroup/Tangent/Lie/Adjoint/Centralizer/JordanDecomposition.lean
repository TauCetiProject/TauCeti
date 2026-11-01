/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Centralizer
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Basic

/-!
# Scheme centralizers and internal Jordan decomposition

For a finite-type affine group in characteristic zero whose Lie algebra has nondegenerate
Killing form, the centralizer of an element is the scheme-theoretic intersection of the
centralizers of its internal nilpotent and semisimple parts. We prove equality of the defining
Hopf ideals, not only equality of complex points. Consequently the comparison holds on points
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
  let a := Derivation.pointInCounitAlgebra (CommAlgCat.of k k) g
  let d := LinearMap.GeneralLinearGroup.toLinearEquiv
    ((Derivation.adRepresentation k).asGroupHom a)
  have hd (v) : d v = Derivation.adDerivation k a v := by
    simp only [d, LinearMap.GeneralLinearGroup.coe_toLinearEquiv]
    rw [Representation.asGroupHom_apply, Derivation.adRepresentation_apply]
  let D : Derivation k H (Bialgebra.CounitAlgebra k H k) ≃ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k) :=
    { d with
      -- The underlying linear equivalence is the adjoint representation at this point.
      map_lie' := fun {v w} ↦ by
        -- The structure field uses the linear-map projection of `d` rather than its coercion.
        change d ⁅v, w⁆ = ⁅d v, d w⁆
        simpa only [hd] using Derivation.adDerivation_lie k a v w }
  have hD (v) : D v = Derivation.adDerivation k a v := hd v
  let c := Derivation.cotangentDualLieEquiv (R := k) (H := H)
  let E := c.trans (D.trans c.symm)
  have hfix (z : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      g ∈ CommHopfAlgCat.quotientPointsSubgroup G (centralizerHopfIdeal H z)
          (CommAlgCat.of k k) ↔ E z = z := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    have hker : (∀ y ∈ centralizerHopfIdeal H z, g.ofConv y = 0) ↔
        (centralizerHopfIdeal H z).toIdeal ≤ RingHom.ker g.ofConv := Iff.rfl
    rw [hker, centralizerHopfIdeal_le_ker_iff]
    rw [← c.injective.eq_iff]
    simp only [E, LieEquiv.trans_apply, LieEquiv.coe_coe, LieEquiv.apply_symm_apply, hD,
      Algebra.ofId_self, Derivation.mapValue_id, LinearMap.id_apply, c,
      Derivation.cotangentDualLieEquiv_apply]
    rfl
  simpa only [Subgroup.mem_inf, hfix] using E.apply_eq_self_iff_jordanParts x

end TauCeti
