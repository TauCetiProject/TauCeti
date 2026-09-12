/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Comap
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Reduction
import TauCeti.RingTheory.FiniteType.Tensor.Product

/-!
# Smoothness of the derived subgroup

Over an algebraically closed field, the derived closed subgroup of a reduced finite-type
affine group is reduced, and hence smooth. This supplies the smooth subgroup needed when
applying representation-theoretic induction to the derived subgroup of a solvable group.

The reduction of the derived subgroup is again a closed subgroup. The commutator morphism
factors through this reduction because its source, the product of the ambient group with
itself, is reduced. Minimality of the derived subgroup then identifies it with its reduction.
Neither connectedness nor solvability is needed for this argument. The reducedness argument
works over any commutative base when the ambient tensor square and the tensor square
of the reduced derived coordinate ring are reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, for derived algebraic groups, and §1.f,
  for reduction of group schemes.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

/-- The derived closed subgroup has reduced coordinate ring over a commutative base
if the ambient tensor square and the tensor square of the reduced derived coordinate ring
are reduced. -/
theorem isReduced_quotient_derivedDefiningIdeal_of_isReduced_tensorProduct
    {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{v} R)
    [IsReduced (H ⊗[R] H)]
    [IsReduced
      ((quotient H (derivedDefiningIdeal H) ⧸ nilradical (quotient H (derivedDefiningIdeal H))) ⊗[R]
        (quotient H (derivedDefiningIdeal H) ⧸ nilradical (quotient H (derivedDefiningIdeal H))))] :
    IsReduced (quotient H (derivedDefiningIdeal H)) := by
  let _ : IsReduced R := isReduced_of_injective (algebraMap R (H ⊗[R] H))
    (Bialgebra.algebraMap_injective (H ⊗[R] H))
  let I := derivedDefiningIdeal (R := R) H
  let D := quotient H I
  let q := (mkQuotient H I).hom
  let J := (HopfIdeal.reduction R D).comapOfSurjective q (mkQuotient_surjective H I)
  -- The commutator kills the reduction's defining ideal since its target algebra is reduced.
  have hJI : J ≤ I := by
    apply (le_derivedDefiningIdeal_iff H J).mpr
    intro x hx
    have hnil : IsNilpotent (q x) :=
      (HopfIdeal.mem_reduction R D).mp
        (HopfIdeal.mem_comapOfSurjective.mp (HopfIdeal.mem_toIdeal.mp hx))
    obtain ⟨n, hn⟩ := hnil
    have hxn : x ^ n ∈ I :=
      (mkQuotient_eq_zero_iff H I (x ^ n)).mp ((map_pow q x n).trans hn)
    have hzero := derivedDefiningIdeal_toIdeal_le_ker (R := R) H
      (HopfIdeal.mem_toIdeal.mpr hxn)
    rw [RingHom.mem_ker] at hzero ⊢
    have hnil : IsNilpotent
        ((HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom x) :=
      ⟨n, by simpa only [map_pow] using hzero⟩
    exact hnil.eq_zero
  have hred : HopfIdeal.reduction R D = ⊥ :=
    eq_bot_of_comapOfSurjective_le _ hJI
  exact nilradical_eq_bot_iff.mp (by
    simpa only [HopfIdeal.reduction_toIdeal, HopfIdeal.bot_toIdeal] using
      congrArg HopfIdeal.toIdeal hred)

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : _root_.CommHopfAlgCat.{v} k) [Algebra.FiniteType k H] [IsReduced H]

/-- The derived closed subgroup of a reduced finite-type affine group over an algebraically
closed field has reduced coordinate ring. -/
theorem isReduced_quotient_derivedDefiningIdeal :
    IsReduced (quotient H (derivedDefiningIdeal H)) := by
  let D := quotient H (derivedDefiningIdeal H)
  -- Establish reducedness before inferring it for the tensor square: the Hopf reduction
  -- quotient theorem already requires that tensor square to be reduced.
  let _ : IsReduced (D ⧸ nilradical D) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  exact isReduced_quotient_derivedDefiningIdeal_of_isReduced_tensorProduct H

/-- The derived closed subgroup of a reduced finite-type affine group over an algebraically
closed field is smooth. -/
theorem smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal :
    smoothCommHopfAlgProperty k (quotient H (derivedDefiningIdeal H)) := by
  let _ := isReduced_quotient_derivedDefiningIdeal H
  exact smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _

end TauCeti.CommHopfAlgCat
