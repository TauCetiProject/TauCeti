/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
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
Neither connectedness nor solvability is needed for this argument.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, for derived algebraic groups, and §1.f,
  for reduction of group schemes.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : _root_.CommHopfAlgCat.{v} k) [Algebra.FiniteType k H] [IsReduced H]

/-- The derived closed subgroup of a reduced finite-type affine group over an algebraically
closed field has reduced coordinate ring. -/
theorem isReduced_quotient_derivedDefiningIdeal :
    IsReduced (quotient H (derivedDefiningIdeal H)) := by
  let I := derivedDefiningIdeal (R := k) H
  let D := quotient H I
  let q := (mkQuotient H I).hom
  let _ : IsReduced (D ⧸ nilradical D) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  let J := (HopfIdeal.reduction k D).comap q
  -- The commutator kills the reduction's defining ideal since its target algebra is reduced.
  have hJI : J ≤ I := by
    apply (le_derivedDefiningIdeal_iff H J).mpr
    intro x hx
    have hnil : IsNilpotent (q x) :=
      (HopfIdeal.mem_reduction k D).mp
        (HopfIdeal.mem_comap.mp (HopfIdeal.mem_toIdeal.mp hx))
    obtain ⟨n, hn⟩ := hnil
    have hxn : x ^ n ∈ I :=
      (mkQuotient_eq_zero_iff H I (x ^ n)).mp ((map_pow q x n).trans hn)
    have hzero := derivedDefiningIdeal_toIdeal_le_ker (R := k) H
      (HopfIdeal.mem_toIdeal.mpr hxn)
    rw [RingHom.mem_ker] at hzero ⊢
    have hnil : IsNilpotent
        ((HopfAlgebra.commutatorAlgHom (R := k) (H := H)).toRingHom x) :=
      ⟨n, by simpa only [map_pow] using hzero⟩
    exact hnil.eq_zero
  constructor
  intro x hx
  obtain ⟨y, rfl⟩ := mkQuotient_surjective H I x
  apply (mkQuotient_eq_zero_iff H I y).mpr
  apply hJI
  exact HopfIdeal.mem_comap.mpr ((HopfIdeal.mem_reduction k D).mpr hx)

/-- The derived closed subgroup of a reduced finite-type affine group over an algebraically
closed field is smooth. -/
theorem smooth_quotient_derivedDefiningIdeal :
    smoothCommHopfAlgProperty k (quotient H (derivedDefiningIdeal H)) := by
  let _ := isReduced_quotient_derivedDefiningIdeal H
  exact smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _

end TauCeti.CommHopfAlgCat
