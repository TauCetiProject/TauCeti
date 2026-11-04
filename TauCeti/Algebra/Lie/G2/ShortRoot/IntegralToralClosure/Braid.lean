/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# The six-factor braid relation in the short-root G₂ carrier

The rank-one root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy
`(n₀ n₁)³ = (n₁ n₀)³` over every commutative ring. This is the length-six braid
relation of the numbered G₂ diagram, retaining the signs of the pinned lifts rather
than passing to their Weyl-group classes. The calculation takes place over the integers
and then specializes, so it also applies in characteristics two and three and over
nonreduced rings.

The carrier is the integral toral closure of the seven-dimensional short-root module.
This relation does not identify it with an independently pinned group scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups* (1968), §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The matrices and divided-square normalization are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open Multiplicative

private def rankOneMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i)) *
    (1 - rootMatrix (.inr i) + rootDividedSquareMatrix (.inr i)) *
      (1 + rootMatrix (.inl i) + rootDividedSquareMatrix (.inl i))

private theorem rankOneMatrix_braid :
    (rankOneMatrix 0 * rankOneMatrix 1) ^ 3 =
      (rankOneMatrix 1 * rankOneMatrix 0) ^ 3 := by
  simp only [rankOneMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr, raisingMatrix, loweringMatrix]
  decide +kernel

private theorem coe_rankOneWord (A : Type*) [CommRing A] (i : Fin 2) :
    (((rootSubgroupPoints (.inl i) A (ofAdd 1) *
        rootSubgroupPoints (.inr i) A (ofAdd (-1)) *
          rootSubgroupPoints (.inl i) A (ofAdd 1) : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (Int.castRingHom A).mapMatrix (rankOneMatrix i) := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints, toAdd_ofAdd,
    one_smul, neg_one_smul, one_pow, neg_one_sq]
  simp only [rankOneMatrix, map_mul, map_add, map_sub, map_one]
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom, sub_eq_add_neg]

/-- The pinned rank-one root words of the seven-dimensional G₂ carrier satisfy the
length-six braid relation over every commutative ring. The representatives themselves,
not just their classes modulo the torus, occur in this equality. -/
theorem rootSubgroupPoints_braid (A : Type*) [CommRing A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (ofAdd 1) *
        rootSubgroupPoints (.inr i) A (ofAdd (-1)) *
          rootSubgroupPoints (.inl i) A (ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  let n := fun i : Fin 2 =>
    rootSubgroupPoints (.inl i) A (ofAdd 1) *
      rootSubgroupPoints (.inr i) A (ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (ofAdd 1)
  let ρ : points A →* Matrix (Fin 7) (Fin 7) A :=
    (Units.coeHom _).comp (points A).subtype
  have hn (i : Fin 2) : ρ (n i) = (Int.castRingHom A).mapMatrix (rankOneMatrix i) :=
    coe_rankOneWord A i
  have h : ρ ((n 0 * n 1) ^ 3) = ρ ((n 1 * n 0) ^ 3) := by
    rw [map_pow, map_pow, map_mul ρ (n 0) (n 1), map_mul ρ (n 1) (n 0), hn, hn]
    simpa only [map_mul, map_pow] using
      congrArg ((Int.castRingHom A).mapMatrix) rankOneMatrix_braid
  exact (Units.coeHom_injective.comp (points A).subtype_injective) h

end TauCeti.G2ShortRoot.IntegralToralClosure
