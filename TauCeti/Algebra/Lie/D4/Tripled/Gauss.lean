/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Gauss

/-!
# Opposite-root factorization in the tripled D₄ carrier

Opposite numbered simple-root subgroups satisfy the rank-one Gauss relation whenever
`1 + a * b` is a unit. The middle factor is the value of the corresponding simple coroot:
in fundamental-weight coordinates it is the existing weight torus at `Pi.mulSingle i c`.
Both multiplication orders are covered, over arbitrary commutative coefficient rings.

The carrier is not identified here with the independently pinned simply connected D₄ group
scheme. These identities transfer to that group only along such an identification.

## Main results

* `TauCeti.D4Tripled.rootSubgroupPoints_inl_mul_inr`: positive times negative factorization.
* `TauCeti.D4Tripled.rootSubgroupPoints_inr_mul_inl`: negative times positive factorization.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.

The calculation specializes the generic minuscule Gauss factorization in
`TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Gauss` using the root and weight-torus
matrices constructed in `TauCeti.Algebra.Lie.D4.Tripled.GroupScheme`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open DynkinType TauCeti.UniversalEnvelopingAlgebra

variable {A : Type*} [CommRing A]

/-- The Gauss factorization for opposite simple-root points. The unit `c` is `1 + a * b`,
and the middle factor is the `i`-th simple coroot evaluated at `c`. No invertibility
of either root parameter is required. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 4) (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c) *
          rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  apply Units.ext
  simp only [Units.val_mul, coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr,
    toAdd_ofAdd, raisingMatrix_def, loweringMatrix_def, coe_weightTorusPoints,
    kostantTorusMatrix_apply, diagGL_coe, torusCharacter_mulSingle]
  simpa only [weightTable_weight] using
    weightTable.one_add_raising_mul_one_add_lowering i a b c hc

/-- The reverse Gauss factorization. Relative to positive times negative, the simple-coroot
factor is inverted, and the positive root factor comes first. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 4) (a b : A) (c : Aˣ)
    (hc : (c : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑c⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i c⁻¹) *
          rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑c⁻¹)) := by
  have hneg : (c : A) = 1 + (-a) * (-b) := by simpa only [neg_mul_neg] using hc
  have h := congrArg Inv.inv (rootSubgroupPoints_inl_mul_inr i (-a) (-b) c hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv,
    neg_mul, Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.D4Tripled
