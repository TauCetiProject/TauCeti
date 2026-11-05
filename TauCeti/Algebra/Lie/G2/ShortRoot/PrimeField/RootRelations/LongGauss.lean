/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.LongGauss
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Long-root Gauss factorization in the G₂ carrier over 𝔽₃

The opposite long simple-root subgroups of the carrier generated over `𝔽₃` satisfy the
rank-one Gauss relation, in both multiplication orders. The lower-root, coroot, upper-root
parameters are uniquely determined. The formulas hold on points over arbitrary commutative
`𝔽₃`-algebras, not only fields or reduced rings.

Transfer uses the existing matrix comparisons with the integral seven-dimensional carrier;
it does not identify the generated prime-field carrier with the specialization of the
integral toral closure, or with an independently pinned simply connected group.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.

The formal inputs are the integral relations in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootRelations.LongGauss` and the matrix
comparisons in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe v

variable (A : Type v) [CommRing A] [Algebra (ZMod 3) A]

/-- The long-simple-root Gauss relation in the carrier generated over `𝔽₃`, with only
`1 + a * b` required to be a unit. -/
theorem rootSubgroupPoints_inl_one_mul_inr_one (a b : A) (z : Aˣ)
    (hz : (z : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * (↑z⁻¹ : A))) *
        weightTorusPoints A (Pi.mulSingle 1 z) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * (↑z⁻¹ : A))) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg (fun g : IntegralToralClosure.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 7) A))
      (IntegralToralClosure.rootSubgroupPoints_inl_one_mul_inr_one A a b z hz)

/-- The three long-root Gauss parameters are uniquely determined, also over nonreduced
`𝔽₃`-algebras. -/
@[simp↓]
theorem rootSubgroupPoints_inl_one_mul_inr_one_eq_iff (a b c d : A) (z : Aˣ) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd c) *
        weightTorusPoints A (Pi.mulSingle 1 z) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd d) ↔
      (z : A) = 1 + a * b ∧ c = b * (↑z⁻¹ : A) ∧ d = a * (↑z⁻¹ : A) := by
  have h := IntegralToralClosure.rootSubgroupPoints_inl_one_mul_inr_one_eq_iff A a b c d z
  rw [← Subtype.coe_inj] at h ⊢
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using h

/-- In the opposite multiplication order, the long-root Gauss relation uses the inverse
simple-coroot parameter. -/
theorem rootSubgroupPoints_inr_one_mul_inl_one (a b : A) (z : Aˣ)
    (hz : (z : A) = 1 + a * b) :
    rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (b * (↑z⁻¹ : A))) *
        weightTorusPoints A (Pi.mulSingle 1 z⁻¹) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (a * (↑z⁻¹ : A))) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints] using
    congrArg (fun g : IntegralToralClosure.points A =>
      (g : Matrix.GeneralLinearGroup (Fin 7) A))
      (IntegralToralClosure.rootSubgroupPoints_inr_one_mul_inl_one A a b z hz)

end TauCeti.G2ShortRoot.PrimeField
