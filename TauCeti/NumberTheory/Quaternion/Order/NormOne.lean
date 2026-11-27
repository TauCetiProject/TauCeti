/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Quaternion.Order.Basic
public import TauCeti.RingTheory.IntegralOrder.Star.Unitary

/-!
# Reduced-norm-one groups of quaternion orders

The reduced-norm-one elements of an order form a subgroup of Mathlib's `unitary` group of the
ambient quaternion algebra. Over a ring with finite quotients any two such groups have finite
relative index. For nested orders, the smaller norm-one group therefore has finite index in
the larger one. In particular this applies to orders over the ring of integers of a number field.

The finite-index proof clears denominators to find a nonzero scalar `r` with `r • Γ ⊆ Λ`.
The kernel of reduction from `Γ¹` to the units of the finite ring `Γ / rΓ` lies in `Λ¹`.

## References

* J. Voight, *Quaternion algebras*, §38.1.5 and §38.3.1.
-/

public section

open scoped Quaternion

namespace TauCeti.IntegralOrder.IsOrder

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]
  [IsFractionRing R F] [IsIntegrallyClosed R] {c₁ c₂ c₃ : F}
  [alg : Algebra R ℍ[F,c₁,c₂,c₃]]
  [tower : @IsScalarTower R F ℍ[F,c₁,c₂,c₃] _ _ alg.toSMul]
  {Λ : Subalgebra R ℍ[F,c₁,c₂,c₃]}

/-- The reduced-norm-one group of a quaternion order, as a subgroup of the ambient norm-one
group. Inversion is quaternion conjugation, which preserves the order. -/
def normOne (hΛ : IsOrder F Λ) : Subgroup (unitary ℍ[F,c₁,c₂,c₃]) :=
  (StarOrder.ofSubalgebra Λ hΛ fun _ hx => hΛ.star_mem hx).unitarySubgroup

/-- An ambient reduced-norm-one element belongs to the order's norm-one group exactly when its
underlying quaternion belongs to the order. -/
@[simp]
theorem mem_normOne (hΛ : IsOrder F Λ) {x : unitary ℍ[F,c₁,c₂,c₃]} :
    x ∈ hΛ.normOne ↔ (x : ℍ[F,c₁,c₂,c₃]) ∈ Λ := by
  rw [normOne, StarOrder.mem_unitarySubgroup, StarOrder.mem_ofSubalgebra]

variable {Γ : Subalgebra R ℍ[F,c₁,c₂,c₃]}

/-- Inclusion of quaternion orders induces inclusion of their reduced-norm-one groups. -/
theorem normOne_mono (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) (h : Λ ≤ Γ) :
    hΛ.normOne ≤ hΓ.normOne := by
  unfold normOne
  apply StarOrder.unitarySubgroup_mono
  rwa [← StarOrder.toSubalgebra_le_toSubalgebra, StarOrder.ofSubalgebra_toSubalgebra,
    StarOrder.ofSubalgebra_toSubalgebra]

/-- **Any two orders have norm-one groups of finite relative index.** This holds over any
integrally closed ring with fraction field and finite quotients, including rings of integers of
number fields. -/
theorem normOne_isFiniteRelIndex [Ring.HasFiniteQuotients R]
    (hΛ : IsOrder F Λ) (hΓ : IsOrder F Γ) :
    hΛ.normOne.IsFiniteRelIndex hΓ.normOne := by
  unfold normOne
  exact StarOrder.unitarySubgroup_isFiniteRelIndex _ _

end TauCeti.IntegralOrder.IsOrder
