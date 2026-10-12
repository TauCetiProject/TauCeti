/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.CentralAugmentation
public import TauCeti.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adjoint-nilpotent elements in central-augmentation quotients

In positive characteristic, a power of the enveloping-algebra generator of an element whose
adjoint action is nilpotent lies in every prescribed power of the central augmentation ideal.
Consequently, any associative target killing such an ideal power sends that generator to a
nilpotent element. Its left-regular representation also acts nilpotently.

These conclusions hold for the quotient by any power of the central augmentation ideal. They
require neither a finite-dimensional separating quotient nor a nilpotent Lie algebra. When a
quotient over a field is finite-dimensional and separates the Lie algebra, its left-regular
action gives a faithful representation that preserves adjoint nilpotence.

The quotient-nilpotence argument follows G. Hochschild, *An Addition to Ado's Theorem*,
Proceedings of the American Mathematical Society **17** (1966), 531–533.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- In exponential characteristic `p ≠ 1`, if a ring homomorphism kills a power of the central
augmentation ideal, then it sends every adjoint-nilpotent Lie element to a nilpotent element. -/
theorem isNilpotent_map_ι_of_isNilpotent_ad {A : Type w} [Semiring A]
    (p : ℕ) [ExpChar R p] (hp : p ≠ 1)
    (q : U →+* A) (n : ℕ)
    (hq : ∀ z ∈ HopfIdeal.centralAugmentationIdeal R U ^ n, q z = 0)
    {x : L} (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    IsNilpotent (q (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  obtain ⟨e, he⟩ :=
    exists_pow_mul_ι_mem_centralAugmentationIdeal_pow_of_isNilpotent_ad p hp hx
  refine ⟨p ^ e * n, ?_⟩
  rw [← map_pow]
  exact hq _ (he n)

variable {A : Type w} [Ring A] [Algebra R A]

/-- In exponential characteristic `p ≠ 1`, every adjoint-nilpotent Lie element has nilpotent
image in the quotient by the `n`-th power of the central augmentation ideal. -/
theorem isNilpotent_quotient_ι_of_isNilpotent_ad (p : ℕ) [ExpChar R p] (hp : p ≠ 1)
    (n : ℕ) {x : L} (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    IsNilpotent (Ideal.Quotient.mk (HopfIdeal.centralAugmentationIdeal R U ^ n)
      (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  exact isNilpotent_map_ι_of_isNilpotent_ad R L p hp
    (Ideal.Quotient.mkₐ R (HopfIdeal.centralAugmentationIdeal R U ^ n)).toRingHom n
    (fun z hz => Ideal.Quotient.eq_zero_iff_mem.mpr hz) hx

/-- In exponential characteristic `p ≠ 1`, the left-regular Lie representation of such a target
acts nilpotently on every adjoint-nilpotent Lie element. -/
theorem isNilpotent_leftRegularRep_of_isNilpotent_ad (p : ℕ) [ExpChar R p] (hp : p ≠ 1)
    (q : U →ₐ[R] A) (n : ℕ)
    (hq : ∀ z ∈ HopfIdeal.centralAugmentationIdeal R U ^ n, q z = 0)
    {x : L} (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    IsNilpotent (LieHom.leftRegularRep
      (((q : U →ₗ⁅R⁆ A).comp (_root_.UniversalEnvelopingAlgebra.ι R))) x) := by
  exact (LieHom.isNilpotent_leftRegularRep_iff _ _).2
    (isNilpotent_map_ι_of_isNilpotent_ad R L p hp q.toRingHom n hq hx)

/-- In exponential characteristic `p ≠ 1`, the left-regular representation on the quotient by
the `n`-th power of the central augmentation ideal sends every adjoint-nilpotent Lie element to
a nilpotent endomorphism. -/
theorem isNilpotent_quotient_leftRegularRep_of_isNilpotent_ad
    (p : ℕ) [ExpChar R p] (hp : p ≠ 1) (n : ℕ)
    {x : L} (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    IsNilpotent (LieHom.leftRegularRep
      ((((Ideal.Quotient.mkₐ R (HopfIdeal.centralAugmentationIdeal R U ^ n)) :
        U →ₗ⁅R⁆ U ⧸ (HopfIdeal.centralAugmentationIdeal R U ^ n)).comp
        (_root_.UniversalEnvelopingAlgebra.ι R))) x) := by
  exact isNilpotent_leftRegularRep_of_isNilpotent_ad R L p hp
    (Ideal.Quotient.mkₐ R (HopfIdeal.centralAugmentationIdeal R U ^ n)) n
    (fun z hz => Ideal.Quotient.eq_zero_iff_mem.mpr hz) hx

end TauCeti.UniversalEnvelopingAlgebra
