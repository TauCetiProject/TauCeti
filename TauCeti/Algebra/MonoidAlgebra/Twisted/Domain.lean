/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic

/-!
# Domains from twisted monoid algebras

A unit-valued twist does not change the unique-product argument for absence of zero divisors:
a uniquely represented product of supported monomials has a nonzero coefficient. We prove this
for arbitrary monoids with `UniqueProds`, over commutative semirings without zero divisors.
Over a domain ring, the resulting twisted monoid algebra is a domain. In particular this applies
to twisted group algebras of free abelian groups, such as based quantum tori, without any
restriction on the order of the scalar parameter.

The coefficient formulas use the existing monomial basis, rather than a second presentation of
the twisted algebra. The proof follows the unique-product argument in Mathlib's
`MonoidAlgebra.coeff_mul_mul_of_uniqueMul` and its `NoZeroDivisors` instance, with the additional
unit factor from the twist.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

open Module

variable {R G : Type*} [CommSemiring R] [Monoid G]
  {α : G → G → Rˣ} [IsFactorSet α]

/-- The coefficient of a product is the twisted convolution of its coefficients in the
monomial basis. -/
theorem repr_mul [DecidableEq G] (f g : twistedMonoidAlgebra R G α) (c : G) :
    (basis R G α).repr (f * g) c =
      ((basis R G α).repr f).sum fun a r ↦
        ((basis R G α).repr g).sum fun b s ↦
          if a * b = c then r * s * (α a b : R) else 0 := by
  classical
  conv_lhs => rw [← (basis R G α).linearCombination_repr f,
    ← (basis R G α).linearCombination_repr g]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_mul, Finsupp.mul_sum,
    smul_mul_smul_comm, map_finsuppSum, map_smul, basis_apply, of_mul_of, smul_smul]
  simp only [← basis_apply R G α, Basis.repr_self, Finsupp.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_zero, mul_one]
  exact Finsupp.sum_comm _ _ _

/-- If a supported product exponent has a unique representation, its coefficient is the
product of the two coefficients and the twisting unit. The selected exponents need not
belong to the supports: then both sides vanish. -/
theorem repr_mul_mul_of_uniqueMul {f g : twistedMonoidAlgebra R G α} {a₀ b₀ : G}
    (h : UniqueMul ((basis R G α).repr f).support ((basis R G α).repr g).support a₀ b₀) :
    (basis R G α).repr (f * g) (a₀ * b₀) =
      (basis R G α).repr f a₀ * (basis R G α).repr g b₀ * (α a₀ b₀ : R) := by
  classical
  rw [repr_mul]
  simp_rw [Finsupp.sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (a₀, b₀) ?_ ?_).trans (ite_eq_left rfl)
  · intro ab hab hne
    simp only [Finset.mem_product] at hab
    exact ite_eq_right fun he ↦ hne (Prod.ext (h hab.1 hab.2 he).1 (h hab.1 hab.2 he).2)
  · intro hnot
    simp only [Finset.mem_product, not_and_or] at hnot
    rcases hnot with ha | hb
    · simp [Finsupp.notMem_support_iff.mp ha]
    · simp [Finsupp.notMem_support_iff.mp hb]

/-- A unit-valued twist preserves absence of zero divisors over a unique-product monoid. -/
instance [NoZeroDivisors R] [UniqueProds G] :
    NoZeroDivisors (twistedMonoidAlgebra R G α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    by_contra h
    obtain ⟨hf, hg⟩ := not_or.mp h
    have hf' : ((basis R G α).repr f).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis R G α).repr.injective).mpr hf)
    have hg' : ((basis R G α).repr g).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis R G α).repr.injective).mpr hg)
    obtain ⟨a, ha, b, hb, hab⟩ := UniqueProds.uniqueMul_of_nonempty hf' hg'
    have hn : (basis R G α).repr (f * g) (a * b) ≠ 0 := by
      rw [repr_mul_mul_of_uniqueMul hab]
      rw [ne_eq, (α a b).mul_left_eq_zero]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp ha) (Finsupp.mem_support_iff.mp hb)
    exact hn (by simp [hfg])

/-- The twisted algebra is nontrivial whenever the coefficient semiring is nontrivial. -/
instance [Nontrivial R] : Nontrivial (twistedMonoidAlgebra R G α) :=
  (basis R G α).repr.symm.injective.nontrivial

/-- A twisted monoid algebra over a domain ring is a domain if the monoid has unique products.
This requires neither commutativity of the monoid nor an infinite-order twist. -/
instance {R : Type*} [CommRing R] [IsDomain R] {α : G → G → Rˣ} [IsFactorSet α]
    [UniqueProds G] : IsDomain (twistedMonoidAlgebra R G α) :=
  NoZeroDivisors.to_isDomain (twistedMonoidAlgebra R G α)

/-! Twisted lattice algebras, including arbitrary-rank lattices and rank zero. -/

example {I : Type*} {R : Type*} [CommRing R] [IsDomain R]
    (α : Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ) [IsFactorSet α] :
    IsDomain (twistedMonoidAlgebra R (Multiplicative (I →₀ ℤ)) α) := inferInstance

example {R : Type*} [CommRing R] [IsDomain R]
    (α : Multiplicative (Empty →₀ ℤ) → Multiplicative (Empty →₀ ℤ) → Rˣ) [IsFactorSet α] :
    IsDomain (twistedMonoidAlgebra R (Multiplicative (Empty →₀ ℤ)) α) := inferInstance

end TauCeti.TwistedMonoidAlgebra
