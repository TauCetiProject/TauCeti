/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic

/-!
# Zero divisors in twisted monoid algebras

A twisted monoid algebra over a monoid with unique products has no zero divisors whenever
its scalar semiring has none. In particular, the based quantum torus of a free abelian
lattice over a commutative domain ring is a domain, including at finite-order parameters.
This is the algebraic input to constructing its fraction division ring.

The coefficient formula is stated using the existing monomial basis. At a uniquely
represented product of support elements, the coefficient is the product of the two
coefficients times the factor-set unit, so it cannot vanish.

The unique-product argument adapts `MonoidAlgebra.coeff_mul_mul_of_uniqueMul` and the
`NoZeroDivisors` instance in `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` to the table of
`TwistedMonoidAlgebra.of`. No ordering or finite generation of the monoid is required.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Monoid G]
  {α : G → G → kˣ} [IsFactorSet α]

/-- The coefficients of a product are the twisted convolution of the two coefficient families. -/
theorem repr_mul (f g : twistedMonoidAlgebra k G α) :
    (basis k G α).repr (f * g) =
      ((basis k G α).repr f).sum fun a r ↦
        ((basis k G α).repr g).sum fun b s ↦
          Finsupp.single (a * b) (r * s * (α a b : k)) := by
  classical
  conv_lhs =>
    rw [← (basis k G α).linearCombination_repr f, ← (basis k G α).linearCombination_repr g]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, basis_apply, of_mul_of]
  simp only [← basis_apply k G α, Module.Basis.repr_self, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [mul_one, mul_assoc, mul_left_comm]

/-- At a uniquely represented product of support elements, twisted convolution has one term. -/
theorem repr_mul_apply_of_uniqueMul {f g : twistedMonoidAlgebra k G α} {a b : G}
    (h : UniqueMul ((basis k G α).repr f).support ((basis k G α).repr g).support a b) :
    (basis k G α).repr (f * g) (a * b) =
      (basis k G α).repr f a * (basis k G α).repr g b * (α a b : k) := by
  classical
  rw [repr_mul]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [← Finset.sum_product']
  refine (Finset.sum_eq_single (a, b) ?_ ?_).trans (ite_eq_left rfl)
  · intro p hp hpne
    rw [Finset.mem_product] at hp
    exact ite_eq_right fun he ↦ hpne (Prod.ext (h hp.1 hp.2 he).1 (h hp.1 hp.2 he).2)
  · intro hab
    simp only [Finset.mem_product, not_and_or] at hab
    rcases hab with ha | hb
    · simp [Finsupp.notMem_support_iff.mp ha]
    · simp [Finsupp.notMem_support_iff.mp hb]

/-- A unit-valued twist does not introduce zero divisors on a unique-product monoid. -/
instance [NoZeroDivisors k] [UniqueProds G] :
    NoZeroDivisors (twistedMonoidAlgebra k G α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    contrapose! hfg
    have hf : ((basis k G α).repr f).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hfg.1)
    have hg : ((basis k G α).repr g).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hfg.2)
    obtain ⟨a, ha, b, hb, hab⟩ := UniqueProds.uniqueMul_of_nonempty hf hg
    have : Nontrivial k := ⟨⟨(basis k G α).repr f a, 0, Finsupp.mem_support_iff.mp ha⟩⟩
    intro heq
    have hc := repr_mul_apply_of_uniqueMul hab
    rw [heq, map_zero, Finsupp.zero_apply] at hc
    exact (mul_ne_zero (mul_ne_zero (Finsupp.mem_support_iff.mp ha)
      (Finsupp.mem_support_iff.mp hb)) (α a b).ne_zero) hc.symm

/-- A twisted monoid algebra over a domain ring and a unique-product monoid is a domain. -/
instance {R : Type*} [CommRing R] [IsDomain R] [UniqueProds G]
    {β : G → G → Rˣ} [IsFactorSet β] : IsDomain (twistedMonoidAlgebra R G β) := by
  have : Nontrivial (twistedMonoidAlgebra R G β) :=
    (basis R G β).repr.symm.injective.nontrivial
  exact NoZeroDivisors.to_isDomain (twistedMonoidAlgebra R G β)

end TauCeti.TwistedMonoidAlgebra
