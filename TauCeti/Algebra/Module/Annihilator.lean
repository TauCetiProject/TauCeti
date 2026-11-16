/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import TauCeti.LinearAlgebra.TensorProduct.Torsion

/-!
# Annihilators in exact sequences and tensor products

If ideals `I` and `J` annihilate the outer terms of an exact sequence, their product
annihilates the middle term. If powers `Iᵃ` and `Jᵇ` annihilate two modules, the power
`(I + J)^(a + b - 1)` annihilates their tensor product. If either exponent is zero,
its corresponding factor is already zero.
These bounds provide closure under extensions and tensor products for modules with
power-annihilated support. Neither finiteness nor flatness is required.

For finitely generated ideals, power-annihilation depends only on the radical.
The uniform power containment is the algebra behind radical independence of formal support.

## References

* The Stacks Project, Tag 00L6.
-/

public section

open scoped TensorProduct

namespace LinearMap

variable {R M N P : Type*} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- The product of annihilating ideals of the outer terms of an exact sequence annihilates
its middle term. The maps need not be injective or surjective. -/
theorem mul_le_annihilator_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) {I J : Ideal R}
    (hI : I ≤ Module.annihilator R M) (hJ : J ≤ Module.annihilator R P) :
    I * J ≤ Module.annihilator R N := by
  refine Ideal.mul_le.mpr fun a ha b hb ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  obtain ⟨y, hy⟩ := (h (b • x)).mp (by rw [map_smul, Module.mem_annihilator.mp (hJ hb)])
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (hI ha), map_zero]

end LinearMap

namespace Module

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- If `Iᵃ` kills `M` and `Jᵇ` kills `N`, then `(I + J)^(a + b - 1)` kills their tensor
product. This also holds for zero exponents, when the corresponding factor is zero. -/
theorem sup_pow_le_annihilator_tensorProduct {I J : Ideal R} {a b : ℕ}
    (hM : I ^ a ≤ annihilator R M) (hN : J ^ b ≤ annihilator R N) :
    (I ⊔ J) ^ (a + b - 1) ≤ annihilator R (M ⊗[R] N) := by
  have hleft : I ^ a ≤ annihilator R (M ⊗[R] N) := fun r hr ↦
    mem_annihilator.mpr (TauCeti.isTorsionBy_tensorProduct_left
      (N := N) (mem_annihilator.mp (hM hr)))
  have hright : J ^ b ≤ annihilator R (M ⊗[R] N) := fun r hr ↦
    mem_annihilator.mpr (TauCeti.isTorsionBy_tensorProduct_right
      (M := M) (mem_annihilator.mp (hN hr)))
  -- Every monomial in the binomial expansion contains either `Iᵃ` or `Jᵇ`.
  rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  refine Finset.sup_le fun i _ ↦ ?_
  by_cases hi : a ≤ i
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hi).trans hleft))
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right (by omega)).trans hright))

end Module

namespace Ideal

/-- Finitely generated ideals with equal radicals define the same power-annihilated
modules, including modules which are not finite. -/
theorem exists_pow_le_annihilator_iff_of_radical_eq {R : Type*} [CommSemiring R]
    {I J : Ideal R} (hI : I.FG) (hJ : J.FG) (h : I.radical = J.radical)
    (M : Type*) [AddCommMonoid M] [Module R M] :
    (∃ n : ℕ, 0 < n ∧ I ^ n ≤ Module.annihilator R M) ↔
      ∃ n : ℕ, 0 < n ∧ J ^ n ≤ Module.annihilator R M := by
  have transfer {I J : Ideal R} (hJ : J.FG) (hJI : J ≤ I.radical)
      (hM : ∃ n : ℕ, 0 < n ∧ I ^ n ≤ Module.annihilator R M) :
      ∃ n : ℕ, 0 < n ∧ J ^ n ≤ Module.annihilator R M := by
    obtain ⟨n, hn, hM⟩ := hM
    obtain ⟨k, hk⟩ := exists_pow_le_of_le_radical_of_fg hJI hJ
    refine ⟨(k + 1) * n, Nat.mul_pos (Nat.succ_pos k) hn, ?_⟩
    rw [pow_mul]
    exact (pow_right_mono ((pow_le_pow_right (Nat.le_succ k)).trans hk) n).trans hM
  exact ⟨transfer hJ (h ▸ le_radical), transfer hI (h.symm ▸ le_radical)⟩

end Ideal
