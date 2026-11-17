/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Non-zero-divisors and domain instances for twisted monoid algebras

When `G` satisfies `UniqueProds G`, every pair of nonempty finite subsets of `G` has `(g₁, g₂)` with
a uniquely formed product `g₁ * g₂`. Since every factor-set value `α g₁ g₂` is a unit of `k`,
the `g₁ * g₂`-coordinate of `x * y` in `TauCeti.twistedMonoidAlgebra k G α` is `α g₁ g₂` times the
product of coordinates at `g₁` and `g₂` (`TauCeti.TwistedMonoidAlgebra.repr_mul_of_uniqueMul`), so
`twistedMonoidAlgebra k G α` inherits `NoZeroDivisors`, multiplicative cancellation, and `IsDomain`
from `k`. Via `TauCeti.Algebra.Group.UniqueProds.TorsionFree`, this applies automatically to twisted
lattice algebras `twistedMonoidAlgebra k (Multiplicative L) α` for `[AddCancelCommMonoid L]
[HasUniqueDiv L]`.

## Main results

* `TauCeti.TwistedMonoidAlgebra.repr_mul_of_uniqueMul`: coordinate formula at a `UniqueMul` pair.
* `TauCeti.TwistedMonoidAlgebra.instNoZeroDivisors`,
  `TauCeti.TwistedMonoidAlgebra.instIsLeftCancelMulZero`,
  `TauCeti.TwistedMonoidAlgebra.instIsRightCancelMulZero`,
  `TauCeti.TwistedMonoidAlgebra.instIsCancelMulZero`,
  `TauCeti.TwistedMonoidAlgebra.instIsDomain`: `UniqueProds G` transfers non-zero-divisor,
  cancellation, and domain instances from `k` to `twistedMonoidAlgebra k G α`.

## Attribution

`repr_mul_of_uniqueMul` and the erase-induction cancellation proofs adapt
`MonoidAlgebra.coeff_mul_mul_of_uniqueMul` and the `UniqueProds` instances in
`Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` (by Damiano Testa) to twisted monoid algebras.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Monoid G] {α : G → G → kˣ} [IsFactorSet α]

/-- At a `UniqueMul` pair `(g₁, g₂)` for the basis supports of `x` and `y`, the `g₁ * g₂`-coordinate
of `x * y` is `(α g₁ g₂ : k)` times the product of coordinates at `g₁` and `g₂`. -/
theorem repr_mul_of_uniqueMul {x y : twistedMonoidAlgebra k G α} {g₁ g₂ : G}
    (h : UniqueMul ((basis k G α).repr x).support ((basis k G α).repr y).support g₁ g₂) :
    (basis k G α).repr (x * y) (g₁ * g₂) =
      (α g₁ g₂ : k) * ((basis k G α).repr x g₁ * (basis k G α).repr y g₂) := by
  classical
  rw [repr_mul_apply]
  simp_rw [Finsupp.sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (g₁, g₂) ?_ ?_).trans (ite_eq_left rfl) <;>
    simp_rw [Finset.mem_product]
  · refine fun ab hab hne ↦ ite_eq_right fun he ↦ hne <| Prod.ext ?_ ?_
    exacts [(h hab.1 hab.2 he).1, (h hab.1 hab.2 he).2]
  · refine fun hnotMem ↦ ite_eq_right_iff.mpr fun _ ↦ ?_
    rcases not_and_or.mp hnotMem with hx | hy
    · rw [Finsupp.notMem_support_iff.mp hx, zero_mul, mul_zero]
    · rw [Finsupp.notMem_support_iff.mp hy, mul_zero, mul_zero]

instance instNoZeroDivisors [NoZeroDivisors k] [UniqueProds G] :
    NoZeroDivisors (twistedMonoidAlgebra k G α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    contrapose! hxy
    obtain ⟨g₁, hg₁, g₂, hg₂, h⟩ := UniqueProds.uniqueMul_of_nonempty
      (Finsupp.support_nonempty_iff.mpr ((basis k G α).repr.map_ne_zero_iff.mpr hxy.1))
      (Finsupp.support_nonempty_iff.mpr ((basis k G α).repr.map_ne_zero_iff.mpr hxy.2))
    refine fun h0 ↦ absurd (by simp [h0] : (basis k G α).repr (x * y) (g₁ * g₂) = 0) ?_
    rw [repr_mul_of_uniqueMul h]
    exact mt (α g₁ g₂).mul_right_eq_zero.mp
      (mul_ne_zero (Finsupp.mem_support_iff.mp hg₁) (Finsupp.mem_support_iff.mp hg₂))

private theorem symm_erase_add_smul_of (g : G) (y : twistedMonoidAlgebra k G α) :
    (basis k G α).repr.symm (((basis k G α).repr y).erase g) +
      (basis k G α).repr y g • of g = y :=
  (basis k G α).repr.injective <| by
    rw [map_add, LinearEquiv.apply_symm_apply, map_smul, repr_of, Finsupp.smul_single_one,
      Finsupp.erase_add_single]

instance instIsLeftCancelMulZero [IsCancelAdd k] [IsLeftCancelMulZero k] [UniqueProds G] :
    IsLeftCancelMulZero (twistedMonoidAlgebra k G α) where
  mul_left_cancel_of_ne_zero {x} hx {y₁ y₂} eq := by
    classical
    induction hy : ((basis k G α).repr y₁).support ∪ ((basis k G α).repr y₂).support
      using Finset.eraseInduction generalizing y₁ y₂ with | _ s ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · rw [Finset.union_eq_empty, Finsupp.support_eq_empty, Finsupp.support_eq_empty] at hy
      exact (basis k G α).repr.injective (hy.1.trans hy.2.symm)
    subst hy
    obtain ⟨gx, hgx, gy, hgy, uniq⟩ := UniqueProds.uniqueMul_of_nonempty
      (Finsupp.support_nonempty_iff.mpr ((basis k G α).repr.map_ne_zero_iff.mpr hx)) hs
    have h := repr_mul_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_left)
    dsimp only at eq
    rw [eq, repr_mul_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_right)] at h
    have hcoord := mul_left_cancel₀ (Finsupp.mem_support_iff.mp hgx)
      ((α gx gy).mul_right_inj.mp h.symm)
    rw [← symm_erase_add_smul_of gy y₁, ← symm_erase_add_smul_of gy y₂, hcoord] at eq ⊢
    simp_rw [mul_add, add_right_cancel_iff] at eq
    rw [ih gy hgy eq]; simp [Finset.erase_union_distrib]

instance instIsRightCancelMulZero [IsCancelAdd k] [IsRightCancelMulZero k] [UniqueProds G] :
    IsRightCancelMulZero (twistedMonoidAlgebra k G α) where
  mul_right_cancel_of_ne_zero {x} hx {y₁ y₂} eq := by
    classical
    induction hy : ((basis k G α).repr y₁).support ∪ ((basis k G α).repr y₂).support
      using Finset.eraseInduction generalizing y₁ y₂ with | _ s ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · rw [Finset.union_eq_empty, Finsupp.support_eq_empty, Finsupp.support_eq_empty] at hy
      exact (basis k G α).repr.injective (hy.1.trans hy.2.symm)
    subst hy
    obtain ⟨gy, hgy, gx, hgx, uniq⟩ := UniqueProds.uniqueMul_of_nonempty hs
      (Finsupp.support_nonempty_iff.mpr ((basis k G α).repr.map_ne_zero_iff.mpr hx))
    have h := repr_mul_of_uniqueMul (uniq.mono Finset.subset_union_left subset_rfl)
    dsimp only at eq
    rw [eq, repr_mul_of_uniqueMul (uniq.mono Finset.subset_union_right subset_rfl)] at h
    have hcoord := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hgx)
      ((α gy gx).mul_right_inj.mp h.symm)
    rw [← symm_erase_add_smul_of gy y₁, ← symm_erase_add_smul_of gy y₂, hcoord] at eq ⊢
    simp_rw [add_mul, add_right_cancel_iff] at eq
    rw [ih gy hgy eq]; simp [Finset.erase_union_distrib]

instance instIsCancelMulZero [IsCancelAdd k] [IsCancelMulZero k] [UniqueProds G] :
    IsCancelMulZero (twistedMonoidAlgebra k G α) where

instance instIsDomain [IsCancelAdd k] [IsDomain k] [UniqueProds G] :
    IsDomain (twistedMonoidAlgebra k G α) where

/-! ### Checks -/

example {R L : Type*} [CommRing R] [IsDomain R] [AddCommGroup L] [HasUniqueDiv L]
    (α : Multiplicative L → Multiplicative L → Rˣ) [IsFactorSet α] :
    ∃ (_ : Ring (twistedMonoidAlgebra R (Multiplicative L) α)),
      IsDomain (twistedMonoidAlgebra R (Multiplicative L) α) := ⟨inferInstance, inferInstance⟩

example {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [CancelCommMonoid G] [HasUniqueRoots G]
    (α : G → G → kˣ) [IsFactorSet α] : NoZeroDivisors (twistedMonoidAlgebra k G α) := inferInstance

end TauCeti.TwistedMonoidAlgebra
