/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import TauCeti.Algebra.Ring.IsFormallyReal
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# Group algebras over formally real rings are reduced

Let `R` be a formally real commutative semiring, such as `ℕ`, `ℤ`, `ℚ` or `ℝ`, and let `G` be a
commutative group. Inversion on `G` induces the ring involution `σ` of `R[G]` with
`σ x g = x g⁻¹`. The coefficient of the identity in `x * σ x` is the sum of the squares of the
coefficients of `x` (`MonoidAlgebra.coeff_mul_mapDomainRingEquiv_inv_one`), so it vanishes only
when `x = 0`.

If `x ^ 2 = 0`, then `y = x * σ x` satisfies `y * σ y = x ^ 2 * σ x ^ 2 = 0`, so `y = 0` and then
`x = 0`. Hence `R[G]` is reduced (`MonoidAlgebra.isReduced_of_isFormallyReal`). No finiteness of
`G` is needed, and `G` may have torsion: for instance `ℤ[G]` is reduced for every commutative
group `G`. Over any coefficient semiring `R` without additive torsion, positive integers are
non-zero-divisors of `R[M]` for every monoid `M` (`MonoidAlgebra.natCast_mem_nonZeroDivisors`).

## References

* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977: the trace-form argument
  for semiprimeness of group algebras in characteristic zero.
-/

public section

open scoped nonZeroDivisors

namespace MonoidAlgebra

section Group

variable {R G : Type*} [CommSemiring R] [CommGroup G]

/-- The coefficient of the identity in `x * σ x`, where `σ x` is the image of `x` under the
involution induced by inversion, is the sum of the squares of the coefficients of `x`. -/
@[to_additive (dont_translate := R) coeff_mul_mapDomainRingEquiv_neg_zero
/-- The coefficient of zero in `x * σ x`, where `σ x` is the image of `x` under the involution
induced by negation, is the sum of the squares of the coefficients of `x`. -/]
theorem coeff_mul_mapDomainRingEquiv_inv_one (x : MonoidAlgebra R G) :
    (x * mapDomainRingEquiv R (MulEquiv.inv G) x).coeff 1 =
      ∑ g ∈ x.coeff.support, x.coeff g * x.coeff g := by
  simp [coeff_mul_apply_left, Finsupp.sum]

variable [IsFormallyReal R]

@[to_additive (dont_translate := R) eq_zero_of_coeff_mul_mapDomainRingEquiv_neg_zero]
private theorem eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one {x : MonoidAlgebra R G}
    (h : (x * mapDomainRingEquiv R (MulEquiv.inv G) x).coeff 1 = 0) : x = 0 := by
  classical
  rw [coeff_mul_mapDomainRingEquiv_inv_one] at h
  ext g
  by_cases hg : g ∈ x.coeff.support
  · rw [← Finset.add_sum_erase _ _ hg] at h
    exact IsFormallyReal.eq_zero_of_mul_self_eq_zero <|
      IsFormallyReal.eq_zero_of_add_right (.mul_self _) (.sum_mul_self _ _) h
  · simpa using hg

/-- The group algebra of a commutative group over a formally real commutative semiring is
reduced. -/
@[to_additive (dont_translate := R)
/-- The group algebra of a commutative additive group over a formally real commutative semiring
is reduced. -/]
instance isReduced_of_isFormallyReal : IsReduced (MonoidAlgebra R G) := by
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro x hx
  have hσ (z : MonoidAlgebra R G) :
      mapDomainRingEquiv R (MulEquiv.inv G) (mapDomainRingEquiv R (MulEquiv.inv G) z) = z := by
    ext; simp
  -- `y = x * σ x` satisfies `y * σ y = x ^ 2 * σ x ^ 2 = 0`, so `y = 0`.
  have hy : x * mapDomainRingEquiv R (MulEquiv.inv G) x = 0 := by
    refine eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one ?_
    rw [map_mul, hσ]
    generalize mapDomainRingEquiv R (MulEquiv.inv G) x = y
    simp [show x * y * (y * x) = x ^ 2 * y ^ 2 by ring, hx]
  exact eq_zero_of_coeff_mul_mapDomainRingEquiv_inv_one (by simp [hy])

end Group

/-- Positive integers are non-zero-divisors of a monoid algebra over a semiring without additive
torsion. -/
@[to_additive (dont_translate := R)
/-- Positive integers are non-zero-divisors of an additive monoid algebra over a semiring without
additive torsion. -/]
theorem natCast_mem_nonZeroDivisors {R M : Type*} [Semiring R] [IsAddTorsionFree R] [Monoid M]
    {n : ℕ} (hn : n ≠ 0) : (n : MonoidAlgebra R M) ∈ (MonoidAlgebra R M)⁰ := by
  have key (x : MonoidAlgebra R M) (hx : n • x = 0) : x = 0 := by
    ext m
    exact (nsmul_eq_zero_iff_right hn).mp (by
      simpa only [coeff_smul_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
        congr(($hx).coeff m))
  exact ⟨fun x hx ↦ key x (by rwa [nsmul_eq_mul]), fun x hx ↦ key x (by rwa [nsmul_eq_mul'])⟩

end MonoidAlgebra
