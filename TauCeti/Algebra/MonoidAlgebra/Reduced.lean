/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.MapDomain
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
group `G`.

## References

* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977: the trace-form argument
  for semiprimeness of group algebras in characteristic zero.
-/

public section

namespace MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [IsFormallyReal R] [CommGroup G]

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

end MonoidAlgebra
