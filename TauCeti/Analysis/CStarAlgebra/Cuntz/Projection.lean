/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Projection
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Subequivalence

/-!
# Cuntz subequivalence of projections

For projections `p` and `q` of a C⋆-algebra, Murray–von Neumann subequivalence implies Cuntz
subequivalence (`TauCeti.cuntzLE_of_star_mul_self_eq_of_mul_star_self_le`): if some `v` has
`v⋆v = p` and `vv⋆ ≤ q`, then `v` is a partial isometry with `vv⋆ = q vv⋆`, so
`v⋆ q v = v⋆ (vv⋆) v = p` exhibits `p` as an element `x⋆ q x`. Murray–von Neumann equivalent
projections are therefore mutually Cuntz subequivalent
(`TauCeti.antisymmRel_cuntzLE_of_star_mul_self_eq_of_mul_star_self_eq`).

The converse, that Cuntz subequivalence of projections gives a partial isometry `v` with `v⋆v = p`
and `vv⋆ ≤ q` (Rørdam, §4.1), is not in this file.

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Murray–von Neumann subequivalence implies Cuntz subequivalence.** For projections `p` and
`q`, if some `v` has `v⋆v = p` and `vv⋆ ≤ q`, then `p ≼ q`, realized exactly as `p = v⋆ q v`. -/
theorem cuntzLE_of_star_mul_self_eq_of_mul_star_self_le {p q v : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hv : star v * v = p) (hvq : v * star v ≤ q) :
    CuntzLE ⟨p, hp.nonneg⟩ ⟨q, hq.nonneg⟩ := by
  have hpi : IsPartialIsometry v :=
    isPartialIsometry_iff_isStarProjection_star_mul_self.2 (hv ▸ hp)
  have hqe : q * (v * star v) = v * star v :=
    (hpi.isStarProjection_mul_star_self.le_iff_mul_eq_right hq).1 hvq
  have hvqv : star v * q * v = p := by
    calc star v * q * v = star v * q * (v * star v * v) := by rw [hpi.mul_star_mul_self]
      _ = star v * (q * (v * star v)) * v := by simp only [mul_assoc]
      _ = star v * v * (star v * v) := by rw [hqe]; simp only [mul_assoc]
      _ = p := by rw [hv, hp.isIdempotentElem.eq]
  convert cuntzLE_star_mul_mul v ⟨q, hq.nonneg⟩ using 2
  exact hvqv.symm

/-- **Murray–von Neumann equivalent projections are mutually Cuntz subequivalent.** -/
theorem antisymmRel_cuntzLE_of_star_mul_self_eq_of_mul_star_self_eq {p q v : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hv : star v * v = p)
    (hv' : v * star v = q) : AntisymmRel CuntzLE (⟨p, hp.nonneg⟩ : {a : A // 0 ≤ a})
      ⟨q, hq.nonneg⟩ :=
  ⟨cuntzLE_of_star_mul_self_eq_of_mul_star_self_le hp hq hv hv'.le,
    cuntzLE_of_star_mul_self_eq_of_mul_star_self_le hq hp (by rwa [star_star]) (by
      rw [star_star, hv])⟩

end TauCeti
