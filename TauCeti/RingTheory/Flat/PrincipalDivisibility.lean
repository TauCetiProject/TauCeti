/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.RingTheory.Ideal.PrincipalIntersection

import Mathlib.Data.Fin.VecNotation

/-!
# Simultaneous scalar divisibility in flat modules

If `(p) ∩ (q) = (pq)` in a commutative ring, simultaneous divisibility by `p` and `q` in a
flat module is divisibility by `pq`. The scalar ring can have zero divisors, and the module
need not be faithful. Both the elementwise and submodule statements are proved here.

The proof uses the equational criterion for flatness on the relation `p • m = q • n`.
Every resulting scalar syzygy lies in the given principal-ideal intersection. Factoring
these finitely many scalar syzygies and summing constructs the module cofactor without any
cancellation. This also gives divisibility in a flat, possibly noncommutative algebra,
whose structure map is central. Powers follow from the separate domain intersection theorem.

## References

* The Stacks Project, [Tag 00HK](https://stacks.math.columbia.edu/tag/00HK), the equational
  criterion for flatness, supplied by Mathlib.
-/

public section

open scoped Pointwise

namespace Module.Flat

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Flat R M] {p q : R}

/-- A relation between multiples of two scalars in a flat module has its common value
divisible by their product whenever the principal-ideal intersection is that product.
Neither scalar has to be regular, and the module need not be faithful. -/
theorem exists_mul_smul_eq_of_smul_eq
    (h : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q})
    {m n : M} (hmn : p • m = q • n) : ∃ t : M, (p * q) • t = p • m := by
  classical
  have hrel : ∑ i : Fin 2, (![p, -q] i) • (![m, n] i) = 0 := by
    simpa [Fin.sum_univ_two, ← sub_eq_add_neg] using sub_eq_zero.mpr hmn
  obtain ⟨k, a, v, hv, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero hrel
  have hcoef (j : Fin k) : p * a 0 j = q * a 1 j := by
    have hj := ha j
    simpa [Fin.sum_univ_two, ← sub_eq_add_neg, sub_eq_zero] using hj
  have hfactor (j : Fin k) : ∃ c : R, p * a 0 j = (p * q) * c := by
    apply Ideal.mem_span_singleton.mp
    rw [← h]
    exact ⟨Ideal.mem_span_singleton.mpr ⟨a 0 j, rfl⟩,
      Ideal.mem_span_singleton.mpr ⟨a 1 j, hcoef j⟩⟩
  choose c hc using hfactor
  refine ⟨∑ j, c j • v j, ?_⟩
  symm
  calc
    p • m = ∑ j, (p * a 0 j) • v j := by
      rw [show m = ∑ j, a 0 j • v j from by simpa using hv 0, Finset.smul_sum]
      simp only [mul_smul]
    _ = ∑ j, ((p * q) * c j) • v j := by simp_rw [hc]
    _ = (p * q) • ∑ j, c j • v j := by simp only [Finset.smul_sum, mul_smul]

/-- Simultaneous scalar divisibility in a flat module is divisibility by the product, under
the principal-ideal intersection hypothesis. -/
theorem exists_mul_smul_eq_iff
    (h : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q}) (z : M) :
    (∃ t : M, (p * q) • t = z) ↔ (∃ m : M, p • m = z) ∧ ∃ n : M, q • n = z := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨q • t, (mul_smul p q t).symm⟩,
      ⟨p • t, by rw [mul_comm p q, mul_smul]⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    obtain ⟨t, ht⟩ := exists_mul_smul_eq_of_smul_eq h (hm.trans hn.symm)
    exact ⟨t, ht.trans hm⟩

/-- Images of two scalar multiplications intersect in the image of their product in a flat
module, whenever the same equality holds for their principal ideals. -/
theorem smul_top_inf_smul_top_eq_mul_smul_top
    (h : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q}) :
    p • (⊤ : Submodule R M) ⊓ q • ⊤ = (p * q) • ⊤ := by
  ext z
  simpa only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and] using (exists_mul_smul_eq_iff h z).symm

/-- The powered principal-ideal intersection theorem transports to every flat module over
a domain, including zero exponents. -/
theorem pow_smul_top_inf_pow_smul_top_eq_mul_smul_top [IsDomain R]
    (h : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q}) (r s : ℕ) :
    p ^ r • (⊤ : Submodule R M) ⊓ q ^ s • ⊤ = (p ^ r * q ^ s) • ⊤ :=
  smul_top_inf_smul_top_eq_mul_smul_top (Ideal.inf_span_singleton_pow_eq_span_singleton_mul h r s)

section Algebra

variable {A : Type*} [Ring A] [Algebra R A] [Flat R A]

/-- In a flat algebra the two central scalar factors divide an element exactly when their
product does. The algebra need not be commutative or have no zero divisors. -/
theorem algebraMap_mul_dvd_iff
    (h : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q}) (z : A) :
    algebraMap R A (p * q) ∣ z ↔ algebraMap R A p ∣ z ∧ algebraMap R A q ∣ z := by
  simpa only [dvd_def, eq_comm, Algebra.smul_def] using exists_mul_smul_eq_iff h z

end Algebra

end Module.Flat
