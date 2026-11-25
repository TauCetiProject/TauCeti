/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Clearing denominators of multivariate polynomials

Let `R` be a domain with fraction field `E`. A nonzero polynomial over `E` in any family of
variables becomes, after multiplication by a common denominator of its coefficients, a nonzero
polynomial over `R` with the same zero locus on `R`-points
(`MvPolynomial.exists_ne_zero_eval_algebraMap_eq_zero_iff_eval_eq_zero`).
-/

public section

open Set

namespace MvPolynomial

variable (R : Type*) {E ι : Type*} [CommRing R] [IsDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]

/-- **Clearing denominators.** A nonzero polynomial over the fraction field `E` of a domain `R`
has a nonzero multiple over `R` with the same zero locus on `R`-points. -/
theorem exists_ne_zero_eval_algebraMap_eq_zero_iff_eval_eq_zero (P : MvPolynomial ι E)
    (hP : P ≠ 0) :
    ∃ Q : MvPolynomial ι R, Q ≠ 0 ∧
      ∀ x : ι → R, eval (algebraMap R E ∘ x) P = 0 ↔ eval x Q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) P.coeffs
  have hb0 : algebraMap R E b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.prop
  obtain ⟨Q, hQ⟩ : C (algebraMap R E b) * P ∈ range (map (algebraMap R E)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.1 hc
    rw [mem_support_iff, coeff_C_mul] at hm
    rw [coeff_C_mul]
    obtain ⟨a, ha⟩ := hb _ (coeff_mem_coeffs m (right_ne_zero_of_mul hm))
    exact ⟨a, by rw [ha, Algebra.smul_def]⟩
  refine ⟨Q, fun h ↦ ?_, fun x ↦ ?_⟩
  · rw [h, map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hQ
    exact hQ.elim hb0 hP
  · have := congrArg (eval (algebraMap R E ∘ x)) hQ
    have h2 : eval₂ (algebraMap R E) (algebraMap R E ∘ x) Q = algebraMap R E (eval x Q) := by
      rw [eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]
    rw [eval_map, h2, eval_mul, eval_C] at this
    rw [← mul_eq_zero_iff_left hb0, ← this, FaithfulSMul.algebraMap_eq_zero_iff]

end MvPolynomial
