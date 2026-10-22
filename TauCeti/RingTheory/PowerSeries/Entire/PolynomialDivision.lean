/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Division

/-!
# Entire division by polynomials with invertible leading coefficient

An entire series has a unique entire quotient and a polynomial remainder of degree less than
the divisor whenever the divisor's leading coefficient is invertible. Normalising the divisor
by that coefficient reduces the construction to `PowerSeries.divByMonic`; the coefficient norm
need not be multiplicative, and the coefficient ring may have nilpotents.

This extends monic entire division to the polynomial factors with invertible leading
coefficient that occur when normalising an entire series to have constant coefficient one.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  Appendix A3.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedCommRing R] [CompleteSpace R]
  {f : R⟦X⟧} {p : Polynomial R}

/-- An entire series admits division by a polynomial with invertible leading coefficient,
with entire quotient and polynomial remainder of degree less than the divisor. No ultrametric
hypothesis is needed for existence. -/
theorem exists_entire_mul_add_eq (hf : f.IsEntire) (hp : IsUnit p.leadingCoeff)
    [Nontrivial R] :
    ∃ (q : R⟦X⟧) (b : Polynomial R),
      q.IsEntire ∧ b.degree < p.degree ∧ (p : R⟦X⟧) * q + b = f := by
  let u := hp.unit
  let P : Polynomial R := u⁻¹ • p
  have hP : P.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp
  have hdeg : P.degree = p.degree :=
    Polynomial.degree_smul_of_smul_regular p (IsSMulRegular.all _)
  have hcoe : (P : R⟦X⟧) = u⁻¹ • (p : R⟦X⟧) := by
    simp [P, Units.smul_def]
  refine ⟨u⁻¹ • f.divByMonic P, f.modByMonic P,
    (hf.divByMonic P).smul _, ?_, ?_⟩
  · rw [← hdeg]
    exact PowerSeries.degree_modByMonic_lt f hP.ne_zero
  · rw [mul_smul_comm, ← smul_mul_assoc, ← hcoe, add_comm]
    exact hf.modByMonic_add_divByMonic hP

variable [IsUltrametricDist R] [NormOneClass R]

/-- Entire quotients and polynomial remainders of degree less than a polynomial with invertible
leading coefficient are unique, over a complete ultrametric norm-one ring. -/
theorem eq_and_eq_of_entire_mul_add_eq (hp : IsUnit p.leadingCoeff)
    {q q' : R⟦X⟧} {b b' : Polynomial R} (hq : q.IsEntire) (hq' : q'.IsEntire)
    (hb : b.degree < p.degree) (hb' : b'.degree < p.degree)
    (h : (p : R⟦X⟧) * q + b = f) (h' : (p : R⟦X⟧) * q' + b' = f) :
    q = q' ∧ b = b' := by
  let u := hp.unit
  let P : Polynomial R := u⁻¹ • p
  have hP : P.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp
  have hdeg : P.degree = p.degree :=
    Polynomial.degree_smul_of_smul_regular p (IsSMulRegular.all _)
  have hcoe : (P : R⟦X⟧) = u⁻¹ • (p : R⟦X⟧) := by
    simp [P, Units.smul_def]
  have hdiv (x : R⟦X⟧) : (P : R⟦X⟧) * (u • x) = (p : R⟦X⟧) * x := by
    rw [hcoe, smul_mul_smul_comm, inv_mul_cancel, one_smul]
  have h₁ := PowerSeries.divByMonic_modByMonic_unique (f := f) (u • q) b hP (hq.smul _)
    ⟨by rw [hdiv, add_comm]; exact h, hdeg.symm ▸ hb⟩
  have h₂ := PowerSeries.divByMonic_modByMonic_unique (f := f) (u • q') b' hP (hq'.smul _)
    ⟨by rw [hdiv, add_comm]; exact h', hdeg.symm ▸ hb'⟩
  exact ⟨(MulAction.injective u) (h₁.1.symm.trans h₂.1), h₁.2.symm.trans h₂.2⟩

/-- **Entire division by a polynomial with invertible leading coefficient.** Over a complete
ultrametric norm-one ring, every entire series has exactly one decomposition as the divisor
times an entire quotient plus a polynomial remainder of smaller degree. This includes constant
unit divisors, whose remainders are zero. -/
theorem existsUnique_entire_mul_add_eq (hf : f.IsEntire) (hp : IsUnit p.leadingCoeff) :
    ∃! qb : R⟦X⟧ × Polynomial R,
      qb.1.IsEntire ∧ qb.2.degree < p.degree ∧ (p : R⟦X⟧) * qb.1 + qb.2 = f := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨q, b, hq, hb, h⟩ := exists_entire_mul_add_eq hf hp
  refine ⟨(q, b), ⟨hq, hb, h⟩, fun qb ⟨hq', hb', h'⟩ ↦ ?_⟩
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_entire_mul_add_eq hp hq' hq hb' hb h' h
  rfl

end TauCeti.PowerSeries
