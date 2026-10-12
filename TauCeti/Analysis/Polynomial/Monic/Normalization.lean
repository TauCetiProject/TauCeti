/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import TauCeti.RingTheory.Polynomial.Monic.Normalization

/-!
# Analytic monic normalization across degree drops

For an analytic coefficient family `F` and a fixed degree `d`, form the monic polynomial with
lower coefficients `(F x).coeff i * (F x).coeff d ^ (d - 1 - i)`. Its coefficients are analytic
even where the leading coefficient of `F` vanishes. At every nonzero degree-`d` fiber this
polynomial is the integral normalization of `F x`; its roots are scaled by the leading
coefficient and its discriminant has the corresponding normalization factor.

This reduces nonmonic analytic polynomial families to monic families without dividing by a
possibly vanishing leading coefficient. In particular, when the leading coefficient and the
discriminant are powers of a distinguished parameter times analytic units, the normalized
discriminant has the same form away from the exceptional hyperplane. A monic root theorem can
then be applied to the normalized family and its roots rescaled on the punctured domain.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Polynomial

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {S : Set E} {F : E → 𝕜[X]} {d : ℕ}

/-- An analytic coefficient family has an analytic monic normalization of any fixed degree `d`.
It agrees with integral normalization at each nonzero degree-`d` fiber. The normalized family
remains analytic at points
where the original degree drops. No openness or finite-dimensionality assumption is needed. -/
theorem exists_analytic_monic_normalization
    (hF : ∀ i ≤ d, AnalyticOnNhd 𝕜 (fun x ↦ (F x).coeff i) S) :
    ∃ Q : E → 𝕜[X],
      (∀ x, (Q x).Monic ∧ (Q x).natDegree = d) ∧
      (∀ i, AnalyticOnNhd 𝕜 (fun x ↦ (Q x).coeff i) S) ∧
      ∀ x, (F x).natDegree = d → F x ≠ 0 →
        Q x = (F x).integralNormalization := by
  let Q := fun x ↦ Polynomial.monicOfCoeff
    (fun i : Fin d ↦ (F x).coeff i * (F x).coeff d ^ (d - 1 - i))
  have hQ (x : E) : (Q x).Monic ∧ (Q x).natDegree = d :=
    ⟨Polynomial.monic_monicOfCoeff _, Polynomial.natDegree_monicOfCoeff _⟩
  refine ⟨Q, hQ, fun i x hx ↦ ?_, fun x hd hf ↦ ?_⟩
  · rcases lt_trichotomy i d with hi | hi | hi
    · have heq : (fun x ↦ (Q x).coeff i) =
          fun x ↦ (F x).coeff i * (F x).coeff d ^ (d - 1 - i) := by
        funext x
        exact Polynomial.coeff_monicOfCoeff _ ⟨i, hi⟩
      rw [heq]
      exact (hF i hi.le x hx).mul ((hF d le_rfl x hx).pow _)
    · subst i
      have heq : (fun x ↦ (Q x).coeff d) = fun _ ↦ 1 := by
        funext x
        rw [← (hQ x).2, (hQ x).1.coeff_natDegree]
      rw [heq]
      exact analyticAt_const
    · have heq : (fun x ↦ (Q x).coeff i) = fun _ ↦ 0 := by
        funext x
        exact coeff_eq_zero_of_natDegree_lt ((hQ x).2 ▸ hi)
      rw [heq]
      exact analyticAt_const
  · have hlc : (F x).coeff d = (F x).leadingCoeff := by rw [← hd, coeff_natDegree]
    simp only [Q, hlc]
    exact Polynomial.monicOfCoeff_mul_pow_eq_integralNormalization hf hd

end TauCeti
