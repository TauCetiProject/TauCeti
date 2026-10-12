/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.ConjugacyClass
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Trace

/-!
# The fixed-trace elliptic contribution

Let `t² - 4n = -D < 0`.  The integral matrices of trace `t` and determinant `n`, modulo
`SL(2, ℤ)`-conjugacy, form the elliptic classes occurring in the Eichler--Selberg trace formula.
Every matrix in this fibre has trace
`(Polynomial.dickson 2 n w).eval t` on the degree-`w` binary forms.  On the other hand, the sum
of the automorphism weights `2 / |Z_SL(M)|` of these classes is `2 H(D)`, by the correspondence
with positive-definite binary quadratic forms.

This file combines those two results.  It is the fixed-trace class-number contribution needed
when the ambient trace of Popa--Zagier's element is grouped by elliptic conjugacy classes.  The
remaining input for that grouping is the separate class-weight identity for the coefficients of
the explicit element.

## Main result

* `TauCeti.finsum_elliptic_binaryForm_trace`: the automorphism-weighted sum of the traces on
  binary forms over all elliptic classes of fixed trace `t` and determinant `n` is
  `2 H(D) P_{w+2}(t,n)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, Sections 1 and 4.
-/

public section

open Matrix MulAction MulOpposite MvPolynomial
open scoped MatrixGroups

namespace TauCeti

variable {t n : ℤ} {D : ℕ} [NeZero D]

/-- **The fixed-trace elliptic contribution.** If `t² - 4n = -D < 0`, then the sum over the
`SL(2, ℤ)`-conjugacy classes of integral matrices of trace `t` and determinant `n` of their
traces on degree-`w` binary forms, weighted by `2 / |Z_SL(M)|`, is
`2 H(D) P_{w+2}(t,n)`.

The representative chosen by `Quotient.out` does not affect the summand: every representative
lies in the fixed trace-and-determinant fibre, so its binary-form trace is the same Dickson value.
The factor `2 / |Z_SL(M)|` is `1 / |\bar\Gamma_M|` after quotienting the modular group by its
central signs. -/
theorem finsum_elliptic_binaryForm_trace {K : Type*} [Field K] [CharZero K]
    (w : ℕ) (h : t ^ 2 - 4 * n = -D) :
    ∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n),
      (2 / (cardStabilizerOnOrbit X : K)) *
        LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
          (binaryFormRep K w (op (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ))) =
      2 * (hurwitzClassNumber D : K) * (Polynomial.dickson 2 (n : K) w).eval (t : K) := by
  classical
  let _ := BinaryQuadraticForm.finite_orbitRel_quotient_traceDetFiber h
  have htrace (X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n)) :
      LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
          (binaryFormRep K w (op (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ))) =
        (Polynomial.dickson 2 (n : K) w).eval (t : K) := by
    rw [trace_binaryFormRep_eq_dickson_eval]
    obtain ⟨ht, hn⟩ := mem_traceDetFiber.1 X.out.2
    rw [ht, hn]
  have hweight :
      ∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n),
          2 / (cardStabilizerOnOrbit X : K) = 2 * (hurwitzClassNumber D : K) := by
    calc
      _ = ∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n),
          algebraMap ℚ K (2 / (cardStabilizerOnOrbit X : ℚ)) := by simp
      _ = algebraMap ℚ K (∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ))
          (traceDetFiber (Fin 2) t n), 2 / (cardStabilizerOnOrbit X : ℚ)) :=
        ((algebraMap ℚ K).toAddMonoidHom.map_finsum
          (f := fun X : orbitRel.Quotient (ConjAct SL(2, ℤ))
            (traceDetFiber (Fin 2) t n) => 2 / (cardStabilizerOnOrbit X : ℚ))
          (Set.toFinite _)).symm
      _ = _ := by
        rw [BinaryQuadraticForm.finsum_traceDetFiber_eq_two_mul_hurwitzClassNumber h]
        simp
  simp_rw [htrace]
  rw [← finsum_mul, hweight]

end TauCeti
