/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.ConjugacyClass
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Trace

/-!
# The fixed-trace split contribution

Let `a ≠ d` be integers. The integer matrices of trace `a + d` and determinant `a d`, modulo
`SL(2, ℤ)`-conjugacy, are the classes with distinct integer eigenvalues `a` and `d` occurring in
the Eichler–Selberg trace formula; for `a d > 0` they are the split hyperbolic classes. Every
matrix in this fibre has trace `(Polynomial.dickson 2 (a d) w).eval (a + d)` on the degree-`w`
binary forms. On the other hand there are exactly `|d - a|` conjugacy classes, represented by the
matrices `!![a, b; 0, d]` with `0 ≤ b < |d - a|`, and each has automorphism weight
`2 / |Z_SL(M)| = 1`.

This file combines those two results. It is the split counterpart of the elliptic contribution
`TauCeti.finsum_elliptic_binaryForm_trace`, for grouping the ambient trace of Popa–Zagier's
element by conjugacy classes. By `TauCeti.dickson_two_eval_add_mul_sub`, the contribution
`|d - a| P_{w+2}(a + d, a d)` is `d ^ (w + 1) - a ^ (w + 1)` when `a < d`.

## Main result

* `TauCeti.finsum_splitHyperbolic_binaryForm_trace`: the automorphism-weighted sum of the traces
  on binary forms over all conjugacy classes of trace `a + d` and determinant `a d` is
  `|d - a| P_{w+2}(a + d, a d)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4.
-/

public section

open Matrix MulAction MulOpposite MvPolynomial
open scoped MatrixGroups

namespace TauCeti

variable {a d : ℤ}

/-- **The fixed-trace split contribution.** If `a ≠ d`, the sum over the `SL(2, ℤ)`-conjugacy
classes of integer matrices of trace `a + d` and determinant `a d` of their traces on degree-`w`
binary forms, weighted by `2 / |Z_SL(M)|`, is `|d - a| P_{w+2}(a + d, a d)`.

The representative chosen by `Quotient.out` does not affect the summand: every representative
lies in the fixed trace-and-determinant fibre, so its binary-form trace is the same Dickson value.
Every weight `2 / |Z_SL(M)|` is `1`, and there are `|d - a|` classes. -/
theorem finsum_splitHyperbolic_binaryForm_trace {K : Type*} [Field K] [NeZero (2 : K)] (w : ℕ)
    (h : a ≠ d) :
    ∑ᶠ X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d)),
      (2 / (cardStabilizerOnOrbit X : K)) *
        LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
          (binaryFormRep K w (op (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ))) =
      (d - a).natAbs * (Polynomial.dickson 2 ((a * d : ℤ) : K) w).eval ((a + d : ℤ) : K) := by
  have hX (X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) (a + d) (a * d))) :
      (2 / (cardStabilizerOnOrbit X : K)) *
          LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
            (binaryFormRep K w (op (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ))) =
        (Polynomial.dickson 2 ((a * d : ℤ) : K) w).eval ((a + d : ℤ) : K) := by
    obtain ⟨ht, hn⟩ := mem_traceDetFiber.1 X.out.2
    rw [BinaryQuadraticForm.cardStabilizerOnOrbit_traceDetFiber_add_mul h, Nat.cast_ofNat,
      div_self two_ne_zero, one_mul, trace_binaryFormRep_eq_dickson_eval, ht, hn]
  simp_rw [hX]
  rw [← finsum_comp_equiv (BinaryQuadraticForm.finEquivOrbitRelQuotientTraceDetFiber h),
    finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end TauCeti
