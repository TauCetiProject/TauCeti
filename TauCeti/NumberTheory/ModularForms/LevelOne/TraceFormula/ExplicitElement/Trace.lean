/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Trace
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.ExchangeRelations
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.TraceReduction

/-!
# Assembling the trace of Popa–Zagier's explicit element

The trace of the explicit element on positive even-degree period polynomials is a finite sum
of fixed-trace weight sums. Writing `Tₙ` for this element, for determinant `n ≠ 0` the formula is

`tr(Tₙ | W_w) = (1/12) ∑_{-4n ≤ t ≤ 4n} (∑_{det M = n, tr M = t} weight M) P_{w+2}(t,n)`.

Here `weight` is twelve times the coefficient in Popa–Zagier's equation (15), and `P` is the
Dickson polynomial already used for binary-form traces. The inner sums have finite support:
every matrix of nonzero weight has all entries bounded by `2n`. No elliptic, hyperbolic or
parabolic weight identity is assumed. Substituting those identities into this formula is what
converts it to the class-number and divisor-sum expression for the trace.

The sum is over integral matrices, not projective classes. Each projective coefficient is the
sum of the weights of its two representatives, so no additional factor of two occurs. This is
distinct from the factor of two in the later transfer from `W_w` to cusp forms.

## Main results

* `TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_eq_finsum`: the ambient
  trace as a weight sum over determinant-`n` matrices.
* `TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_eq_sum_trace_fibres`:
  the ambient trace grouped by integral trace.

The analogous theorem `trace_periodActionRestrict_popaZagierElement_eq_sum_trace_fibres` gives
this formula on period polynomials of positive even degree.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§2, 4, equation (15).
-/

public section

open Matrix MvPolynomial MonoidAlgebra

namespace TauCeti.TraceFormulaMatrixModule

variable {K : Type*} [Field K] {n : ℤ}

/-- The trace of Popa–Zagier's explicit element on degree-`w` binary forms is the sum of
its integer matrix weights times the Dickson trace polynomial, divided by twelve. -/
theorem trace_periodAction_popaZagierElement_eq_finsum (hn : n ≠ 0) (w : ℕ) (hw : Even w) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction hw (popaZagierElement K n)) =
      (12 : K)⁻¹ * ∑ᶠ A : TraceFormulaMatrix n,
        (PopaZagier.weight A.1 : K) *
          (Polynomial.dickson 2 (n : K) w).eval (A.1.trace : K) := by
  classical
  let s := (FixedDetMatrices.finite_setOf_abs_le (m := Fin 2) n (2 * n)).toFinset
  have hs (A : TraceFormulaMatrix n) (hA : (PopaZagier.weight A.1 : K) ≠ 0) : A ∈ s := by
    simpa [s] using abs_le_of_intCast_ne_zero (fun _ ↦ id) A hA
  rw [popaZagierElement_eq_inv_smul_ofWeight,
    ofWeight_eq_sum hn _ _ _ s hs, map_smul, map_smul, smul_eq_mul,
    trace_periodAction_sum_eq_dickson_eval]
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro A hA
  exact hs A (mul_ne_zero_iff.mp hA).1

/-- Grouping by integral trace reduces the ambient trace to finitely many fixed-trace weight
sums. The interval `[-4n,4n]` contains the trace of every matrix of nonzero weight. -/
theorem trace_periodAction_popaZagierElement_eq_sum_trace_fibres (hn : n ≠ 0)
    (w : ℕ) (hw : Even w) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction hw (popaZagierElement K n)) =
      (12 : K)⁻¹ * ∑ t ∈ Finset.Icc (-4 * n) (4 * n),
        (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, PopaZagier.weight A.1) : K) *
          (Polynomial.dickson 2 (n : K) w).eval (t : K) := by
  classical
  let s := (FixedDetMatrices.finite_setOf_abs_le (m := Fin 2) n (2 * n)).toFinset
  have hs (A : TraceFormulaMatrix n) (hA : PopaZagier.weight A.1 ≠ 0) : A ∈ s := by
    simpa [s, A.2] using PopaZagier.abs_le_of_weight_ne_zero hA
  have htrace (A : TraceFormulaMatrix n) (hA : A ∈ s) :
      A.1.trace ∈ Finset.Icc (-4 * n) (4 * n) := by
    have hbound : ∀ i j, |A.1 i j| ≤ 2 * n := by simpa [s] using hA
    have h0 := hbound 0 0
    have h1 := hbound 1 1
    simp only [abs_le] at h0 h1
    have ht : -4 * n ≤ A.1 0 0 + A.1 1 1 ∧ A.1 0 0 + A.1 1 1 ≤ 4 * n := by omega
    simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Finset.mem_Icc] using ht
  have hfibre (t : ℤ) :
      (∑ᶠ A : traceDetFiber (Fin 2) t n, PopaZagier.weight A.1) =
      ∑ A ∈ s with A.1.trace = t, PopaZagier.weight A.1 := by
    -- Reorder the two subtype conditions using their membership characterizations.
    let e : {A : TraceFormulaMatrix n // A.1.trace = t} ≃ traceDetFiber (Fin 2) t n :=
      { toFun A := ⟨A.1.1, mem_traceDetFiber.mpr ⟨A.2, A.1.2⟩⟩
        invFun A := ⟨⟨A.1, (mem_traceDetFiber.mp A.2).2⟩, (mem_traceDetFiber.mp A.2).1⟩ }
    calc
      _ = ∑ᶠ A : {A : TraceFormulaMatrix n // A.1.trace = t},
          PopaZagier.weight A.1.1 := (finsum_comp_equiv e).symm
      _ = ∑ᶠ A ∈ {A : TraceFormulaMatrix n | A.1.trace = t}, PopaZagier.weight A.1 :=
        finsum_subtype_eq_finsum_cond (f := fun A : TraceFormulaMatrix n ↦
          PopaZagier.weight A.1) (fun A ↦ A.1.trace = t)
      _ = _ := finsum_mem_eq_sum_of_subset _
        (fun A hA ↦ Finset.mem_filter.mpr ⟨hs A hA.2, hA.1⟩)
        (fun A hA ↦ (Finset.mem_filter.mp hA).2)
  rw [trace_periodAction_popaZagierElement_eq_finsum hn w hw]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) (by
    intro A hA
    exact hs A (ne_zero_of_map (f := Int.castAddHom K) (mul_ne_zero_iff.mp hA).1)),
    ← Finset.sum_fiberwise_of_maps_to htrace]
  apply Finset.sum_congr rfl
  intro t _
  rw [hfibre, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [(Finset.mem_filter.mp hA).2]

/-- The trace of Popa–Zagier's explicit element on period polynomials of positive even degree
is the fixed-trace weight sum. The exchange relations identify this trace with the ambient
binary-form trace. -/
theorem trace_periodActionRestrict_popaZagierElement_eq_sum_trace_fibres [CharZero K]
    (hn : n ≠ 0) (w : ℕ) (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
        ((exchangeRelations_popaZagierElement K n).periodActionRestrict hw) =
      (12 : K)⁻¹ * ∑ t ∈ Finset.Icc (-4 * n) (4 * n),
        (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, PopaZagier.weight A.1) : K) *
          (Polynomial.dickson 2 (n : K) w).eval (t : K) := by
  rw [(exchangeRelations_popaZagierElement K n).trace_periodActionRestrict_eq_trace hw hw₀,
    trace_periodAction_popaZagierElement_eq_sum_trace_fibres hn w hw]

end TauCeti.TraceFormulaMatrixModule
