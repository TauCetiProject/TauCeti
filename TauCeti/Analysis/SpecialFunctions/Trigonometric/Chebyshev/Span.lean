module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Moments
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure
import TauCeti.RingTheory.Polynomial.Chebyshev.Basis

/-!
# Polynomial span of the Chebyshev modes

This file connects the algebraic Chebyshev basis of `ℝ[X]` with the normalized Chebyshev
functions in `L²(Polynomial.Chebyshev.measureT)`.  Evaluation followed by the canonical map into
`L²` is bundled as a linear map.  Since every Chebyshev polynomial is a nonzero scalar multiple
of its normalized mode, every polynomial evaluation belongs to the linear span of those modes.

This is the algebra-to-analysis handoff in Part C of the `OrthogonalL2Bases` roadmap.  In the
completeness argument, it upgrades orthogonality against every Chebyshev mode to orthogonality
against every polynomial.

## Main declarations

* `TauCeti.polynomialEvalChebyshevLp`: polynomial evaluation as a linear map into
  `L²(Polynomial.Chebyshev.measureT)`.
* `TauCeti.polynomialEvalChebyshevLp_mem_span`: every polynomial evaluation lies in the span of
  the normalized Chebyshev modes.
* `TauCeti.inner_polynomialEvalChebyshevLp_eq_zero`: orthogonality to all normalized modes implies
  orthogonality to every polynomial evaluation.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- Evaluate a real polynomial and regard the resulting function as an element of
`L²(Polynomial.Chebyshev.measureT)`.

The map is well-defined because every polynomial has finite second moment for the Chebyshev
measure. -/
noncomputable def polynomialEvalChebyshevLp :
    Polynomial ℝ →ₗ[ℝ] Lp ℝ 2 Polynomial.Chebyshev.measureT where
  toFun q := (memLp_two_eval_measureT q).toLp fun x => q.eval x
  map_add' q r := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by simp
  map_smul' a q := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      change Polynomial.eval x (a • q) = a * Polynomial.eval x q
      rw [Polynomial.smul_eq_C_mul, Polynomial.eval_C_mul]

/-- The `L²` representative of a polynomial evaluation is the expected pointwise evaluation. -/
lemma coeFn_polynomialEvalChebyshevLp (q : Polynomial ℝ) :
    ⇑(polynomialEvalChebyshevLp q) =ᵐ[Polynomial.Chebyshev.measureT] fun x => q.eval x :=
  MemLp.coeFn_toLp (memLp_two_eval_measureT q)

/-- Under the polynomial-evaluation map, the `n`th Chebyshev polynomial is the square root of its
squared norm times the normalized `n`th Chebyshev mode. -/
lemma polynomialEvalChebyshevLp_T (n : ℕ) :
    polynomialEvalChebyshevLp (T ℝ n) =
      Real.sqrt (chebyshevTNormSq n) • normalizedChebyshevTLp ℝ n := by
  apply Lp.ext
  filter_upwards [coeFn_polynomialEvalChebyshevLp (T ℝ n),
    coeFn_normalizedChebyshevTLp (𝕜 := ℝ) n,
    Lp.coeFn_smul (Real.sqrt (chebyshevTNormSq n)) (normalizedChebyshevTLp ℝ n)] with
      x hT hnorm hsmul
  rw [hT, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hnorm]
  change (T ℝ n).eval x =
    Real.sqrt (chebyshevTNormSq n) * normalizedChebyshevT n x
  rw [normalizedChebyshevT_def]
  field_simp [Real.sqrt_ne_zero'.mpr (chebyshevTNormSq_pos n)]

/-- Every real polynomial evaluation in `L²(measureT)` belongs to the linear span of the
normalized Chebyshev modes. -/
theorem polynomialEvalChebyshevLp_mem_span (q : Polynomial ℝ) :
    polynomialEvalChebyshevLp q ∈
      Submodule.span ℝ (Set.range (normalizedChebyshevTLp ℝ)) := by
  let S := Submodule.span ℝ (Set.range (normalizedChebyshevTLp ℝ))
  have hq : q ∈ Submodule.span ℝ (Set.range (chebyshevTBasis (R := ℝ))) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_
    ((polynomialEvalChebyshevLp.map_zero : polynomialEvalChebyshevLp 0 = 0).symm ▸ S.zero_mem)
    (fun _ _ _ _ hx hy => by simpa using S.add_mem hx hy)
    (fun _ _ _ hx => by simpa using S.smul_mem _ hx) hq
  rintro p ⟨n, rfl⟩
  rw [chebyshevTBasis_apply, polynomialEvalChebyshevLp_T]
  exact S.smul_mem _ (Submodule.subset_span (Set.mem_range_self n))

/-- A vector orthogonal to every normalized Chebyshev mode is orthogonal to the `L²` evaluation
of every real polynomial.

This is the form used in the Chebyshev completeness argument: the algebraic Chebyshev basis
converts the mode hypotheses into vanishing polynomial moments. -/
theorem inner_polynomialEvalChebyshevLp_eq_zero
    (g : Lp ℝ 2 Polynomial.Chebyshev.measureT)
    (hmode : ∀ n, inner ℝ g (normalizedChebyshevTLp ℝ n) = 0) (q : Polynomial ℝ) :
    inner ℝ g (polynomialEvalChebyshevLp q) = 0 := by
  have hmem := polynomialEvalChebyshevLp_mem_span q
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hx hy => by simp [inner_add_right, hx, hy])
    (fun _ _ _ hx => by simp [inner_smul_right, hx]) hmem
  rintro v ⟨n, rfl⟩
  exact hmode n

end TauCeti
