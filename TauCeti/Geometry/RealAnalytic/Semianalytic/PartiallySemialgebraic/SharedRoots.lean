/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic.Polynomial
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.SharedRoots
import Mathlib.FieldTheory.IsRealClosed.Real

/-!
# Shared root regions of analytic polynomial families

The ordered distinct-root loci and complementary sectors of a finite family of polynomials
with analytic coefficients are partially semialgebraic in the height variable. The description
is uniform along the entire height fiber. Roots shared by several members, and repeated roots,
are counted once. Nullified members contribute no roots, and the empty family is allowed.

The coefficient-space formulas come from
`Finset.isSemialgebraic_setOf_mem_biUnion_roots_map_eval` and
`Finset.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt`; analytic coefficient substitution
then gives the same formulas for analytic families. These descriptions make the sections and
sectors of analytic-coefficient delineations semianalytic, even at their frontier points.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 10 and 11 (uniform shared-root descriptions).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]
  {F : κ → E → ℝ[X]} {x₀ : E} {d : κ → ℕ}

/-- The locus of the `i`-th shared distinct root of a finite analytic polynomial family is
partially semialgebraic. Root indexing starts at zero; zero polynomials contribute no roots. -/
theorem partiallySemialgebraicAt_setOf_mem_biUnion_roots_card_lt
    (hF : ∀ k i, i ≤ d k → AnalyticAt ℝ (fun x ↦ (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).natDegree ≤ d k) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      p.2 () ∈ Finset.univ.biUnion (fun k ↦ (F k p.1).roots.toFinset) ∧
      {r ∈ Finset.univ.biUnion (fun k ↦ (F k p.1).roots.toFinset) | r < p.2 ()}.card = i} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomialFamily_condition
    (fun P t ↦ t ∈ Finset.univ.biUnion (fun k ↦ (P k).roots.toFinset) ∧
      {r ∈ Finset.univ.biUnion (fun k ↦ (P k).roots.toFinset) | r < t}.card = i) ?_ hF hdeg
  let P (k : κ) := Polynomial.ofFn (d k + 1)
    (fun j : Fin (d k + 1) ↦
      (MvPolynomial.X (.inl ⟨k, j⟩) : MvPolynomial ((Σ k, Fin (d k + 1)) ⊕ Unit) ℝ))
  let G := Finset.univ.image P
  convert (G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval (MvPolynomial.X (.inr ()))).inter
    (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X (.inr ())) i) using 1
  ext v
  simp only [G, Finset.image_biUnion, P, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X, mem_inter_iff,
    mem_ofPred_eq]

/-- The locus of the `i`-th shared-root sector is partially semialgebraic. It consists of
non-roots with exactly `i` shared distinct roots below them. If there are no roots, sector zero
is the whole height fiber, including for an empty or entirely nullified family. -/
theorem partiallySemialgebraicAt_setOf_notMem_biUnion_roots_card_lt
    (hF : ∀ k i, i ≤ d k → AnalyticAt ℝ (fun x ↦ (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).natDegree ≤ d k) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      p.2 () ∉ Finset.univ.biUnion (fun k ↦ (F k p.1).roots.toFinset) ∧
      {r ∈ Finset.univ.biUnion (fun k ↦ (F k p.1).roots.toFinset) | r < p.2 ()}.card = i} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomialFamily_condition
    (fun P t ↦ t ∉ Finset.univ.biUnion (fun k ↦ (P k).roots.toFinset) ∧
      {r ∈ Finset.univ.biUnion (fun k ↦ (P k).roots.toFinset) | r < t}.card = i) ?_ hF hdeg
  let P (k : κ) := Polynomial.ofFn (d k + 1)
    (fun j : Fin (d k + 1) ↦
      (MvPolynomial.X (.inl ⟨k, j⟩) : MvPolynomial ((Σ k, Fin (d k + 1)) ⊕ Unit) ℝ))
  let G := Finset.univ.image P
  convert ((G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval
    (MvPolynomial.X (.inr ()))).compl).inter
    (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X (.inr ())) i) using 1
  ext v
  simp only [G, Finset.image_biUnion, P, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X, mem_inter_iff,
    mem_compl_iff, mem_ofPred_eq]

end TauCeti
