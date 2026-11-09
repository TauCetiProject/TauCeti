/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic.Polynomial
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Thom
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.Data.Finset.Sort

/-!
# Ordered root regions of analytic polynomial families

For a univariate polynomial family with analytic coefficients and locally bounded degree,
its ordered distinct-root loci and complementary sectors are partially semialgebraic in the
height coordinate. In particular, restricting these loci to a semianalytic base gives
semianalytic root sections and sectors. No squarefreeness or constancy of degree is required.
Repeated roots are counted once. A zero polynomial has an empty `Polynomial.roots` multiset,
so its ordered distinct-root loci are empty; its non-root sectors are empty as well.

The coefficient-space root-count and Thom descriptions in
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Thom` are pulled back by analytic coefficient
substitution. Thus the description holds over an entire vertical cylinder, including near
points outside a root graph, rather than only near the points of the graph itself.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 4, 5 and 10 (ordered roots and sign descriptions).
S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1 (semianalytic sections).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → ℝ[X]} {x₀ : E} {d : ℕ}

/-- In an analytic polynomial family of locally bounded degree, the locus where the height is
its `i`-th distinct root is partially semialgebraic over the base point. Index zero means the
smallest root. Fibers where the polynomial is zero contribute no points. -/
theorem partiallySemialgebraicAt_setOf_mem_roots_card_lt
    (hF : ∀ k ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff k) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      p.2 () ∈ (F p.1).roots.toFinset ∧
      {r ∈ (F p.1).roots.toFinset | r < p.2 ()}.card = i} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomial_condition
    (fun P t ↦ t ∈ P.roots.toFinset ∧ {r ∈ P.roots.toFinset | r < t}.card = i) ?_ hF hdeg
  let P := Polynomial.ofFn (d + 1)
    (fun i : Fin (d + 1) ↦ (MvPolynomial.X (.inl i) : MvPolynomial (Fin (d + 1) ⊕ Unit) ℝ))
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_eq
    P (MvPolynomial.X (.inr ())) i using 1
  ext v
  simp only [P, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, MvPolynomial.eval_X]
  simp [eq_comm]

/-- The non-root locus with exactly `i` distinct roots below the height is partially
semialgebraic. This includes both unbounded sectors and the whole fiber for a nonzero
constant polynomial; a zero polynomial contributes no points. -/
theorem partiallySemialgebraicAt_setOf_not_isRoot_card_lt
    (hF : ∀ k ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff k) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      ¬ (F p.1).IsRoot (p.2 ()) ∧
      {r ∈ (F p.1).roots.toFinset | r < p.2 ()}.card = i} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomial_condition
    (fun P t ↦ ¬ P.IsRoot t ∧ {r ∈ P.roots.toFinset | r < t}.card = i) ?_ hF hdeg
  let P := Polynomial.ofFn (d + 1)
    (fun i : Fin (d + 1) ↦ (MvPolynomial.X (.inl i) : MvPolynomial (Fin (d + 1) ⊕ Unit) ℝ))
  convert (isSemialgebraic_eval_ne_zero (P.eval (MvPolynomial.X (.inr ())))).inter
    (isSemialgebraic_setOf_card_roots_map_eval_lt P (MvPolynomial.X (.inr ())) i) using 1
  ext v
  simp only [mem_inter_iff, mem_ofPred_eq, IsRoot.def, ← eval_map_apply, MvPolynomial.eval_X,
    P, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum, Polynomial.map_monomial]

/-- The region strictly below the `i`-th distinct root is partially semialgebraic for an
analytic polynomial family of locally bounded degree. Where that root does not exist,
the region is empty. -/
theorem partiallySemialgebraicAt_setOf_lt_root_card_lt
    (hF : ∀ k ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff k) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      ∃ r ∈ (F p.1).roots.toFinset,
        {z ∈ (F p.1).roots.toFinset | z < r}.card = i ∧ p.2 () < r} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomial_condition
    (fun P t ↦ ∃ r ∈ P.roots.toFinset,
      {z ∈ P.roots.toFinset | z < r}.card = i ∧ t < r) ?_ hF hdeg
  let P := Polynomial.ofFn (d + 1)
    (fun i : Fin (d + 1) ↦ (MvPolynomial.X (.inl i) : MvPolynomial (Fin (d + 1) ⊕ Unit) ℝ))
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_eval_lt
    P (MvPolynomial.X (.inr ())) i using 1
  ext v
  simp only [mem_ofPred_eq, P, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, MvPolynomial.eval_X]

/-- The region strictly above the `i`-th distinct root is partially semialgebraic for an
analytic polynomial family of locally bounded degree. Where that root does not exist,
the region is empty. -/
theorem partiallySemialgebraicAt_setOf_gt_root_card_lt
    (hF : ∀ k ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff k) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (i : ℕ) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) |
      ∃ r ∈ (F p.1).roots.toFinset,
        {z ∈ (F p.1).roots.toFinset | z < r}.card = i ∧ r < p.2 ()} x₀ := by
  classical
  apply partiallySemialgebraicAt_polynomial_condition
    (fun P t ↦ ∃ r ∈ P.roots.toFinset,
      {z ∈ P.roots.toFinset | z < r}.card = i ∧ r < t) ?_ hF hdeg
  let P := Polynomial.ofFn (d + 1)
    (fun i : Fin (d + 1) ↦ (MvPolynomial.X (.inl i) : MvPolynomial (Fin (d + 1) ⊕ Unit) ℝ))
  convert isSemialgebraic_setOf_mem_roots_card_roots_lt_and_lt_eval
    P (MvPolynomial.X (.inr ())) i using 1
  ext v
  simp only [mem_ofPred_eq, P, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, MvPolynomial.eval_X]

/-- A root section over a semianalytic base, selected by its position in the distinct-root
order, has a partially semialgebraic graph over the base point. The root and index conditions
need only hold near that point on the base set. In particular the graph is semianalytic at
every height over the base point, including heights outside the graph. -/
theorem SemianalyticAt.partiallySemialgebraicAt_graphOn_of_roots_card_lt
    {S : Set E} {r : E → ℝ} (hS : SemianalyticAt S x₀)
    (hF : ∀ k ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff k) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (i : ℕ)
    (hr : ∀ᶠ x in 𝓝 x₀, x ∈ S → r x ∈ (F x).roots.toFinset ∧
      {z ∈ (F x).roots.toFinset | z < r x}.card = i) :
    PartiallySemialgebraicAt (S.graphOn (fun x (_ : Unit) ↦ r x)) x₀ := by
  classical
  have hL := hS.partiallySemialgebraicAt_preimage_fst.inter
    (partiallySemialgebraicAt_setOf_mem_roots_card_lt hF hdeg i)
  apply hL.congr hr
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_graphOn,
    and_congr_left_iff]
  intro hp
  constructor
  · rintro ⟨hx, ht, hi⟩
    refine ⟨hx, funext fun u ↦ ?_⟩
    obtain ⟨hroot, hindex⟩ := hp hx
    let Z := (F p.1).roots.toFinset
    let e := Z.orderIsoOfFin rfl
    have rank (a : ℝ) (ha : a ∈ Z) :
        {z ∈ Z | z < a}.card = (e.symm ⟨a, ha⟩).val := by
      simpa only [e, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply] using
        Z.card_filter_lt_orderEmbOfFin rfl (e.symm ⟨a, ha⟩)
    have heq : (e.symm ⟨r p.1, hroot⟩).val = (e.symm ⟨p.2 (), ht⟩).val := by
      rw [← rank _ hroot, ← rank _ ht, hindex, hi]
    have heq' := congrArg Subtype.val (e.symm.injective (Fin.ext heq))
    cases u
    exact heq'
  · rintro ⟨hx, ht⟩
    have heq := congrFun ht ()
    exact ⟨hx, heq ▸ (hp hx).1, heq ▸ (hp hx).2⟩

end TauCeti
