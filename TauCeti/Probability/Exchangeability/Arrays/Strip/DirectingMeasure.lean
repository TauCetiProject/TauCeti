/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.DeFinetti
import TauCeti.Probability.DeFinetti.Subsequence
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
import TauCeti.Probability.Exchangeability.ConditionallyIID.Congr

/-!
# Directing measures of strips from a hidden array block

Choose infinite sets of hidden rows and columns of a separately exchangeable array, enumerated
by injections `e` and `f`. All row strips along `f` are conditionally i.i.d. with a directing law
that is a measurable function of the hidden block `(X (e i, f j))`. The analogous statement for
column strips uses the same hidden block.

These are the row and column directing laws used in the hidden/visible decomposition of a
separately exchangeable array. In particular, after restricting to visible rows or columns with
`ConditionallyIIDWith.comp_injective`, the witness still depends only on the hidden block.
The statements concern conditioning on these directing laws; they do not assert that the row
and column strips are independent of one another given the entire hidden block.

Only the recovering axis must be injectively enumerated: row-strip recovery needs injective `e`,
and column-strip recovery needs injective `f`. Measurability is needed only on the hidden block;
the remaining entries may be merely a.e. measurable.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [StandardBorelSpace α] [Nonempty α]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

/-- The row strips along `f` admit a directing law measurable in the block selected by `e` and
`f`. Only `e` must be injective: infinitely many selected rows determine the directing law of
all the row strips. -/
theorem SeparatelyExchangeable.exists_rowStrip_directing_of_injective
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hblock : ∀ i j, Measurable (X (e i, f j))) :
    ∃ R : (ℕ × ℕ → α) → ProbabilityMeasure (ℕ → α), Measurable R ∧
      ConditionallyIIDWith μ (fun i ω j ↦ X (i, f j) ω)
        (fun ω ↦ R (fun p ↦ X (e p.1, f p.2) ω)) := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayRow hX).exists_directing
  have hstrip := hν.map_values (Measurable.of_eval fun j ↦ measurable_pi_apply (f j))
  simp only [arrayRow_apply] at hstrip
  obtain ⟨F, hF, heq⟩ := hstrip.exists_measurable_directing_eq_comp he
  refine ⟨fun z ↦ F (fun i j ↦ z (i, j)),
    hF.comp (Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦
      measurable_pi_apply (i, j)), ?_⟩
  exact hstrip.congr_directing
    (hF.comp (Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ hblock i j)) heq

/-- The column strips along `e` admit a directing law measurable in the block selected by `e`
and `f`. Only `f` must be injective. Together with the row-strip theorem, this gives both
directing laws as measurable functions of one common hidden block. -/
theorem SeparatelyExchangeable.exists_colStrip_directing_of_injective
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hf : Function.Injective f) (hblock : ∀ i j, Measurable (X (e i, f j))) :
    ∃ C : (ℕ × ℕ → α) → ProbabilityMeasure (ℕ → α), Measurable C ∧
      ConditionallyIIDWith μ (fun j ω i ↦ X (e i, j) ω)
        (fun ω ↦ C (fun p ↦ X (e p.1, f p.2) ω)) := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayCol hX).exists_directing
  have hstrip := hν.map_values (Measurable.of_eval fun i ↦ measurable_pi_apply (e i))
  simp only [arrayCol_apply] at hstrip
  obtain ⟨F, hF, heq⟩ := hstrip.exists_measurable_directing_eq_comp hf
  refine ⟨fun z ↦ F (fun j i ↦ z (i, j)),
    hF.comp (Measurable.of_eval fun j ↦ Measurable.of_eval fun i ↦
      measurable_pi_apply (i, j)), ?_⟩
  exact hstrip.congr_directing
    (hF.comp (Measurable.of_eval fun j ↦ Measurable.of_eval fun i ↦ hblock i j)) heq

end TauCeti.Probability
