/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block.Basic
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Exchangeability.Arrays.Block.Independence
import TauCeti.Data.Set.Infinite

/-!
# Conditional independence of crossing array strips

For a separately exchangeable array, the row strips along `T` and the column strips along `S` are
conditionally independent given their intersection `S ×ˢ T` whenever either index set
is infinite. Thus the two
families of strips used in the hidden/visible array decomposition are independent given
the entire hidden block, not merely given a directing measure.

## References

* The finite-observation argument is adapted from
  `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_domRestrict_compl_of_finite` in
  `TauCeti.Probability.Exchangeability.Arrays.Block.Independence`.
* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Lemma 1.3 and Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- The row strips along `T` and the column strips along `S` are conditionally independent given
the entire intersection block whenever at least one of `S` and `T` is infinite. -/
theorem SeparatelyExchangeable.condIndepFun_rowStrip_colStrip
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (S : Set ℕ)
    {T : Set ℕ} (hST : S.Infinite ∨ T.Infinite) :
    (Set.univ ×ˢ T).domRestrict ⟂ᵢ[(S ×ˢ T).domRestrict, Set.measurable_restrict _; ρ]
      (S ×ˢ Set.univ).domRestrict := by
  rcases hST with hS | hT
  · apply CondIndepFun.symm
    refine hρ.condIndepFun_domRestrict_of_finite_reindexing (S ×ˢ T) (Set.univ ×ˢ T)
      (S ×ˢ Set.univ) (Set.prod_mono_left (Set.subset_univ S)) ?_
    intro C hC hCS
    obtain ⟨a, ha, haC, haS⟩ := hS.exists_injective_into_eqOn_of_finite
      (hC.image Prod.fst) (by rintro i ⟨p, hp, rfl⟩; exact (hCS hp).1)
    exact ⟨a, id, ha, Function.injective_id,
      fun p hp ↦ Prod.ext (haC p.1 ⟨p, hp, rfl⟩) rfl,
      fun p hp ↦ ⟨haS _, hp.2⟩⟩
  · refine hρ.condIndepFun_domRestrict_of_finite_reindexing (S ×ˢ T) (S ×ˢ Set.univ)
      (Set.univ ×ˢ T) (Set.prod_mono_right (Set.subset_univ T)) ?_
    intro C hC hCT
    obtain ⟨b, hb, hbC, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
      (hC.image Prod.snd) (by rintro j ⟨p, hp, rfl⟩; exact (hCT hp).2)
    exact ⟨id, b, Function.injective_id, hb,
      fun p hp ↦ Prod.ext rfl (hbC p.2 ⟨p, hp, rfl⟩),
      fun p hp ↦ ⟨hp.1, hbT _⟩⟩

end TauCeti.Probability
