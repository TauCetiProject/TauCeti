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
import TauCeti.Probability.Independence.Conditional

/-!
# Conditional independence of crossing array strips

For a separately exchangeable array, the row strips along `T` and the column strips along `S` are
conditionally independent given their intersection `S ×ˢ T` whenever either index set
is infinite. Thus the two
families of strips used in the hidden/visible array decomposition are independent given
the entire hidden block, not merely given a directing measure.

When `S` and `T` are both infinite, a finite visible rectangle outside those hidden axes is
conditionally independent of every entry outside it given the union of the row and column strips.
This is the block form of the conditional cell-noise factorization: after the crossing strips have
been revealed, the rest of the array carries no further information about that visible block.

## References

* The finite-observation argument is adapted from
  `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_domRestrict_of_finite_reindexing` in
  `TauCeti.Probability.Exchangeability.Arrays.Block.Independence`.
* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Lemma 1.3 and Chapter 7.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_rowStrip_colStrip` — the two crossing
  strip families are conditionally independent given their intersection.
* `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_visibleBlock_compl` — a finite visible
  rectangle is conditionally independent of its complement given the full crossing strips.
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

/-- **A finite visible rectangle is conditionally independent of its complement given the
crossing hidden strips.** Let `S` and `T` be infinite sets of hidden row and column indices, and
let the finite sets `I` and `J` be disjoint from them. Once all entries in hidden rows or hidden
columns are known, the block `I ×ˢ J` is conditionally independent of every entry outside that
block.

The conditioning set is the full cross `(univ ×ˢ T) ∪ (S ×ˢ univ)`, rather than only the finite
part of the cross adjacent to `I ×ˢ J`. This form can therefore be iterated over disjoint visible
blocks when constructing the cell-noise layer of an array representation. -/
theorem SeparatelyExchangeable.condIndepFun_visibleBlock_compl
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T I J : Set ℕ} (hS : S.Infinite) (hT : T.Infinite) (hI : I.Finite) (hJ : J.Finite)
    (hIS : Disjoint I S) (hJT : Disjoint J T) :
    let C : Set (ℕ × ℕ) := I ×ˢ J
    let H : Set (ℕ × ℕ) := (Set.univ ×ˢ T) ∪ (S ×ˢ Set.univ)
    C.domRestrict ⟂ᵢ[H.domRestrict, Set.measurable_restrict _; ρ] Cᶜ.domRestrict := by
  dsimp
  let R : Set (ℕ × ℕ) := (S ∪ I) ×ˢ (T ∪ J) \ (I ×ˢ J)
  let H : Set (ℕ × ℕ) := (Set.univ ×ˢ T) ∪ (S ×ˢ Set.univ)
  have hRsub : R ⊆ H := by
    rintro p ⟨⟨hpS | hpI, hpT | hpJ⟩, hpC⟩
    · exact Set.mem_union_left _ ⟨Set.mem_univ _, hpT⟩
    · exact Set.mem_union_right _ ⟨hpS, Set.mem_univ _⟩
    · exact Set.mem_union_left _ ⟨Set.mem_univ _, hpT⟩
    · exact (hpC ⟨hpI, hpJ⟩).elim
  have hHsub : H ⊆ (I ×ˢ J)ᶜ := by
    rintro p (hp | hp) hpC
    · exact Set.disjoint_left.1 hJT hpC.2 hp.2
    · exact Set.disjoint_left.1 hIS hpC.1 hp.1
  have hRH : MeasurableSpace.comap (R.domRestrict (π := fun _ ↦ α)) inferInstance ≤
      MeasurableSpace.comap (H.domRestrict (π := fun _ ↦ α)) inferInstance := by
    rw [← Set.domRestrict₂_comp_domRestrict hRsub, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hRsub).comap_le
  have hHC : MeasurableSpace.comap (H.domRestrict (π := fun _ ↦ α)) inferInstance ≤
      MeasurableSpace.comap (((I ×ˢ J)ᶜ).domRestrict (π := fun _ ↦ α)) inferInstance := by
    rw [← Set.domRestrict₂_comp_domRestrict hHsub, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hHsub).comap_le
  have hlocal := hρ.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset
    (S := S ∪ I) (T := T ∪ J) (B := I ×ˢ J) (C := I ×ˢ J)
    (hS.mono Set.subset_union_left) (hT.mono Set.subset_union_left) (hI.prod hJ)
    Set.Subset.rfl (Set.prod_mono Set.subset_union_right Set.subset_union_right)
  rw [condIndepFun_iff_condIndep] at hlocal ⊢
  exact condIndep_of_condIndep_of_le_of_le
    (Set.measurable_restrict _).comap_le (Set.measurable_restrict _).comap_le
    (Set.measurable_restrict _).comap_le hlocal hRH hHC

end TauCeti.Probability
