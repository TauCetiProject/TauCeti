/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block
public import Mathlib.Probability.Independence.Conditional
-- Non-public: Kallenberg's contraction-independence identity, the drop-information criterion for
-- conditional independence and conditioning on an intermediate σ-algebra are used only inside the
-- proof.
import TauCeti.Probability.Independence.Conditional
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.Data.Set.Infinite

/-!
# Local conditional independence of the entries of a separately exchangeable array

Fix an entry `c` of a separately exchangeable array and an infinite rectangle `S ×ˢ T` through it.
Given the other entries of that rectangle, the entry at `c` is conditionally independent of the
entire rest of the array:

```text
x c  ⟂  (x q)_{q ≠ c}   given   (x q)_{q ∈ S ×ˢ T, q ≠ c}.
```

This is the conditional independence at the heart of Aldous's proof of the representation
`X i j = f (U, Uᵢ, Vⱼ, Uᵢⱼ)` of separately exchangeable arrays. There one splits both axes into a
hidden and a visible part and takes `S` and `T` to be the hidden rows and columns together with one
visible row `i` and one visible column `j`. The rectangle minus its corner then consists of the
hidden block, the hidden part of row `i` and the hidden part of column `j`, and the theorem says
that the visible entry `(i, j)` depends on the rest of the array only through these three pieces of
data. The cell variable `Uᵢⱼ` of the representation is the randomization of this conditional law.

The statement is about a law on array space, whose coordinate process is the array; a process on
an arbitrary sample space enters through its law.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_apply_domRestrict_compl`: the entry at
  `c` is conditionally independent of all other entries given the other entries of an infinite
  rectangle through `c`.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Lemma 1.3
  and Chapter 7.

-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] {ρ : Measure (ℕ × ℕ → α)}
  [IsFiniteMeasure ρ]

/-- **The entries of a separately exchangeable array are locally conditionally independent.** For
an infinite rectangle `S ×ˢ T` through the index `c`, the entry at `c` is conditionally independent
of all the other entries, given the other entries of the rectangle. -/
theorem SeparatelyExchangeable.condIndepFun_apply_domRestrict_compl
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) {S T : Set ℕ} (hS : S.Infinite)
    (hT : T.Infinite) {c : ℕ × ℕ} (hc₁ : c.1 ∈ S) (hc₂ : c.2 ∈ T) :
    (fun x : ℕ × ℕ → α ↦ x c) ⟂ᵢ[(S ×ˢ T \ {c}).domRestrict, Set.measurable_restrict _; ρ]
      ({c}ᶜ : Set (ℕ × ℕ)).domRestrict := by
  obtain ⟨a, ha, hac, haS⟩ := hS.exists_injective_into_apply_eq_of_mem hc₁
  obtain ⟨b, hb, hbc, hbT⟩ := hT.exists_injective_into_apply_eq_of_mem hc₂
  set R : Set (ℕ × ℕ) := S ×ˢ T \ {c}
  set D : Set (ℕ × ℕ) := {c}ᶜ
  set rR : (ℕ × ℕ → α) → R → α := R.domRestrict
  set rD : (ℕ × ℕ → α) → D → α := D.domRestrict
  have hRD : R ⊆ D := Set.sdiff_subset_compl _ _
  -- Reindexing both axes along `a` and `b` preserves the law and fixes the entry at `c`.
  let F : (ℕ × ℕ → α) → ℕ × ℕ → α := fun x p ↦ x (a p.1, b p.2)
  have hF : Measurable F := measurable_blockReadOff a b
  have hlaw : ρ.map F = ρ := by
    simpa only [arrayBlock_apply, Measure.map_id'] using
      hρ.map_arrayBlock_eq (fun p ↦ (measurable_pi_apply p).aemeasurable) ha hb
  have hFc : ∀ x, F x c = x c := fun x ↦ by simp only [F, hac, hbc]
  -- Off `c`, the reindexing lands in the rectangle minus its corner.
  have hmem : ∀ q : D, (a q.1.1, b q.1.2) ∈ R := by
    rintro ⟨q, hq⟩
    refine ⟨⟨haS _, hbT _⟩, fun h ↦ hq ?_⟩
    rw [Set.mem_singleton_iff, Prod.ext_iff] at h ⊢
    exact ⟨ha (h.1.trans hac.symm), hb (h.2.trans hbc.symm)⟩
  let G : (R → α) → D → α := fun y q ↦ y ⟨_, hmem q⟩
  have hG : Measurable G := Measurable.of_eval fun q ↦ measurable_pi_apply _
  -- The rest of the array, read after reindexing, is a function of the rest of the rectangle.
  let W : (ℕ × ℕ → α) → D → α := fun x ↦ rD (F x)
  have hW : W = G ∘ rR := rfl
  have hWR : MeasurableSpace.comap W inferInstance ≤
      MeasurableSpace.comap rR inferInstance := by
    rw [hW, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hG.comap_le
  have hRD' : MeasurableSpace.comap rR inferInstance ≤
      MeasurableSpace.comap rD (inferInstance : MeasurableSpace (D → α)) := by
    have hcomp : rR = Set.domRestrict₂ (π := fun _ ↦ α) hRD ∘ rD := by
      simpa only [rR, rD] using (Set.domRestrict₂_comp_domRestrict hRD).symm
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hRD).comap_le
  have hpair : ρ.map (fun x ↦ (x c, W x)) = ρ.map fun x ↦ (x c, rD x) := by
    have hcomp : (fun x ↦ (x c, W x)) = (fun x ↦ (x c, rD x)) ∘ F := by
      funext x
      simp only [Function.comp_apply, hFc, W]
    rw [hcomp, ← Measure.map_map (by fun_prop) hF, hlaw]
  rw [condIndepFun_iff_condIndep]
  refine CondIndep.symm ?_
  refine condIndep_of_indicator_condExp_eq (Set.measurable_restrict D).comap_le
    (Set.measurable_restrict R).comap_le (measurable_pi_apply c).comap_le ?_
  rintro _ ⟨A, hA, rfl⟩
  rw [sup_eq_left.mpr hRD']
  -- Conditioning on the rest of the array is conditioning on the reindexed read-off, which the
  -- rest of the rectangle refines.
  have hcontr := condExp_indicator_eq_of_law_eq_of_comap_le (fun x : ℕ × ℕ → α ↦ x c) W
    rD (measurable_pi_apply c) (hW ▸ hG.comp (Set.measurable_restrict R))
    (Set.measurable_restrict D) hpair (hWR.trans hRD') hA
  exact hcontr.trans (TauCeti.MeasureTheory.condExp_ae_eq_of_le_of_le hWR hRD'
    (Set.measurable_restrict D).comap_le hcontr).symm

end Probability

end TauCeti
