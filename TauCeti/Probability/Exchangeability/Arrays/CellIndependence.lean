/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block.Independence

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
  have h := SeparatelyExchangeable.condIndepFun_domRestrict_compl_of_finite hρ hS hT
    (Set.finite_singleton c) (Set.singleton_subset_iff.mpr ⟨hc₁, hc₂⟩)
  have heval : Measurable (fun z : ({c} : Set (ℕ × ℕ)) → α ↦ z ⟨c, by simp⟩) :=
    measurable_pi_apply _
  have h' := h.comp heval measurable_id
  simpa [Function.comp_def, Set.domRestrict] using h'

end Probability

end TauCeti
