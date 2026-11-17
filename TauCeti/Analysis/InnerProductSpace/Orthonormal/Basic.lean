/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Reindexing conditions on orthonormal families

Conditions quantified over all orthonormal families of a fixed size, such as `k`-nonnegativity of
an operator, are naturally stated for families indexed by `Fin k`. Reindexing along a bijection
preserves orthonormality and finite products, so such a condition on `∏ᵢ f (wᵢ)` transfers to
orthonormal families indexed by any finite type of the same cardinality.

## Main statements

* `Orthonormal.prod_of_forall_of_card_eq`, `Orthonormal.sum_of_forall_of_card_eq`: a condition on
  `∏ᵢ f (vᵢ)` (resp. `∑ᵢ f (vᵢ)`) along all orthonormal families `v` indexed by `κ` holds along
  every orthonormal family indexed by a type with as many elements as `κ`.
-/

public section

namespace Orthonormal

variable {𝕜 E M ι κ : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CommMonoid M] [Fintype ι] [Fintype κ]

/-- If a condition `P` holds for the product `∏ᵢ f (vᵢ)` along every orthonormal family `v`
indexed by `κ`, then it holds for `∏ᵢ f (wᵢ)` along every orthonormal family `w` indexed by a type
with as many elements as `κ`. -/
@[to_additive /-- If a condition `P` holds for the sum `∑ᵢ f (vᵢ)` along every orthonormal family
`v` indexed by `κ`, then it holds for `∑ᵢ f (wᵢ)` along every orthonormal family `w` indexed by a
type with as many elements as `κ`. -/]
theorem prod_of_forall_of_card_eq {w : ι → E} (hw : Orthonormal 𝕜 w)
    (hι : Fintype.card ι = Fintype.card κ) (f : E → M) (P : M → Prop)
    (h : ∀ v : κ → E, Orthonormal 𝕜 v → P (∏ i, f (v i))) : P (∏ i, f (w i)) := by
  let e := Fintype.equivOfCardEq hι
  simpa [← e.symm.prod_comp] using h (w ∘ e.symm) (hw.comp _ e.symm.injective)

end Orthonormal
