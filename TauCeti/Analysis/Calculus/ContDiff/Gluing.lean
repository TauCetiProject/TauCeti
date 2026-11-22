/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Gluing compatible local `Cⁿ` functions

Functions that are `Cⁿ` on the members of an open cover of a set `Ω` and agree where their
domains overlap inside `Ω` glue to one function that is `Cⁿ` on `Ω`: at a point of `Ω` take the
value of any member of the family whose domain contains it. Being `Cⁿ` is local
(`contDiffOn_of_locally_contDiffOn`), and near each point the glued function is one member of
the family.

## Main declarations

* `TauCeti.exists_contDiffOn_eqOn_of_locally`: functions that are `Cⁿ` on the sets of an open
  cover of `Ω` and agree on overlaps glue to one function that is `Cⁿ` on `Ω`.
-/

public section

open Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {Ω : Set E}

/-- **Gluing compatible local `Cⁿ` functions.** If open sets `U i` cover `Ω`, each `g i` is `Cⁿ`
on `U i`, and any two of them agree where their domains overlap inside `Ω`, then a single function
that is `Cⁿ` on `Ω` agrees with every `g i` on `Ω ∩ U i`. Outside `Ω` it agrees with an arbitrary
prescribed function `u`. -/
theorem exists_contDiffOn_eqOn_of_locally {ι : Type*} {U : ι → Set E} {g : ι → E → F}
    (hU : ∀ i, IsOpen (U i)) (hΩ : Ω ⊆ ⋃ i, U i) (hg : ∀ i, ContDiffOn 𝕜 n (g i) (U i))
    (hgg : ∀ i j, EqOn (g i) (g j) (Ω ∩ U i ∩ U j)) (u : E → F) :
    ∃ G : E → F, ContDiffOn 𝕜 n G Ω ∧ (∀ i, EqOn G (g i) (Ω ∩ U i)) ∧ EqOn G u Ωᶜ := by
  classical
  -- At `y ∈ Ω` take the value of any function whose domain contains `y`.
  choose j hj using fun x : Ω ↦ mem_iUnion.1 (hΩ x.property)
  let G : E → F := fun y ↦ if hy : y ∈ Ω then g (j ⟨y, hy⟩) y else u y
  have hG (i : ι) : EqOn G (g i) (Ω ∩ U i) := fun y hy ↦ by
    simp only [G, hy.1, ↓reduceDIte]
    exact hgg _ _ ⟨⟨hy.1, hj _⟩, hy.2⟩
  refine ⟨G, contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_, hG,
    fun y (hy : y ∉ Ω) ↦ by simp [G, hy]⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hΩ hx)
  exact ⟨U i, hU i, hi, ((hg i).mono inter_subset_right).congr (hG i)⟩

end TauCeti
