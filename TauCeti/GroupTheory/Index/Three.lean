/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Data.Fin.VecNotation

/-!
# Index three from three covering cosets

Let `H` be a subgroup of a group `G`. If some `g` has `g² ∉ H` and every element of `G` lies in
one of the left cosets `H`, `g H` and `g⁻¹ H`, then `H` has index three: the hypothesis `g² ∉ H`
rules out each coincidence `H = g H`, `H = g⁻¹ H` and `g H = g⁻¹ H`, so the classes of `1`, `g`
and `g⁻¹` enumerate `G ⧸ H` without repetition.

For example, at Tate's reduction symbol `IV*` the points of an elliptic curve with singular
reduction fall into two classes, one for each root of a residue quadratic, and negation exchanges
the classes. So if some point has singular reduction, the subgroup of points with nonsingular
reduction has index three; otherwise it is the whole group.

## Main results

* `Subgroup.index_eq_three_of_sq_notMem` and `AddSubgroup.index_eq_three_of_two_nsmul_notMem`: if
  `g² ∉ H` and every element lies in `H`, `g H` or `g⁻¹ H`, then `H.index = 3`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **Three covering cosets give index three.** If `g² ∉ H` and every `a` satisfies `a ∈ H`,
`g⁻¹ a ∈ H` or `g a ∈ H` (that is, `a` lies in `H`, `g H` or `g⁻¹ H`), then `H.index = 3`. -/
@[to_additive index_eq_three_of_two_nsmul_notMem /-- **Three covering cosets give index three.**
If `2 • g ∉ H` and every `a` satisfies `a ∈ H`, `-g + a ∈ H` or `g + a ∈ H` (that is, `a` lies in
`H`, `g + H` or `-g + H`), then `H.index = 3`. -/]
theorem index_eq_three_of_sq_notMem {g : G} (hg : g ^ 2 ∉ H)
    (h : ∀ a, a ∈ H ∨ g⁻¹ * a ∈ H ∨ g * a ∈ H) : H.index = 3 := by
  have hg₁ : g ∉ H := fun hg₁ ↦ hg (H.pow_mem hg₁ 2)
  -- `1`, `g` and `g⁻¹` represent the three classes of `G ⧸ H`
  have hf : Function.Bijective ![((1 : G) : G ⧸ H), (g : G ⧸ H), ((g⁻¹ : G) : G ⧸ H)] := by
    refine ⟨?_, QuotientGroup.mk_surjective.forall.2 fun a ↦ ?_⟩
    · simp [Function.Injective, Fin.forall_fin_succ, QuotientGroup.eq, ← pow_two, hg, hg₁]
    · simpa [Fin.exists_fin_succ, QuotientGroup.eq] using h a
  rw [index, ← Nat.card_eq_of_bijective _ hf, Nat.card_fin]

end Subgroup
