/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Spans in modules over `ℤ/nℤ`

In a `ZMod n`-module, additive generation and linear generation agree. This identifies
the group-theoretic generation criterion for an elementary abelian group with a spanning
criterion in its associated vector space. For `n = p` prime it lets a basis be extracted from any
generating set of a finite elementary abelian `p`-group, with the size of the generated subgroup
read off from the size of the basis.

## Main results

* `Set.span_zmod_eq_addSubgroupClosure`: the span of a set over `ℤ/nℤ` is the additive subgroup
  it generates.
* `Set.exists_finset_subset_addSubgroupClosure_eq_natCard_eq_pow`: in a finite `𝔽_p`-vector space
  every set contains a finite subset generating the same additive subgroup, which has `p ^ #b`
  elements.
-/

public section

namespace Set

/-- The span over `ℤ/nℤ` has the same underlying additive subgroup as the subgroup generated
by the set. This also includes `n = 0`, where `ZMod 0 = ℤ`. -/
@[simp]
theorem span_zmod_eq_addSubgroupClosure {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    (s : Set M) :
    (Submodule.span (ZMod n) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · exact (Submodule.span_le (p := (AddSubgroup.closure s).toZModSubmodule n)).mpr
      AddSubgroup.subset_closure
  · exact (AddSubgroup.closure_le _).mpr Submodule.subset_span

/-- **A generating set of a finite elementary abelian `p`-group contains a basis.** In a finite
`𝔽_p`-vector space every set `s` contains a finite subset `b` generating the same additive
subgroup, and that subgroup has exactly `p ^ #b` elements: `b` is a basis of the span of `s`. -/
theorem exists_finset_subset_addSubgroupClosure_eq_natCard_eq_pow {p : ℕ} [Fact p.Prime]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Finite M] (s : Set M) :
    ∃ b : Finset M, (b : Set M) ⊆ s ∧ AddSubgroup.closure (b : Set M) = AddSubgroup.closure s ∧
      Nat.card (AddSubgroup.closure s) = p ^ b.card := by
  obtain ⟨b, hbs, hcard, hbspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn (ZMod p) s
  refine ⟨b, hbs, ?_, ?_⟩
  · rw [← span_zmod_eq_addSubgroupClosure (n := p), ← span_zmod_eq_addSubgroupClosure (n := p),
      hbspan]
  · rw [hcard, ← span_zmod_eq_addSubgroupClosure (n := p),
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Submodule.mem_toAddSubgroup _),
      Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

end Set
