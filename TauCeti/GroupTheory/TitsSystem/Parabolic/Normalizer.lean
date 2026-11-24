/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Conjugate

/-!
# Parabolic subgroups of a Tits system are self-normalizing

Every subgroup containing the distinguished subgroup `B` of a Tits system is its own
normalizer. In particular this holds for every standard parabolic, including `B` itself.
Consequently a parabolic has no additional symmetries under conjugation beyond those
coming from its own elements; its conjugates can be parametrized by its cosets.

An element `g` normalizing an overgroup `P` of `B` conjugates `B` into `P`, so it lies in `P` by
`TauCeti.TitsSystem.mem_of_conj_subgroupB_le` from
`TauCeti.GroupTheory.TitsSystem.Parabolic.Conjugate`.

These are statements about abstract subgroups of a group with a BN-pair, without a
finiteness or sphericality assumption. They do not assert scheme-theoretic normalizer
equalities for parabolic subgroup schemes.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 5.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), §8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- Every subgroup containing the distinguished `B` of a Tits system is self-normalizing. -/
theorem normalizer_eq_of_subgroupB_le {P : Subgroup G} (hB : T.subgroupB ≤ P) :
    Subgroup.normalizer (P : Set G) = P := by
  refine le_antisymm (fun g hg ↦ ?_) Subgroup.le_normalizer
  exact T.mem_of_conj_subgroupB_le hB fun b hb ↦ (Subgroup.mem_normalizer_iff.mp hg b).mp (hB hb)

/-- Every standard parabolic of a Tits system is self-normalizing. -/
@[simp]
theorem normalizer_standardParabolic (J : Set T.simple) :
    Subgroup.normalizer (T.standardParabolic J : Set G) = T.standardParabolic J :=
  T.normalizer_eq_of_subgroupB_le (T.subgroupB_le_standardParabolic J)

/-- The distinguished subgroup `B` of a Tits system is self-normalizing. -/
@[simp]
theorem normalizer_subgroupB :
    Subgroup.normalizer (T.subgroupB : Set G) = T.subgroupB :=
  T.normalizer_eq_of_subgroupB_le le_rfl

end TauCeti.TitsSystem
