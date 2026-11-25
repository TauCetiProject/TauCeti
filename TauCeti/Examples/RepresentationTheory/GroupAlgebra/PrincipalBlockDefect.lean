/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.PrincipalBlock
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Principal

/-!
# The route to the Sylow defect groups on `𝔽₂[S₃]`

The principal block `e₀ = 1 + ρ + ρ²` of `𝔽₂[S₃]` has augmentation `1 · 1 + 1 · 2 = 1 ≠ 0`, so
`TauCeti.isDefectGroup_iff_sylow_of_augmentation_ne_zero` makes its defect groups exactly the
Sylow `2`-subgroups; the subgroup `⟨t⟩` of order `2 = |S₃|₂` is one of them. The other block
`ρ + ρ²` has augmentation `2 = 0`, and the criterion says nothing about it (its defect group is
`1`).

This is the Check "The route to the Sylow defect groups" of §6.2 *Defect groups* of the
RepresentationTheory/ModularCharactersAndBlocks roadmap.
-/

public section

namespace TauCeti.PrincipalBlockDefectExamples

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockExamples

/-- The transposition `t = (0 1)` of `S₃`. -/
abbrev t : S₃ := Equiv.swap 0 1

/-- **The defect groups of `1 + ρ + ρ²` are the Sylow `2`-subgroups of `S₃`**, by the
augmentation criterion. -/
theorem isDefectGroup_blockOneS₃_iff_sylow {D : Subgroup S₃} :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) D ↔
      ∃ S : Sylow 2 S₃, D = S :=
  isDefectGroup_iff_sylow_of_augmentation_ne_zero blockOneS₃.property
    (by rw [augmentation_blockOneS₃]; exact one_ne_zero)

/-- The subgroup `⟨t⟩` has order `2 = |S₃|₂`. -/
theorem card_zpowers_t : Nat.card (Subgroup.zpowers t) = 2 ^ (Nat.card S₃).factorization 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by decide) (by decide), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  have : (Nat.factorial 3).factorization 2 = 1 := by
    rw [show Nat.factorial 3 = 2 * 3 by decide, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [this, pow_one]

/-- `⟨t⟩` is a defect group of `1 + ρ + ρ²`: it is a Sylow `2`-subgroup. -/
theorem isDefectGroup_blockOneS₃_zpowers_t :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) (Subgroup.zpowers t) :=
  isDefectGroup_blockOneS₃_iff_sylow.2 ⟨Sylow.ofCard _ card_zpowers_t, rfl⟩

/-- The criterion does not apply to `ρ + ρ²`: its augmentation is `2 = 0`. -/
example : augmentation (ZMod 2) S₃ (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 :=
  augmentation_blockTwoS₃

end TauCeti.PrincipalBlockDefectExamples
