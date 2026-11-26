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
Sylow `2`-subgroups; the subgroup `⟨τ⟩` of order `2 = |S₃|₂` is one of them. The other block
`ρ + ρ²` has augmentation `2 = 0`, and the criterion says nothing about it (its defect group is
`1`).
-/

public section

namespace TauCeti.PrincipalBlockDefectExamples

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockExamples

/-- The transposition `τ = (0 1)` of `S₃`. -/
abbrev τ : S₃ := Equiv.swap 0 1

/-- **The defect groups of `1 + ρ + ρ²` are the Sylow `2`-subgroups of `S₃`**, by the
augmentation criterion. -/
theorem isDefectGroup_blockOneS₃_iff_sylow {D : Subgroup S₃} :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) D ↔
      ∃ S : Sylow 2 S₃, D = S :=
  isDefectGroup_iff_sylow_of_augmentation_ne_zero blockOneS₃.property
    (by rw [augmentation_blockOneS₃]; exact one_ne_zero)

/-- `|S₃|₂ = 2¹`: the exponent of `2` in `|S₃| = 3! = 6` is `1`, as `2 ∣ 6` while `2 ^ 2 ∤ 6`. -/
theorem factorization_card_two : (Nat.card S₃).factorization 2 = 1 := by
  rw [Nat.card_perm, Nat.card_fin, Nat.factorization_def _ Nat.prime_two]
  exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)

/-- The subgroup `⟨τ⟩` has order `2 = |S₃|₂`. -/
theorem card_zpowers_τ : Nat.card (Subgroup.zpowers τ) = 2 ^ (Nat.card S₃).factorization 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by decide) (by decide), factorization_card_two,
    pow_one]

/-- `⟨τ⟩` is a defect group of `1 + ρ + ρ²`: it is a Sylow `2`-subgroup. -/
theorem isDefectGroup_blockOneS₃_zpowers_τ :
    IsDefectGroup (ZMod 2) 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) (Subgroup.zpowers τ) :=
  isDefectGroup_blockOneS₃_iff_sylow.2 ⟨Sylow.ofCard _ card_zpowers_τ, (Sylow.coe_ofCard _ _).symm⟩

/-- The criterion does not apply to `ρ + ρ²`: its augmentation is `2 = 0`. -/
example : augmentation (ZMod 2) S₃ (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 :=
  augmentation_blockTwoS₃

end TauCeti.PrincipalBlockDefectExamples
