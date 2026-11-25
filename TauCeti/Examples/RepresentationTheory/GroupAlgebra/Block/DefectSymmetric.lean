/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNormal
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.TraceMinimality
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.NormalPSubgroup

/-!
# The defects of the blocks of `S₃`, and the normal `p`-subgroup route

The Checks of `TauCeti.blockDefect` and of the route to `O_p(G)` on `S₃ = Equiv.Perm (Fin 3)`,
with `ρ` the `3`-cycle `finRotate 3`.

* At `p = 2`, the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]` has defect `1`: its defect groups are
  the Sylow `2`-subgroups, of order `2 = 2¹`. The block `ρ + ρ² = Tr_1^{S₃}(ρ)` has defect `0`:
  the trivial subgroup is minimal with `ρ + ρ² ∈ Tr_1^{S₃}(𝔽₂[S₃])`, so it is the defect group.
* At `p = 3`, the subgroup `Q = ⟨ρ⟩ ≅ C₃` is a normal `3`-subgroup of `S₃`, so it lies in every
  defect group of the single block `1` of `𝔽₃[S₃]` (`Br_Q(1) = 1 ≠ 0`). As `|S₃|₃ = 3`, the
  defect group is `⟨ρ⟩` itself, and the defect of the block is `1`.
-/

public section

namespace TauCeti.Examples.BlockDefectSymmetric

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockDefectExamples
  TauCeti.GroupAlgebraTraceMinimalityExamples

/-! ### `p = 2` -/

/-- `|S₃|₂ = 2¹`: the exponent of `2` in `|S₃| = 6` is `1`. -/
theorem factorization_card_two : (Nat.card S₃).factorization 2 = 1 := by
  rw [Nat.card_perm, Nat.card_fin, Nat.factorization_def _ Nat.prime_two]
  exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)

/-- **The principal block of `𝔽₂[S₃]` has defect `1`**: its defect groups are the Sylow
`2`-subgroups, of order `2 = 2¹`. -/
theorem blockDefect_blockOneS₃ :
    blockDefect 2 (blockOneS₃ : MonoidAlgebra (ZMod 2) S₃) = 1 := by
  rw [← factorization_card_two]
  exact isBlockIdempotent_blockOneS₃.blockDefect_eq_iff_forall_sylow.2 fun S =>
    isDefectGroup_blockOneS₃_iff_sylow.2 ⟨S, rfl⟩

/-- The trivial subgroup is a defect group of the block `ρ + ρ²` of `𝔽₂[S₃]`: it is minimal with
`ρ + ρ² ∈ Tr_1^{S₃}(𝔽₂[S₃])`, as `ρ + ρ² = Tr_1^{S₃}(ρ)`. -/
theorem isDefectGroup_blockTwoS₃_bot :
    IsDefectGroup (ZMod 2) 2 (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) ⊥ :=
  isBlockIdempotent_blockTwoS₃.isDefectGroup_iff_minimal.2
    ⟨⟨_, relTrace_bot_top_of_ρ.trans coe_blockTwoS₃.symm⟩, fun _ _ _ => bot_le⟩

/-- **The block `ρ + ρ²` of `𝔽₂[S₃]` has defect `0`.** -/
theorem blockDefect_blockTwoS₃ :
    blockDefect 2 (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) = 0 :=
  isBlockIdempotent_blockTwoS₃.blockDefect_eq_zero_iff.2 isDefectGroup_blockTwoS₃_bot

/-! ### `p = 3` -/

/-- `⟨ρ⟩` has order `3`. -/
theorem card_zpowers_ρ : Nat.card (Subgroup.zpowers ρ) = 3 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 3) (by decide) (by decide)]

/-- `⟨ρ⟩` has index `2` in `S₃`. -/
theorem index_zpowers_ρ : (Subgroup.zpowers ρ).index = 2 := by
  have h := (Subgroup.zpowers ρ).index_mul_card
  rw [card_zpowers_ρ, Nat.card_perm, Nat.card_fin] at h
  simp only [Nat.factorial] at h
  omega

/-- `⟨ρ⟩`, of index `2`, is normal in `S₃`. -/
instance normal_zpowers_ρ : (Subgroup.zpowers ρ).Normal :=
  Subgroup.normal_of_index_eq_two index_zpowers_ρ

/-- `⟨ρ⟩` is a `3`-group. -/
theorem isPGroup_zpowers_ρ : IsPGroup 3 (Subgroup.zpowers ρ) :=
  IsPGroup.of_card (n := 1) (by rw [card_zpowers_ρ, pow_one])

/-- The identity `1` is a block of `𝔽₃[S₃]`, the only one. -/
theorem isBlockIdempotent_one_zmod_three :
    IsBlockIdempotent (1 : Subalgebra.center (ZMod 3) (MonoidAlgebra (ZMod 3) S₃)) :=
  (isBlockIdempotent_iff_eq_one_zmod_three_s₃ 1).2 rfl

/-- `Br_{⟨ρ⟩}(1) = 1 ≠ 0` in `𝔽₃[S₃]`. -/
theorem brauerProjection_zpowers_ρ_one_ne_zero :
    brauerProjection (Subgroup.zpowers ρ) (1 : MonoidAlgebra (ZMod 3) S₃) ≠ 0 := by
  rw [brauerProjection_one]
  exact one_ne_zero

/-- **The normal `3`-subgroup route on `S₃`.** The normal `3`-subgroup `⟨ρ⟩` lies in every defect
group of the block `1` of `𝔽₃[S₃]`. -/
theorem zpowers_ρ_le_of_isDefectGroup {D : Subgroup S₃}
    (hD : IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D) :
    Subgroup.zpowers ρ ≤ D :=
  isBlockIdempotent_one_zmod_three.le_of_isDefectGroup_of_isPGroup_of_normal isPGroup_zpowers_ρ
    hD

/-- A `3`-subgroup of `S₃` containing `⟨ρ⟩` is `⟨ρ⟩`: its order is a power of `3` dividing `6`,
so at most `3`. -/
theorem eq_zpowers_ρ_of_le {D : Subgroup S₃} (hD : IsPGroup 3 D) (hle : Subgroup.zpowers ρ ≤ D) :
    D = Subgroup.zpowers ρ := by
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have h6 : 3 ^ n ∣ 6 := by
    rw [← hn]
    have := Subgroup.card_subgroup_dvd_card D
    rwa [Nat.card_perm, Nat.card_fin] at this
  have hn1 : n ≤ 1 := by
    by_contra h
    exact absurd ((Nat.pow_dvd_pow 3 (by omega : 2 ≤ n)).trans h6) (by decide)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hn, card_zpowers_ρ]
  calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by decide) hn1
    _ = 3 := pow_one 3

/-- **The defect group of the block of `𝔽₃[S₃]` is `⟨ρ⟩ ≅ C₃`.** -/
theorem isDefectGroup_one_zmod_three_iff {D : Subgroup S₃} :
    IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D ↔ D = Subgroup.zpowers ρ := by
  refine ⟨fun hD => eq_zpowers_ρ_of_le hD.isPGroup (zpowers_ρ_le_of_isDefectGroup hD), ?_⟩
  rintro rfl
  obtain ⟨D, hD⟩ := exists_isDefectGroup 3 (one_ne_zero : (1 : MonoidAlgebra (ZMod 3) S₃) ≠ 0)
  rwa [← eq_zpowers_ρ_of_le hD.isPGroup (zpowers_ρ_le_of_isDefectGroup hD)]

/-- **The block of `𝔽₃[S₃]` has defect `1`**: its defect group `⟨ρ⟩` has order `3 = 3¹`. -/
theorem blockDefect_one_zmod_three :
    blockDefect 3 (1 : MonoidAlgebra (ZMod 3) S₃) = 1 := by
  have h := isBlockIdempotent_one_zmod_three.card_eq_pow_blockDefect
    (isDefectGroup_one_zmod_three_iff.2 rfl)
  rw [Subalgebra.coe_one, card_zpowers_ρ] at h
  exact Nat.pow_right_injective (a := 3) (by decide) (h.symm.trans (pow_one 3).symm)

end TauCeti.Examples.BlockDefectSymmetric
