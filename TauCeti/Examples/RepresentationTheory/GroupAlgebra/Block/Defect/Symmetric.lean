/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.DefectGroup.Principal
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.TraceMinimality
public import TauCeti.GroupTheory.Perm.FinThree.Complement
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.NormalPSubgroup

/-!
# The defects of the blocks of `S₃`, and the normal `p`-subgroup route

The Checks of `TauCeti.blockDefect` and of the route to `O_p(G)` on `S₃ = Equiv.Perm (Fin 3)`,
with `ρ` the `3`-cycle `finRotate 3`.

* At `p = 2`, the principal block `1 + ρ + ρ²` of `𝔽₂[S₃]` has defect `1`: its defect groups are
  the Sylow `2`-subgroups, of order `2 = 2¹`. The block `ρ + ρ² = Tr_1^{S₃}(ρ)` has defect `0`:
  the trivial subgroup is minimal with `ρ + ρ² ∈ Tr_1^{S₃}(𝔽₂[S₃])`, so it is the defect group.
* At `p = 3`, the alternating group `Q = A₃ = ⟨ρ⟩ ≅ C₃` is a normal `3`-subgroup of `S₃`, so it
  lies in every defect group of the single block `1` of `𝔽₃[S₃]` (`Br_Q(1) = 1 ≠ 0`). As
  `|S₃|₃ = 3`, the defect group is `A₃` itself, and the defect of the block is `1`.
-/

public section

namespace TauCeti.Examples.BlockDefectSymmetric

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.PrincipalBlockDefectExamples
  TauCeti.GroupAlgebraTraceMinimalityExamples

/-! ### `p = 2` -/

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

/-- The identity `1` is a block of `𝔽₃[S₃]`, the only one. -/
theorem isBlockIdempotent_one_zmod_three :
    IsBlockIdempotent (1 : Subalgebra.center (ZMod 3) (MonoidAlgebra (ZMod 3) S₃)) :=
  (isBlockIdempotent_iff_eq_one_zmod_three_s₃ 1).2 rfl

/-- **The normal `3`-subgroup route on `S₃`.** The normal `3`-subgroup `A₃ = ⟨ρ⟩` lies in every
defect group of the block `1` of `𝔽₃[S₃]`. -/
theorem alternatingGroup_le_of_isDefectGroup {D : Subgroup S₃}
    (hD : IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D) :
    alternatingGroup (Fin 3) ≤ D :=
  isBlockIdempotent_one_zmod_three.le_of_isDefectGroup_of_isPGroup_of_normal
    isPGroup_three_alternatingGroup_fin_three hD

/-- **The defect group of the block of `𝔽₃[S₃]` is `A₃ = ⟨ρ⟩ ≅ C₃`**: it contains the Sylow
`3`-subgroup `A₃`, which is maximal among `3`-subgroups. -/
theorem isDefectGroup_one_zmod_three_iff {D : Subgroup S₃} :
    IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D ↔ D = alternatingGroup (Fin 3) := by
  have hmax {D : Subgroup S₃}
      (hD : IsDefectGroup (ZMod 3) 3 (1 : MonoidAlgebra (ZMod 3) S₃) D) :
      D = alternatingGroup (Fin 3) :=
    (coe_alternatingGroupSylowThree ▸ alternatingGroupSylowThree.maximal_isPGroup).eq_of_ge
      hD.isPGroup (alternatingGroup_le_of_isDefectGroup hD)
  refine ⟨hmax, ?_⟩
  rintro rfl
  obtain ⟨D, hD⟩ := exists_isDefectGroup 3 (one_ne_zero : (1 : MonoidAlgebra (ZMod 3) S₃) ≠ 0)
  rwa [← hmax hD]

/-- **The block of `𝔽₃[S₃]` has defect `1`**: its defect group `A₃` has order `3 = 3¹`. -/
theorem blockDefect_one_zmod_three :
    blockDefect 3 (1 : MonoidAlgebra (ZMod 3) S₃) = 1 :=
  blockDefect_eq_of_forall_card (isDefectGroup_one_zmod_three_iff.2 rfl) fun D hD => by
    rw [isDefectGroup_one_zmod_three_iff.1 hD, card_alternatingGroup_fin_three, pow_one]

end TauCeti.Examples.BlockDefectSymmetric
