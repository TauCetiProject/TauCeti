/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Defect.Symmetric
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DomCongr

/-!
# Examples: the Brauer correspondent at `D = 1`

The `D = 1` Check of ModularCharactersAndBlocks §7.1 on `𝔽₂[S₃]`: `N_{S₃}(1) = S₃`, the Brauer
projection at `1` is the identity, and the Brauer correspondent of the defect-zero block `ρ + ρ²`
(`ρ` a `3`-cycle) is a block of `𝔽₂[N_{S₃}(1)]` of defect zero.
-/

public section

namespace TauCeti.Examples.BrauerCorrespondentBot

open _root_.MonoidAlgebra TauCeti.GroupAlgebraBlockExamples TauCeti.Examples.BlockDefectSymmetric

-- `N_{S₃}(1) = S₃`.
example : Subgroup.normalizer ((⊥ : Subgroup S₃) : Set S₃) = ⊤ :=
  normalizer_bot_eq_top

-- The Brauer correspondent at `1` keeps every coefficient.
example (x : MonoidAlgebra (ZMod 2) S₃) (g : S₃) :
    (brauerCorrespondent ⊥ x).coeff (normalizerBotEquiv g) = x.coeff g := by
  rw [brauerCorrespondent_bot, coeff_domCongr, MulEquiv.symm_apply_apply]

-- The Brauer correspondent of the defect-zero block `ρ + ρ²` is a block of `𝔽₂[N_{S₃}(1)]`.
example : ∃ b' : Subalgebra.center (ZMod 2)
      (MonoidAlgebra (ZMod 2) (Subgroup.normalizer ((⊥ : Subgroup S₃) : Set S₃))),
    IsBlockIdempotent b' ∧ (b' : MonoidAlgebra (ZMod 2) _) =
      brauerCorrespondent ⊥ (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃) :=
  isBlockIdempotent_blockTwoS₃.isBlockIdempotent_brauerCorrespondent_bot

-- It has defect group `1`.
example : IsDefectGroup (ZMod 2) 2
    (brauerCorrespondent ⊥ (blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃)) ⊥ :=
  isDefectGroup_blockTwoS₃_bot.isDefectGroup_brauerCorrespondent_bot

end TauCeti.Examples.BrauerCorrespondentBot
