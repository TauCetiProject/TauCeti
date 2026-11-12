/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Simple

/-!
# Simplicity of the Suzuki groups on the classification list

The Suzuki index `²B₂(2^(2m+1))` of the classification list carries, through the dispatcher
`TauCeti.ValidLieTypeIndex.Group`, the derived subgroup of the fixed points of the Suzuki Steinberg
endomorphism modulo its centre. That is the candidate group `TauCeti.SuzukiLieIndex.Group` of the
Suzuki family, which `TauCeti.SuzukiLieIndex.isSimpleGroup_group` identifies with the simple group
`Sz(2^(2m+1))`. This file reads that result on the dispatcher, for every parameter `m` the
validity predicate retains.

## Main results

* `TauCeti.ValidLieTypeIndex.isSimpleGroup_suzuki`: the group attached to every valid Suzuki index
  is simple.
-/

public section

namespace TauCeti.ValidLieTypeIndex

/-- **The Suzuki groups on the classification list are simple.** -/
theorem isSimpleGroup_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_suzuki]
  exact SuzukiLieIndex.isSimpleGroup_group m hv

end TauCeti.ValidLieTypeIndex

end
