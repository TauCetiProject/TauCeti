/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Sporadic.McLaughlin.Perfect
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.McLaughlin.Basic

/-!
# Perfectness of the McLaughlin permutation model

The canonical ATLAS permutation model `TauCeti.Sporadic.McL` is perfect, because the exact
presented group `TauCeti.SporadicName.McL.Group` is (`TauCeti.Sporadic.isPerfect_group_McL`) and
surjects onto it (`TauCeti.Sporadic.exists_surjective_McL`). This does not assume finiteness or
simplicity of the presented group.

The argument is that of `TauCeti.Sporadic.isPerfect_HS` in
`TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Perfect`.

## Main results

* `TauCeti.Sporadic.isPerfect_McL`: the degree-275 permutation model is perfect.
-/

public section

namespace TauCeti.Sporadic

/-- The canonical ATLAS McLaughlin permutation model is perfect. -/
instance isPerfect_McL : Group.IsPerfect McL := by
  obtain ⟨f, hf⟩ := exists_surjective_McL
  exact Group.IsPerfect.ofSurjective hf

end TauCeti.Sporadic
