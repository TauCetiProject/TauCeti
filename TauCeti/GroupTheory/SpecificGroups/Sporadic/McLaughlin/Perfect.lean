/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.McLaughlin.Basic
public import TauCeti.GroupTheory.Presentation.Perfect

/-!
# Perfectness of the McLaughlin presentation and permutation model

The transcribed McLaughlin presentation `TauCeti.Sporadic.mclPresentation` is perfect, already from
its first, second and fourth relations `a² = b⁵ = (ab)¹¹ = 1`, whose exponents are pairwise
coprime (`TauCeti.GroupPresentation.isPerfect_of_coprime`).

The canonical ATLAS permutation model `TauCeti.Sporadic.McL` is consequently perfect through the
existing presentation surjection `TauCeti.Sporadic.exists_surjective_McL`. Neither statement
assumes finiteness or simplicity of the presented group.

## Main results

* `TauCeti.Sporadic.isPerfect_mclPresentation`: the transcribed presentation is perfect.
* `TauCeti.Sporadic.isPerfect_group_McL`: so is the exact carrier attached to the name `McL`.
* `TauCeti.Sporadic.isPerfect_McL`: so is the degree-275 permutation model.

## References

* J. N. Bray, ATLAS presentation `McLG1-P1`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/McLG1-P1>.
-/

public section

namespace TauCeti.Sporadic

/-- The exact fifteen-relator McLaughlin presentation is perfect. -/
instance isPerfect_mclPresentation : Group.IsPerfect mclPresentation.Group := by
  apply mclPresentation.isPerfect_of_coprime mclPresentation_generatorCount
    (a := 2) (b := 5) (c := 11)
  · rw [mclPresentation_transcribed]; simp
  · rw [mclPresentation_transcribed]; simp
  · rw [mclPresentation_transcribed]; simp
  all_goals decide

/-- The exact carrier attached to the McLaughlin sporadic name is perfect. -/
instance isPerfect_group_McL : Group.IsPerfect SporadicName.McL.Group := by
  exact (congrArg (fun P : GroupPresentation => Group.IsPerfect P.Group)
    SporadicName.presentation_McL).mpr isPerfect_mclPresentation

/-- The canonical ATLAS McLaughlin permutation model is perfect. -/
instance isPerfect_McL : Group.IsPerfect McL := by
  obtain ⟨f, hf⟩ := exists_surjective_McL
  exact Group.IsPerfect.ofSurjective hf

end TauCeti.Sporadic
