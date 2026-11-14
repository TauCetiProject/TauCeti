/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Basic
public import TauCeti.GroupTheory.Presentation.Perfect

/-!
# Perfectness of the Higman--Sims presentation and permutation model

The exact Higman--Sims presentation is perfect, already from its first three relations
`a² = b⁵ = (ab)¹¹ = 1`, whose exponents are pairwise coprime.
The canonical ATLAS permutation model is consequently perfect through the existing presentation
surjection. Neither statement assumes finiteness or simplicity of the presented group.

## References

* J. N. Bray, ATLAS presentation `HSG1-P1`, demonstration of correctness,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HSG1-P1>.
-/

public section

namespace TauCeti.Sporadic

/-- The exact thirteen-relator Higman--Sims presentation is perfect. -/
instance isPerfect_hsPresentation : Group.IsPerfect hsPresentation.Group := by
  apply hsPresentation.isPerfect_of_coprime hsPresentation_generatorCount
    (a := 2) (b := 5) (c := 11)
  · rw [hsPresentation_transcribed]; simp
  · rw [hsPresentation_transcribed]; simp
  · rw [hsPresentation_transcribed]; simp
  all_goals decide

/-- The exact carrier attached to the Higman--Sims sporadic name is perfect. -/
instance isPerfect_group_HS : Group.IsPerfect SporadicName.HS.Group := by
  exact (congrArg (fun P : GroupPresentation => Group.IsPerfect P.Group)
    SporadicName.presentation_HS).mpr isPerfect_hsPresentation

/-- The canonical ATLAS Higman--Sims permutation model is perfect. -/
instance isPerfect_HS : Group.IsPerfect HS := by
  obtain ⟨f, hf⟩ := exists_surjective_HS
  exact Group.IsPerfect.ofSurjective hf

end TauCeti.Sporadic
