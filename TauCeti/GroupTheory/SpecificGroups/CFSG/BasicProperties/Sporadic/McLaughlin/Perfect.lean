/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Perfect
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Perfectness of the McLaughlin presentation

The exact carrier `TauCeti.SporadicName.McL.Group`, presented by the transcribed McLaughlin
presentation `TauCeti.Sporadic.mclPresentation`, is perfect, already from the first, second and
fourth relations `a² = b⁵ = (ab)¹¹ = 1`, whose exponents are pairwise coprime
(`TauCeti.GroupPresentation.isPerfect_of_coprime`). This does not assume finiteness or simplicity
of the presented group, and does not use the permutation model.

The proof is that of `TauCeti.Sporadic.isPerfect_hsPresentation` in
`TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Perfect`, whose presentation has relators
of the same three orders.

## Main results

* `TauCeti.Sporadic.isPerfect_group_McL`: the exact carrier attached to the name `McL` is perfect.

## References

* J. N. Bray, ATLAS presentation `McLG1-P1`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/McLG1-P1>.
-/

public section

namespace TauCeti.Sporadic

/-- The exact carrier attached to the McLaughlin sporadic name, presented by the fifteen-relator
McLaughlin presentation, is perfect. -/
instance isPerfect_group_McL : Group.IsPerfect SporadicName.McL.Group := by
  refine (congrArg (fun P : GroupPresentation => Group.IsPerfect P.Group)
    SporadicName.presentation_McL).mpr ?_
  apply mclPresentation.isPerfect_of_coprime mclPresentation_generatorCount
    (a := 2) (b := 5) (c := 11)
  · rw [mclPresentation_transcribed]; simp
  · rw [mclPresentation_transcribed]; simp
  · rw [mclPresentation_transcribed]; simp
  all_goals decide

end TauCeti.Sporadic
