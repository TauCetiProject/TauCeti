/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cyclic.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic.Inversion
import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# Cohomology of cyclic extensions of `C₂` by `C_{2n}` acting by inversion

This module specializes `TauCeti.GroupTheory.GroupExtension.Cyclic.Cohomology` and
`TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic.Inversion` to extensions of
`C₂ = Multiplicative (ZMod 2)` by `C_{2n} = Multiplicative (ZMod (2 * n))` inducing the inversion
action `TauCeti.invMulDistribMulAction`:

* `GroupExtension.Section.groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff`:
  evaluates the extension class under `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n`
  directly in `ZMod 2`.
-/

public section

namespace TauCeti.GroupExtension

open Rep.FiniteCyclicGroup

section InversionTwo

attribute [local instance] TauCeti.invMulDistribMulAction

/-- **Evaluation of `groupCohomologyTwoInvEquivZModTwo` on an extension class.** For any extension
`S` of `C₂` by `C_{2n}` inducing the inversion action, if `e` lifts `ofAdd 1` and
`S.inl (ofAdd a) = e ^ 2`, then `groupCohomologyTwoInvEquivZModTwo n` maps the cohomology class
of any normalized section of `S` to the unique `x : ZMod 2` satisfying `x.val * n = a` in
`ZMod (2 * n)`. -/
theorem
    _root_.GroupExtension.Section.groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff
    {n : ℕ} [NeZero n] {E : Type*} [Group E]
    {S : GroupExtension (Multiplicative (ZMod (2 * n))) E (Multiplicative (ZMod 2))}
    (σ : S.Section) (hσ : σ 1 = 1) (hact : S.InducesAction)
    {e : E} (he : S.rightHom e = Multiplicative.ofAdd 1) {a : ZMod (2 * n)}
    (ha : S.inl (Multiplicative.ofAdd a) = e ^ 2) (x : ZMod 2) :
    groupCohomologyTwoInvEquivZModTwo n (factorSet σ hσ hact).cohomologyClass = x ↔
      (x.val * n : ℕ) = a := by
  have ha' : S.inl (Multiplicative.ofAdd a) =
      e ^ orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [TauCeti.orderOf_ofAdd_one_zmod, ha]
  rw [σ.cohomologyClass_factorSet_eq_groupCohomologyπEven hσ hact
      Multiplicative.mem_zpowers_ofAdd_one he ha',
    groupCohomologyTwoInvEquivZModTwo_groupCohomologyπEven]
  simp

end InversionTwo

end TauCeti.GroupExtension
