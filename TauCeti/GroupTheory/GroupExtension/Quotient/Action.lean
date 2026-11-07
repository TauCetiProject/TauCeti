/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Basic
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# The quotient action on an abelian normal subgroup

If `N` is abelian and normal in `G`, conjugation on `N` factors through `G ⧸ N`.
`Subgroup.quotientConjugationAction` supplies this action explicitly, rather than as a global
instance. The quotient extension induces precisely this action, so its normalized sections
have factor sets with coefficients in this conjugation module.

The construction descends Mathlib's `MulAut.conjNormal` along the quotient homomorphism.
-/

public section

namespace Subgroup

open scoped IsMulCommutative

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

/-- Conjugation on an abelian normal subgroup, viewed as an action of the quotient group.
Use `letI := N.quotientConjugationAction` to install the action locally. -/
@[instance_reducible]
def quotientConjugationAction : MulDistribMulAction (G ⧸ N) N :=
  MulDistribMulAction.compHom N (QuotientGroup.lift N MulAut.conjNormal fun g hg => by
    refine MonoidHom.mem_ker.mpr ?_
    apply MulEquiv.ext
    intro n
    rw [← Subtype.coe_mk g hg, MulAut.conjNormal_val]
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_comm _ n, mul_inv_cancel_right])

attribute [local instance] quotientConjugationAction

/-- A coset acts on `N` by conjugation by any representative. -/
@[simp]
theorem quotientConjugationAction_mk_smul (g : G) (n : N) :
    (g : G ⧸ N) • n = MulAut.conjNormal g n :=
  congrArg (fun f : MulAut N => f n) (QuotientGroup.lift_mk N _ g)

/-- The quotient extension induces the quotient conjugation action on its kernel. -/
theorem quotientExtension_inducesAction :
    TauCeti.GroupExtension.InducesAction N.quotientExtension := by
  rw [TauCeti.GroupExtension.inducesAction_iff]
  intro g n
  apply Subtype.ext
  have h := GroupExtension.inl_conjAct_comm N.quotientExtension (e := g) (n := n)
  simpa only [quotientExtension_inl, quotientExtension_rightHom, subtype_apply,
    QuotientGroup.mk'_apply, quotientConjugationAction_mk_smul, MulAut.conjNormal_apply] using h

end Subgroup
