/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Basic
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# The quotient action on an abelian normal subgroup

If `N` is abelian and normal in `G`, conjugation on `N` factors through `G ⧸ N`.
`Subgroup.quotientConjugationAction` supplies this action explicitly, rather than as a global
instance. The quotient extension induces precisely this action, so its normalized sections
have factor sets with coefficients in this conjugation module.

The construction descends Mathlib's `MulAut.conjNormal` along the quotient homomorphism. When the
quotient `G ⧸ N` is identified with `Multiplicative (ZMod 2)` and elements outside `N` conjugate `N`
by inversion, the quotient conjugation action agrees with `TauCeti.invMulDistribMulAction`
(`Subgroup.invMulDistribMulAction_smul_eq_quotientConjugationAction`), and transports along any
kernel equivalence `eN : M ≃* N`
(`Subgroup.quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo`).
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

section Inversion

attribute [local instance] TauCeti.invMulDistribMulAction

/-- If `G ⧸ N` is identified with `Multiplicative (ZMod 2)` and elements outside `N` conjugate
`N` by inversion, then the quotient conjugation action on `N` equals
`TauCeti.invMulDistribMulAction` pulled back along `eG`. -/
theorem invMulDistribMulAction_smul_eq_quotientConjugationAction
    (eG : G ⧸ N ≃* Multiplicative (ZMod 2))
    (hinv : ∀ g ∉ N, ∀ x : N, MulAut.conjNormal g x = x⁻¹)
    (q : G ⧸ N) (x : N) :
    eG q • x = q • x := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  by_cases hg : g ∈ N
  · have h1 : (g : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hg
    rw [h1, map_one, one_smul, one_smul]
  · have hne : eG (g : G ⧸ N) ≠ 1 := fun h ↦
      hg ((QuotientGroup.eq_one_iff _).1 (eG.injective (h.trans (map_one eG).symm)))
    rw [TauCeti.invMulDistribMulAction_smul, ite_eq_right_iff.mpr (fun h ↦ absurd h hne),
      quotientConjugationAction_mk_smul, hinv g hg x]

/-- Identifying `N` with `M` via `eN` and `G ⧸ N` with `C₂` via `eG` intertwines
`TauCeti.invMulDistribMulAction` on `M` with the quotient conjugation action on `N` whenever
elements outside `N` conjugate `N` by inversion. -/
theorem quotientConjugationAction_smul_eq_of_mulEquiv_zmodTwo {M : Type*} [CommGroup M]
    (eN : M ≃* N) (eG : G ⧸ N ≃* Multiplicative (ZMod 2))
    (hinv : ∀ g ∉ N, ∀ x : N, MulAut.conjNormal g x = x⁻¹)
    (q : G ⧸ N) (m : M) :
    eN (eG q • m) = q • eN m :=
  (eN.toMonoidHom.map_invMulDistribMulAction_smul (eG q) m).trans
    (N.invMulDistribMulAction_smul_eq_quotientConjugationAction eG hinv q (eN m))

end Inversion

end Subgroup
