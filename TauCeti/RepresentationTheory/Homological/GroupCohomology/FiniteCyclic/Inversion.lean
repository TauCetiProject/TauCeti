/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import TauCeti.RepresentationTheory.Rep.OfMulDistribMulAction
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Data.ZMod.Torsion

/-!
# Second cohomology of the inversion action of `C₂` on `C_{2n}`

For every nonzero `n : ℕ`, `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n` identifies
`H²(C₂, C_{2n}^{inv})` additively with `ZMod 2`, composing the general negation-action
identification `Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy` with
`TauCeti.submoduleTorsionByEquivAddSubgroup`, `AddEquiv.torsionByCongr`, and
`TauCeti.zmodTorsionByEquiv`.

## Main definitions

* `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo`: `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2`
  for `n ≠ 0`.

## Main results

* `Rep.FiniteCyclicGroup.natCard_groupCohomologyTwoInv`,
  `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo_groupCohomologyπEven`,
  `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo_symm_apply`: cardinality and
  forward/inverse evaluation of `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2`.
-/

public section

namespace Rep.FiniteCyclicGroup

section Inversion

open CategoryTheory groupCohomology TauCeti

attribute [local instance] invMulDistribMulAction

/-- **Second cohomology of the inversion action on `C_{2n}`.** For every nonzero `n`,
`H²(C₂, C_{2n}^{inv})` is additively isomorphic to `ZMod 2`, obtained by composing the
`2`-torsion identification `Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy` with
`TauCeti.submoduleTorsionByEquivAddSubgroup`, `AddEquiv.torsionByCongr`, and
`TauCeti.zmodTorsionByEquiv`. -/
noncomputable def groupCohomologyTwoInvEquivZModTwo (n : ℕ) [NeZero n] :
    groupCohomology
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 ≃+
      ZMod 2 :=
  let e₁ :=
    (groupCohomologyEvenEquivTorsionBy
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
      (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one
      ((orderOf_ofAdd_one_zmod 2).symm ▸ even_two)
      (Rep.ofMulDistribMulAction_ρ_eq_neg_of_smul_eq_inv invMulDistribMulAction_ofAdd_one_smul)
      2 even_two).toAddEquiv
  let e₁₂ :=
    submoduleTorsionByEquivAddSubgroup
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))).V 2
  let e₂ :=
    AddEquiv.torsionByCongr
      ((Rep.toAdditive (M := Multiplicative (ZMod 2)) (G := Multiplicative (ZMod (2 * n)))).trans
        (AddEquiv.additiveMultiplicative (ZMod (2 * n))))
      2
  ((e₁.trans e₁₂).trans e₂).trans (zmodTorsionByEquiv 2 n).symm

/-- `H²(C₂, C_{2n}^{inv})` has order `2` for every nonzero `n`. -/
theorem natCard_groupCohomologyTwoInv (n : ℕ) [NeZero n] :
    Nat.card (groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2) =
      2 := by
  rw [Nat.card_congr (groupCohomologyTwoInvEquivZModTwo n).toEquiv, Nat.card_zmod]

/-- Under `groupCohomologyTwoInvEquivZModTwo n`, the periodic-resolution class of a `1`-fixed
element `y` corresponds to the unique residue `x : ZMod 2` satisfying `x.val * n = a` in
`ZMod (2 * n)`. -/
theorem groupCohomologyTwoInvEquivZModTwo_groupCohomologyπEven (n : ℕ) [NeZero n]
    (y : LinearMap.ker
      ((Rep.applyAsHom
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
        (Multiplicative.ofAdd (1 : ZMod 2)) - 𝟙 _).hom.toLinearMap))
    (x : ZMod 2) :
    groupCohomologyTwoInvEquivZModTwo n
      (groupCohomologyπEven
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
        (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one 2 even_two y) =
      x ↔
      ((x.val * n : ℕ) : ZMod (2 * n)) =
        Multiplicative.toAdd (Additive.toMul (Rep.toAdditive y.val)) := by
  rw [groupCohomologyTwoInvEquivZModTwo]
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
  rw [groupCohomologyEvenEquivTorsionBy_groupCohomologyπEven,
    zmodTorsionByEquiv_symm_apply_eq_iff]
  simp [AddEquiv.additiveMultiplicative_apply, -Rep.toAdditive_apply]

/-- Under `(groupCohomologyTwoInvEquivZModTwo n).symm`, a residue `x : ZMod 2` maps to the
periodic-resolution class of the `1`-fixed element `(x.val * n : ℕ)` in `ZMod (2 * n)`. -/
@[simp]
theorem groupCohomologyTwoInvEquivZModTwo_symm_apply (n : ℕ) [NeZero n] (x : ZMod 2) :
    (groupCohomologyTwoInvEquivZModTwo n).symm x =
      groupCohomologyπEven
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
        (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one 2 even_two
        ⟨(Rep.toAdditive (M := Multiplicative (ZMod 2))
              (G := Multiplicative (ZMod (2 * n)))).symm
            (Additive.ofMul (Multiplicative.ofAdd ((x.val * n : ℕ) : ZMod (2 * n)))),
          Rep.mem_ker_applyAsHom_sub_of_smul_eq_self (by
            rw [invMulDistribMulAction_ofAdd_one_smul, ← ofAdd_neg]
            congr 1
            rw [neg_eq_iff_add_eq_zero]
            norm_cast
            have hmul : x.val * n + x.val * n = x.val * (2 * n) := by ring
            rw [hmul, Nat.cast_mul, ZMod.natCast_self, mul_zero])⟩ := by
  rw [AddEquiv.symm_apply_eq, eq_comm, groupCohomologyTwoInvEquivZModTwo_groupCohomologyπEven]
  simp

end Inversion

end Rep.FiniteCyclicGroup
