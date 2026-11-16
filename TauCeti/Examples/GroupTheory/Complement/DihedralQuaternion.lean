/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.Algebra.GroupAction.Inversion
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.GroupExtension.Relabel
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.Data.ZMod.Torsion
import TauCeti.GroupTheory.GroupExtension.Cyclic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Dihedral and generalized quaternion extensions with the same inversion action

For every positive integer `n`, the dihedral group `DihedralGroup (2 * n)` and the generalized
quaternion group `QuaternionGroup n` both sit in a short exact sequence
`1 → C_{2n} → E → C₂ → 1` whose quotient `C₂` acts on the cyclic rotation subgroup `C_{2n}` by
inversion (`TauCeti.invMulDistribMulAction`). This file transports both quotient extensions to
the common kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)` via
`GroupExtension.relabel` and `TauCeti.GroupExtension.relabelCohomologyIso`, and separates them
inside the single cohomology group `H²(C₂, C_{2n}^{inv}) ≅ ℤ/2`.

* **Cohomology of the inversion action.** Specializing
  `Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy` to `C₂` acting on `C_{2n}` by
  inversion gives an additive equivalence `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2`
  (`cohomologyInvEquivZModTwo`), sending the extension class of a lift `e` of the generator with
  `S.inl (ofAdd a) = e ^ 2` to the unique residue `x : ZMod 2` with `x.val * n = a` in
  `ZMod (2 * n)`.
* **Same kernel, same quotient, same action.** Identifying the rotation subgroups with
  `Multiplicative (ZMod (2 * n))` and the quotients with `Multiplicative (ZMod 2)`
  (`TauCeti.dihedralQuotientEquiv`, `TauCeti.quaternionQuotientEquiv`) intertwines both quotient
  conjugation actions with `TauCeti.invMulDistribMulAction` (`dihedralRotationsMulEquiv_symm_smul`,
  `quaternionRotationsMulEquiv_symm_smul`), so both relabelled extensions `dihedralExtension n`
  and `quaternionExtension n` induce the same action.
* **Separation in `H²(C₂, C_{2n}^{inv})`.** Under `cohomologyInvEquivZModTwo n`, the dihedral
  extension class maps to `0` (`(sr 0) ^ 2 = 1`) and the quaternion extension class maps to `1`
  (`(xa 0) ^ 2 = a n`). Thus the two classes are distinct, exhaust `H²(C₂, C_{2n}^{inv})`, witness
  that the two extensions are inequivalent, and separate splitting from non-splitting:
  `dihedralRotations (2 * n)` has a complement while `quaternionRotations n` has none
  (`not_exists_isComplement'_quaternionRotations`).
* **The order-`8` case (`n = 2`) and coprime contrast.** At `n = 2`, `D₈` and `Q₈` are extensions
  of `C₂` by `C₄` with `|C₄| = 4` and `[E : C₄] = 2` not coprime
  (`not_coprime_card_index_dihedralFour`, `not_coprime_card_index_quaternionTwo`), and every
  involution of `QuaternionGroup n` (`n ≠ 0`) lies inside the rotation subgroup
  (`TauCeti.sq_eq_one_iff_quaternionGroup`). By contrast, for any Klein four-group `V` and every
  action of `C₃` on `V`, coprimality `gcd(3, 4) = 1` forces `H^{k+1}(C₃, V) = 0`
  (`subsingleton_groupCohomology_zmodThree_kleinFour`).

## Main definitions

* `TauCeti.Examples.DihedralQuaternion.cohomologyInvEquivZModTwo`:
  `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2` for `n ≠ 0`.
* `TauCeti.Examples.DihedralQuaternion.dihedralExtension`,
  `TauCeti.Examples.DihedralQuaternion.quaternionExtension`: the dihedral and quaternion quotient
  extensions relabelled to `Multiplicative (ZMod (2 * n))` and `Multiplicative (ZMod 2)`.
* `TauCeti.Examples.DihedralQuaternion.dihedralExtensionClass`,
  `TauCeti.Examples.DihedralQuaternion.quaternionExtensionClass`: their cohomology classes inside
  the common group `H²(C₂, C_{2n}^{inv})`.

## Main results

* `TauCeti.Examples.DihedralQuaternion.cohomologyInvEquivZModTwo_dihedralExtensionClass`,
  `TauCeti.Examples.DihedralQuaternion.cohomologyInvEquivZModTwo_quaternionExtensionClass`: the
  two classes map to `0` and `1` in `ZMod 2`.
* `TauCeti.Examples.DihedralQuaternion.eq_dihedralExtensionClass_or_eq_quaternionExtensionClass`:
  the dihedral and quaternion classes exhaust `H²(C₂, C_{2n}^{inv})`.
* `TauCeti.Examples.DihedralQuaternion.isEmpty_equiv_dihedralExtension_quaternionExtension`: the
  relabelled dihedral and quaternion extensions are not equivalent.
* `TauCeti.Examples.DihedralQuaternion.not_exists_isComplement'_quaternionRotations`: the
  rotation subgroup of `QuaternionGroup n` (`n ≠ 0`) has no complement.
* `TauCeti.Examples.DihedralQuaternion.subsingleton_groupCohomology_zmodThree_kleinFour`:
  `H^{k+1}(C₃, V) = 0` for every Klein four-group `V` and every `C₃`-action.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter IV, §3.
-/

public section

namespace TauCeti.Examples.DihedralQuaternion

open _root_.groupCohomology
open scoped IsMulCommutative IsKleinFour

/-! ### Cohomology of `C₂` acting by inversion on `C_{2n}` -/

section CohomologyInv

attribute [local instance] invMulDistribMulAction

private theorem even_orderOf_ofAdd_one_zmod_two :
    Even (orderOf (Multiplicative.ofAdd (1 : ZMod 2))) := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact even_two

/-- Identify the `2`-torsion of the representation `Rep.ofMulDistribMulAction C₂ C_{2n}` with
`AddSubgroup.torsionBy (ZMod (2 * n)) 2`. -/
private def repInvTorsionByTwoEquiv (n : ℕ) :
    Submodule.torsionBy ℤ
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
        (2 : ℤ) ≃+
      AddSubgroup.torsionBy (ZMod (2 * n)) (2 : ℤ) :=
  let e :=
    (Rep.toAdditive (M := Multiplicative (ZMod 2)) (G := Multiplicative (ZMod (2 * n)))).trans
      (AddEquiv.additiveMultiplicative (ZMod (2 * n)))
  { toFun := fun x ↦ ⟨e x.1, (Submodule.mem_torsionBy_iff _ _).2 <| by
      have hx : x.1 + x.1 = 0 := by
        simpa only [two_smul] using (Submodule.mem_torsionBy_iff (2 : ℤ) x.1).1 x.2
      rw [two_zsmul, ← map_add, hx, map_zero]⟩
    invFun := fun y ↦ ⟨e.symm y.1, (Submodule.mem_torsionBy_iff _ _).2 <| by
      have hy : y.1 + y.1 = 0 := by
        simpa only [two_zsmul] using (Submodule.mem_torsionBy_iff (2 : ℤ) y.1).1 y.2
      rw [two_smul, ← map_add, hy, map_zero]⟩
    left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.1)
    right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.1)
    map_add' := fun _ _ ↦ Subtype.ext (map_add e _ _) }

private theorem repInvTorsionByTwoEquiv_apply_coe (n : ℕ)
    (x : Submodule.torsionBy ℤ
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
      (2 : ℤ)) :
    (repInvTorsionByTwoEquiv n x : ZMod (2 * n)) =
      AddEquiv.additiveMultiplicative (ZMod (2 * n))
        (Rep.toAdditive (M := Multiplicative (ZMod 2)) (G := Multiplicative (ZMod (2 * n))) x.1) :=
  (rfl)

/-- **Second cohomology of the inversion action on `C_{2n}`.** For every nonzero `n`,
`H²(C₂, C_{2n}^{inv})` is additively isomorphic to `ZMod 2`, obtained by composing the
`2`-torsion identification `Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy` with
`TauCeti.zmodTorsionByEquiv`. -/
noncomputable def cohomologyInvEquivZModTwo (n : ℕ) [NeZero n] :
    groupCohomology
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 ≃+
      ZMod 2 :=
  let A := Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))
  let e₁ :=
    (Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy A
      (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one
      even_orderOf_ofAdd_one_zmod_two
      (TauCeti.GroupExtension.ofMulDistribMulAction_ρ_eq_neg_of_smul_eq_inv
        invMulDistribMulAction_ofAdd_one_smul)
      2 even_two).toAddEquiv
  (e₁.trans (repInvTorsionByTwoEquiv n)).trans (zmodTorsionByEquiv 2 n).symm

/-- `H²(C₂, C_{2n}^{inv})` has order `2` for every nonzero `n`. -/
theorem card_cohomologyInv (n : ℕ) [NeZero n] :
    Nat.card (groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2) =
      2 := by
  rw [Nat.card_congr (cohomologyInvEquivZModTwo n).toEquiv, Nat.card_zmod]

/-- **Evaluation of `cohomologyInvEquivZModTwo` on an extension class.** For any extension `S` of
`C₂` by `C_{2n}` inducing the inversion action, if `e` lifts `ofAdd 1` and
`S.inl (ofAdd a) = e ^ 2`, then `cohomologyInvEquivZModTwo n` maps the cohomology class of any
normalized section of `S` to the unique `x : ZMod 2` satisfying `x.val * n = a` in
`ZMod (2 * n)`. -/
theorem cohomologyInvEquivZModTwo_cohomologyClass_factorSet_iff {n : ℕ} [NeZero n]
    {E : Type*} [Group E]
    {S : GroupExtension (Multiplicative (ZMod (2 * n))) E (Multiplicative (ZMod 2))}
    (σ : S.Section) (hσ : σ 1 = 1) (hact : TauCeti.GroupExtension.InducesAction S)
    {e : E} (he : S.rightHom e = Multiplicative.ofAdd 1) {a : ZMod (2 * n)}
    (ha : S.inl (Multiplicative.ofAdd a) = e ^ 2) (x : ZMod 2) :
    cohomologyInvEquivZModTwo n (TauCeti.GroupExtension.factorSet σ hσ hact).cohomologyClass = x ↔
      (x.val * n : ℕ) = a := by
  have ha' : S.inl (Multiplicative.ofAdd a) = e ^ orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one, ha]
  rw [cohomologyInvEquivZModTwo, AddEquiv.trans_apply, zmodTorsionByEquiv_symm_apply_eq_iff,
    AddEquiv.trans_apply, repInvTorsionByTwoEquiv_apply_coe, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply,
    TauCeti.GroupExtension.groupCohomologyEvenEquivTorsionBy_cohomologyClass_factorSet σ hσ hact
      Multiplicative.mem_zpowers_ofAdd_one even_orderOf_ofAdd_one_zmod_two
      invMulDistribMulAction_ofAdd_one_smul he ha',
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul, toAdd_ofAdd]

end CohomologyInv

/-! ### Same kernel, same quotient, and same action for `DihedralGroup (2 * n)` and
`QuaternionGroup n` -/

section RelabelledExtensions

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The dihedral coordinate equivalences intertwine the quotient conjugation action on
`dihedralRotations n` with `TauCeti.invMulDistribMulAction`. -/
theorem dihedralRotationsMulEquiv_symm_smul (n : ℕ)
    (q : DihedralGroup n ⧸ dihedralRotations n) (m : Multiplicative (ZMod n)) :
    (dihedralRotationsMulEquiv n).symm (dihedralQuotientEquiv n q • m) =
      q • (dihedralRotationsMulEquiv n).symm m := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  cases g with
  | r i =>
    have h1 : (DihedralGroup.r i : DihedralGroup n ⧸ dihedralRotations n) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (r_mem_dihedralRotations i)
    rw [h1, map_one, one_smul, one_smul]
  | sr i =>
    rw [dihedralQuotientEquiv_mk, dihedralReflectionParity_sr,
      invMulDistribMulAction_ofAdd_one_smul, map_inv, Subgroup.quotientConjugationAction_mk_smul,
      conjNormal_eq_inv_of_notMem_dihedralRotations (sr_notMem_dihedralRotations i)]

/-- The quaternion coordinate equivalences intertwine the quotient conjugation action on
`quaternionRotations n` with `TauCeti.invMulDistribMulAction`. -/
theorem quaternionRotationsMulEquiv_symm_smul (n : ℕ)
    (q : QuaternionGroup n ⧸ quaternionRotations n) (m : Multiplicative (ZMod (2 * n))) :
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n q • m) =
      q • (quaternionRotationsMulEquiv n).symm m := by
  refine QuotientGroup.induction_on q fun g ↦ ?_
  cases g with
  | a i =>
    have h1 : (QuaternionGroup.a i : QuaternionGroup n ⧸ quaternionRotations n) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (a_mem_quaternionRotations i)
    rw [h1, map_one, one_smul, one_smul]
  | xa i =>
    rw [quaternionQuotientEquiv_mk, quaternionCosetParity_xa,
      invMulDistribMulAction_ofAdd_one_smul, map_inv, Subgroup.quotientConjugationAction_mk_smul,
      conjNormal_eq_inv_of_notMem_quaternionRotations (xa_notMem_quaternionRotations i)]

/-- The quotient extension of `DihedralGroup (2 * n)` by its rotation subgroup, relabelled to
kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)`. -/
noncomputable def dihedralExtension (n : ℕ) :
    GroupExtension (Multiplicative (ZMod (2 * n))) (DihedralGroup (2 * n))
      (Multiplicative (ZMod 2)) :=
  (dihedralRotations (2 * n)).quotientExtension.relabel
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))

/-- The inclusion of `dihedralExtension n` sends `ofAdd i` to the rotation `r i`. -/
@[simp]
theorem dihedralExtension_inl (n : ℕ) (m : Multiplicative (ZMod (2 * n))) :
    (dihedralExtension n).inl m = DihedralGroup.r (Multiplicative.toAdd m) := by
  simp [dihedralExtension]

/-- The projection of `dihedralExtension n` is the reflection parity. -/
@[simp]
theorem dihedralExtension_rightHom (n : ℕ) (g : DihedralGroup (2 * n)) :
    (dihedralExtension n).rightHom g = dihedralReflectionParity (2 * n) g := by
  simp [dihedralExtension]

/-- The relabelled dihedral extension induces the inversion action of `C₂` on `C_{2n}`. -/
theorem dihedralExtension_inducesAction (n : ℕ) :
    TauCeti.GroupExtension.InducesAction (dihedralExtension n) :=
  (dihedralRotations (2 * n)).quotientExtension_inducesAction.relabel
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))
    (dihedralRotationsMulEquiv_symm_smul (2 * n))

/-- The quotient extension of `QuaternionGroup n` by its rotation subgroup, relabelled to
kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)`. -/
noncomputable def quaternionExtension (n : ℕ) :
    GroupExtension (Multiplicative (ZMod (2 * n))) (QuaternionGroup n)
      (Multiplicative (ZMod 2)) :=
  (quaternionRotations n).quotientExtension.relabel
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)

/-- The inclusion of `quaternionExtension n` sends `ofAdd i` to `a i`. -/
@[simp]
theorem quaternionExtension_inl (n : ℕ) (m : Multiplicative (ZMod (2 * n))) :
    (quaternionExtension n).inl m = QuaternionGroup.a (Multiplicative.toAdd m) := by
  simp [quaternionExtension]

/-- The projection of `quaternionExtension n` is the coset parity. -/
@[simp]
theorem quaternionExtension_rightHom (n : ℕ) (g : QuaternionGroup n) :
    (quaternionExtension n).rightHom g = quaternionCosetParity n g := by
  simp [quaternionExtension]

/-- The relabelled quaternion extension induces the inversion action of `C₂` on `C_{2n}`. -/
theorem quaternionExtension_inducesAction (n : ℕ) :
    TauCeti.GroupExtension.InducesAction (quaternionExtension n) :=
  (quaternionRotations n).quotientExtension_inducesAction.relabel
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)
    (quaternionRotationsMulEquiv_symm_smul n)

end RelabelledExtensions

/-! ### Separating `DihedralGroup (2 * n)` and `QuaternionGroup n` inside `H²(C₂, C_{2n}^{inv})` -/

section Separation

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The cohomology class of `1 → C_{2n} → DihedralGroup (2 * n) → C₂ → 1` inside
`H²(C₂, C_{2n}^{inv})`. -/
noncomputable def dihedralExtensionClass (n : ℕ) :
    groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 :=
  (TauCeti.GroupExtension.factorSet
    ((dihedralExtension n).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := DihedralGroup.sr 0) (by simp))
    ((dihedralExtension n).cyclicPowerSection_one _ _ _)
    (dihedralExtension_inducesAction n)).cohomologyClass

/-- The cohomology class of `1 → C_{2n} → QuaternionGroup n → C₂ → 1` inside
`H²(C₂, C_{2n}^{inv})`. -/
noncomputable def quaternionExtensionClass (n : ℕ) :
    groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 :=
  (TauCeti.GroupExtension.factorSet
    ((quaternionExtension n).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := QuaternionGroup.xa 0) (by simp))
    ((quaternionExtension n).cyclicPowerSection_one _ _ _)
    (quaternionExtension_inducesAction n)).cohomologyClass

/-- Relabelling sends the cohomology class of any normalized section of the dihedral quotient
extension to `dihedralExtensionClass n`. -/
theorem relabelCohomologyIso_dihedral_cohomologyClass (n : ℕ)
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.relabelCohomologyIso (dihedralRotationsMulEquiv (2 * n)).symm
        (dihedralQuotientEquiv (2 * n)) (dihedralRotationsMulEquiv_symm_smul (2 * n)) 2).hom
      (TauCeti.GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass =
      dihedralExtensionClass n :=
  TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet
    (dihedralRotationsMulEquiv (2 * n)).symm (dihedralQuotientEquiv (2 * n))
    (dihedralRotationsMulEquiv_symm_smul (2 * n)) σ hσ
    (dihedralRotations (2 * n)).quotientExtension_inducesAction _ _

/-- Relabelling sends the cohomology class of any normalized section of the quaternion quotient
extension to `quaternionExtensionClass n`. -/
theorem relabelCohomologyIso_quaternion_cohomologyClass (n : ℕ)
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.relabelCohomologyIso (quaternionRotationsMulEquiv n).symm
        (quaternionQuotientEquiv n) (quaternionRotationsMulEquiv_symm_smul n) 2).hom
      (TauCeti.GroupExtension.factorSet σ hσ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass =
      quaternionExtensionClass n :=
  TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet
    (quaternionRotationsMulEquiv n).symm (quaternionQuotientEquiv n)
    (quaternionRotationsMulEquiv_symm_smul n) σ hσ
    (quaternionRotations n).quotientExtension_inducesAction _ _

/-- The dihedral extension class maps to `0 : ZMod 2` under `cohomologyInvEquivZModTwo n`,
because the reflection lift `sr 0` satisfies `(sr 0) ^ 2 = 1`. -/
@[simp]
theorem cohomologyInvEquivZModTwo_dihedralExtensionClass (n : ℕ) [NeZero n] :
    cohomologyInvEquivZModTwo n (dihedralExtensionClass n) = 0 := by
  refine (cohomologyInvEquivZModTwo_cohomologyClass_factorSet_iff _ _ _ (e := DihedralGroup.sr 0)
    (by simp) (a := (0 : ZMod (2 * n))) ?_ 0).2 (by simp)
  simp [sq]

/-- The dihedral extension class vanishes in `H²(C₂, C_{2n}^{inv})`. -/
theorem dihedralExtensionClass_eq_zero (n : ℕ) : dihedralExtensionClass n = 0 := by
  have hsq : (dihedralExtension n).inl 1 = (DihedralGroup.sr (0 : ZMod (2 * n))) ^
      orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one, map_one, sq, DihedralGroup.sr_mul_sr,
      sub_self, DihedralGroup.r_zero]
  exact (TauCeti.GroupExtension.cohomologyClass_factorSet_eq_zero_iff_eq_one_of_smul_eq_inv _ _ _
    Multiplicative.mem_zpowers_ofAdd_one even_orderOf_ofAdd_one_zmod_two
    invMulDistribMulAction_ofAdd_one_smul (e := DihedralGroup.sr 0) (by simp) hsq).2 rfl

/-- The quaternion extension class maps to `1 : ZMod 2` under `cohomologyInvEquivZModTwo n`,
because the lift `xa 0` satisfies `(xa 0) ^ 2 = a n`. -/
@[simp]
theorem cohomologyInvEquivZModTwo_quaternionExtensionClass (n : ℕ) [NeZero n] :
    cohomologyInvEquivZModTwo n (quaternionExtensionClass n) = 1 := by
  refine (cohomologyInvEquivZModTwo_cohomologyClass_factorSet_iff _ _ _ (e := QuaternionGroup.xa 0)
    (by simp) (a := (n : ZMod (2 * n))) ?_ 1).2 (by rw [ZMod.val_one, one_mul])
  simp [sq, QuaternionGroup.xa_mul_xa]

/-- The quaternion extension class is nonzero in `H²(C₂, C_{2n}^{inv})`. -/
theorem quaternionExtensionClass_ne_zero (n : ℕ) [NeZero n] :
    quaternionExtensionClass n ≠ 0 := fun h ↦ by
  have h1 := congrArg (cohomologyInvEquivZModTwo n) h
  rw [cohomologyInvEquivZModTwo_quaternionExtensionClass, map_zero] at h1
  exact one_ne_zero h1

/-- **Same-action separation of dihedral and quaternion extensions.** Inside the single group
`H²(C₂, C_{2n}^{inv})`, the classes of `DihedralGroup (2 * n)` and `QuaternionGroup n` are
distinct. -/
theorem dihedralExtensionClass_ne_quaternionExtensionClass (n : ℕ) [NeZero n] :
    dihedralExtensionClass n ≠ quaternionExtensionClass n := by
  rw [dihedralExtensionClass_eq_zero]
  exact (quaternionExtensionClass_ne_zero n).symm

/-- **The dihedral and quaternion classes exhaust `H²(C₂, C_{2n}^{inv})`.** Every cohomology class
in `H²(C₂, C_{2n}^{inv}) ≅ ℤ/2` is either the dihedral class `0` or the quaternion class `1`. -/
theorem eq_dihedralExtensionClass_or_eq_quaternionExtensionClass (n : ℕ) [NeZero n]
    (c : groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2) :
    c = dihedralExtensionClass n ∨ c = quaternionExtensionClass n := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (cohomologyInvEquivZModTwo n c) with h | h
  · left
    exact (cohomologyInvEquivZModTwo n).injective (by simp [h])
  · right
    exact (cohomologyInvEquivZModTwo n).injective (by simp [h])

/-- The relabelled dihedral and quaternion extensions over `C₂` by `C_{2n}` are inequivalent,
even though they induce the same inversion action. -/
theorem isEmpty_equiv_dihedralExtension_quaternionExtension (n : ℕ) [NeZero n] :
    IsEmpty ((dihedralExtension n).Equiv (quaternionExtension n)) := by
  refine ⟨fun e ↦ dihedralExtensionClass_ne_quaternionExtensionClass n ?_⟩
  exact (TauCeti.GroupExtension.nonempty_equiv_iff_cohomologyClass_factorSet_eq _ _ _ _
    (dihedralExtension_inducesAction n) (quaternionExtension_inducesAction n)).1 ⟨e⟩

/-- Every normalized section of the dihedral quotient extension has vanishing cohomology class in
`H²(D_{4n} ⧸ C_{2n}, C_{2n})`. -/
theorem cohomologyClass_quotientExtension_dihedral_eq_zero (n : ℕ)
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
      (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((dihedralRotations (2 * n)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).1
    ⟨_, isComplement'_dihedralRotations_zpowers_sr 0⟩

/-- Every normalized section of the quaternion quotient extension has nonzero cohomology class in
`H²(Q_{4n} ⧸ C_{2n}, C_{2n})`. -/
theorem cohomologyClass_quotientExtension_quaternion_ne_zero (n : ℕ) [NeZero n]
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
      (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass ≠ 0 := by
  intro h0
  apply quaternionExtensionClass_ne_zero n
  rw [← relabelCohomologyIso_quaternion_cohomologyClass n σ hσ, h0, map_zero]

/-- The rotation subgroup of `DihedralGroup (2 * n)` has a complement (for instance, the
subgroup generated by the reflection `sr 0`). -/
theorem exists_isComplement'_dihedralRotations (n : ℕ) :
    ∃ D : Subgroup (DihedralGroup (2 * n)), (dihedralRotations (2 * n)).IsComplement' D :=
  ⟨_, isComplement'_dihedralRotations_zpowers_sr 0⟩

/-- **The rotation subgroup of `QuaternionGroup n` (`n ≠ 0`) has no complement.** Deduced from
the nonvanishing of its cohomology class via the cohomological comparison
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero`. -/
theorem not_exists_isComplement'_quaternionRotations (n : ℕ) [NeZero n] :
    ¬ ∃ D : Subgroup (QuaternionGroup n), (quaternionRotations n).IsComplement' D := by
  classical
  let σ : (quaternionRotations n).quotientExtension.Section :=
    { toFun := fun q ↦ if q = 1 then 1 else QuaternionGroup.xa 0
      rightInverse_rightHom := fun q ↦ by
        refine QuotientGroup.induction_on q fun g ↦ ?_
        cases g with
        | a i =>
          have h1 : (QuaternionGroup.a i : QuaternionGroup n ⧸ quaternionRotations n) = 1 :=
            (QuotientGroup.eq_one_iff _).2 (a_mem_quaternionRotations i)
          simp [h1]
        | xa i =>
          have hne : (QuaternionGroup.xa i : QuaternionGroup n ⧸ quaternionRotations n) ≠ 1 := by
            rw [ne_eq, QuotientGroup.eq_one_iff]
            exact xa_notMem_quaternionRotations i
          simp only [hne, ↓reduceIte, Subgroup.quotientExtension_rightHom, QuotientGroup.mk'_apply]
          exact (quaternionQuotientEquiv n).injective (by simp) }
  have hσ : σ 1 = 1 := by simp [σ]
  rw [(quaternionRotations n).exists_complement_iff_cohomologyClass_eq_zero σ hσ]
  exact cohomologyClass_quotientExtension_quaternion_ne_zero n σ hσ

end Separation

/-! ### The order-`8` case (`D₈` and `Q₈` over `C₄`) and coprime contrast (`C₃` on `V₄`) -/

section OrderEightAndContrast

/-- In `D₈ = DihedralGroup 4`, the order `4` of the rotation subgroup `C₄` and its index `2` are
not coprime. -/
theorem not_coprime_card_index_dihedralFour :
    ¬ Nat.Coprime (Nat.card (dihedralRotations 4)) (dihedralRotations 4).index := by
  rw [card_dihedralRotations, index_dihedralRotations]
  decide

/-- In `Q₈ = QuaternionGroup 2`, the order `4` of the rotation subgroup `C₄` and its index `2` are
not coprime. -/
theorem not_coprime_card_index_quaternionTwo :
    ¬ Nat.Coprime (Nat.card (quaternionRotations 2)) (quaternionRotations 2).index := by
  rw [card_quaternionRotations, index_quaternionRotations]
  decide

/-- The orders `|C₃| = 3` and `|V₄| = 4` are coprime for every Klein four-group `V`. -/
theorem coprime_card_zmodThree_kleinFour (V : Type*) [CommGroup V] [IsKleinFour V] :
    Nat.Coprime (Nat.card (Multiplicative (ZMod 3))) (Nat.card V) := by
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod, IsKleinFour.card_four]
  decide

/-- **Action insensitivity in the coprime regime.** For every Klein four-group `V` and *every*
action of `C₃ = Multiplicative (ZMod 3)` on `V` (trivial or nontrivial), every positive-degree
cohomology group `H^{k+1}(C₃, V)` vanishes. -/
theorem subsingleton_groupCohomology_zmodThree_kleinFour (V : Type) [CommGroup V] [IsKleinFour V]
    [MulDistribMulAction (Multiplicative (ZMod 3)) V] (k : ℕ) :
    Subsingleton
      (groupCohomology (Rep.ofMulDistribMulAction (Multiplicative (ZMod 3)) V) (k + 1)) := by
  refine groupCohomology.subsingleton_of_bijective_nsmul _ ?_ k
  have hcard : Nat.card (Rep.ofMulDistribMulAction (Multiplicative (ZMod 3)) V) = Nat.card V :=
    Nat.card_congr
      ((Rep.toAdditive (M := Multiplicative (ZMod 3)) (G := V)).toEquiv.trans Additive.toMul)
  exact Nat.Coprime.nsmul_right_bijective (hcard ▸ (coprime_card_zmodThree_kleinFour V).symm)

/-- In particular, `H²(C₃, V) = 0` for every Klein four-group `V` and every action of `C₃` on `V`,
so `H²` cannot distinguish between the trivial action and a nontrivial action in the coprime case
`gcd(3, 4) = 1`. -/
theorem groupCohomology_two_eq_zero_of_zmodThree_kleinFour (V : Type) [CommGroup V] [IsKleinFour V]
    [MulDistribMulAction (Multiplicative (ZMod 3)) V]
    (c : groupCohomology (Rep.ofMulDistribMulAction (Multiplicative (ZMod 3)) V) 2) :
    c = 0 := by
  have := subsingleton_groupCohomology_zmodThree_kleinFour V 1
  exact Subsingleton.elim c 0

end OrderEightAndContrast

end TauCeti.Examples.DihedralQuaternion
