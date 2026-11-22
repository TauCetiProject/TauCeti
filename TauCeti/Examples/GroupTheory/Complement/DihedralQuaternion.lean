/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.GroupTheory.GroupExtension.Relabel
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Extension
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Extension
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.Data.ZMod.OrderOf
import TauCeti.Data.ZMod.Torsion
import TauCeti.GroupTheory.GroupExtension.Cyclic.Cohomology
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Cohomology
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Dihedral and generalized quaternion extensions with the same inversion action

For every positive integer `n`, the dihedral group `DihedralGroup (2 * n)` and the generalized
quaternion group `QuaternionGroup n` both sit in a short exact sequence
`1 → C_{2n} → E → C₂ → 1` whose quotient `C₂` acts on the cyclic rotation subgroup `C_{2n}` by
inversion (`TauCeti.invMulDistribMulAction`). This file transports both quotient extensions to
the common kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)` via
`TauCeti.dihedralExtension`, `TauCeti.quaternionExtension`, and
`TauCeti.GroupExtension.relabelCohomologyIso`, and separates them inside the single cohomology group
`H²(C₂, C_{2n}^{inv}) ≅ ℤ/2`.

* **Cohomology of the inversion action.** By `groupCohomologyTwoInvEquivZModTwo`,
  `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2`, sending the extension class of a lift `e` of the generator with
  `S.inl (ofAdd a) = e ^ 2` to the unique residue `x : ZMod 2` with `x.val * n = a` in
  `ZMod (2 * n)`
  (`groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff`).
* **Separation in `H²(C₂, C_{2n}^{inv})`.** Under `groupCohomologyTwoInvEquivZModTwo n`, the
  dihedral extension class maps to `0` (`(sr 0) ^ 2 = 1`) and the quaternion extension class maps
  to `1` (`(xa 0) ^ 2 = a n`). Thus the two classes are distinct, exhaust
  `H²(C₂, C_{2n}^{inv})`, witness that the two extensions are inequivalent, and separate splitting
  from non-splitting: `TauCeti.isComplement'_dihedralRotations_zpowers_sr 0` exhibits a complement
  in `DihedralGroup (2 * n)` (with vanishing quotient cohomology class
  `TauCeti.cohomologyClass_dihedralRotations_eq_zero`), whereas `quaternionRotations n` has no
  complement (`TauCeti.not_exists_isComplement'_quaternionRotations`, with nonzero quotient
  cohomology class `TauCeti.cohomologyClass_quaternionRotations_ne_zero`).
* **The order-`8` case (`n = 2`) and coprime contrast.** At `n = 2`, `D₈` and `Q₈` are extensions
  of `C₂` by `C₄` with `|C₄| = 4` and `[E : C₄] = 2` not coprime
  (`not_coprime_card_index_dihedralFour`, `not_coprime_card_index_quaternionTwo`), and every
  involution of `QuaternionGroup n` (`n ≠ 0`) lies inside the rotation subgroup
  (`TauCeti.sq_eq_one_quaternionGroup_iff`). By contrast, for any Klein four-group `V` and every
  action of `C₃` on `V`, coprimality `gcd(3, 4) = 1` forces `H^{k+1}(C₃, V) = 0`
  (`subsingleton_groupCohomology_zmodThree_kleinFour`).

## Main definitions

* `TauCeti.Examples.DihedralQuaternion.groupCohomologyTwoInvEquivZModTwo`:
  `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2` for `n ≠ 0`.
* `TauCeti.Examples.DihedralQuaternion.dihedralEvenExtensionClass`,
  `TauCeti.Examples.DihedralQuaternion.quaternionExtensionClass`: the dihedral and quaternion
  cohomology classes inside the common group `H²(C₂, C_{2n}^{inv})`.

## Main results

* `TauCeti.Examples.DihedralQuaternion.natCard_groupCohomologyTwoInv`:
  `|H²(C₂, C_{2n}^{inv})| = 2`.
* `TauCeti.Examples.DihedralQuaternion.groupCohomologyTwoInvEquivZModTwo_dihedralEvenExtensionClass`
  and
  `TauCeti.Examples.DihedralQuaternion.groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass`:
  the two classes map to `0` and `1` in `ZMod 2`.
* `TauCeti.Examples.DihedralQuaternion.eq_dihedralEvenExtensionClass_or_eq_quaternionExtensionClass`
  shows that the dihedral and quaternion classes exhaust `H²(C₂, C_{2n}^{inv})`.
* `TauCeti.Examples.DihedralQuaternion.isEmpty_equiv_dihedralEvenExtension_quaternionExtension`:
  the relabelled dihedral and quaternion extensions are not equivalent.
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

/-! ### Explicit identification `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2` -/

section CohomologyTwoInv

open CategoryTheory
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
    (Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
      (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one
      ((TauCeti.orderOf_ofAdd_one_zmod 2).symm ▸ even_two)
      (Rep.ofMulDistribMulAction_ρ_eq_neg_of_smul_eq_inv invMulDistribMulAction_ofAdd_one_smul)
      2 even_two).toAddEquiv
  let e₁₂ :=
    TauCeti.submoduleTorsionByEquivAddSubgroup
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
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n))))
        (Multiplicative.ofAdd (1 : ZMod 2)) Multiplicative.mem_zpowers_ofAdd_one 2 even_two y) =
      x ↔
      ((x.val * n : ℕ) : ZMod (2 * n)) =
        Multiplicative.toAdd (Additive.toMul (Rep.toAdditive y.val)) := by
  rw [groupCohomologyTwoInvEquivZModTwo]
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
  rw [Rep.FiniteCyclicGroup.groupCohomologyEvenEquivTorsionBy_groupCohomologyπEven,
    zmodTorsionByEquiv_symm_apply_eq_iff, AddEquiv.torsionByCongr_apply_coe,
    TauCeti.submoduleTorsionByEquivAddSubgroup_apply_coe, AddEquiv.trans_apply,
    AddEquiv.additiveMultiplicative_apply]

/-- **Evaluation of `groupCohomologyTwoInvEquivZModTwo` on an extension class.** For any extension
`S` of `C₂` by `C_{2n}` inducing the inversion action, if `e` lifts `ofAdd 1` and
`S.inl (ofAdd a) = e ^ 2`, then `groupCohomologyTwoInvEquivZModTwo n` maps the cohomology class
of any normalized section of `S` to the unique `x : ZMod 2` satisfying `x.val * n = a` in
`ZMod (2 * n)`. -/
theorem groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff
    {n : ℕ} [NeZero n] {E : Type*} [Group E]
    {S : GroupExtension (Multiplicative (ZMod (2 * n))) E (Multiplicative (ZMod 2))}
    (σ : S.Section) (hσ : σ 1 = 1)
    (hact : TauCeti.GroupExtension.InducesAction S)
    {e : E} (he : S.rightHom e = Multiplicative.ofAdd 1) {a : ZMod (2 * n)}
    (ha : S.inl (Multiplicative.ofAdd a) = e ^ 2) (x : ZMod 2) :
    groupCohomologyTwoInvEquivZModTwo n
        (TauCeti.GroupExtension.factorSet σ hσ hact).cohomologyClass = x ↔
      (x.val * n : ℕ) = a := by
  have ha' : S.inl (Multiplicative.ofAdd a) =
      e ^ orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [TauCeti.orderOf_ofAdd_one_zmod, ha]
  rw [σ.cohomologyClass_factorSet_eq_groupCohomologyπEven hσ hact
      Multiplicative.mem_zpowers_ofAdd_one he ha',
    groupCohomologyTwoInvEquivZModTwo_groupCohomologyπEven]
  simp

end CohomologyTwoInv

/-! ### Separating `DihedralGroup (2 * n)` and `QuaternionGroup n` inside `H²(C₂, C_{2n}^{inv})` -/

section Separation

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

/-- The cohomology class of `1 → C_{2n} → DihedralGroup (2 * n) → C₂ → 1` inside
`H²(C₂, C_{2n}^{inv})`. -/
noncomputable def dihedralEvenExtensionClass (n : ℕ) :
    groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2 :=
  (TauCeti.GroupExtension.factorSet
    ((dihedralExtension (2 * n)).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := DihedralGroup.sr 0) (by simp))
    ((dihedralExtension (2 * n)).cyclicPowerSection_one _ _ _)
    (dihedralExtension_inducesAction (2 * n))).cohomologyClass

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

/-- Relabelling sends the cohomology class of any normalized section of `S₀` to the cohomology
class of any normalized section of an extension `S` equal to `S₀.relabel eM eG`. -/
private theorem relabelCohomologyIso_cohomologyClass_of_eq
    {M G M' G' : Type} [CommGroup M] [Group G] [MulDistribMulAction G M]
    [CommGroup M'] [Group G'] [MulDistribMulAction G' M'] {E : Type*} [Group E]
    {S₀ : _root_.GroupExtension M E G} {S : _root_.GroupExtension M' E G'}
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m)
    (hS : S = S₀.relabel eM eG)
    (σ : S₀.Section) (hσ : σ 1 = 1) (hact₀ : TauCeti.GroupExtension.InducesAction S₀)
    (σ' : S.Section) (hσ' : σ' 1 = 1) (hact : TauCeti.GroupExtension.InducesAction S) :
    (TauCeti.GroupExtension.relabelCohomologyIso eM eG hsmul 2).hom
        (TauCeti.GroupExtension.factorSet σ hσ hact₀).cohomologyClass =
      (TauCeti.GroupExtension.factorSet σ' hσ' hact).cohomologyClass := by
  subst hS
  exact TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet
    eM eG hsmul σ hσ hact₀ σ' hσ'

/-- Relabelling sends the cohomology class of any normalized section of the dihedral quotient
extension to `dihedralEvenExtensionClass n`. -/
theorem relabelCohomologyIso_dihedral_cohomologyClass (n : ℕ)
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.relabelCohomologyIso (dihedralRotationsMulEquiv (2 * n)).symm
        (dihedralQuotientEquiv (2 * n)) (dihedralRotationsMulEquiv_symm_smul (2 * n)) 2).hom
      (TauCeti.GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass =
      dihedralEvenExtensionClass n := by
  rw [dihedralEvenExtensionClass]
  exact relabelCohomologyIso_cohomologyClass_of_eq (dihedralRotationsMulEquiv (2 * n)).symm
    (dihedralQuotientEquiv (2 * n)) (dihedralRotationsMulEquiv_symm_smul (2 * n))
    (dihedralExtension_def (2 * n)) σ hσ
    (dihedralRotations (2 * n)).quotientExtension_inducesAction _ _
    (dihedralExtension_inducesAction (2 * n))

/-- Relabelling sends the cohomology class of any normalized section of the quaternion quotient
extension to `quaternionExtensionClass n`. -/
theorem relabelCohomologyIso_quaternion_cohomologyClass (n : ℕ)
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.relabelCohomologyIso (quaternionRotationsMulEquiv n).symm
        (quaternionQuotientEquiv n) (quaternionRotationsMulEquiv_symm_smul n) 2).hom
      (TauCeti.GroupExtension.factorSet σ hσ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass =
      quaternionExtensionClass n := by
  rw [quaternionExtensionClass]
  exact relabelCohomologyIso_cohomologyClass_of_eq (quaternionRotationsMulEquiv n).symm
    (quaternionQuotientEquiv n) (quaternionRotationsMulEquiv_symm_smul n)
    (quaternionExtension_def n) σ hσ
    (quaternionRotations n).quotientExtension_inducesAction _ _
    (quaternionExtension_inducesAction n)

/-- The dihedral extension class maps to `0 : ZMod 2` under
`groupCohomologyTwoInvEquivZModTwo n`, because the reflection lift `sr 0` satisfies
`(sr 0) ^ 2 = 1`. -/
@[simp]
theorem groupCohomologyTwoInvEquivZModTwo_dihedralEvenExtensionClass (n : ℕ) [NeZero n] :
    groupCohomologyTwoInvEquivZModTwo n (dihedralEvenExtensionClass n) = 0 := by
  rw [dihedralEvenExtensionClass]
  refine (groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff
    ((dihedralExtension (2 * n)).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := DihedralGroup.sr 0) (by simp))
    ((dihedralExtension (2 * n)).cyclicPowerSection_one _ _ _)
    (dihedralExtension_inducesAction (2 * n)) (e := DihedralGroup.sr 0) (by simp)
    (a := (0 : ZMod (2 * n))) ?_ 0).2 (by simp)
  simp [sq]

/-- The dihedral extension class vanishes in `H²(C₂, C_{2n}^{inv})`. -/
theorem dihedralEvenExtensionClass_eq_zero (n : ℕ) : dihedralEvenExtensionClass n = 0 := by
  have hsq : (dihedralExtension (2 * n)).inl 1 = (DihedralGroup.sr (0 : ZMod (2 * n))) ^
      orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [TauCeti.orderOf_ofAdd_one_zmod, map_one, sq, DihedralGroup.sr_mul_sr,
      sub_self, DihedralGroup.r_zero]
  exact (GroupExtension.Section.cohomologyClass_factorSet_eq_zero_iff_eq_one_of_smul_eq_inv
    ((dihedralExtension (2 * n)).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := DihedralGroup.sr 0) (by simp))
    ((dihedralExtension (2 * n)).cyclicPowerSection_one _ _ _)
    (dihedralExtension_inducesAction (2 * n)) Multiplicative.mem_zpowers_ofAdd_one
    ((TauCeti.orderOf_ofAdd_one_zmod 2).symm ▸ even_two)
    invMulDistribMulAction_ofAdd_one_smul (e := DihedralGroup.sr 0) (by simp) hsq).2 rfl

/-- The quaternion extension class maps to `1 : ZMod 2` under
`groupCohomologyTwoInvEquivZModTwo n`, because the lift `xa 0` satisfies `(xa 0) ^ 2 = a n`. -/
@[simp]
theorem groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass (n : ℕ) [NeZero n] :
    groupCohomologyTwoInvEquivZModTwo n (quaternionExtensionClass n) = 1 := by
  rw [quaternionExtensionClass]
  refine (groupCohomologyTwoInvEquivZModTwo_cohomologyClass_factorSet_iff
    ((quaternionExtension n).cyclicPowerSection (Multiplicative.ofAdd 1)
      Multiplicative.mem_zpowers_ofAdd_one (e := QuaternionGroup.xa 0) (by simp))
    ((quaternionExtension n).cyclicPowerSection_one _ _ _)
    (quaternionExtension_inducesAction n) (e := QuaternionGroup.xa 0) (by simp)
    (a := (n : ZMod (2 * n))) ?_ 1).2 (by rw [ZMod.val_one, one_mul])
  simp [sq, QuaternionGroup.xa_mul_xa]

/-- The quaternion extension class is nonzero in `H²(C₂, C_{2n}^{inv})`. -/
theorem quaternionExtensionClass_ne_zero (n : ℕ) [NeZero n] :
    quaternionExtensionClass n ≠ 0 := fun h ↦ by
  have h1 := congrArg (groupCohomologyTwoInvEquivZModTwo n) h
  rw [groupCohomologyTwoInvEquivZModTwo_quaternionExtensionClass, map_zero] at h1
  exact one_ne_zero h1

/-- **Same-action separation of dihedral and quaternion extensions.** Inside the single group
`H²(C₂, C_{2n}^{inv})`, the classes of `DihedralGroup (2 * n)` and `QuaternionGroup n` are
distinct. -/
theorem dihedralEvenExtensionClass_ne_quaternionExtensionClass (n : ℕ) [NeZero n] :
    dihedralEvenExtensionClass n ≠ quaternionExtensionClass n := by
  rw [dihedralEvenExtensionClass_eq_zero]
  exact (quaternionExtensionClass_ne_zero n).symm

/-- **The dihedral and quaternion classes exhaust `H²(C₂, C_{2n}^{inv})`.** Every cohomology class
in `H²(C₂, C_{2n}^{inv}) ≅ ℤ/2` is either the dihedral class `0` or the quaternion class `1`. -/
theorem eq_dihedralEvenExtensionClass_or_eq_quaternionExtensionClass (n : ℕ) [NeZero n]
    (c : groupCohomology
      (Rep.ofMulDistribMulAction (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * n)))) 2) :
    c = dihedralEvenExtensionClass n ∨ c = quaternionExtensionClass n := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (groupCohomologyTwoInvEquivZModTwo n c) with h | h
  · left
    exact (groupCohomologyTwoInvEquivZModTwo n).injective (by simp [h])
  · right
    exact (groupCohomologyTwoInvEquivZModTwo n).injective (by simp [h])

/-- The relabelled dihedral and quaternion extensions over `C₂` by `C_{2n}` are inequivalent,
even though they induce the same inversion action. -/
theorem isEmpty_equiv_dihedralEvenExtension_quaternionExtension (n : ℕ) [NeZero n] :
    IsEmpty ((dihedralExtension (2 * n)).Equiv (quaternionExtension n)) := by
  refine ⟨fun e ↦ dihedralEvenExtensionClass_ne_quaternionExtensionClass n ?_⟩
  exact (TauCeti.GroupExtension.nonempty_equiv_iff_cohomologyClass_factorSet_eq _ _ _ _
    (dihedralExtension_inducesAction (2 * n)) (quaternionExtension_inducesAction n)).1 ⟨e⟩

-- The canonical quotient-extension vanishing/nonvanishing and complement results live in
-- `Dihedral.Cohomology`, `Dihedral.Basic`, `Quaternion.Cohomology`, and `Quaternion.Basic`.
example (n : ℕ)
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
      (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass = 0 :=
  TauCeti.cohomologyClass_dihedralRotations_eq_zero (2 * n) σ hσ

example (n : ℕ) :
    ∃ D : Subgroup (DihedralGroup (2 * n)), (dihedralRotations (2 * n)).IsComplement' D :=
  ⟨_, isComplement'_dihedralRotations_zpowers_sr 0⟩

-- Cohomological proof that `quaternionRotations n` (`n ≠ 0`) has no complement: normalize
-- `surjInvRightHom` and transport its class to `quaternionExtensionClass n ≠ 0`.
example (n : ℕ) [NeZero n] :
    ¬ ∃ D : Subgroup (QuaternionGroup n), (quaternionRotations n).IsComplement' D := by
  let σ := TauCeti.GroupExtension.normalizeSection
    (quaternionRotations n).quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  rw [(quaternionRotations n).exists_complement_iff_cohomologyClass_eq_zero σ hσ]
  intro h0
  apply quaternionExtensionClass_ne_zero n
  rw [← relabelCohomologyIso_quaternion_cohomologyClass n σ hσ, h0, map_zero]

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
  rw [natCard_quaternionRotations, index_quaternionRotations]
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
theorem groupCohomology_two_class_eq_zero_of_zmodThree_kleinFour (V : Type) [CommGroup V]
    [IsKleinFour V] [MulDistribMulAction (Multiplicative (ZMod 3)) V]
    (c : groupCohomology (Rep.ofMulDistribMulAction (Multiplicative (ZMod 3)) V) 2) :
    c = 0 := by
  have := subsingleton_groupCohomology_zmodThree_kleinFour V 1
  exact Subsingleton.elim c 0

end OrderEightAndContrast

end TauCeti.Examples.DihedralQuaternion
