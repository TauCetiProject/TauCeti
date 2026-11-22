/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Cohomology
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Dihedral and generalized quaternion extensions with the same inversion action

For every positive integer `n`, the dihedral group `DihedralGroup (2 * n)` and the generalized
quaternion group `QuaternionGroup n` both sit in a short exact sequence
`1 → C_{2n} → E → C₂ → 1` whose quotient `C₂` acts on the cyclic rotation subgroup `C_{2n}` by
inversion (`TauCeti.invMulDistribMulAction`). Transporting both quotient extensions to the common
kernel `Multiplicative (ZMod (2 * n))` and quotient `Multiplicative (ZMod 2)` via
`TauCeti.dihedralExtension`, `TauCeti.quaternionExtension`, and
`TauCeti.groupCohomology.relabelCohomologyIso` compares their classes
`TauCeti.dihedralEvenExtensionClass n` and `TauCeti.quaternionExtensionClass n` inside the single
cohomology group `H²(C₂, C_{2n}^{inv}) ≅ ℤ/2`.

* **Cohomology of the inversion action.** By
  `Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo`, `H²(C₂, C_{2n}^{inv}) ≃+ ZMod 2`,
  sending `TauCeti.dihedralEvenExtensionClass n` to `0` and `TauCeti.quaternionExtensionClass n` to
  `1`.
* **Separation in `H²(C₂, C_{2n}^{inv})`.** The two classes are distinct, exhaust
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

## Main results

* `dihedralEvenExtensionClass_ne_quaternionExtensionClass`: the dihedral and quaternion classes
  are distinct inside `H²(C₂, C_{2n}^{inv})`.
* `eq_dihedralEvenExtensionClass_or_eq_quaternionExtensionClass`: the dihedral and quaternion
  classes exhaust `H²(C₂, C_{2n}^{inv})`.
* `isEmpty_equiv_dihedralEvenExtension_quaternionExtension`: the relabelled dihedral and
  quaternion extensions are not equivalent.
* `subsingleton_groupCohomology_zmodThree_kleinFour`: `H^{k+1}(C₃, V) = 0` for every Klein
  four-group `V` and every `C₃`-action.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter IV, §3.
-/

public section

namespace TauCeti.Examples.DihedralQuaternion

open _root_.groupCohomology
open scoped IsMulCommutative IsKleinFour

/-! ### Separating `DihedralGroup (2 * n)` and `QuaternionGroup n` inside `H²(C₂, C_{2n}^{inv})` -/

section Separation

attribute [local instance] Subgroup.quotientConjugationAction invMulDistribMulAction

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
  rcases h2 (Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n c) with h | h
  · left
    exact (Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n).injective (by simp [h])
  · right
    exact (Rep.FiniteCyclicGroup.groupCohomologyTwoInvEquivZModTwo n).injective (by simp [h])

/-- The relabelled dihedral and quaternion extensions over `C₂` by `C_{2n}` are inequivalent,
even though they induce the same inversion action. -/
theorem isEmpty_equiv_dihedralEvenExtension_quaternionExtension (n : ℕ) [NeZero n] :
    IsEmpty ((dihedralExtension (2 * n)).Equiv (quaternionExtension n)) := by
  refine ⟨fun e ↦ dihedralEvenExtensionClass_ne_quaternionExtensionClass n ?_⟩
  let σ := TauCeti.GroupExtension.normalizeSection (dihedralExtension (2 * n)).surjInvRightHom
  let σ' := TauCeti.GroupExtension.normalizeSection (quaternionExtension n).surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  have hσ' : σ' 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  rw [← cohomologyClass_factorSet_dihedralExtension n σ hσ,
    ← cohomologyClass_factorSet_quaternionExtension n σ' hσ']
  exact (TauCeti.GroupExtension.nonempty_equiv_iff_cohomologyClass_factorSet_eq σ σ' hσ hσ'
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
