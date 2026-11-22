/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Inversion
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicAutomorphism
import TauCeti.Data.ZMod.Torsion

/-!
# The dihedral and quaternion extensions of `C₂` by `C₂ₙ`

The dihedral group `D₄ₙ = DihedralGroup (2 * n)` and the generalized quaternion group
`Q₄ₙ = QuaternionGroup n` both contain a cyclic subgroup of order `2 * n` and index two, their
rotations, and in both every element outside it inverts it. So the two quotient extensions
`C₂ₙ → D₄ₙ → C₂` and `C₂ₙ → Q₄ₙ → C₂` have the same kernel, the same quotient and the same
action, and their classes lie in one group: `H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by
negation. This file identifies both cohomology groups with that one
(`TauCeti.Examples.DihedralQuaternion.dihedralGroupCohomologyIso`,
`TauCeti.Examples.DihedralQuaternion.quaternionGroupCohomologyIso`) and shows that the two
classes are its two elements.

For the action by negation, `H²(C₂, T)` is the `2`-torsion of `T`
(`TauCeti.groupCohomologyEvenNegEquivTorsionBy`): the fixed points of `x ↦ -x` modulo the image of
the norm `x + (-x) = 0`. For `T = ZMod d` with `d ≠ 0` it therefore has `gcd 2 d` elements
(`TauCeti.Examples.DihedralQuaternion.natCard_groupCohomology_two_neg_zmod`), two of them for
`d = 2 * n`. The dihedral class is zero, since the reflections form a complement; the quaternion
class is not, since `Q₄ₙ` has a single involution, which is a rotation. So every class is one of
the two (`TauCeti.Examples.DihedralQuaternion.eq_dihedral_or_eq_quaternion`), and they differ
(`TauCeti.Examples.DihedralQuaternion.dihedral_ne_quaternion`).

At `n = 2` this is the comparison of `D₈` and `Q₈` over their cyclic subgroup of order four. Here
`|N| = 4` and `[G : N] = 2` are not coprime, so the comparison is not forced by orders, and both
extensions induce the same action, so the criterion
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero` separates them through the class and
not through the action.

## Main definitions

* `TauCeti.Examples.DihedralQuaternion.dihedralGroupCohomologyIso`,
  `TauCeti.Examples.DihedralQuaternion.quaternionGroupCohomologyIso`: the cohomology of the
  quotient modules of `DihedralGroup m` and `Q₄ₙ`, identified with that of `C₂` acting on
  `ZMod m` and on `ZMod (2 * n)` by negation.

## Main results

* `TauCeti.Examples.DihedralQuaternion.natCard_groupCohomology_two_neg_zmod`: for `d ≠ 0`,
  `H²(C₂, ZMod d)` with the action by negation has `gcd 2 d` elements.
* `TauCeti.Examples.DihedralQuaternion.dihedralGroupCohomologyIso_hom_cohomologyClass`,
  `TauCeti.Examples.DihedralQuaternion.quaternionGroupCohomologyIso_hom_cohomologyClass_ne_zero`:
  the dihedral class is zero and the quaternion class is not.
* `TauCeti.Examples.DihedralQuaternion.eq_dihedral_or_eq_quaternion`,
  `TauCeti.Examples.DihedralQuaternion.dihedral_ne_quaternion`: the two classes are the two
  elements of `H²(C₂, ZMod (2 * n))`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §1 (the cohomology of a cyclic group) and Chapter IV, §3 (extensions with abelian
  kernel are classified by `H²`).
-/

public section

open CategoryTheory

open scoped IsMulCommutative

namespace TauCeti.Examples.DihedralQuaternion

attribute [local instance] Subgroup.quotientConjugationAction

/-- For `d ≠ 0`, the second cohomology of `C₂` acting on `ZMod d` by negation has `gcd 2 d`
elements: it is the `2`-torsion of `ZMod d`. -/
theorem natCard_groupCohomology_two_neg_zmod (d : ℕ) [NeZero d] :
    Nat.card (groupCohomology ((AddEquiv.neg (ZMod d)).cyclicRep (AddEquiv.iterate_neg_two _)) 2) =
      Nat.gcd 2 d := by
  rw [Nat.card_congr (groupCohomologyEvenNegEquivTorsionBy (ZMod d) 2 even_two).toEquiv]
  -- `AddSubgroup.torsionBy` is the additive subgroup underlying `Submodule.torsionBy ℤ`.
  simpa using ZMod.card_torsionBy 2 d

/-- In `H²(C₂, ZMod (2 * n))` for the action by negation, with `n ≠ 0`, any two nonzero classes
are equal. -/
theorem eq_of_ne_zero_of_ne_zero {n : ℕ} [NeZero n]
    {x y : groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep
      (AddEquiv.iterate_neg_two _)) 2} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  have hcard := (natCard_groupCohomology_two_neg_zmod (2 * n)).trans (Nat.gcd_mul_right_right n 2)
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' 0).1 hcard
  exact (hz x hx).trans (hz y hy).symm

/-- The cohomology of the quotient module of `DihedralGroup m` on its rotations, identified with
the cohomology of `C₂` acting on `ZMod m` by negation through `DihedralGroup m ⧸ C_m ≃* C₂` and
the rotation coordinate `C_m ≃* ZMod m`. -/
noncomputable def dihedralGroupCohomologyIso (m k : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (DihedralGroup m ⧸ dihedralRotations m)
        (dihedralRotations m)) k ≅
      groupCohomology ((AddEquiv.neg (ZMod m)).cyclicRep (AddEquiv.iterate_neg_two _)) k :=
  Subgroup.quotientGroupCohomologyIsoNeg (index_dihedralRotations m)
    (sr_notMem_dihedralRotations 0)
    (fun _ hx ↦ conj_eq_inv_of_notMem_dihedralRotations (sr_notMem_dihedralRotations 0) hx)
    (dihedralRotationsMulEquiv m) k

/-- The cohomology of the quotient module of `Q₄ₙ = QuaternionGroup n` on its rotations,
identified with the cohomology of `C₂` acting on `ZMod (2 * n)` by negation through
`Q₄ₙ ⧸ C₂ₙ ≃* C₂` and the rotation coordinate `C₂ₙ ≃* ZMod (2 * n)`. -/
noncomputable def quaternionGroupCohomologyIso (n k : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (QuaternionGroup n ⧸ quaternionRotations n)
        (quaternionRotations n)) k ≅
      groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep (AddEquiv.iterate_neg_two _)) k :=
  Subgroup.quotientGroupCohomologyIsoNeg (index_quaternionRotations n)
    (xa_notMem_quaternionRotations 0)
    (fun _ hx ↦ conj_eq_inv_of_notMem_quaternionRotations (xa_notMem_quaternionRotations 0) hx)
    (quaternionRotationsMulEquiv n) k

/-- The class of the dihedral extension `C_m → DihedralGroup m → C₂` is zero in
`H²(C₂, ZMod m)`. -/
theorem dihedralGroupCohomologyIso_hom_cohomologyClass (m : ℕ)
    (σ : (dihedralRotations m).quotientExtension.Section) (hσ : σ 1 = 1) :
    (dihedralGroupCohomologyIso m 2).hom (GroupExtension.factorSet σ hσ
      (dihedralRotations m).quotientExtension_inducesAction).cohomologyClass = 0 := by
  rw [cohomologyClass_dihedralRotations_eq_zero, map_zero]

/-- For `n ≠ 0`, the class of the quaternion extension `C₂ₙ → Q₄ₙ → C₂` is nonzero in
`H²(C₂, ZMod (2 * n))`. -/
theorem quaternionGroupCohomologyIso_hom_cohomologyClass_ne_zero (n : ℕ) [NeZero n]
    (σ : (quaternionRotations n).quotientExtension.Section) (hσ : σ 1 = 1) :
    (quaternionGroupCohomologyIso n 2).hom (GroupExtension.factorSet σ hσ
      (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass ≠ 0 :=
  (map_ne_zero_iff _ (quaternionGroupCohomologyIso n 2).toLinearEquiv.injective).2
    (cohomologyClass_quaternionRotations_ne_zero n σ hσ)

/-- **The two extensions of `C₂` by `C₂ₙ` with the inversion action.** For `n ≠ 0`, every class in
`H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by negation, is the class of the dihedral
extension `C₂ₙ → D₄ₙ → C₂` or that of the quaternion extension `C₂ₙ → Q₄ₙ → C₂`. -/
theorem eq_dihedral_or_eq_quaternion (n : ℕ) [NeZero n]
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (quaternionRotations n).quotientExtension.Section) (hτ : τ 1 = 1)
    (x : groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep
      (AddEquiv.iterate_neg_two _)) 2) :
    x = (dihedralGroupCohomologyIso (2 * n) 2).hom (GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass ∨
      x = (quaternionGroupCohomologyIso n 2).hom (GroupExtension.factorSet τ hτ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass := by
  rw [dihedralGroupCohomologyIso_hom_cohomologyClass]
  exact (eq_or_ne x 0).imp_right fun hx ↦
    eq_of_ne_zero_of_ne_zero hx (quaternionGroupCohomologyIso_hom_cohomologyClass_ne_zero n τ hτ)

/-- For `n ≠ 0`, the classes of the dihedral and quaternion extensions of `C₂` by `C₂ₙ` differ
in `H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by negation. -/
theorem dihedral_ne_quaternion (n : ℕ) [NeZero n]
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (quaternionRotations n).quotientExtension.Section) (hτ : τ 1 = 1) :
    (dihedralGroupCohomologyIso (2 * n) 2).hom (GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass ≠
      (quaternionGroupCohomologyIso n 2).hom (GroupExtension.factorSet τ hτ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass := by
  rw [dihedralGroupCohomologyIso_hom_cohomologyClass]
  exact (quaternionGroupCohomologyIso_hom_cohomologyClass_ne_zero n τ hτ).symm

end TauCeti.Examples.DihedralQuaternion
