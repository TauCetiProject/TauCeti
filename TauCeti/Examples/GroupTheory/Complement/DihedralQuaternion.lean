/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Cohomology
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CyclicAutomorphism

/-!
# The dihedral and quaternion extensions of `C₂` by `C₂ₙ`

The dihedral group `D₄ₙ = DihedralGroup (2 * n)` and the generalized quaternion group
`Q₄ₙ = QuaternionGroup n` both contain a cyclic subgroup of order `2 * n` and index two, their
rotations, and in both every element outside it inverts it. So the two quotient extensions
`C₂ₙ → D₄ₙ → C₂` and `C₂ₙ → Q₄ₙ → C₂` have the same kernel, the same quotient and the same
action, and their classes lie in one group: `H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by
negation. Both cohomology groups are identified with that one
(`TauCeti.dihedralRotationsGroupCohomologyIsoNeg`,
`TauCeti.quaternionRotationsGroupCohomologyIsoNeg`), and this file shows that the two classes are
its two elements.

For the action by negation, `H²(C₂, T)` is the `2`-torsion of `T`
(`TauCeti.groupCohomologyEvenNegEquivTorsionBy`): the fixed points of `x ↦ -x` modulo the image of
the norm `x + (-x) = 0`. For `T = ZMod d` with `d ≠ 0` it therefore has `gcd 2 d` elements
(`TauCeti.natCard_groupCohomology_two_neg_zmod`), two of them for `d = 2 * n`. The dihedral class
is zero, since the reflections form a complement
(`TauCeti.dihedralRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_eq_zero`); the quaternion
class is not, since `Q₄ₙ` has a single involution, which is a rotation
(`TauCeti.quaternionRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_ne_zero`). So every class is
one of the two (`TauCeti.Examples.DihedralQuaternion.eq_dihedral_or_eq_quaternion`), and they differ
(`TauCeti.Examples.DihedralQuaternion.dihedral_ne_quaternion`).

At `n = 2` this is the comparison of `D₈` and `Q₈` over their cyclic subgroup of order four. Here
`|N| = 4` and `[G : N] = 2` are not coprime, so the comparison is not forced by orders, and both
extensions induce the same action, so the criterion
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero` separates them through the class and
not through the action.

## Main results

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

/-- In `H²(C₂, ZMod (2 * n))` for the action by negation, with `n ≠ 0`, any two nonzero classes
are equal. -/
theorem eq_of_ne_zero_of_ne_zero {n : ℕ} [NeZero n]
    {x y : groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep
      (AddEquiv.iterate_neg_two _)) 2} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  have hcard := (natCard_groupCohomology_two_neg_zmod (2 * n)).trans (Nat.gcd_mul_right_right n 2)
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' 0).1 hcard
  exact (hz x hx).trans (hz y hy).symm

/-- **The two extensions of `C₂` by `C₂ₙ` with the inversion action.** For `n ≠ 0`, every class in
`H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by negation, is the class of the dihedral
extension `C₂ₙ → D₄ₙ → C₂` or that of the quaternion extension `C₂ₙ → Q₄ₙ → C₂`. -/
theorem eq_dihedral_or_eq_quaternion (n : ℕ) [NeZero n]
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (quaternionRotations n).quotientExtension.Section) (hτ : τ 1 = 1)
    (x : groupCohomology ((AddEquiv.neg (ZMod (2 * n))).cyclicRep
      (AddEquiv.iterate_neg_two _)) 2) :
    x = (dihedralRotationsGroupCohomologyIsoNeg (2 * n) 2).hom (GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass ∨
      x = (quaternionRotationsGroupCohomologyIsoNeg n 2).hom (GroupExtension.factorSet τ hτ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass := by
  rw [dihedralRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_eq_zero]
  exact (eq_or_ne x 0).imp_right fun hx ↦
    eq_of_ne_zero_of_ne_zero hx
      (quaternionRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_ne_zero n τ hτ)

/-- For `n ≠ 0`, the classes of the dihedral and quaternion extensions of `C₂` by `C₂ₙ` differ
in `H²(C₂, ZMod (2 * n))`, the generator of `C₂` acting by negation. -/
theorem dihedral_ne_quaternion (n : ℕ) [NeZero n]
    (σ : (dihedralRotations (2 * n)).quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (quaternionRotations n).quotientExtension.Section) (hτ : τ 1 = 1) :
    (dihedralRotationsGroupCohomologyIsoNeg (2 * n) 2).hom (GroupExtension.factorSet σ hσ
        (dihedralRotations (2 * n)).quotientExtension_inducesAction).cohomologyClass ≠
      (quaternionRotationsGroupCohomologyIsoNeg n 2).hom (GroupExtension.factorSet τ hτ
        (quaternionRotations n).quotientExtension_inducesAction).cohomologyClass := by
  rw [dihedralRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_eq_zero]
  exact (quaternionRotationsGroupCohomologyIsoNeg_hom_cohomologyClass_ne_zero n τ hτ).symm

end TauCeti.Examples.DihedralQuaternion
