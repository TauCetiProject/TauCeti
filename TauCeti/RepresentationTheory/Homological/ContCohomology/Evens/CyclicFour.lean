/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Nontrivial
public import TauCeti.GroupTheory.GroupExtension.ZModFour

/-!
# The Evens graph class for the cyclic group of order four

For the subgroup of even elements of `Multiplicative (ZMod 4)`, the nontrivial character has a
nonzero graph class. This checks the index-two Evens class on a finite cyclic group whose subgroup
of order two contains an involution detected by the character. The explicit class is nonzero by
`explicitGraphClass_ne_zero_of_involution`; the comparison carries the result to Mathlib's
canonical continuous cohomology.

The graph formula is due to L. Evens, *A generalization of the transfer map in the cohomology of
groups*, Trans. Amer. Math. Soc. **108** (1963), 54–65.
-/

public section

namespace TauCeti.ContCohomology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul (Multiplicative (ZMod 4))
    (trivialF2 (Multiplicative (ZMod 4))).V :=
  (isSmoothDiscrete_trivialF2 (Multiplicative (ZMod 4))).continuousSMul

/-- The open subgroup of even elements of the cyclic group of order four. -/
def cyclicFourEvenSubgroup : OpenSubgroup (Multiplicative (ZMod 4)) :=
  ⟨TauCeti.zmodFourExtension.rightHom.ker, isOpen_discrete _⟩

/-- The even subgroup has index two. -/
theorem cyclicFourEvenSubgroup_index : cyclicFourEvenSubgroup.toSubgroup.index = 2 := by
  rw [cyclicFourEvenSubgroup, Subgroup.index_ker]
  rw [MonoidHom.range_eq_top.mpr TauCeti.zmodFourExtension.rightHom_surjective]
  simp

/-- The doubling map identifies the cyclic group of order two with the even subgroup of the
cyclic group of order four. -/
noncomputable def cyclicTwoEquivCyclicFourEvenSubgroup :
    Multiplicative (ZMod 2) ≃* cyclicFourEvenSubgroup.toSubgroup :=
  (TauCeti.zmodFourExtension.inl.ofInjective TauCeti.zmodFourExtension.inl_injective).trans
    (MulEquiv.subgroupCongr TauCeti.zmodFourExtension.range_inl_eq_ker_rightHom)

/-- The nontrivial character of the even subgroup of the cyclic group of order four. -/
noncomputable def cyclicFourEvenCharacter :
    cyclicFourEvenSubgroup.toSubgroup →* Multiplicative (ZMod 2) :=
  cyclicTwoEquivCyclicFourEvenSubgroup.symm.toMonoidHom

/-- The character of the even subgroup sends the doubled element back to its original value. -/
@[simp] theorem cyclicFourEvenCharacter_cyclicTwoEquivCyclicFourEvenSubgroup
    (x : Multiplicative (ZMod 2)) :
    cyclicFourEvenCharacter (cyclicTwoEquivCyclicFourEvenSubgroup x) = x := by
  simp [cyclicFourEvenCharacter]

private noncomputable def cyclicFourInvolution : cyclicFourEvenSubgroup.toSubgroup :=
  cyclicTwoEquivCyclicFourEvenSubgroup (Multiplicative.ofAdd 1)

private theorem cyclicFourInvolution_mul_self :
    (cyclicFourInvolution : Multiplicative (ZMod 4)) * cyclicFourInvolution = 1 := by
  have h : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  exact congrArg Subtype.val (by
    simpa only [map_mul, map_one, cyclicFourInvolution] using
      congrArg cyclicTwoEquivCyclicFourEvenSubgroup h)

private theorem cyclicFourEvenCharacter_involution :
    Multiplicative.toAdd (cyclicFourEvenCharacter cyclicFourInvolution) = 1 := by
  simp [cyclicFourEvenCharacter, cyclicFourInvolution]

/-- The graph class of the nontrivial character on the even subgroup of the cyclic group of
order four is nonzero in explicit degree-two cohomology. -/
theorem explicitGraphClass_cyclicFour_ne_zero :
    explicitGraphClass cyclicFourEvenSubgroup cyclicFourEvenSubgroup_index
      cyclicFourEvenCharacter (continuous_of_discreteTopology) ≠ 0 :=
  explicitGraphClass_ne_zero_of_involution cyclicFourEvenSubgroup cyclicFourEvenSubgroup_index
    cyclicFourEvenCharacter continuous_of_discreteTopology cyclicFourInvolution
    cyclicFourInvolution_mul_self
    (fun s => by simp [mul_comm s⁻¹ (cyclicFourInvolution : Multiplicative (ZMod 4)), mul_assoc])
    cyclicFourEvenCharacter_involution

/-- The canonical continuous degree-two graph class for the even subgroup of the cyclic group
of order four is nonzero. -/
theorem graphClass_cyclicFour_ne_zero :
    graphClass cyclicFourEvenSubgroup cyclicFourEvenSubgroup_index
      cyclicFourEvenCharacter continuous_of_discreteTopology ≠ 0 :=
  graphClass_ne_zero_of_involution cyclicFourEvenSubgroup cyclicFourEvenSubgroup_index
    cyclicFourEvenCharacter continuous_of_discreteTopology cyclicFourInvolution
    cyclicFourInvolution_mul_self
    (fun s => by simp [mul_comm s⁻¹ (cyclicFourInvolution : Multiplicative (ZMod 4)), mul_assoc])
    cyclicFourEvenCharacter_involution

end TauCeti.ContCohomology
