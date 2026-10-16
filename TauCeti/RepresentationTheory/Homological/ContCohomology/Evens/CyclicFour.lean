/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
public import TauCeti.GroupTheory.GroupExtension.ZModFour
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Nontrivial

/-!
# The Evens graph class for the cyclic group of order four

For the subgroup of even elements of `Multiplicative (ZMod 4)`, the nontrivial character has a
nonzero graph class. This checks the index-two Evens class on a finite cyclic group whose subgroup
of order two contains an involution detected by the character. The explicit class is nonzero by
`explicitGraphClass_ne_zero_of_involution`; the comparison carries the result to Mathlib's
canonical continuous cohomology.

The same graph cocycle, read multiplicatively, is a factor set on `C₄` with values in `C₂`.
Its twisted-product extension has a canonical lift of the generator whose fourth power is the
nontrivial kernel element. Hence the lift has order eight and identifies the extension with `C₈`.
This is the `C₈` normalization anchor for the index-two Evens norm.

## Main declarations

* `cyclicFourGraphFactorSet`: the graph cocycle as a multiplicative factor set.
* `cyclicFourGraphLift_pow_four`: its canonical lift has nontrivial fourth power.
* `cyclicEightEquivCyclicFourGraphExtension`: the resulting extension is `C₈`.

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

/-! ### The classified extension -/

attribute [local instance] trivialMulDistribMulAction

/-- The standard generator of the cyclic group of order four. -/
private def cyclicFourGenerator : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1

private theorem cyclicFourGenerator_not_mem :
    cyclicFourGenerator ∉ cyclicFourEvenSubgroup := by
  rw [cyclicFourEvenSubgroup]
  change TauCeti.zmodFourExtension.rightHom cyclicFourGenerator ≠ 1
  rw [TauCeti.zmodFourExtension_rightHom]
  decide

private theorem cyclicFourGenerator_sq_mem :
    cyclicFourGenerator * cyclicFourGenerator ∈ cyclicFourEvenSubgroup := by
  rw [cyclicFourEvenSubgroup]
  change TauCeti.zmodFourExtension.rightHom
    (cyclicFourGenerator * cyclicFourGenerator) = 1
  rw [TauCeti.zmodFourExtension_rightHom]
  decide

private theorem cyclicFourEvenCharacter_generator_sq :
    Multiplicative.toAdd (cyclicFourEvenCharacter
      ⟨cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator_sq_mem⟩) = 1 := by
  have hx : (⟨cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator_sq_mem⟩ :
      cyclicFourEvenSubgroup.toSubgroup) ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    change Multiplicative.ofAdd (1 + 1 : ZMod 4) = Multiplicative.ofAdd 0 at this
    exact of_decide_eq_false rfl this
  have hα : cyclicFourEvenCharacter
      ⟨cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator_sq_mem⟩ ≠ 1 := by
    simpa [cyclicFourEvenCharacter] using hx
  generalize cyclicFourEvenCharacter
    ⟨cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator_sq_mem⟩ = z at hα ⊢
  revert z
  decide

/-- The factor set on `C₄` obtained from the Evens graph cocycle of the nontrivial character of
its index-two subgroup, using the standard generator as the element outside the subgroup. -/
noncomputable def cyclicFourGraphFactorSet :
    FactorSet (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) where
  toFun p := Multiplicative.ofAdd
    (evensGraphCochain cyclicFourEvenSubgroup.toSubgroup cyclicFourGenerator
      cyclicFourEvenCharacter p)
  isMulCocycle₂' g h j := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, trivialMulDistribMulAction_smul]
    exact evensGraphCochain_cocycle_identity cyclicFourEvenSubgroup_index
      cyclicFourGenerator_not_mem g h j
  map_one_one' := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, evensGraphCochain_of_mem (Subgroup.one_mem _),
      evensB1_of_mem (Subgroup.one_mem _), evensExtend_of_mem (Subgroup.one_mem _)]
    have hα1 : cyclicFourEvenCharacter ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
    rw [hα1, toAdd_one, zero_mul]

/-- The central extension of `C₄` by `C₂` classified by its Evens graph cocycle. -/
abbrev CyclicFourGraphExtension := cyclicFourGraphFactorSet.Extension

/-- The canonical lift of the standard generator of `C₄` to its Evens graph extension. -/
noncomputable def cyclicFourGraphLift : CyclicFourGraphExtension :=
  cyclicFourGraphFactorSet.canonicalSection cyclicFourGenerator

@[simp] private theorem cyclicFourGraphFactorSet_generator_generator :
    cyclicFourGraphFactorSet (cyclicFourGenerator, cyclicFourGenerator) =
    Multiplicative.ofAdd 1 := by
  apply Multiplicative.toAdd.injective
  change evensGraphCochain cyclicFourEvenSubgroup.toSubgroup cyclicFourGenerator
    cyclicFourEvenCharacter (cyclicFourGenerator, cyclicFourGenerator) = 1
  rw [evensGraphCochain_of_notMem cyclicFourGenerator_not_mem,
    evensB1_of_notMem cyclicFourGenerator_not_mem,
    evensExtend_of_mem cyclicFourGenerator_sq_mem,
    cyclicFourEvenCharacter_generator_sq,
    evensBs_apply]
  have hsinv : cyclicFourGenerator⁻¹ * cyclicFourGenerator = 1 := by decide
  rw [hsinv, evensB1_of_mem (Subgroup.one_mem _), evensExtend_of_mem (Subgroup.one_mem _)]
  have hα1 : cyclicFourEvenCharacter ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
  rw [hα1, toAdd_one]
  simp

private theorem cyclicFourGenerator_cube_not_mem :
    cyclicFourGenerator ^ 3 ∉ cyclicFourEvenSubgroup := by
  rw [cyclicFourEvenSubgroup]
  change TauCeti.zmodFourExtension.rightHom (cyclicFourGenerator ^ 3) ≠ 1
  rw [TauCeti.zmodFourExtension_rightHom]
  decide

private theorem cyclicFourGenerator_sq_mul_generator :
    (cyclicFourGenerator * cyclicFourGenerator) * cyclicFourGenerator =
      cyclicFourGenerator ^ 3 := by
  rw [pow_succ, pow_two]

@[simp] private theorem cyclicFourGraphFactorSet_generator_sq_generator :
    cyclicFourGraphFactorSet
      (cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator) = 1 := by
  apply Multiplicative.toAdd.injective
  change evensGraphCochain cyclicFourEvenSubgroup.toSubgroup cyclicFourGenerator
    cyclicFourEvenCharacter
      (cyclicFourGenerator * cyclicFourGenerator, cyclicFourGenerator) = 0
  rw [evensGraphCochain_of_mem cyclicFourGenerator_sq_mem,
    evensBs_apply]
  have hcancel : cyclicFourGenerator⁻¹ * cyclicFourGenerator = 1 := by group
  rw [hcancel, evensB1_of_mem (Subgroup.one_mem _),
    evensExtend_of_mem (Subgroup.one_mem _)]
  have hα1 : cyclicFourEvenCharacter ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
  rw [hα1, toAdd_one, mul_zero]

@[simp] private theorem cyclicFourGraphFactorSet_generator_cube_generator :
    cyclicFourGraphFactorSet (cyclicFourGenerator ^ 3, cyclicFourGenerator) = 1 := by
  apply Multiplicative.toAdd.injective
  change evensGraphCochain cyclicFourEvenSubgroup.toSubgroup cyclicFourGenerator
    cyclicFourEvenCharacter (cyclicFourGenerator ^ 3, cyclicFourGenerator) = 0
  rw [evensGraphCochain_of_notMem cyclicFourGenerator_cube_not_mem,
    evensB1_of_notMem cyclicFourGenerator_cube_not_mem]
  have hfour : cyclicFourGenerator ^ 3 * cyclicFourGenerator = 1 := by decide
  rw [hfour, evensExtend_of_mem (Subgroup.one_mem _)]
  have hα1 : cyclicFourEvenCharacter ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
  rw [hα1, toAdd_one, zero_mul, zero_add, evensBs_apply]
  have hcancel : cyclicFourGenerator⁻¹ * cyclicFourGenerator = 1 := by group
  rw [hcancel, evensB1_of_mem (Subgroup.one_mem _),
    evensExtend_of_mem (Subgroup.one_mem _), hα1, toAdd_one, mul_zero]

private theorem cyclicFourGraphLift_pow_two :
    cyclicFourGraphLift ^ 2 =
      ⟨Multiplicative.ofAdd 1, cyclicFourGenerator * cyclicFourGenerator⟩ := by
  ext <;> simp [cyclicFourGraphLift, pow_two]

private theorem cyclicFourGraphLift_pow_three :
    cyclicFourGraphLift ^ 3 =
      ⟨Multiplicative.ofAdd 1, cyclicFourGenerator ^ 3⟩ := by
  rw [show cyclicFourGraphLift ^ 3 = cyclicFourGraphLift ^ 2 * cyclicFourGraphLift by group,
    cyclicFourGraphLift_pow_two]
  ext <;> simp [cyclicFourGraphLift, cyclicFourGenerator_sq_mul_generator]

/-- **The fourth power of the canonical lift is the nontrivial kernel element.** -/
theorem cyclicFourGraphLift_pow_four :
    cyclicFourGraphLift ^ 4 = FactorSet.inl cyclicFourGraphFactorSet (Multiplicative.ofAdd 1) := by
  rw [show cyclicFourGraphLift ^ 4 = cyclicFourGraphLift ^ 3 * cyclicFourGraphLift by group,
    cyclicFourGraphLift_pow_three]
  apply FactorSet.Extension.ext
  · simp [cyclicFourGraphLift]
  · simp only [FactorSet.Extension.mul_right, cyclicFourGraphLift,
      FactorSet.canonicalSection_apply, FactorSet.inl_right]
    decide

private theorem cyclicFourGraphLift_pow_four_ne_one : cyclicFourGraphLift ^ 4 ≠ 1 := by
  rw [cyclicFourGraphLift_pow_four]
  intro h
  have hleft := congrArg FactorSet.Extension.left h
  simp only [FactorSet.inl_left, FactorSet.Extension.one_left] at hleft
  exact of_decide_eq_false rfl hleft

private theorem cyclicFourGraphLift_pow_eight : cyclicFourGraphLift ^ 8 = 1 := by
  rw [show cyclicFourGraphLift ^ 8 = (cyclicFourGraphLift ^ 4) ^ 2 by group,
    cyclicFourGraphLift_pow_four, ← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  rw [h, map_one]

/-- **The canonical lift of the generator of `C₄` has order eight.** The graph cocycle is
nonzero precisely in the first multiplication step, so the fourth power is the nontrivial kernel
element and the eighth power is one. -/
theorem orderOf_cyclicFourGraphLift : orderOf cyclicFourGraphLift = 8 := by
  simpa using orderOf_eq_prime_pow (p := 2) (n := 2)
    cyclicFourGraphLift_pow_four_ne_one cyclicFourGraphLift_pow_eight

private theorem natCard_cyclicFourGraphExtension : Nat.card CyclicFourGraphExtension = 8 := by
  rw [Nat.card_congr (FactorSet.Extension.equivProd cyclicFourGraphFactorSet)]
  simp

private theorem cyclicFourGraphLift_mem_zpowers (x : CyclicFourGraphExtension) :
    x ∈ Subgroup.zpowers cyclicFourGraphLift := by
  have htop : Subgroup.zpowers cyclicFourGraphLift = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, orderOf_cyclicFourGraphLift,
        natCard_cyclicFourGraphExtension])
  rw [htop]
  exact Subgroup.mem_top x

/-- **The extension classified by the `C₄` Evens graph cocycle is `C₈`.** This equivalence
sends the standard generator of `C₈` to the canonical lift of the standard generator of `C₄`.
Together with `cyclicFourGraphLift_pow_four`, it fixes the normalization of the graph cocycle. -/
noncomputable def cyclicEightEquivCyclicFourGraphExtension :
    Multiplicative (ZMod 8) ≃* CyclicFourGraphExtension :=
  zmodMulEquivOfGenerator cyclicFourGraphLift_mem_zpowers
    natCard_cyclicFourGraphExtension

/-- The `C₈` identification sends its standard generator to the canonical lift in the graph
extension. -/
@[simp]
theorem cyclicEightEquivCyclicFourGraphExtension_generator :
    cyclicEightEquivCyclicFourGraphExtension (Multiplicative.ofAdd 1) =
      cyclicFourGraphLift :=
  zmodMulEquivOfGenerator_apply_ofAdd_one _ _

end TauCeti.ContCohomology
