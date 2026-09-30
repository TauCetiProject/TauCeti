/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class

/-!
# Nontriviality of an index-two Evens graph class

For a topological group, a character of an index-two open subgroup that detects a central
involution has a nonzero Evens graph class. The proof compares the graph cocycle at the pair of
identities and at the pair of involutions. A two-coboundary has the same value at both pairs, while
the graph cocycle has values zero and one.

The graph formula is due to L. Evens, *A generalization of the transfer map in the cohomology of
groups*, Trans. Amer. Math. Soc. **108** (1963), 54–65.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance continuousSMul_trivialF2_nontrivial : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- If an index-two subgroup contains a central involution on which a character is nontrivial,
its choice-free Evens graph class is nonzero. -/
theorem explicitGraphClass_ne_zero_of_involution (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) (v : U.toSubgroup) (hv : (v : G) * v = 1)
    (hcentral : ∀ s : G, s⁻¹ * (v : G) * s = v)
    (hαv : Multiplicative.toAdd (α v) = 1) :
    explicitGraphClass U hU α hα ≠ 0 := by
  intro hzero
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  have hzero' : (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) = 0 := by
    rw [← explicitGraphClass_eq_evensGraphCocycle U hU s hs α hα]
    exact hzero
  obtain ⟨b, -, hb⟩ := mem_B2_iff'.1 (H2pi_eq_zero_iff.1 hzero')
  have hb11 := hb 1 1
  have hbvv := hb (v : G) (v : G)
  have hconj : s⁻¹ * (v : G) * s = v := hcentral s
  have hf11 : evensGraphCochain U.toSubgroup s α (1, 1) = 0 := by
    rw [evensGraphCochain_apply_of_mem_of_mem hs (one_mem U.toSubgroup)
      (one_mem U.toSubgroup)]
    simp only [mul_one, evensExtend_of_mem (one_mem U.toSubgroup)]
    have hαone' : α (⟨1, one_mem U.toSubgroup⟩ : U.toSubgroup) = 1 := map_one α
    rw [hαone', toAdd_one, zero_mul]
  have hb11' : b 1 = 0 := by
    simpa only [coe_evensGraphCocycle, hf11, map_zero, one_smul, one_mul, sub_self,
      zero_add] using hb11
  have hbvv' : b (v : G) - b 1 + b (v : G) = (trivialF2Equiv G).symm 1 := by
    simpa [coe_evensGraphCocycle, evensGraphCochain_apply_of_mem_of_mem hs v.2 v.2,
      hconj, evensExtend_of_mem v.2, hαv, hv, TopRep.distribMulAction_smul,
      trivialF2_ρ_apply_apply] using hbvv
  have htwo : ∀ x : (trivialF2 G).V, x + x = 0 := by
    intro x
    apply (trivialF2Equiv G).injective
    simpa only [map_add, map_zero] using
      (CharTwo.add_self_eq_zero (trivialF2Equiv G x))
  rw [hb11', sub_zero, htwo] at hbvv'
  have hfalse := congrArg (trivialF2Equiv G) hbvv'
  norm_num at hfalse

end TauCeti.ContCohomology
