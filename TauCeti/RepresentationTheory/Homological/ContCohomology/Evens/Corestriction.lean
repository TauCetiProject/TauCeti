/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

import Mathlib.GroupTheory.IndexNormal

/-!
# The degree-one corestriction formula for the index-two Evens construction

Let `U` be an open subgroup of index two in a topological group `G`, choose `s ∉ U`, and let
`α : U →* Multiplicative (ZMod 2)` be continuous.  The degree-one corestriction of the class of
`α` is represented by the sum `b₁ + b_s` of the two Shapiro components used in the graph
cochain.  The individual components need not be cocycles, whereas their sum always is, so the
formula is an equality between the corestriction class and the class of that sum.

Everything here lives in the explicit inhomogeneous model: corestriction is `explicitCor1` and
both sides of the formula are classes in `H1`.  The formula holds for an arbitrary representative
`s ∉ U`, which enters the right-hand side through the Shapiro component `b_s`.

## Main definitions

* `TauCeti.ContCohomology.evensCorCocycle`: the sum `b₁ + b_s`, as a continuous `1`-cocycle.

## Main results

* `TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient`: the degree-one corestriction
  `explicitCor1` of the class of `α` is the class of `evensCorCocycle`, the cocycle whose
  underlying cochain is the Shapiro sum `evensCorCochain`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

section Corestriction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete.
The name is given explicitly: the sibling `Evens` files carry the same local instance
anonymously, and this file and `Evens.Restriction` would otherwise be auto-assigned the
same name. -/
local instance continuousSMul_trivialF2 : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

omit [IsTopologicalGroup G] in
private theorem cochainsCor1_evensHomCocycleAmbient (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    cochainsCor1 G (trivialF2 G).V U.toSubgroup (U.toSubgroup.indexTwoTransversal s)
        (Subgroup.indexTwoTransversal_mk hU hs)
        (evensHomCocycleAmbient U.toSubgroup α hα : U.toSubgroup → (trivialF2 G).V) =
      fun γ => (trivialF2Equiv G).symm (evensCorCochain U.toSubgroup s α γ) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let _ : Fintype (G ⧸ U.toSubgroup) := U.toSubgroup.fintypeQuotientOfFiniteIndex
  funext γ
  rw [cochainsCor1_apply, sum_quotient_eq_add_of_index_two hU hs]
  simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, coe_evensHomCocycleAmbient]
  apply (trivialF2Equiv G).injective
  simp only [map_add, AddEquiv.apply_symm_apply, evensCorCochain_apply]
  by_cases hγ : γ ∈ U
  · have hγ' : γ ∈ U.toSubgroup := hγ
    simp_rw [lWord_indexTwoTransversal_mk_one_of_mem s hγ',
      lWord_indexTwoTransversal_mk_of_mem hU hs hγ']
    rw [evensB1_of_mem hγ, evensBs_apply]
    have hsγ : s⁻¹ * γ ∉ U := by
      intro h
      have hi := (Subgroup.mul_mem_iff_of_index_two hU).1 h
      exact (mt U.inv_mem_iff.1 hs) (hi.mpr hγ)
    have hconj : s⁻¹ * γ * s ∈ U.toSubgroup :=
      by simpa only [inv_inv] using
        (Subgroup.normal_of_index_eq_two hU).conj_mem γ hγ s⁻¹
    rw [evensExtend_of_mem hγ, evensB1_of_notMem hsγ, evensExtend_of_mem hconj]
  · have hγ' : γ ∉ U.toSubgroup := hγ
    simp_rw [lWord_indexTwoTransversal_mk_one_of_notMem hU hs hγ',
      lWord_indexTwoTransversal_mk_of_notMem hU hs hγ']
    rw [evensB1_of_notMem hγ, evensBs_apply]
    have hsγ : s⁻¹ * γ ∈ U :=
      (Subgroup.mul_mem_iff_of_index_two hU).2
        (iff_of_false (mt U.inv_mem_iff.1 hs) hγ)
    have hγs : γ * s ∈ U :=
      (Subgroup.mul_mem_iff_of_index_two hU).2 (iff_of_false hγ hs)
    rw [evensB1_of_mem hsγ]
    rw [evensExtend_of_mem hγs, evensExtend_of_mem hsγ]

/-- The sum `b₁ + b_s` as a continuous `1`-cocycle with coefficients in `trivialF2 G`. -/
noncomputable def evensCorCocycle (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) : Z1 G (trivialF2 G).V :=
  ⟨fun γ => (trivialF2Equiv G).symm (evensCorCochain U.toSubgroup s α γ),
    mem_Z1_iff.2 ⟨
      (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
        (continuous_evensCorCochain U.toSubgroup s α U.isOpen' hα),
      fun γ η => by
        apply (trivialF2Equiv G).injective
        simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, map_add,
          AddEquiv.apply_symm_apply]
        exact (evensCorCochain_mul hU hs γ η).trans (add_comm _ _)⟩⟩

/-- The underlying cochain of `evensCorCocycle` is the lifted sum `b₁ + b_s`. -/
@[simp]
theorem coe_evensCorCocycle (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) :
    (evensCorCocycle U s α hU hs hα : G → (trivialF2 G).V) =
      fun γ => (trivialF2Equiv G).symm (evensCorCochain U.toSubgroup s α γ) :=
  (rfl)

/-- At index two, degree-one corestriction is represented by the sum `b₁ + b_s` of the two
Shapiro components.  Neither summand need be a cocycle on its own, whereas their sum always
is; the equation is between the corestriction class and the class of that sum, in the explicit
inhomogeneous model `H1` that carries the corestriction `explicitCor1`.  This is the model
computation behind the Evens-norm corestriction identity, not a statement about canonical
`continuousCohomology` classes. -/
theorem explicitCor1_evensHomCocycleAmbient (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (s : G) (hs : s ∉ U) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    explicitCor1 G (trivialF2 G).V U.toSubgroup U.isOpen'
        (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V) =
      (evensCorCocycle U s α hU hs hα : H1 G (trivialF2 G).V) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  rw [explicitCor1_eq_transversal G (trivialF2 G).V U.toSubgroup
    (U.toSubgroup.indexTwoTransversal s) (Subgroup.indexTwoTransversal_mk hU hs) U.isOpen']
  rw [explicitCor1Transversal_mk]
  apply congrArg (fun z : Z1 G (trivialF2 G).V => (z : H1 G (trivialF2 G).V))
  apply Subtype.ext
  rw [coe_cocyclesCor1, cochainsCor1_evensHomCocycleAmbient U s α hU hs hα]
  exact (coe_evensCorCocycle U s α hU hs hα).symm

end Corestriction

end TauCeti.ContCohomology
