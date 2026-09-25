/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class

import Mathlib.GroupTheory.IndexNormal

/-!
# The degree-one corestriction formula for the index-two Evens construction

Let `U` be an open subgroup of index two in a topological group `G`, choose `s ∉ U`, and let
`α : U →* Multiplicative (ZMod 2)` be continuous.  The degree-one corestriction of the class of
`α` is represented by the sum `b₁ + b_s` of the two Shapiro components used in the graph
cochain.  The individual components are not cocycles, so the formula is necessarily an equality
between the corestriction class and the class of their sum.

The proof computes corestriction with the two-element transversal which sends the trivial coset
to `1` and the other coset to `s`.  Independence of the transversal then identifies this formula
with the canonical corestriction in the explicit inhomogeneous model.  The accompanying
`homClass` constructor places continuous homomorphisms in Mathlib's canonical continuous
cohomology when that model is needed.

## Main definitions

* `TauCeti.ContCohomology.evensHomCocycle`: a continuous homomorphism to `ZMod 2`, lifted to a
  continuous `1`-cocycle with coefficients in `trivialF2`.
* `TauCeti.ContCohomology.homClass`: its class in canonical continuous cohomology, the carrier
  in which the canonical-model form of the Layer 13 identities is to be stated.

## Main results

* `TauCeti.ContCohomology.evensNorm_cor_shapiro`: the degree-one corestriction `explicitCor1` of
  the class of `α` is the class of `evensCorCochain`.  The equality is between classes in the
  explicit inhomogeneous model `H1`: neither pinned Mathlib nor Tau Ceti has a corestriction on
  the canonical `continuousCohomology` carrier in any degree, so `explicitCor1` is the only
  corestriction there is to compute with.  Transporting the identity along
  `explicitH1AddEquivContinuousCohomology` is immediate once a canonical-model corestriction and
  its degree-one agreement with `explicitCor1` land.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section HomClass

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul H (trivialF2 H).V :=
  (isSmoothDiscrete_trivialF2 H).continuousSMul

omit [IsTopologicalGroup H] in
private theorem evensHomCochain_mem_Z1 (α : H →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    (fun h => (trivialF2Equiv H).symm (Multiplicative.toAdd (α h))) ∈
      Z1 H (trivialF2 H).V := by
  refine mem_Z1_iff.2 ⟨?_, ?_⟩
  · exact (continuous_of_discreteTopology : Continuous (trivialF2Equiv H).symm).comp
      (continuous_toAdd.comp hα)
  · intro g h
    apply (trivialF2Equiv H).injective
    simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, map_add,
      AddEquiv.apply_symm_apply, map_mul, toAdd_mul]
    exact add_comm _ _

/-- A continuous homomorphism to `Multiplicative (ZMod 2)` as a continuous `1`-cocycle with
coefficients in `trivialF2`. -/
noncomputable def evensHomCocycle (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    Z1 H (trivialF2 H).V :=
  ⟨fun h => (trivialF2Equiv H).symm (Multiplicative.toAdd (α h)),
    evensHomCochain_mem_Z1 α hα⟩

omit [IsTopologicalGroup H] in
/-- The underlying cochain of `evensHomCocycle`. -/
@[simp]
theorem coe_evensHomCocycle (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    (evensHomCocycle α hα : H → (trivialF2 H).V) =
      fun h => (trivialF2Equiv H).symm (Multiplicative.toAdd (α h)) :=
  (rfl)

/-- The canonical continuous-cohomology class of a continuous homomorphism
`H → Multiplicative (ZMod 2)`. -/
noncomputable def homClass (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    continuousCohomology 1 (trivialF2 H) :=
  (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
    (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V (evensHomCocycle α hα))

/-- The class `homClass α` is the image of `evensHomCocycle α` under the degree-one comparison. -/
theorem homClass_def (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass α hα =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
        (explicitH1AddEquivContinuousCohomology H (trivialF2 H).V
          (evensHomCocycle α hα)) :=
  (rfl)

end HomClass

section Corestriction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

open scoped Classical in
private noncomputable def evensTransversal (U : Subgroup G) (s : G) : G ⧸ U → G :=
  fun q => if q = QuotientGroup.mk 1 then 1 else s

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem quotient_eq_one_or_mk_of_index_two (U : Subgroup G) (s : G)
    (hU : U.index = 2) (hs : s ∉ U) (q : G ⧸ U) :
    q = QuotientGroup.mk 1 ∨ q = QuotientGroup.mk s := by
  by_cases hq : q = QuotientGroup.mk 1
  · exact Or.inl hq
  · right
    rw [← Quotient.out_eq' q]
    apply QuotientGroup.eq.2
    have hout : Quotient.out q ∉ U := by
      intro hout
      apply hq
      rw [← Quotient.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using hout)
    exact (Subgroup.mul_mem_iff_of_index_two hU).2
      (iff_of_false (mt U.inv_mem_iff.1 hout) hs)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem evensTransversal_mk (U : Subgroup G) (s : G)
    (hU : U.index = 2) (hs : s ∉ U) (q : G ⧸ U) :
    QuotientGroup.mk (evensTransversal U s q) = q := by
  rcases quotient_eq_one_or_mk_of_index_two U s hU hs q with hq | hq
  · rw [evensTransversal, ite_eq_left hq]
    exact hq.symm
  · have hne : q ≠ QuotientGroup.mk 1 := by
      intro h
      apply hs
      simpa using QuotientGroup.eq.1 (hq.symm.trans h)
    rw [evensTransversal, ite_eq_right hne]
    exact hq.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem quotient_mk_ne_one (U : Subgroup G) {s : G} (hs : s ∉ U) :
    (QuotientGroup.mk s : G ⧸ U) ≠ QuotientGroup.mk 1 := by
  intro h
  exact hs (by simpa using QuotientGroup.eq.1 h)

open scoped Classical in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem lWord_evensTransversal_one (U : Subgroup G) (s : G)
    (hU : U.index = 2) (hs : s ∉ U) (γ : G) :
    lWord U (evensTransversal U s) (QuotientGroup.mk 1) γ =
      if γ ∈ U then γ else γ * s := by
  by_cases hγ : γ ∈ U
  · have hcoset : γ⁻¹ • (QuotientGroup.mk 1 : G ⧸ U) = QuotientGroup.mk 1 := by
      apply QuotientGroup.eq.2
      simpa using hγ
    rw [lWord_def, hcoset]
    simp [evensTransversal, hγ]
  · have hγs : γ * s ∈ U :=
      (Subgroup.mul_mem_iff_of_index_two hU).2 (iff_of_false hγ hs)
    have hcoset : γ⁻¹ • (QuotientGroup.mk 1 : G ⧸ U) = QuotientGroup.mk s := by
      apply QuotientGroup.eq.2
      simpa using hγs
    rw [lWord_def, hcoset]
    simp [evensTransversal, hγ, quotient_mk_ne_one U hs]

open scoped Classical in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem lWord_evensTransversal_mk (U : Subgroup G) (s : G)
    (hU : U.index = 2) (hs : s ∉ U) (γ : G) :
    lWord U (evensTransversal U s) (QuotientGroup.mk s) γ =
      if γ ∈ U then s⁻¹ * γ * s else s⁻¹ * γ := by
  have hs1 := quotient_mk_ne_one U hs
  by_cases hγ : γ ∈ U
  · have hcoset : γ⁻¹ • (QuotientGroup.mk s : G ⧸ U) = QuotientGroup.mk s := by
      apply QuotientGroup.eq.2
      simpa [mul_assoc] using (Subgroup.normal_of_index_eq_two hU).conj_mem γ hγ s⁻¹
    rw [lWord_def, hcoset]
    simp [evensTransversal, hs1, hγ]
  · have hcoset : γ⁻¹ • (QuotientGroup.mk s : G ⧸ U) = QuotientGroup.mk 1 := by
      apply QuotientGroup.eq.2
      have hsInv : s⁻¹ ∉ U := mt U.inv_mem_iff.1 hs
      exact (by simpa using
        (Subgroup.mul_mem_iff_of_index_two hU).2 (iff_of_false hsInv hγ))
    rw [lWord_def, hcoset]
    simp [evensTransversal, hs1, hγ]

/-- A continuous homomorphism on a subgroup, regarded as a `1`-cocycle with the ambient group's
lifted trivial coefficient carrier.  This is the representative to which explicit corestriction
applies. -/
noncomputable def evensHomCocycleAmbient (U : OpenSubgroup G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    Z1 U.toSubgroup (trivialF2 G).V :=
  ⟨fun h => (trivialF2Equiv G).symm (Multiplicative.toAdd (α h)),
    mem_Z1_iff.2 ⟨
      (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
        (continuous_toAdd.comp hα),
      fun g h => by
        let x : (trivialF2 G).V :=
          (trivialF2Equiv G).symm (Multiplicative.toAdd (α h))
        have hx : g • x = x := by
          calc
            g • x = (g : G) • x := rfl
            _ = x := trivialF2_ρ_apply_apply G g x
        rw [hx]
        dsimp only [x]
        apply (trivialF2Equiv G).injective
        simp only [map_add, AddEquiv.apply_symm_apply, map_mul, toAdd_mul]
        exact add_comm (Multiplicative.toAdd (α g)) (Multiplicative.toAdd (α h))⟩⟩

omit [IsTopologicalGroup G] in
/-- The underlying cochain of `evensHomCocycleAmbient`. -/
@[simp]
theorem coe_evensHomCocycleAmbient (U : OpenSubgroup G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    (evensHomCocycleAmbient U α hα : U.toSubgroup → (trivialF2 G).V) =
      fun h => (trivialF2Equiv G).symm (Multiplicative.toAdd (α h)) :=
  (rfl)

omit [IsTopologicalGroup G] in
private theorem cochainsCor1_evensTransversal (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    cochainsCor1 G (trivialF2 G).V U.toSubgroup (evensTransversal U.toSubgroup s)
        (evensTransversal_mk U.toSubgroup s hU hs)
        (evensHomCocycleAmbient U α hα : U.toSubgroup → (trivialF2 G).V) =
      fun γ => (trivialF2Equiv G).symm (evensCorCochain U.toSubgroup s α γ) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let _ : Fintype (G ⧸ U.toSubgroup) := U.toSubgroup.fintypeQuotientOfFiniteIndex
  funext γ
  rw [cochainsCor1_apply]
  have hne := (quotient_mk_ne_one U.toSubgroup hs).symm
  rw [Fintype.sum_eq_add (QuotientGroup.mk 1 : G ⧸ U.toSubgroup)
    (QuotientGroup.mk s) hne (fun q hq => False.elim <|
      (quotient_eq_one_or_mk_of_index_two U.toSubgroup s hU hs q).elim hq.1 hq.2)]
  simp only [evensTransversal, ite_eq_right (quotient_mk_ne_one U.toSubgroup hs),
    TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, coe_evensHomCocycleAmbient]
  apply (trivialF2Equiv G).injective
  simp only [map_add, AddEquiv.apply_symm_apply, evensCorCochain_apply]
  by_cases hγ : γ ∈ U
  · simp_rw [lWord_evensTransversal_one U.toSubgroup s hU hs,
      lWord_evensTransversal_mk U.toSubgroup s hU hs]
    have hγ' : γ ∈ U.toSubgroup := hγ
    simp_rw [ite_eq_left hγ']
    rw [evensB1_of_mem hγ, evensBs_apply]
    have hsγ : s⁻¹ * γ ∉ U := by
      intro h
      have hi := (Subgroup.mul_mem_iff_of_index_two hU).1 h
      exact (mt U.inv_mem_iff.1 hs) (hi.mpr hγ)
    have hconj : s⁻¹ * γ * s ∈ U.toSubgroup :=
      by simpa only [inv_inv] using
        (Subgroup.normal_of_index_eq_two hU).conj_mem γ hγ s⁻¹
    rw [evensExtend_of_mem hγ, evensB1_of_notMem hsγ, evensExtend_of_mem hconj]
  · simp_rw [lWord_evensTransversal_one U.toSubgroup s hU hs,
      lWord_evensTransversal_mk U.toSubgroup s hU hs]
    have hγ' : γ ∉ U.toSubgroup := hγ
    simp_rw [ite_eq_right hγ']
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
Shapiro components.  Neither summand is a cocycle on its own; the equation is between the
corestriction class and the class of their sum, in the explicit inhomogeneous model `H1` that
carries the corestriction `explicitCor1`. -/
theorem evensNorm_cor_shapiro (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (s : G) (hs : s ∉ U) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    explicitCor1 G (trivialF2 G).V U.toSubgroup U.isOpen'
        (evensHomCocycleAmbient U α hα : H1 U.toSubgroup (trivialF2 G).V) =
      (evensCorCocycle U s α hU hs hα : H1 G (trivialF2 G).V) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  rw [explicitCor1_eq_transversal G (trivialF2 G).V U.toSubgroup
    (evensTransversal U.toSubgroup s) (evensTransversal_mk U.toSubgroup s hU hs) U.isOpen']
  rw [explicitCor1Transversal_mk]
  apply congrArg (fun z : Z1 G (trivialF2 G).V => (z : H1 G (trivialF2 G).V))
  apply Subtype.ext
  rw [coe_cocyclesCor1, cochainsCor1_evensTransversal U s α hU hs hα]
  exact (coe_evensCorCocycle U s α hU hs hα).symm

end Corestriction

end TauCeti.ContCohomology
