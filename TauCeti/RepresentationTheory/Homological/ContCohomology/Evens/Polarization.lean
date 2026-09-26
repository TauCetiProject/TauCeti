/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Restriction

/-!
# Polarization of the explicit Evens graph-cocycle class

Let `U` be an open subgroup of index two in a topological group `G`, let `s ∉ U`, and let
`α β : U →* Multiplicative (ZMod 2)` be continuous homomorphisms. The graph cochain `ν_α` of
`TauCeti.ContCohomology.evensGraphCochain` is quadratic in `α`, and this file identifies its
failure of additivity on classes: in the explicit inhomogeneous model,

```text
[ν_{α + β}] - [ν_α] - [ν_β] = cor² ([α] ⌣ evensConj1 [β])   in H²(G, 𝔽₂),
```

where `cor²` is degree-two corestriction, `⌣` is the `(1,1)` cup product for the multiplication
pairing of `𝔽₂`, and `evensConj1 = res ∘ cor - id` is the choice-free conjugation on `H¹(U, 𝔽₂)`.
This is the polarization identity of the index-two Evens norm (Kozlowski, Lemma 2.4 in
cohomological form). Its right-hand side carries the conjugate of `[β]`, not `[β]` itself. The sum
`α + β` of two homomorphisms to `𝔽₂` is the pointwise product `α * β` of homomorphisms to
`Multiplicative (ZMod 2)`, and that is how it is written in the statement.

## Main result

* `TauCeti.ContCohomology.evensGraphCocycle_polarization`: the polarization identity above, in
  explicit `H²(G, 𝔽₂)`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

section Transversal

/-! ### The corestriction sum on the transversal `{1, s}` -/

variable {G : Type u} [Group G] {U : Subgroup G} {s : G} {α β : U →* Multiplicative (ZMod 2)}

/-- At the trivial coset, `α` read on the transversal word is the first Shapiro component. -/
private theorem evensExtend_lWord_mk_one (hU : U.index = 2) (hs : s ∉ U) (γ : G) :
    evensExtend U α (lWord U (U.indexTwoTransversal s) (QuotientGroup.mk 1) γ) =
      evensB1 U s α γ := by
  by_cases hγ : γ ∈ U
  · rw [lWord_indexTwoTransversal_mk_one_of_mem s hγ, evensB1_of_mem hγ]
  · rw [lWord_indexTwoTransversal_mk_one_of_notMem hU hs hγ, evensB1_of_notMem hγ]

/-- At the coset of `s`, `α` read on the transversal word is the second Shapiro component. -/
private theorem evensExtend_lWord_mk (hU : U.index = 2) (hs : s ∉ U) (γ : G) :
    evensExtend U α (lWord U (U.indexTwoTransversal s) (QuotientGroup.mk s) γ) =
      evensBs U s α γ := by
  by_cases hγ : γ ∈ U
  · have hsγ : s⁻¹ * γ ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
    rw [lWord_indexTwoTransversal_mk_of_mem hU hs hγ, evensBs_apply, evensB1_of_notMem hsγ]
  · have hsγ : s⁻¹ * γ ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
    rw [lWord_indexTwoTransversal_mk_of_notMem hU hs hγ, evensBs_apply, evensB1_of_mem hsγ]

open scoped Classical in
/-- At the trivial coset, the `s`-conjugate of `β` read on the transversal word is the second
Shapiro component, corrected by `β (s²)` off `U`. -/
private theorem evensExtend_conj_lWord_mk_one (hU : U.index = 2) (hs : s ∉ U) (η : G) :
    evensExtend U β (s⁻¹ * lWord U (U.indexTwoTransversal s) (QuotientGroup.mk 1) η * s) =
      evensBs U s β η + if η ∈ U then 0 else evensExtend U β (s * s) := by
  have hss : s * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs]
  by_cases hη : η ∈ U
  · have hsη : s⁻¹ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    rw [lWord_indexTwoTransversal_mk_one_of_mem s hη, evensBs_apply, evensB1_of_notMem hsη,
      ite_eq_left hη, add_zero]
  · have hsη : s⁻¹ * η ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    have hsplit : s⁻¹ * (η * s) * s = s⁻¹ * η * (s * s) := by group
    rw [lWord_indexTwoTransversal_mk_one_of_notMem hU hs hη, hsplit, evensExtend_mul hsη hss,
      evensBs_apply, evensB1_of_mem hsη, ite_eq_right hη]

open scoped Classical in
/-- At the coset of `s`, the `s`-conjugate of `β` read on the transversal word is the first
Shapiro component, corrected by `β (s²)` off `U`. -/
private theorem evensExtend_conj_lWord_mk (hU : U.index = 2) (hs : s ∉ U) (η : G) :
    evensExtend U β (s⁻¹ * lWord U (U.indexTwoTransversal s) (QuotientGroup.mk s) η * s) =
      evensB1 U s β η + if η ∈ U then 0 else evensExtend U β (s * s) := by
  have hss : s * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs]
  by_cases hη : η ∈ U
  · have hsplit : s⁻¹ * (s⁻¹ * η * s) * s = (s * s)⁻¹ * η * (s * s) := by group
    rw [lWord_indexTwoTransversal_mk_of_mem hU hs hη, hsplit,
      evensExtend_mul (U.mul_mem (U.inv_mem hss) hη) hss, evensExtend_mul (U.inv_mem hss) hη,
      evensExtend_inv, evensB1_of_mem hη, ite_eq_left hη]
    grind
  · have hηs : η * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    have hsplit : s⁻¹ * (s⁻¹ * η) * s = (s * s)⁻¹ * (η * s) := by group
    rw [lWord_indexTwoTransversal_mk_of_notMem hU hs hη, hsplit,
      evensExtend_mul (U.inv_mem hss) hηs, evensExtend_inv, evensB1_of_notMem hη, ite_eq_right hη,
      add_comm]

open scoped Classical in
/-- The sum of the extension by zero at `γ` and at `s⁻¹ γ` is the first Shapiro
component on `U` and the second one off `U`: exactly one of the two points lies in `U`. -/
private theorem evensExtend_add_evensExtend_inv_mul (hU : U.index = 2) (hs : s ∉ U) (γ : G) :
    evensExtend U α γ + evensExtend U α (s⁻¹ * γ) =
      if γ ∈ U then evensB1 U s α γ else evensBs U s α γ := by
  by_cases hγ : γ ∈ U
  · have hsγ : s⁻¹ * γ ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
    rw [evensExtend_of_notMem hsγ, add_zero, ite_eq_left hγ, evensB1_of_mem hγ]
  · have hsγ : s⁻¹ * γ ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
    rw [evensExtend_of_notMem hγ, zero_add, ite_eq_right hγ, evensBs_apply, evensB1_of_mem hsγ]

/-
The proof is a cochain computation on the transversal `{1, s}`. Writing `a₁, a_s` and `b₁, b_s`
for the Shapiro components of `α` and `β`, the transversal words turn the value of `α` into `a₁`
or `a_s` and the value of the conjugate of `β` into `b_s` or `b₁`, up to the constant `β (s²)` off
`U`. The difference between the corestriction cochain and the polarization of the graph cochain
is then the coboundary of

```text
γ ↦ b₁ γ · a_s γ + β (s²) · (alpha-tilde γ + alpha-tilde (s⁻¹ γ)),
```

Here alpha-tilde denotes the extension of `α` by zero. Both summands are needed; the second
absorbs the cup product of `cor α` with the character of `G ⧸ U`.
-/
/-- **The polarization of the graph cochain, on cochains.** The polarization of `ν` differs from
the corestriction over `{1, s}` of the cup product of `α` with the `s`-conjugate of `β` by the
coboundary of the stated cochain, with `a_s` the second Shapiro component of `α`, `b₁` the first
one of `β` and alpha-tilde the extension of `α` by zero. -/
private theorem evensGraphCochain_polarization [Fintype (G ⧸ U)] (hU : U.index = 2)
    (hs : s ∉ U) (γ η : G) :
    evensGraphCochain U s (α * β) (γ, η) - evensGraphCochain U s α (γ, η) -
        evensGraphCochain U s β (γ, η) -
        ∑ u : G ⧸ U, evensExtend U α (lWord U (U.indexTwoTransversal s) u γ) *
          evensExtend U β (s⁻¹ * lWord U (U.indexTwoTransversal s) (γ⁻¹ • u) η * s) =
      (evensB1 U s β η * evensBs U s α η +
          evensExtend U β (s * s) * (evensExtend U α η + evensExtend U α (s⁻¹ * η))) -
        (evensB1 U s β (γ * η) * evensBs U s α (γ * η) +
          evensExtend U β (s * s) *
            (evensExtend U α (γ * η) + evensExtend U α (s⁻¹ * (γ * η)))) +
        (evensB1 U s β γ * evensBs U s α γ +
          evensExtend U β (s * s) * (evensExtend U α γ + evensExtend U α (s⁻¹ * γ))) := by
  have := Subgroup.normal_of_index_eq_two hU
  rw [sum_quotient_eq_add_of_index_two hU hs,
    evensExtend_add_evensExtend_inv_mul hU hs η, evensExtend_add_evensExtend_inv_mul hU hs γ,
    evensExtend_add_evensExtend_inv_mul hU hs (γ * η),
    evensExtend_lWord_mk_one hU hs, evensExtend_lWord_mk hU hs]
  by_cases hγ : γ ∈ U <;> by_cases hη : η ∈ U
  · simp only [smul_quotient_eq_self_of_mem (U.inv_mem hγ), ite_eq_left hγ, ite_eq_left hη,
      ite_eq_left (U.mul_mem hγ hη),
      evensExtend_conj_lWord_mk_one hU hs, evensExtend_conj_lWord_mk hU hs,
      evensGraphCochain_of_mem hγ, evensB1_mul_hom, evensBs_mul_hom,
      evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_mem hU hs hγ]
    grind
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    simp only [smul_quotient_eq_self_of_mem (U.inv_mem hγ), ite_eq_left hγ, ite_eq_right hη,
      ite_eq_right hγη,
      evensExtend_conj_lWord_mk_one hU hs, evensExtend_conj_lWord_mk hU hs,
      evensGraphCochain_of_mem hγ, evensB1_mul_hom, evensBs_mul_hom,
      evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_mem hU hs hγ]
    grind
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    simp only [smul_mk_one_of_notMem_of_index_two hU hs (mt U.inv_mem_iff.1 hγ),
      smul_mk_of_notMem_of_index_two hU hs (mt U.inv_mem_iff.1 hγ), ite_eq_right hγ,
      ite_eq_left hη, ite_eq_right hγη,
      evensExtend_conj_lWord_mk_one hU hs, evensExtend_conj_lWord_mk hU hs,
      evensGraphCochain_of_notMem hγ, evensB1_mul_hom, evensBs_mul_hom,
      evensB1_mul_of_notMem hU hs hγ, evensBs_mul_of_notMem hU hs hγ]
    grind
  · have hγη : γ * η ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    simp only [smul_mk_one_of_notMem_of_index_two hU hs (mt U.inv_mem_iff.1 hγ),
      smul_mk_of_notMem_of_index_two hU hs (mt U.inv_mem_iff.1 hγ), ite_eq_right hγ,
      ite_eq_right hη, ite_eq_left hγη,
      evensExtend_conj_lWord_mk_one hU hs, evensExtend_conj_lWord_mk hU hs,
      evensGraphCochain_of_notMem hγ, evensB1_mul_hom, evensBs_mul_hom,
      evensB1_mul_of_notMem hU hs hγ, evensBs_mul_of_notMem hU hs hγ]
    grind

end Transversal

section Class

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The `1`-cochain whose coboundary is the polarization defect is continuous. -/
private theorem continuous_evensPolarizationCochain (U : Subgroup G) (s : G)
    (α β : U →* Multiplicative (ZMod 2)) (hopen : IsOpen (U : Set G)) (hα : Continuous α)
    (hβ : Continuous β) :
    Continuous fun x : G => evensB1 U s β x * evensBs U s α x +
      evensExtend U β (s * s) * (evensExtend U α x + evensExtend U α (s⁻¹ * x)) := by
  have hext := continuous_evensExtend U α hopen hα
  exact ((continuous_evensB1 U s β hopen hβ).mul (continuous_evensBs U s α hopen hα)).add
    (Continuous.mul (M := ZMod 2) continuous_const
      (hext.add (hext.comp (continuous_const_mul s⁻¹))))

/-- **Polarization of the explicit Evens graph-cocycle class.** For an open subgroup `U` of index
two, an element `s ∉ U` and continuous homomorphisms `α β : U → 𝔽₂`, the failure of additivity of
the graph-cocycle class, `[ν_{α + β}] - [ν_α] - [ν_β]`, is the degree-two corestriction of the
`(1,1)` cup product of `[α]` with the choice-free conjugate `TauCeti.ContCohomology.evensConj1` of
`[β]`, for the multiplication pairing of `𝔽₂`. The sum `α + β` is written `α * β`, the pointwise
product in `Multiplicative (ZMod 2)`. All classes lie in the explicit model. -/
theorem evensGraphCocycle_polarization (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    {s : G} (hs : s ∉ U) (α β : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α)
    (hβ : Continuous β) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (evensGraphCocycle U s (α * β) hU hs (hα.mul hβ) : H2 G (trivialF2 G).V) -
        (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) -
        (evensGraphCocycle U s β hU hs hβ : H2 G (trivialF2 G).V) =
      explicitCor2 G (trivialF2 G).V U.toSubgroup U.isOpen'
        (explicitCup11 U.toSubgroup (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
          (trivialF2Pairing G) continuous_of_discreteTopology
          (fun u m n => trivialF2Pairing_smul_smul G (u : G) m n)
          (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)
          (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen'
            (evensHomCocycleAmbient U.toSubgroup β hβ : H1 U.toSubgroup (trivialF2 G).V))) := by
  have := Subgroup.normal_of_index_eq_two hU
  have : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let : Fintype (G ⧸ U.toSubgroup) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [evensConj1_eq_explicitConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen' hs,
    explicitConj1_apply_eq_smul, smul_mk, explicitCup11_mk,
    explicitCor2_eq_transversal G (trivialF2 G).V U.toSubgroup (U.toSubgroup.indexTwoTransversal s)
      (Subgroup.indexTwoTransversal_mk hU hs) U.isOpen',
    explicitCor2Transversal_mk, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub, H2pi_eq_iff]
  refine mem_B2_iff'.2 ⟨fun x => (trivialF2Equiv G).symm
    (evensB1 U.toSubgroup s β x * evensBs U.toSubgroup s α x +
      evensExtend U.toSubgroup β (s * s) *
        (evensExtend U.toSubgroup α x + evensExtend U.toSubgroup α (s⁻¹ * x))), ?_, ?_⟩
  · exact continuous_of_discreteTopology.comp
      (continuous_evensPolarizationCochain U.toSubgroup s α β U.isOpen' hα hβ)
  · intro γ η
    apply (trivialF2Equiv G).injective
    simp only [trivialF2Equiv_symm_apply, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply,
      map_add, map_sub, trivialF2Equiv_apply, AddSubgroupClass.coe_sub, coe_evensGraphCocycle,
      coe_evensHomCocycleAmbient, cocyclesMap1_coe, cochainsMap1_apply, MonoidHom.coe_coe,
      Subgroup.inverseConjugationHom_apply, DistribSMul.toAddMonoidHom_apply,
      trivialF2Pairing_apply, coe_cocyclesCor2, Pi.sub_apply, cochainsCor2_apply,
      Subgroup.mk_smul, map_sum]
    simp only [← evensExtend_of_mem]
    exact (evensGraphCochain_polarization hU hs γ η).symm

end Class

end TauCeti.ContCohomology
