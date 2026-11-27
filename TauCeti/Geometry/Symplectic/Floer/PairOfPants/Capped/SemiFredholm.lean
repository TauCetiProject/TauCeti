/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere

/-!
# The semi-Fredholm property along the capped comparison family

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz plane to each of the three ends of a pair of pants. The domains of the
resulting one-parameter family of Floer problems are spheres with three poles, `0`, `1` and `∞` in
the coordinate `w` of `ℂ`, with the Hamiltonian data `K_R`
(`TauCeti.Floer.cappedComparisonPerturbation`) and the almost complex structures `J_R`
(`TauCeti.Floer.cappedComparisonAlmostComplex`). Both are unperturbed near the poles: `K_R`
vanishes and `J_R` is the base structure `J₀` outside a compact truncation of the pair of pants.

This file records, for every member `R` of the family and every `C¹` map `u` of the plane chart
`ℝ × ℝ ≅ ℂ` into a symplectic vector space, the a priori estimate behind the Fredholm property of
the linearized operator `D_u` on the closed sphere: there are `R'` and `C ≥ 0` such that

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ R'} ‖ξ‖²)`,  `ρ(w) = (1 + |w|²)⁻²`,

for every compactly supported `C²` section `ξ`
(`exists_forall_integral_le_mul_integral_floerLinearization_cappedComparison_add`, in the namespace
`TauCeti.SymplecticForm`). The left side is the squared `W^{1,2}` norm of `ξ` on the sphere. This
is the estimate on the sphere with data unperturbed near `∞`,
`TauCeti.SymplecticForm.exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base`;
the poles `0` and `1` are interior points of the plane chart.

The same reduction applies to the realization of `D_u` on the Sobolev space of the sphere,
`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the weight
`TauCeti.Floer.sphereWeight` (`TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere`). Along every
member of the family its coefficient field is essentially bounded
(`memLp_floerConformalJetCoeff_cappedComparison`), so it realizes `D_u` from `W^{1,2}` of the
sphere to `L²`, and it has finite-dimensional kernel
(`finiteDimensional_ker_floerConformalSobolevOperator_cappedComparison`) and closed range
(`isClosed_range_floerConformalSobolevOperator_cappedComparison`), all in the namespace
`TauCeti.SymplecticForm`. The finiteness of the cokernel, which makes `D_u` Fredholm, is proved in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped.Fredholm`; the index is not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set TauCeti.ThricePuncturedSphere
open scoped ENNReal

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- Near the pole `∞`, on `‖w‖ ≥ T` in the plane chart, the data of the capped comparison family
are the base structure `J₀` and the zero perturbation. -/
theorem exists_cappedComparison_eq_base {ω : SymplecticForm V} (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Tames (J q t x)) (R : ℝ) :
    ∃ T, (∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y,
        cappedComparisonAlmostComplex h₀ J hJ R (equivRealProdCLM.symm z) y = J₀) ∧
      ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y v,
        cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y v = 0 := by
  have hT := equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact.eventually
    ((eventually_cocompact_cappedAlmostComplex_eq_base (M := V) (J := J) (hJ := hJ)
      (L := comparisonNeckLength R) h₀ (3 * R - 1)).and
      (eventually_cocompact_cappedPerturbation_eq_zero (M := V) (a := comparisonCutoff R)
        (L := comparisonNeckLength R) (H := H)))
  rw [← cobounded_eq_cocompact, hasBasis_cobounded_norm.eventually_iff] at hT
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at hT
  obtain ⟨T, -, hT⟩ := hT
  refine ⟨T, fun z hz y ↦ ?_, fun z hz y v ↦ ?_⟩
  · rw [cappedComparisonAlmostComplex_def]
    exact (hT hz).1 y
  · rw [cappedComparisonPerturbation_def, (hT hz).2 y, zero_apply]

/-- **The semi-Fredholm estimate along the capped comparison family.** Let `J₀` be
`ω`-compatible, let `J_q(t, x)` be period-one `C¹` families of `ω`-compatible structures on the
three ends, and let `H_q` be period-one `C²` Hamiltonians. For every member `R` of the comparison
family and every `C¹` map `u` of the plane chart of the three-pole sphere there are `R'` and
`C ≥ 0` such that every compactly supported `C²` section `ξ` satisfies

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ R'} ‖ξ‖²)`,  `ρ(w) = (1 + |w|²)⁻²`,

for the linearized operator `D_u` of the data `K_R` and `J_R` of the family. -/
theorem exists_forall_integral_le_mul_integral_floerLinearization_cappedComparison_add
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) :
    ∃ R' C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
            (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
          (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
          (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u ξ z‖ ^ 2) +
          ∫ z in closedBall 0 R', ‖ξ z‖ ^ 2) := by
  obtain ⟨T, hJ₀, hK₀⟩ := exists_cappedComparison_eq_base (H := H) h₀ hJ R
  exact exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base
    (T := T) hJ₀ (fun z hz y ↦ hK₀ z hz y 1) (fun z hz y ↦ hK₀ z hz y I)
    (fun z ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt) hu
    fun z ↦ by
      rw [cappedComparisonAlmostComplex_def]
      exact compatible_cappedAlmostComplex h₀ hJc _ _ _ _

/-- **The coefficient field along the capped comparison family is bounded.** Under the hypotheses
of `exists_forall_integral_le_mul_integral_floerLinearization_cappedComparison_add`, without the
compatibility of the structures, the coefficient field of the linearized operator `D_u` of the
data `K_R` and `J_R` on the conformal jets of the weight of the sphere is essentially bounded on the
plane, so that `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from
`W^{1,2}` of the sphere to `L²`. -/
theorem memLp_floerConformalJetCoeff_cappedComparison (ω : SymplecticForm V)
    (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Tames (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) :
    MemLp (ω.floerConformalJetCoeff sphereWeight
      (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
        (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u) ∞
      (volume.restrict univ) := by
  obtain ⟨T, hJ₀, hK₀⟩ := exists_cappedComparison_eq_base (H := H) h₀ hJ R
  exact ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
    (J₀ := J₀.toLinearMap.toContinuousLinearMap) (T := T) (fun z hz y ↦ by rw [hJ₀ z hz y])
    (fun z hz y ↦ hK₀ z hz y 1) (fun z hz y ↦ hK₀ z hz y I)
    (fun z ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt) hu

/-- **The linearized operator along the capped comparison family has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of
`exists_forall_integral_le_mul_integral_floerLinearization_cappedComparison_add`, the realization
of the linearized operator `D_u` of the data `K_R` and `J_R` from `W^{1,2}` of the sphere to `L²`
has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
        (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u).ker := by
  obtain ⟨T, hJ₀, hK₀⟩ := exists_cappedComparison_eq_base (H := H) h₀ hJ R
  exact ω.finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (T := T) hJ₀ (fun z hz y ↦ hK₀ z hz y 1) (fun z hz y ↦ hK₀ z hz y I)
    (fun z ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt) hu
    fun z ↦ by
      rw [cappedComparisonAlmostComplex_def]
      exact compatible_cappedAlmostComplex h₀ hJc _ _ _ _

/-- **The linearized operator along the capped comparison family has closed range on
`W^{1,2}`.** Under the hypotheses of
`exists_forall_integral_le_mul_integral_floerLinearization_cappedComparison_add`, the realization
of the linearized operator `D_u` of the data `K_R` and `J_R` from `W^{1,2}` of the sphere to `L²`
has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) :
    IsClosed (Set.range (ω.floerConformalSobolevOperator univ sphereWeight
      (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
        (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u)) := by
  obtain ⟨T, hJ₀, hK₀⟩ := exists_cappedComparison_eq_base (H := H) h₀ hJ R
  exact ω.isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (T := T) hJ₀ (fun z hz y ↦ hK₀ z hz y 1) (fun z hz y ↦ hK₀ z hz y I)
    (fun z ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt) hu
    fun z ↦ by
      rw [cappedComparisonAlmostComplex_def]
      exact compatible_cappedAlmostComplex h₀ hJc _ _ _ _

end TauCeti.SymplecticForm
