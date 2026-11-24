/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The semi-Fredholm estimate along the capped comparison family

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

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

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
  -- Near the pole `∞` the data are `J₀` and `0`.
  have hT := equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact.eventually
    ((eventually_cocompact_cappedAlmostComplex_eq_base (M := V) (J := J) (hJ := hJ)
      (L := comparisonNeckLength R) h₀ (3 * R - 1)).and
      (eventually_cocompact_cappedPerturbation_eq_zero (M := V) (a := comparisonCutoff R)
        (L := comparisonNeckLength R) (H := H)))
  rw [← cobounded_eq_cocompact, hasBasis_cobounded_norm.eventually_iff] at hT
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at hT
  obtain ⟨T, -, hT⟩ := hT
  -- The data, read in the plane chart, are smooth jointly in the domain and target points.
  have hg {n : WithTop ℕ∞} : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × V) (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))) n
      fun p : (ℝ × ℝ) × V ↦ (equivRealProdCLM.symm p.1, (R, p.2)) :=
    (equivRealProdCLM.symm.contDiff.comp contDiff_fst).contMDiff.prodMk
      (contMDiff_const.prodMk contDiff_snd.contMDiff)
  have hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (cappedComparisonAlmostComplex h₀ J hJ R
      (equivRealProdCLM.symm p.1) p.2).toLinearMap.toContinuousLinearMap :=
    ((contMDiff_cappedComparisonAlmostComplex h₀ hJp
      fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJs q).contMDiff).comp hg).contDiff
  have hK' (v : ℂ) : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦
      cappedComparisonPerturbation H R (equivRealProdCLM.symm p.1) p.2 v :=
    (contDiff_cappedComparisonPerturbation_apply hH hHs v).comp
      (contDiff_const.prodMk contDiff_id)
  exact exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base
    (fun z hz y ↦ by rw [cappedComparisonAlmostComplex_def]; exact (hT hz).1 y)
    (fun z hz y ↦ by
      rw [cappedComparisonPerturbation_def, (hT hz).2 y, zero_apply])
    (fun z hz y ↦ by
      rw [cappedComparisonPerturbation_def, (hT hz).2 y, zero_apply])
    (fun z ↦ hJ'.contDiffAt) (fun z ↦ (hK' 1).contDiffAt)
    (fun z ↦ (hK' I).contDiffAt) hu fun z ↦ by
      rw [cappedComparisonAlmostComplex_def]
      exact compatible_cappedAlmostComplex h₀ hJc _ _ _ _

end TauCeti.SymplecticForm
