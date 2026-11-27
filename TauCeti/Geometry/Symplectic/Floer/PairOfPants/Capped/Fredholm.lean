/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped.SemiFredholm

/-!
# The Fredholm property along the capped comparison family

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz plane to each of the three ends of a pair of pants. The domains of the
resulting one-parameter family of Floer problems are spheres with three poles, `0`, `1` and `∞` in
the coordinate `w` of `ℂ`, with the Hamiltonian data `K_R`
(`TauCeti.Floer.cappedComparisonPerturbation`) and the almost complex structures `J_R`
(`TauCeti.Floer.cappedComparisonAlmostComplex`), unperturbed near the poles.

This file proves that for every member `R` of the family and every `C³` map `u` of the plane chart
into a symplectic inner product space, the realization of the linearized operator `D_u` from
`W^{1,2}` of the sphere to `L²` is Fredholm
(`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_cappedComparison`), for `C³`
families of compatible structures and `C⁴` Hamiltonians on the ends. This is
`TauCeti.SymplecticForm.isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base` for the
data of the family, which are the base structure and the zero perturbation near `∞`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
-/

public section

open Complex Function Set TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **The linearized operator along the capped comparison family is Fredholm.** Let `J₀` be
`ω`-compatible, let `J_q(t, x)` be period-one `C³` families of `ω`-compatible structures on the
three ends, and let `H_q` be period-one `C⁴` Hamiltonians. For every member `R` of the comparison
family and every `C³` map `u` of the plane chart of the three-pole sphere, the realization of the
linearized operator `D_u` of the data `K_R` and `J_R` from `W^{1,2}` of the sphere to `L²` is
Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 3 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 4 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 3 u) :
    (ω.floerConformalSobolevOperator univ sphereWeight
      (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
        (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
      (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u).IsFredholm := by
  obtain ⟨T, hJ₀, hK₀⟩ := exists_cappedComparison_eq_base (H := H) h₀ hJ R
  exact ω.isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (T := T) hJ₀ (fun z hz y ↦ hK₀ z hz y 1) (fun z hz y ↦ hK₀ z hz y I)
    (fun z ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun z ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt) hu
    fun z ↦ by
      rw [cappedComparisonAlmostComplex_def]
      exact compatible_cappedAlmostComplex h₀ hJc _ _ _ _

end TauCeti.SymplecticForm
