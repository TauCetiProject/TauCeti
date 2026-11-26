/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal

/-!
# Hamiltonian variations along the capped comparison family detect the cokernel

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz plane to each of the three ends of a pair of pants. The domains of the
resulting one-parameter family of Floer problems are spheres with three poles, `0`, `1` and `∞` in
the coordinate `w` of `ℂ`, with the Hamiltonian data `K_R`
(`TauCeti.Floer.cappedComparisonPerturbation`) and the almost complex structures `J_R`
(`TauCeti.Floer.cappedComparisonAlmostComplex`), on a finite-dimensional symplectic vector space
`(V, ω)`.

This file proves that Hamiltonian variations detect the whole cokernel of the linearized operator
`D_u` of every member of the family, realized from `W^{1,2}` of the sphere to `L²` as
`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the weight
`TauCeti.Floer.sphereWeight`: for any nonempty open set `O` of the plane chart and any
neighbourhood `W` of the graph of `u` over `O`, the range of `D_u` and the Hamiltonian variations
supported in `W` (`TauCeti.SymplecticForm.hamiltonianVariationsOn`) span a dense subspace of `L²`
(`topologicalClosure_range_sup_span_hamiltonianVariationsOn_cappedComparison_eq_top`, in the
namespace `TauCeti.SymplecticForm`). This is the cokernel detection of
`TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal` on the whole plane, with the
essential boundedness of the coefficient field of `D_u` on conformal jets
(`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_cappedComparison`). The smoothness it needs
is that of the data read in the plane chart
(`TauCeti.Floer.contDiff_cappedComparisonAlmostComplex_equivRealProdCLM`,
`TauCeti.Floer.contDiff_cappedComparisonPerturbation_equivRealProdCLM`). No hypothesis is
placed on `u` over `O`, which may be constant there.

The statement is linear: it holds for every member `R`, including the member `R = 0`, whose
perturbation vanishes. When `D_u` is Fredholm, the closed range of finite codimension turns
density into surjectivity, with finitely many variations
(`TauCeti.SymplecticForm.exists_finset_subset_hamiltonianVariationsOn_range_sup_span_eq_top`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 and Section 8.1.
-/

public section

open Complex Set Function Topology MeasureTheory TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **Hamiltonian variations make the linearized operator along the capped comparison family
dense.** Let `J₀` be `ω`-compatible, let `J_q(t, x)` be period-one `C²` families of `ω`-tame
structures on the three ends, and let `H_q` be period-one `C³` Hamiltonians. For every member `R`
of the comparison family, every `C²` map `u` of the plane chart of the three-pole sphere, every
nonempty open set `O` of the plane chart and every neighbourhood `W` of the graph of `u` over `O`,
the range of the realization `D_u` of the linearized operator of the data `K_R` and `J_R` from
`W^{1,2}` of the sphere to `L²`, and the Hamiltonian variations supported in `W`, span a dense
subspace of `L²`. -/
theorem topologicalClosure_range_sup_span_hamiltonianVariationsOn_cappedComparison_eq_top
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) (R : ℝ)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hOne : O.Nonempty)
    {W : Set ((ℝ × ℝ) × V)} (hW : ∀ z ∈ O, W ∈ 𝓝 (z, u z)) :
    ((ω.floerConformalSobolevOperator univ sphereWeight
        (fun z y ↦ (cappedComparisonAlmostComplex h₀ J hJ R
          (equivRealProdCLM.symm z) y).toLinearMap.toContinuousLinearMap)
        (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y 1)
        (fun z y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y I) u).range ⊔
      Submodule.span ℝ (ω.hamiltonianVariationsOn univ u W)).topologicalClosure = ⊤ :=
  topologicalClosure_range_floerConformalSobolevOperator_sup_span_hamiltonianVariationsOn_eq_top
    isWeight_sphereWeight isPreconnected_univ
    (fun _ _ ↦ (contDiff_cappedComparisonAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs R).contDiffAt)
    (fun _ _ ↦ ContinuousLinearMap.ext fun v ↦ by simp)
    (fun _ _ ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R 1).contDiffAt)
    (fun _ _ ↦ (contDiff_cappedComparisonPerturbation_equivRealProdCLM hH hHs R I).contDiffAt)
    (fun _ _ ↦ hu.contDiffAt)
    (ω.memLp_floerConformalJetCoeff_cappedComparison h₀ hJ hJp (fun q ↦ (hJs q).of_le one_le_two)
      hH (fun q ↦ (hHs q).of_le (by norm_num)) R (hu.of_le one_le_two))
    hO hOne (subset_univ O) hW

end TauCeti.SymplecticForm
