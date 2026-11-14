/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Capped
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Compactness of the capped comparison family

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes. The result is a sphere
with three poles `0`, `1` and `∞`, carrying the one-parameter family of Hamiltonian data
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R` and of almost complex structures
`J_R = TauCeti.Floer.cappedComparisonAlmostComplex h₀ J hJ R`, for `R ≥ 0`. At `R = 0` the
problem is the unperturbed one for the domain-independent compatible structure `J₀`; as `R → ∞`
three necks of length `R - 1` grow along the ends.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window of parameters `C ⊆ [0, ∞)`, for a symplectic vector space target `(V, ω)`, in the plane
chart `ℂ ≅ ℝ × ℝ` of the complement of the pole `∞`. The datum `K_R` vanishes and `J_R` is `J₀`
near the poles `0` and `1`, so these are ordinary points of the chart, at which a solution is
`J₀`-holomorphic.

The input is the energy identity of the family
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`):
for `|H_q| ≤ B_q` and every `R ≥ 0`, the Floer energy of a map differs from its symplectic area
`∫ ω(∂ₛu, ∂ₜu)` by at most `2 (B₀ + B₁ + B_∞)`. For maps extending to the sphere in a class `A`,
the area is `ω(A)`. So solutions whose areas are bounded by `A`, for instance the solutions in a
fixed class, have Floer energy at most `A + 2 (B₀ + B₁ + B_∞)` for every member of the family.
The data `K_R` and `J_R` are smooth jointly in `R` and in the domain and target points
(`TauCeti.Floer.contMDiff_cappedComparisonPerturbation`,
`TauCeti.Floer.contMDiff_cappedComparisonAlmostComplex`), and `J_R` is tamed by `ω`
everywhere. Compactness over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
then applies on every compact window `D` of the plane chart.

The main result, in the namespace `TauCeti.SymplecticForm`,
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison`)
gives a threshold `δ > 0` such that every sequence of solutions for parameters `Rₖ ∈ C`, with
areas at most `A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V`, has a subsequence whose
parameters converge to some `R₀ ∈ C` and which converges locally uniformly on `Ω` off a finite set
`Z` of bubbling points, with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`. The regularity of the limit, the
bubbles at the points of `Z`, the behaviour near the pole `∞`, and the long-neck end `R → ∞` of
the family are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **Solutions of the capped comparison family converge off finitely many bubbling points.** Let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let
`J_q(t, x)` be period-one `C²` families of `ω`-tame structures on the three ends. Fix a compact
window `C ⊆ [0, ∞)` of parameters and compact sets `D ⊆ ℝ × ℝ` and `K ⊆ V`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the
three-pole sphere solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures
`J_{Rₖ}(z, u)` of the comparison family, with `Rₖ ∈ C`, integrable energy density, symplectic area
`∫ ω(∂ₛuₖ, ∂ₜuₖ) ≤ A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `φ`, a
limit `R₀ ∈ C` of `R_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
Floer energy at least `δ`, the differentials are uniformly bounded on every compact subset of
`Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₀ : C ⊆ Ici 0)
    (hD : IsCompact D) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, R k ∈ C) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      ∃ (φ : ℕ → ℕ) (R₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ R₀ ∈ C ∧
        Tendsto (fun n ↦ R (φ n)) atTop (𝓝 R₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The data of the family, read in the plane chart, are jointly smooth in `(R, z, x)`: they are
  -- the smooth data on `ℂ × (ℝ × V)` composed with `(R, z, x) ↦ (z, (R, x))`.
  have hg {n : WithTop ℕ∞} : ContMDiff 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V))
      (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))) n
      fun q : ℝ × ((ℝ × ℝ) × V) ↦ (equivRealProdCLM.symm q.2.1, (q.1, q.2.2)) :=
    (equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.prodMk
      (contDiff_fst.contMDiff.prodMk (contDiff_snd.comp contDiff_snd).contMDiff)
  have hK' (v : ℂ) : ContDiffOn ℝ 3 (fun q : ℝ × ((ℝ × ℝ) × V) ↦
      cappedComparisonPerturbation H q.1 (equivRealProdCLM.symm q.2.1) q.2.2 v) univ :=
    (contDiff_cappedComparisonPerturbation_apply (n := 3) hH hHs v).contDiffOn
  have hJ' : ContDiffOn ℝ 2 (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (cappedComparisonAlmostComplex h₀ J hJ
      q.1 (equivRealProdCLM.symm q.2.1) q.2.2).toLinearMap.toContinuousLinearMap) univ :=
    ((contMDiff_cappedComparisonAlmostComplex h₀ hJp
      fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJs q).contMDiff).comp hg
      ).contDiff.contDiffOn
  have hJt (R : ℝ) (w : ℂ) (x : V) : ω.Tames (cappedComparisonAlmostComplex h₀ J hJ R w x) := by
    rw [cappedComparisonAlmostComplex_def]
    exact tames_cappedAlmostComplex h₀ _ _ w x
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
    (Kt := fun R z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I)
    (J := fun R z x ↦ cappedComparisonAlmostComplex h₀ J hJ R (equivRealProdCLM.symm z) x)
    isOpen_univ (hK' 1) (hK' I) hJ' hC hD hK (subset_univ _) fun R _ z _ x _ ↦ hJt R _ x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hRC hu hfl huK hint harea ↦ ?_⟩
  -- The Floer energy over `Ω` is at most the energy over the plane, which exceeds the area by at
  -- most `2 (B₀ + B₁ + B_∞)`.
  have hE (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k) z ≤
        A + 2 * ∑ q, B q := by
    have habs := ω.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀ (hRC k)) ((hu k).of_le (by norm_num))
      (hint k)
    refine (setIntegral_le_integral (hint k) (Eventually.of_forall fun z ↦
      ω.floerEnergyDensity_nonneg (hJt _ _ _) (hfl k z))).trans ?_
    linarith [(abs_sub_le_iff.1 habs).1, harea k]
  exact hconv hΩ hΩD hRC (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK
    (fun k ↦ (hint k).integrableOn) hE

end TauCeti.SymplecticForm
