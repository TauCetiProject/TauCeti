/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Compactness of spheres with moving input ends over compact windows of configurations

A sphere with moving input ends has input punctures at points `c i` of `ℂ`, with cylindrical
ends of scales `a i`, and an output puncture at `∞`. It carries the perturbation datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, equal to `H_i(t) dt` far out on the input
end `i` and to `Hout(t) dt` far out on the output end. Letting the configuration `(c, a)` move
along a family gives the one-parameter families of four-punctured spheres through which the
associativity of the pair-of-pants product is proved: the path of configurations
`τ ↦ (TauCeti.Floer.associativityCenter f τ, TauCeti.Floer.associativityScale f τ)` joins the two
compositions of the product. This file proves the interior part of Gromov–Floer compactness
for such families, over a compact window of parameters, for a symplectic vector space target
`(V, ω)`.

The configurations are smooth functions `c p`, `a p` of a parameter `p` in a real inner product
space `P`, for instance the path parameter `τ ∈ ℝ` of the associativity family. On the compact
window `C ⊆ P` they satisfy the hypotheses of the energy identity: nonzero scales, and pairwise
disjoint discs `‖w - c i‖ < ‖a i‖ / 2` contained in the disc `‖w‖ ≤ 2 exp (2π)`. A compact window
`D` of the domain avoids the centers for every `p ∈ C`.

The input is the energy identity of the family on the truncations `Σ_R`, in the namespace
`TauCeti.SmoothTwoForm`
`IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`,
read for the constant form `TauCeti.SymplecticForm.constSmooth`: for `|H i| ≤ B i` and
`|Hout| ≤ Bout`, the Floer energy over `Σ_R` differs from the *topological energy*, the symplectic
area over `Σ_R` plus `β(R - 1)` times the Hamiltonian terms of the boundary circles, by at most
`∑ i, B i + Bout`, uniformly in `R` and in the configuration. A solution whose topological energy
is at most `A` for all large `R` therefore has Floer energy at most `A + ∑ i, B i + Bout` over
`Σ_R` for all large `R`, and these truncations eventually contain `D`
(`TauCeti.ThricePuncturedSphere.eventually_subset_puncturedSphereTruncation`). For a solution on
the sphere minus its input punctures, with tame almost complex structures, this bounds the energy
over every subset of `D`
(`integrableOn_and_setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`). The data are
jointly smooth in the parameter and the domain and target points
(`TauCeti.Floer.contDiffAt_puncturedSpherePerturbation_comp`), so compactness over a compact
parameter window
(`SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`) applies.

The main result, in the namespace `TauCeti.SymplecticForm`,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere`,
gives a threshold `δ > 0` such that every sequence of solutions for parameters `pₖ ∈ C`, with
topological energies eventually at most `A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V`,
has a subsequence whose parameters converge to some `p₀ ∈ C` and which converges locally uniformly
on `Ω` off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + ∑ i, B i + Bout`. The almost
complex structures `J_p(z, x)` are any family that is jointly `C²` near `C × D × K` and tamed by
`ω`. The regularity of the limit, the bubbles at the points of `Z`, breaking along the ends and the
degeneration of the configurations at the boundary of the window are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through families of
  four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function Manifold MeasureTheory Metric Real Set Topology
open TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer Puncture

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {H : ι → ℝ → V → ℝ} {Hout : ℝ → V → ℝ}

/-- **The energy of a sphere with moving input ends over a window, for a vector space target.**
Let `K` be the datum `puncturedSpherePerturbation c a H Hout` of period-one `C¹` Hamiltonians with
`|H i| ≤ B i` and `|Hout| ≤ Bout`, read in the real coordinates of `ℂ`, for nonzero scales and
pairwise disjoint discs `‖w - c i‖ < ‖a i‖ / 2` contained in the disc `‖w‖ ≤ 2 exp (2π)`. Let `u`
be a `C¹` solution of `(du - X_K)^{0,1} = 0` for `ω`-tame structures `J z` on the sphere minus the
input punctures, whose topological energy over the truncation `Σ_R`, the symplectic area plus
`β(R - 1)` times the Hamiltonian terms of its boundary circles, is at most `A` for all large `R`.
Then on every set `Ω` contained in a compact set `D` avoiding the centers the Floer energy density
is integrable, with integral at most `A + ∑ i, B i + Bout`. -/
theorem integrableOn_and_setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le
    (ω : SymplecticForm V) {c a : ι → ℂ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ 1 (uncurry Hout)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j ↦ ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u {z | ∀ i, equivRealProdCLM.symm z ≠ c i})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z, (∀ i, equivRealProdCLM.symm z ≠ c i) → ω.Tames (J z))
    (hfl : ∀ z, (∀ i, equivRealProdCLM.symm z ≠ c i) →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x I) u z :
            ℝ × ℝ →ₗ[ℝ] V))
    {A : ℝ} (hA : ∀ᶠ R in atTop,
      (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * I))))) ≤ A)
    {D Ω : Set (ℝ × ℝ)} (hD : IsCompact D) (hDc : ∀ z ∈ D, ∀ i, equivRealProdCLM.symm z ≠ c i)
    (hΩD : Ω ⊆ D) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x I) u) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (equivRealProdCLM.symm z) x I) u z ≤
        A + (∑ i, B i + Bout) := by
  set S : Set (ℝ × ℝ) := {z | ∀ i, equivRealProdCLM.symm z ≠ c i} with hS
  have hSo : IsOpen S := by
    simp only [hS, ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) continuous_const
  have hum : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) 1 u S := contMDiffOn_iff_contDiffOn.2 hu
  have hHm (i : ι) := contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff
  have hHoutm := contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff
  -- Choose a truncation `Σ_R`, `R ≥ 1`, containing `D`, with topological energy at most `A`.
  have hDsub : ∀ᶠ R in atTop, D ⊆ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R := by
    refine (eventually_subset_puncturedSphereTruncation (hD.image
      equivRealProdCLM.symm.continuous) ?_).mono fun R hR z hz ↦ hR (mem_image_of_mem _ hz)
    rintro _ ⟨z, hz, rfl⟩ i
    exact hDc z hz i
  obtain ⟨R, hR1, hRD, hRA⟩ := ((eventually_ge_atTop (1 : ℝ)).and (hDsub.and hA)).exists
  set T := equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  have hTS : T ⊆ S := fun z hz i ↦ ne_of_mem_puncturedSphereTruncation (ha i) hz
  have hTm : MeasurableSet T := ((isCompact_puncturedSphereTruncation c a R).isClosed.preimage
    equivRealProdCLM.symm.continuous).measurableSet
  -- The energy identity on `Σ_R` for the constant form `ω`.
  have hω := isNondegenerate_constSmooth ω
  have hint := hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHm
    hHout hHoutm ha hsep hout hSo hTS hum
  have habs := hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    hH hHm hHout hHoutm ha hsep hout hB hBout hSo hTS hum hR1
  rw [funext (floerEnergyDensity_constSmooth ω _ _ u)] at hint
  simp only [floerEnergyDensity_constSmooth, eval₂_constSmooth_mfderiv_stdComplexLine] at habs
  -- The energy density is nonnegative on `Σ_R`, so the energy over `Ω ⊆ Σ_R` is at most that over
  -- `Σ_R`.
  refine ⟨hint.mono_set (hΩD.trans hRD), (setIntegral_mono_set hint
    (ae_restrict_of_forall_mem hTm fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z (hTS hz))
      (hfl z (hTS hz))) (Eventually.of_forall (hΩD.trans hRD))).trans ?_⟩
  linarith [(abs_le.1 habs).2]

/-- **Spheres with moving input ends converge off finitely many bubbling points over a compact
window of configurations.** Let the centers `c p` and the scales `a p` of the input ends depend
`C³` on a parameter `p` in a real inner product space `P`, and let `K_p` be the datum
`puncturedSpherePerturbation (c p) (a p) H Hout` of period-one `C³` Hamiltonians with
`|H i| ≤ B i` and `|Hout| ≤ Bout`, read in the real coordinates of `ℂ`. On a compact window
`C ⊆ P` let the scales be nonzero and the discs `‖w - c p i‖ < ‖a p i‖ / 2` be pairwise disjoint
and contained in the disc `‖w‖ ≤ 2 exp (2π)`. Let `J_p(z, x)` be jointly `C²` on an open set `U`
containing `C × D × K`, and tamed by `ω` away from the centers, for compact `D` avoiding the
centers and compact `K ⊆ V`. There is a threshold `δ > 0` with the following property.

Let `uₖ` be `C³` solutions of `(du - X_{K_{pₖ}})^{0,1} = 0` for `J_{pₖ}(z, u)` on the sphere
minus the input punctures, for parameters `pₖ ∈ C`, with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`, and
whose topological energy over the truncation `Σ_R`, the symplectic area plus `β(R - 1)` times the
Hamiltonian terms of its boundary circles, is at most `A` for all large `R`. Then there are a
subsequence `φ`, a limit `p₀ ∈ C` of the parameters `p_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + ∑ i, B i + Bout`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere
    (ω : SymplecticForm V) {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {c a : P → ι → ℂ} (hc : ContDiff ℝ 3 c) (ha : ContDiff ℝ 3 a)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 3 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 3 (uncurry Hout))
    {B : ι → ℝ} {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    {J : P → ℝ × ℝ → V → AlmostComplexStructure V} {U : Set (P × ((ℝ × ℝ) × V))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set V} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) U)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDK : C ×ˢ (D ×ˢ K) ⊆ U)
    (hCa : ∀ p ∈ C, ∀ i, a p i ≠ 0)
    (hCsep : ∀ p ∈ C, Pairwise fun i j ↦ ‖a p i‖ / 2 + ‖a p j‖ / 2 ≤ ‖c p i - c p j‖)
    (hCout : ∀ p ∈ C, ∀ i, ‖c p i‖ + ‖a p i‖ / 2 ≤ 2 * Real.exp (2 * π))
    (hDc : ∀ p ∈ C, ∀ z ∈ D, ∀ i, equivRealProdCLM.symm z ≠ c p i)
    (hJt : ∀ p ∈ C, ∀ z, (∀ i, equivRealProdCLM.symm z ≠ c p i) → ∀ x, ω.Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) {z | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i}) →
      (∀ k, ∀ z, (∀ i, equivRealProdCLM.symm z ≠ c (p k) i) →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x I) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, ∀ᶠ R in atTop,
        (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R,
            ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag)) +
          smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u k (equivRealProdCLM
              (c (p k) i + a (p k) i * zero.cylindricalEndLift (↑R + ↑t * I))))) -
            ∫ t in (0 : ℝ)..1, Hout t (u k (equivRealProdCLM
              (inf.cylindricalEndLift (↑(-R) + ↑t * I))))) ≤ A) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The data of the family are `C³` jointly in the parameter and the domain and target points,
  -- at nonzero scales and away from the centers.
  set W₀ : Set (P × ((ℝ × ℝ) × V)) :=
    {q | ∀ i, a q.1 i ≠ 0 ∧ equivRealProdCLM.symm q.2.1 ≠ c q.1 i} with hW₀
  have hW₀o : IsOpen W₀ := by
    simp only [hW₀, ofPred_forall, ofPred_and]
    exact isOpen_iInter_of_finite fun i ↦
      (isOpen_ne_fun ((continuous_apply i).comp (ha.continuous.comp continuous_fst))
        continuous_const).inter
      (isOpen_ne_fun (equivRealProdCLM.symm.continuous.comp (continuous_fst.comp continuous_snd))
        ((continuous_apply i).comp (hc.continuous.comp continuous_fst)))
  have hKd (v : ℂ) : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦
      puncturedSpherePerturbation (c q.1) (a q.1) H Hout (equivRealProdCLM.symm q.2.1) q.2.2 v)
      W₀ := fun q hq ↦ (contDiffAt_puncturedSpherePerturbation_comp hH hHs hHout hHouts hc ha
        (fun i ↦ (hq i).1) (fun i ↦ (hq i).2) v).contDiffWithinAt
  have hCDKW : C ×ˢ (D ×ˢ K) ⊆ U ∩ W₀ := fun q hq ↦
    ⟨hCDK hq, fun i ↦ ⟨hCa q.1 hq.1 i, hDc q.1 hq.1 q.2.1 hq.2.1 i⟩⟩
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) x 1)
    (Kt := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) x I)
    (J := J) (hU.inter hW₀o) ((hKd 1).mono inter_subset_right) ((hKd I).mono inter_subset_right)
    (hJ.mono inter_subset_left) hC hD hK hCDKW
    fun p hp z hz x _ ↦ hJt p hp z (hDc p hp z hz) x
  refine ⟨δ, hδ, fun Ω p u A hΩ hΩD hpC hu hfl huK htop ↦ ?_⟩
  -- Each solution has energy at most `A + ∑ i, B i + Bout` over `Ω`.
  have hbound (k : ℕ) :=
    integrableOn_and_setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le ω hH
    (fun i ↦ (hHs i).of_le (by norm_num)) hHout (hHouts.of_le (by norm_num)) hB hBout
    (hCa _ (hpC k)) (hCsep _ (hpC k)) (hCout _ (hpC k)) ((hu k).of_le (by norm_num))
    (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (htop k) hD (hDc _ (hpC k)) hΩD
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono fun z hz i ↦ hDc _ (hpC k) z (hΩD hz) i)
    (fun k z hz ↦ hfl k z fun i ↦ hDc _ (hpC k) z (hΩD hz) i) huK (fun k ↦ (hbound k).1)
    fun k ↦ (hbound k).2

end TauCeti.SymplecticForm
