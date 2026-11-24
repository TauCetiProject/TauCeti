/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath

/-!
# Compactness of spheres with moving input ends in a closed manifold

The associativity of the pair-of-pants product compares the two broken products `(a ⋆ b) ⋆ c` and
`a ⋆ (b ⋆ c)` through a family of four-punctured spheres whose three inputs sit at moving punctures
of `ℂ`. A configuration of input ends is a family of centers `c i` and nonzero scales `a i`; the
sphere carries the perturbation datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, which
is `H_i(t) dt` far out on the input end `i` and `Hout(t) dt` far out on the output end at `∞`. The
truncation `Σ_R` (`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation`) cuts the sphere along
the circle `s = R` of every end.

Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic
manifold. This file proves the interior part of Gromov–Floer compactness for this family over a
compact window of configurations, on every compact window of the domain lying in the truncations,
with no condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.MovingEnds.Manifold` assume instead that
the images stay in a compact subset of one symplectic chart.

The general compactness theorem in a closed manifold over a compact parameter window,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** Along a `C³` family of configurations `p ↦ (c p, a p)` on an
  open set `U` of parameters, the datum is `C³` jointly in the parameter, the domain point off the
  centers and the target point (`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation`), on an
  open set of `(p, z)` containing every compact window of the domain lying in the truncations of a
  compact window of configurations. So for `C³` Hamiltonians the Hamiltonian vector fields of its
  two components, read in the chart at any point of `M`, are `C²` there
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`). The almost
  complex structures read in the charts are assumed `C²` in `(p, z, y)`.
* **The energy bound.** If the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in
  `‖w‖ ≤ 2 exp (2π)`, and `|H i| ≤ B i`, `|Hout| ≤ Bout`, the Floer energy of a solution over any
  part of `Σ_R` is at most its topological energy on `Σ_R` plus `∑ i, B i + Bout`, uniformly in
  the configuration (`IsNondegenerate.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`
  in the namespace `TauCeti.SmoothTwoForm`).

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_puncturedSphere`:
  for a `C³` family of configurations over a finite-dimensional normed space of parameters and a
  compact window `D` of the domain lying in the truncation `Σ_R` of every configuration of the
  parameter window, there is a threshold `δ > 0` such that every sequence of solutions with
  topological energy on `Σ_R` at most `A` has a subsequence with convergent parameters, converging
  off a finite set `Z` of bubbling points with `#Z * δ ≤ A + ∑ i, B i + Bout`.
* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_associativity`: the
  same for the associativity path `τ ↦ (associativityCenter f τ, associativityScale f τ)` joining
  the two broken products, for a plumbing factor `0 < f` with `3 f ≤ 1`, along which the separation
  and nonvanishing hypotheses hold automatically.

The regularity of the limit, the bubbles at the points of `Z` and breaking along the ends are not
treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through the family of
  four-punctured spheres between its two degenerations.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold Real

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {e : M → F}
  {ι : Type*} [Fintype ι] {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

omit [Fintype ι] in
/-- For a family of configurations `p ↦ (c p, a p)` of input ends, continuous on an open set `U`
of parameters, the points `(p, z)` with `p ∈ U`, nonzero scales and the domain point `z` (in real
coordinates) off the centers form an open set. -/
private theorem isOpen_setOf_mem_and_forall_ne_zero_and_forall_ne [Finite ι] {P : Type*}
    [TopologicalSpace P] {c a : P → ι → ℂ} {U : Set P} (hU : IsOpen U) (hc : ContinuousOn c U)
    (ha : ContinuousOn a U) :
    IsOpen {q : P × (ℝ × ℝ) | q.1 ∈ U ∧ (∀ i, a q.1 i ≠ 0) ∧
      ∀ i, equivRealProdCLM.symm q.2 ≠ c q.1 i} := by
  -- The conditions are open conditions on `((c p, a p), z)`, which is continuous on `U × ℝ²`.
  have hO : IsOpen {r : ((ι → ℂ) × (ι → ℂ)) × ℂ | (∀ i, r.1.2 i ≠ 0) ∧ ∀ i, r.2 ≠ r.1.1 i} := by
    simp only [ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) continuous_const).inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) (by fun_prop))
  have hcont : ContinuousOn
      (fun q : P × (ℝ × ℝ) ↦ ((c q.1, a q.1), equivRealProdCLM.symm q.2)) (U ×ˢ univ) :=
    ((hc.comp continuousOn_fst mapsTo_fst_prod).prodMk
      (ha.comp continuousOn_fst mapsTo_fst_prod)).prodMk
      (by fun_prop : Continuous fun q : P × (ℝ × ℝ) ↦ equivRealProdCLM.symm q.2).continuousOn
  convert hcont.isOpen_inter_preimage (hU.prod isOpen_univ) hO using 1
  ext q
  simp

/-- **Solutions on spheres with moving input ends in a closed manifold converge off finitely many
bubbling points, uniformly over a compact window of configurations.** Let `ω` be a nondegenerate
two-form on a closed manifold `M`, let `H i` and `Hout` be period-one `C³` Hamiltonians with
`|H i| ≤ B i` and `|Hout| ≤ Bout`, and let `p ↦ (c p, a p)` be a `C³` family of configurations of
input ends on an open set `U` of a finite-dimensional real normed space. Fix a compact window
`C ⊆ U` of parameters at which the scales are nonzero, the discs `‖w - c i‖ < ‖a i‖ / 2` are
pairwise disjoint and lie in `‖w‖ ≤ 2 exp (2π)`, a cutoff `R ≥ 1` and a compact window `D` of the
domain lying in the truncation `Σ_R` of every configuration of `C`. Let the structures `J_p(z, x)`
on the tangent spaces of `M` be tamed by `ω` on `Σ_R` for `p ∈ C`, and, read in the chart at every
point of `M`, be `C²` jointly in `(p, z, y)` on an open set `W` containing `C × D`. Let `e : M → F`
be injective and differentiable, and for `p ∈ C` and `z ∈ D` let the structures be uniformly tame
with respect to `e`, `κ ‖d e v‖² ≤ ω(v, J_p v)` with `κ > 0`, and the pushforwards through `e` of
the Hamiltonian vector fields of the two components of the datum be at most `L`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps from the sphere minus the
centers of the configuration `pₖ ∈ C` into `M` solving the Floer equation for the datum of `pₖ`
and the structures `J_{pₖ}` on `Σ_R`, with topological energy on `Σ_R` at most `A`, and let
`Ω ⊆ D` be open. Then there are a subsequence `φ`, a limit `p₀ ∈ C` of `p_{φ n}`, and a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + (∑ i, B i + Bout)` such that, along `φ`, every disc about a point of
`Z` eventually carries energy at least `δ`, the energy densities are uniformly bounded on every
compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`, locally
uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_puncturedSphere
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {c a : P → ι → ℂ}
    {U : Set P} (hU : IsOpen U) (hc : ContDiffOn ℝ 3 c U) (ha : ContDiffOn ℝ 3 a U) {C : Set P}
    (hC : IsCompact C) (hCU : C ⊆ U) (ha₀ : ∀ p ∈ C, ∀ i, a p i ≠ 0)
    (hsep : ∀ p ∈ C, Pairwise fun i j => ‖a p i‖ / 2 + ‖a p j‖ / 2 ≤ ‖c p i - c p j‖)
    (hout : ∀ p ∈ C, ∀ i, ‖c p i‖ + ‖a p i‖ / 2 ≤ 2 * Real.exp (2 * π)) {R : ℝ} (hR : 1 ≤ R)
    {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDT : ∀ p ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} (hW : IsOpen W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hCDW : C ×ˢ D ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R,
      ∀ x, (hω.symplecticFormAt x).Tames (J p z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJκ : ∀ p ∈ C, ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J p z x v))
    (hLs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) y 1) x)‖ ≤
        L)
    (hLt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) y
        Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k)
        {z | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i}) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation (c (p k)) (a (p k)) H Hout
              (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      (∀ k, (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R,
          (SmoothBundleForm.eval₂ ω (u k z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        Real.smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u k (equivRealProdCLM
            (c (p k) i + a (p k) i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u k (equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ C, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (c (p (φ n))) (a (p (φ n))) H Hout
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- The points `(p, z)` with `p ∈ U`, nonzero scales and `z` off the centers form an open set,
  -- on which the components of the datum are `C³` jointly with the target point.
  set S := {q : P × (ℝ × ℝ) | q.1 ∈ U ∧ (∀ i, a q.1 i ≠ 0) ∧
    ∀ i, equivRealProdCLM.symm q.2 ≠ c q.1 i}
  have hSo : IsOpen S := isOpen_setOf_mem_and_forall_ne_zero_and_forall_ne hU hc.continuousOn
    ha.continuousOn
  have hK (w : ℂ) (q : P × (ℝ × ℝ)) (hq : q ∈ S) (x : M) :
      ContMDiffAt (𝓘(ℝ, P × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry (uncurry fun p z x ↦
          puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z) x w)) (q, x) :=
    contMDiffAt_uncurry_uncurry_puncturedSpherePerturbation hH hHs hHout hHouts
      (hc.contDiffAt (hU.mem_nhds hq.1)) (ha.contDiffAt (hU.mem_nhds hq.1)) hq.2.1 hq.2.2 x w
  -- The parameter window and the domain window lie in the open set where the data are `C³`.
  have hCDS : C ×ˢ D ⊆ W ∩ S := fun q hq ↦ ⟨hCDW hq, hCU hq.1, ha₀ _ hq.1,
    fun i ↦ ne_of_mem_puncturedSphereTruncation (ha₀ _ hq.1 i) (hDT _ hq.1 hq.2)⟩
  have hsub (α : M) : (W ∩ S) ×ˢ (extChartAt I α).target ⊆ S ×ˢ (extChartAt I α).target :=
    prod_mono inter_subset_right subset_rfl
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z)
        x 1)
      (Kt := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z)
        x Complex.I)
      he he_inj (hW.inter hSo) hC hD hCDS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono (hsub α))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono (hsub α))
      (fun p hp z hz x ↦ hJt p hp z (hDT p hp hz) x) hκ hJκ hLs hLt
  refine ⟨δ, hδ, fun Ω p u A hΩ hΩD hpC hu hfl hA ↦ ?_⟩
  have hHs₁ (i : ι) := (hHs i).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hHouts₁ := hHouts.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  -- The sphere minus the centers of `pₖ` is an open set containing `Σ_R`, on which `uₖ` is `C¹`.
  have hVo (k : ℕ) : IsOpen {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) continuous_const
  have hTV (k : ℕ) : equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c (p k)) (a (p k)) R ⊆
      {z | ∀ i, equivRealProdCLM.symm z ≠ c (p k) i} := fun z hz i ↦
    ne_of_mem_puncturedSphereTruncation (ha₀ _ (hpC k) i) hz
  have hu₁ (k : ℕ) := (hu k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hΩT (k : ℕ) := hΩD.trans (hDT _ (hpC k))
  -- The energy over `Ω` is at most the topological energy on `Σ_R` plus `∑ i, B i + Bout`.
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono ((hΩT k).trans (hTV k)))
    (fun k z hz ↦ hfl k z (hΩT k hz))
    (fun k ↦ (hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs₁
      hHout hHouts₁ (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) (hVo k) (hTV k)
      (hu₁ k)).mono_set (hΩT k))
    fun k ↦ (hω.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le hH hHs₁ hHout
      hHouts₁ (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) hB hBout (hVo k) (hTV k) (hu₁ k) hR
      (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (hΩT k)).trans (add_le_add (hA k) le_rfl)

/-- **Solutions along the associativity path in a closed manifold converge off finitely many
bubbling points.** For a plumbing factor `0 < f` with `3 f ≤ 1`, the configurations
`τ ↦ (associativityCenter f τ, associativityScale f τ)` of the three input ends join the two
broken products `(a ⋆ b) ⋆ c` (for `τ ≤ 0`) and `a ⋆ (b ⋆ c)` (for `τ ≥ 1`). Over a compact
window `C ⊆ ℝ` of parameters, with a compact window `D` of the domain lying in the truncation
`Σ_R`, `R ≥ 1`, of every configuration of `C`, solutions in a closed manifold of bounded
topological energy on `Σ_R` have a subsequence with convergent parameters converging off finitely
many bubbling points, as in
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_puncturedSphere`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_associativity
    (hω : ω.IsNondegenerate) {H : Fin 3 → ℝ → M → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) {B : Fin 3 → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {f : ℝ} (hf : 0 < f)
    (hf₃ : 3 * f ≤ 1) {C : Set ℝ} (hC : IsCompact C) {R : ℝ} (hR : 1 ≤ R) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D)
    (hDT : ∀ τ ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} (hW : IsOpen W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hCDW : C ×ˢ D ⊆ W)
    (hJt : ∀ τ ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R,
      ∀ x, (hω.symplecticFormAt x).Tames (J τ z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJκ : ∀ τ ∈ C, ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J τ z x v))
    (hLs : ∀ τ ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ puncturedSpherePerturbation (associativityCenter f τ) (associativityScale f τ) H
        Hout (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ τ ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ puncturedSpherePerturbation (associativityCenter f τ) (associativityScale f τ) H
        Hout (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃τ : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, τ k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k)
        {z | ∀ i, equivRealProdCLM.symm z ≠ associativityCenter f (τ k) i}) →
      (∀ k, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
          (associativityCenter f (τ k)) (associativityScale f (τ k)) R,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (τ k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ k))
              (associativityScale f (τ k)) H Hout (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ k))
              (associativityScale f (τ k)) H Hout (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, (∫ z in equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
            (associativityCenter f (τ k)) (associativityScale f (τ k)) R,
          (SmoothBundleForm.eval₂ ω (u k z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        Real.smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u k (equivRealProdCLM
            (associativityCenter f (τ k) i + associativityScale f (τ k) i *
              zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u k (equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ τ₀ ∈ C, Tendsto (fun n ↦ τ (φ n)) atTop (𝓝 τ₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (φ n)))
            (associativityScale f (τ (φ n))) H Hout (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) :=
  hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_puncturedSphere hH
    hHs hHout hHouts hB hBout isOpen_univ (contDiff_associativityCenter f).contDiffOn
    (contDiff_associativityScale f).contDiffOn hC (subset_univ C)
    (fun τ _ ↦ associativityScale_ne_zero hf τ)
    (fun τ _ ↦ pairwise_add_le_norm_associativityCenter_sub hf.le hf₃ τ)
    (fun τ _ ↦ norm_associativityCenter_add_le hf.le (by linarith) τ) hR hD hDT hW hJ hCDW hJt he
    he_inj hκ hJκ hLs hLt

end TauCeti.SmoothTwoForm.IsNondegenerate
