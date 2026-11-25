/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath

/-!
# Compactness of spheres with moving input ends in a symplectic chart of a manifold

The associativity of the pair-of-pants product compares the two broken products `(a ⋆ b) ⋆ c` and
`a ⋆ (b ⋆ c)` through a family of four-punctured spheres whose three inputs sit at moving punctures
of `ℂ`. A configuration of input ends is a family of centers `c i` and nonzero scales `a i`; the
sphere carries the perturbation datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, which
is `H_i(t) dt` far out on the input end `i` and `Hout(t) dt` far out on the output end at `∞`. The
truncation `Σ_R` (`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation`) cuts the sphere along
the circle `s = R` of every end.

This file proves the interior part of Gromov–Floer compactness for this family over a compact
window of configurations, for a manifold target `M` with a nondegenerate two-form `ω`, such as a
closed symplectic manifold, on the part of the domain that the solutions map into a compact subset
of a symplectic chart, such as a Darboux chart. It is the manifold-target counterpart of the
vector-space theorems of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.MovingEnds`.

The inputs are:

* the energy bound of the family on a manifold target
  (`IsNondegenerate.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le`, in the
  namespace `TauCeti.SmoothTwoForm`): if the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint
  and lie in `‖w‖ ≤ 2 exp (2π)`, and `|H i| ≤ B i`, `|Hout| ≤ Bout`, the Floer energy of a
  solution over any part of `Σ_R` is at most its topological energy on `Σ_R` plus
  `∑ i, B i + Bout`, uniformly in the configuration;
* the smoothness of the datum in the configuration
  (`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation`): along a `C³` family of configurations
  `p ↦ (c p, a p)` with nonzero scales, the datum read in a chart is `C³` jointly in the parameter,
  the domain point off the centers and the chart point;
* compactness over a compact parameter window in a symplectic chart
  (`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`, in the
  namespace `TauCeti.SmoothTwoForm`).

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere`: for a
  `C³` family of configurations over a real inner product space of parameters, structures `J_p`
  read in the chart by a `C²` family `J'_p`, and a compact window `D` of the domain lying in the
  truncation `Σ_R` of every configuration of the parameter window, there is a threshold `δ > 0`
  such that every sequence of solutions with topological energy on `Σ_R` at most `A` and images of
  an open `Ω ⊆ D` in a compact `K ⊆ φ.source` has a subsequence with convergent parameters,
  converging off a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + ∑ i, B i + Bout`: locally uniformly in the
  chart, with locally bounded derivatives, and pointwise in `M`.
* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_associativity`: the same
  for the associativity path `τ ↦ (associativityCenter f τ, associativityScale f τ)` joining the
  two broken products, for a plumbing factor `0 < f` with `3 f ≤ 1`, along which the separation
  and nonvanishing hypotheses hold automatically.

The regularity of the limit, the bubbles at the points of `Z` and breaking along the ends are not
treated here. Solutions in a closed manifold with arbitrary images, covered by several charts, are
treated in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.MovingEnds.Closed`.

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

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V}

omit [FiniteDimensional ℝ E] [IsManifold I ⊤ M] [FiniteDimensional ℝ V] in
/-- Along a `C³` family of configurations `p ↦ (c p, a p)` of input ends on an open set `U` of
parameters, the components of the datum of the sphere with moving input ends, read in a smooth
partial diffeomorphism `φ`, are `C³` jointly in the parameter, the domain point and the chart
point, on the open set of points `(p, z, y)` with `p ∈ U`, nonzero scales, `z` off the centers and
`y` in the chart target. -/
private theorem isOpen_and_contDiffOn_puncturedSpherePerturbation {ι : Type*} [Fintype ι]
    {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {c a : P → ι → ℂ} {U : Set P} (hU : IsOpen U) (hc : ContDiffOn ℝ 3 c U)
    (ha : ContDiffOn ℝ 3 a U) :
    IsOpen {q : P × ((ℝ × ℝ) × V) | q.1 ∈ U ∧ (∀ i, a q.1 i ≠ 0) ∧
      (∀ i, equivRealProdCLM.symm q.2.1 ≠ c q.1 i) ∧ q.2.2 ∈ φ.target} ∧
    ∀ w : ℂ, ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ puncturedSpherePerturbation (c q.1)
      (a q.1) H Hout (equivRealProdCLM.symm q.2.1) (φ.symm q.2.2) w)
      {q | q.1 ∈ U ∧ (∀ i, a q.1 i ≠ 0) ∧ (∀ i, equivRealProdCLM.symm q.2.1 ≠ c q.1 i) ∧
        q.2.2 ∈ φ.target} := by
  obtain ⟨hSo, hS⟩ :=
    isOpen_and_contMDiffAt_puncturedSpherePerturbation (n := 3) hH hHs hHout hHouts hU hc ha
  set S := {q : P × ((ℝ × ℝ) × V) | q.1 ∈ U ∧ (∀ i, a q.1 i ≠ 0) ∧
    (∀ i, equivRealProdCLM.symm q.2.1 ≠ c q.1 i) ∧ q.2.2 ∈ φ.target}
  -- The point `(p, z)` of the family and the point of `M` with chart coordinate `y`.
  set g : P × ((ℝ × ℝ) × V) → (P × (ℝ × ℝ)) × M := fun q ↦ ((q.1, q.2.1), φ.symm q.2.2)
  have hSo' : IsOpen S := by
    have hp : Continuous fun q : P × ((ℝ × ℝ) × V) ↦ (q.1, q.2.1) := by fun_prop
    convert (hSo.preimage hp).inter
      (φ.open_target.preimage (f := fun q : P × ((ℝ × ℝ) × V) ↦ q.2.2) (by fun_prop)) using 1
    ext q
    simp [S, and_assoc]
  refine ⟨hSo', fun w ↦ contMDiffOn_iff_contDiffOn.1 fun q hq ↦ ?_⟩
  have hg : ContMDiffAt 𝓘(ℝ, P × ((ℝ × ℝ) × V)) (𝓘(ℝ, P × (ℝ × ℝ)).prod I) 3 g q :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contMDiff.contMDiffAt.prodMk
      (((φ.symm.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).contMDiffAt
        (φ.open_target.mem_nhds hq.2.2.2)).comp q
        (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffAt)
  exact ((hS w _ ⟨hq.1, hq.2.1, hq.2.2.1⟩ (φ.symm q.2.2)).comp q hg).contMDiffWithinAt

variable {ι : Type*} [Fintype ι] {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- **Solutions on spheres with moving input ends in a symplectic chart of a manifold converge off
finitely many bubbling points, uniformly over a compact window of configurations.** Let `ω` be a
nondegenerate two-form on `M`, let `H i` and `Hout` be period-one `C³` Hamiltonians with
`|H i| ≤ B i` and `|Hout| ≤ Bout`, and let `p ↦ (c p, a p)` be a `C³` family of configurations of
input ends on an open set `U` of a real inner product space. Fix a compact window `C ⊆ U` of
parameters at which the scales are nonzero, the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in `‖w‖ ≤ 2 exp (2π)`, a cutoff `R ≥ 1` and a compact window `D` of the domain
lying in the truncation `Σ_R` of every configuration of `C`. Let `φ` be a smooth partial
diffeomorphism from `M` onto an open subset of `V` pulling the symplectic form `ω₀` back to `ω` on
a compact set `K ⊆ φ.source`, let the structures `J_p(z, x)` be tamed by `ω` on `Σ_R`, and let
`J'_p` be `J_p` read in the chart, `dφ_x ∘ J_p(z, x) = J'_p(z, φ x) ∘ dφ_x` for `p ∈ C`, `z ∈ D`
and `x ∈ K`, `C²` jointly in `(p, z, y)` on an open set `W` containing `C × D × φ(K)`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps from the sphere minus the
centers of the configuration `pₖ ∈ C` into `M` solving the Floer equation for the datum of `pₖ`
and the structures `J_{pₖ}` on `Σ_R`, with topological energy on `Σ_R` at most `A` and `uₖ(Ω) ⊆ K`
for an open `Ω ⊆ D`. Then there are a subsequence `ψ`, a limit `p₀ ∈ C` of `p_{ψ n}`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + (∑ i, B i + Bout)`, and a map `v`, continuous on `Ω \ Z` with values in
`K`, such that along `ψ` every disc about a point of `Z` eventually carries Floer energy at least
`δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded on every
compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally uniformly on `Ω \ Z`,
and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] {c a : P → ι → ℂ} {U : Set P}
    (hU : IsOpen U) (hc : ContDiffOn ℝ 3 c U) (ha : ContDiffOn ℝ 3 a U) {C : Set P}
    (hC : IsCompact C) (hCU : C ⊆ U) (ha₀ : ∀ p ∈ C, ∀ i, a p i ≠ 0)
    (hsep : ∀ p ∈ C, Pairwise fun i j => ‖a p i‖ / 2 + ‖a p j‖ / 2 ≤ ‖c p i - c p j‖)
    (hout : ∀ p ∈ C, ∀ i, ‖c p i‖ + ‖a p i‖ / 2 ≤ 2 * Real.exp (2 * π)) {R : ℝ} (hR : 1 ≤ R)
    {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDT : ∀ p ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : P → ℝ × ℝ → V → AlmostComplexStructure V} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJt : ∀ p ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation (c p) (a p) R,
      ∀ x, (hω.symplecticFormAt x).Tames (J p z x))
    (hJJ' : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K,
      IsComplexLinearMap (J p z x) (J' p z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (P × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hK : IsCompact K) (hKφ : K ⊆ φ.source) (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W) :
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
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (ψ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (c (p (ψ n))) (a (p (ψ n))) H Hout
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (c (p (ψ n))) (a (p (ψ n))) H Hout
            (equivRealProdCLM.symm z) x Complex.I) (u (ψ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  obtain ⟨hSo, hK'⟩ :=
    isOpen_and_contDiffOn_puncturedSpherePerturbation hH hHs hHout hHouts φ hU hc ha
  -- The parameter window, the domain window and the chart image of `K` lie in the open set where
  -- the coordinate Hamiltonians are `C³`.
  have hCDKS : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W ∩ {q : P × ((ℝ × ℝ) × V) | q.1 ∈ U ∧
      (∀ i, a q.1 i ≠ 0) ∧ (∀ i, equivRealProdCLM.symm q.2.1 ≠ c q.1 i) ∧ q.2.2 ∈ φ.target} := by
    rintro q ⟨hq, hz, x, hx, hxq⟩
    exact ⟨hCDKW ⟨hq, hz, x, hx, hxq⟩, hCU hq, ha₀ _ hq,
      fun i ↦ ne_of_mem_puncturedSphereTruncation (ha₀ _ hq i) (hDT _ hq hz),
      hxq ▸ φ.toPartialEquiv.map_source (hKφ hx)⟩
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z)
      x 1)
    (Kt := fun p z x ↦ puncturedSpherePerturbation (c p) (a p) H Hout (equivRealProdCLM.symm z)
      x Complex.I) hφ hJJ' (hW.inter hSo) ((hK' 1).mono inter_subset_right)
    ((hK' Complex.I).mono inter_subset_right) (hJ'.mono inter_subset_left) hC hD hK hKφ hCDKS
    fun p hp z hz x _ ↦ hJt p hp z (hDT p hp hz) x
  refine ⟨δ, hδ, fun Ω p u A hΩ hΩD hpC hu hfl hA huK ↦ ?_⟩
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
  have hE (k : ℕ) := (hω.setIntegral_floerEnergyDensity_puncturedSpherePerturbation_le hH hHs₁
    hHout hHouts₁ (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) hB hBout (hVo k) (hTV k)
    (hu₁ k) hR (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (hΩT k)).trans
    (add_le_add (hA k) le_rfl)
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono ((hΩT k).trans (hTV k)))
    (fun k z hz ↦ hfl k z (hΩT k hz)) huK
    (fun k ↦ (hω.integrableOn_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs₁
      hHout hHouts₁ (ha₀ _ (hpC k)) (hsep _ (hpC k)) (hout _ (hpC k)) (hVo k) (hTV k)
      (hu₁ k)).mono_set (hΩT k)) hE

/-- **Solutions along the associativity path in a symplectic chart of a manifold converge off
finitely many bubbling points.** For a plumbing factor `0 < f` with `3 f ≤ 1`, the configurations
`τ ↦ (associativityCenter f τ, associativityScale f τ)` of the three input ends join the two
broken products `(a ⋆ b) ⋆ c` (for `τ ≤ 0`) and `a ⋆ (b ⋆ c)` (for `τ ≥ 1`). Over a compact
window `C ⊆ ℝ` of parameters, with a compact window `D` of the domain lying in the truncation
`Σ_R`, `R ≥ 1`, of every configuration of `C`, solutions of bounded topological energy on `Σ_R`
whose images of an open `Ω ⊆ D` lie in a compact subset `K` of a symplectic chart have a
subsequence converging off finitely many bubbling points, as in
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_associativity
    (hω : ω.IsNondegenerate) {H : Fin 3 → ℝ → M → ℝ} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) {B : Fin 3 → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {f : ℝ} (hf : 0 < f)
    (hf₃ : 3 * f ≤ 1) {C : Set ℝ} (hC : IsCompact C) {R : ℝ} (hR : 1 ≤ R) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D)
    (hDT : ∀ τ ∈ C, D ⊆ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJt : ∀ τ ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹'
      puncturedSphereTruncation (associativityCenter f τ) (associativityScale f τ) R,
      ∀ x, (hω.symplecticFormAt x).Tames (J τ z x))
    (hJJ' : ∀ τ ∈ C, ∀ z ∈ D, ∀ x ∈ K,
      IsComplexLinearMap (J τ z x) (J' τ z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (ℝ × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : ℝ × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hK : IsCompact K) (hKφ : K ⊆ φ.source) (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W) :
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
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (τ₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ τ₀ ∈ C ∧
        Tendsto (fun n ↦ τ (ψ n)) atTop (𝓝 τ₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + (∑ i, B i + Bout) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (ψ n)))
            (associativityScale f (τ (ψ n))) H Hout (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation (associativityCenter f (τ (ψ n)))
            (associativityScale f (τ (ψ n))) H Hout (equivRealProdCLM.symm z) x Complex.I)
          (u (ψ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) :=
  hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_puncturedSphere hH hHs
    hHout hHouts hB hBout isOpen_univ (contDiff_associativityCenter f).contDiffOn
    (contDiff_associativityScale f).contDiffOn hC (subset_univ C)
    (fun τ _ ↦ associativityScale_ne_zero hf τ)
    (fun τ _ ↦ pairwise_add_le_norm_associativityCenter_sub hf.le hf₃ τ)
    (fun τ _ ↦ norm_associativityCenter_add_le hf.le (by linarith) τ) hR hD hDT φ hφ hJt hJJ' hW hJ'
    hK hKφ hCDKW

end TauCeti.SmoothTwoForm.IsNondegenerate
