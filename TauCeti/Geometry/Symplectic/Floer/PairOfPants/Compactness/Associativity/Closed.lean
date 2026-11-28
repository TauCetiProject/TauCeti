/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Associativity
import TauCeti.Topology.Separation.Basic

/-!
# Compactness of the associativity family in a closed manifold

The associativity of the pair-of-pants product on homology compares the two compositions
`(x₁ x₂) x₃` and `x₁ (x₂ x₃)` through the one-parameter family of Floer data
`K_τ = TauCeti.Floer.associativityPerturbation H Hout G G' L τ`, `τ ∈ ℝ`, on spheres with three
moving input ends: for `τ ≤ -1` it is the plumbed four-punctured sphere of `(x₁ x₂) x₃`, for
`τ ≥ 2` that of `x₁ (x₂ x₃)`; on `[-1, 0]` and `[1, 2]` the neck Hamiltonians `G`, `G'` are
turned off by the cutoffs `β(-τ)`, `β(τ - 1)`, where `β = Real.smoothTransition`, and on `[0, 1]`
the input ends move along the associativity path with no neck terms. The counts of this family
give the homotopy between the two compositions, and they are finite below each energy level only
if its moduli spaces are compact up to bubbling and breaking.

This file proves the interior part of Gromov–Floer compactness for this family in a closed
manifold `M`, for a fixed neck length `L > 4`, uniformly over a compact window `C` of parameters
`τ`, with no condition on where the solutions take their values. It is an application of the
compactness theorem over a compact parameter window in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
whose hypotheses are checked for the family as follows.

* **The data in the charts of `M`.** For `L > 4` the family is smooth jointly in `τ`, the domain
  point off the three input punctures of the configuration at `τ`, and the target point
  (`TauCeti.Floer.contMDiffAt_associativityPerturbation`). So its two components, read in the
  real coordinates `z = s + i t` of the domain, have Hamiltonian vector fields which are `C²` in
  `(τ, z, y)` in the chart at any point of `M`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`).
* **The energy bound.** Let `uₖ` solve the Floer equation on the whole sphere minus its punctures,
  for the member `K_{τₖ}` and structures tamed by `ω`, with asymptotic loops `xₖ i` along the input
  ends and `xoutₖ` along the output end. Its energy density is nonnegative, so its energy over
  any part of the sphere is at most its total energy, and by the energy identity of the family
  (`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le`)
  this is at most its topological energy
  `∫ uₖ^*ω + ∑ i, ∫₀¹ H_i(t, xₖ i t) dt - ∫₀¹ Hout(t, xoutₖ t) dt` plus
  `∑ i, B i + Bout + 2 (BG + BG')`, for bounds `|H i| ≤ B i`, `|Hout| ≤ Bout`, `|G| ≤ BG` and
  `|G'| ≤ BG'`, whatever `τ`. When `ω` is closed (for instance symplectic), the topological
  energy is fixed for solutions in a fixed class between fixed capped orbits; this file assumes
  only that `ω` is nondegenerate.

The almost complex structures `J_τ(z, x)` are any family tamed by `ω` on the sphere minus the
punctures of the configuration at `τ` which, read in the charts of `M`, is `C²` jointly in
`(τ, z, y)` near the parameter and domain windows, such as the structures
`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex` of the associativity path
(`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_puncturedSphereAlmostComplex_associativity`). As in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

The regularity of the limit, the bubbles at the bubbling points, the breaking of Floer cylinders
along the ends and the necks, and the long-neck end `L → ∞` are not treated here.

## Main results

* `…_off_finset_associativityPerturbation`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`, the case of the associativity family of
  `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset`: there is a
  threshold `δ > 0` such that every sequence of solutions along the associativity family, for
  parameters in a compact window `C`, with topological energy at most `A`, has a subsequence
  whose parameters converge in `C` and which converges on an open `Ω` of a compact window `D` of
  the domain off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + (∑ i, B i + Bout + 2 (BG + BG'))`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through the family of
  four-punctured spheres between its two degenerations.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Bundle Complex Filter Function MeasureTheory Metric Set Topology
  TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold Real

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E E' M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace E'] {I : ModelWithCorners ℝ E E'} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace E' M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Fin 3 → ℝ → M → ℝ} {Hout G G' : ℝ → M → ℝ}
  {L : ℝ} {e : M → F}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ⊤ M] [CompactSpace M] in
/-- For `L > 4`, a component of the associativity family, read in the real coordinates of the
domain, is `C³` jointly in the parameter `τ`, the domain point off the input punctures of the
configuration at `τ` and the target point. -/
private theorem contMDiffAt_associativityPerturbation_apply (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry G)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry G')) (hL : 4 < L) (v : ℂ)
    {q : ℝ × (ℝ × ℝ)}
    (hq : ∀ i, equivRealProdCLM.symm q.2 ≠ associativityCenter (Real.exp (-(2 * π * L)) / 4) q.1 i)
    (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) 𝓘(ℝ) 3
      (uncurry fun (q : ℝ × (ℝ × ℝ)) x ↦
        associativityPerturbation H Hout G G' L q.1 (equivRealProdCLM.symm q.2) x v)
      (q, x) := by
  -- The coordinates `((τ, z), x) ↦ ((L, τ), (z, x))` of the family are smooth.
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 3
      (fun p : (ℝ × (ℝ × ℝ)) × M ↦ ((L, p.1.1), (equivRealProdCLM.symm p.1.2, p.2))) (q, x) :=
    (contMDiffAt_const.prodMk_space
      (contDiff_fst.contMDiff.contMDiffAt.comp _ contMDiffAt_fst)).prodMk
      ((equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _
        (contDiff_snd.contMDiff.contMDiffAt.comp _ contMDiffAt_fst)).prodMk contMDiffAt_snd)
  exact ((contMDiffAt_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's hL hq x).comp
    (q, x) hφ).clm_apply contMDiffAt_const

/-- **Solutions along the associativity family in a closed manifold converge off finitely many
bubbling points, uniformly over a compact window of parameters.** Let `ω` be a nondegenerate
two-form on a closed manifold `M`, let `H i`, `Hout`, `G` and `G'` be period-one `C³` Hamiltonians
with `|H i| ≤ B i`, `|Hout| ≤ Bout`, `|G| ≤ BG` and `|G'| ≤ BG'`, and let `L > 4`. Fix a compact
window `C` of parameters `τ` and a compact window `D` of the domain containing none of the input
punctures of the configurations at the parameters of `C`. Let the structures `J_τ(z, x)` on the
tangent spaces of `M` be tamed by `ω` off the punctures, for `τ ∈ C`, and read in the chart at
every point of `M` be `C²` jointly in `(τ, z, y)` on `W × (chart target)` for an open `W`
containing `C × D`. Let `e : M → F` be injective and differentiable, with the structures uniformly
tame with respect to `e` over `C × D`, `κ ‖d e v‖² ≤ ω(v, J_τ(z) v)` with `κ > 0`, and the
pushforwards through `e` of the Hamiltonian vector fields of the two components of the datum at
most `b` there. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps
from the sphere minus the punctures of the configuration at `τₖ ∈ C` into `M` solving the Floer
equation for `K_{τₖ}` and `J_{τₖ}` there, with integrable energy and area densities, whose loops
along the input ends converge pointwise to loops `xₖ i` and along the output end to a loop
`xoutₖ`, and whose topological energy
`∫ uₖ^*ω + ∑ i, ∫₀¹ H_i(t, xₖ i t) dt - ∫₀¹ Hout(t, xoutₖ t) dt` is at most `A`. Let `Ω ⊆ D` be
open. Then there are a subsequence `φ`, a limit `τ₀ ∈ C` of the parameters `τ_{φ n}` and a finite
set `Z ⊆ Ω` with `#Z * δ ≤ A + (∑ i, B i + Bout + 2 (BG + BG'))` such that, along `φ`, every disc
about a point of `Z` eventually carries energy at least `δ`, the energy densities are uniformly
bounded on every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous
map `v`, locally uniformly after applying `e` and pointwise in `M`. -/
theorem
exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_associativityPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry G)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry G')) {B : Fin 3 → ℝ}
    {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (hBG : ∀ t x, |G t x| ≤ BG) (hBG' : ∀ t x, |G' t x| ≤ BG') (hL : 4 < L) {C : Set ℝ}
    (hC : IsCompact C) {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDc : ∀ τ ∈ C, ∀ z ∈ D, ∀ i,
      equivRealProdCLM.symm z ≠ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} (hW : IsOpen W) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ τ ∈ C, ∀ z ∈ {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
      ∀ x, (hω.symplecticFormAt x).Tames (J τ z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ b : ℝ} (hκ : 0 < κ)
    (hJc : ∀ τ ∈ C, ∀ z ∈ D, ∀ x v,
      κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J τ z x v))
    (hbs : ∀ τ ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ associativityPerturbation H Hout G G' L τ (equivRealProdCLM.symm z) y 1) x)‖ ≤ b)
    (hbt : ∀ τ ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ associativityPerturbation H Hout G G' L τ (equivRealProdCLM.symm z) y
        Complex.I) x)‖ ≤ b) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃τ : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Fin 3 → ℝ → M⦄
      ⦃xout : ℕ → ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, τ k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i}) →
      (∀ k, ∀ z ∈ {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i},
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (τ k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x
              Complex.I) (u k) z).toLinearMap) →
      (∀ k i (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i +
          associativityScale (Real.exp (-(2 * π * L)) / 4) (τ k) i *
            zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x k i t))) →
      (∀ k (t : ℝ), Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout k t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x
            Complex.I) (u k))
        {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i}) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ))
        {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i}) →
      (∀ k, (∫ z in {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
            associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i},
          (SmoothBundleForm.eval₂ ω (u k z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x k i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout k t)) ≤
        A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ τ₀ ∈ C, Tendsto (fun n ↦ τ (φ n)) atTop (𝓝 τ₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + (∑ i, B i + Bout + 2 * (BG + BG')) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ (φ n)) (equivRealProdCLM.symm z)
            x 1)
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ (φ n)) (equivRealProdCLM.symm z)
            x Complex.I) (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ (φ n)) (equivRealProdCLM.symm z)
            x 1)
          (fun z x ↦ associativityPerturbation H Hout G G' L (τ (φ n)) (equivRealProdCLM.symm z)
            x Complex.I) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- The parameters and the domain points off the input punctures form an open set.
  set S := {q : ℝ × (ℝ × ℝ) | ∀ i, equivRealProdCLM.symm q.2 ≠
    associativityCenter (Real.exp (-(2 * π * L)) / 4) q.1 i}
  have hSo : IsOpen S := by
    simp only [S, ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop)
      ((continuous_apply i).comp
        ((contDiff_associativityCenter (n := 0) _).continuous.comp continuous_fst))
  have hCDS : C ×ˢ D ⊆ W ∩ S := fun q hq ↦ ⟨hCDW hq, hDc _ hq.1 _ hq.2⟩
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun τ z x ↦ associativityPerturbation H Hout G G' L τ (equivRealProdCLM.symm z) x 1)
      (Kt := fun τ z x ↦
        associativityPerturbation H Hout G G' L τ (equivRealProdCLM.symm z) x Complex.I)
      he he_inj (hW.inter hSo) hC hD hCDS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2)
        (fun q hq x ↦ contMDiffAt_associativityPerturbation_apply hH hHs hHout hHouts hG hGs hG'
          hG's hL 1 hq x) α).mono (prod_mono inter_subset_right subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2)
        (fun q hq x ↦ contMDiffAt_associativityPerturbation_apply hH hHs hHout hHouts hG hGs hG'
          hG's hL Complex.I hq x) α).mono (prod_mono inter_subset_right subset_rfl))
      (fun τ hτ z hz ↦ hJt τ hτ z (hDc τ hτ z hz)) hκ hJc hbs hbt
  refine ⟨δ, hδ, fun Ω τ u x xout A hΩ hΩD hτC hu hfl hx hxout hE hA hAtop ↦ ?_⟩
  have hΩS (k : ℕ) : Ω ⊆ {z : ℝ × ℝ | ∀ i, equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k) i} :=
    fun z hz ↦ hDc _ (hτC k) z (hΩD hz)
  -- Over `Ω` the energy is at most the total energy, which is at most the topological energy
  -- plus the curvature bound of the family.
  have hEΩ (k : ℕ) : ∫ y in Ω, ω.floerEnergyDensity
      (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ associativityPerturbation H Hout G G' L (τ k) (equivRealProdCLM.symm z) x
        Complex.I) (u k) y ≤ A + (∑ i, B i + Bout + 2 * (BG + BG')) := by
    have hmono := hω.setIntegral_floerEnergyDensity_mono_set (hΩS k)
      (isOpen_forall_ne (c := associativityCenter (Real.exp (-(2 * π * L)) / 4) (τ k))
        equivRealProdCLM.symm.continuous).measurableSet
      (hE k) (fun z hz ↦ hJt _ (hτC k) z hz _) (hfl k)
    have hbd := (abs_le.1 (hω.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le hH
      (fun i ↦ (hHs i).of_le (by norm_num)) hHout (hHouts.of_le (by norm_num)) hG
      (hGs.of_le (by norm_num)) hG' (hG's.of_le (by norm_num)) hL (τ k) hB hBout hBG hBG'
      ((hu k).of_le (by norm_num)) (hx k) (hxout k) (hE k) (hA k))).2
    linarith [hAtop k]
  exact hconv hΩ hΩD hτC (fun k ↦ (hu k).mono (hΩS k)) (fun k z hz ↦ hfl k z (hΩS k hz))
    (fun k ↦ (hE k).mono_set (hΩS k)) hEΩ

end TauCeti.SmoothTwoForm.IsNondegenerate
