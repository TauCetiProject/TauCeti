/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange

/-!
# Compactness of the input-exchange family in a closed manifold

Graded commutativity of the pair-of-pants product compares the product with the product of the
exchanged inputs through the input-exchange family of Floer data on `S = ℂ ∖ {0, 1}`: the
perturbations `K_c = TauCeti.Floer.exchangePerturbation H c`, whose output end is the end at `∞`
recentred at `c`, for `c` in the parameter interval `[0, 1]`, together with almost complex
structures `J_c`. Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed
symplectic manifold. This file proves the interior part of Gromov–Floer compactness for the
solutions `u : S → M` of the whole family, over a compact window of parameters and on every
compact window of the domain, with no condition on where the solutions take their values. The
theorems of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Exchange` assume instead that
the images stay in a compact subset of one symplectic chart.

The general compactness theorem in a closed manifold over a compact parameter window,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** The family is smooth jointly in the parameter `c`, the domain
  point of `S` and the target point (`TauCeti.Floer.contMDiffAt_exchangePerturbation`), so for
  `C³` Hamiltonians `H_q` the Hamiltonian vector fields of its two components, read in the chart
  at any point of `M`, are `C²` in `(c, z, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`). The almost
  complex structures read in the charts are assumed `C²` in `(c, z, y)`.
* **The energy bound.** For `|H_q| ≤ B_q` and every `c ∈ [0, 1]`, the Floer energy over `S` of a
  solution exceeds its topological energy `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` by at most
  `B₀ + B₁ + B_∞`
  (`IsNondegenerate.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le` in the namespace
  `TauCeti.SmoothTwoForm`), and the energy over a part of `S` is at most the energy over `S`.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange`: on a
  compact window `D ⊆ S`, a sequence of solutions of the input-exchange family for parameters in a
  compact window `C ⊆ [0, 1]`, with topological energy at most `A`, has a subsequence whose
  parameters converge in `C` and which converges off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + B₀ + B₁ + B_∞` for a threshold `δ > 0` depending only on the data, `C` and `D`.

The regularity of the limit, the bubbles at the points of `Z` and breaking along the three ends are
not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

/-- **Solutions of the input-exchange family in a closed manifold converge off finitely many
bubbling points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `K_c` be the
input-exchange family of period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let
`J_c(z, x)` be structures on the tangent spaces of `M` which, read in the chart at every point of
`M`, are `C²` jointly in `(c, z, y)` on an open set `W` of parameters and domain points (in real
coordinates) containing `C × D`, for a compact window `C ⊆ [0, 1]` of parameters and a compact
window `D ⊆ S = ℂ ∖ {0, 1}` of the domain; let `J_c(z, x)` be tamed by `ω` for `c ∈ C` and
`z ∈ S`. Let `e : M → F` be injective and differentiable, and for `c ∈ C` and `z ∈ D` let the
structures be uniformly tame with respect to `e`, `κ ‖d e v‖² ≤ ω(v, J_c v)` with `κ > 0`, and the
pushforwards through `e` of the Hamiltonian vector fields of the two components of `K_c` be at
most `L`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_{K_{cₖ}})^{0,1} = 0` on `S` for `J_{cₖ}(z, u)`, with `cₖ ∈ C`, whose input loops
`uₖ(φ_q(R + i t))` and recentred output loops `uₖ(cₖ + φ_∞(-R + i t))` converge pointwise to loops
`xₖ q` as `R → ∞`, with integrable energy and area densities and topological energy
`∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt ≤ A`, and let `Ω ⊆ D` be open. Then there are a
subsequence `φ`, a limit `c₀ ∈ C` of `c_{φ n}`, and a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + B₀ + B₁ + B_∞` such that, along `φ`, every disc about a point of `Z` eventually
carries energy at least `δ`, the energy densities are uniformly bounded on every compact subset of
`Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`, locally uniformly after
applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {W : Set (ℝ × (ℝ × ℝ))} (hW : IsOpen W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    {C : Set ℝ} (hC : IsCompact C) (hC₀₁ : C ⊆ Icc 0 1) {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDS : D ⊆ thricePuncturedSphereReal) (hCDW : C ×ˢ D ⊆ W)
    (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJκ : ∀ c ∈ C, ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J c z x v))
    (hLs : ∀ c ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ c ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ q ≠ Puncture.inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (↑(c k) + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop
          (𝓝 (x k Puncture.inf t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c₀ ∈ C, Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  set S := thricePuncturedSphereReal
  -- Each component `(c, z) ↦ K_{c, z}(w)` of the family is `C³` jointly in the parameter, the
  -- domain point of `S` and the target point, so its Hamiltonian vector field is `C²` in every
  -- chart.
  have hK (w : ℂ) (q : ℝ × (ℝ × ℝ)) (hq : q ∈ univ ×ˢ S) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry (uncurry fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x w))
        (q, x) :=
    (((contMDiffAt_exchangePerturbation hH hHs q.1
      ⟨_, mem_thricePuncturedSphereReal_iff.1 hq.2⟩ x).comp (q, x)
      (((contDiff_fst.contMDiff.comp contMDiff_fst).prodMk
        (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).prodMk
          contMDiff_snd)).contMDiffAt)).clm_apply contMDiffAt_const).of_le (by norm_num)
  have hWS : IsOpen (W ∩ univ ×ˢ S) :=
    hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  have hsub (α : M) : (W ∩ univ ×ˢ S) ×ˢ (extChartAt I α).target ⊆
      (univ ×ˢ S) ×ˢ (extChartAt I α).target :=
    prod_mono inter_subset_right subset_rfl
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
      (Kt := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x Complex.I)
      he he_inj hWS hC hD (subset_inter hCDW (prod_mono (subset_univ C) hDS))
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono (hsub α))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono (hsub α))
      (fun c hc z hz x ↦ hJt c hc z (hDS hz) x) hκ hJκ hLs hLt
  refine ⟨δ, hδ, fun Ω c u x A hΩ hΩD hcC hu hfl hx hxinf hint harea htop ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hDS
  -- The Floer energy over `Ω` is at most the energy over `S`, which exceeds the topological energy
  -- by at most `B₀ + B₁ + B_∞`.
  refine hconv hΩ hΩD hcC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz))
    (fun k ↦ (hint k).mono_set hΩS) fun k ↦ ?_
  have habs := hω.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
    ((hu k).of_le (by norm_num)) (hx k) (hxinf k) (hint k) (harea k)
  refine (hω.setIntegral_floerEnergyDensity_mono_set hΩS
    isOpen_thricePuncturedSphereReal.measurableSet (hint k) (fun z hz ↦ hJt _ (hcC k) z hz _)
    (hfl k)).trans ?_
  linarith [(abs_sub_le_iff.1 habs).1, htop k]

end TauCeti.SmoothTwoForm.IsNondegenerate
