/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange

/-!
# Compactness of the input-exchange family in a closed manifold

Graded commutativity of the pair-of-pants product compares the product with the product of the
exchanged inputs through the input-exchange family of Floer data on `S = ℂ ∖ {0, 1}`: the
perturbations `K_c = TauCeti.Floer.exchangePerturbation H c`, whose output end is the end at `∞`
recentred at `c`, together with almost complex structures `J_c`, for `c` in the parameter
interval `[0, 1]`. This file proves the interior part of Gromov–Floer compactness for the
solutions of the whole family in a closed manifold `M`, uniformly over a compact window of
parameters, with no condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Exchange` assume instead that the
images stay in a compact subset of one symplectic chart.

The compactness theorem over a compact parameter window in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** The perturbations are smooth jointly in the parameter `c`,
  the domain point of `S` and the target point (`TauCeti.Floer.contMDiffAt_exchangePerturbation`),
  so their Hamiltonian vector fields read in the chart at any point of `M` are `C²` in `(c, z, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`).
* **The energy bound.** Uniformly in `c ∈ [0, 1]`, the Floer energy over `S` exceeds the
  topological energy `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` by at most `B₀ + B₁ + B_∞`
  (`IsNondegenerate.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le` in the namespace
  `TauCeti.SmoothTwoForm`).
* **The almost complex structures of the family.** For the structures
  `TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex` of the family, built from a compatible
  base structure and period-one `C²` end structures, the structures read in the charts are `C²` in
  `(c, z, y)` for `-1 < c < 2` and `z ∈ S`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_exchangeAlmostComplex`, read in the charts by
  `TauCeti.Floer.contDiffOn_almostComplexInChartAt_almostComplexStructureAt`), and they are tame
  everywhere (`TauCeti.SmoothTwoForm.Compatible.tames_exchangeAlmostComplex`).

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange`: for any
  family `J_c(z, x)` of tame structures which is `C²` read in the charts of `M` near the parameter
  and domain windows, there is a threshold `δ > 0` such that every sequence of solutions for
  parameters `cₖ` in a compact window `C ⊆ [0, 1]`, with topological energy at most `A`, has a
  subsequence whose parameters converge to some `c₀ ∈ C` and which converges on an open `Ω ⊆ D`
  off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + B₀ + B₁ + B_∞`.

In the namespace `TauCeti.SmoothTwoForm.Compatible`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchangeAlmostComplex`
  is the same for the almost complex structures of the family.

The regularity of the limit, the bubbles at the points of `Z` and breaking along the three ends
are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Bundle Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {e : M → F}

namespace IsNondegenerate

/-- **Solutions of the input-exchange family in a closed manifold converge off finitely many
bubbling points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `H_q` be
period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, and let `K_c` be the perturbations of the
input-exchange family. Let `J_c(z, x)` be structures on the tangent spaces of `M`, tamed by `ω` for
`c` in a compact window `C ⊆ [0, 1]` of parameters and `z ∈ S = ℂ ∖ {0, 1}` (in real coordinates),
which read in the chart at every point of `M` are `C²` jointly in `(c, z, y)` on `W × (chart
target)`, for an open `W` containing `C × D` with `D ⊆ S` compact. Let `e : M → F` be injective and
differentiable, with the structures uniformly tame with respect to `e` over `C × D`,
`κ ‖d e v‖² ≤ ω(v, J_c(z) v)` with `κ > 0`, and the pushforwards through `e` of the Hamiltonian
vector fields of the two components of `K_c` at most `L` there. There is a threshold `δ > 0` with
the following property. Let `uₖ` be `C³` maps from `S` to `M` solving the Floer equation
`(du - X_{K_{cₖ}})^{0,1} = 0` for the structures `J_{cₖ}(z, u)`, with `cₖ ∈ C`, whose input loops
`uₖ(φ_q(R + i t))` and recentred output loops `uₖ(cₖ + φ_∞(-R + i t))` converge pointwise to loops
`xₖ q` as `R → ∞`, whose Floer energy and symplectic area densities are integrable over `S`, and
whose topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt` is at most `A`, and let
`Ω ⊆ D` be open. Then there are a subsequence `φ`, a limit `c₀ ∈ C` of the parameters `c_{φ n}`
and a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B₀ + B₁ + B_∞` such that, along `φ`, every disc about
a point of `Z` eventually carries energy at least `δ`, the energy densities are uniformly bounded
on every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous map `v`,
locally uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} {C : Set ℝ} {D : Set (ℝ × ℝ)} (hW : IsOpen W) (hC : IsCompact C)
    (hC₀₁ : C ⊆ Icc 0 1) (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal)
    (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJc : ∀ c ∈ C, ∀ z ∈ D, ∀ x v,
      κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J c z x v))
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
  -- Each component `(c, z) ↦ K_c(z)(w)` of the perturbations is `C³` jointly in the parameter,
  -- the domain point of `S` and the target point, so its Hamiltonian vector field is `C²` in
  -- every chart.
  have hK (w : ℂ) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ univ ×ˢ S) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry fun (p : ℝ × (ℝ × ℝ)) x ↦
          exchangePerturbation H p.1 (equivRealProdCLM.symm p.2) x w) (p, x) :=
    contMDiffAt_uncurry_exchangePerturbation_apply hH hHs w hp.2 x
  have hWS : IsOpen (W ∩ univ ×ˢ S) := hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  have hCDWS : C ×ˢ D ⊆ W ∩ univ ×ˢ S :=
    subset_inter hCDW (prod_mono (subset_univ _) hDS)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
      (Kt := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x Complex.I)
      he he_inj hWS hC hD hCDWS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun c hc z hz ↦ hJt c hc z (hDS hz)) hκ hJc hLs hLt
  refine ⟨δ, hδ, fun Ω c u x A hΩ hΩD hcC hu hfl hx hxinf hint harea htop ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hDS
  -- The Floer energy over `Ω` is at most the energy over `S`, which exceeds the topological energy
  -- by at most `B₀ + B₁ + B_∞`.
  exact hconv hΩ hΩD hcC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz))
    (fun k ↦ (hint k).mono_set hΩS) fun k ↦
      hω.setIntegral_floerEnergyDensity_exchangePerturbation_le hH
        (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
        ((hu k).of_le (by norm_num)) (hx k) (hxinf k) (hint k) (harea k)
        (fun z hz ↦ hJt _ (hcC k) z hz _) (hfl k) (htop k) hΩS

end IsNondegenerate

namespace Compatible

variable {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

/-- **Solutions of the input-exchange family in a closed manifold converge off finitely many
bubbling points, for the structures of the family.** Let `σ` be a two-form on a closed manifold
`M` compatible with a smooth almost complex structure `J₀`, and let the end structures `J q t` be
tamed by `σ`, of period one in `t` and jointly `C²` on `ℝ × M`. Take the structures
`TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex` of the input-exchange family, and
otherwise the hypotheses of
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, for a compact window `C ⊆ [0, 1]` of
parameters and a compact window `D ⊆ S`: the structures of the family are tame and regular in the
charts of `M`, so only the uniform tameness with respect to `e` and the bound on the Hamiltonian
vector fields remain as hypotheses. Then there is a threshold `δ > 0` such that every sequence of
solutions for parameters in `C` with topological energy at most `A` has a subsequence whose
parameters converge in `C` and which converges on an open `Ω ⊆ D` off a finite set `Z` of bubbling
points, with `#Z * δ ≤ A + B₀ + B₁ + B_∞`. -/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchangeAlmostComplex
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {C : Set ℝ} {D : Set (ℝ × ℝ)}
    (hC : IsCompact C) (hC₀₁ : C ⊆ Icc 0 1) (hD : IsCompact D)
    (hDS : D ⊆ thricePuncturedSphereReal)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJc : ∀ c ∈ C, ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.exchangeAlmostComplex J hJ c (equivRealProdCLM.symm z) x v))
    (hLs : ∀ c ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ c ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          ((h₀.exchangeAlmostComplex J hJ (c k) (equivRealProdCLM.symm z)).almostComplexStructureAt
            (u k z))
          (σ.perturbedMFDeriv
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ q ≠ Puncture.inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (↑(c k) + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop
          (𝓝 (x k Puncture.inf t))) →
      (∀ k, IntegrableOn (σ.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c₀ ∈ C, Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', σ.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hω := h₀.isNondegenerate
  -- The structures of the family are `C²` jointly in `(c, z, x)` for `-1 < c < 2` and `z ∈ S`.
  have hJ' (p : ℝ × (ℝ × ℝ)) (hp : p ∈ Ioo (-1) 2 ×ˢ thricePuncturedSphereReal) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (2 : ℕ∞)
        (fun q : (ℝ × (ℝ × ℝ)) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
          ((h₀.exchangeAlmostComplex J hJ q.1.1 (equivRealProdCLM.symm q.1.2)).toEndomorphism
            q.2)) (p, x) :=
    (h₀.contMDiffAt_exchangeAlmostComplex J hJ (n := 2) hJp hJs
      (contDiff_fst.contMDiff.comp contMDiff_fst).contMDiffAt
      ((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).contMDiffAt
      contMDiffAt_snd (y₀ := (p, x)) hp.1 hp.2).of_le (by norm_num)
  exact hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange
    (J := fun c z ↦
      (h₀.exchangeAlmostComplex J hJ c (equivRealProdCLM.symm z)).almostComplexStructureAt)
    hH hHs hB ((isOpen_Ioo (a := (-1 : ℝ)) (b := 2)).prod isOpen_thricePuncturedSphereReal) hC
    hC₀₁ hD hDS
    (prod_mono (hC₀₁.trans (Icc_subset_Ioo (by norm_num) (by norm_num))) hDS)
    (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2)
      (J := fun q : ℝ × (ℝ × ℝ) ↦ h₀.exchangeAlmostComplex J hJ q.1 (equivRealProdCLM.symm q.2))
      hJ')
    (fun c _ z _ x ↦ hω.tames_iff.1 (h₀.tames_exchangeAlmostComplex J hJ c _) x) he he_inj hκ
    (fun c hc z hz x v ↦ by
      simpa only [IsNondegenerate.symplecticFormAt_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc c hc z hz x v)
    hLs hLt

end Compatible

end TauCeti.SmoothTwoForm
