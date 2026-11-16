/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.PDE.Regularity.Semilinear
import TauCeti.Analysis.PDE.Regularity.Smooth
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Chart
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Elliptic regularity on closed Riemannian manifolds

Let `M` be a compact Hausdorff smooth manifold without boundary carrying a smooth Riemannian
metric, with Riemannian volume `dV`, nonnegative Laplacian `Δ⁺ = -div grad`, and Sobolev space
`H¹(M)` (`TauCeti.Manifold.SobolevH1`). This file transfers interior Euclidean elliptic regularity
for divergence-form operators (`TauCeti/Analysis/PDE/Regularity/Smooth.lean` and
`TauCeti/Analysis/PDE/Regularity/Semilinear.lean`) to weak solutions on `M` via coordinate charts.

Near each point `p ∈ M`, identify the model space `E` with `EuclideanSpace ℝ (Fin d)` using the
canonical basis `Module.finBasis ℝ E`. This identification carries the coordinate Haar measure of
`Module.finBasis ℝ E` to Lebesgue measure on `ℝᵈ`, so the Riemannian volume in coordinates has
exact density `ρ = √det G` (`TauCeti.chartVolumeDensity`). On a sufficiently small coordinate ball
`Ω` around `p`, reading an element of `H¹(M)` in the chart is a continuous linear map
`T : H¹(M) → W^{1,2}(Ω)` (`TauCeti.Manifold.SobolevH1.exists_continuousLinearMap_w1p_extChartAt`),
and the Riemannian Dirichlet form agrees with the Euclidean divergence-form energy form for the
smooth, uniformly elliptic coefficient matrix `a = ρ G⁻¹`:

`D(w, ψ_M) = ∫_Ω ⟨∇ψ, (ρ G⁻¹) ∇(T w)⟩`

for every test function `ψ ∈ 𝓓(Ω, ℝ)` transplanted to `M` as `ψ_M`.

Euclidean interior regularity then yields a smooth representative of `T w` on `Ω`. Pulling these
local smooth representatives back to `M`, uniqueness of continuous representatives with respect to
the strictly positive measure `dV` glues them into a global smooth function `u ∈ C^∞(M)` with
`w = ofSmooth u`. Finally, Green's identity tested against the smooth residual `-Δu - F` upgrades
the weak equation to the pointwise classical PDE.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_add_mul_eq`: a weak
  solution in `H¹(M)` of the linear equation `Δ⁺w + c w = f` with smooth `c` and `f` is smooth
  and satisfies `-Δu + c u = f` everywhere, in any dimension.
* `TauCeti.Manifold.SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq`: the Poisson case
  `c = 0`.
* `TauCeti.Manifold.existsUnique_contMDiff_neg_laplaceBeltrami_eq`: on a closed connected smooth
  Riemannian manifold of any dimension, every smooth function `f` with `∫ f dV = 0` has a unique
  smooth solution `u` of `Δ⁺u = f` with `∫ u dV = 0`.
* `TauCeti.Manifold.SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq_mul_comp_add`: in
  dimension at most three, a weak solution in `H¹(M)` of the semilinear equation
  `Δ⁺w = A Φ(w) + C` with smooth `A, C, Φ` and square-integrable forcing is smooth and satisfies
  `-Δu = A Φ(u) + C` everywhere.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 4.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
-/

public section

open Bundle MeasureTheory Metric Riemannian.Tensor Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Identification of the model space `E` with `EuclideanSpace ℝ (Fin d)` sending
`Module.finBasis ℝ E` to the standard orthonormal basis of `EuclideanSpace ℝ (Fin d)`. -/
private def basisEquivEuclidean :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  ((Module.finBasis ℝ E).equiv
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
    (Equiv.refl _)).toContinuousLinearEquiv

private theorem basisEquivEuclidean_apply_finBasis (i : Fin (Module.finrank ℝ E)) :
    basisEquivEuclidean (Module.finBasis ℝ E i) = EuclideanSpace.single i 1 := by
  simp [basisEquivEuclidean, EuclideanSpace.basisFun_apply]

private theorem basisEquivEuclidean_symm_single (i : Fin (Module.finrank ℝ E)) :
    basisEquivEuclidean.symm (EuclideanSpace.single i (1 : ℝ)) = Module.finBasis ℝ E i := by
  rw [← basisEquivEuclidean_apply_finBasis, ContinuousLinearEquiv.symm_apply_apply]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- The basis identification sends the Haar measure of `Module.finBasis ℝ E` to Lebesgue measure
on `EuclideanSpace ℝ (Fin d)`. -/
private theorem measurePreserving_basisEquivEuclidean :
    MeasurePreserving (basisEquivEuclidean (E := E)) (Module.finBasis ℝ E).addHaar volume := by
  refine ⟨basisEquivEuclidean.continuous.measurable, ?_⟩
  rw [Module.Basis.map_addHaar]
  have hmap : (Module.finBasis ℝ E).map (basisEquivEuclidean (E := E)).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis := by
    ext i
    simp [basisEquivEuclidean]
  rw [hmap]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume

/-- The inverse basis identification carries Lebesgue measure on `EuclideanSpace ℝ (Fin d)` to the
Haar measure of `Module.finBasis ℝ E`. -/
private theorem measurePreserving_basisEquivEuclidean_symm :
    MeasurePreserving (basisEquivEuclidean (E := E)).symm volume (Module.finBasis ℝ E).addHaar := by
  have h := (measurePreserving_basisEquivEuclidean (E := E)).symm
    (basisEquivEuclidean (E := E)).toHomeomorph.toMeasurableEquiv
  simpa using h

end Coordinates

section UniformEllipticity

/-- A continuous matrix field on a compact set whose quadratic form is strictly positive on every
nonzero vector is uniformly elliptic on that set. -/
private theorem exists_uniformlyEllipticOn_of_continuousOn_pos
    {ι X : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ ι, ξ ≠ 0 → 0 < (a x).toQuadraticForm' ξ) :
    ∃ lam Lam, TauCeti.PDE.UniformlyEllipticOn K a lam Lam := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, 1, TauCeti.PDE.UniformlyEllipticOn.of_bounds zero_lt_one le_rfl
      (fun _ hx _ ↦ False.elim hx) (fun _ hx _ _ ↦ False.elim hx)⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, TauCeti.PDE.UniformlyEllipticOn.of_bounds zero_lt_one le_rfl
      (fun _ _ ξ ↦ ?_) (fun _ _ η ξ ↦ ?_)⟩
    · have hξ : ξ = 0 := Subsingleton.elim _ _
      simp [hξ]
    · have hξ : ξ = 0 := Subsingleton.elim _ _
      simp [hξ]
  obtain ⟨i₀⟩ := hι
  -- Minimize the quadratic form on the compact product `K × S^{n-1}`.
  have hS : IsCompact (sphere (0 : EuclideanSpace ℝ ι) 1) := isCompact_sphere 0 1
  have hSne : (sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
    ⟨EuclideanSpace.single i₀ 1, by simp⟩
  have hqcont : ContinuousOn
      (fun p : X × EuclideanSpace ℝ ι ↦ (p.2 : ι → ℝ) ⬝ᵥ (a p.1 *ᵥ (p.2 : ι → ℝ)))
      (K ×ˢ sphere (0 : EuclideanSpace ℝ ι) 1) := by
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    have hcoord (k : ι) : ContinuousOn (fun p : X × EuclideanSpace ℝ ι ↦ p.2 k)
        (K ×ˢ sphere (0 : EuclideanSpace ℝ ι) 1) :=
      (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) k).comp_continuousOn continuousOn_snd
    refine (hcoord i).mul (continuousOn_finsetSum _ fun j _ ↦ ?_)
    have ha_ij : ContinuousOn (fun p : X × EuclideanSpace ℝ ι ↦ a p.1 i j)
        (K ×ˢ sphere (0 : EuclideanSpace ℝ ι) 1) :=
      (continuousOn_pi.1 (continuousOn_pi.1 ha i) j).comp continuousOn_fst mapsTo_fst_prod
    exact ha_ij.mul (hcoord j)
  obtain ⟨⟨x₀, ξ₀⟩, ⟨hx₀, hξ₀⟩, hmin⟩ :=
    (hK.prod hS).exists_isMinOn (hKne.prod hSne) hqcont
  have hξ₀_ne : ξ₀ ≠ 0 := by
    intro h
    simp [h] at hξ₀
  let lam : ℝ := (ξ₀ : ι → ℝ) ⬝ᵥ (a x₀ *ᵥ (ξ₀ : ι → ℝ))
  have hlam : 0 < lam := by
    simpa [lam, Matrix.toQuadraticForm'_apply] using hpos x₀ hx₀ ξ₀ hξ₀_ne
  -- Bound each matrix entry on `K` to obtain an upper bound for the bilinear form.
  have hbound_entry (i j : ι) : ∃ C : ℝ, ∀ x ∈ K, |a x i j| ≤ C := by
    obtain ⟨C, hC⟩ :=
      hK.exists_bound_of_continuousOn (continuousOn_pi.1 (continuousOn_pi.1 ha i) j)
    exact ⟨C, fun x hx ↦ by simpa [Real.norm_eq_abs] using hC x hx⟩
  choose C hC using hbound_entry
  let Lam := max lam (∑ i : ι, ∑ j : ι, C i j)
  refine ⟨lam, Lam, TauCeti.PDE.UniformlyEllipticOn.of_bounds hlam (le_max_left _ _)
    (fun x hx ξ ↦ ?_) (fun x hx η ξ ↦ ?_)⟩
  · by_cases hξ : ξ = 0
    · simp [hξ]
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      have hu : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : EuclideanSpace ℝ ι) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have hle : lam ≤ ((‖ξ‖⁻¹ • ξ : EuclideanSpace ℝ ι) : ι → ℝ) ⬝ᵥ
          (a x *ᵥ ((‖ξ‖⁻¹ • ξ : EuclideanSpace ℝ ι) : ι → ℝ)) :=
        isMinOn_iff.1 hmin (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hu⟩
      rw [WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow, inv_mul_eq_div,
        le_div_iff₀ (sq_pos_of_pos hn)] at hle
      rwa [Matrix.toQuadraticForm'_apply]
  · have habs : |(η : ι → ℝ) ⬝ᵥ (a x *ᵥ (ξ : ι → ℝ))| ≤
        (∑ i : ι, ∑ j : ι, C i j) * ‖η‖ * ‖ξ‖ := by
      calc |(η : ι → ℝ) ⬝ᵥ (a x *ᵥ (ξ : ι → ℝ))|
          = |∑ i : ι, η i * ∑ j : ι, a x i j * ξ j| := rfl
        _ ≤ ∑ i : ι, |η i * ∑ j : ι, a x i j * ξ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : ι, ∑ j : ι, C i j * ‖η‖ * ‖ξ‖ := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [abs_mul]
            calc |η i| * |∑ j : ι, a x i j * ξ j|
                ≤ |η i| * ∑ j : ι, |a x i j * ξ j| :=
                  mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
              _ = ∑ j : ι, |η i| * (|a x i j| * |ξ j|) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun j _ ↦ ?_
                  rw [abs_mul]
              _ ≤ ∑ j : ι, C i j * ‖η‖ * ‖ξ‖ := by
                  refine Finset.sum_le_sum fun j _ ↦ ?_
                  have hη : |η i| ≤ ‖η‖ := by
                    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le η i
                  have hξ : |ξ j| ≤ ‖ξ‖ := by
                    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
                  have h1 : |a x i j| * |ξ j| ≤ C i j * ‖ξ‖ :=
                    mul_le_mul (hC i j x hx) hξ (abs_nonneg _)
                      ((abs_nonneg _).trans (hC i j x hx))
                  have h2 : |η i| * (|a x i j| * |ξ j|) ≤ ‖η‖ * (C i j * ‖ξ‖) :=
                    mul_le_mul hη h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
                  linarith
        _ = (∑ i : ι, ∑ j : ι, C i j) * ‖η‖ * ‖ξ‖ := by
            simp_rw [← Finset.sum_mul]
    exact habs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg η)) (norm_nonneg ξ))

end UniformEllipticity

section EnergyFormMass

/-- Extending a test-function weak equation for the principal part `a(u, ψ) = ∫ (f - c u) ψ` to
all `v ∈ H¹₀(Ω)` and moving the mass term `c u` back to the energy form `energyFormH1 a 0 c`. -/
private theorem forall_energyFormH1_mass_eq_setIntegral {ι : Type*} [Fintype ι]
    {Ω : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {c f : EuclideanSpace ℝ ι → ℝ}
    (hcoeff : MemLp (fun y ↦ TauCeti.PDE.energyIntegrand (a y) 0 0) ⊤ (volume.restrict (Ω : Set _)))
    {u : W1p volume Ω 2}
    (hf : MemLp f 2 (volume.restrict (Ω : Set _)))
    (hc : MemLp (fun y ↦ c y * W1p.value u y) 2 (volume.restrict (Ω : Set _)))
    (htest : ∀ ψ : 𝓓(Ω, ℝ),
      TauCeti.PDE.energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 ψ) =
        ∫ y in Ω, (f y - c y * W1p.value u y) * ψ y ∂volume)
    (v : W1p0 volume Ω 2) :
    TauCeti.PDE.energyFormH1 a 0 c u (v : W1p volume Ω 2) =
      ∫ y in Ω, f y * W1p.value (v : W1p volume Ω 2) y ∂volume := by
  have hW1p0_zero : TauCeti.PDE.energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ y in Ω, (f y - c y * W1p.value u y) * W1p.value (v : W1p volume Ω 2) y ∂volume := by
    simpa only [W1p.restrictL_self] using
      TauCeti.PDE.forall_energyFormH1_restrictL_eq_setIntegral (le_rfl : Ω ≤ Ω) hcoeff htest
        (hf.sub hc) v
  have h1 : Integrable (fun y ↦ TauCeti.PDE.energyIntegrand (a y)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) y) ((0 : EuclideanSpace ℝ ι → ℝ) y)
      (TauCeti.PDE.jetField u y) (TauCeti.PDE.jetField (v : W1p volume Ω 2) y))
      (volume.restrict (Ω : Set _)) :=
    (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (v : W1p volume Ω 2)).congr
      (Filter.Eventually.of_forall fun _ ↦ by simp only [Pi.zero_apply])
  have h2 : Integrable (fun y ↦ c y * W1p.value u y * W1p.value (v : W1p volume Ω 2) y)
      (volume.restrict (Ω : Set _)) :=
    hc.integrable_mul (Lp.memLp (W1p.value (v : W1p volume Ω 2)))
  have h3 : Integrable (fun y ↦ f y * W1p.value (v : W1p volume Ω 2) y)
      (volume.restrict (Ω : Set _)) :=
    hf.integrable_mul (Lp.memLp (W1p.value (v : W1p volume Ω 2)))
  have hsplit : TauCeti.PDE.energyFormH1 a 0 c u (v : W1p volume Ω 2) =
      TauCeti.PDE.energyFormH1 a 0 0 u (v : W1p volume Ω 2) +
        ∫ y in Ω, c y * W1p.value u y * W1p.value (v : W1p volume Ω 2) y ∂volume := by
    rw [TauCeti.PDE.energyFormH1_def, TauCeti.PDE.energyFormH1_def]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)).trans (integral_add h1 h2)
    simp only [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.massForm_apply,
      TauCeti.PDE.jetField_apply, Pi.zero_apply, zero_mul, add_zero]
  have hrhs : ∫ y in Ω, (f y - c y * W1p.value u y) * W1p.value (v : W1p volume Ω 2) y ∂volume =
      (∫ y in Ω, f y * W1p.value (v : W1p volume Ω 2) y ∂volume) -
        ∫ y in Ω, c y * W1p.value u y * W1p.value (v : W1p volume Ω 2) y ∂volume := by
    simp_rw [sub_mul]
    exact integral_sub h3 h2
  rw [hsplit, hW1p0_zero, hrhs]
  ring

end EnergyFormMass

section ChartOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The chart volume density at `p`, read on `EuclideanSpace ℝ (Fin d)` through
`basisEquivEuclidean`. -/
private def chartDensity (p : M) (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  chartVolumeDensity (I := I) p ((extChartAt I p).symm (basisEquivEuclidean.symm y))

/-- The divergence-form principal coefficient matrix `ρ G⁻¹` of the Laplace–Beltrami operator in
the extended chart at `p`, read on `EuclideanSpace ℝ (Fin d)` through `basisEquivEuclidean`. -/
private def chartEllipticCoeff (p : M) (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  chartDensity (I := I) p y •
    chartInvGramMatrix (I := I) p ((extChartAt I p).symm (basisEquivEuclidean.symm y))

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- Reading a smooth function on `M` in the extended chart at `p` through `basisEquivEuclidean`
yields a smooth function on the preimage of the chart target. -/
private theorem contDiffOn_comp_extChartAt_symm (p : M) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f (chartAt H p).source) :
    ContDiffOn ℝ ∞ (fun y ↦ f ((extChartAt I p).symm (basisEquivEuclidean.symm y)))
      (basisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I p).symm) (extChartAt I p).target :=
    hf.comp (contMDiffOn_extChartAt_symm p) fun z hz ↦ by
      rw [mem_preimage, ← extChartAt_source (I := I)]
      exact (extChartAt I p).map_target hz
  exact h1.contDiffOn.comp basisEquivEuclidean.symm.contDiff.contDiffOn (mapsTo_preimage _ _)

/-- The chart volume density in Euclidean coordinates is smooth on the preimage of the chart
target. -/
private theorem contDiffOn_chartDensity
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (p : M) :
    ContDiffOn ℝ ∞ (chartDensity (I := I) p)
      (basisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := (∞ : ℕ∞ω)) (by simp)
  have h : ContMDiffOn I 𝓘(ℝ) ∞ (chartVolumeDensity (I := I) p) (chartAt H p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartVolumeDensity (I := I) (n := ∞) p
  exact contDiffOn_comp_extChartAt_symm p h

/-- Every entry of the chart elliptic coefficient matrix is smooth on the preimage of the chart
target. -/
private theorem contDiffOn_chartEllipticCoeff_entry
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (p : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun y ↦ chartEllipticCoeff (I := I) p y i j)
      (basisEquivEuclidean.symm ⁻¹' (extChartAt I p).target) := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := (∞ : ℕ∞ω)) (by simp)
  have hinv : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x ↦ chartInvGramMatrix (I := I) p x i j) (chartAt H p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) p i j
  simpa only [chartEllipticCoeff, Matrix.smul_apply, smul_eq_mul] using
    (contDiffOn_chartDensity p).mul (contDiffOn_comp_extChartAt_symm p hinv)

/-- The chart elliptic coefficient matrix has strictly positive quadratic form on every nonzero
vector throughout the preimage of the chart target. -/
private theorem toQuadraticForm'_chartEllipticCoeff_pos (p : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : basisEquivEuclidean.symm y ∈ (extChartAt I p).target)
    {ξ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (hξ : ξ ≠ 0) :
    0 < (chartEllipticCoeff (I := I) p y).toQuadraticForm' ξ := by
  let x := (extChartAt I p).symm (basisEquivEuclidean.symm y)
  have hx : x ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hy
  have hxb : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hρ : 0 < chartDensity (I := I) p y := chartVolumeDensity_pos p hxb
  let G := chartGramMatrix (I := I) p x
  let Ginv := chartInvGramMatrix (I := I) p x
  have hGpd : G.PosDef := posDef_chartGramMatrix p hxb
  have hGGinv : G * Ginv = 1 := chartGramMatrix_mul_chartInvGramMatrix p hx
  let η : Fin (Module.finrank ℝ E) → ℝ := Ginv *ᵥ ξ
  have hGη : G *ᵥ η = ξ := by
    rw [Matrix.mulVec_mulVec, hGGinv, Matrix.one_mulVec]
  have hη : η ≠ 0 := by
    intro h0
    apply hξ
    ext i
    have hi := congrFun hGη i
    simp [h0] at hi
    exact hi.symm
  have hquad : 0 < (Ginv).toQuadraticForm' ξ := by
    rw [Matrix.toQuadraticForm'_apply]
    have hdot : (ξ : Fin (Module.finrank ℝ E) → ℝ) ⬝ᵥ η = η ⬝ᵥ (G *ᵥ η) :=
      calc (ξ : Fin (Module.finrank ℝ E) → ℝ) ⬝ᵥ η
          = (G *ᵥ η) ⬝ᵥ η := by rw [hGη]
        _ = η ⬝ᵥ (G *ᵥ η) := dotProduct_comm _ _
    rw [hdot]
    simpa only [star_trivial] using hGpd.dotProduct_mulVec_pos hη
  rw [chartEllipticCoeff, Matrix.toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul]
  exact mul_pos hρ hquad

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
/-- The `i`-th coordinate of the Euclidean gradient of a smooth function read in the chart at `p`
is its manifold derivative along the `i`-th chart-local frame vector. -/
private theorem gradient_comp_extChartAt_symm_apply [I.Boundaryless] (p : M) (u : C^∞⟮I, M; ℝ⟯)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : basisEquivEuclidean.symm y ∈ (extChartAt I p).target)
    (i : Fin (Module.finrank ℝ E)) :
    (∇ (fun z ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm z))) y) i =
      mvfderiv I u ((extChartAt I p).symm (basisEquivEuclidean.symm y))
        (chartLocalFrame (I := I) p i ((extChartAt I p).symm (basisEquivEuclidean.symm y))) := by
  set x := (extChartAt I p).symm (basisEquivEuclidean.symm y)
  have hx : x ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hy
  have hright : extChartAt I p x = basisEquivEuclidean.symm y := (extChartAt I p).right_inv hy
  have hfun : (fun z ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm z))) =
      ((u : M → ℝ) ∘ (extChartAt I p).symm) ∘ basisEquivEuclidean.symm := rfl
  have hinner : (∇ (fun z ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm z))) y) i =
      ⟪∇ (fun z ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm z))) y,
        EuclideanSpace.single i 1⟫_ℝ := by
    rw [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  rw [hinner, gradient, InnerProductSpace.toDual_symm_apply, hfun,
    basisEquivEuclidean.symm.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, basisEquivEuclidean_symm_single, ← hright]
  exact (mvfderiv_chartLocalFrame (I := I) p hx
    (u.contMDiff.mdifferentiable (by simp) x) i).symm

/-- Pointwise chart formula for the Dirichlet integrand: in coordinates, the matrix bilinear form
of `chartEllipticCoeff p = ρ G⁻¹` on the Euclidean gradients of `v` and `u` equals
`ρ ⟪grad u, grad v⟫`. -/
private theorem matrixBilinearForm_chartEllipticCoeff_gradient_eq [I.Boundaryless] (p : M)
    (u v : C^∞⟮I, M; ℝ⟯) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : basisEquivEuclidean.symm y ∈ (extChartAt I p).target) :
    TauCeti.PDE.matrixBilinearForm (chartEllipticCoeff (I := I) p y)
        (∇ (fun z ↦ v ((extChartAt I p).symm (basisEquivEuclidean.symm z))) y)
        (∇ (fun z ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm z))) y) =
      chartDensity (I := I) p y *
        ⟪mgradient I u ((extChartAt I p).symm (basisEquivEuclidean.symm y)),
          mgradient I v ((extChartAt I p).symm (basisEquivEuclidean.symm y))⟫_ℝ := by
  set x := (extChartAt I p).symm (basisEquivEuclidean.symm y)
  have hx : x ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hy
  rw [chartEllipticCoeff, TauCeti.PDE.matrixBilinearForm_smul_apply]
  congr 1
  rw [inner_mgradient_right, mgradient_def, rieszDual_eq_sum_chartLocalFrame (I := I) p hx,
    map_sum, TauCeti.PDE.matrixBilinearForm_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 1
  · simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [gradient_comp_extChartAt_symm_apply p u hy j]
  · exact gradient_comp_extChartAt_symm_apply p v hy i

end ChartOperator

section LocalBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Integrating a function supported in the chart preimage of an open set `Ω ⊆ ℝᵈ` against the
Riemannian volume is the integral over `Ω` of the chart density times the coordinate expression. -/
private theorem integral_eq_setIntegral_chartDensity (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hΩt : MapsTo (basisEquivEuclidean (E := E)).symm Ω (extChartAt I p).target)
    {g : M → ℝ}
    (hg : ∀ x, x ∉ (extChartAt I p).source ∩
      extChartAt I p ⁻¹' (basisEquivEuclidean ⁻¹' (Ω : Set _)) → g x = 0) :
    ∫ x, g x ∂riemannianVolume I M =
      ∫ y in Ω, chartDensity (I := I) p y *
        g ((extChartAt I p).symm (basisEquivEuclidean.symm y)) ∂volume := by
  let L := basisEquivEuclidean (E := E)
  let U : Set M := (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L ⁻¹' (Ω : Set _))
  have hLΩ_open : IsOpen (L ⁻¹' (Ω : Set _)) := Ω.isOpen.preimage L.continuous
  have hLΩ_sub : L ⁻¹' (Ω : Set _) ⊆ (extChartAt I p).target := fun z hz ↦ by
    simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using hΩt hz
  have hU_open : IsOpen U := isOpen_extChartAt_preimage' p hLΩ_open
  have hU_sub : U ⊆ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact inter_subset_left
  have himage : extChartAt I p '' U = L ⁻¹' (Ω : Set _) := by
    rw [PartialEquiv.image_source_inter_eq',
      PartialEquiv.target_inter_inv_preimage_preimage, inter_eq_right.2 hLΩ_sub]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg,
    setIntegral_riemannianVolume_of_subset hU_sub hU_open.measurableSet, himage]
  have hmp : MeasurePreserving L.symm volume (Module.finBasis ℝ E).addHaar :=
    measurePreserving_basisEquivEuclidean_symm (E := E)
  have hemb : MeasurableEmbedding (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
    L.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpre : L.symm ⁻¹' (L ⁻¹' (Ω : Set _)) = (Ω : Set _) := by
    ext y
    simp [L]
  rw [← hmp.setIntegral_preimage_emb hemb, hpre]
  simp only [smul_eq_mul, chartDensity, L]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Transplanting a Euclidean test function to the manifold.** Given `ψ ∈ 𝓓(Ω, ℝ)` on a
coordinate open set `Ω` inside the chart target at `p`, there is a smooth function `ψM` on `M`,
supported in the chart preimage of `Ω` and agreeing with `ψ` in coordinates, such that
1. integrating any `f : M → ℝ` against `ψM` equals integrating `ρ (f ∘ φ⁻¹) ψ` over `Ω`;
2. the chart divergence-form energy of `T w` against `ψ` equals the Dirichlet form `D(w, ψM)` for
   every `w ∈ H¹(M)`. -/
private theorem exists_transplant_testFunction (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hΩt : MapsTo (basisEquivEuclidean (E := E)).symm Ω (extChartAt I p).target)
    (hcoeff : MemLp (fun y ↦ TauCeti.PDE.energyIntegrand (chartEllipticCoeff (I := I) p y) 0 0)
      ⊤ (volume.restrict (Ω : Set _)))
    (T : SobolevH1 I M →L[ℝ] W1p volume Ω 2)
    (hTgrad : ∀ u : C^∞⟮I, M; ℝ⟯, W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
      ∇ fun y ↦ u ((extChartAt I p).symm (basisEquivEuclidean.symm y)))
    (ψ : 𝓓(Ω, ℝ)) :
    ∃ ψM : C^∞⟮I, M; ℝ⟯,
      (∀ f : M → ℝ, ∫ x, f x * ψM x ∂riemannianVolume I M =
        ∫ y in Ω, (chartDensity (I := I) p y *
          f ((extChartAt I p).symm (basisEquivEuclidean.symm y))) * ψ y ∂volume) ∧
      ∀ w : SobolevH1 I M,
        TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (T w)
          (W1p.ofTestFunctionₗ volume Ω 2 ψ) = dirichletForm w (ofSmooth ψM) := by
  let L := basisEquivEuclidean (E := E)
  let w₀ : E → ℝ := (ψ : _ → ℝ) ∘ L
  have hw₀_diff : ContDiff ℝ ∞ w₀ := ψ.contDiff.comp L.contDiff
  have hw₀_tsupp_eq : tsupport w₀ = L ⁻¹' tsupport (ψ : _ → ℝ) :=
    tsupport_comp_eq_preimage _ L.toHomeomorph
  have hw₀_tsupp : tsupport w₀ ⊆ L ⁻¹' (Ω : Set _) :=
    hw₀_tsupp_eq.trans_subset (preimage_mono ψ.tsupport_subset)
  have hw₀_supp : HasCompactSupport w₀ := by
    rw [HasCompactSupport, hw₀_tsupp_eq]
    exact L.toHomeomorph.isCompact_preimage.2 ψ.hasCompactSupport
  have hw₀_target : tsupport w₀ ⊆ (extChartAt I p).target := hw₀_tsupp.trans fun z hz ↦ by
    simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using hΩt hz
  obtain ⟨ψ_fun, hψ_smooth, -, hψ_tsupp, hψ_eq⟩ :=
    exists_contMDiff_comp_extChartAt_symm_eq (I := I) (c := p) hw₀_diff hw₀_supp hw₀_target
  let ψM : C^∞⟮I, M; ℝ⟯ := ⟨ψ_fun, hψ_smooth⟩
  let U : Set M := (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L ⁻¹' (Ω : Set _))
  have hψM_tsupp : tsupport (ψM : M → ℝ) ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hψ_tsupp hx
    have hzt : z ∈ (extChartAt I p).target := hw₀_target hz
    exact ⟨(extChartAt I p).map_target hzt, by
      rw [mem_preimage, (extChartAt I p).right_inv hzt]
      exact hw₀_tsupp hz⟩
  have hψM_eq : ∀ y ∈ (Ω : Set _), ψM ((extChartAt I p).symm (L.symm y)) = ψ y := fun y hy ↦
    (hψ_eq (L.symm y) (hΩt hy)).trans (by simp [w₀, L])
  refine ⟨ψM, fun f ↦ ?_, fun w ↦ ?_⟩
  · -- Formula for integrating any `f` against `ψM`.
    have hzero : ∀ x, x ∉ U → f x * ψM x = 0 := fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψM_tsupp h)), mul_zero]
    rw [integral_eq_setIntegral_chartDensity p hΩt hzero]
    refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y hy ↦ ?_
    rw [hψM_eq y hy, mul_assoc]
  · -- Match the energy form and Dirichlet form by density from smooth functions.
    have heq_cont : Continuous fun w : SobolevH1 I M ↦
        TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (T w)
          (W1p.ofTestFunctionₗ volume Ω 2 ψ) := by
      have hrewrite : (fun w : SobolevH1 I M ↦
          TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (T w)
            (W1p.ofTestFunctionₗ volume Ω 2 ψ)) =
          fun w ↦ TauCeti.PDE.energyFormH1L hcoeff (T w) (W1p.ofTestFunctionₗ volume Ω 2 ψ) :=
        funext fun w ↦ (TauCeti.PDE.energyFormH1L_apply hcoeff _ _).symm
      rw [hrewrite]
      exact ((ContinuousLinearMap.apply ℝ ℝ (W1p.ofTestFunctionₗ volume Ω 2 ψ)).comp
        ((TauCeti.PDE.energyFormH1L hcoeff).comp T)).continuous
    have hdir_cont : Continuous fun w : SobolevH1 I M ↦ dirichletForm w (ofSmooth ψM) :=
      ((ContinuousLinearMap.apply ℝ ℝ (ofSmooth ψM)).comp dirichletForm).continuous
    refine induction_on w (isClosed_eq heq_cont hdir_cont) fun u ↦ ?_
    -- For smooth `u`, both sides reduce to the coordinate integral over `Ω`.
    have hzero_grad : ∀ x, x ∉ U → ⟪mgradient I u x, mgradient I ψM x⟫_ℝ = 0 := fun x hx ↦ by
      have hx' : x ∉ tsupport (ψM : M → ℝ) := fun h ↦ hx (hψM_tsupp h)
      have hloc : (ψM : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
        Filter.eventually_of_mem ((isClosed_tsupport _).isOpen_compl.mem_nhds hx') fun z hz ↦
          image_eq_zero_of_notMem_tsupport hz
      have hder : mvfderiv I (ψM : M → ℝ) x = 0 := by
        rw [hloc.mvfderiv_eq]
        exact mvfderiv_const 0
      rw [mgradient_eq_zero_iff.2 hder, inner_zero_right]
    rw [dirichletForm_ofSmooth, integral_eq_setIntegral_chartDensity p hΩt hzero_grad,
      TauCeti.PDE.energyFormH1_zero_zero_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hTgrad u, W1p.gradient_ofTestFunctionₗ (mu := volume) (Omega := Ω) (p := 2) ψ ▸
      gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω) 2 ψ,
      ae_restrict_mem Ω.isOpen.measurableSet] with y hu_grad hψ_grad hy
    have hgrad_ψ : ∇ (fun z ↦ ψM ((extChartAt I p).symm (L.symm z))) y = ∇ (ψ : _ → ℝ) y := by
      have hloc : (fun z ↦ ψM ((extChartAt I p).symm (L.symm z))) =ᶠ[𝓝 y] (ψ : _ → ℝ) :=
        Filter.eventually_of_mem (Ω.isOpen.mem_nhds hy) fun z hz ↦ hψM_eq z hz
      simp only [gradient, hloc.fderiv_eq]
    rw [hu_grad, hψ_grad, ← hgrad_ψ,
      matrixBilinearForm_chartEllipticCoeff_gradient_eq p u ψM (hΩt hy)]

/-- Local chart elliptic data near a point `p ∈ M`: an open coordinate ball `Ω` inside a compact
set `K` in the chart target, uniform ellipticity and boundedness of `chartEllipticCoeff p` on `K`,
lower and upper bounds on the chart density on `K`, and the chart reading map
`T : H¹(M) → W^{1,2}(Ω)` matching the Dirichlet form against transplanted test functions. -/
private structure ChartEllipticData (p : M) where
  Ω : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  lam : ℝ
  Lam : ℝ
  m : ℝ
  Mρ : ℝ
  mem_center : basisEquivEuclidean (extChartAt I p p) ∈ Ω
  subset_K : (Ω : Set _) ⊆ K
  isCompact_K : IsCompact K
  mapsTo_K : MapsTo (basisEquivEuclidean (E := E)).symm K (extChartAt I p).target
  elliptic : TauCeti.PDE.UniformlyEllipticOn K (chartEllipticCoeff (I := I) p) lam Lam
  m_pos : 0 < m
  density_bounds : ∀ y ∈ K, m ≤ chartDensity (I := I) p y ∧ chartDensity (I := I) p y ≤ Mρ
  memLp_energyIntegrand : MemLp
    (fun y ↦ TauCeti.PDE.energyIntegrand (chartEllipticCoeff (I := I) p y) 0 0)
    ⊤ (volume.restrict (Ω : Set _))
  read : SobolevH1 I M →L[ℝ] W1p volume Ω 2
  value_read : ∀ w : SobolevH1 I M,
    W1p.value (read w) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w ((extChartAt I p).symm (basisEquivEuclidean.symm y))
  transplant : ∀ ψ : 𝓓(Ω, ℝ),
    ∃ ψM : C^∞⟮I, M; ℝ⟯,
      (∀ f : M → ℝ, ∫ x, f x * ψM x ∂riemannianVolume I M =
        ∫ y in Ω, (chartDensity (I := I) p y *
          f ((extChartAt I p).symm (basisEquivEuclidean.symm y))) * ψ y ∂volume) ∧
      ∀ w : SobolevH1 I M,
        TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (read w)
          (W1p.ofTestFunctionₗ volume Ω 2 ψ) = dirichletForm w (ofSmooth ψM)

/-- Every point `p ∈ M` admits local chart elliptic data. -/
private theorem nonempty_chartEllipticData (p : M) : Nonempty (ChartEllipticData (I := I) p) := by
  let L := basisEquivEuclidean (E := E)
  obtain ⟨Ω₀, hpΩ₀, hΩ₀t, T₀, hT₀s, hT₀v⟩ :=
    exists_continuousLinearMap_w1p_extChartAt (I := I) (M := M) p L
  obtain ⟨r, hr, hrΩ₀⟩ := nhds_basis_closedBall.mem_iff.1 (Ω₀.isOpen.mem_nhds hpΩ₀)
  let Ω : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ⟨ball (L (extChartAt I p p)) r, isOpen_ball⟩
  let K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := closedBall (L (extChartAt I p p)) r
  have hΩΩ₀ : Ω ≤ Ω₀ := ball_subset_closedBall.trans hrΩ₀
  have hKt : MapsTo L.symm K (extChartAt I p).target := hΩ₀t.mono_left hrΩ₀
  have hΩt : MapsTo L.symm Ω (extChartAt I p).target := hKt.mono_left ball_subset_closedBall
  have hKcomp : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨L (extChartAt I p p), mem_closedBall_self hr.le⟩
  have hcont_a : ContinuousOn (chartEllipticCoeff (I := I) p) K :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
      (contDiffOn_chartEllipticCoeff_entry p i j).continuousOn.mono hKt
  obtain ⟨lam, Lam, haK⟩ := exists_uniformlyEllipticOn_of_continuousOn_pos hKcomp hcont_a
    fun y hy ξ hξ ↦ toQuadraticForm'_chartEllipticCoeff_pos p (hKt hy) hξ
  have hcont_ρ : ContinuousOn (chartDensity (I := I) p) K :=
    (contDiffOn_chartDensity p).continuousOn.mono hKt
  obtain ⟨y_min, hy_min, hmin⟩ := hKcomp.exists_isMinOn hKne hcont_ρ
  obtain ⟨y_max, -, hmax⟩ := hKcomp.exists_isMaxOn hKne hcont_ρ
  have hm_pos : 0 < chartDensity (I := I) p y_min := by
    have hx : (extChartAt I p).symm (L.symm y_min) ∈
        (trivializationAt E (TangentSpace I) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)] using
        (extChartAt I p).map_target (hKt hy_min)
    exact chartVolumeDensity_pos p hx
  have hclosure_sub : closure (Ω : Set _) ⊆ K := Metric.closure_ball_subset_closedBall
  have hcoeff : MemLp (fun y ↦ TauCeti.PDE.energyIntegrand (chartEllipticCoeff (I := I) p y) 0 0)
      ⊤ (volume.restrict (Ω : Set _)) :=
    TauCeti.PDE.memLp_energyIntegrand_of_continuousOn
      (hKcomp.of_isClosed_subset isClosed_closure hclosure_sub)
      (hcont_a.mono hclosure_sub) continuousOn_const continuousOn_const
  let T : SobolevH1 I M →L[ℝ] W1p volume Ω 2 := (W1p.restrictL hΩΩ₀).comp T₀
  have hTval (w : SobolevH1 I M) : W1p.value (T w) =ᵐ[volume.restrict (Ω : Set _)]
      fun y ↦ toLp w ((extChartAt I p).symm (L.symm y)) :=
    (W1p.value_restrictL_ae hΩΩ₀ (T₀ w)).trans
      (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀v w))
  have hTgrad (u : C^∞⟮I, M; ℝ⟯) : W1p.gradient (T (ofSmooth u)) =ᵐ[volume.restrict (Ω : Set _)]
      ∇ fun y ↦ u ((extChartAt I p).symm (L.symm y)) :=
    (W1p.gradient_restrictL_ae hΩΩ₀ (T₀ (ofSmooth u))).trans
      (ae_restrict_of_ae_restrict_of_subset hΩΩ₀ (hT₀s u).2)
  exact ⟨⟨Ω, K, lam, Lam, chartDensity (I := I) p y_min, chartDensity (I := I) p y_max,
    mem_ball_self hr, ball_subset_closedBall, hKcomp, hKt, haK, hm_pos,
    fun y hy ↦ ⟨hmin hy, hmax hy⟩, hcoeff, T, hTval,
    fun ψ ↦ exists_transplant_testFunction p hΩt hcoeff T hTgrad ψ⟩⟩

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Pull a smooth Euclidean representative on a coordinate open set `Ω` back to a smooth
representative on the chart preimage `U ⊆ M` almost everywhere for `riemannianVolume I M`. -/
private theorem pullback_contDiffOn_ae_eq (p : M)
    {Ω : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hpΩ : basisEquivEuclidean (extChartAt I p p) ∈ Ω)
    (hΩt : MapsTo (basisEquivEuclidean (E := E)).symm Ω (extChartAt I p).target)
    {w : SobolevH1 I M} {v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω)
    (hae : (fun y ↦ toLp w ((extChartAt I p).symm (basisEquivEuclidean.symm y)))
      =ᵐ[volume.restrict (Ω : Set _)] v) :
    ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (g : M → ℝ),
      ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] g := by
  let L := basisEquivEuclidean (E := E)
  let U : Set M := (extChartAt I p).source ∩ extChartAt I p ⁻¹' (L ⁻¹' (Ω : Set _))
  let g : M → ℝ := fun x ↦ v (L (extChartAt I p x))
  have hLΩ_open : IsOpen (L ⁻¹' (Ω : Set _)) := Ω.isOpen.preimage L.continuous
  have hLΩ_sub : L ⁻¹' (Ω : Set _) ⊆ (extChartAt I p).target := fun z hz ↦ by
    simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using hΩt hz
  have hU_open : IsOpen U := isOpen_extChartAt_preimage' p hLΩ_open
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, hpΩ⟩
  have hg : ContMDiffOn I 𝓘(ℝ) ∞ g U := by
    have hcomp : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞
        (fun x ↦ L (extChartAt I p x)) U :=
      L.contDiff.contMDiff.comp_contMDiffOn
        ((contMDiffOn_extChartAt (I := I) (x := p)).mono fun x hx ↦
          (extChartAt_source I p).subset hx.1)
    exact hv.contMDiffOn.comp hcomp fun x hx ↦ hx.2
  -- Show `∫⁻_{U} edist (toLp w x) (g x) dV = 0` by changing to Euclidean coordinates.
  have hlint : ∫⁻ x in U, edist (toLp w x) (g x) ∂riemannianVolume I M = 0 := by
    rw [setLIntegral_riemannianVolume_inter_preimage p hLΩ_open hLΩ_sub]
    have hmp : MeasurePreserving L.symm volume (Module.finBasis ℝ E).addHaar :=
      measurePreserving_basisEquivEuclidean_symm (E := E)
    have hemb : MeasurableEmbedding (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
      L.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hpre : L.symm ⁻¹' (L ⁻¹' (Ω : Set _)) = (Ω : Set _) := by
      ext y
      simp [L]
    rw [← hmp.setLIntegral_comp_preimage_emb hemb, hpre]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_restrict_mem Ω.isOpen.measurableSet] with y hy hyΩ
    dsimp only [g, Pi.zero_apply]
    rw [(extChartAt I p).right_inv (hΩt hyΩ), L.apply_symm_apply, hy, edist_self, mul_zero]
  have hmeas : AEMeasurable (fun x ↦ edist (toLp w x) (g x)) ((riemannianVolume I M).restrict U) :=
    ((Lp.aestronglyMeasurable (toLp w)).mono_measure Measure.restrict_le_self).edist
      (hg.continuousOn.aestronglyMeasurable hU_open.measurableSet)
  refine ⟨U, hU_open, hpU, g, hg, ?_⟩
  filter_upwards [(lintegral_eq_zero_iff' hmeas).1 hlint] with x hx
  exact edist_eq_zero.1 hx

/-- **Gluing local smooth representatives on a compact manifold.** If `w ∈ H¹(M)` agrees almost
everywhere with a smooth function near every point of `M`, then `w = ofSmooth u` for a globally
smooth function `u : C^∞(M)`. -/
private theorem exists_ofSmooth_eq_of_locally_contMDiffOn {w : SobolevH1 I M}
    (hloc : ∀ p : M, ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (g : M → ℝ),
      ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] g) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  choose U hUopen hpU g hg hae using hloc
  -- On every overlap `U p ∩ U q`, the continuous representatives `g p` and `g q` coincide.
  have hoverlap (p q : M) : EqOn (g p) (g q) (U p ∩ U q) := by
    have h1 : (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (U p ∩ U q)] g p :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae p)
    have h2 : (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (U p ∩ U q)] g q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae q)
    exact Measure.eqOn_open_of_ae_eq (h1.symm.trans h2) ((hUopen p).inter (hUopen q))
      ((hg p).continuousOn.mono inter_subset_left)
      ((hg q).continuousOn.mono inter_subset_right)
  let u_fun : M → ℝ := fun x ↦ g x x
  have hgu (p : M) : EqOn (g p) u_fun (U p) := fun x hx ↦ hoverlap p x ⟨hx, hpU x⟩
  have hu_smooth : ContMDiff I 𝓘(ℝ) ∞ u_fun := fun p ↦
    ((hg p).contMDiffAt ((hUopen p).mem_nhds (hpU p))).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((hUopen p).mem_nhds (hpU p)) fun x hx ↦ (hgu p hx).symm)
  let u : C^∞⟮I, M; ℝ⟯ := ⟨u_fun, hu_smooth⟩
  -- Cover the compact manifold `M` by finitely many of the open sets `U p`.
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U fun p ↦ (hUopen p).mem_nhds (hpU p)
  have hae_global : (toLp w : M → ℝ) =ᵐ[riemannianVolume I M] u := by
    rw [Filter.EventuallyEq, ae_iff]
    have hsub : {x : M | ¬toLp w x = u x} ⊆ ⋃ p ∈ s, ({x : M | ¬toLp w x = u x} ∩ U p) := by
      intro x hx
      have hx' : x ∈ ⋃ p ∈ s, U p := hs.symm ▸ mem_univ x
      rw [mem_iUnion₂] at hx' ⊢
      obtain ⟨p, hp, hxp⟩ := hx'
      exact ⟨p, hp, hx, hxp⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff s.countable_toSet).2 fun p _ ↦ ?_)
    have hpu : (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict (U p)] u := by
      filter_upwards [hae p, ae_restrict_mem (hUopen p).measurableSet] with x hx hxp
      exact hx.trans (hgu p hxp)
    rw [Filter.EventuallyEq, ae_restrict_iff' (hUopen p).measurableSet, ae_iff] at hpu
    convert hpu using 2
    ext x
    simp [and_comm]
  refine ⟨u, toLp_injective (Lp.ext (hae_global.trans (toLp_ofSmooth_ae_eq u).symm))⟩

/-- **Pointwise classical equation from a smooth weak solution.** If `u` and `F` are smooth and
`D(u, v) = ∫ F v dV` for every smooth `v`, then `-Δu = F` everywhere on `M`. -/
private theorem neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq
    (u : C^∞⟮I, M; ℝ⟯) {F : M → ℝ} (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (hu : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm (ofSmooth u) (ofSmooth v) = ∫ x, F x * v x ∂riemannianVolume I M) (x : M) :
    -laplaceBeltrami I u x = F x := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hΔ : ContMDiff I 𝓘(ℝ) ∞ (laplaceBeltrami I u) :=
    contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp)
      (u.contMDiff.of_le (by simp))
  let r : C^∞⟮I, M; ℝ⟯ := ⟨fun y ↦ -laplaceBeltrami I u y - F y, hΔ.neg.sub hF⟩
  have hr_apply (y : M) : r y = -laplaceBeltrami I u y - F y := rfl
  have hr_eq := hu r
  rw [dirichletForm_comm, dirichletForm_ofSmooth_right] at hr_eq
  have hlhs : ∫ y, toLp (ofSmooth r) y * -laplaceBeltrami I u y ∂riemannianVolume I M =
      ∫ y, r y * -laplaceBeltrami I u y ∂riemannianVolume I M :=
    integral_congr_ae ((toLp_ofSmooth_ae_eq r).mono fun y hy ↦ by dsimp only; rw [hy])
  rw [hlhs] at hr_eq
  have hint1 : Integrable (fun y ↦ r y * -laplaceBeltrami I u y) (riemannianVolume I M) :=
    ((map_continuous r).mul hΔ.continuous.neg).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hint2 : Integrable (fun y ↦ F y * r y) (riemannianVolume I M) :=
    (hF.continuous.mul (map_continuous r)).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hsq_zero : ∫ y, r y ^ 2 ∂riemannianVolume I M = 0 := by
    have hsub : ∫ y, (r y * -laplaceBeltrami I u y - F y * r y) ∂riemannianVolume I M = 0 := by
      rw [integral_sub hint1 hint2, hr_eq, sub_self]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)).symm.trans hsub
    rw [hr_apply]
    ring
  have hae : (fun y ↦ r y ^ 2) =ᵐ[riemannianVolume I M] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y ↦ sq_nonneg _)
      (((map_continuous r).pow 2).integrable_of_hasCompactSupport (.of_compactSpace _))).1 hsq_zero
  have hall : (fun y ↦ r y ^ 2) = 0 :=
    ((map_continuous r).pow 2).ae_eq_iff_eq (riemannianVolume I M) continuous_const |>.1 hae
  have hrx : r x = 0 := sq_eq_zero_iff.1 (congrFun hall x)
  exact sub_eq_zero.1 hrx

/-! ### Linear elliptic regularity -/

/-- Local chart smoothness step for linear elliptic equations `Δ⁺w + c w = f`. -/
private theorem locally_contMDiffOn_of_linear
    {c f : M → ℝ} (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : SobolevH1 I M}
    (hw : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth v) + ∫ x, c x * toLp w x * v x ∂riemannianVolume I M =
        ∫ x, f x * v x ∂riemannianVolume I M) (p : M) :
    ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (g : M → ℝ),
      ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] g := by
  let L := basisEquivEuclidean (E := E)
  obtain ⟨d⟩ := nonempty_chartEllipticData (I := I) (M := M) p
  have hΩt : MapsTo L.symm d.Ω (extChartAt I p).target := d.mapsTo_K.mono_left d.subset_K
  have haΩ : TauCeti.PDE.UniformlyEllipticOn (d.Ω : Set _) (chartEllipticCoeff (I := I) p)
      d.lam d.Lam := d.elliptic.mono_set d.subset_K
  let cChart : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun y ↦ chartDensity (I := I) p y * c ((extChartAt I p).symm (L.symm y))
  let fChart : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun y ↦ chartDensity (I := I) p y * f ((extChartAt I p).symm (L.symm y))
  have hcChart_smooth : ContDiffOn ℝ ∞ cChart (L.symm ⁻¹' (extChartAt I p).target) :=
    (contDiffOn_chartDensity p).mul (contDiffOn_comp_extChartAt_symm p hc.contMDiffOn)
  have hfChart_smooth : ContDiffOn ℝ ∞ fChart (L.symm ⁻¹' (extChartAt I p).target) :=
    (contDiffOn_chartDensity p).mul (contDiffOn_comp_extChartAt_symm p hf.contMDiffOn)
  -- Verify the chart test-function equation for the principal part with forcing
  -- `fChart - cChart * (d.read w)`.
  have htest : ∀ ψ : 𝓓(d.Ω, ℝ),
      TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (d.read w)
        (W1p.ofTestFunctionₗ volume d.Ω 2 ψ) =
      ∫ y in d.Ω, (fChart y - cChart y * W1p.value (d.read w) y) * ψ y ∂volume := by
    intro ψ
    obtain ⟨ψM, hψM_int, hψM_form⟩ := d.transplant ψ
    have hint_f : Integrable (fun x ↦ f x * ψM x) (riemannianVolume I M) :=
      (hf.continuous.mul (map_continuous ψM)).integrable_of_hasCompactSupport (.of_compactSpace _)
    have hint_c : Integrable (fun x ↦ c x * toLp w x * ψM x) (riemannianVolume I M) := by
      have hcont : Continuous fun x ↦ c x * ψM x := hc.continuous.mul (map_continuous ψM)
      have hmem : MemLp (fun x ↦ c x * ψM x) 2 (riemannianVolume I M) :=
        (Lp.memLp (ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨_, hcont⟩)).ae_eq
          (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M) ⟨_, hcont⟩)
      refine (hmem.integrable_mul (Lp.memLp (toLp w))).congr
        (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply]
      ring
    have hdir : dirichletForm w (ofSmooth ψM) =
        ∫ x, (f x - c x * toLp w x) * ψM x ∂riemannianVolume I M := by
      have hsub : ∫ x, (f x - c x * toLp w x) * ψM x ∂riemannianVolume I M =
          (∫ x, f x * ψM x ∂riemannianVolume I M) -
            ∫ x, c x * toLp w x * ψM x ∂riemannianVolume I M := by
        simp_rw [sub_mul]
        exact integral_sub hint_f hint_c
      linarith [hw ψM, hsub]
    rw [hψM_form w, hdir, hψM_int]
    refine integral_congr_ae ?_
    filter_upwards [d.value_read w] with y hy
    dsimp only [fChart, cChart]
    rw [hy]
    ring
  -- Extend from test functions to all `v ∈ H¹₀(d.Ω)` and move `cChart` back into the energy form.
  have hfChart_lp : MemLp fChart 2 (volume.restrict (d.Ω : Set _)) :=
    ContinuousOn.memLp_restrict_of_subset_isCompact
      (hfChart_smooth.continuousOn.mono d.mapsTo_K) d.isCompact_K d.Ω.isOpen.measurableSet
      d.subset_K 2
  obtain ⟨Mc, hMc⟩ :=
    d.isCompact_K.exists_bound_of_continuousOn (hcChart_smooth.continuousOn.mono d.mapsTo_K)
  have hcChart_meas : AEStronglyMeasurable cChart (volume.restrict (d.Ω : Set _)) :=
    (hcChart_smooth.continuousOn.mono hΩt).aestronglyMeasurable d.Ω.isOpen.measurableSet
  have hcChart_bdd : ∀ᵐ y ∂volume.restrict (d.Ω : Set _), ‖cChart y‖ ≤ Mc :=
    (ae_restrict_mem d.Ω.isOpen.measurableSet).mono fun y hy ↦ hMc y (d.subset_K hy)
  have hcChartw_lp : MemLp (fun y ↦ cChart y * W1p.value (d.read w) y) 2
      (volume.restrict (d.Ω : Set _)) :=
    MemLp.of_le_mul (Lp.memLp (W1p.value (d.read w))) (c := Mc)
      (hcChart_meas.mul (Lp.aestronglyMeasurable _))
      (hcChart_bdd.mono fun y hy ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  have hW1p0 : ∀ v : W1p0 volume d.Ω 2,
      TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 cChart (d.read w)
        (v : W1p volume d.Ω 2) =
        ∫ y in d.Ω, fChart y * W1p.value (v : W1p volume d.Ω 2) y ∂volume :=
    forall_energyFormH1_mass_eq_setIntegral d.memLp_energyIntegrand hfChart_lp hcChartw_lp htest
  -- Apply Euclidean interior smoothness on `d.Ω`.
  have hfChart_wkp : ∀ y ∈ d.Ω, ∃ V : Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), y ∈ V ∧
      ∀ k, ∃ F : Wkp volume V 2 k, (Wkp.value k F : _ → ℝ) =ᵐ[volume.restrict (V : Set _)] fChart :=
    fun y hy ↦ ⟨d.Ω, hy, fun k ↦
      Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact k
        ((isOpen_extChartAt_target p).preimage L.symm.continuous)
        (hfChart_smooth.of_le (by exact_mod_cast le_top)) d.isCompact_K d.subset_K d.mapsTo_K⟩
  obtain ⟨v, hv_smooth, hv_ae⟩ := haΩ.exists_contDiffOn_ae_eq_of_contDiffOn
    (fun i j ↦ (contDiffOn_chartEllipticCoeff_entry p i j).mono hΩt)
    contDiffOn_const (hcChart_smooth.mono hΩt) hfChart_wkp hW1p0
  exact pullback_contDiffOn_ae_eq p d.mem_center hΩt hv_smooth
    ((d.value_read w).symm.trans hv_ae)

/-- **Smoothness of weak solutions of linear elliptic equations on a closed manifold.** On a
closed Hausdorff smooth Riemannian manifold of any dimension, let `c` and `f` be smooth functions.
If `w ∈ H¹(M)` solves `Δ⁺w + c w = f` weakly against smooth test functions, then `w = ofSmooth u`
for a smooth function `u` satisfying `-Δu + c u = f` everywhere. -/
theorem exists_ofSmooth_eq_and_neg_laplaceBeltrami_add_mul_eq
    {c f : M → ℝ} (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : SobolevH1 I M}
    (hw : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth v) + ∫ x, c x * toLp w x * v x ∂riemannianVolume I M =
        ∫ x, f x * v x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧
      ∀ x, -laplaceBeltrami I u x + c x * u x = f x := by
  obtain ⟨u, rfl⟩ := exists_ofSmooth_eq_of_locally_contMDiffOn
    (locally_contMDiffOn_of_linear hc hf hw)
  refine ⟨u, rfl, fun x ↦ ?_⟩
  have hpt : -laplaceBeltrami I u x = f x - c x * u x := by
    refine neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq u
      (F := fun y ↦ f y - c y * u y) (hf.sub (hc.mul u.contMDiff)) (fun v ↦ ?_) x
    have hint_f : Integrable (fun y ↦ f y * v y) (riemannianVolume I M) :=
      (hf.continuous.mul (map_continuous v)).integrable_of_hasCompactSupport (.of_compactSpace _)
    have hint_c : Integrable (fun y ↦ c y * u y * v y) (riemannianVolume I M) :=
      ((hc.continuous.mul (map_continuous u)).mul
        (map_continuous v)).integrable_of_hasCompactSupport (.of_compactSpace _)
    have hc_eq : ∫ y, c y * toLp (ofSmooth u) y * v y ∂riemannianVolume I M =
        ∫ y, c y * u y * v y ∂riemannianVolume I M :=
      integral_congr_ae ((toLp_ofSmooth_ae_eq u).mono fun y hy ↦ by dsimp only; rw [hy])
    have hsub : ∫ y, (f y - c y * u y) * v y ∂riemannianVolume I M =
        (∫ y, f y * v y ∂riemannianVolume I M) - ∫ y, c y * u y * v y ∂riemannianVolume I M := by
      simp_rw [sub_mul]
      exact integral_sub hint_f hint_c
    linarith [hw v, hc_eq, hsub]
  linarith

/-- **Smoothness of weak solutions of the Poisson equation on a closed manifold.** On a closed
Hausdorff smooth Riemannian manifold of any dimension, if `f` is smooth and `w ∈ H¹(M)` solves
`Δ⁺w = f` weakly against smooth test functions, then `w = ofSmooth u` for a smooth function `u`
satisfying `-Δu = f` everywhere. -/
theorem exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {w : SobolevH1 I M}
    (hw : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth v) = ∫ x, f x * v x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  simpa using exists_ofSmooth_eq_and_neg_laplaceBeltrami_add_mul_eq (c := 0) contMDiff_const hf
    (fun v ↦ by simpa using hw v)

/-! ### Semilinear elliptic regularity -/

/-- Local chart smoothness step for semilinear elliptic equations `Δ⁺w = A Φ(w) + C` in dimension
at most three. -/
private theorem locally_contMDiffOn_of_semilinear
    (hE : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hF : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth v) =
        ∫ x, (A x * Φ (toLp w x) + C x) * v x ∂riemannianVolume I M) (p : M) :
    ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (g : M → ℝ),
      ContMDiffOn I 𝓘(ℝ) ∞ g U ∧
      (toLp w : M → ℝ) =ᵐ[(riemannianVolume I M).restrict U] g := by
  let L := basisEquivEuclidean (E := E)
  obtain ⟨d⟩ := nonempty_chartEllipticData (I := I) (M := M) p
  have hΩt : MapsTo L.symm d.Ω (extChartAt I p).target := d.mapsTo_K.mono_left d.subset_K
  have haΩ : TauCeti.PDE.UniformlyEllipticOn (d.Ω : Set _) (chartEllipticCoeff (I := I) p)
      d.lam d.Lam := d.elliptic.mono_set d.subset_K
  let AChart : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun y ↦ chartDensity (I := I) p y * A ((extChartAt I p).symm (L.symm y))
  let CChart : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun y ↦ chartDensity (I := I) p y * C ((extChartAt I p).symm (L.symm y))
  have hAChart : ContDiffOn ℝ ∞ AChart d.Ω :=
    ((contDiffOn_chartDensity p).mul (contDiffOn_comp_extChartAt_symm p hA.contMDiffOn)).mono hΩt
  have hCChart : ContDiffOn ℝ ∞ CChart d.Ω :=
    ((contDiffOn_chartDensity p).mul (contDiffOn_comp_extChartAt_symm p hC.contMDiffOn)).mono hΩt
  -- Square integrability of the chart forcing on `d.Ω` from `hF` on `M`.
  have hFΩ : MemLp (fun y ↦ AChart y * Φ (W1p.value (d.read w) y) + CChart y) 2
      (volume.restrict (d.Ω : Set _)) := by
    have hmeas : AEStronglyMeasurable (fun y ↦ AChart y * Φ (W1p.value (d.read w) y) + CChart y)
        (volume.restrict (d.Ω : Set _)) :=
      ((hAChart.continuousOn.aestronglyMeasurable d.Ω.isOpen.measurableSet).mul
        (hΦ.continuous.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable (W1p.value (d.read w))))).add
        (hCChart.continuousOn.aestronglyMeasurable d.Ω.isOpen.measurableSet)
    let F : M → ℝ := fun x ↦ A x * Φ (toLp w x) + C x
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
      (by norm_num) ENNReal.ofNat_ne_top hmeas]
    simp only [ENNReal.toReal_ofNat]
    have hF_fin : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M < ⊤ := by
      simpa only [ENNReal.toReal_ofNat] using
        lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
          (by norm_num) ENNReal.ofNat_ne_top hF.eLpNorm_lt_top
    have hLΩ_open : IsOpen (L ⁻¹' (d.Ω : Set _)) := d.Ω.isOpen.preimage L.continuous
    have hLΩ_sub : L ⁻¹' (d.Ω : Set _) ⊆ (extChartAt I p).target := fun z hz ↦ by
      simpa only [L, ContinuousLinearEquiv.symm_apply_apply] using hΩt hz
    have hmp : MeasurePreserving L.symm volume (Module.finBasis ℝ E).addHaar :=
      measurePreserving_basisEquivEuclidean_symm (E := E)
    have hemb : MeasurableEmbedding (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
      L.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hpre : L.symm ⁻¹' (L ⁻¹' (d.Ω : Set _)) = (d.Ω : Set _) := by
      ext y
      simp [L]
    calc ∫⁻ y in d.Ω, ‖AChart y * Φ (W1p.value (d.read w) y) + CChart y‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ y in d.Ω, ENNReal.ofReal d.Mρ ^ (2 : ℝ) *
            ‖F ((extChartAt I p).symm (L.symm y))‖ₑ ^ (2 : ℝ) ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [d.value_read w, ae_restrict_mem d.Ω.isOpen.measurableSet] with y hy hyΩ
          have hrewrite : AChart y * Φ (W1p.value (d.read w) y) + CChart y =
              chartDensity (I := I) p y * F ((extChartAt I p).symm (L.symm y)) := by
            dsimp only [AChart, CChart, F]
            rw [hy]
            ring
          rw [hrewrite, eNorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          gcongr
          have hρ_le := (d.density_bounds y (d.subset_K hyΩ)).2
          have hρ_nn : 0 ≤ chartDensity (I := I) p y :=
            chartVolumeDensity_nonneg (I := I) p ((extChartAt I p).symm (L.symm y))
          rw [Real.eNorm_eq_ofReal hρ_nn]
          exact ENNReal.ofReal_le_ofReal hρ_le
      _ = ENNReal.ofReal d.Mρ ^ (2 : ℝ) *
            ∫⁻ y in d.Ω, ‖F ((extChartAt I p).symm (L.symm y))‖ₑ ^ (2 : ℝ) ∂volume :=
          lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            ENNReal.ofReal_ne_top).ne
      _ = ENNReal.ofReal d.Mρ ^ (2 : ℝ) *
            ∫⁻ z in L ⁻¹' (d.Ω : Set _), ‖F ((extChartAt I p).symm z)‖ₑ ^ (2 : ℝ)
              ∂(Module.finBasis ℝ E).addHaar := by
          congr 1
          rw [← hmp.setLIntegral_comp_preimage_emb hemb, hpre]
      _ ≤ ENNReal.ofReal d.Mρ ^ (2 : ℝ) *
            (ENNReal.ofReal d.m⁻¹ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂riemannianVolume I M) := by
          gcongr
          refine setLIntegral_comp_extChartAt_symm_le_mul_lintegral p hLΩ_open hLΩ_sub d.m_pos
            (fun z hz ↦ ?_) (fun x ↦ ‖F x‖ₑ ^ (2 : ℝ))
          have hmem : L z ∈ d.K := d.subset_K hz
          simpa only [chartDensity, L, ContinuousLinearEquiv.symm_apply_apply] using
            (d.density_bounds (L z) hmem).1
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF_fin)
  -- Test-function weak equation in the chart.
  have htest : ∀ ψ : 𝓓(d.Ω, ℝ),
      TauCeti.PDE.energyFormH1 (chartEllipticCoeff (I := I) p) 0 0 (d.read w)
        (W1p.ofTestFunctionₗ volume d.Ω 2 ψ) =
      ∫ y in d.Ω, (AChart y * Φ (W1p.value (d.read w) y) + CChart y) * ψ y ∂volume := by
    intro ψ
    obtain ⟨ψM, hψM_int, hψM_form⟩ := d.transplant ψ
    rw [hψM_form w, hw ψM, hψM_int]
    refine integral_congr_ae ?_
    filter_upwards [d.value_read w] with y hy
    dsimp only [AChart, CChart]
    rw [hy]
    ring
  obtain ⟨v, hv_smooth, hv_ae⟩ :=
    haΩ.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq
      (by simpa using hE)
      (fun i j ↦ (contDiffOn_chartEllipticCoeff_entry p i j).mono hΩt) hAChart hCChart hΦ
      (fun _ _ hsub ↦ hFΩ.mono_measure (Measure.restrict_mono hsub le_rfl)) htest
  exact pullback_contDiffOn_ae_eq p d.mem_center hΩt hv_smooth
    ((d.value_read w).symm.trans hv_ae)

/-- **Smoothness of weak solutions of semilinear elliptic equations on a closed manifold.** On a
closed Hausdorff smooth Riemannian manifold of dimension at most three, let `A`, `C` and `Φ` be
smooth. If `w ∈ H¹(M)` solves `Δ⁺w = A Φ(w) + C` weakly against smooth test functions and the
nonlinear forcing `A Φ(w) + C` is square integrable on `M`, then `w = ofSmooth u` for a smooth
function `u` satisfying `-Δu = A Φ(u) + C` everywhere. -/
theorem exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq_mul_comp_add
    (hE : Module.finrank ℝ E < 4)
    {A C : M → ℝ} (hA : ContMDiff I 𝓘(ℝ) ∞ A) (hC : ContMDiff I 𝓘(ℝ) ∞ C)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {w : SobolevH1 I M}
    (hF : MemLp (fun x ↦ A x * Φ (toLp w x) + C x) 2 (riemannianVolume I M))
    (hw : ∀ v : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth v) =
        ∫ x, (A x * Φ (toLp w x) + C x) * v x ∂riemannianVolume I M) :
    ∃ u : C^∞⟮I, M; ℝ⟯, w = ofSmooth u ∧
      ∀ x, -laplaceBeltrami I u x = A x * Φ (u x) + C x := by
  obtain ⟨u, rfl⟩ := exists_ofSmooth_eq_of_locally_contMDiffOn
    (locally_contMDiffOn_of_semilinear hE hA hC hΦ hF hw)
  refine ⟨u, rfl, ?_⟩
  have hFu : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ A x * Φ (u x) + C x :=
    (hA.mul (hΦ.contMDiff.comp u.contMDiff)).add hC
  refine neg_laplaceBeltrami_eq_of_forall_dirichletForm_ofSmooth_eq u hFu fun v ↦ ?_
  rw [hw v]
  exact integral_congr_ae ((toLp_ofSmooth_ae_eq u).mono fun x hx ↦ by dsimp only; rw [hx])

end LocalBridge

end TauCeti.Manifold.SobolevH1

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M]
  [PreconnectedSpace M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected smooth Riemannian
manifold of any dimension, for every smooth function `f` with `∫ f dV = 0`, there is a unique
smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`, where `Δ⁺ = -div grad` is the nonnegative
Laplacian. -/
theorem existsUnique_contMDiff_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      ∫ x, u x ∂riemannianVolume I M = 0 ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  set F : Lp ℝ 2 (riemannianVolume I M) :=
    ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨f, hf.continuous⟩
  have hF_ae : (F : M → ℝ) =ᵐ[riemannianVolume I M] f :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M) ⟨f, hf.continuous⟩
  have hF0 : ∫ x, F x ∂riemannianVolume I M = 0 := (integral_congr_ae hF_ae).trans hf0
  obtain ⟨w, ⟨hw0, hw⟩, huniq⟩ := SobolevH1.existsUnique_dirichletForm_eq F hF0
  obtain ⟨u, rfl, hu⟩ := SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq hf fun v ↦ by
    rw [hw (SobolevH1.ofSmooth v)]
    refine integral_congr_ae ?_
    filter_upwards [hF_ae, SobolevH1.toLp_ofSmooth_ae_eq v] with x hFx hvx
    rw [hFx, hvx]
  refine ⟨u, ⟨u.contMDiff, (integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq u)).symm.trans hw0,
    hu⟩, fun u' ⟨hu'_smooth, hu'0, hu'⟩ ↦ ?_⟩
  set u'm : C^∞⟮I, M; ℝ⟯ := ⟨u', hu'_smooth⟩
  have hofSmooth : SobolevH1.ofSmooth u'm = SobolevH1.ofSmooth u := by
    refine huniq (SobolevH1.ofSmooth u'm) ⟨?_, fun v ↦ ?_⟩
    · exact (integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq u'm)).trans hu'0
    · rw [SobolevH1.dirichletForm_comm, SobolevH1.dirichletForm_ofSmooth_right]
      refine integral_congr_ae ?_
      filter_upwards [hF_ae] with x hFx
      rw [hFx, ← hu' x, mul_comm]
      rfl
  have hae : u' =ᵐ[riemannianVolume I M] u :=
    (SobolevH1.toLp_ofSmooth_ae_eq u'm).symm.trans
      (hofSmooth ▸ SobolevH1.toLp_ofSmooth_ae_eq u)
  exact (hu'_smooth.continuous.ae_eq_iff_eq (riemannianVolume I M) (map_continuous u)).1 hae

end TauCeti.Manifold
