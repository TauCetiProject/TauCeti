/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.SmoothSingular.Reparametrization
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.AlgebraicTopology.Singular.Subdivision.FullSimplex
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.NormDet
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.MeasureTheory.Integral.FullSimplex
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# Parametrized Riemannian mass of smooth singular simplices

On a manifold `M` equipped with a Riemannian bundle
`RiemannianBundle (fun x : M ↦ TangentSpace I x)`, the **parametrized mass** of a smooth singular
`p`-simplex `σ : SmoothSimplex I M p` is the integral over the full-dimensional standard simplex
`Δᵖ ⊆ ℝᵖ` of the `p`-dimensional Jacobian `LinearMap.normDet` of its differential within `Δᵖ`:

`σ.mass = ∫ x in Δᵖ, LinearMap.normDet (mfderivWithin σ.extension Δᵖ x)`.

Because `Δᵖ` has unique derivatives at every point (`TauCeti.uniqueDiffOn_fullSimplex`), the
integrand depends only on the values of `σ` on `Δᵖ`, agrees with the Riemannian Jacobian of any
local smooth extension, and is continuous (hence integrable) whenever `M` is `C¹` and the metric
is continuous (`SmoothSimplex.continuousOn_normDet_mfderivWithin`,
`SmoothSimplex.integrableOn_normDet_mfderivWithin`).

This is the parametrized mass, which counts multiplicity and folding rather than passing to the
image set: for example, the folded `1`-simplex `t ↦ 4 * t * (1 - t)` tracing `[0, 1]` back and
forth has mass `2` (`SmoothSimplex.mass_ofCurve_folded`) while its range is `[0, 1]`
(`SmoothSimplex.range_toContinuousMap_ofCurve_folded`) and its oriented integral of `dt` vanishes
(`SmoothSimplex.integral_ofCurve_folded_realLineCoordForm`).

## Main definitions and results

* `TauCeti.SmoothSimplex.mass`: the parametrized Riemannian mass of a smooth `p`-simplex.
* `TauCeti.SmoothSimplex.continuousOn_normDet_mfderivWithin`,
  `TauCeti.SmoothSimplex.integrableOn_normDet_mfderivWithin`: continuity and integrability of the
  Jacobian integrand on `Δᵖ`.
* `TauCeti.SmoothSimplex.mass_zero_dim`, `TauCeti.SmoothSimplex.mass_eq_zero_of_const`,
  `TauCeti.SmoothSimplex.mass_σ`: degree-`0`, constant, and degenerate simplex masses.
* `TauCeti.SmoothSimplex.mass_ofCurve`, `TauCeti.SmoothSimplex.mass_ofCurve_real`,
  `TauCeti.SmoothSimplex.mass_ofCurve_const_mul`, `TauCeti.SmoothSimplex.mass_ofCurve_folded`:
  arc-length formula for smooth `1`-simplices, linear scaling, and folded-curve check on `ℝ`.
* `TauCeti.SmoothSimplex.mass_smoothSingularSubcomplexMap_app_le`,
  `TauCeti.SmoothSimplex.mass_smoothSingularSubcomplexMap_riemannianIsometry`: functoriality
  under Lipschitz smooth maps and invariance under Riemannian isometries.
* `TauCeti.SmoothSimplex.mass_compContDiffOn`, `TauCeti.SmoothSimplex.mass_compPerm`:
  invariance of simplex mass under smooth bijective reparametrizations and vertex permutations.
* `TauCeti.SmoothSimplex.abs_mpullbackWithin_riemannianVolumeForm`,
  `TauCeti.SmoothSimplex.integral_riemannianVolumeForm_eq_mass`,
  `TauCeti.SmoothSimplex.integral_riemannianVolumeForm_eq_neg_mass`: top-degree comparison with
  the Riemannian volume form.
* `TauCeti.SmoothSimplex.sum_mass_compAffineMapMk_vertex`: barycentric subdivision preserves
  simplex mass.
* `TauCeti.SmoothSimplex.norm_mpullbackWithin_le_opNorm_mul_normDet`,
  `TauCeti.SmoothSimplex.norm_integral_le_mul_mass`,
  `TauCeti.SmoothSimplex.abs_integral_le_mass_of_orthonormal`: pointwise and integrated comass
  bounds without finite-dimensionality assumptions on the model space.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969, §§1.8.1, 4.1.7.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18.
-/

public section

noncomputable section

open Bundle
open CategoryTheory Convexity MeasureTheory Set Simplicial Opposite Topology
open scoped BigOperators ContDiff InnerProductSpace Manifold

universe u

namespace TauCeti

/-! ### Private linear-algebra and derivative helpers -/

section Helpers

private theorem normDet_comp_le_pow_mul {U V W : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (f : U →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) {C : ℝ} (hC : 0 ≤ C) (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖) :
    (g ∘ₗ f).normDet ≤ C ^ Module.finrank ℝ U * f.normDet := by
  by_cases hker : f.ker = ⊥
  · rw [LinearMap.normDet_comp]
    refine mul_le_mul_of_nonneg_right ?_ f.normDet_nonneg
    have hrank : Module.finrank ℝ f.range = Module.finrank ℝ U :=
      (f.normDet_ne_zero_tfae.out 2 3).mp hker
    let b := stdOrthonormalBasis ℝ f.range
    have hsq : (g.domRestrict f.range).normDet ^ 2 ≤ (C ^ Module.finrank ℝ U) ^ 2 := by
      have hgram := (g.domRestrict f.range).normDet_sq_eq_det_gram b
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hgram
      rw [hgram]
      have hbound : ∀ i : Fin (Module.finrank ℝ f.range),
          ‖(g.domRestrict f.range) (b i)‖ ^ 2 ≤ C ^ 2 := fun i ↦ by
        have h1 : ‖g (b i : V)‖ ≤ C * ‖(b i : V)‖ := hg (b i : V)
        have hnorm : ‖(b i : V)‖ = 1 := b.orthonormal.1 i
        rw [hnorm, mul_one] at h1
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hhad := Matrix.re_det_gram_le_pow (𝕜 := ℝ) hbound
      simp only [RCLike.re_to_real, Fintype.card_fin, hrank] at hhad
      simpa only [← pow_mul, mul_comm 2] using hhad
    exact (sq_le_sq₀ (LinearMap.normDet_nonneg _) (pow_nonneg hC _)).mp hsq
  · have hgf : (g ∘ₗ f).ker ≠ ⊥ := by
      contrapose hker with hbot
      simpa [hbot] using LinearMap.ker_le_ker_comp f g
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hgf,
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hker, mul_zero]

private theorem normDet_comp_of_inner_eq {U V W : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (f : U →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) (hg : ∀ v w, inner ℝ (g v) (g w) = inner ℝ v w) :
    (g ∘ₗ f).normDet = f.normDet := by
  let b := stdOrthonormalBasis ℝ U
  have h1 := (g ∘ₗ f).normDet_sq_eq_det_gram b
  have h2 := f.normDet_sq_eq_det_gram b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h1 h2
  have hsq : (g ∘ₗ f).normDet ^ 2 = f.normDet ^ 2 := by
    rw [h1, h2]
    congr 1
    ext i j
    simp [Matrix.gram_apply, hg]
  exact (sq_eq_sq₀ (LinearMap.normDet_nonneg _) (LinearMap.normDet_nonneg _)).mp hsq

private theorem normDet_mfderivWithin_congr {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    {s : Set U} {f₁ f₂ : U → M} {x : U} (hL : f₁ =ᶠ[𝓝[s] x] f₂) (hx : x ∈ s) :
    LinearMap.normDet (U := U) (mfderivWithin 𝓘(ℝ, U) I f₁ s x).toLinearMap =
      LinearMap.normDet (U := U) (mfderivWithin 𝓘(ℝ, U) I f₂ s x).toLinearMap := by
  have heq : f₁ x = f₂ x := mem_of_mem_nhdsWithin hx hL
  have hmf := hL.mfderivWithin_eq_of_mem (I := 𝓘(ℝ, U)) (I' := I) hx
  let b := stdOrthonormalBasis ℝ U
  have h1 := LinearMap.normDet_sq_eq_det_gram (U := U)
    (mfderivWithin 𝓘(ℝ, U) I f₁ s x).toLinearMap b
  have h2 := LinearMap.normDet_sq_eq_det_gram (U := U)
    (mfderivWithin 𝓘(ℝ, U) I f₂ s x).toLinearMap b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h1 h2
  have hsq :
      (LinearMap.normDet (U := U) (mfderivWithin 𝓘(ℝ, U) I f₁ s x).toLinearMap) ^ 2 =
        (LinearMap.normDet (U := U) (mfderivWithin 𝓘(ℝ, U) I f₂ s x).toLinearMap) ^ 2 := by
    rw [h1, h2]
    congr 1
    ext i j
    simp only [Matrix.gram_apply, hmf]
    exact inner_tangentSpace_congr (I := I) heq rfl rfl
  exact (sq_eq_sq₀ (LinearMap.normDet_nonneg (U := U) _) (LinearMap.normDet_nonneg (U := U) _)).mp
    hsq

end Helpers

/-! ### Parametrized mass of smooth singular simplices -/

namespace SmoothSimplex

section MassBasic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {p : ℕ}

/-- The **parametrized Riemannian mass** of a smooth singular `p`-simplex `σ`: the integral over
`Δᵖ ⊆ ℝᵖ` of the `p`-dimensional Jacobian `LinearMap.normDet` of its within-set differential. -/
def mass (σ : SmoothSimplex I M p) : ℝ :=
  ∫ x in fullSimplex p,
    LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x).toLinearMap

/-- Unfolding the definition of the parametrized mass of a smooth simplex. -/
theorem mass_def (σ : SmoothSimplex I M p) :
    σ.mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x).toLinearMap :=
  (rfl)

/-- The parametrized mass of any smooth simplex is nonnegative. -/
theorem mass_nonneg (σ : SmoothSimplex I M p) : 0 ≤ σ.mass :=
  setIntegral_nonneg (isClosed_fullSimplex p).measurableSet fun _ _ ↦
    LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin p)) _

/-- The mass of a smooth simplex may be computed from any ambient map `g : ℝᵖ → M` agreeing with
the simplex on `Δᵖ`, differentiating within `Δᵖ`. -/
theorem mass_eq_setIntegral_normDet (σ : SmoothSimplex I M p)
    {g : EuclideanSpace ℝ (Fin p) → M} (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    σ.mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) x).toLinearMap := by
  rw [mass_def]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  exact normDet_mfderivWithin_congr
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy ↦ by
      rw [σ.extension_coe ⟨y, hy⟩, hg ⟨y, hy⟩]) hx

/-- The mass of a smooth simplex may be computed using the ordinary differential of any ambient
map `g : ℝᵖ → M` agreeing with `σ` on `Δᵖ` and differentiable at every point of `Δᵖ`. -/
theorem mass_eq_setIntegral_mfderiv_normDet (σ : SmoothSimplex I M p)
    {g : EuclideanSpace ℝ (Fin p) → M} (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x)
    (hgd : ∀ x ∈ fullSimplex p, MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x) :
    σ.mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x).toLinearMap := by
  rw [σ.mass_eq_setIntegral_normDet hg]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mfderivWithin_eq_mfderiv
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)) (hgd x hx)]

/-- The mass of `SmoothSimplex.ofContMDiffOn hg hU` is the integral of the Jacobian of `g` over
`Δᵖ`. -/
theorem mass_ofContMDiffOn {U : Set (EuclideanSpace ℝ (Fin p))}
    {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g U) (hU : U ∈ 𝓝ˢ (fullSimplex p)) :
    (ofContMDiffOn hg hU).mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x).toLinearMap :=
  (ofContMDiffOn hg hU).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofContMDiffOn_apply hg hU x).symm)
    fun x hx ↦ (hg.contMDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).mdifferentiableAt (by simp)

/-- The mass of `SmoothSimplex.ofContMDiff hg` is the integral of the Jacobian of `g` over `Δᵖ`. -/
theorem mass_ofContMDiff {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g) :
    (ofContMDiff hg).mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x).toLinearMap :=
  (ofContMDiff hg).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofContMDiff_apply hg x).symm)
    fun x _ ↦ (hg.mdifferentiable (by simp)) x

/-- On a `C¹` manifold with a continuous Riemannian metric, the Jacobian `normDet` of the
within-set differential of a smooth simplex is continuous on `Δᵖ`. -/
theorem continuousOn_normDet_mfderivWithin [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    ContinuousOn
      (fun x ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) x).toLinearMap)
      (fullSimplex p) := by
  intro x hx
  obtain ⟨U, hU, g', hg', hgf⟩ := σ.contMDiffOnSubset_toContinuousMap.exists_contMDiffOn ⟨x, hx⟩
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  have hgV : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I 1 g' V :=
    (hg'.mono hVU).of_le (by simp)
  have hcontV : ContinuousOn
      (fun y ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g' y).toLinearMap) V :=
    (continuousOn_riemannianJacobian (I := I)
      (EuclideanSpace.basisFun (Fin p) ℝ).toBasis hgV hVopen).congr fun y _ ↦
        (riemannianJacobian_eq_normDet (EuclideanSpace.basisFun (Fin p) ℝ) g' y).symm
  refine ((hcontV.continuousAt (hVopen.mem_nhds hxV)).continuousWithinAt).congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hxV)] with
      y hyΔ hyV
    have heq : g =ᶠ[𝓝[fullSimplex p] y] g' := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hyV)] with
        z hzΔ hzV
      rw [hg ⟨z, hzΔ⟩, hgf ⟨z, hzΔ⟩ (hVU hzV)]
    rw [normDet_mfderivWithin_congr heq hyΔ,
      mfderivWithin_eq_mfderiv
        (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p y hyΔ))
        ((hgV.contMDiffAt (hVopen.mem_nhds hyV)).mdifferentiableAt one_ne_zero)]
  · have heq : g =ᶠ[𝓝[fullSimplex p] x] g' := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hxV)] with
        z hzΔ hzV
      rw [hg ⟨z, hzΔ⟩, hgf ⟨z, hzΔ⟩ (hVU hzV)]
    rw [normDet_mfderivWithin_congr heq hx,
      mfderivWithin_eq_mfderiv
        (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx))
        ((hgV.contMDiffAt (hVopen.mem_nhds hxV)).mdifferentiableAt one_ne_zero)]

/-- On a `C¹` manifold with a continuous Riemannian metric, the Jacobian `normDet` of a smooth
simplex is integrable on the compact simplex `Δᵖ`. -/
theorem integrableOn_normDet_mfderivWithin [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    IntegrableOn
      (fun x ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) x).toLinearMap)
      (fullSimplex p) :=
  (σ.continuousOn_normDet_mfderivWithin hg).integrableOn_compact (isCompact_fullSimplex p)

/-- Every smooth `0`-simplex has mass `1`. -/
@[simp]
theorem mass_zero_dim (σ : SmoothSimplex I M 0) : σ.mass = 1 := by
  rw [mass_def]
  have h1 : ∀ x ∈ fullSimplex 0,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin 0))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) I σ.extension (fullSimplex 0) x).toLinearMap =
      1 := fun x _ ↦ LinearMap.normDet_of_subsingleton (U := EuclideanSpace ℝ (Fin 0)) _
  rw [setIntegral_congr_fun (isClosed_fullSimplex 0).measurableSet h1,
    setIntegral_const, volume_real_fullSimplex_zero, one_smul]

/-- Every constant smooth simplex of positive degree has mass `0`. -/
theorem mass_eq_zero_of_const (hp : 0 < p) (σ : SmoothSimplex I M p) {y₀ : M}
    (hσ : ∀ x : fullSimplex p, σ.toContinuousMap x = y₀) : σ.mass = 0 := by
  rw [σ.mass_eq_setIntegral_mfderiv_normDet (g := fun _ ↦ y₀)
    (fun x ↦ (hσ x).symm) (fun _ _ ↦ mdifferentiableAt_const)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ ?_
  rw [mfderiv_const]
  -- The zero continuous linear map has zero underlying linear map, whose `normDet` is `0^p = 0`.
  change LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
    (0 : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] _) = 0
  rw [LinearMap.normDet_zero, finrank_euclideanSpace_fin, zero_pow hp.ne']

/-- If `p < q`, the image of a smooth `p`-simplex under any simplicial operator `f : ⦋q⦌ ⟶ ⦋p⦌`
has mass `0`, because its differential factors through `ℝᵖ` and cannot be injective. -/
theorem mass_map_eq_zero_of_lt {q : ℕ} (σ : SmoothSimplex I M p) (hpq : p < q) (f : ⦋q⦌ ⟶ ⦋p⦌) :
    mass ((smoothSingularSubcomplex I M : SSet).map f.op σ) = 0 := by
  let L := simplexMapAmbient f.toOrderHom
  rw [mass_eq_setIntegral_normDet _ (g := σ.extension ∘ L) fun x ↦ by
    rw [Function.comp_apply, σ.toContinuousMap_map_apply,
      ← σ.extension_coe ⟨L x, mapsTo_simplexMapAmbient _ x.2⟩]]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) (L x) :=
    (σ.contMDiffOn_extension (L x) (mapsTo_simplexMapAmbient _ hx)).mdifferentiableWithinAt
      (by simp)
  have hLx : HasMFDerivWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      L (fullSimplex q) x L.contLinear :=
    L.hasFDerivAt.hasFDerivWithinAt.hasMFDerivWithinAt
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) I (σ.extension ∘ L)
      (fullSimplex q) x
      ((mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) (L x)).comp
        L.contLinear) :=
    hσx.hasMFDerivWithinAt.comp x hLx (mapsTo_simplexMapAmbient _)
  rw [hcomp.mfderivWithin
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex q x hx))]
  refine ((LinearMap.normDet_eq_zero_tfae (U := EuclideanSpace ℝ (Fin q)) _).out 1 6).mpr ?_
  intro hinj
  have hLinj : Function.Injective L.contLinear := fun y z hyz ↦
    hinj (by
      -- Evaluating the composite linear map applies `L.contLinear` first.
      change (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) (L x))
          (L.contLinear y) =
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) (L x))
          (L.contLinear z)
      rw [hyz])
  have hle := LinearMap.finrank_le_finrank_of_injective (f := L.contLinear.toLinearMap) hLinj
  rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hle
  exact hpq.not_ge hle

-- `simp` reduces `SmoothSimplex` in implicit type arguments via `Subfunctor.toFunctor_obj` before
-- looking up `mass_σ`, so the left-hand side is normalized with `dsimp% only`.
/-- **Degeneracy vanishing for mass.** Every degenerate smooth `(p + 1)`-simplex has mass `0`. -/
@[simp]
theorem mass_σ (σ : SmoothSimplex I M p) (i : Fin (p + 1)) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (mass ((smoothSingularSubcomplex I M : SSet).σ i σ))) = 0 :=
  σ.mass_map_eq_zero_of_lt (Nat.lt_succ_self p) (SimplexCategory.σ i)

/-- The mass of the smooth `1`-simplex `SmoothSimplex.ofCurve hγ` of a smooth curve `γ : ℝ → M` is
its Riemannian arc length `∫ t in 0..1, ‖dγ_t(1)‖`. -/
theorem mass_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (ofCurve hγ).mass = ∫ t in (0 : ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ := by
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hγP : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I ∞ (γ ∘ P) :=
    hγ.comp P.contDiff.contMDiff
  rw [(ofCurve hγ).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofCurve_apply hγ x).symm)
    fun x _ ↦ (hγP.mdifferentiable (by simp)) x]
  have hjac : ∀ x : EuclideanSpace ℝ (Fin 1),
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I (γ ∘ P) x).toLinearMap =
      ‖mfderiv 𝓘(ℝ, ℝ) I γ (P x) (1 : ℝ)‖ := fun x ↦ by
    have hcomp : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I (γ ∘ P) x =
        (mfderiv 𝓘(ℝ, ℝ) I γ (P x)).comp P :=
      ((hγ.mdifferentiable (by simp) (P x)).hasMFDerivAt.comp x
        P.hasFDerivAt.hasMFDerivAt).mfderiv
    have hsq := LinearMap.normDet_sq_eq_det_gram (U := EuclideanSpace ℝ (Fin 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I (γ ∘ P) x).toLinearMap
      (EuclideanSpace.basisFun (Fin 1) ℝ)
    simp only [RCLike.ofReal_real_eq_id, id_eq, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq] at hsq
    have he0 : P (EuclideanSpace.basisFun (Fin 1) ℝ default) = (1 : ℝ) := by
      simp [P]
    have hsq' : (LinearMap.normDet (U := EuclideanSpace ℝ (Fin 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I (γ ∘ P) x).toLinearMap) ^ 2 =
        ‖mfderiv 𝓘(ℝ, ℝ) I γ (P x) (1 : ℝ)‖ ^ 2 := by
      rw [hsq, hcomp]
      -- Evaluate the composition `(mfderiv γ (P x)).comp P` on the basis vector `e₀`.
      change ‖mfderiv 𝓘(ℝ, ℝ) I γ (P x) (P (EuclideanSpace.basisFun (Fin 1) ℝ default))‖ ^ 2 = _
      rw [he0]
    exact (sq_eq_sq₀ (LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin 1)) _)
      (norm_nonneg _)).mp hsq'
  simp_rw [hjac]
  dsimp only [P]
  rw [fullSimplex_one_eq_preimage_proj_zero_Icc,
    (volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
      (measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)
      (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖) (Icc 0 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

/-- For a smooth real-valued curve `γ : ℝ → ℝ`, the mass of `SmoothSimplex.ofCurve hγ` is
`∫ t in 0..1, |deriv γ t|`. -/
theorem mass_ofCurve_real {γ : ℝ → ℝ} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ) :
    (ofCurve hγ).mass = ∫ t in (0 : ℝ)..1, |deriv γ t| := by
  rw [mass_ofCurve hγ]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [norm_tangentSpace_vectorSpace, mfderiv_eq_fderiv]
  -- On `ℝ`, `NormedSpace.fromTangentSpace` is the identity and `fderiv ℝ γ t 1 = deriv γ t`.
  change ‖fderiv ℝ γ t 1‖ = |deriv γ t|
  rw [fderiv_apply_one_eq_deriv, Real.norm_eq_abs]

/-- The linear smooth `1`-simplex `t ↦ c * t` on `ℝ` has mass `|c|`. -/
theorem mass_ofCurve_const_mul (c : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ c * t)) :
    (ofCurve hγ).mass = |c| := by
  rw [mass_ofCurve_real hγ]
  have hderiv : ∀ t : ℝ, |deriv (fun s : ℝ ↦ c * s) t| = |c| := fun t ↦ by
    have hd : HasDerivAt (fun s : ℝ ↦ c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    rw [hd.deriv]
  simp_rw [hderiv]
  simp

/-- The folded smooth `1`-simplex `t ↦ 4 * t * (1 - t)` has range `[0, 1]`. -/
theorem range_toContinuousMap_ofCurve_folded
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    Set.range (ofCurve hγ).toContinuousMap = Icc 0 1 := by
  ext y
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    rw [toContinuousMap_ofCurve_apply]
    simp only [fullSimplex_one_eq_preimage_proj_zero_Icc, mem_preimage, EuclideanSpace.coe_proj,
      mem_Icc] at hv
    rcases hv with ⟨ht0, ht1⟩
    dsimp only
    exact ⟨by nlinarith, by nlinarith [sq_nonneg (2 * v 0 - 1)]⟩
  · rintro ⟨hy0, hy1⟩
    set t : ℝ := (1 - Real.sqrt (1 - y)) / 2 with ht
    have ht0 : 0 ≤ t := by
      have hle : Real.sqrt (1 - y) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      linarith
    have ht1 : t ≤ 1 := by
      have hge : 0 ≤ Real.sqrt (1 - y) := Real.sqrt_nonneg _
      linarith
    have hxmem : EuclideanSpace.single (0 : Fin 1) t ∈ fullSimplex 1 := by
      rw [fullSimplex_one_eq_preimage_proj_zero_Icc]
      simpa using ⟨ht0, ht1⟩
    refine ⟨⟨EuclideanSpace.single (0 : Fin 1) t, hxmem⟩, ?_⟩
    rw [toContinuousMap_ofCurve_apply]
    have h0 : (EuclideanSpace.single (0 : Fin 1) t : EuclideanSpace ℝ (Fin 1)) 0 = t := by
      simp
    rw [h0]
    have hsq : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
    nlinarith

/-- A folded smooth `1`-simplex tracing `[0, 1]` back and forth via `t ↦ 4 * t * (1 - t)` has
parametrized mass `2`, even though its image `[0, 1]` has length `1`. -/
theorem mass_ofCurve_folded
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    (ofCurve hγ).mass = 2 := by
  rw [mass_ofCurve_real hγ]
  have hderiv : ∀ t : ℝ, deriv (fun s : ℝ ↦ 4 * s * (1 - s)) t = 4 - 8 * t := fun t ↦ by
    have h1 : HasDerivAt (fun s : ℝ ↦ 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ ↦ 1 - s) (0 - 1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hd : HasDerivAt (fun s : ℝ ↦ 4 * s * (1 - s)) (4 - 8 * t) t := by
      convert h1.mul h2 using 1
      ring
    exact hd.deriv
  simp_rw [hderiv]
  have hcont : Continuous fun t : ℝ ↦ abs (4 - 8 * t) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := (1 / 2 : ℝ)) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hleft : ∫ t in (0 : ℝ)..(1 / 2), abs (4 - 8 * t) = 1 := by
    have hcongr : EqOn (fun t : ℝ ↦ abs (4 - 8 * t)) (fun t : ℝ ↦ 4 - 8 * t) (uIcc 0 (1 / 2)) := by
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
      exact abs_of_nonneg (by linarith [ht.2])
    rw [intervalIntegral.integral_congr hcongr]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ ↦ 4 * t - 4 * t ^ 2) (f' := fun t : ℝ ↦ 4 - 8 * t)
      (a := 0) (b := 1 / 2)
      (fun t _ ↦ by
        have h1 : HasDerivAt (fun s : ℝ ↦ 4 * s) 4 t := by
          simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
        have h2 : HasDerivAt (fun s : ℝ ↦ 4 * s ^ 2) (8 * t) t := by
          convert ((hasDerivAt_pow 2 t).const_mul (4 : ℝ)) using 1
          ring
        exact h1.sub h2)
      ((by fun_prop : Continuous fun t : ℝ ↦ 4 - 8 * t).intervalIntegrable _ _)
    rw [hftc]
    norm_num
  have hright : ∫ t in (1 / 2 : ℝ)..1, abs (4 - 8 * t) = 1 := by
    have hcongr : EqOn (fun t : ℝ ↦ abs (4 - 8 * t)) (fun t : ℝ ↦ 8 * t - 4) (uIcc (1 / 2) 1) := by
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
      dsimp only
      rw [abs_of_nonpos (by linarith [ht.1])]
      ring
    rw [intervalIntegral.integral_congr hcongr]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ ↦ 4 * t ^ 2 - 4 * t) (f' := fun t : ℝ ↦ 8 * t - 4)
      (a := 1 / 2) (b := 1)
      (fun t _ ↦ by
        have h1 : HasDerivAt (fun s : ℝ ↦ 4 * s ^ 2) (8 * t) t := by
          convert ((hasDerivAt_pow 2 t).const_mul (4 : ℝ)) using 1
          ring
        have h2 : HasDerivAt (fun s : ℝ ↦ 4 * s) 4 t := by
          simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
        exact h1.sub h2)
      ((by fun_prop : Continuous fun t : ℝ ↦ 8 * t - 4).intervalIntegrable _ _)
    rw [hftc]
    norm_num
  rw [hleft, hright]
  norm_num

/-- The oriented integral of `dt` over the folded `1`-simplex `t ↦ 4 * t * (1 - t)` vanishes
because the forward and backward traversals cancel, contrasting with `mass_ofCurve_folded`. -/
theorem integral_ofCurve_folded_realLineCoordForm
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    (ofCurve hγ).integral SmoothForm.realLineCoordForm.1 = 0 := by
  have hd : SmoothForm.realLineCoordForm.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
    simpa only [mpullback_id] using SmoothForm.mpullback_realLineCoordForm (I := 𝓘(ℝ)) id
  rw [integral_ofCurve, hd,
    pathIntegral_mextDeriv_ofFunction contMDiff_id (hγ.of_le (by simp)) 0 1]
  norm_num

end MassBasic

/-! ### Functoriality of simplex mass under smooth maps and Riemannian isometries -/

section Functoriality

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {p : ℕ}

/-- A smooth map whose differential has operator norm at most `C ≥ 0` multiplies the mass of every
smooth `p`-simplex by at most `C ^ p`. -/
theorem mass_smoothSingularSubcomplexMap_app_le [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsManifold J 1 N]
    [IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace J y)]
    {f : M → N} (hf : ContMDiff I J ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x (v : TangentSpace I x), ‖mfderiv I J f x v‖ ≤ C * ‖v‖)
    (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) ≤ C ^ p * σ.mass := by
  let τ : SmoothSimplex J N p := (smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ
  have hg : ∀ x : fullSimplex p, (f ∘ σ.extension) x = τ.toContinuousMap x := fun x ↦ by
    rw [Function.comp_apply, toContinuousMap_smoothSingularSubcomplexMap_app]
    simp
  rw [τ.mass_eq_setIntegral_normDet hg, mass_def, ← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on (τ.integrableOn_normDet_mfderivWithin hg)
    ((σ.integrableOn_normDet_mfderivWithin σ.extension_coe).const_mul (C ^ p))
    (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) x :=
    (σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp)
  have hfx : MDifferentiableAt I J f (σ.extension x) :=
    (hf.mdifferentiable (by simp)) (σ.extension x)
  have hmf : mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) J (f ∘ σ.extension) (fullSimplex p) x =
      (mfderiv I J f (σ.extension x)).comp
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x) :=
    mfderiv_comp_mfderivWithin x hfx hσx
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx))
  rw [hmf]
  have hcomp :
      ((mfderiv I J f (σ.extension x)).comp
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x)).toLinearMap =
      (mfderiv I J f (σ.extension x)).toLinearMap ∘ₗ
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x).toLinearMap :=
    rfl
  rw [hcomp]
  have hbound := normDet_comp_le_pow_mul (U := EuclideanSpace ℝ (Fin p))
    (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x).toLinearMap
    (mfderiv I J f (σ.extension x)).toLinearMap hC (hLip (σ.extension x))
  rw [finrank_euclideanSpace_fin] at hbound
  exact hbound

/-- A smooth map whose differential preserves tangent inner products preserves the mass of every
smooth simplex. -/
theorem mass_smoothSingularSubcomplexMap_app_of_inner_mfderiv {f : M → N} (hf : ContMDiff I J ∞ f)
    (hinner : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w)
    (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) = σ.mass := by
  let τ : SmoothSimplex J N p := (smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ
  have hg : ∀ x : fullSimplex p, (f ∘ σ.extension) x = τ.toContinuousMap x := fun x ↦ by
    rw [Function.comp_apply, toContinuousMap_smoothSingularSubcomplexMap_app]
    simp
  rw [τ.mass_eq_setIntegral_normDet hg, mass_def]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) x :=
    (σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp)
  have hfx : MDifferentiableAt I J f (σ.extension x) :=
    (hf.mdifferentiable (by simp)) (σ.extension x)
  have hmf : mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) J (f ∘ σ.extension) (fullSimplex p) x =
      (mfderiv I J f (σ.extension x)).comp
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x) :=
    mfderiv_comp_mfderivWithin x hfx hσx
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx))
  rw [hmf]
  have hcomp :
      ((mfderiv I J f (σ.extension x)).comp
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x)).toLinearMap =
      (mfderiv I J f (σ.extension x)).toLinearMap ∘ₗ
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x).toLinearMap :=
    rfl
  rw [hcomp]
  exact normDet_comp_of_inner_eq (U := EuclideanSpace ℝ (Fin p)) _ _ (hinner (σ.extension x))

/-- Smooth Riemannian isometries preserve the mass of every smooth simplex. -/
theorem mass_smoothSingularSubcomplexMap_riemannianIsometry
    (Φ : RiemannianIsometry I J M N) (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap Φ Φ.toDiffeomorph.contMDiff).app (op ⦋p⦌) σ) = σ.mass :=
  mass_smoothSingularSubcomplexMap_app_of_inner_mfderiv Φ.toDiffeomorph.contMDiff
    Φ.inner_mfderiv σ

end Functoriality

/-! ### Reparametrization invariance, top-degree volume form, and subdivision mass -/

section MassProperties

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {p : ℕ}

private theorem normDet_mfderivWithin_comp_of_hasFDerivWithinAt (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p))
    {x : EuclideanSpace ℝ (Fin p)} (hx : x ∈ fullSimplex p)
    {L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hΨ : HasFDerivWithinAt Ψ L (fullSimplex p) x) :
    LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (σ.extension ∘ Ψ)
        (fullSimplex p) x).toLinearMap =
    |L.det| • LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
        (fullSimplex p) (Ψ x)).toLinearMap := by
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) (Ψ x) :=
    (σ.contMDiffOn_extension (Ψ x) (hmaps hx)).mdifferentiableWithinAt (by simp)
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (σ.extension ∘ Ψ)
      (fullSimplex p) x
      ((mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) (Ψ x)).comp L) :=
    hσx.hasMFDerivWithinAt.comp x hΨ.hasMFDerivWithinAt hmaps
  rw [hcomp.mfderivWithin
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx))]
  let L₁ : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p) := L.toLinearMap
  let L₂ : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] TangentSpace I (σ.extension (Ψ x)) :=
    (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) (Ψ x)).toLinearMap
  -- Identify `TangentSpace 𝓘(ℝ, ℝᵖ)` with `ℝᵖ` to apply `normDet_comp_of_finrank_eq`.
  change LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (L₂ ∘ₗ L₁) =
    |LinearMap.det L₁| • LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) L₂
  rw [LinearMap.normDet_comp_of_finrank_eq (U := EuclideanSpace ℝ (Fin p))
    (V := EuclideanSpace ℝ (Fin p)) L₁ L₂ rfl,
    LinearMap.normDet_eq_abs_det, smul_eq_mul, mul_comm]

/-- **Reparametrization invariance of simplex mass.** Any smooth bijective self-reparametrization
`Ψ` of `Δᵖ` (defined on a neighbourhood of `Δᵖ`) preserves the mass of `σ`, regardless of whether
`Ψ` preserves or reverses orientation. -/
theorem mass_compContDiffOn (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin p))}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p))
    (hinj : InjOn Ψ (fullSimplex p)) (himage : Ψ '' fullSimplex p = fullSimplex p) :
    (σ.compContDiffOn hΨ hU hmaps).mass = σ.mass := by
  rw [(σ.compContDiffOn hΨ hU hmaps).mass_eq_setIntegral_normDet (g := σ.extension ∘ Ψ) fun x ↦ by
    rw [Function.comp_apply, toContinuousMap_compContDiffOn_apply,
      σ.extension_coe ⟨Ψ x, hmaps x.2⟩]]
  have hΨfderiv : ∀ x ∈ fullSimplex p,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) (fullSimplex p) x := fun x hx ↦
    ((hΨ.contDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet
    (fun x hx ↦ σ.normDet_mfderivWithin_comp_of_hasFDerivWithinAt hmaps hx (hΨfderiv x hx)),
    mass_def]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet hΨfderiv hinj
    (fun y ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) y).toLinearMap)
  rw [himage] at hcov
  exact hcov.symm

/-- Permuting the vertices of a smooth simplex leaves its mass unchanged. -/
theorem mass_compPerm (σ : SmoothSimplex I M p) (e : Equiv.Perm (Fin (p + 1))) :
    (σ.compPerm e).mass = σ.mass := by
  have heq : σ.compPerm e = σ.compContDiffOn (simplexMapAmbient e).contDiff.contDiffOn
      Filter.univ_mem (mapsTo_simplexMapAmbient e) := by
    ext x
    simp
  rw [heq]
  exact σ.mass_compContDiffOn _ Filter.univ_mem (mapsTo_simplexMapAmbient e)
    (simplexMapAmbient_perm_injective e).injOn (image_simplexMapAmbient_perm e)

/-- **Pointwise top-degree volume comparison.** For an oriented Riemannian manifold of dimension
`p`, the absolute value of the pulled-back Riemannian volume form on the standard basis equals the
Jacobian `LinearMap.normDet` of the differential of `σ`. -/
theorem abs_mpullbackWithin_riemannianVolumeForm [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (o : Manifold.Orientation I M (Fin p)) (σ : SmoothSimplex I M p)
    (x : EuclideanSpace ℝ (Fin p)) :
    |mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x fun i ↦ EuclideanSpace.single i 1| =
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
          (fullSimplex p) x).toLinearMap := by
  have hmp := mpullbackWithin_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (I' := I)
    σ.extension (fullSimplex p) (riemannianVolumeForm o) x
    (fun i ↦ EuclideanSpace.single i (1 : ℝ))
  refine (congrArg abs hmp).trans ?_
  rw [riemannianVolumeForm_apply]
  let := o.fact_finrank_tangentSpace (σ.extension x)
  rw [Orientation.abs_volumeForm_apply_eq_sqrt_det_gram]
  have hsq := LinearMap.normDet_sq_eq_det_gram (U := EuclideanSpace ℝ (Fin p))
    (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x).toLinearMap
    (EuclideanSpace.basisFun (Fin p) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq, EuclideanSpace.basisFun_apply] at hsq
  refine Eq.trans ?_ (Real.sqrt_sq (LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin p)) _))
  rw [hsq]
  rfl

/-- Integrating the Riemannian volume form over a positively oriented top-dimensional smooth simplex
recovers its mass. -/
theorem integral_riemannianVolumeForm_eq_mass [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (o : Manifold.Orientation I M (Fin p)) (σ : SmoothSimplex I M p)
    (hpos : ∀ x ∈ fullSimplex p,
      0 ≤ mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x fun i ↦ EuclideanSpace.single i 1) :
    σ.integral (riemannianVolumeForm o) = σ.mass := by
  rw [integral_def, mass_def]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [← abs_of_nonneg (hpos x hx), abs_mpullbackWithin_riemannianVolumeForm]

/-- Integrating the Riemannian volume form over a negatively oriented top-dimensional smooth simplex
gives minus its mass. -/
theorem integral_riemannianVolumeForm_eq_neg_mass [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (o : Manifold.Orientation I M (Fin p)) (σ : SmoothSimplex I M p)
    (hneg : ∀ x ∈ fullSimplex p,
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x (fun i ↦ EuclideanSpace.single i 1) ≤ 0) :
    σ.integral (riemannianVolumeForm o) = -σ.mass := by
  rw [integral_def, mass_def, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [← abs_mpullbackWithin_riemannianVolumeForm, abs_of_nonpos (hneg x hx), neg_neg]

/-- **Barycentric subdivision preserves simplex mass.** Summing the masses of the `(p + 1)!`
barycentric subdivision simplices of a smooth `p`-simplex recovers its mass. -/
theorem sum_mass_compAffineMapMk_vertex [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) :
    ∑ e : Equiv.Perm (Fin (p + 1)),
      (σ.compAffineMapMk (BarycentricSubdivision.vertex e)).mass = σ.mass := by
  have hterm (e : Equiv.Perm (Fin (p + 1))) :
      (σ.compAffineMapMk (BarycentricSubdivision.vertex e)).mass =
        ∫ x in fullSimplex p,
          |LinearMap.det
            (affineMapAmbient (BarycentricSubdivision.vertex e)).contLinear.toLinearMap| •
            LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
              (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
                (affineMapAmbient (BarycentricSubdivision.vertex e) x)).toLinearMap := by
    let A := affineMapAmbient (BarycentricSubdivision.vertex e)
    let τ := σ.compAffineMapMk (BarycentricSubdivision.vertex e)
    rw [τ.mass_eq_setIntegral_normDet (g := σ.extension ∘ A) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compAffineMapMk_apply,
        σ.extension_coe ⟨A x, mapsTo_affineMapAmbient _ x.2⟩]]
    refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
    exact σ.normDet_mfderivWithin_comp_of_hasFDerivWithinAt (mapsTo_affineMapAmbient _) hx
      A.hasFDerivAt.hasFDerivWithinAt
  simp_rw [hterm]
  exact BarycentricSubdivision.sum_setIntegral_affineMapAmbient_vertex
    (σ.integrableOn_normDet_mfderivWithin σ.extension_coe)

end MassProperties

/-! ### Comass and calibration bounds on smooth simplices -/

section Comass

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- **Pointwise comass inequality for smooth simplices.** At every point `x ∈ ℝᵖ`, the norm of the
pulled-back `p`-form evaluated on the standard basis is bounded by the comass (operator norm) of
the form times the Jacobian `LinearMap.normDet` of the differential. No finite-dimensionality
assumption on the model space `E` is needed. -/
theorem norm_mpullbackWithin_le_opNorm_mul_normDet (σ : SmoothSimplex I M p)
    (φ : RoughForm I M F p) (x : EuclideanSpace ℝ (Fin p)) :
    ‖mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ x
        fun i ↦ EuclideanSpace.single i 1‖ ≤
      ‖φ (σ.extension x)‖ *
        LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
          (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
            (fullSimplex p) x).toLinearMap := by
  let L : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] TangentSpace I (σ.extension x) :=
    (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) x).toLinearMap
  let W : Submodule ℝ (TangentSpace I (σ.extension x)) := L.range
  let ω' : W [⋀^Fin p]→L[ℝ] F := (φ (σ.extension x)).compContinuousLinearMap W.subtypeL
  have hω' : ‖ω'‖ ≤ ‖φ (σ.extension x)‖ := by
    refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal
      (norm_nonneg (φ (σ.extension x)))).mpr fun v hv ↦ ?_
    have hv' : Orthonormal ℝ (fun i ↦ (v i : TangentSpace I (σ.extension x))) :=
      hv.comp_linearIsometry W.subtypeₗᵢ
    exact (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal
      (norm_nonneg (φ (σ.extension x)))).mp le_rfl _ hv'
  have hbound := ContinuousAlternatingMap.le_opNorm_mul_normDet ω' L.rangeRestrict
    (EuclideanSpace.basisFun (Fin p) ℝ)
  have hdet : L.rangeRestrict.normDet = L.normDet :=
    LinearMap.normDet_codRestrict (f := L) (fun c ↦ LinearMap.mem_range_self L c)
  rw [hdet] at hbound
  refine le_trans ?_ (hbound.trans (mul_le_mul_of_nonneg_right hω' L.normDet_nonneg))
  have hmp := mpullbackWithin_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (I' := I)
    σ.extension (fullSimplex p) φ x (fun i ↦ EuclideanSpace.single i (1 : ℝ))
  refine le_of_eq (congrArg norm (hmp.trans ?_))
  simp only [ω', ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp only [Function.comp_apply, Submodule.subtypeL_apply, EuclideanSpace.basisFun_apply]
  rfl

/-- **Comass bound for integration over a smooth simplex.** If `‖φ‖ ≤ C` along the image of `σ`,
then `‖∫_σ φ‖ ≤ C * σ.mass`. Neither finite-dimensionality of `E` nor continuity of `φ` is
needed. -/
theorem norm_integral_le_mul_mass [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) {C : ℝ}
    (hφ : ∀ x : fullSimplex p, ‖φ (σ.toContinuousMap x)‖ ≤ C) :
    ‖σ.integral φ‖ ≤ C * σ.mass := by
  rw [integral_def, mass_def, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.norm_integral_le_of_norm_le
    ((σ.integrableOn_normDet_mfderivWithin σ.extension_coe).const_mul C) ?_
  filter_upwards [ae_restrict_mem (isClosed_fullSimplex p).measurableSet] with x hx
  refine (σ.norm_mpullbackWithin_le_opNorm_mul_normDet φ x).trans ?_
  rw [σ.extension_coe ⟨x, hx⟩]
  exact mul_le_mul_of_nonneg_right (hφ ⟨x, hx⟩)
    (LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin p)) _)

/-- **Comass bound via orthonormal frames.** If `‖φ v‖ ≤ C` (with `0 ≤ C`) on every orthonormal
`p`-frame along `σ`, then `‖∫_σ φ‖ ≤ C * σ.mass`. -/
theorem norm_integral_le_mul_mass_of_orthonormal [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x : fullSimplex p, ∀ v : Fin p → TangentSpace I (σ.toContinuousMap x),
      Orthonormal ℝ v → ‖φ (σ.toContinuousMap x) v‖ ≤ C) :
    ‖σ.integral φ‖ ≤ C * σ.mass :=
  σ.norm_integral_le_mul_mass φ fun x ↦
    (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal hC).mpr (hφ x)

/-- **Unit comass / calibration bound on a smooth simplex.** If a real `p`-form satisfies
`|φ v| ≤ 1` on every orthonormal `p`-frame along `σ`, then `|∫_σ φ| ≤ σ.mass`. -/
theorem abs_integral_le_mass_of_orthonormal [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (σ : SmoothSimplex I M p) (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : fullSimplex p, ∀ v : Fin p → TangentSpace I (σ.toContinuousMap x),
      Orthonormal ℝ v → |φ (σ.toContinuousMap x) v| ≤ 1) :
    |σ.integral φ| ≤ σ.mass := by
  simpa only [Real.norm_eq_abs, one_mul] using
    σ.norm_integral_le_mul_mass_of_orthonormal φ zero_le_one hφ

end Comass

end SmoothSimplex

end TauCeti
