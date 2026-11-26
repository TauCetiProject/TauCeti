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
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.MeasureTheory.Integral.FullSimplex
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# Parametrized Riemannian mass of smooth singular simplices

On a manifold `M` with a Riemannian bundle, the **parametrized mass** of a smooth `p`-simplex
`σ : SmoothSimplex I M p` is `∫ x in Δᵖ, LinearMap.normDet (mfderivWithin σ.extension Δᵖ x)`.
It counts multiplicity and folding (`t ↦ 4 * t * (1 - t)` has range `[0, 1]`, oriented
`dt`-integral `0`, and mass `2`). We establish continuity and integrability of the Jacobian
integrand, mass `1` in degree zero and vanishing for positive-degree constant and degenerate
simplices, `1`-simplex arc-length and folded-curve
checks, Lipschitz pushforward bounds and isometry invariance, reparametrization / permutation /
barycentric subdivision invariance, top-degree comparison with `riemannianVolumeForm`, and
pointwise/integrated comass bounds without finite-dimensionality assumptions on the model space.

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

/-! ### Parametrized mass of smooth singular simplices -/

namespace SmoothSimplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {p : ℕ}

/-- The **parametrized Riemannian mass** of a smooth singular `p`-simplex `σ`: the integral over
`Δᵖ ⊆ ℝᵖ` of the `p`-dimensional Jacobian `LinearMap.normDet` of its within-set differential. -/
def mass (σ : SmoothSimplex I M p) : ℝ :=
  ∫ x in fullSimplex p, LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
    (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap

/-- Unfolding the definition of the parametrized mass of a smooth simplex. -/
theorem mass_def (σ : SmoothSimplex I M p) :
    σ.mass = ∫ x in fullSimplex p, LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap := (rfl)

/-- The parametrized mass of any smooth simplex is nonnegative. -/
theorem mass_nonneg (σ : SmoothSimplex I M p) : 0 ≤ σ.mass :=
  setIntegral_nonneg (isClosed_fullSimplex p).measurableSet fun _ _ ↦
    LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin p)) _

/-- Compute `σ.mass` from any ambient map `g : ℝᵖ → M` agreeing with `σ` on `Δᵖ`. -/
theorem mass_eq_setIntegral_normDet (σ : SmoothSimplex I M p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    σ.mass = ∫ x in fullSimplex p, LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I g (fullSimplex p) x).toLinearMap := by
  rw [mass_def]
  exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦
    normDet_mfderivWithin_congr (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun y hy ↦ by
      rw [σ.extension_coe ⟨y, hy⟩, hg ⟨y, hy⟩]) hx

/-- Compute `σ.mass` via `mfderiv` of `g` agreeing with `σ` and differentiable on `Δᵖ`. -/
theorem mass_eq_setIntegral_mfderiv_normDet (σ : SmoothSimplex I M p)
    {g : EuclideanSpace ℝ (Fin p) → M} (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x)
    (hgd : ∀ x ∈ fullSimplex p, MDifferentiableAt (𝓡 p) I g x) :
    σ.mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (mfderiv (𝓡 p) I g x).toLinearMap := by
  rw [σ.mass_eq_setIntegral_normDet hg]
  exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ by
    rw [mfderivWithin_eq_mfderiv
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)) (hgd x hx)]

/-- The mass of `SmoothSimplex.ofContMDiffOn hg hU` is the Jacobian integral of `g` over `Δᵖ`. -/
theorem mass_ofContMDiffOn {U : Set (EuclideanSpace ℝ (Fin p))} {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiffOn (𝓡 p) I ∞ g U) (hU : U ∈ 𝓝ˢ (fullSimplex p)) :
    (ofContMDiffOn hg hU).mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (mfderiv (𝓡 p) I g x).toLinearMap :=
  (ofContMDiffOn hg hU).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofContMDiffOn_apply hg hU x).symm)
    fun x hx ↦ (hg.contMDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).mdifferentiableAt (by simp)

/-- The mass of `SmoothSimplex.ofContMDiff hg` is the Jacobian integral of `g` over `Δᵖ`. -/
theorem mass_ofContMDiff {g : EuclideanSpace ℝ (Fin p) → M} (hg : ContMDiff (𝓡 p) I ∞ g) :
    (ofContMDiff hg).mass = ∫ x in fullSimplex p,
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (mfderiv (𝓡 p) I g x).toLinearMap :=
  (ofContMDiff hg).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofContMDiff_apply hg x).symm)
    fun x _ ↦ (hg.mdifferentiable (by simp)) x

section Continuity
variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The Jacobian `normDet` of the within-set differential of `σ` is continuous on `Δᵖ`. -/
theorem continuousOn_normDet_mfderivWithin (σ : SmoothSimplex I M p)
    {g : EuclideanSpace ℝ (Fin p) → M} (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    ContinuousOn (fun x ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I g (fullSimplex p) x).toLinearMap) (fullSimplex p) := by
  intro x hx
  obtain ⟨U, hU, g', hg', hgf⟩ := σ.contMDiffOnSubset_toContinuousMap.exists_contMDiffOn ⟨x, hx⟩
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  have hgV : ContMDiffOn (𝓡 p) I 1 g' V := (hg'.mono hVU).of_le (by simp)
  have hcontV : ContinuousOn (fun y ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderiv (𝓡 p) I g' y).toLinearMap) V :=
    (continuousOn_riemannianJacobian (I := I)
      (EuclideanSpace.basisFun (Fin p) ℝ).toBasis hgV hVopen).congr fun y _ ↦
        (riemannianJacobian_eq_normDet (EuclideanSpace.basisFun (Fin p) ℝ) g' y).symm
  have hpt {y} (hyΔ : y ∈ fullSimplex p) (hyV : y ∈ V) :
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin (𝓡 p) I g (fullSimplex p) y).toLinearMap =
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (mfderiv (𝓡 p) I g' y).toLinearMap := by
    have heq : g =ᶠ[𝓝[fullSimplex p] y] g' := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hyV)] with
        z hzΔ hzV; rw [hg ⟨z, hzΔ⟩, hgf ⟨z, hzΔ⟩ (hVU hzV)]
    rw [normDet_mfderivWithin_congr heq hyΔ, mfderivWithin_eq_mfderiv
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p y hyΔ))
      ((hgV.contMDiffAt (hVopen.mem_nhds hyV)).mdifferentiableAt one_ne_zero)]
  refine (hcontV.continuousAt (hVopen.mem_nhds hxV)).continuousWithinAt.congr_of_eventuallyEq
    ?_ (hpt hx hxV)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hxV)] with
    y hyΔ hyV; exact hpt hyΔ hyV

/-- The Jacobian `normDet` of a smooth simplex is integrable on the compact simplex `Δᵖ`. -/
theorem integrableOn_normDet_mfderivWithin (σ : SmoothSimplex I M p)
    {g : EuclideanSpace ℝ (Fin p) → M} (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    IntegrableOn (fun x ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I g (fullSimplex p) x).toLinearMap) (fullSimplex p) :=
  (σ.continuousOn_normDet_mfderivWithin hg).integrableOn_compact (isCompact_fullSimplex p)

end Continuity

/-- Every smooth `0`-simplex has mass `1`. -/
@[simp]
theorem mass_zero_dim (σ : SmoothSimplex I M 0) : σ.mass = 1 := by
  rw [mass_def]
  have h1 : ∀ x ∈ fullSimplex 0, LinearMap.normDet (U := EuclideanSpace ℝ (Fin 0))
      (mfderivWithin (𝓡 0) I σ.extension (fullSimplex 0) x).toLinearMap = 1 := fun _ _ ↦
    LinearMap.normDet_of_subsingleton (U := EuclideanSpace ℝ (Fin 0)) _
  rw [setIntegral_congr_fun (isClosed_fullSimplex 0).measurableSet h1,
    setIntegral_const, volume_real_fullSimplex_zero, one_smul]

/-- Every constant smooth simplex of positive degree has mass `0`. -/
theorem mass_eq_zero_of_const (hp : 0 < p) (σ : SmoothSimplex I M p) {y₀ : M}
    (hσ : ∀ x : fullSimplex p, σ.toContinuousMap x = y₀) : σ.mass = 0 := by
  rw [σ.mass_eq_setIntegral_mfderiv_normDet (g := fun _ ↦ y₀)
    (fun x ↦ (hσ x).symm) (fun _ _ ↦ mdifferentiableAt_const)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ ?_
  rw [mfderiv_const]
  -- `TangentSpace (𝓡 p) x` is `EuclideanSpace ℝ (Fin p)` only definitionally, blocking `rw` from
  -- matching `ContinuousLinearMap.coe_zero` on the domain of `.toLinearMap`.
  change LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (0 : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] _) =
    0
  rw [LinearMap.normDet_zero, finrank_euclideanSpace_fin, zero_pow hp.ne']

/-- If `p < q`, pulling back a `p`-simplex along `f : ⦋q⦌ ⟶ ⦋p⦌` yields mass `0`. -/
theorem mass_map_eq_zero_of_lt {q : ℕ} (σ : SmoothSimplex I M p) (hpq : p < q) (f : ⦋q⦌ ⟶ ⦋p⦌) :
    mass ((smoothSingularSubcomplex I M : SSet).map f.op σ) = 0 := by
  let L := simplexMapAmbient f.toOrderHom
  rw [mass_eq_setIntegral_normDet _ (g := σ.extension ∘ L) fun x ↦ by
    rw [Function.comp_apply, σ.toContinuousMap_map_apply,
      ← σ.extension_coe ⟨L x, mapsTo_simplexMapAmbient _ x.property⟩]]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  have hcomp := ((σ.contMDiffOn_extension (L x)
    (mapsTo_simplexMapAmbient _ hx)).mdifferentiableWithinAt (by simp)).hasMFDerivWithinAt.comp x
    L.hasFDerivAt.hasFDerivWithinAt.hasMFDerivWithinAt (mapsTo_simplexMapAmbient _)
  rw [hcomp.mfderivWithin
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_fullSimplex q x hx))]
  refine ((LinearMap.normDet_eq_zero_tfae (U := EuclideanSpace ℝ (Fin q)) _).out 1 6).mpr
    fun hinj ↦ hpq.not_ge ?_
  have hle := LinearMap.finrank_le_finrank_of_injective (f := L.contLinear.toLinearMap) fun y z h ↦
    hinj (congrArg (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) (L x)) h)
  simpa only [finrank_euclideanSpace_fin] using hle

-- `simp` reduces `SmoothSimplex` in implicit type arguments via `Subfunctor.toFunctor_obj` before
-- looking up `mass_σ`, so the left-hand side is normalized with `dsimp% only`.
/-- **Degeneracy vanishing for mass.** Every degenerate smooth `(p + 1)`-simplex has mass `0`. -/
@[simp]
theorem mass_σ (σ : SmoothSimplex I M p) (i : Fin (p + 1)) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (mass ((smoothSingularSubcomplex I M : SSet).σ i σ))) = 0 :=
  σ.mass_map_eq_zero_of_lt (Nat.lt_succ_self p) (SimplexCategory.σ i)

/-- The mass of `SmoothSimplex.ofCurve hγ` is its Riemannian arc length `∫ t in 0..1, ‖dγ_t(1)‖`. -/
theorem mass_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (ofCurve hγ).mass = ∫ t in (0 : ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ := by
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hγP : ContMDiff (𝓡 1) I ∞ (γ ∘ P) := hγ.comp P.contDiff.contMDiff
  rw [(ofCurve hγ).mass_eq_setIntegral_mfderiv_normDet
    (fun x ↦ (toContinuousMap_ofCurve_apply hγ x).symm) fun x _ ↦ (hγP.mdifferentiable (by simp)) x]
  have hjac (x : EuclideanSpace ℝ (Fin 1)) :
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin 1)) (mfderiv (𝓡 1) I (γ ∘ P) x).toLinearMap =
        ‖mfderiv 𝓘(ℝ, ℝ) I γ (P x) (1 : ℝ)‖ := by
    have hcomp : mfderiv (𝓡 1) I (γ ∘ P) x = (mfderiv 𝓘(ℝ, ℝ) I γ (P x)).comp P :=
      ((hγ.mdifferentiable (by simp) (P x)).hasMFDerivAt.comp x P.hasFDerivAt.hasMFDerivAt).mfderiv
    have hsq := LinearMap.normDet_sq_eq_det_gram (U := EuclideanSpace ℝ (Fin 1))
      (mfderiv (𝓡 1) I (γ ∘ P) x).toLinearMap (EuclideanSpace.basisFun (Fin 1) ℝ)
    simp only [RCLike.ofReal_real_eq_id, id_eq, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq] at hsq
    refine (sq_eq_sq₀ (LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin 1)) _)
      (norm_nonneg _)).mp ?_
    rw [hsq, hcomp]
    -- `TangentSpace (𝓡 1) x` and `TangentSpace 𝓘(ℝ, ℝ) (P x)` are `EuclideanSpace ℝ (Fin 1)` and
    -- `ℝ` only definitionally, blocking `ContinuousLinearMap.comp_apply` from matching via `rw`.
    change ‖mfderiv 𝓘(ℝ, ℝ) I γ (P x) (P (EuclideanSpace.basisFun (Fin 1) ℝ default))‖ ^ 2 = _
    have hP : P (EuclideanSpace.basisFun (Fin 1) ℝ default) = 1 := by simp [P]
    rw [hP]
  simp_rw [hjac]; dsimp only [P]
  rw [fullSimplex_one_eq_preimage_proj_zero_Icc,
    (volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
      (measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)
      (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖) (Icc 0 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

/-- For `γ : ℝ → ℝ`, the mass of `SmoothSimplex.ofCurve hγ` is `∫ t in 0..1, |deriv γ t|`. -/
theorem mass_ofCurve_real {γ : ℝ → ℝ} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ) :
    (ofCurve hγ).mass = ∫ t in (0 : ℝ)..1, |deriv γ t| := by
  rw [mass_ofCurve hγ]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [norm_tangentSpace_vectorSpace, mfderiv_eq_fderiv]
  -- `TangentSpace 𝓘(ℝ, ℝ) t` is `ℝ` only definitionally, so `NormedSpace.fromTangentSpace`
  -- reduces to the identity by `change` rather than a rewrite lemma.
  change ‖fderiv ℝ γ t 1‖ = |deriv γ t|
  rw [fderiv_apply_one_eq_deriv, Real.norm_eq_abs]

/-- The linear smooth `1`-simplex `t ↦ c * t` on `ℝ` has mass `|c|`. -/
theorem mass_ofCurve_const_mul (c : ℝ) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ c * t)) :
    (ofCurve hγ).mass = |c| := by
  rw [mass_ofCurve_real hγ]
  have hderiv (t : ℝ) : deriv (fun s : ℝ ↦ c * s) t = c :=
    (by simpa using (hasDerivAt_id t).const_mul c : HasDerivAt (fun s : ℝ ↦ c * s) c t).deriv
  simp [hderiv]

/-- The folded smooth `1`-simplex `t ↦ 4 * t * (1 - t)` has range `[0, 1]`. -/
theorem range_toContinuousMap_ofCurve_folded
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    Set.range (ofCurve hγ).toContinuousMap = Icc 0 1 := by
  ext y; constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩; rw [toContinuousMap_ofCurve_apply]
    simp only [fullSimplex_one_eq_preimage_proj_zero_Icc, mem_preimage, EuclideanSpace.coe_proj,
      mem_Icc] at hv
    exact ⟨by nlinarith, by nlinarith [sq_nonneg (2 * v 0 - 1)]⟩
  · rintro ⟨hy0, hy1⟩
    set t : ℝ := (1 - Real.sqrt (1 - y)) / 2 with ht
    have hle : Real.sqrt (1 - y) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
    have hxmem : EuclideanSpace.single (0 : Fin 1) t ∈ fullSimplex 1 := by
      rw [fullSimplex_one_eq_preimage_proj_zero_Icc]
      simpa using ⟨by linarith, by linarith [Real.sqrt_nonneg (1 - y)]⟩
    refine ⟨⟨EuclideanSpace.single (0 : Fin 1) t, hxmem⟩, ?_⟩
    rw [toContinuousMap_ofCurve_apply, PiLp.single_eq_same]
    have hsq : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt (by linarith); nlinarith

/-- The folded `1`-simplex `t ↦ 4 * t * (1 - t)` has mass `2` (though its image has length `1`). -/
theorem mass_ofCurve_folded (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    (ofCurve hγ).mass = 2 := by
  rw [mass_ofCurve_real hγ]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ 4 * s * (1 - s)) (4 - 8 * t) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ ↦ 1 - s) (0 - 1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    convert h1.mul h2 using 1; ring
  simp_rw [(hd _).deriv]
  have hcont : Continuous fun t : ℝ ↦ abs (4 - 8 * t) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (1 / 2 : ℝ))
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr fun t ht ↦
      abs_of_nonneg (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht; linarith [ht.right]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      ((by fun_prop : Continuous fun t : ℝ ↦ 4 - 8 * t).intervalIntegrable _ _),
    intervalIntegral.integral_congr fun t ht ↦
      abs_of_nonpos (by rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht; linarith [ht.left]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ (hd t).neg)
      ((by fun_prop : Continuous fun t : ℝ ↦ -(4 - 8 * t)).intervalIntegrable _ _)]
  norm_num

/-- The oriented integral of `dt` over `t ↦ 4 * t * (1 - t)` vanishes (`mass_ofCurve_folded`). -/
theorem integral_ofCurve_folded_realLineCoordForm
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 4 * t * (1 - t))) :
    (ofCurve hγ).integral SmoothForm.realLineCoordForm.val = 0 := by
  have hd : SmoothForm.realLineCoordForm.val = mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
    simpa only [mpullback_id] using SmoothForm.mpullback_realLineCoordForm (I := 𝓘(ℝ)) id
  rw [integral_ofCurve, hd, pathIntegral_mextDeriv_ofFunction contMDiff_id (hγ.of_le (by simp)) 0 1]
  norm_num

/-! ### Functoriality of simplex mass under smooth maps and Riemannian isometries -/

section Functoriality
variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] in
private theorem mfderivWithin_comp_extension {f : M → N} (hf : ContMDiff I J ∞ f)
    (σ : SmoothSimplex I M p) {x : EuclideanSpace ℝ (Fin p)} (hx : x ∈ fullSimplex p) :
    (mfderivWithin (𝓡 p) J (f ∘ σ.extension) (fullSimplex p) x).toLinearMap =
      (mfderiv I J f (σ.extension x)).toLinearMap ∘ₗ
        (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap := by
  rw [mfderiv_comp_mfderivWithin x ((hf.mdifferentiable (by simp)) (σ.extension x))
    ((σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp))
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_fullSimplex p x hx))]
  -- `ContinuousLinearMap.toLinearMap` turns `∘SL` into `∘ₗ`, with `TangentSpace (𝓡 p) x` read
  -- definitionally as `EuclideanSpace ℝ (Fin p)`.
  rfl

/-- A smooth map with differential operator norm `≤ C` multiplies `p`-simplex mass by `≤ C ^ p`. -/
theorem mass_smoothSingularSubcomplexMap_app_le [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsManifold J 1 N]
    [IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace J y)]
    {f : M → N} (hf : ContMDiff I J ∞ f) {C : ℝ}
    (hLip : ∀ x (v : TangentSpace I x), ‖mfderiv I J f x v‖ ≤ C * ‖v‖)
    (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) ≤ C ^ p * σ.mass := by
  let τ : SmoothSimplex J N p := (smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ
  have hg (x : fullSimplex p) : (f ∘ σ.extension) x = τ.toContinuousMap x := by
    rw [Function.comp_apply, toContinuousMap_smoothSingularSubcomplexMap_app]; simp
  rw [τ.mass_eq_setIntegral_normDet hg, mass_def, ← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on (τ.integrableOn_normDet_mfderivWithin hg)
    ((σ.integrableOn_normDet_mfderivWithin σ.extension_coe).const_mul (C ^ p))
    (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mfderivWithin_comp_extension hf σ hx]
  have hbound := LinearMap.normDet_comp_le_pow_finrank_mul (E := EuclideanSpace ℝ (Fin p))
    (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap
    (mfderiv I J f (σ.extension x)).toLinearMap (hLip (σ.extension x))
  rw [finrank_euclideanSpace_fin] at hbound; exact hbound

/-- A smooth map whose differential preserves tangent inner products preserves simplex mass. -/
theorem mass_smoothSingularSubcomplexMap_app_of_inner_mfderiv {f : M → N} (hf : ContMDiff I J ∞ f)
    (hinner : ∀ x (v w : TangentSpace I x),
      inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w)
    (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) = σ.mass := by
  let τ : SmoothSimplex J N p := (smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ
  have hg (x : fullSimplex p) : (f ∘ σ.extension) x = τ.toContinuousMap x := by
    rw [Function.comp_apply, toContinuousMap_smoothSingularSubcomplexMap_app]; simp
  rw [τ.mass_eq_setIntegral_normDet hg, mass_def]
  exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ by
    rw [mfderivWithin_comp_extension hf σ hx]
    exact LinearMap.normDet_comp_of_inner_eq (E := EuclideanSpace ℝ (Fin p)) _ _
      (hinner (σ.extension x))

/-- Smooth Riemannian isometries preserve the mass of every smooth simplex. -/
theorem mass_smoothSingularSubcomplexMap_riemannianIsometry
    (Φ : RiemannianIsometry I J M N) (σ : SmoothSimplex I M p) :
    mass ((smoothSingularSubcomplexMap Φ Φ.toDiffeomorph.contMDiff).app (op ⦋p⦌) σ) = σ.mass :=
  mass_smoothSingularSubcomplexMap_app_of_inner_mfderiv Φ.toDiffeomorph.contMDiff Φ.inner_mfderiv σ

end Functoriality

/-! ### Reparametrization invariance, top-degree volume form, and subdivision mass -/

private theorem normDet_mfderivWithin_comp_of_hasFDerivWithinAt (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p)) {x : EuclideanSpace ℝ (Fin p)}
    (hx : x ∈ fullSimplex p) {L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hΨ : HasFDerivWithinAt Ψ L (fullSimplex p) x) :
    LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I (σ.extension ∘ Ψ) (fullSimplex p) x).toLinearMap =
    |L.det| • LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) (Ψ x)).toLinearMap := by
  have hcomp := ((σ.contMDiffOn_extension (Ψ x) (hmaps hx)).mdifferentiableWithinAt
    (by simp)).hasMFDerivWithinAt.comp x hΨ.hasMFDerivWithinAt hmaps
  rw [hcomp.mfderivWithin
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_fullSimplex p x hx))]
  let L₁ : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p) := L.toLinearMap
  let L₂ : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] TangentSpace I (σ.extension (Ψ x)) :=
    (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) (Ψ x)).toLinearMap
  -- `TangentSpace (𝓡 p)` is `EuclideanSpace ℝ (Fin p)` only definitionally, blocking
  -- `ContinuousLinearMap.coe_comp` from matching via `rw`.
  change LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) (L₂ ∘ₗ L₁) =
    |LinearMap.det L₁| • LinearMap.normDet (U := EuclideanSpace ℝ (Fin p)) L₂
  rw [LinearMap.normDet_comp_of_finrank_eq (U := EuclideanSpace ℝ (Fin p))
    (V := EuclideanSpace ℝ (Fin p)) L₁ L₂ rfl, LinearMap.normDet_eq_abs_det, smul_eq_mul, mul_comm]

/-- **Reparametrization invariance of simplex mass.** Any smooth bijective self-reparametrization
`Ψ` of `Δᵖ` (on a neighbourhood of `Δᵖ`) preserves `σ.mass`, regardless of orientation. -/
theorem mass_compContDiffOn (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin p))} (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p)) (hinj : InjOn Ψ (fullSimplex p))
    (himage : Ψ '' fullSimplex p = fullSimplex p) :
    (σ.compContDiffOn hΨ hU hmaps).mass = σ.mass := by
  rw [(σ.compContDiffOn hΨ hU hmaps).mass_eq_setIntegral_normDet (g := σ.extension ∘ Ψ) fun x ↦ by
    rw [Function.comp_apply, toContinuousMap_compContDiffOn_apply,
      σ.extension_coe ⟨Ψ x, hmaps x.property⟩]]
  have hΨfderiv (x : EuclideanSpace ℝ (Fin p)) (hx : x ∈ fullSimplex p) :
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) (fullSimplex p) x :=
    ((hΨ.contDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet
    (fun x hx ↦ σ.normDet_mfderivWithin_comp_of_hasFDerivWithinAt hmaps hx (hΨfderiv x hx)),
    mass_def]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet hΨfderiv hinj
    (fun y ↦ LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
      (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) y).toLinearMap)
  rw [himage] at hcov; exact hcov.symm

/-- Permuting the vertices of a smooth simplex leaves its mass unchanged. -/
@[simp]
theorem mass_compPerm (σ : SmoothSimplex I M p) (e : Equiv.Perm (Fin (p + 1))) :
    (σ.compPerm e).mass = σ.mass := by
  rw [σ.compPerm_eq_compContDiffOn e]
  exact σ.mass_compContDiffOn _ Filter.univ_mem (mapsTo_simplexMapAmbient e)
    (simplexMapAmbient_perm_injective e).injOn (image_simplexMapAmbient_perm e)

section OrientedVolume
variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- **Pointwise top-degree volume comparison.** `|σ*(vol_o)(e)| = normDet (dσ)` in dimension `p`. -/
theorem abs_mpullbackWithin_riemannianVolumeForm (o : Manifold.Orientation I M (Fin p))
    (σ : SmoothSimplex I M p) (x : EuclideanSpace ℝ (Fin p)) :
    |mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x fun i ↦ EuclideanSpace.single i 1| =
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap := by
  refine (congrArg abs (mpullbackWithin_apply (I := 𝓡 p) (I' := I) σ.extension (fullSimplex p)
    (riemannianVolumeForm o) x (fun i ↦ EuclideanSpace.single i (1 : ℝ)))).trans ?_
  rw [riemannianVolumeForm_apply]; let := o.fact_finrank_tangentSpace (σ.extension x)
  rw [Orientation.abs_volumeForm_apply_eq_sqrt_det_gram]
  have hsq := LinearMap.normDet_sq_eq_det_gram (U := EuclideanSpace ℝ (Fin p))
    (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap
    (EuclideanSpace.basisFun (Fin p) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq, EuclideanSpace.basisFun_apply] at hsq
  have hgram : (Matrix.gram ℝ fun i ↦
        mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x (EuclideanSpace.single i 1)).det =
      LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap ^ 2 := by
    rw [hsq]
    -- `.toLinearMap` is read on `EuclideanSpace ℝ (Fin p)`, which is `TangentSpace (𝓡 p) x`
    -- only definitionally, so `ContinuousLinearMap.coe_coe` cannot rewrite across the two domains.
    rfl
  exact (congrArg Real.sqrt hgram).trans
    (Real.sqrt_sq (LinearMap.normDet_nonneg (U := EuclideanSpace ℝ (Fin p)) _))

/-- Integrating `riemannianVolumeForm` over a positively oriented smooth simplex yields `σ.mass`. -/
theorem integral_riemannianVolumeForm_eq_mass (o : Manifold.Orientation I M (Fin p))
    (σ : SmoothSimplex I M p)
    (hpos : ∀ x ∈ fullSimplex p,
      0 ≤ mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x fun i ↦ EuclideanSpace.single i 1) :
    σ.integral (riemannianVolumeForm o) = σ.mass := by
  rw [integral_def, mass_def]
  exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ by
    rw [← abs_of_nonneg (hpos x hx), abs_mpullbackWithin_riemannianVolumeForm]

/-- Integrating `riemannianVolumeForm` over a negatively oriented smooth simplex gives `-σ.mass`. -/
theorem integral_riemannianVolumeForm_eq_neg_mass (o : Manifold.Orientation I M (Fin p))
    (σ : SmoothSimplex I M p)
    (hneg : ∀ x ∈ fullSimplex p,
      mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p)
        (riemannianVolumeForm o) x (fun i ↦ EuclideanSpace.single i 1) ≤ 0) :
    σ.integral (riemannianVolumeForm o) = -σ.mass := by
  rw [integral_def, mass_def, ← MeasureTheory.integral_neg]
  exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ by
    rw [← abs_mpullbackWithin_riemannianVolumeForm, abs_of_nonpos (hneg x hx), neg_neg]

end OrientedVolume

/-- **Barycentric subdivision preserves simplex mass.** -/
theorem sum_mass_compAffineMapMk_vertex [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (σ : SmoothSimplex I M p) :
    ∑ e : Equiv.Perm (Fin (p + 1)),
      (σ.compAffineMapMk (BarycentricSubdivision.vertex e)).mass = σ.mass := by
  have hterm (e : Equiv.Perm (Fin (p + 1))) :
      (σ.compAffineMapMk (BarycentricSubdivision.vertex e)).mass =
        ∫ x in fullSimplex p,
          |(affineMapAmbient (BarycentricSubdivision.vertex e)).contLinear.det| •
            LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
              (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p)
                (affineMapAmbient (BarycentricSubdivision.vertex e) x)).toLinearMap := by
    let A := affineMapAmbient (BarycentricSubdivision.vertex e)
    rw [(σ.compAffineMapMk (BarycentricSubdivision.vertex e)).mass_eq_setIntegral_normDet
      (g := σ.extension ∘ A) fun x ↦ by
        rw [Function.comp_apply, toContinuousMap_compAffineMapMk_apply,
          σ.extension_coe ⟨A x, mapsTo_affineMapAmbient _ x.property⟩]]
    exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦
      σ.normDet_mfderivWithin_comp_of_hasFDerivWithinAt (mapsTo_affineMapAmbient _) hx
        A.hasFDerivAt.hasFDerivWithinAt
  simp_rw [hterm]
  exact BarycentricSubdivision.sum_setIntegral_affineMapAmbient_vertex
    (σ.integrableOn_normDet_mfderivWithin σ.extension_coe)

/-! ### Comass and calibration bounds on smooth simplices -/

section Comass
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Pointwise comass inequality:** `‖σ*φ(e)‖ ≤ ‖φ‖ * normDet (dσ)`, without assuming
`FiniteDimensional ℝ E`. -/
theorem norm_mpullbackWithin_le_opNorm_mul_normDet (σ : SmoothSimplex I M p)
    (φ : RoughForm I M F p) (x : EuclideanSpace ℝ (Fin p)) :
    ‖mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ x
        fun i ↦ EuclideanSpace.single i 1‖ ≤
      ‖φ (σ.extension x)‖ * LinearMap.normDet (U := EuclideanSpace ℝ (Fin p))
        (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap := by
  let L : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] TangentSpace I (σ.extension x) :=
    (mfderivWithin (𝓡 p) I σ.extension (fullSimplex p) x).toLinearMap
  let W := L.range
  let ω' : W [⋀^Fin p]→L[ℝ] F := (φ (σ.extension x)).compContinuousLinearMap W.subtypeL
  have hω' : ‖ω'‖ ≤ ‖φ (σ.extension x)‖ :=
    (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal
      (norm_nonneg (φ (σ.extension x)))).mpr fun v hv ↦
      (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal
        (norm_nonneg (φ (σ.extension x)))).mp le_rfl _ (hv.comp_linearIsometry W.subtypeₗᵢ)
  have hbound := ContinuousAlternatingMap.le_opNorm_mul_normDet ω' L.rangeRestrict
    (EuclideanSpace.basisFun (Fin p) ℝ)
  rw [LinearMap.normDet_codRestrict (f := L) (LinearMap.mem_range_self L)] at hbound
  refine le_trans ?_ (hbound.trans (mul_le_mul_of_nonneg_right hω' L.normDet_nonneg))
  refine le_of_eq (congrArg norm ((mpullbackWithin_apply (I := 𝓡 p) (I' := I) σ.extension
    (fullSimplex p) φ x (fun i ↦ EuclideanSpace.single i (1 : ℝ))).trans ?_))
  simp only [ω', ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1; funext i
  simp only [Function.comp_apply, Submodule.subtypeL_apply, LinearMap.codRestrict_apply,
    EuclideanSpace.basisFun_apply]
  -- `L` is `(mfderivWithin ...).toLinearMap` with `TangentSpace (𝓡 p) x` read definitionally as
  -- `EuclideanSpace ℝ (Fin p)`.
  rfl

section ComassIntegrated
variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **Comass bound on a smooth simplex:** if `‖φ‖ ≤ C` on `σ`, then `‖∫_σ φ‖ ≤ C * σ.mass`. -/
theorem norm_integral_le_mul_mass (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) {C : ℝ}
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

/-- **Comass bound via orthonormal frames** along `σ`. -/
theorem norm_integral_le_mul_mass_of_orthonormal (σ : SmoothSimplex I M p) (φ : RoughForm I M F p)
    {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x : fullSimplex p, ∀ v : Fin p → TangentSpace I (σ.toContinuousMap x),
      Orthonormal ℝ v → ‖φ (σ.toContinuousMap x) v‖ ≤ C) :
    ‖σ.integral φ‖ ≤ C * σ.mass :=
  σ.norm_integral_le_mul_mass φ fun x ↦
    (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal hC).mpr (hφ x)

/-- **Calibration bound on a smooth simplex:** `|φ v| ≤ 1` implies `|∫_σ φ| ≤ σ.mass`. -/
theorem abs_integral_le_mass_of_orthonormal (σ : SmoothSimplex I M p) (φ : RoughForm I M ℝ p)
    (hφ : ∀ x : fullSimplex p, ∀ v : Fin p → TangentSpace I (σ.toContinuousMap x),
      Orthonormal ℝ v → |φ (σ.toContinuousMap x) v| ≤ 1) :
    |σ.integral φ| ≤ σ.mass := by
  simpa only [Real.norm_eq_abs, one_mul] using
    σ.norm_integral_le_mul_mass_of_orthonormal φ zero_le_one hφ

end ComassIntegrated

end Comass

end SmoothSimplex

end TauCeti
