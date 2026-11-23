/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.AffineScaling
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# Transport of `W^{k,p}` along linear isometries

Let `e : E ≃ₗᵢ[ℝ] E'` be a linear isometry between finite-dimensional real inner product spaces
carrying `μ` to `ν` (for instance `volume` to `volume`, `LinearIsometryEquiv.measurePreserving`),
and let `U = e⁻¹(W)` for open sets `U ⊆ E` and `W ⊆ E'`. For every order `k` and every exponent
`1 ≤ p ≤ ∞`, precomposition with `e` is a linear isometric equivalence

`TauCeti.Wkp.compLinearIsometryEquiv : W^{k,p}(W) ≃ₗᵢ[ℝ] W^{k,p}(U)`.

The value of `u ∘ e` is `u ∘ e`, and its weak derivative of order `k + 1` at `x` is the highest
weak derivative of `u` at `e x`, pulled back by `e` in every slot: at order two this is
`D²(u ∘ e)(x) = e† ∘ D²u(e x) ∘ e`, the formula of
`TauCeti.Wkp.iteratedGradient_compAffineEquiv_ae`, where `e† = e⁻¹` is the adjoint of `e`.
The pullback of iterated gradients is `(e.iteratedGradientCongr j).symm`, where
`LinearIsometryEquiv.iteratedGradientCongr` pushes iterated gradients forward along `e`.
Zero boundary values are preserved and reflected: a test function on `W` composed with `e` is a
test function on `U`.

This transports results stated on a model space, such as the Lipschitz-domain theorems on
`WithLp 2 (ℝ × E)`, to any isometric copy of it, for instance from `WithLp 2 (ℝ × ℝ)` to `ℂ`
along `Complex.equivRealProdL2`.

## The argument

`TauCeti.Wkp.compLinearIsometryEquiv` is the specialization of `TauCeti.Wkp.compAffineEquiv` to the
continuous linear equivalence `e.toContinuousLinearEquiv` and zero translation. Norm preservation
follows by induction on `k` from measure preservation of `e` and
`LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm`.

## Main declarations

* `TauCeti.Wkp.compLinearIsometryEquiv`: precomposition with `e` on `W^{k,p}`.
* `TauCeti.Wkp.compAffineL_eq_compLinearIsometryEquiv`: `compAffineL` with zero translation agrees
  with `compLinearIsometryEquiv`.
* `TauCeti.Wkp.value_compLinearIsometryEquiv_ae`,
  `TauCeti.Wkp.iteratedGradient_compLinearIsometryEquiv_ae`: its value and highest derivative.
* `TauCeti.Wkp.compLinearIsometryEquiv_mem_wkp0Submodule_iff`: zero boundary values are preserved
  and reflected.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Opens E} {W : Opens E'} {e : E ≃ₗᵢ[ℝ] E'}

namespace Wkp

private theorem norm_compAffineEquiv_zero (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) :
    ∀ (k : ℕ) (u : Wkp ν W p k),
      ‖compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u‖ = ‖u‖
  | 0, u => by
    have hres : MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
      hUW ▸ he.restrict_preimage W.isOpen.measurableSet
    rw [← value_zero (compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) 0 u),
      Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal <|
      (eLpNorm_congr_ae (by simpa using
        value_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0 (by simpa using hUW) 0 u)).trans
        (by
          rw [← Function.comp_def]
          exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable _) hres)
  | 1, u => by
    have hres : MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
      hUW ▸ he.restrict_preimage W.isOpen.measurableSet
    let v : W1p μ U p := compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) 1 u
    let u₁ : W1p ν W p := u
    have hv_norm : ∀ᵐ x ∂μ.restrict U,
        ‖(v : Sobolev1JetLp μ U p) x‖ = ‖(u₁ : Sobolev1JetLp ν W p) (e x)‖ := by
      filter_upwards [W1p.norm_apply_sq_ae v,
        hres.quasiMeasurePreserving.ae (W1p.norm_apply_sq_ae u₁),
        value_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0 (by simpa using hUW) 1 u,
        iteratedGradient_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0 (by simpa using hUW) 0 u]
        with x h1 h2 hx hg
      rw [value_one, value_one] at hx
      rw [iteratedGradient_zero, iteratedGradient_zero,
        LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm,
        LinearIsometryEquiv.iteratedGradientCongr_zero] at hg
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [h1, h2, hx, hg]
      simp [u₁]
    change ‖v‖ = ‖u₁‖
    have hm : AEStronglyMeasurable (u₁ : Sobolev1JetLp ν W p) (ν.restrict W) :=
      Lp.aestronglyMeasurable _
    rw [← Submodule.norm_coe v, ← Submodule.norm_coe u₁, Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal <|
      (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        (hm.comp_quasiMeasurePreserving hres.quasiMeasurePreserving)
        hv_norm).trans (eLpNorm_comp_measurePreserving hm hres)
  | k + 2, u => by
    have hres : MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
      hUW ▸ he.restrict_preimage W.isOpen.measurableSet
    let w := compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) (k + 2) u
    have hlow : ‖lowerOrder (k + 1) w‖ = ‖lowerOrder (k + 1) u‖ := by
      dsimp only [w]
      rw [lowerOrder_compAffineEquiv]
      exact norm_compAffineEquiv_zero he hUW (k + 1) (lowerOrder (k + 1) u)
    have hgrad_ae : ∀ᵐ x ∂μ.restrict U,
        ‖iteratedGradient (k + 1) w x‖ = ‖iteratedGradient (k + 1) u (e x)‖ := by
      filter_upwards [iteratedGradient_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0
        (by simpa using hUW) (k + 1) u] with x hx
      rw [hx, add_zero, LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm]
      exact (e.iteratedGradientCongr (k + 1)).symm.norm_map _
    have hgrad : ‖iteratedGradient (k + 1) w‖ = ‖iteratedGradient (k + 1) u‖ := by
      have hm : AEStronglyMeasurable (iteratedGradient (k + 1) u) (ν.restrict W) :=
        Lp.aestronglyMeasurable _
      rw [Lp.norm_def, Lp.norm_def]
      exact congrArg ENNReal.toReal <|
        (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
          (hm.comp_quasiMeasurePreserving hres.quasiMeasurePreserving)
          hgrad_ae).trans (eLpNorm_comp_measurePreserving hm hres)
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k w,
      norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u, hlow, hgrad]

/-- **Transport of `W^{k,p}` along a linear isometry.** If the linear isometry `e` carries `μ`
to `ν` and `U = e⁻¹(W)`, precomposition with `e` is a linear isometric equivalence
`W^{k,p}(W) ≃ₗᵢ[ℝ] W^{k,p}(U)` for every order `k` and every exponent `1 ≤ p ≤ ∞`. Its value and
highest derivative are `TauCeti.Wkp.value_compLinearIsometryEquiv_ae` and
`TauCeti.Wkp.iteratedGradient_compLinearIsometryEquiv_ae`. -/
def compLinearIsometryEquiv (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (k : ℕ) : Wkp ν W p k ≃ₗᵢ[ℝ] Wkp μ U p k where
  toLinearEquiv :=
    (compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k).toLinearEquiv
  norm_map' := norm_compAffineEquiv_zero he hUW k

/-- For a measure-preserving linear isometry `e`, `compAffineL` with zero translation agrees with
`TauCeti.Wkp.compLinearIsometryEquiv`. -/
theorem compAffineL_eq_compLinearIsometryEquiv {μ : Measure E} [μ.IsAddHaarMeasure]
    (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ)
    (u : Wkp ν W p k) :
    compAffineL μ e.toContinuousLinearEquiv 0
        (fun x hx ↦ by simpa [hUW] using hx) k u =
      compLinearIsometryEquiv he hUW k u :=
  (compAffineEquiv_apply μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u).symm

/-- The inverse of the transport along `e` is the transport along `e⁻¹`. -/
theorem compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (he' : MeasurePreserving e.symm ν μ)
    (hWU : (W : Set E') = e.symm ⁻¹' U) (k : ℕ) :
    (compLinearIsometryEquiv (p := p) he hUW k).symm = compLinearIsometryEquiv he' hWU k := by
  refine LinearIsometryEquiv.ext fun u ↦ (compLinearIsometryEquiv he hUW k).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine Eq.symm <| (compAffineEquiv_eq_iff μ _ 0 (by simpa using hUW) k _ _).2 ?_
  have hres : MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
    hUW ▸ he.restrict_preimage W.isOpen.measurableSet
  filter_upwards [hres.quasiMeasurePreserving.ae
    (value_compAffineEquiv_ae ν e.symm.toContinuousLinearEquiv 0 (by simpa using hWU) k u)]
    with x hx
  simpa [compLinearIsometryEquiv] using hx.symm

/-- The value of `u ∘ e` is the value of `u` composed with `e`. -/
theorem value_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    value k (compLinearIsometryEquiv he hUW k u) =ᵐ[μ.restrict U] fun x => value k u (e x) := by
  simpa [compLinearIsometryEquiv] using
    value_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u

/-- **The chain rule for the highest derivative.** The weak derivative of order `k + 1` of `u ∘ e`
at `x` is that of `u` at `e x`, pulled back by `e` in every slot; at order two it is
`e† ∘ D²u(e x) ∘ e` (`LinearIsometryEquiv.iteratedGradientCongr_symm_succ_apply`). -/
theorem iteratedGradient_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compLinearIsometryEquiv he hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x => (e.iteratedGradientCongr k).symm (iteratedGradient k u (e x)) := by
  filter_upwards [iteratedGradient_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0
    (by simpa using hUW) k u] with x hx
  simpa [compLinearIsometryEquiv,
    LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm] using hx

/-- The transport commutes with forgetting the highest derivative. -/
theorem lowerOrder_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    lowerOrder k (compLinearIsometryEquiv he hUW (k + 1) u) =
      compLinearIsometryEquiv he hUW k (lowerOrder k u) :=
  lowerOrder_compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u

/-- The transport of a test function `φ` on `W` is the test function `φ ∘ e` on `U`. -/
theorem compLinearIsometryEquiv_ofTestFunctionₗ (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (hWU : MapsTo e.symm W U) (k : ℕ) (φ : 𝓓(W, ℝ)) :
    compLinearIsometryEquiv he hUW k (ofTestFunctionₗ (mu := ν) (p := p) k φ) =
      ofTestFunctionₗ k (e.symm.toContinuousLinearEquiv.transportTestFunction hWU φ) := by
  simpa [compLinearIsometryEquiv, ContinuousLinearEquiv.transportAddTestFunction_zero] using
    compAffineEquiv_ofTestFunctionₗ μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k φ

/-- The transport maps `W^{k,p}_0(W)` into `W^{k,p}_0(U)`. -/
theorem compLinearIsometryEquiv_mem_wkp0Submodule (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} (hu : u ∈ wkp0Submodule ν W p k) :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k :=
  compAffineEquiv_mem_wkp0Submodule μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k hu

/-- **Zero boundary values are invariant under linear isometries.** The transport `u ∘ e` lies in
`W^{k,p}_0(U)` exactly when `u` lies in `W^{k,p}_0(W)`. -/
@[simp]
theorem compLinearIsometryEquiv_mem_wkp0Submodule_iff (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k ↔ u ∈ wkp0Submodule ν W p k :=
  compAffineEquiv_mem_wkp0Submodule_iff μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k

end Wkp

end TauCeti
