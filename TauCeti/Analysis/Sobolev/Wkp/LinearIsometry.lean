/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Affine
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

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [FiniteDimensional ℝ E'] [ν.IsAddHaarMeasure] in
private theorem measurePreserving_restrict (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) :
    MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
  hUW ▸ he.restrict_preimage W.isOpen.measurableSet

private theorem norm_compAffineEquiv_zero (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    ‖compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u‖ = ‖u‖ :=
  norm_eq_of_measurePreserving (measurePreserving_restrict he hUW)
    (fun j w ↦ compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) j w)
    (fun j w ↦ lowerOrder_compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) j w)
    (fun j w ↦ by
      filter_upwards [value_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0
        (by simpa using hUW) j w] with x hx
      rw [hx, add_zero, LinearIsometryEquiv.coe_toContinuousLinearEquiv])
    (fun j w ↦ by
      filter_upwards [iteratedGradient_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0
        (by simpa using hUW) j w] with x hx
      rw [hx, add_zero, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm]
      exact (e.iteratedGradientCongr j).symm.norm_map _)
    k u

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

/-- Evaluating `compLinearIsometryEquiv` applies `compAffineEquiv` with zero translation. -/
theorem compLinearIsometryEquiv_apply (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    compLinearIsometryEquiv he hUW k u =
      compAffineEquiv μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u := by
  simp [compLinearIsometryEquiv]

/-- For a measure-preserving linear isometry `e`, `compAffineL` with zero translation agrees with
`TauCeti.Wkp.compLinearIsometryEquiv`. -/
theorem compAffineL_eq_compLinearIsometryEquiv {μ : Measure E} [μ.IsAddHaarMeasure]
    (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ)
    (u : Wkp ν W p k) :
    compAffineL μ e.toContinuousLinearEquiv 0
        (fun x hx ↦ by simpa [hUW] using hx) k u =
      compLinearIsometryEquiv he hUW k u := by
  rw [compLinearIsometryEquiv_apply, compAffineEquiv_apply]

/-- The inverse of the transport along `e` is the transport along `e⁻¹`. -/
theorem compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (he' : MeasurePreserving e.symm ν μ)
    (hWU : (W : Set E') = e.symm ⁻¹' U) (k : ℕ) :
    (compLinearIsometryEquiv (p := p) he hUW k).symm = compLinearIsometryEquiv he' hWU k := by
  refine LinearIsometryEquiv.ext fun u ↦ (compLinearIsometryEquiv he hUW k).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, compLinearIsometryEquiv_apply]
  refine Eq.symm <| (compAffineEquiv_eq_iff μ _ 0 (by simpa using hUW) k _ _).2 ?_
  filter_upwards [(measurePreserving_restrict he hUW).quasiMeasurePreserving.ae
    (value_compAffineEquiv_ae ν e.symm.toContinuousLinearEquiv 0 (by simpa using hWU) k u)]
    with x hx
  rw [compLinearIsometryEquiv_apply]
  simpa using hx.symm

/-- The value of `u ∘ e` is the value of `u` composed with `e`. -/
theorem value_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    value k (compLinearIsometryEquiv he hUW k u) =ᵐ[μ.restrict U] fun x => value k u (e x) := by
  rw [compLinearIsometryEquiv_apply]
  simpa only [add_zero, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    value_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k u

/-- **The chain rule for the highest derivative.** The weak derivative of order `k + 1` of `u ∘ e`
at `x` is that of `u` at `e x`, pulled back by `e` in every slot; at order two it is
`e† ∘ D²u(e x) ∘ e` (`LinearIsometryEquiv.iteratedGradientCongr_symm_succ_apply`). -/
theorem iteratedGradient_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compLinearIsometryEquiv he hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x => (e.iteratedGradientCongr k).symm (iteratedGradient k u (e x)) := by
  rw [compLinearIsometryEquiv_apply]
  filter_upwards [iteratedGradient_compAffineEquiv_ae μ e.toContinuousLinearEquiv 0
    (by simpa using hUW) k u] with x hx
  simpa only [add_zero, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.iteratedGradientPullback_eq_iteratedGradientCongr_symm,
    LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv] using hx

/-- The transport commutes with forgetting the highest derivative. -/
theorem lowerOrder_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    lowerOrder k (compLinearIsometryEquiv he hUW (k + 1) u) =
      compLinearIsometryEquiv he hUW k (lowerOrder k u) := by
  rw [compLinearIsometryEquiv_apply, compLinearIsometryEquiv_apply, lowerOrder_compAffineEquiv]

/-- The transport of a test function `φ` on `W` is the test function `φ ∘ e` on `U`. -/
theorem compLinearIsometryEquiv_ofTestFunctionₗ (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (hWU : MapsTo e.symm W U) (k : ℕ) (φ : 𝓓(W, ℝ)) :
    compLinearIsometryEquiv he hUW k (ofTestFunctionₗ (mu := ν) (p := p) k φ) =
      ofTestFunctionₗ k (e.symm.toContinuousLinearEquiv.transportTestFunction ℝ hWU φ) := by
  rw [compLinearIsometryEquiv_apply]
  refine (compAffineEquiv_ofTestFunctionₗ (ν := ν) (p := p) μ e.toContinuousLinearEquiv 0
    (by simpa using hUW) k φ).trans (congrArg (ofTestFunctionₗ k) ?_)
  ext x
  rw [translateTestFunction_apply]
  refine (ContinuousLinearEquiv.transportTestFunction_apply _ _ φ _).trans ?_
  refine Eq.trans ?_ (ContinuousLinearEquiv.transportTestFunction_apply _ _ φ _).symm
  simp [← LinearIsometryEquiv.toContinuousLinearEquiv_symm]

/-- The transport maps `W^{k,p}_0(W)` into `W^{k,p}_0(U)`. -/
theorem compLinearIsometryEquiv_mem_wkp0Submodule (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} (hu : u ∈ wkp0Submodule ν W p k) :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k := by
  rw [compLinearIsometryEquiv_apply]
  exact compAffineEquiv_mem_wkp0Submodule μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k hu

/-- **Zero boundary values are invariant under linear isometries.** The transport `u ∘ e` lies in
`W^{k,p}_0(U)` exactly when `u` lies in `W^{k,p}_0(W)`. -/
@[simp]
theorem compLinearIsometryEquiv_mem_wkp0Submodule_iff (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k ↔ u ∈ wkp0Submodule ν W p k := by
  rw [compLinearIsometryEquiv_apply]
  exact compAffineEquiv_mem_wkp0Submodule_iff μ e.toContinuousLinearEquiv 0 (by simpa using hUW) k

end Wkp

end TauCeti
