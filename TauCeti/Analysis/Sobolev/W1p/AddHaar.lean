/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Restriction
public import TauCeti.Analysis.Sobolev.W1p.Zero
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.AddHaar

/-!
# `W^{1,p}(Ω)` does not depend on the choice of Haar measure

Let `μ` and `ν` be additive Haar measures on a finite-dimensional real inner product space `E`.
They differ by a positive finite factor, `ν = c • μ`
(`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`), so they have the same null sets, the same
`Lᵖ` functions, and the same weak derivatives (`TauCeti.HasWeakFDerivOn.of_isAddHaarMeasure`).
Hence `W^{1,p}(Ω)` built on `μ` and on `ν` consist of the same functions, with equivalent norms.
This file packages this as a continuous linear equivalence

`TauCeti.W1p.addHaarEquivL μ ν : W^{1,p}_μ(Ω) ≃L[ℝ] W^{1,p}_ν(Ω)`,

which keeps the value and the weak gradient of every function
(`TauCeti.W1p.value_addHaarEquivL_ae`, `TauCeti.W1p.gradient_addHaarEquivL_ae`), commutes with
restriction to smaller open sets and with the embedding of test functions, and preserves
`W^{1,p}_0(Ω)` in both directions (`TauCeti.W1p.addHaarEquivL_mem_w1p0Submodule_iff`).

Results proved for one Haar measure, typically `volume`, transfer through it to every other
additive Haar measure, such as the one an energy form or a boundary-value problem is stated with.

## Main declarations

* `TauCeti.W1p.addHaarEquivL`: the equivalence, with `TauCeti.W1p.addHaarEquivL_symm`.
* `TauCeti.W1p.value_addHaarEquivL_ae` and `TauCeti.W1p.gradient_addHaarEquivL_ae`: it is the
  identity on values and gradients.
* `TauCeti.W1p.addHaarEquivL_restrictL` and `TauCeti.W1p.addHaarEquivL_ofTestFunctionₗ`: it
  commutes with restriction and with the embedding of test functions.
* `TauCeti.W1p.addHaarEquivL_mem_w1p0Submodule_iff`: it preserves zero boundary values.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Distributions

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] (mu nu : Measure E) [mu.IsAddHaarMeasure]
  [nu.IsAddHaarMeasure] {Omega U : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The identity of value-gradient jets -/

omit [Fact (1 ≤ p)] in
/-- On an open set, `ν` is at most the finite multiple `addHaarScalarFactor ν μ` of `μ`. -/
private theorem restrict_le_smul_restrict (Omega : Opens E) :
    nu.restrict Omega ≤ (nu.addHaarScalarFactor mu : ℝ≥0∞) • mu.restrict Omega := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul nu mu]
  rw [Measure.restrict_smul]
  exact le_rfl

omit [Fact (1 ≤ p)] in
/-- Almost-everywhere statements on `Ω` pass from `μ` to `ν`. -/
private theorem ae_restrict_le (Omega : Opens E) :
    ae (nu.restrict Omega) ≤ ae (mu.restrict Omega) :=
  ((Measure.absolutelyContinuous_isAddHaarMeasure nu mu).restrict _).ae_le

/-- The identity of value-gradient jets, from `Lᵖ(Ω, μ)` to `Lᵖ(Ω, ν)`. -/
private def jetL : Sobolev1JetLp mu Omega p →L[ℝ] Sobolev1JetLp nu Omega p :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top (restrict_le_smul_restrict mu nu Omega)

private theorem coeFn_jetL (J : Sobolev1JetLp mu Omega p) :
    jetL mu nu J =ᵐ[nu.restrict Omega] J :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ J

/-- The jet of a Sobolev function for `μ` is one for `ν`. -/
private theorem jetL_mem_w1pSubmodule (u : W1p mu Omega p) :
    jetL mu nu (u : Sobolev1JetLp mu Omega p) ∈ w1pSubmodule nu Omega p := by
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  set J := jetL mu nu (u : Sobolev1JetLp mu Omega p)
  have hJ := coeFn_jetL mu nu (u : Sobolev1JetLp mu Omega p)
  have hvalue : Sobolev1JetLp.value J =ᵐ[nu.restrict Omega] W1p.value u := by
    filter_upwards [Sobolev1JetLp.value_apply_ae J,
      (W1p.value_apply_ae u).filter_mono (ae_restrict_le mu nu _), hJ] with x hJv huv hJu
    rw [hJv, huv, hJu]
  have hgradient : Sobolev1JetLp.gradient J =ᵐ[nu.restrict Omega] W1p.gradient u := by
    filter_upwards [Sobolev1JetLp.gradient_apply_ae J,
      (W1p.gradient_apply_ae u).filter_mono (ae_restrict_le mu nu _), hJ] with x hJg hug hJu
    rw [hJg, hug, hJu]
  refine ((W1p.hasWeakFDerivOn u).of_isAddHaarMeasure nu).congr_ae hvalue.symm
    |>.congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  rw [Sobolev1JetLp.candidateWeakFDeriv_def, hx]

/-- The identity of `W^{1,p}(Ω)`, from `μ` to `ν`, as a bounded operator. -/
private def addHaarL : W1p mu Omega p →L[ℝ] W1p nu Omega p :=
  ContinuousLinearMap.codRestrict
    ((jetL mu nu).comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL)
    (w1pSubmodule nu Omega p).toSubmodule (jetL_mem_w1pSubmodule mu nu)

private theorem value_addHaarL_ae (u : W1p mu Omega p) :
    W1p.value (addHaarL mu nu u) =ᵐ[nu.restrict Omega] W1p.value u := by
  filter_upwards [W1p.value_apply_ae (addHaarL mu nu u),
    coeFn_jetL mu nu (u : Sobolev1JetLp mu Omega p),
    (W1p.value_apply_ae u).filter_mono (ae_restrict_le mu nu _)] with x h1 h2 h3
  rw [h1, h3]
  exact congrArg WithLp.fst h2

private theorem gradient_addHaarL_ae (u : W1p mu Omega p) :
    W1p.gradient (addHaarL mu nu u) =ᵐ[nu.restrict Omega] W1p.gradient u := by
  filter_upwards [W1p.gradient_apply_ae (addHaarL mu nu u),
    coeFn_jetL mu nu (u : Sobolev1JetLp mu Omega p),
    (W1p.gradient_apply_ae u).filter_mono (ae_restrict_le mu nu _)] with x h1 h2 h3
  rw [h1, h3]
  exact congrArg WithLp.snd h2

private theorem addHaarL_addHaarL (u : W1p mu Omega p) :
    addHaarL nu mu (addHaarL mu nu u) = u := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_addHaarL_ae nu mu (addHaarL mu nu u),
    (value_addHaarL_ae mu nu u).filter_mono (ae_restrict_le nu mu _)] with x h1 h2
  rw [h1, h2]

/-! ### The equivalence -/

/-- **`W^{1,p}(Ω)` does not depend on the Haar measure.** For additive Haar measures `μ` and `ν`,
the identity on functions is a continuous linear equivalence between `W^{1,p}(Ω)` built on `μ`
and `W^{1,p}(Ω)` built on `ν`: it keeps the value (`TauCeti.W1p.value_addHaarEquivL_ae`) and the
weak gradient (`TauCeti.W1p.gradient_addHaarEquivL_ae`). -/
def W1p.addHaarEquivL : W1p mu Omega p ≃L[ℝ] W1p nu Omega p :=
  ContinuousLinearEquiv.ofContinuousLinearMap (addHaarL mu nu) (addHaarL nu mu)
    (ContinuousLinearMap.ext (addHaarL_addHaarL nu mu))
    (ContinuousLinearMap.ext (addHaarL_addHaarL mu nu))

/-- The value of `u` is kept by `TauCeti.W1p.addHaarEquivL`. -/
theorem W1p.value_addHaarEquivL_ae (u : W1p mu Omega p) :
    W1p.value (W1p.addHaarEquivL mu nu u) =ᵐ[nu.restrict Omega] W1p.value u :=
  value_addHaarL_ae mu nu u

/-- The weak gradient of `u` is kept by `TauCeti.W1p.addHaarEquivL`. -/
theorem W1p.gradient_addHaarEquivL_ae (u : W1p mu Omega p) :
    W1p.gradient (W1p.addHaarEquivL mu nu u) =ᵐ[nu.restrict Omega] W1p.gradient u :=
  gradient_addHaarL_ae mu nu u

/-- The inverse of the change of Haar measure from `μ` to `ν` is the one from `ν` to `μ`. -/
@[simp]
theorem W1p.addHaarEquivL_symm :
    (W1p.addHaarEquivL mu nu : W1p mu Omega p ≃L[ℝ] W1p nu Omega p).symm =
      W1p.addHaarEquivL nu mu :=
  ContinuousLinearEquiv.symm_ofContinuousLinearMap _ _ _ _

/-- A Sobolev function for `ν` is equal to the image of one for `μ` exactly when their values
agree almost everywhere on `Ω`. -/
theorem W1p.addHaarEquivL_eq_iff {u : W1p mu Omega p} {v : W1p nu Omega p} :
    W1p.addHaarEquivL mu nu u = v ↔ W1p.value u =ᵐ[nu.restrict Omega] W1p.value v := by
  refine ⟨fun h => h ▸ (W1p.value_addHaarEquivL_ae mu nu u).symm, fun h => ?_⟩
  exact W1p.ext_value (Lp.ext ((W1p.value_addHaarEquivL_ae mu nu u).trans h))

/-- The change of Haar measure commutes with restriction to a smaller open set. -/
@[simp]
theorem W1p.addHaarEquivL_restrictL (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.addHaarEquivL mu nu (W1p.restrictL hU u) =
      W1p.restrictL hU (W1p.addHaarEquivL mu nu u) := by
  rw [W1p.addHaarEquivL_eq_iff]
  filter_upwards [(W1p.value_restrictL_ae hU u).filter_mono (ae_restrict_le mu nu _),
    W1p.value_restrictL_ae hU (W1p.addHaarEquivL mu nu u),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hU)
      (W1p.value_addHaarEquivL_ae mu nu u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The change of Haar measure sends an embedded test function to the same test function. -/
@[simp]
theorem W1p.addHaarEquivL_ofTestFunctionₗ (φ : 𝓓(Omega, ℝ)) :
    W1p.addHaarEquivL mu nu (W1p.ofTestFunctionₗ mu Omega p φ) =
      W1p.ofTestFunctionₗ nu Omega p φ := by
  rw [W1p.addHaarEquivL_eq_iff]
  filter_upwards [(W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := p) φ).filter_mono
      (ae_restrict_le mu nu _), W1p.value_ofTestFunctionₗ_ae (mu := nu) (p := p) φ]
    with x h1 h2
  rw [h1, h2]

omit [Fact (1 ≤ p)] in
/-- The change of Haar measure maps `W^{1,p}_0(Ω)` into `W^{1,p}_0(Ω)`. -/
private theorem addHaarEquivL_mem_w1p0Submodule [Fact (1 ≤ p)] {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.addHaarEquivL mu nu u ∈ w1p0Submodule nu Omega p := by
  refine w1p0Submodule_subset_of_isClosed (p := p)
    ((w1p0Submodule nu Omega p).isClosed.preimage (W1p.addHaarEquivL mu nu).continuous)
    (fun φ => ?_) hu
  rw [Set.mem_preimage, W1p.addHaarEquivL_ofTestFunctionₗ]
  exact W1p.ofTestFunctionₗ_mem_w1p0Submodule φ

/-- **The change of Haar measure preserves zero boundary values**: `u` lies in `W^{1,p}_0(Ω)` for
`μ` exactly when its image lies in `W^{1,p}_0(Ω)` for `ν`. -/
@[simp]
theorem W1p.addHaarEquivL_mem_w1p0Submodule_iff {u : W1p mu Omega p} :
    W1p.addHaarEquivL mu nu u ∈ w1p0Submodule nu Omega p ↔ u ∈ w1p0Submodule mu Omega p := by
  refine ⟨fun hu => ?_, addHaarEquivL_mem_w1p0Submodule mu nu⟩
  have h := addHaarEquivL_mem_w1p0Submodule nu mu hu
  rwa [← W1p.addHaarEquivL_symm, ContinuousLinearEquiv.symm_apply_apply] at h

end TauCeti
