/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.ContDiffMapSupportedIn

/-!
# Test-function jet restriction

For any `n : ℕ∞` with `m ≤ n` and any subset `K ⊆ E`, restricting the derivatives of a test
function on `Ω` to `K` defines a continuous linear map
`TestFunction.jetRestrictionCLM : 𝓓^{n}(Ω, F) →L[ℝ] TauCeti.JetSpace E F K m`.

## Main declarations

* `TestFunction.jetRestrictionCLM`: continuous linear `m`-jet restriction on test functions.
* `TestFunction.eval_jetRestrictionCLM`: pointwise evaluation of the `m`-jet restriction.
* `TestFunction.jetRestrictionCLM_eq_ofContDiffOn`: germ agreement with a `C^m` function on an open
  neighbourhood of `K`.
* `TestFunction.jetRestrictionCLM_eq_zero_of_tsupport_subset_compl`: tests supported off `K` have
  zero `m`-jet on `K`.
-/

public section

noncomputable section

open ContDiff Filter Set TopologicalSpace Topology
open scoped BoundedContinuousFunction ContDiff Distributions

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous linear `m`-jet restriction from `𝓓^{n}(Ω, F)` into `TauCeti.JetSpace E F K m`
whenever `m ≤ n`. -/
def jetRestrictionCLM (Ω : Opens E) (K : Set E) (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) :
    𝓓^{n}(Ω, F) →L[ℝ] TauCeti.JetSpace E F K m :=
  TestFunction.limitCLM ℝ
    (fun φ ↦
      let L : Compacts E := ⟨tsupport (φ : E → F), φ.hasCompactSupport.isCompact⟩
      ContDiffMapSupportedIn.jetRestrictionCLM K m hm L
        (.of_support_subset φ.contDiff (subset_tsupport _)))
    (fun L _ ↦ ContDiffMapSupportedIn.jetRestrictionCLM K m hm L)
    (fun L _ f ↦ TauCeti.JetSpace.ext fun k x ↦ by
      simp only [ContDiffMapSupportedIn.eval_jetRestrictionCLM]
      rw [funext (ContDiffMapSupportedIn.coe_of_support_subset _ _), coe_ofSupportedIn])

@[simp]
theorem eval_jetRestrictionCLM (Ω : Opens E) (K : Set E) (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n)
    (φ : 𝓓^{n}(Ω, F)) (k : Fin (m + 1)) (x : K) :
    (jetRestrictionCLM Ω K m hm φ).eval k x = iteratedFDeriv ℝ (k : ℕ) (φ : E → F) x.val := by
  rw [jetRestrictionCLM, TestFunction.limitCLM_apply, ContDiffMapSupportedIn.eval_jetRestrictionCLM,
    funext (ContDiffMapSupportedIn.coe_of_support_subset _ _)]

/-- If a test function `φ` agrees near a compact set `K` with a `C^m` function `g` on an open
neighbourhood of `K`, then its `m`-jet restriction to `K` equals `TauCeti.JetSpace.ofContDiffOn`
of `g`. -/
theorem jetRestrictionCLM_eq_ofContDiffOn {Ω : Opens E} {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) {g : E → F}
    (hg : ContDiffOn ℝ m g U) {φ : 𝓓^{n}(Ω, F)} (hφ : (φ : E → F) =ᶠ[𝓝ˢ K] g) :
    jetRestrictionCLM Ω K m hm φ = TauCeti.JetSpace.ofContDiffOn hK hU hKU m hg :=
  TauCeti.JetSpace.ext fun k x ↦ by
    simp only [eval_jetRestrictionCLM, TauCeti.JetSpace.eval_ofContDiffOn]
    exact ((hφ.filter_mono (nhds_le_nhdsSet x.property)).iteratedFDeriv (𝕜 := ℝ) (k : ℕ)).eq_of_nhds

/-- A test function supported away from `K` has zero `m`-jet on `K`. -/
theorem jetRestrictionCLM_eq_zero_of_tsupport_subset_compl {Ω : Opens E} {K : Set E} (m : ℕ)
    {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) {φ : 𝓓^{n}(Ω, F)} (hφ : tsupport (φ : E → F) ⊆ Kᶜ) :
    jetRestrictionCLM Ω K m hm φ = 0 :=
  TauCeti.JetSpace.ext fun k x ↦ by
    simp only [eval_jetRestrictionCLM, TauCeti.JetSpace.eval_zero, FunLike.coe_zero, Pi.zero_apply]
    exact image_eq_zero_of_notMem_tsupport fun h ↦
      hφ (tsupport_iteratedFDeriv_subset k h) x.property

end TestFunction
