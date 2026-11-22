/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Calculus.Jet.Continuous

/-!
# Test-function jet restriction and distributional pullback

For any `n : ℕ∞` with `m ≤ n` and any subset `K ⊆ E`, restricting the derivatives of a test
function to `K` defines continuous linear maps `ContDiffMapSupportedIn.jetRestrictionCLM` on
`𝓓^{n}_{L}(E, F)` and `TestFunction.jetRestrictionCLM` on `𝓓^{n}(Ω, F)` into
`TauCeti.JetSpace E F K m`. Composing `TestFunction.jetRestrictionCLM` with any continuous linear
map `ℓ : TauCeti.JetSpace E F K m →L[ℝ] G` produces a continuous linear map on `𝓓^{n}(Ω, F)`
(in particular, a `G`-valued distribution of order at most `n` when `F = ℝ`) whose distributional
support is contained in `K` whenever `K` is closed.

## Main declarations

* `ContDiffMapSupportedIn.jetRestrictionCLM`, `TestFunction.jetRestrictionCLM`: continuous linear
  `m`-jet restriction maps on compactly supported `C^n` functions and on test functions.
* `Distribution.dsupport_comp_jetRestrictionCLM_subset`: pulling back a continuous linear map on
  `TauCeti.JetSpace E F K m` along `TestFunction.jetRestrictionCLM` yields a map supported in `K`
  when `K` is closed.
-/

public section

noncomputable section

open ContDiff Filter Set TopologicalSpace Topology
open scoped BoundedContinuousFunction ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous linear `m`-jet restriction from `𝓓^{n}_{L}(E, F)` into `TauCeti.JetSpace E F K m`
whenever `m ≤ n`. -/
def jetRestrictionCLM (K : Set E) (m : ℕ) {n : ℕ∞} (_hm : (m : ℕ∞) ≤ n) (L : Compacts E) :
    𝓓^{n}_{L}(E, F) →L[ℝ] TauCeti.JetSpace E F K m :=
  (ContinuousLinearMap.pi fun k : Fin (m + 1) ↦
    BoundedContinuousFunction.compContinuousCLM (E [×(k : ℕ)]→L[ℝ] F) ℝ
      ⟨Subtype.val, continuous_subtypeVal⟩ ∘L ContDiffMapSupportedIn.structureMapCLM ℝ n k :
    𝓓^{n}_{L}(E, F) →L[ℝ] Π k : Fin (m + 1), K →ᵇ (E [×(k : ℕ)]→L[ℝ] F))

@[simp]
theorem eval_jetRestrictionCLM (K : Set E) (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) (L : Compacts E)
    (φ : 𝓓^{n}_{L}(E, F)) (k : Fin (m + 1)) (x : K) :
    (jetRestrictionCLM K m hm L φ).eval k x = iteratedFDeriv ℝ (k : ℕ) (φ : E → F) x.val := by
  have hk : ((k : ℕ) : ℕ∞) ≤ n := (Nat.cast_le.2 (Nat.le_of_lt_succ k.isLt)).trans hm
  have hpi : (jetRestrictionCLM K m hm L φ).eval k =
      BoundedContinuousFunction.compContinuousCLM (E [×(k : ℕ)]→L[ℝ] F) ℝ
        ⟨Subtype.val, continuous_subtypeVal⟩
        (ContDiffMapSupportedIn.structureMapCLM ℝ n k φ) :=
    ContinuousLinearMap.pi_apply _ φ k
  simp [hpi, hk]

end ContDiffMapSupportedIn

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
    have hx : x.val ∉ tsupport (φ : E → F) := fun hmem ↦ hφ hmem x.property
    have hev : (φ : E → F) =ᶠ[𝓝 x.val] (0 : E → F) := notMem_tsupport_iff_eventuallyEq.1 hx
    simpa using (hev.iteratedFDeriv (𝕜 := ℝ) (k : ℕ)).eq_of_nhds

end TestFunction

namespace Distribution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]

/-- Pulling back a continuous linear map `ℓ` on `TauCeti.JetSpace E F K m` along
`TestFunction.jetRestrictionCLM` produces a continuous linear map on `𝓓^{n}(Ω, F)` (in particular,
a distribution when `F = ℝ`) whose distributional support lies in `K` whenever `K` is closed. -/
theorem dsupport_comp_jetRestrictionCLM_subset {Ω : Opens E} {K : Set E} (hK : IsClosed K)
    (m : ℕ) {n : ℕ∞} (hm : (m : ℕ∞) ≤ n) (ℓ : TauCeti.JetSpace E F K m →L[ℝ] G) :
    dsupport (ℓ ∘L TestFunction.jetRestrictionCLM Ω K m hm) ⊆ K := by
  have hvan : IsVanishingOn (ℓ ∘L TestFunction.jetRestrictionCLM Ω K m hm) Kᶜ := fun φ hφ ↦ by
    simp [TestFunction.jetRestrictionCLM_eq_zero_of_tsupport_subset_compl m hm hφ]
  exact Disjoint.subset_right_of_subset_union
    (by simp) (hvan.disjoint_dsupport hK.isOpen_compl).symm

end Distribution
