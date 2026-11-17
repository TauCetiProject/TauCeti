/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Test functions are Schwartz functions

A smooth function with compact support is a Schwartz function
(`HasCompactSupport.toSchwartzMap`). This file shows that the inclusion is continuous, both on the
Fréchet space `𝓓_{K}(E, F)` of smooth functions supported in a compact set `K`, where the Schwartz
seminorm `sup ‖x‖ ^ k ‖D^l f x‖` is at most `R ^ k` times the sup norm of `D^l f` when `K` lies in
the ball of radius `R`, and on the space `𝓓(Ω, F)` of test functions on an open set with its
inductive limit topology. Transposing the second inclusion restricts tempered distributions to
distributions on open sets.

## Main declarations

* `ContDiffMapSupportedIn.toSchwartzMapCLM`: the inclusion `𝓓_{K}(E, F) → 𝓢(E, F)`.
* `TestFunction.toSchwartzMapCLM`: the inclusion `𝓓(Ω, F) → 𝓢(E, F)`.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions SchwartzMap ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

namespace ContDiffMapSupportedIn

variable {K : Compacts E}

/-- The Schwartz seminorm `(k, l)` of a smooth function supported in `K ⊆ closedBall 0 R` is at most
`R ^ k` times the sup norm of its `l`-th derivative. -/
private theorem seminorm_toSchwartzMap_le (f : 𝓓_{K}(E, F)) {R : ℝ} (hR : 0 ≤ R)
    (hKR : (K : Set E) ⊆ Metric.closedBall 0 R) (k l : ℕ) :
    SchwartzMap.seminorm 𝕜 k l (f.hasCompactSupport.toSchwartzMap f.contDiff) ≤
      R ^ k * N[𝕜]_{K, l} f := by
  have hcoe : ⇑(f.hasCompactSupport.toSchwartzMap f.contDiff) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  refine SchwartzMap.seminorm_le_bound 𝕜 k l _ (by positivity) fun x ↦ ?_
  rw [hcoe]
  by_cases hx : x ∈ (K : Set E)
  · have hxR : ‖x‖ ≤ R := by simpa using hKR hx
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hxR k)
      (norm_iteratedFDeriv_apply_le_seminorm_top 𝕜) (norm_nonneg _) (by positivity)
  · simp only [f.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
    positivity

variable (𝕜) in
/-- **Smooth functions supported in a compact set are Schwartz functions**, continuously: the
inclusion `𝓓_{K}(E, F) → 𝓢(E, F)` as a continuous linear map. -/
def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) :=
  letI Φ : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓢(E, F) :=
    { toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  { toLinearMap := Φ
    cont := by
      obtain ⟨R, hR, hKR⟩ : ∃ R, 0 ≤ R ∧ (K : Set E) ⊆ Metric.closedBall 0 R := by
        obtain ⟨R, hKR⟩ := K.isCompact.isBounded.subset_closedBall 0
        exact ⟨max R 0, le_max_right R 0,
          hKR.trans (Metric.closedBall_subset_closedBall (le_max_left R 0))⟩
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K) (schwartz_withSeminorms 𝕜 E F) Φ
        (.of_real fun ⟨k, l⟩ ↦ ⟨{l}, R ^ k, fun f ↦ ?_⟩)
      simp only [SchwartzMap.schwartzSeminormFamily_apply, Finset.sup_singleton]
      exact seminorm_toSchwartzMap_le f hR hKR k l }

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓_{K}(E, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  (rfl)

theorem toSchwartzMapCLM_apply (f : 𝓓_{K}(E, F)) (x : E) : toSchwartzMapCLM 𝕜 f x = f x :=
  (rfl)

end ContDiffMapSupportedIn

namespace TestFunction

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] {Ω : Opens E}

variable (𝕜) in
/-- **Test functions are Schwartz functions**, continuously: the inclusion `𝓓(Ω, F) → 𝓢(E, F)`
of the test functions on an open set `Ω`, extended by zero, as a continuous linear map for the
inductive limit topology of `𝓓(Ω, F)`. -/
def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.mkCLM 𝕜 (fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦
      (ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜).continuous.congr fun _ ↦ (rfl)

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓(Ω, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  (rfl)

theorem toSchwartzMapCLM_apply (f : 𝓓(Ω, F)) (x : E) : toSchwartzMapCLM 𝕜 f x = f x :=
  (rfl)

theorem hasCompactSupport_toSchwartzMapCLM (f : 𝓓(Ω, F)) :
    HasCompactSupport (toSchwartzMapCLM 𝕜 f) := by
  rw [coe_toSchwartzMapCLM]
  exact f.hasCompactSupport

end TestFunction
