/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Test functions are Schwartz functions

A smooth function with compact support decays faster than every power together with all its
derivatives, so it is a Schwartz function (`HasCompactSupport.toSchwartzMap`). This file shows
that the inclusion is continuous for the natural topologies on the two sides: on smooth functions
supported in a fixed compact set `K`, the Schwartz seminorm `sup_x ‖x‖ ^ k ‖D^l f(x)‖` is at most
`R ^ k` times the sup norm of `D^l f` for any `R` with `K ⊆ closedBall 0 R`
(`ContDiffMapSupportedIn.toSchwartzMapCLM`), and by the universal property of the inductive limit
topology this gives a continuous linear map on all test functions
(`TestFunction.toSchwartzMapCLM`).

Restricting along this inclusion turns a tempered distribution into a distribution on any open
set, which is how tempered distributions, and in particular the Bessel-potential spaces `H^s`, are
compared with distributions on open sets.

## Main declarations

* `ContDiffMapSupportedIn.toSchwartzMapCLM`: smooth functions supported in a compact set as
  Schwartz functions, as a continuous linear map, with the seminorm bound
  `ContDiffMapSupportedIn.seminorm_toSchwartzMapCLM_le`.
* `TestFunction.toSchwartzMapCLM`: test functions on an open set as Schwartz functions, as a
  continuous linear map, with `TestFunction.coe_toSchwartzMapCLM`; it commutes with directional
  derivatives (`TestFunction.toSchwartzMapCLM_lineDerivOp`) and with postcomposition by continuous
  linear maps (`TestFunction.toSchwartzMapCLM_postcompCLM`).
* `SchwartzMap.toTestFunction`: a compactly supported Schwartz function as a test function, sent
  back to itself by `TestFunction.toSchwartzMapCLM` (`SchwartzMap.toSchwartzMapCLM_toTestFunction`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1 (the inclusion
  `C_c^∞ ⊆ 𝓢`, by which `𝓢'` is a space of distributions).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff SchwartzMap LineDeriv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

namespace ContDiffMapSupportedIn

variable {K : Compacts E}

/-- On smooth functions supported in `K ⊆ closedBall 0 R`, the Schwartz seminorm of orders `k`
and `l` is at most `R ^ k` times the sup norm of the `l`-th derivative. -/
private theorem seminorm_toSchwartzMap_le {R : ℝ} (hR : 0 ≤ R)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ) (f : 𝓓_{K}(E, F)) :
    SchwartzMap.seminorm 𝕜 k l (f.hasCompactSupport.toSchwartzMap f.contDiff) ≤
      R ^ k * N[𝕜]_{K, l} f := by
  refine SchwartzMap.seminorm_le_bound 𝕜 k l _ (by positivity) fun x ↦ ?_
  have hf : ⇑(f.hasCompactSupport.toSchwartzMap f.contDiff) = f :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [hf]
  by_cases hx : x ∈ K
  · gcongr
    · exact hKR x hx
    · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
  · simpa [f.iteratedFDeriv_zero_on_compl hx] using
      mul_nonneg (pow_nonneg hR k) (apply_nonneg _ f)

/-- The inclusion `𝓓_{K}(E, F) → 𝓢(E, F)` as a linear map. -/
private def toSchwartzMapLM : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓢(E, F) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (𝕜) in
/-- A smooth function supported in a compact set `K` is a Schwartz function, and the inclusion
`𝓓_{K}(E, F) → 𝓢(E, F)` is a continuous linear map. -/
def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) where
  toLinearMap := toSchwartzMapLM
  cont := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    have hKR (x : E) (hx : x ∈ K) : ‖x‖ ≤ max R 0 :=
      (mem_closedBall_zero_iff.1 (hR hx)).trans (le_max_left _ _)
    refine (schwartz_withSeminorms 𝕜 E F).continuous_of_continuous_comp _ fun i ↦ ?_
    set C : NNReal := (max R 0 ^ i.1).toNNReal
    refine Seminorm.continuous_of_le (q := C • N[𝕜]_{K, i.2}) ?_ fun f ↦ ?_
    · exact ((ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K).continuous_seminorm i.2).const_smul C
    · exact (seminorm_toSchwartzMap_le (le_max_right R 0) hKR i.1 i.2 f).trans_eq (by
        rw [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)])

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓_{K}(E, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  -- `HasCompactSupport.toSchwartzMap` keeps the underlying function.
  (rfl)

/-- **Quantitative inclusion of test functions in Schwartz space.** On smooth functions supported
in `K ⊆ closedBall 0 R`, the Schwartz seminorm of orders `k` and `l` is at most `R ^ k` times the
sup norm of the `l`-th derivative. -/
theorem seminorm_toSchwartzMapCLM_le {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ)
    (f : 𝓓_{K}(E, F)) :
    SchwartzMap.seminorm 𝕜 k l (toSchwartzMapCLM 𝕜 f) ≤ R ^ k * N[𝕜]_{K, l} f :=
  -- `toSchwartzMapCLM 𝕜 f` is `HasCompactSupport.toSchwartzMap` applied to `f` by definition.
  seminorm_toSchwartzMap_le hR hKR k l f

end ContDiffMapSupportedIn

namespace TestFunction

variable {Ω : Opens E} [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- **Test functions are Schwartz functions.** A smooth function with compact support in an open
set `Ω` is a Schwartz function, and the inclusion `𝓓(Ω, F) → 𝓢(E, F)` is a continuous linear map
for the inductive limit topology on test functions. -/
def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM 𝕜 (fun φ ↦ φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    (fun _ _ ↦ ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜) fun _ _ _ ↦ (rfl)

@[simp]
theorem coe_toSchwartzMapCLM (φ : 𝓓(Ω, F)) : ⇑(toSchwartzMapCLM 𝕜 φ) = φ :=
  -- `HasCompactSupport.toSchwartzMap` keeps the underlying function.
  (rfl)

theorem toSchwartzMapCLM_apply (φ : 𝓓(Ω, F)) (x : E) : toSchwartzMapCLM 𝕜 φ x = φ x :=
  (rfl)

/-- A test function, read as a Schwartz function, still has compact support. -/
theorem hasCompactSupport_toSchwartzMapCLM (φ : 𝓓(Ω, F)) :
    HasCompactSupport (toSchwartzMapCLM 𝕜 φ) :=
  φ.hasCompactSupport

theorem toSchwartzMapCLM_injective : Function.Injective (toSchwartzMapCLM 𝕜 : 𝓓(Ω, F) → _) :=
  fun _ _ h ↦ TestFunction.ext fun x ↦ by
    simpa using congrArg (fun f : 𝓢(E, F) ↦ f x) h

/-- The inclusion of test functions in Schwartz space commutes with directional derivatives. -/
@[simp]
theorem toSchwartzMapCLM_lineDerivOp (v : E) (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (∂_{v} φ) = ∂_{v} (toSchwartzMapCLM 𝕜 φ) := by
  ext x
  simp [lineDerivOp_eq_lineDerivCLM ℝ, SchwartzMap.lineDerivOp_apply]

/-- The inclusion of test functions in Schwartz space commutes with postcomposition by continuous
linear maps. -/
@[simp]
theorem toSchwartzMapCLM_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G] [IsScalarTower ℝ 𝕜 G] (L : F →L[ℝ] G)
    (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (postcompCLM L φ) = (toSchwartzMapCLM 𝕜 φ).postcompCLM L := by
  ext x
  simp

end TestFunction

namespace SchwartzMap

variable {Ω : Opens E}

/-- A compactly supported Schwartz function whose support lies in the open set `Ω` is a test
function on `Ω`. -/
def toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f) (hΩ : tsupport f ⊆ Ω) :
    𝓓(Ω, F) :=
  ⟨f, f.smooth ⊤, hf, hΩ⟩

@[simp]
theorem coe_toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f) (hΩ : tsupport f ⊆ Ω) :
    ⇑(f.toTestFunction hf hΩ) = f :=
  (rfl)

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] in
@[simp]
theorem toSchwartzMapCLM_toTestFunction (f : 𝓢(E, F)) (hf : HasCompactSupport f)
    (hΩ : tsupport f ⊆ Ω) : TestFunction.toSchwartzMapCLM 𝕜 (f.toTestFunction hf hΩ) = f :=
  -- `TestFunction.toSchwartzMapCLM` is `TestFunction.limitCLM` of
  -- `HasCompactSupport.toSchwartzMap`, which unfolds to that map; it keeps the underlying
  -- function, and `SchwartzMap` has structure eta.
  (rfl)

end SchwartzMap
