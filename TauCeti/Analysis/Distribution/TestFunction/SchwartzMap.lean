/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Test functions are Schwartz functions

A smooth compactly supported function decays faster than any power, so every test function on an
open set `Ω` of `E` is a Schwartz function on `E`. This file shows that the inclusion is a
continuous linear map `TestFunction.toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F)` for the LF topology
of test functions, and that, conversely, multiplying a Schwartz function by a smooth cutoff `χ`
whose support is a compact subset of `Ω` is a continuous linear map
`SchwartzMap.cutoffCLM : 𝓢(E, F) →L[𝕜] 𝓓(Ω, F)`.

Restricting a tempered distribution to test functions is precomposition with the first map, and
extending a compactly supported distribution to a tempered distribution is precomposition with the
second one (`TauCeti.Analysis.Distribution.TemperedDistribution.Restriction`).

## Main declarations

* `ContDiffMapSupportedIn.toSchwartzMapCLM`: smooth functions supported in a fixed compact set
  `K` are Schwartz functions; the Schwartz seminorm `sup ‖x‖ ^ k ‖D^i f x‖` is at most
  `R ^ k` times the `i`-th seminorm of `𝓓_K`, where `R` bounds the norm on `K`.
* `TestFunction.toSchwartzMapCLM`: the inclusion of test functions into Schwartz space, which
  commutes with directional derivatives (`TestFunction.toSchwartzMapCLM_lineDerivOp`).
* `SchwartzMap.cutoffSupportedInCLM`: multiplication `f ↦ χ f` by a smooth function `χ`
  supported in `K`, from Schwartz functions to `𝓓_K`; Leibniz's rule bounds the seminorms of
  `χ f` by the Schwartz seminorms of `f` without polynomial weight.
* `SchwartzMap.cutoffCLM`: multiplication `f ↦ χ f` by a smooth cutoff `χ` with compact support
  in `Ω`, from Schwartz functions to test functions on `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1.
-/

public section

noncomputable section

open Set TopologicalSpace Function
open scoped Distributions SchwartzMap ContDiff LineDeriv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

namespace ContDiffMapSupportedIn

variable {K : Compacts E}

variable (𝕜) in
/-- A smooth function supported in a fixed compact set `K` is a Schwartz function, and the
inclusion `𝓓_K(E, F) → 𝓢(E, F)` is a continuous linear map. -/
def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) :=
  letI A : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓢(E, F) :=
    { toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  { toLinearMap := A
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K)
        (schwartz_withSeminorms 𝕜 E F) A (Seminorm.IsBounded.of_real fun ⟨k, i⟩ ↦ ?_)
      obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
      refine ⟨{i}, max R 0 ^ k, fun f ↦ ?_⟩
      refine SchwartzMap.seminorm_le_bound 𝕜 k i _ (by positivity) fun x ↦ ?_
      have hA : ⇑(A f) = f := funext (HasCompactSupport.toSchwartzMap_toFun f.hasCompactSupport _)
      rw [Finset.sup_singleton, hA]
      by_cases hx : x ∈ (K : Set E)
      · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) ((hR x hx).trans (le_max_left R 0)) k)
          (norm_iteratedFDeriv_apply_le_seminorm_top 𝕜) (norm_nonneg _) (by positivity)
      · rw [f.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
        exact mul_nonneg (by positivity) (apply_nonneg _ _) }

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓_{K}(E, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  (rfl)

end ContDiffMapSupportedIn

namespace TestFunction

variable {Ω : Opens E} [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- **Test functions are Schwartz functions.** The inclusion of the test functions on an open set
`Ω` into the Schwartz functions on the whole space is a continuous linear map for the LF topology
of test functions. -/
def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM 𝕜 (fun φ ↦ φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    (fun _ _ ↦ ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜) (fun _ _ _ ↦ rfl)

@[simp]
theorem coe_toSchwartzMapCLM (φ : 𝓓(Ω, F)) : ⇑(toSchwartzMapCLM 𝕜 φ) = φ :=
  (rfl)

theorem injective_toSchwartzMapCLM : Injective (toSchwartzMapCLM 𝕜 : 𝓓(Ω, F) → 𝓢(E, F)) :=
  fun _ _ h ↦ TestFunction.ext fun x ↦ congr($h x)

/-- The inclusion of test functions into Schwartz space commutes with directional derivatives. -/
theorem toSchwartzMapCLM_lineDerivOp (v : E) (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (∂_{v} φ) = ∂_{v} (toSchwartzMapCLM 𝕜 φ) := by
  ext x
  rw [coe_toSchwartzMapCLM, lineDerivOp_apply, SchwartzMap.lineDerivOp_apply, coe_toSchwartzMapCLM]

/-- The Schwartz function of a test function does not depend on the scalars for which the
inclusion is linear. -/
theorem toSchwartzMapCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [Algebra ℝ 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] [IsScalarTower ℝ 𝕜' F] (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 φ = toSchwartzMapCLM 𝕜' φ :=
  (rfl)

end TestFunction

namespace SchwartzMap

variable {Ω : Opens E} [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] {χ : E → ℝ}

variable (𝕜) in
/-- Multiplication `f ↦ χ f` by a smooth function `χ` supported in a fixed compact set `K`, as a
continuous linear map from Schwartz functions to smooth functions supported in `K`. -/
def cutoffSupportedInCLM (hχ : ContDiff ℝ ∞ χ) {K : Compacts E}
    (hχK : support χ ⊆ K) : 𝓢(E, F) →L[𝕜] 𝓓_{K}(E, F) :=
  letI A : 𝓢(E, F) →ₗ[𝕜] 𝓓_{K}(E, F) :=
    { toFun f := .of_support_subset (f := fun x ↦ χ x • f x) (hχ.smul (f.smooth ⊤)) <|
        (support_smul_subset_left _ _).trans hχK
      map_add' f g := by
        ext x
        simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_add]
      map_smul' c f := by
        ext x
        simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_comm c] }
  { toLinearMap := A
    cont := by
      refine WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 E F)
        (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K) _
        (Seminorm.IsBounded.of_real fun i ↦ ?_)
      -- Leibniz's rule bounds the `i`-th derivative of `χ f` by the derivatives of `f` of order
      -- at most `i`, with coefficients bounded by those of `χ`.
      obtain ⟨M, hM₀, hM⟩ := (HasCompactSupport.intro K.isCompact fun x hx ↦
        notMem_support.1 fun h ↦ hx (hχK h)).exists_bound_iteratedFDeriv hχ i
      let s : Finset (ℕ × ℕ) := (Finset.range (i + 1)).image fun j ↦ (0, j)
      refine ⟨s, ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M, fun f ↦ ?_⟩
      have hs (j : ℕ) (hj : j ∈ Finset.range (i + 1)) :
          SchwartzMap.seminorm 𝕜 0 j f ≤ (s.sup (schwartzSeminormFamily 𝕜 E F)) f :=
        Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily 𝕜 E F)
          (Finset.mem_image_of_mem (fun j ↦ (0, j)) hj)
      refine (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜
        (mul_nonneg (Finset.sum_nonneg fun j _ ↦ by positivity) (apply_nonneg _ _)) i _).2
        fun x _ ↦ ?_
      have hA : ⇑(A f) = fun x ↦ χ x • f x :=
        funext <| ContDiffMapSupportedIn.coe_of_support_subset _
          ((support_smul_subset_left _ _).trans hχK)
      rw [hA]
      refine (norm_iteratedFDeriv_smul_le hχ (f.smooth ⊤) x (mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      rw [mul_assoc, mul_assoc]
      gcongr
      · exact hM j (Finset.mem_range_succ_iff.1 hj) x
      · exact (norm_iteratedFDeriv_le_seminorm 𝕜 f _ x).trans
          (hs _ (Finset.mem_range_succ_iff.2 (Nat.sub_le i j))) }

@[simp]
theorem cutoffSupportedInCLM_apply (hχ : ContDiff ℝ ∞ χ) {K : Compacts E}
    (hχK : support χ ⊆ K) (f : 𝓢(E, F)) (x : E) :
    cutoffSupportedInCLM 𝕜 hχ hχK f x = χ x • f x :=
  ContDiffMapSupportedIn.coe_of_support_subset (f := fun x ↦ χ x • f x) (hχ.smul (f.smooth ⊤))
    ((support_smul_subset_left _ _).trans hχK) x

variable (𝕜) in
/-- Multiplication `f ↦ χ f` by a smooth function `χ` with compact support in `Ω`, as a continuous
linear map from Schwartz functions on `E` to test functions on `Ω`. -/
def cutoffCLM (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    𝓢(E, F) →L[𝕜] 𝓓(Ω, F) :=
  TestFunction.ofSupportedInCLM 𝕜 (K := ⟨tsupport χ, hχc⟩) hχΩ ∘L
    cutoffSupportedInCLM 𝕜 hχ (K := ⟨tsupport χ, hχc⟩) (subset_tsupport χ)

@[simp]
theorem cutoffCLM_apply (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (f : 𝓢(E, F)) (x : E) : cutoffCLM 𝕜 hχ hχc hχΩ f x = χ x • f x :=
  cutoffSupportedInCLM_apply (𝕜 := 𝕜) hχ (K := ⟨tsupport χ, hχc⟩) (subset_tsupport χ) f x

end SchwartzMap
