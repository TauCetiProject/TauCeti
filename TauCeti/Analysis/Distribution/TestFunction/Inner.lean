/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Test functions valued in a real inner product space

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓(Ω, V)` pairs with a field `w : E → V` through the inner product, and the integrals
`∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that these
pairings, and those with the coordinate derivatives of `φ`, are integrable for locally integrable
`w`, and proves the fundamental lemma of the calculus of variations in this form: a locally
integrable field is determined almost everywhere on `Ω` by its pairings with `𝓓(Ω, V)`.

## Main results

* `TestFunction.integrable_inner`: `x ↦ ⟪φ x, w x⟫` is integrable for `w` locally integrable
  on `Ω`.
* `TestFunction.integrable_inner_fderiv`: `x ↦ ⟪∂_v φ x, w x⟫` is integrable for `w` locally
  integrable on `Ω`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq`: two locally integrable fields with the same
  pairings against every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on `Ω`. The target `V` need only
  be complete; the proof tests against `ψ • c` for scalar test functions `ψ` and a constant
  vector `c`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq_rclike`: the same for fields valued in an inner
  product space over `𝕜 = ℝ` or `ℂ`, paired through the `𝕜`-valued inner product.
* `TauCeti.eq_of_forall_integral_inner_eq_of_continuous`: two continuous fields with the same
  pairings `∫ ⟪φ, ·⟫_𝕜` against every test function on `E` are equal, for a measure finite on
  compact sets and charging every nonempty open set.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TestFunction

/-- A test function paired with a locally integrable field is integrable. -/
theorem integrable_inner {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V)) :
    Integrable (fun x => ⟪(φ : E → V) x, w x⟫_ℝ) μ :=
  φ.integrable_bilin (innerSL ℝ) hw

/-- A directional derivative of a test function, paired with a locally integrable field, is
integrable. -/
theorem integrable_inner_fderiv {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V))
    (v : E) : Integrable (fun x => ⟪fderiv ℝ (φ : E → V) x v, w x⟫_ℝ) μ := by
  have h := (lineDerivCLM ℝ v φ : 𝓓(Ω, V)).integrable_inner hw
  simp only [coe_lineDerivCLM, lineDeriv_eq_fderiv] at h
  exact h

end TestFunction

namespace TauCeti

variable [CompleteSpace V] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The **fundamental lemma** for vector-valued test functions: locally integrable `g, h` on the
open set `Ω` with `∫ ⟪φ, g⟫ = ∫ ⟪φ, h⟫` for every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on
`Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq {g h : E → V} (hg : LocallyIntegrableOn g Ω μ)
    (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, V), ∫ x, ⟪(φ : E → V) x, g x⟫_ℝ ∂μ = ∫ x, ⟪(φ : E → V) x, h x⟫_ℝ ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hgh : LocallyIntegrableOn (g - h) Ω μ := hg.sub hh
  have key := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Ω.isOpen hgh
    fun ψ hψ hψc hψΩ => by
      set w := ∫ x, ψ x • (g - h) x ∂μ
      let ψ' : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψΩ⟩
      let Φ : 𝓓(Ω, V) := ⟨fun x => ψ x • w, hψ.smul contDiff_const, hψc.smul_right,
        (tsupport_smul_subset_left _ _).trans hψΩ⟩
      have hΦ := H Φ
      have hint : Integrable (fun x => ψ x • (g - h) x) μ :=
        ψ'.integrable_smul hgh
      have : ⟪w, w⟫_ℝ = 0 := by
        calc ⟪w, w⟫_ℝ = ∫ x, ⟪w, ψ x • (g - h) x⟫_ℝ ∂μ := (integral_inner hint w).symm
          _ = ∫ x, ⟪(Φ : E → V) x, g x⟫_ℝ ∂μ - ∫ x, ⟪(Φ : E → V) x, h x⟫_ℝ ∂μ := by
            rw [← integral_sub (Φ.integrable_inner hg) (Φ.integrable_inner hh)]
            refine integral_congr_ae (.of_forall fun x => ?_)
            simp [Φ, inner_smul_left, inner_smul_right, inner_sub_right, mul_sub]
          _ = 0 := sub_eq_zero.2 hΦ
      exact inner_self_eq_zero.1 this
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

/-- The **fundamental lemma** for fields valued in an inner product space `F` over `𝕜 = ℝ` or `ℂ`:
locally integrable `g, h` on the open set `Ω` with `∫ ⟪φ, g⟫_𝕜 = ∫ ⟪φ, h⟫_𝕜` for every
`φ ∈ 𝓓(Ω, F)` agree almost everywhere on `Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq_rclike {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]
    {g h : E → F} (hg : LocallyIntegrableOn g Ω μ) (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, F), ∫ x, ⟪(φ : E → F) x, g x⟫_𝕜 ∂μ = ∫ x, ⟪(φ : E → F) x, h x⟫_𝕜 ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hsmul (r : ℝ) (a b : F) : ⟪r • a, b⟫_𝕜 = r • ⟪a, b⟫_𝕜 := by
    rw [← algebraMap_smul 𝕜 r a, RCLike.algebraMap_eq_ofReal, inner_smul_real_left]
  -- The real parts of the pairings form the underlying real inner product. It is built by hand,
  -- rather than as `InnerProductSpace.rclikeToReal`, so that it extends the given
  -- `[NormedSpace ℝ F]` on which `𝓓(Ω, F)` depends instead of the restricted-scalars structure.
  let _ : InnerProductSpace ℝ F :=
    { inner a b := RCLike.re ⟪a, b⟫_𝕜
      norm_sq_eq_re_inner a := by simp [sq]
      conj_inner_symm a b := by simp [inner_re_symm]
      add_left a b c := by simp [inner_add_left]
      smul_left a b r := by simp [hsmul, RCLike.smul_re] }
  -- The pairing `⟪·, ·⟫_𝕜` is real bilinear, so it is integrable against test functions.
  let B : F →L[ℝ] F →L[ℝ] 𝕜 := LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a b ↦ ⟪a, b⟫_𝕜) inner_add_left hsmul inner_add_right
      fun r a b ↦ by rw [← inner_conj_symm, hsmul, RCLike.conj_smul, inner_conj_symm]) 1
    fun a b ↦ by simpa using norm_inner_le_norm (𝕜 := 𝕜) a b
  have hB (a b : F) : B a b = ⟪a, b⟫_𝕜 := by
    simp only [B, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]
  have hre (a b : F) : ⟪a, b⟫_ℝ = RCLike.re ⟪a, b⟫_𝕜 := rfl
  refine ae_eq_of_forall_integral_inner_eq hg hh fun φ ↦ ?_
  have hint {f : E → F} (hf : LocallyIntegrableOn f Ω μ) :
      Integrable (fun x ↦ ⟪(φ : E → F) x, f x⟫_𝕜) μ := by
    simpa only [hB] using φ.integrable_bilin B hf
  simp only [hre]
  rw [integral_re (hint hg), integral_re (hint hh), H φ]

/-- The **fundamental lemma** for continuous fields valued in an inner product space `F` over
`𝕜 = ℝ` or `ℂ`: continuous `g, h : E → F` with `∫ ⟪φ, g⟫_𝕜 = ∫ ⟪φ, h⟫_𝕜` for every `φ ∈ 𝓓(E, F)`
are equal, for a measure finite on compact sets and charging every nonempty open set. -/
theorem eq_of_forall_integral_inner_eq_of_continuous {𝕜 F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {g h : E → F}
    (hg : Continuous g) (hh : Continuous h)
    (H : ∀ φ : 𝓓((⊤ : Opens E), F),
      ∫ x, ⟪(φ : E → F) x, g x⟫_𝕜 ∂μ = ∫ x, ⟪(φ : E → F) x, h x⟫_𝕜 ∂μ) :
    g = h := by
  have hae := ae_eq_of_forall_integral_inner_eq_rclike
    (hg.locallyIntegrable.locallyIntegrableOn _) (hh.locallyIntegrable.locallyIntegrableOn _) H
  rw [Opens.coe_top, Measure.restrict_univ] at hae
  exact (hg.ae_eq_iff_eq μ hh).1 hae

end TauCeti
