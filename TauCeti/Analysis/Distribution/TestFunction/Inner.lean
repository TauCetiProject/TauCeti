/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Test functions valued in a real inner product space

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓(Ω, V)` pairs with a field `w : E → V` through the inner product, and the integrals
`∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that these
pairings, and those with the coordinate derivatives of `φ`, are integrable for locally integrable
`w`, splits pairings against `WithLp 2 (V₁ × V₂)`-valued test functions into their factor
projections, and proves the fundamental lemma of the calculus of variations in this form: a locally
integrable field is determined almost everywhere on `Ω` by its pairings with `𝓓(Ω, V)`.

## Main results

* `TestFunction.integrable_inner`: `x ↦ ⟪φ x, w x⟫` is integrable for `w` locally integrable
  on `Ω`.
* `TestFunction.integrable_inner_fderiv`: `x ↦ ⟪∂_v φ x, w x⟫` is integrable for `w` locally
  integrable on `Ω`.
* `TestFunction.integrable_mul_inner`: `x ↦ α x * ⟪v, w x⟫` is integrable for `α ∈ 𝓓^{n}(Ω, ℝ)`
  and `w` locally integrable on `Ω`.
* `TestFunction.integral_inner_postcomp_prodL2`, `TestFunction.integral_inner_postcomp_prodL2_add`,
  `TestFunction.integral_inner_postcomp_prodL2_sub`,
  `TestFunction.integral_inner_fderiv_postcomp_prodL2`: splitting integrals of `WithLp 2`
  product test functions (and their directional derivatives) against pairs of locally integrable
  fields into the two factor pairings.
* `TauCeti.ae_eq_of_forall_integral_inner_eq`: two locally integrable fields with the same
  pairings against every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on `Ω`. The target `V` need only
  be complete; the proof tests against `ψ • c` for scalar test functions `ψ` and a constant
  vector `c`.
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

/-- A scalar test function multiplied by the inner product of a constant vector with a locally
integrable field is integrable. -/
theorem integrable_mul_inner {n : ℕ∞} {w : E → V} (hw : LocallyIntegrableOn w Ω μ)
    (α : 𝓓^{n}(Ω, ℝ)) (v : V) : Integrable (fun x => (α : E → ℝ) x * ⟪v, w x⟫_ℝ) μ := by
  simpa only [innerSL_apply_apply, inner_smul_right] using
    (innerSL ℝ v).integrable_comp (α.integrable_smul hw)

section ProdL2

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]

/-- Pairing a `WithLp 2 (V₁ × V₂)`-valued test function with a pair `(f, g)` of locally integrable
fields splits into the sum of the component pairings against the projected test functions. -/
theorem integral_inner_postcomp_prodL2 {n : ℕ∞} {f : E → V₁} {g : E → V₂}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ)
    (Φ : 𝓓^{n}(Ω, WithLp 2 (V₁ × V₂))) :
    ∫ x, ⟪(Φ : E → WithLp 2 (V₁ × V₂)) x, WithLp.toLp 2 (f x, g x)⟫_ℝ ∂μ =
      (∫ x, ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f x⟫_ℝ ∂μ) +
        ∫ x, ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g x⟫_ℝ ∂μ := by
  have hf' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f x⟫_ℝ) μ :=
    (postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hf
  have hg' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g x⟫_ℝ) μ :=
    (postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hg
  rw [← integral_add hf' hg']
  exact integral_congr_ae (.of_forall fun x => by
    dsimp only; rw [WithLp.prod_inner_apply]; simp)

/-- Pairing a `WithLp 2 (V₁ × V₂)`-valued test function with a sum `(f₁ + f₂, g₁ + g₂)` of
locally integrable fields splits into the four component pairings against the projected test
functions. -/
theorem integral_inner_postcomp_prodL2_add {n : ℕ∞} {f₁ f₂ : E → V₁} {g₁ g₂ : E → V₂}
    (hf₁ : LocallyIntegrableOn f₁ Ω μ) (hf₂ : LocallyIntegrableOn f₂ Ω μ)
    (hg₁ : LocallyIntegrableOn g₁ Ω μ) (hg₂ : LocallyIntegrableOn g₂ Ω μ)
    (Φ : 𝓓^{n}(Ω, WithLp 2 (V₁ × V₂))) :
    ∫ x, ⟪(Φ : E → WithLp 2 (V₁ × V₂)) x, WithLp.toLp 2 (f₁ x + f₂ x, g₁ x + g₂ x)⟫_ℝ ∂μ =
      ((∫ x, ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₁ x⟫_ℝ ∂μ) +
          ∫ x, ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₂ x⟫_ℝ ∂μ) +
        ((∫ x, ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₁ x⟫_ℝ ∂μ) +
          ∫ x, ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₂ x⟫_ℝ ∂μ) := by
  have hf₁' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₁ x⟫_ℝ) μ :=
    (postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hf₁
  have hf₂' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₂ x⟫_ℝ) μ :=
    (postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hf₂
  have hg₁' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₁ x⟫_ℝ) μ :=
    (postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hg₁
  have hg₂' :
      Integrable (fun x => ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₂ x⟫_ℝ) μ :=
    (postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ).integrable_bilin (innerSL ℝ) hg₂
  rw [integral_inner_postcomp_prodL2 (f := fun x => f₁ x + f₂ x) (g := fun x => g₁ x + g₂ x)
    (hf₁.add hf₂) (hg₁.add hg₂) Φ]
  simp only [inner_add_right]
  rw [integral_add hf₁' hf₂', integral_add hg₁' hg₂']

/-- Pairing a `WithLp 2 (V₁ × V₂)`-valued test function with a difference
`(f₁ - f₂, g₁ - g₂)` of locally integrable fields splits into the four component pairings against
the projected test functions. -/
theorem integral_inner_postcomp_prodL2_sub {n : ℕ∞} {f₁ f₂ : E → V₁}
    {g₁ g₂ : E → V₂} (hf₁ : LocallyIntegrableOn f₁ Ω μ) (hf₂ : LocallyIntegrableOn f₂ Ω μ)
    (hg₁ : LocallyIntegrableOn g₁ Ω μ) (hg₂ : LocallyIntegrableOn g₂ Ω μ)
    (Φ : 𝓓^{n}(Ω, WithLp 2 (V₁ × V₂))) :
    ∫ x,
        ⟪(Φ : E → WithLp 2 (V₁ × V₂)) x, WithLp.toLp 2 (f₁ x - f₂ x, g₁ x - g₂ x)⟫_ℝ ∂μ =
      ((∫ x, ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₁ x⟫_ℝ ∂μ) -
          ∫ x, ⟪(postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x, f₂ x⟫_ℝ ∂μ) +
        ((∫ x, ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₁ x⟫_ℝ ∂μ) -
          ∫ x, ⟪(postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x, g₂ x⟫_ℝ ∂μ) := by
  simpa only [← sub_eq_add_neg, inner_neg_right, integral_neg] using
    integral_inner_postcomp_prodL2_add (f₂ := fun x => -f₂ x) (g₂ := fun x => -g₂ x)
      hf₁ hf₂.neg hg₁ hg₂.neg Φ

/-- Pairing the directional derivative of a `WithLp 2 (V₁ × V₂)`-valued test function with a
pair `(f, g)` of locally integrable fields splits into the sum of the component pairings against
the derivatives of the projected test functions. -/
theorem integral_inner_fderiv_postcomp_prodL2 {f : E → V₁} {g : E → V₂}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ)
    (u : E) (Φ : 𝓓(Ω, WithLp 2 (V₁ × V₂))) :
    ∫ x, ⟪fderiv ℝ (Φ : E → WithLp 2 (V₁ × V₂)) x u, WithLp.toLp 2 (f x, g x)⟫_ℝ ∂μ =
      (∫ x,
          ⟪fderiv ℝ (postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ : E → V₁) x u, f x⟫_ℝ ∂μ) +
        ∫ x, ⟪fderiv ℝ (postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ : E → V₂) x u, g x⟫_ℝ ∂μ := by
  rw [← integral_add ((postcompCLM (WithLp.fstL 2 ℝ V₁ V₂) Φ).integrable_inner_fderiv hf u)
    ((postcompCLM (WithLp.sndL 2 ℝ V₁ V₂) Φ).integrable_inner_fderiv hg u)]
  refine integral_congr_ae (.of_forall fun x => ?_)
  dsimp only
  rw [WithLp.prod_inner_apply, fderiv_postcompCLM, fderiv_postcompCLM]
  simp

end ProdL2

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

end TauCeti
