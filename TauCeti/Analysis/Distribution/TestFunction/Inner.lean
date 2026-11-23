/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Inner-product pairings and Riesz transport on test functions

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓(Ω, V)` pairs with a field `w : E → V` through the inner product, and the integrals
`∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that these
pairings, and those with the coordinate derivatives of `φ`, are integrable for locally integrable
`w`, splits pairings against `WithLp 2 (V₁ × V₂)`-valued test functions into their factor
projections, builds adjoint-weighted vector test functions `α • F(·)* v` for smooth operator
fields `F` along with their value and derivative pairings, and proves the fundamental lemma of
the calculus of variations in this form: a locally integrable field is determined almost everywhere
on `Ω` by its pairings with `𝓓(Ω, V)`.

For real or complex Hilbert coefficients, `TestFunction.rieszEquiv` is a real continuous
linear equivalence to dual-valued tests, conjugating the coefficient scalar action. The original
test topologies and every finite regularity order and infinity are retained.
`TestFunction.eq_of_forall_integral_inner_eq` separates tests by their spatial inner pairings
for any Borel measure finite on compact sets and positive on nonempty open sets; it needs no
completeness of the coefficient space.

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
* `TestFunction.smulAdjointTestFunction`, `TestFunction.inner_smulAdjointTestFunction_apply`,
  `TestFunction.integral_inner_fderiv_smul_adjoint_eq`: adjoint-weighted vector test functions
  `x ↦ α x • F(x)* v` for a smooth operator field `F`, with their value and derivative pairings.
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

section RealPairings

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

section Adjoint

open LineDeriv

private noncomputable def adjointApplyCLM {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (v : V) : (V →L[ℝ] V) →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V v).comp
    ((ContinuousLinearMap.adjoint : (V →L[ℝ] V) ≃ₗᵢ⋆[ℝ] (V →L[ℝ] V)).toContinuousLinearEquiv
      |> ContinuousLinearEquiv.toContinuousLinearMap)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- For a `C^∞` operator field `F : E → V →L[ℝ] V`, a scalar test function `α ∈ 𝓓(Ω, ℝ)` and
`v : V`, the vector test function `x ↦ α x • F(x)* v`. -/
noncomputable def smulAdjointTestFunction [CompleteSpace V] {F : E → V →L[ℝ] V}
    (hF : ContDiff ℝ ∞ F) (α : 𝓓(Ω, ℝ)) (v : V) : 𝓓(Ω, V) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    ((adjointApplyCLM v).contDiff.comp hF) α

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Pairing `smulAdjointTestFunction hF α v` pointwise against `y : V` equals
`α x * ⟪v, F x y⟫_ℝ`. -/
@[simp]
theorem inner_smulAdjointTestFunction_apply [CompleteSpace V] {F : E → V →L[ℝ] V}
    (hF : ContDiff ℝ ∞ F) (α : 𝓓(Ω, ℝ)) (v : V) (x : E) (y : V) :
    ⟪(smulAdjointTestFunction hF α v : E → V) x, y⟫_ℝ = (α : E → ℝ) x * ⟪v, F x y⟫_ℝ := by
  simp [smulAdjointTestFunction, adjointApplyCLM, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- Expanding the directional derivative of `smulAdjointTestFunction hF α v` against a locally
integrable field `w` splits into the `∂_u α` and `∂_u F` terms. -/
theorem integral_inner_fderiv_smul_adjoint_eq [CompleteSpace V] {F : E → V →L[ℝ] V}
    (hF : ContDiff ℝ ∞ F) (α : 𝓓(Ω, ℝ)) (v : V) (u : E) {w : E → V}
    (hw : LocallyIntegrableOn w Ω μ) :
    ∫ x, ⟪fderiv ℝ (smulAdjointTestFunction hF α v : E → V) x u, w x⟫_ℝ ∂μ =
      (∫ x, (∂_{u} α : 𝓓(Ω, ℝ)) x * ⟪v, F x (w x)⟫_ℝ ∂μ) +
        ∫ x, (α : E → ℝ) x * ⟪v, fderiv ℝ F x u (w x)⟫_ℝ ∂μ := by
  let adjV : (V →L[ℝ] V) →L[ℝ] V := adjointApplyCLM v
  let αu : 𝓓(Ω, ℝ) := ∂_{u} α
  have hint {G : E → V →L[ℝ] V} (hG : Continuous G) (β : 𝓓(Ω, ℝ)) :
      Integrable (fun x => (β : E → ℝ) x * ⟪v, G x (w x)⟫_ℝ) μ := by
    have hg : Integrable (fun x => ⟪(β : E → ℝ) x • adjV (G x), w x⟫_ℝ) μ :=
      hw.integrable_inner_left_of_hasCompactSupport
        (β.contDiff.continuous.smul (adjV.continuous.comp hG))
        β.hasCompactSupport.smul_right
        ((tsupport_smul_subset_left (β : E → ℝ) (adjV ∘ G)).trans β.tsupport_subset)
    simpa only [adjV, adjointApplyCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, inner_smul_left, RCLike.conj_to_real,
      ContinuousLinearMap.adjoint_inner_left] using hg
  have hi1 := hint hF.continuous αu
  have hF1 : ContDiff ℝ 1 F := hF.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤))
  have hDF_c : Continuous fun x => fderiv ℝ F x u :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u).continuous.comp (hF1.continuous_fderiv one_ne_zero)
  have hi2 := hint hDF_c α
  have hcoe : (smulAdjointTestFunction hF α v : E → V) = (α : E → ℝ) • (adjV ∘ F) := by
    ext x; simp [smulAdjointTestFunction, adjV]
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have h1 := (α.contDiff.differentiable (by simp) x).hasFDerivAt
  have h2 := adjV.hasFDerivAt.comp x ((hF.differentiable (by simp) x).hasFDerivAt)
  dsimp only
  rw [hcoe, (h1.smul h2).fderiv]
  simp only [αu, TestFunction.lineDerivOp_apply_eq_fderiv α u x, adjV, adjointApplyCLM,
    add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, inner_add_left, inner_smul_left,
    RCLike.conj_to_real, ContinuousLinearMap.adjoint_inner_left]
  ring

end Adjoint

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

end RealPairings

noncomputable section

open TopologicalSpace ComplexConjugate MeasureTheory
open scoped Distributions

namespace TestFunction

variable {𝕜 E V : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {n : ℕ∞} {Ω : Opens E}

/-- Native Riesz transport of coefficient values, for the original test-function topologies.
The equivalence is real-linear and conjugates the coefficient scalar action. -/
def rieszEquiv : 𝓓^{n}(Ω, V) ≃L[ℝ] 𝓓^{n}(Ω, StrongDual 𝕜 V) :=
  postcompCLE ((InnerProductSpace.toDual 𝕜 V).toIsometryEquiv
    |>.toRealLinearIsometryEquivOfMapZero (map_zero (InnerProductSpace.toDual 𝕜 V))
    |>.toContinuousLinearEquiv)

/-- Riesz transport evaluates to the original `𝕜` Hilbert pairing. -/
@[simp]
theorem rieszEquiv_apply (u : 𝓓^{n}(Ω, V)) (x : E) (v : V) :
    rieszEquiv u x v = inner 𝕜 (u x) v := by
  simp only [rieszEquiv, postcompCLE_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have he := IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero
    (InnerProductSpace.toDual 𝕜 V).toIsometryEquiv (map_zero (InnerProductSpace.toDual 𝕜 V))
  exact (congrArg (fun L : V → StrongDual 𝕜 V ↦ L (u x) v) he).trans
    InnerProductSpace.toDual_apply_apply

/-- The inverse native map recovers the Riesz representative of every original dual-valued test. -/
@[simp]
theorem rieszEquiv_symm_apply (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) (x : E) (v : V) :
    inner 𝕜 (rieszEquiv.symm φ x) v = φ x v := by
  have h := congrArg (fun q : 𝓓^{n}(Ω, StrongDual 𝕜 V) ↦ q x v)
    (rieszEquiv.apply_symm_apply φ)
  simpa only [rieszEquiv_apply] using h

/-- Native Riesz transport conjugates the original `𝕜` test action. -/
theorem rieszEquiv_smul (c : 𝕜) (u : 𝓓^{n}(Ω, V)) :
    rieszEquiv (𝕜 := 𝕜) (c • u) = conj c • rieszEquiv (𝕜 := 𝕜) u := by
  apply TestFunction.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [rieszEquiv_apply, smul_apply, inner_smul_left]
  rfl

/-- The inverse Riesz transport has the same conjugate-scalar action. -/
theorem rieszEquiv_symm_smul (c : 𝕜) (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) :
    (rieszEquiv (𝕜 := 𝕜) (V := V)).symm (c • φ) =
      conj c • (rieszEquiv (𝕜 := 𝕜) (V := V)).symm φ := by
  apply (rieszEquiv (𝕜 := 𝕜) (V := V)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, rieszEquiv_smul,
    starRingEnd_self_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace V] in
/-- Native tests are separated by their spatial Hilbert pairings. The measure need only be
finite on compact sets and charge every nonempty open set; no finite-dimensional base is needed. -/
theorem eq_of_forall_integral_inner_eq [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] {f g : 𝓓^{n}(Ω, V)}
    (h : ∀ u : 𝓓^{n}(Ω, V), (∫ x, inner 𝕜 (u x) (f x) ∂μ) =
      ∫ x, inner 𝕜 (u x) (g x) ∂μ) : f = g := by
  have hint (a b : 𝓓^{n}(Ω, V)) : Integrable (fun x ↦ inner 𝕜 (a x) (b x)) μ :=
    (a.continuous.inner b.continuous).integrable_of_hasCompactSupport
      (a.hasCompactSupport.mono fun x hx hz ↦ hx (by simp [hz]))
  let d := f - g
  have hz : (∫ x, inner 𝕜 (d x) (d x) ∂μ) = 0 := by
    have he (x : E) : inner 𝕜 (d x) (d x) =
        inner 𝕜 (d x) (f x) - inner 𝕜 (d x) (g x) := inner_sub_right _ _ _
    simp_rw [he]
    rw [integral_sub (hint d f) (hint d g), h d, sub_self]
  have hi : Integrable (fun x ↦ ‖d x‖ ^ 2) μ :=
    (d.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (by
        have hc := d.hasCompactSupport.comp_left
          (g := fun v : V ↦ ‖v‖ ^ 2) (by simp)
        exact hc)
  have hnorm : (∫ x, ‖d x‖ ^ 2 ∂μ) = 0 := by
    have hr := congrArg (RCLike.re : 𝕜 → ℝ) hz
    rw [← integral_re (hint d d)] at hr
    simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow, map_zero] using hr
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖d x‖) hi).mp hnorm
  have hdz : (d : E → V) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hde : (d : E → V) = 0 := (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdz
  apply sub_eq_zero.mp
  apply TestFunction.ext
  intro x
  exact congrFun hde x

end TestFunction
