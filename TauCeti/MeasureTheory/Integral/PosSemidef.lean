/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals of positive-semidefinite and positive-definite matrices

An entrywise integral of an almost everywhere positive-semidefinite family of matrices over an
`RCLike` scalar field is positive semidefinite: its quadratic form is the integral of the pointwise
quadratic forms. Over a nonzero measure, almost everywhere positive definiteness likewise passes to
the entrywise integral.

## Main results

* `TauCeti.posSemidef_integral` — the entrywise integral of an a.e. positive-semidefinite family of
  finite matrices with integrable entries is positive semidefinite.
* `TauCeti.posDef_integral` — over a nonzero measure, the entrywise integral of an a.e.
  positive-definite family of finite matrices with integrable entries is positive definite.
-/

public section

namespace TauCeti

open Matrix MeasureTheory
open scoped ComplexOrder

private lemma dotProduct_mulVec_integral_eq {α ι 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] [RCLike 𝕜] {M : α → Matrix ι ι 𝕜}
    (hint : ∀ i j, Integrable (fun x => M x i j) μ) (c : ι → 𝕜) :
    star c ⬝ᵥ ((Matrix.of fun i j => ∫ x, M x i j ∂μ) *ᵥ c) =
      ∫ x, star c ⬝ᵥ (M x *ᵥ c) ∂μ ∧
      Integrable (fun x => star c ⬝ᵥ (M x *ᵥ c)) μ := by
  have hint_quad : Integrable (fun x => star c ⬝ᵥ (M x *ᵥ c)) μ := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const (c j)).const_mul (star (c i))
  refine ⟨?_, hint_quad⟩
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hint i j).mul_const (c j)).const_mul (star (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const (c j)]
  simp only [integral_mul_const]

/-- The **entrywise integral of positive-semidefinite matrices** is positive semidefinite: if
`M x` is positive semidefinite for almost every `x` and every entry of `M` is integrable, then the
matrix of entrywise integrals is positive semidefinite. -/
theorem posSemidef_integral {α ι 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [Finite ι]
    [RCLike 𝕜] {M : α → Matrix ι ι 𝕜} (hM : ∀ᵐ x ∂μ, (M x).PosSemidef)
    (hint : ∀ i j, Integrable (fun x => M x i j) μ) :
    (Matrix.of fun i j => ∫ x, M x i j ∂μ).PosSemidef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, RCLike.star_def, ← integral_conj]
    exact integral_congr_ae
      (hM.mono fun x hx => by simpa [RCLike.star_def] using hx.isHermitian.apply i j)
  · obtain ⟨hquad, hint_quad⟩ := dotProduct_mulVec_integral_eq hint c
    rw [hquad, RCLike.nonneg_iff, ← integral_re hint_quad, ← integral_im hint_quad]
    refine ⟨integral_nonneg_of_ae (hM.mono fun x hx => hx.re_dotProduct_nonneg c), ?_⟩
    exact integral_eq_zero_of_ae
      (hM.mono fun x hx => (RCLike.nonneg_iff.mp (hx.dotProduct_mulVec_nonneg c)).2)

/-- Over a nonzero measure, the **entrywise integral of positive-definite matrices** is positive
definite. -/
theorem posDef_integral {α ι 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [hμ : NeZero μ]
    [Finite ι] [RCLike 𝕜] {M : α → Matrix ι ι 𝕜} (hM : ∀ᵐ x ∂μ, (M x).PosDef)
    (hint : ∀ i j, Integrable (fun x => M x i j) μ) :
    (Matrix.of fun i j => ∫ x, M x i j ∂μ).PosDef := by
  have := Fintype.ofFinite ι
  have hpsd : (Matrix.of fun i j => ∫ x, M x i j ∂μ).PosSemidef :=
    posSemidef_integral (hM.mono fun _ hx => hx.posSemidef) hint
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian fun c hc => ?_
  obtain ⟨hquad, hint_quad⟩ := dotProduct_mulVec_integral_eq hint c
  have him : RCLike.im (star c ⬝ᵥ ((Matrix.of fun i j => ∫ x, M x i j ∂μ) *ᵥ c)) = 0 :=
    (RCLike.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg c)).2
  rw [RCLike.pos_iff]
  refine ⟨?_, him⟩
  rw [hquad, ← integral_re hint_quad]
  have hpos_ae : ∀ᵐ x ∂μ, 0 < RCLike.re (star c ⬝ᵥ (M x *ᵥ c)) :=
    hM.mono fun x hx => hx.re_dotProduct_pos hc
  rw [integral_pos_iff_support_of_nonneg_ae (hpos_ae.mono fun _ hx => hx.le) hint_quad.re]
  rw [pos_iff_ne_zero]
  intro hsupp
  have hcompl : μ (Function.support fun x => RCLike.re (star c ⬝ᵥ (M x *ᵥ c)))ᶜ = 0 := by
    rw [ae_iff] at hpos_ae
    refine measure_mono_null (fun x hx => ?_) hpos_ae
    simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx
    simp [hx]
  have huniv : μ Set.univ ≤ 0 := by
    simpa [hsupp, hcompl] using
      measure_univ_le_add_compl (μ := μ)
        (s := Function.support fun x => RCLike.re (star c ⬝ᵥ (M x *ᵥ c)))
  exact hμ.out (Measure.measure_univ_eq_zero.mp (nonpos_iff_eq_zero.mp huniv))

end TauCeti
