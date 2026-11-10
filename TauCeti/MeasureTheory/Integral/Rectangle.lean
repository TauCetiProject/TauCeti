/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrals over closed rectangles in the plane

Over a closed rectangle `[a₁, b₁] × [a₂, b₂]` in `ℝ × ℝ`, the fundamental theorem of calculus in one
coordinate computes the integral of a partial derivative from the values on two opposite sides;
in particular, a partial derivative of a function which takes the same values on the two
opposite sides of the rectangle integrates to zero. Together with the vanishing of a continuous
nonnegative function with zero integral, this is how energy identities on a fundamental domain of
a doubly (twisted) periodic map are used.

## Main declarations

* `TauCeti.setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst`,
  `TauCeti.setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd`: the integral of a partial
  derivative is the integral of the difference of the values on the two opposite sides.
* `TauCeti.setIntegral_rect_eq_zero_of_hasDerivAt_fst`,
  `TauCeti.setIntegral_rect_eq_zero_of_hasDerivAt_snd`: a partial derivative of a function with
  equal values on the two opposite sides integrates to zero over the rectangle.
* `TauCeti.eqOn_zero_of_setIntegral_rect_eq_zero`: a continuous nonnegative function with zero
  integral over a nondegenerate rectangle vanishes on it.
* `TauCeti.setIntegral_Icc_prod_le_of_comp_add_le`: comparison of the integrals of `f` and `M` over
  a translated strip `[c + L, d + L] × I` and the original one, when `f (z + (L, 0)) ≤ M z`.
* `TauCeti.neg_mul_setIntegral_le_setIntegral_deriv_mul`: for a monotone `C¹` profile `β` and
  `-B(t) ≤ f`, the lower bound `-(β(b₁) - β(a₁)) ∫ B ≤ ∫∫ β'(s) f`.
-/

public section

open Set MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a₁ b₁ a₂ b₂ : ℝ}

/-- **The fundamental theorem of calculus in the first coordinate.** The integral of a continuous
partial derivative `φ = ∂₁ Φ` over the rectangle `[a₁, b₁] × [a₂, b₂]` is the integral over
`[a₂, b₂]` of the difference of the values of `Φ` on the two vertical sides. -/
theorem setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun s ↦ Φ (s, t)) (φ (s, t)) s)
    (hab : a₁ ≤ b₁) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = ∫ t in Icc a₂ b₂, (Φ (b₁, t) - Φ (a₁, t)) := by
  have hint : Integrable φ ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hφ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hΦ s t)
      ((hφ.comp (Continuous.prodMk_left t)).intervalIntegrable _ _)]

/-- A derivative in the first coordinate of a function with equal values on the vertical sides
`{a₁} × ℝ` and `{b₁} × ℝ` integrates to zero over the rectangle `[a₁, b₁] × [a₂, b₂]`. -/
theorem setIntegral_rect_eq_zero_of_hasDerivAt_fst {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun s ↦ Φ (s, t)) (φ (s, t)) s)
    (hper : ∀ t, Φ (b₁, t) = Φ (a₁, t)) : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = 0 := by
  rcases lt_or_ge b₁ a₁ with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  rw [setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst hφ hΦ hab]
  simp [hper]

/-- **The fundamental theorem of calculus in the second coordinate.** The integral of a
continuous partial derivative `φ = ∂₂ Φ` over the rectangle `[a₁, b₁] × [a₂, b₂]` is the integral
over `[a₁, b₁]` of the difference of the values of `Φ` on the two horizontal sides. -/
theorem setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun t ↦ Φ (s, t)) (φ (s, t)) t)
    (hab : a₂ ≤ b₂) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = ∫ s in Icc a₁ b₁, (Φ (s, b₂) - Φ (s, a₂)) := by
  have hint : Integrable φ ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hφ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hΦ s t)
      ((hφ.comp (Continuous.prodMk_right s)).intervalIntegrable _ _)]

/-- A derivative in the second coordinate of a function with equal values on the horizontal
sides `ℝ × {a₂}` and `ℝ × {b₂}` integrates to zero over the rectangle `[a₁, b₁] × [a₂, b₂]`. -/
theorem setIntegral_rect_eq_zero_of_hasDerivAt_snd {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun t ↦ Φ (s, t)) (φ (s, t)) t)
    (hper : ∀ s, Φ (s, b₂) = Φ (s, a₂)) : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = 0 := by
  rcases lt_or_ge b₂ a₂ with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  rw [setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd hφ hΦ hab]
  simp [hper]

/-- A continuous nonnegative function with zero integral over a nondegenerate rectangle
`[a₁, b₁] × [a₂, b₂]` vanishes on it. -/
theorem eqOn_zero_of_setIntegral_rect_eq_zero {f : ℝ × ℝ → ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂)
    (hf : Continuous f) (hf0 : 0 ≤ f) (hint : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f z = 0) :
    EqOn f 0 (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := by
  have hR : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    (hf.continuousOn.integrableOn_compact hR)).1 hint
  have hU : EqOn f 0 (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hae) (isOpen_Ioo.prod isOpen_Ioo)
      hf.continuousOn continuousOn_const
  have hcl : closure (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) = Icc a₁ b₁ ×ˢ Icc a₂ b₂ := by
    rw [closure_prod_eq, closure_Ioo h₁.ne, closure_Ioo h₂.ne]
  rw [← hcl]
  exact hU.of_subset_closure hf.continuousOn continuousOn_const subset_closure subset_rfl

/-- **Comparison of integrals over a translated strip.** If `f` at the translate `z + (L, 0)` is
pointwise bounded by `M z` on the strip `[c, d] × I`, with `M` integrable on that strip and `f`
integrable on the translated strip `[c + L, d + L] × I`, then the integral of `f` over the
translated strip is at most the integral of `M` over the original one. -/
theorem setIntegral_Icc_prod_le_of_comp_add_le {f M : ℝ × ℝ → ℝ} {c d L : ℝ} {I : Set ℝ}
    (hI : MeasurableSet I) (hfi : IntegrableOn f (Icc (c + L) (d + L) ×ˢ I))
    (hMi : IntegrableOn M (Icc c d ×ˢ I))
    (hfM : ∀ z ∈ Icc c d ×ˢ I, f (z + (L, 0)) ≤ M z) :
    ∫ z in Icc (c + L) (d + L) ×ˢ I, f z ≤ ∫ z in Icc c d ×ˢ I, M z := by
  have he : MeasurePreserving (· + (L, 0) : ℝ × ℝ → ℝ × ℝ) := by
    -- Translation invariance of `volume` on `ℝ × ℝ` is found on the product measure.
    have : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
      rw [Measure.volume_eq_prod]
      infer_instance
    exact measurePreserving_add_right volume (L, 0)
  have hemb : MeasurableEmbedding (· + (L, 0) : ℝ × ℝ → ℝ × ℝ) :=
    measurableEmbedding_addRight (L, 0)
  have hpre : (· + (L, 0) : ℝ × ℝ → ℝ × ℝ) ⁻¹' (Icc (c + L) (d + L) ×ˢ I) = Icc c d ×ˢ I := by
    ext z
    simp only [mem_preimage, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add, add_zero]
    constructor <;> rintro ⟨⟨h, h'⟩, h''⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h''⟩
  rw [← he.setIntegral_preimage_emb hemb f, hpre]
  rw [← he.integrableOn_comp_preimage hemb, hpre] at hfi
  exact setIntegral_mono_on hfi hMi (measurableSet_Icc.prod hI) hfM

/-- **The integrated curvature bound of a monotone profile.** Let `β` be a monotone `C¹` profile
and `f` a function continuous on `[a₁, b₁] × [a₂, b₂]` with `-B(t) ≤ f` there, for a function `B`
integrable on `[a₂, b₂]`. Then `-(β(b₁) - β(a₁)) ∫ B ≤ ∫∫ β'(s) f(s, t)`. Applied to
`f = (H₁ - H₀)(t, u)` with `H₀ - H₁ ≤ B`, this bounds the curvature term `-∫∫ ∂_s H` of a linear
homotopy `H = H₀ + β(s) (H₁ - H₀)` along a map `u`. -/
theorem neg_mul_setIntegral_le_setIntegral_deriv_mul {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hab : a₁ ≤ b₁) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Icc a₁ b₁ ×ˢ Icc a₂ b₂)) {B : ℝ → ℝ} (hB : IntegrableOn B (Icc a₂ b₂))
    (hfB : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, -B z.2 ≤ f z) :
    -((β b₁ - β a₁) * ∫ t in Icc a₂ b₂, B t) ≤
      ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, deriv β z.1 * f z := by
  have hβ' : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  have hfi : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * f z) (Icc a₁ b₁ ×ˢ Icc a₂ b₂) :=
    ((hβ'.comp continuous_fst).continuousOn.mul hf).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  have hgi : IntegrableOn (fun z : ℝ × ℝ ↦ deriv β z.1 * B z.2) (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := by
    rw [IntegrableOn, hvol, ← Measure.prod_restrict]
    exact hβ'.continuousOn.integrableOn_Icc.mul_prod hB
  have hle : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, -(deriv β z.1 * B z.2) ≤
      ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, deriv β z.1 * f z :=
    setIntegral_mono_on hgi.neg hfi (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦ by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left (hfB z hz) hβm.deriv_nonneg
  have hftc : ∫ s in Icc a₁ b₁, deriv β s = β b₁ - β a₁ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hβ.differentiable one_ne_zero x)
        (hβ'.intervalIntegrable _ _)]
  rwa [integral_neg, hvol, setIntegral_prod_mul (deriv β) B, ← hvol, hftc] at hle

end TauCeti

end
