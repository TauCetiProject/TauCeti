/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.MeasureTheory.Measure.Haar.Prod

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
* `Continuous.integrableOn_Icc_prod_Icc`: a continuous function is integrable over every closed
  rectangle.
* `TauCeti.setIntegral_Icc_prod_comp_fst`: a function of the first coordinate integrates over
  `[a₁, b₁] × [a₂, b₂]` to `b₂ - a₂` times its integral over `[a₁, b₁]`.
* `TauCeti.setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero`: a function vanishing outside
  the strip `[a₁, b₁] × I` has the same integral over every wider strip `[c, d] × I`.
* `TauCeti.setIntegral_Icc_add_prod_eq`: the integral over a translated strip
  `[c + L, d + L] × I` is the integral of the translate `z ↦ f (z + (L, 0))` over `[c, d] × I`.
* `TauCeti.setIntegral_Icc_prod_le_of_comp_add_le`: comparison of the integrals of `f` and `M` over
  a translated strip `[c + L, d + L] × I` and the original one, when `f (z + (L, 0)) ≤ M z`.
* `TauCeti.setIntegral_rect_le_mul_of_forall_setIntegral_le`: an inequality between the integrals
  over the vertical segments `{s} × [a₂, b₂]` integrates to the same inequality over the rectangle.
* `TauCeti.setIntegral_rect_le_mul_of_forall_setIntegral_le_symm`: the same for the horizontal
  segments `[a₁, b₁] × {t}`.
* `TauCeti.neg_mul_setIntegral_le_setIntegral_deriv_mul`: for a monotone `C¹` profile `β` and
  `-B(t) ≤ f`, the lower bound `-(β(b₁) - β(a₁)) ∫ B ≤ ∫∫ β'(s) f`.
* `TauCeti.setLIntegral_univ_prod_Icc_add_one_eq`,
  `TauCeti.setLIntegral_univ_prod_Icc_add_one_eq_of_periodic`,
  `TauCeti.setLIntegral_univ_prod_Icc_neg_one_two_le`,
  `TauCeti.eLpNorm_restrict_univ_prod_Icc_neg_one_two_le`: for a function of period one in the
  second coordinate, integrals over the horizontal strips `ℝ × [c, c + 1]` agree, and those over
  `ℝ × [-1, 2]` are controlled by those over the fundamental strip `ℝ × [0, 1]`.
* `TauCeti.eq_zero_of_forall_setIntegral_rect_norm_sq_eq_zero`: a continuous function of period
  one in the second coordinate whose `L²` norm vanishes on every rectangle `[-R, R] × [0, 1]` is
  zero.

Translation invariance of Lebesgue measure on `ℝ × ℝ` comes from
`TauCeti.isAddHaarMeasure_volume_prod`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a₁ b₁ a₂ b₂ : ℝ}

/-- **The fundamental theorem of calculus in the first coordinate.** The integral of a continuous
partial derivative `φ = ∂₁ Φ` over the rectangle `[a₁, b₁] × [a₂, b₂]` is the integral over
`[a₂, b₂]` of the difference of the values of `Φ` on the two vertical sides. -/
theorem setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun s ↦ Φ (s, t)) (φ (s, t)) s)
    (hab : a₁ ≤ b₁) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = ∫ t in Icc a₂ b₂, (Φ (b₁, t) - Φ (a₁, t)) := by
  by_cases hE : CompleteSpace E
  swap
  · simp [integral_of_not_completeSpace hE]
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
  by_cases hE : CompleteSpace E
  swap
  · simp [integral_of_not_completeSpace hE]
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

omit [NormedSpace ℝ E] in
/-- A continuous function is integrable over every closed rectangle `[a₁, b₁] × [a₂, b₂]`. -/
theorem _root_.Continuous.integrableOn_Icc_prod_Icc {f : ℝ × ℝ → E} (hf : Continuous f) :
    IntegrableOn f (Icc a₁ b₁ ×ˢ Icc a₂ b₂) :=
  hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- A function of the first coordinate integrates over the rectangle `[a₁, b₁] × [a₂, b₂]` to
`b₂ - a₂` times its integral over `[a₁, b₁]`. -/
theorem setIntegral_Icc_prod_comp_fst (f : ℝ → E) (h₂ : a₂ ≤ b₂) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f z.1 = (b₂ - a₂) • ∫ s in Icc a₁ b₁, f s := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_fst]
  simp [h₂]

/-- **Enlarging a strip.** If `f` vanishes at every point whose first coordinate lies outside
`[a₁, b₁]`, then its integrals over a wider strip `[c, d] × I ⊇ [a₁, b₁] × I` and over
`[a₁, b₁] × I` agree. -/
theorem setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure (ℝ × X)} {f : ℝ × X → E} {c d : ℝ} {I : Set X} (hI : MeasurableSet I)
    (hc : c ≤ a₁) (hd : b₁ ≤ d) (hf : ∀ z : ℝ × X, z.1 ∉ Icc a₁ b₁ → f z = 0) :
    ∫ z in Icc c d ×ˢ I, f z ∂μ = ∫ z in Icc a₁ b₁ ×ˢ I, f z ∂μ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_Icc.prod hI)
    (prod_mono (Icc_subset_Icc hc hd) subset_rfl) fun z hz ↦ hf z fun h ↦ hz.2 ⟨h, hz.1.2⟩

/-- The translate by `(L, 0)` of a point lies in the strip `[c + L, d + L] × I` exactly when the
point lies in `[c, d] × I`. -/
private theorem preimage_add_fst_Icc_prod (c d L : ℝ) (I : Set ℝ) :
    (· + (L, 0) : ℝ × ℝ → ℝ × ℝ) ⁻¹' (Icc (c + L) (d + L) ×ˢ I) = Icc c d ×ˢ I := by
  ext z
  simp only [mem_preimage, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add, add_zero]
  constructor <;> rintro ⟨⟨h, h'⟩, h''⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h''⟩

/-- **Integrals over a translated strip.** The integral of `f` over the strip `[c + L, d + L] × I`
is the integral of its translate `z ↦ f (z + (L, 0))` over the strip `[c, d] × I`. -/
theorem setIntegral_Icc_add_prod_eq (f : ℝ × ℝ → E) (c d L : ℝ) (I : Set ℝ) :
    ∫ z in Icc (c + L) (d + L) ×ˢ I, f z = ∫ z in Icc c d ×ˢ I, f (z + (L, 0)) := by
  rw [← (measurePreserving_add_right volume (L, 0)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) f, preimage_add_fst_Icc_prod]

/-- **Comparison of integrals over a translated strip.** If `f` at the translate `z + (L, 0)` is
pointwise bounded by `M z` on the strip `[c, d] × I`, with `M` integrable on that strip and `f`
integrable on the translated strip `[c + L, d + L] × I`, then the integral of `f` over the
translated strip is at most the integral of `M` over the original one. -/
theorem setIntegral_Icc_prod_le_of_comp_add_le {f M : ℝ × ℝ → ℝ} {c d L : ℝ} {I : Set ℝ}
    (hI : MeasurableSet I) (hfi : IntegrableOn f (Icc (c + L) (d + L) ×ˢ I))
    (hMi : IntegrableOn M (Icc c d ×ˢ I))
    (hfM : ∀ z ∈ Icc c d ×ˢ I, f (z + (L, 0)) ≤ M z) :
    ∫ z in Icc (c + L) (d + L) ×ˢ I, f z ≤ ∫ z in Icc c d ×ˢ I, M z := by
  rw [setIntegral_Icc_add_prod_eq]
  rw [← (measurePreserving_add_right volume (L, 0)).integrableOn_comp_preimage
    (measurableEmbedding_addRight _), preimage_add_fst_Icc_prod] at hfi
  exact setIntegral_mono_on hfi hMi (measurableSet_Icc.prod hI) hfM

/-- **Integrating a slicewise inequality.** If `f` and `g` are integrable over the rectangle
`[a₁, b₁] × [a₂, b₂]` and, for every `s ∈ [a₁, b₁]`, the integral of `f (s, ·)` over `[a₂, b₂]` is
at most `c` times that of `g (s, ·)`, then the integral of `f` over the rectangle is at most `c`
times that of `g`. -/
theorem setIntegral_rect_le_mul_of_forall_setIntegral_le {f g : ℝ × ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Icc a₁ b₁ ×ˢ Icc a₂ b₂)) (hg : IntegrableOn g (Icc a₁ b₁ ×ˢ Icc a₂ b₂))
    (h : ∀ s ∈ Icc a₁ b₁, ∫ t in Icc a₂ b₂, f (s, t) ≤ c * ∫ t in Icc a₂ b₂, g (s, t)) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f z ≤ c * ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, g z := by
  -- The integrals over the vertical segments are integrable functions of `s`, by Fubini.
  have hslice {k : ℝ × ℝ → ℝ} (hk : IntegrableOn k (Icc a₁ b₁ ×ˢ Icc a₂ b₂)) :
      IntegrableOn (fun s ↦ ∫ t in Icc a₂ b₂, k (s, t)) (Icc a₁ b₁) := by
    have h : Integrable k ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hk
    exact h.integral_prod_left
  rw [Measure.volume_eq_prod, setIntegral_prod _ hf, setIntegral_prod _ hg, ← integral_const_mul]
  exact setIntegral_mono_on (hslice hf) ((hslice hg).const_mul c) measurableSet_Icc h

/-- **Integrating a slicewise inequality, horizontal slices.** If `f` and `g` are integrable over
the rectangle `[a₁, b₁] × [a₂, b₂]` and, for every `t ∈ [a₂, b₂]`, the integral of `f (·, t)` over
`[a₁, b₁]` is at most `c` times that of `g (·, t)`, then the integral of `f` over the rectangle is
at most `c` times that of `g`. -/
theorem setIntegral_rect_le_mul_of_forall_setIntegral_le_symm {f g : ℝ × ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Icc a₁ b₁ ×ˢ Icc a₂ b₂)) (hg : IntegrableOn g (Icc a₁ b₁ ×ˢ Icc a₂ b₂))
    (h : ∀ t ∈ Icc a₂ b₂, ∫ s in Icc a₁ b₁, f (s, t) ≤ c * ∫ s in Icc a₁ b₁, g (s, t)) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f z ≤ c * ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, g z := by
  -- Fubini, integrating first over the horizontal segments and then in `t`.
  have hprod {k : ℝ × ℝ → ℝ} (hk : IntegrableOn k (Icc a₁ b₁ ×ˢ Icc a₂ b₂)) :
      Integrable k ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hk
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ (hprod hf),
    integral_prod_symm _ (hprod hg), ← integral_const_mul]
  exact setIntegral_mono_on (hprod hf).integral_prod_right
    ((hprod hg).integral_prod_right.const_mul c) measurableSet_Icc h

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

/-! ### Periodicity in the second coordinate -/

/-- For a function invariant under translation by `(0, k)`, the integrals over the strips
`ℝ × [k, k + 1]` and `ℝ × [0, 1]` agree. -/
theorem setLIntegral_univ_prod_Icc_add_one_eq {g : ℝ × ℝ → ℝ≥0∞} (k : ℝ)
    (hg : ∀ z, g (z + ((0 : ℝ), k)) = g z) :
    ∫⁻ z in univ ×ˢ Icc k (k + 1), g z = ∫⁻ z in univ ×ˢ Icc 0 1, g z := by
  have hφ := measurePreserving_add_right (volume : Measure (ℝ × ℝ)) ((0 : ℝ), k)
  have hpre : (· + ((0 : ℝ), k)) ⁻¹' (univ ×ˢ Icc k (k + 1)) = univ ×ˢ Icc (0 : ℝ) 1 := by
    ext ⟨s, t⟩
    simp only [mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, mem_Icc, true_and]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [← hφ.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight _) g, hpre]
  simp only [hg]

/-- For a measurable function of period one in `t`, the integrals over the strips
`ℝ × [c, c + 1]` and `ℝ × [0, 1]` agree, for every real `c`. -/
theorem setLIntegral_univ_prod_Icc_add_one_eq_of_periodic {g : ℝ × ℝ → ℝ≥0∞} (hgm : Measurable g)
    (hg : ∀ s t, g (s, t + 1) = g (s, t)) (c : ℝ) :
    ∫⁻ z in univ ×ˢ Icc c (c + 1), g z = ∫⁻ z in univ ×ˢ Icc 0 1, g z := by
  -- By Tonelli, both integrals are integrals over `s` of the integrals of the `1`-periodic slices
  -- `t ↦ g (s, t)` over a period, which are their integrals over the circle `ℝ ⧸ ℤ`.
  have hgp (s : ℝ) : Function.Periodic (fun t ↦ g (s, t)) 1 := hg s
  have key (a : ℝ) : ∫⁻ z in univ ×ˢ Icc a (a + 1), g z =
      ∫⁻ s, ∫⁻ x : UnitAddCircle, (hgp s).lift x := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod _ hgm.aemeasurable]
    refine lintegral_congr fun s ↦ ?_
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, ← UnitAddCircle.lintegral_preimage a]
    simp only [Function.Periodic.lift_coe]
  rw [key c]
  simpa using (key 0).symm

/-- For a function of period one in `t`, the integral over `ℝ × [-1, 2]` is at most three times
the integral over the strip `ℝ × [0, 1]`. -/
theorem setLIntegral_univ_prod_Icc_neg_one_two_le {g : ℝ × ℝ → ℝ≥0∞}
    (hg : ∀ s t, g (s, t + 1) = g (s, t)) :
    ∫⁻ z in univ ×ˢ Icc (-1) 2, g z ≤ 3 * ∫⁻ z in univ ×ˢ Icc 0 1, g z := by
  have h₁ : ∀ z, g (z + ((0 : ℝ), (1 : ℝ))) = g z := fun ⟨s, t⟩ ↦ by simpa using hg s t
  have hm₁ : ∀ z, g (z + ((0 : ℝ), (-1 : ℝ))) = g z := fun ⟨s, t⟩ ↦ by
    simpa [sub_eq_add_neg] using (hg s (t - 1)).symm
  have hU : (univ : Set ℝ) ×ˢ Icc (-1 : ℝ) 2 ⊆ ((univ : Set ℝ) ×ˢ Icc (-1) (-1 + 1)) ∪
      ((univ : Set ℝ) ×ˢ Icc 0 1) ∪ ((univ : Set ℝ) ×ˢ Icc 1 (1 + 1)) := by
    rintro ⟨s, t⟩ ⟨-, ht₁, ht₂⟩
    simp only [mem_union, mem_prod, mem_univ, mem_Icc, true_and]
    by_cases h0 : t ≤ 0
    · exact Or.inl (Or.inl ⟨ht₁, by linarith⟩)
    · by_cases h1 : t ≤ 1
      · exact Or.inl (Or.inr ⟨by linarith, h1⟩)
      · exact Or.inr ⟨by linarith, by linarith⟩
  calc ∫⁻ z in univ ×ˢ Icc (-1) 2, g z
      ≤ ∫⁻ z in ((univ : Set ℝ) ×ˢ Icc (-1) (-1 + 1)) ∪ ((univ : Set ℝ) ×ˢ Icc 0 1) ∪
          ((univ : Set ℝ) ×ˢ Icc 1 (1 + 1)), g z :=
        lintegral_mono_set hU
    _ ≤ (∫⁻ z in univ ×ˢ Icc (-1) (-1 + 1), g z) + (∫⁻ z in univ ×ˢ Icc 0 1, g z) +
          ∫⁻ z in univ ×ˢ Icc 1 (1 + 1), g z :=
        (lintegral_union_le _ _ _).trans (add_le_add_left (lintegral_union_le _ _ _) _)
    _ = 3 * ∫⁻ z in univ ×ˢ Icc 0 1, g z := by
        rw [setLIntegral_univ_prod_Icc_add_one_eq _ hm₁, setLIntegral_univ_prod_Icc_add_one_eq _ h₁]
        ring

/-- For a function of period one in `t`, the `L²` norm over `ℝ × [-1, 2]` is at most twice the
`L²` norm over the strip `ℝ × [0, 1]`. -/
theorem eLpNorm_restrict_univ_prod_Icc_neg_one_two_le {F : Type*} [NormedAddCommGroup F]
    {f : ℝ × ℝ → F}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ s t, f (s, t + 1) = f (s, t)) :
    eLpNorm f 2 (volume.restrict (univ ×ˢ Icc (-1) 2)) ≤
      2 * eLpNorm f 2 (volume.restrict (univ ×ˢ Icc 0 1)) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hfm.restrict,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hfm.restrict]
  have h := setLIntegral_univ_prod_Icc_neg_one_two_le (g := fun z ↦ ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal)
    fun s t ↦ by simp only [hf]
  calc (∫⁻ z in univ ×ˢ Icc (-1) 2, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
      ≤ (3 * ∫⁻ z in univ ×ˢ Icc 0 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = 3 ^ (1 / (2 : ℝ≥0∞).toReal) *
          (∫⁻ z in univ ×ˢ Icc 0 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 2 * (∫⁻ z in univ ×ˢ Icc 0 1, ‖f z‖ₑ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        calc (3 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) ≤ 4 ^ (1 / (2 : ℝ≥0∞).toReal) :=
              ENNReal.rpow_le_rpow (by norm_num) (by norm_num)
          _ = 2 := by
              rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]
              norm_num

omit [NormedSpace ℝ E] in
/-- A continuous function `ξ : ℝ × ℝ → E` of period one in the second coordinate whose `L²` norm
vanishes on every rectangle `[-R, R] × [0, 1]` is zero. -/
theorem eq_zero_of_forall_setIntegral_rect_norm_sq_eq_zero {ξ : ℝ × ℝ → E} (hξ : Continuous ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (h : ∀ R, 0 < R → ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 = 0) : ξ = 0 := by
  -- Periodicity in `t` moves every point into a rectangle `[-R, R] × [0, 1]`, where `‖ξ‖²`
  -- vanishes.
  funext z
  obtain ⟨s, t⟩ := z
  have hst := (show Function.Periodic (fun t ↦ ξ (s, t)) 1 from fun t ↦ hper s t).sub_int_mul_eq
    (x := t) ⌊t⌋
  rw [mul_one] at hst
  rw [Pi.zero_apply, ← hst, ← norm_eq_zero, ← sq_eq_zero_iff]
  have hR : (0 : ℝ) < |s| + 1 := by positivity
  refine eqOn_zero_of_setIntegral_rect_eq_zero (by linarith) zero_lt_one (by fun_prop)
    (fun z ↦ sq_nonneg ‖ξ z‖) (h _ hR) ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [neg_abs_le s]
  · linarith [le_abs_self s]
  · exact sub_nonneg.2 (Int.floor_le t)
  · linarith [Int.lt_floor_add_one t]

end TauCeti

end
