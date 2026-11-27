/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability

/-!
# Equality in the joint slicing inequality forces interval sections

Let `s` be a finite-volume Lebesgue-measurable set and `e` a unit direction. Write
`L y = |{t | y + t • e ∈ s}|` for the lengths of the line sections over the orthogonal hyperplane
`(ℝ ∙ e)ᗮ`, and `D = {y | 0 < L y}`. For a test vector field `φ` on `(ℝ ∙ e)ᗮ` with `‖φ‖ ≤ 1`, the
joint slicing inequality and the one-dimensional bound `P ≥ 2` for sections of positive length give

`2 ∫_D √(1 - ‖φ‖²) + ∫ div φ · L ≤ P(s)`,

so the supremum of the left side over all such `φ` is at most `P(s)`
(`TauCeti.iSup_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`). This supremum depends on
`s` only through the section lengths `L`, which Steiner symmetrization along `e` preserves; it is
the total variation of the measure `(2 · 1_D, DL)` on the hyperplane.

This file proves the equality case: if `P(s)` is finite and at most this supremum, then almost
every line section of `s` agrees almost everywhere with an interval
(`TauCeti.ae_lineSection_ordConnected_of_perimeter_le_iSup`).

Each noninterval section in a family `A` costs an extra `2 √(1 - ‖φ‖²)` in the slicing bound
(`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`).
Replacing `φ` by `(1 - τ) • φ` with `0 < τ ≤ 1` multiplies the pairing by `1 - τ`, does not
decrease the weight `√(1 - ‖φ‖²)` by more than the factor `1 - τ`, and makes the weight at least
`√τ` everywhere. So `(1 - τ) P(s) + 2 √τ |A| ≤ P(s)`, that is `2 √τ |A| ≤ τ P(s)`, and letting
`τ → 0` gives `|A| = 0`.

In the rigidity argument for the isoperimetric inequality this is applied to a set with the
same perimeter as its Steiner symmetral. The Steiner symmetral, whose sections are centered
intervals, has perimeter at most the supremum above; equality of perimeters then forces the
sections of `s` itself to be intervals.

## References

* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2 and Theorem A, for the interval-section
  condition in the equality case of Steiner's inequality.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 14, for the
  slicing bound in Steiner's inequality.
-/

public section

open MeasureTheory Set TestFunction Filter
open scoped ENNReal Distributions Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The slicing lower bound for perimeter, as a supremum.** For a null-measurable set `s` of
finite volume and a unit vector `e`, the supremum over test vector fields `φ` on `(ℝ ∙ e)ᗮ` with
`‖φ‖ ≤ 1` of `2 ∫_D √(1 - ‖φ‖²) + ∫ div φ · L` is at most `P(s)`, where `L` gives the lengths of
the line sections of `s` along `e` and `D = {L > 0}`. -/
theorem iSup_two_mul_setLIntegral_add_ofReal_integral_le_perimeter {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
        2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≤ perimeter volume ⊤ s :=
  iSup₂_le fun φ hφ ↦ le_trans (by simp)
    (two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter hs hfin e he
      (A := ∅) nullMeasurableSet_empty (.of_forall fun _ h ↦ h.elim) φ hφ)

/-- Shrinking a field of norm at most one by the factor `1 - τ` keeps the slicing weight
`√(1 - ‖φ‖²)` above both `(1 - τ) √(1 - ‖φ‖²)` and `√(2 * τ - τ ^ 2)`. -/
private theorem le_sqrt_one_sub_mul_sq {τ r : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) :
    (1 - τ) * √(1 - r ^ 2) ≤ √(1 - ((1 - τ) * r) ^ 2) ∧
      √(2 * τ - τ ^ 2) ≤ √(1 - ((1 - τ) * r) ^ 2) := by
  have hc₀ : 0 ≤ 1 - τ := by linarith
  constructor
  · calc (1 - τ) * √(1 - r ^ 2) = √((1 - τ) ^ 2) * √(1 - r ^ 2) := by rw [Real.sqrt_sq hc₀]
      _ = √((1 - τ) ^ 2 * (1 - r ^ 2)) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ ≤ √(1 - ((1 - τ) * r) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
  · exact Real.sqrt_le_sqrt
      (by have : ((1 - τ) * r) ^ 2 ≤ (1 - τ) ^ 2 := by
            nlinarith [mul_le_of_le_one_right hc₀ hr₁, mul_nonneg hc₀ hr₀]
          linarith)

/-- The slicing bound at the shrunken field `(1 - τ) • φ`: for `0 ≤ τ ≤ 1` and every
null-measurable family `A` of noninterval sections, `(1 - τ)` times the slicing functional at `φ`,
plus `2 √(2 τ - τ²) |A|`, is at most `P(s)`. -/
theorem one_sub_mul_add_two_mul_sqrt_mul_volume_le_perimeter {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ENNReal.ofReal (1 - τ) *
        (2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s})) +
      2 * ENNReal.ofReal √(2 * τ - τ ^ 2) * volume A ≤ perimeter volume ⊤ s := by
  have hc₀ : 0 ≤ 1 - τ := by linarith
  have hψ : ∀ y, ‖((1 - τ) • φ) y‖ ≤ 1 := fun y ↦ by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg hc₀]
    nlinarith [norm_nonneg (φ y), hφ y]
  have hw : ∀ y, ‖((1 - τ) • φ) y‖ = (1 - τ) * ‖φ y‖ := fun y ↦ by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg hc₀]
  have h := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
    hs hfin e he hA hbad ((1 - τ) • φ) hψ
  have hD : ENNReal.ofReal (1 - τ) *
      ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) ≤
      ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖((1 - τ) • φ) y‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y ↦ ?_
    rw [← ENNReal.ofReal_mul hc₀, hw]
    exact ENNReal.ofReal_le_ofReal (le_sqrt_one_sub_mul_sq hτ₀ hτ₁ (norm_nonneg _) (hφ y)).1
  have hA' : ENNReal.ofReal √(2 * τ - τ ^ 2) * volume A ≤
      ∫⁻ y in A, ENNReal.ofReal √(1 - ‖((1 - τ) • φ) y‖ ^ 2) := by
    rw [← setLIntegral_const]
    refine lintegral_mono fun y ↦ ?_
    rw [hw]
    exact ENNReal.ofReal_le_ofReal (le_sqrt_one_sub_mul_sq hτ₀ hτ₁ (norm_nonneg _) (hφ y)).2
  have hdiv : ENNReal.ofReal (1 - τ) * ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
      volume.real {t : ℝ | (y : E) + t • e ∈ s}) =
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM ((1 - τ) • φ) y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
    simp only [map_smul, smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, ENNReal.ofReal_mul hc₀]
  calc _ = 2 * (ENNReal.ofReal (1 - τ) *
          ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
            ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        2 * (ENNReal.ofReal √(2 * τ - τ ^ 2) * volume A) +
        ENNReal.ofReal (1 - τ) * ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by ring
    _ ≤ _ := by rw [hdiv]; gcongr
    _ ≤ _ := h

/-- If `P(s)` is at most the slicing supremum, then for `0 ≤ τ ≤ 1` the noninterval sections satisfy
`(1 - τ) P(s) + 2 √τ |A| ≤ P(s)`. -/
private theorem one_sub_mul_perimeter_add_two_mul_sqrt_mul_volume_le_perimeter {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (h : perimeter volume ⊤ s ≤ ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
      2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}))
    {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) :
    ENNReal.ofReal (1 - τ) * perimeter volume ⊤ s +
        2 * ENNReal.ofReal √τ * volume {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
          ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} ≤
      perimeter volume ⊤ s := by
  have : Nonempty {φ : 𝓓(⊤, (ℝ ∙ e)ᗮ) // ∀ y : (ℝ ∙ e)ᗮ, ‖φ y‖ ≤ 1} :=
    ⟨⟨0, fun y ↦ by simp [zero_apply]⟩⟩
  refine le_trans (add_le_add_left (mul_le_mul_right h _) _) ?_
  rw [iSup_subtype', ENNReal.mul_iSup, ENNReal.iSup_add]
  exact iSup_le fun φ ↦ le_trans (by gcongr; nlinarith)
    (one_sub_mul_add_two_mul_sqrt_mul_volume_le_perimeter hs hfin e he
      (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ hy ↦ hy)
      hτ₀ hτ₁ φ.val φ.property)

/-- Cancelling `ofReal (1 - τ) * a` against `a` in real numbers: for finite `a` and `b`,
`ofReal (1 - τ) * a + 2 √τ b ≤ a` gives `2 √τ b ≤ τ a`. -/
private theorem two_mul_sqrt_mul_toReal_le_mul_toReal {τ : ℝ} {a b : ℝ≥0∞} (ha : a ≠ ∞)
    (hb : b ≠ ∞) (hτ₁ : τ ≤ 1) (h : ENNReal.ofReal (1 - τ) * a + 2 * ENNReal.ofReal √τ * b ≤ a) :
    2 * √τ * b.toReal ≤ τ * a.toReal := by
  have h' := ENNReal.toReal_mono ha h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hτ₁),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg τ), ENNReal.toReal_ofNat] at h'
  linarith

/-- **Equality in the joint slicing inequality forces interval sections.** Let `s` be a
null-measurable set of finite volume and finite perimeter and `e` a unit vector. If `P(s)` is at
most the supremum over test vector fields `φ` on `(ℝ ∙ e)ᗮ` with `‖φ‖ ≤ 1` of
`2 ∫_D √(1 - ‖φ‖²) + ∫ div φ · L`, where `L` gives the lengths of the line sections of `s` along `e`
and `D = {L > 0}`, then almost every line section `{t | y + t • e ∈ s}` agrees almost everywhere
with an interval. By `TauCeti.iSup_two_mul_setLIntegral_add_ofReal_integral_le_perimeter` the
hypothesis is equivalent to equality. -/
theorem ae_lineSection_ordConnected_of_perimeter_le_iSup {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) (hP : perimeter volume ⊤ s ≠ ∞)
    (e : E) (he : ‖e‖ = 1)
    (h : perimeter volume ⊤ s ≤ ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
      2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s})) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  set A := {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
    ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hτ := fun τ (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1) ↦
    one_sub_mul_perimeter_add_two_mul_sqrt_mul_volume_le_perimeter hs hfin e he h hτ₀ hτ₁
  have hAfin : volume A ≠ ∞ := by
    have h1 := hτ 1 zero_le_one le_rfl
    simp only [sub_self, ENNReal.ofReal_zero, zero_mul, zero_add, Real.sqrt_one,
      ENNReal.ofReal_one, mul_one] at h1
    exact ne_top_of_le_ne_top hP (le_trans (le_mul_of_one_le_left' (by norm_num)) h1)
  -- In real numbers: `2 √τ |A| ≤ τ P(s)`, so `2 |A| ≤ √τ P(s)` for `0 < τ ≤ 1`.
  have hreal : ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      (volume A).toReal ≤ √τ * (perimeter volume ⊤ s).toReal / 2 := fun τ hτ₀ hτ₁ ↦ by
    have h' := two_mul_sqrt_mul_toReal_le_mul_toReal hP hAfin hτ₁ (hτ τ hτ₀.le hτ₁)
    rw [le_div_iff₀ two_pos]
    refine le_of_mul_le_mul_left ?_ (Real.sqrt_pos.2 hτ₀)
    rw [← mul_assoc √τ √τ, Real.mul_self_sqrt hτ₀.le]
    linarith
  have hlim : Tendsto (fun τ : ℝ ↦ √τ * (perimeter volume ⊤ s).toReal / 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).mul_const
      (perimeter volume ⊤ s).toReal |>.div_const 2).mono_left nhdsWithin_le_nhds
  have hzero : (volume A).toReal ≤ 0 := ge_of_tendsto hlim <| by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with τ ⟨hτ₀, hτ₁⟩ using hreal τ hτ₀ hτ₁
  have hA0 : volume A = 0 :=
    (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hzero ENNReal.toReal_nonneg) |>.resolve_right
      hAfin
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA0] with y hy
  simpa [A] using hy

end TauCeti
