/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Variational

/-!
# Noninterval excess and equality rigidity for Steiner perimeter

Let `E` be a finite-dimensional real inner product space, `e` a unit vector, and `s` a
null-measurable set of finite volume with Steiner symmetral `S_e s = steinerSymmetrization e he s`.

1. **Scaled perimeter bound and Pythagorean noninterval excess.** Combining the exact transverse
   variational formula for `P(S_e s)` (`TauCeti.perimeter_steinerSymmetrization_eq_iSup` in
   `TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Variational`) with the localized
   noninterval-excess slicing inequality of `TauCeti.Analysis.BoundedVariation.Slicing.Excess` at
   rescaled test fields `(1 - δ) • φ` for `δ ∈ [0, 1]` shows that every family `A ⊆ (ℝ ∙ e)ᗮ` of
   sections that, for almost every `y ∈ A`, do not agree almost everywhere with any interval
   (`OrdConnected` set) satisfies
   `(1 - δ) P(S_e s) + 2 √(2 δ - δ²) |A| ≤ P(s)`
   (`TauCeti.ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter`). Optimizing in `δ` gives
   the parameter-free Pythagorean excess inequality
   `P(S_e s)² + 4 |A|² ≤ P(s)²`
   (`TauCeti.perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le`), which holds in
   particular for the full family of noninterval sections up to null sets
   (`TauCeti.perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le`).

2. **Steiner equality forces interval sections.** When `P(s) < ∞` and `P(S_e s) = P(s)`, the excess
   term `4 |A|²` vanishes, so for almost every `y ∈ (ℝ ∙ e)ᗮ` the line section
   `{t | y + t • e ∈ s}` agrees almost everywhere with an order-connected set (an interval, possibly
   empty; `TauCeti.ae_exists_ordConnected_lineSection_ae_eq_of_perimeter_steinerSymmetrization_eq`).
   Finiteness of `P(s)` is essential: both `P(s)` and `P(S_e s)` can be `∞` even when noninterval
   sections have positive transverse measure.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593, §1.2 and Theorem 1.1.
* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace TestFunction
open scoped Distributions ENNReal

namespace TauCeti

section SteinerEqualityRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Rescaling any `φ` (`‖φ‖ ≤ 1`) to `(1 - δ) • φ` (`0 ≤ δ ≤ 1`) scales the main variational
functional by at least `1 - δ` while gaining `2 √(2 δ - δ²) |A|` on any null-measurable family `A`
of noninterval sections. -/
private theorem mul_variational_add_excess_le_perimeter (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ENNReal.ofReal (1 - δ) *
        (2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s})) +
      2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      perimeter volume ⊤ s := by
  have h1δ : 0 ≤ 1 - δ := sub_nonneg.2 hδ1
  have hφ' (y : (ℝ ∙ e)ᗮ) : ‖((1 - δ) • φ) y‖ ≤ 1 := by
    rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ]
    exact (mul_le_of_le_one_right h1δ (hφ y)).trans (by linarith)
  have hex := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
    hs hfin e he hA hbad ((1 - δ) • φ) hφ'
  have hD_le : ENNReal.ofReal (1 - δ) *
      (2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) ≤
      2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖((1 - δ) • φ) y‖ ^ 2) := by
    rw [mul_left_comm (ENNReal.ofReal (1 - δ)) 2,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr 2 * ?_
    refine lintegral_mono fun y => ?_
    have hrhs : ENNReal.ofReal √((1 - δ) ^ 2 * (1 - ‖φ y‖ ^ 2)) =
        ENNReal.ofReal (1 - δ) * ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1δ, ENNReal.ofReal_mul h1δ]
    rw [← hrhs, FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    have hsq1 : (1 - δ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖φ y‖]
  have hB_eq : ENNReal.ofReal (1 - δ) * ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) =
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM ((1 - δ) • φ) y *
        volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
    rw [← ENNReal.ofReal_mul h1δ, ← integral_const_mul]
    congr 1; refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hA_le : 2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      2 * ∫⁻ y in A, ENNReal.ofReal √(1 - ‖((1 - δ) • φ) y‖ ^ 2) := by
    rw [mul_assoc, ← setLIntegral_const A (ENNReal.ofReal √(2 * δ - δ ^ 2))]
    gcongr 2 * ?_
    refine lintegral_mono fun y => ?_
    rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1δ, mul_pow]
    have hsq : ‖φ y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hφ y)
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - δ)]))
  rw [mul_add, hB_eq, add_right_comm]
  exact (add_le_add (add_le_add hD_le hA_le) le_rfl).trans hex

/-- **Scaled Steiner perimeter and noninterval excess bound.** For any null-measurable set `s` of
finite volume, a unit vector `e`, any family `A ⊆ (ℝ ∙ e)ᗮ` of sections that, for almost every
`y ∈ A`, do not agree almost everywhere with any interval (`OrdConnected` set), and `δ ∈ [0, 1]`,
`(1 - δ) P(S_e s) + 2 √(2 δ - δ²) |A| ≤ P(s)`. -/
theorem ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ}
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) * perimeter volume ⊤ (steinerSymmetrization e he s) +
        2 * ENNReal.ofReal √(2 * δ - δ ^ 2) * volume A ≤
      perimeter volume ⊤ s := by
  let Φ := {φ : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ) // ∀ y, ‖φ y‖ ≤ 1}
  have : Nonempty Φ := ⟨⟨0, by simp⟩⟩
  let V : Φ → ℝ≥0∞ := fun p =>
    2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
      ENNReal.ofReal √(1 - ‖p.1 y‖ ^ 2)) +
    ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM p.1 y *
      volume.real {t : ℝ | (y : E) + t • e ∈ s})
  have hsup : perimeter volume ⊤ (steinerSymmetrization e he s) = ⨆ p : Φ, V p := by
    rw [perimeter_steinerSymmetrization_eq_iSup e he hs hfin, iSup_subtype]
  have hAB : A ≤ᵐ[volume] {y : (ℝ ∙ e)ᗮ |
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} := hbad
  refine (add_le_add le_rfl (mul_le_mul_right (measure_mono_ae hAB) _)).trans ?_
  rw [hsup, ENNReal.mul_iSup, ENNReal.iSup_add]
  exact iSup_le fun p => mul_variational_add_excess_le_perimeter e he hs hfin
    (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ => id)
    hδ0 hδ1 p.1 p.2

private theorem eq_zero_of_forall_delta_le {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hdelta : ∀ {δ : ℝ}, 0 < δ → δ < 1 → (1 - δ) * p + 2 * √(2 * δ - δ ^ 2) * a ≤ p) :
    a = 0 := by
  by_contra ha_ne
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_ne)
  set δ := 4 * a ^ 2 / (p ^ 2 + 4 * a ^ 2)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := (div_lt_one (by positivity)).2 (by linarith [mul_pos hp hp])
  have hb := hdelta hδ0 hδ1
  have hsq : 4 * (2 * δ - δ ^ 2) * a ^ 2 ≤ (δ * p) ^ 2 := by
    have hsub : 2 * √(2 * δ - δ ^ 2) * a ≤ δ * p := by linarith
    calc 4 * (2 * δ - δ ^ 2) * a ^ 2
        = (2 * √(2 * δ - δ ^ 2) * a) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]; ring
      _ ≤ (δ * p) ^ 2 := pow_le_pow_left₀ (by positivity) hsub 2
  have hid : δ * (p ^ 2 + 4 * a ^ 2) = 4 * a ^ 2 := div_mul_cancel₀ _ (by positivity)
  have hmul_id : δ ^ 2 * (p ^ 2 + 4 * a ^ 2) = 4 * δ * a ^ 2 := by
    calc δ ^ 2 * (p ^ 2 + 4 * a ^ 2) = δ * (δ * (p ^ 2 + 4 * a ^ 2)) := by ring
      _ = 4 * δ * a ^ 2 := by rw [hid]; ring
  linarith [mul_pos hδ0 (sq_pos_of_pos ha_pos)]

private theorem sq_add_four_mul_sq_le_of_forall_delta {p p₀ a : ℝ}
    (hp₀ : 0 ≤ p₀) (ha : 0 ≤ a) (hp₀_le : p₀ ≤ p) (h2a : 2 * a ≤ p)
    (hdelta : ∀ {δ : ℝ}, 0 < δ → δ < 1 → (1 - δ) * p₀ + 2 * √(2 * δ - δ ^ 2) * a ≤ p) :
    p₀ ^ 2 + 4 * a ^ 2 ≤ p ^ 2 := by
  rcases eq_or_lt_of_le hp₀ with hp₀_eq | hp₀_pos
  · rw [← hp₀_eq]; nlinarith
  rcases eq_or_lt_of_le hp₀_le with hp_eq | hp₀_lt
  · subst hp_eq
    have ha_zero : a = 0 := eq_zero_of_forall_delta_le hp₀_pos ha hdelta
    rw [ha_zero]; ring_nf; exact le_rfl
  · have hp_pos : 0 < p := hp₀_pos.trans hp₀_lt
    set δ := 1 - p₀ / p
    have hδ0 : 0 < δ := sub_pos.2 ((div_lt_one hp_pos).2 hp₀_lt)
    have hδ1 : δ < 1 := sub_lt_self 1 (div_pos hp₀_pos hp_pos)
    have hb := hdelta hδ0 hδ1
    have h1δ : 1 - δ = p₀ / p := by ring
    have h2δ : 2 * δ - δ ^ 2 = (p ^ 2 - p₀ ^ 2) / p ^ 2 := by
      calc 2 * δ - δ ^ 2 = 1 - (1 - δ) ^ 2 := by ring
        _ = 1 - (p₀ / p) ^ 2 := by rw [h1δ]
        _ = (p ^ 2 - p₀ ^ 2) / p ^ 2 := by rw [div_pow, one_sub_div (by positivity)]
    rw [h1δ, h2δ, Real.sqrt_div (by nlinarith), Real.sqrt_sq hp_pos.le] at hb
    have hmul : p₀ ^ 2 + 2 * √(p ^ 2 - p₀ ^ 2) * a ≤ p ^ 2 := by
      have hbp := mul_le_mul_of_nonneg_right hb hp_pos.le
      calc p₀ ^ 2 + 2 * √(p ^ 2 - p₀ ^ 2) * a
          = (p₀ / p * p₀ + 2 * (√(p ^ 2 - p₀ ^ 2) / p) * a) * p := by field_simp
        _ ≤ p * p := hbp
        _ = p ^ 2 := (sq p).symm
    have hdiff_pos : 0 ≤ p ^ 2 - p₀ ^ 2 := by nlinarith
    have h2a_sqrt : 2 * a ≤ √(p ^ 2 - p₀ ^ 2) := by
      have hle_sqrt : 2 * √(p ^ 2 - p₀ ^ 2) * a ≤ √(p ^ 2 - p₀ ^ 2) ^ 2 := by
        rw [Real.sq_sqrt hdiff_pos]; linarith
      have hrt_pos : 0 < √(p ^ 2 - p₀ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      nlinarith
    have hsq : (2 * a) ^ 2 ≤ √(p ^ 2 - p₀ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2a_sqrt 2
    rw [Real.sq_sqrt hdiff_pos] at hsq
    linarith

/-- **Pythagorean noninterval excess in Steiner's perimeter inequality.** For any null-measurable
set `s` of finite volume, a unit vector `e`, and any family `A ⊆ (ℝ ∙ e)ᗮ` of line sections of `s`
in direction `e` that, for almost every `y ∈ A`, do not agree almost everywhere with any interval
(`OrdConnected` set),
`P(S_e s)² + 4 |A|² ≤ P(s)²`. -/
theorem perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    {A : Set (ℝ ∙ e)ᗮ}
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ^ 2 + 4 * volume A ^ 2 ≤
      perimeter volume ⊤ s ^ 2 := by
  set P := perimeter volume ⊤ s
  set P₀ := perimeter volume ⊤ (steinerSymmetrization e he s)
  rcases eq_or_ne P ⊤ with hPtop | hPfin
  · simp [hPtop]
  have hP₀_le : P₀ ≤ P := perimeter_steinerSymmetrization_le e he hs hfin
  have hP₀_fin : P₀ ≠ ⊤ := ne_top_of_le_ne_top hPfin hP₀_le
  have hAB : A ≤ᵐ[volume] {y : (ℝ ∙ e)ᗮ |
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} := hbad
  have h2A : 2 * volume A ≤ P :=
    (mul_le_mul_right (measure_mono_ae hAB) _).trans
      (le_add_self.trans (two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
        hs hfin e he (nullMeasurableSet_noninterval_lineSection hs hfin e he)
        (.of_forall fun _ => id)))
  have hA_fin : volume A ≠ ⊤ := fun htop => hPfin (top_unique (by simpa [htop] using h2A))
  set p := P.toReal; set p₀ := P₀.toReal; set a := (volume A).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp₀0 : 0 ≤ p₀ := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have h2a_le : 2 * a ≤ p := by
    simpa [p, a, ENNReal.toReal_mul] using ENNReal.toReal_mono hPfin h2A
  have hdelta {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
      (1 - δ) * p₀ + 2 * √(2 * δ - δ ^ 2) * a ≤ p := by
    have hlt := ENNReal.toReal_mono hPfin
      (ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter e he hs hfin hbad
        hδ0.le hδ1.le)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP₀_fin)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hA_fin)] at hlt
    simpa [p, p₀, a, hδ1.le] using hlt
  have hreal : p₀ ^ 2 + 4 * a ^ 2 ≤ p ^ 2 :=
    sq_add_four_mul_sq_le_of_forall_delta hp₀0 ha0 (ENNReal.toReal_mono hPfin hP₀_le) h2a_le hdelta
  have hof := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (sq_nonneg p₀) (mul_nonneg (by positivity) (sq_nonneg a))] at hof
  simpa [p, p₀, a, hp0, hp₀0, ha0, hPfin, hP₀_fin, hA_fin] using hof

/-- **Pythagorean noninterval excess for the full family of noninterval sections.** For any
null-measurable set `s` of finite volume and any unit vector `e`,
`P(S_e s)² + 4 |{y | s_y is not a.e. an interval}|² ≤ P(s)²`. -/
theorem perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ^ 2 +
        4 * volume {y : (ℝ ∙ e)ᗮ |
          ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} ^ 2 ≤
      perimeter volume ⊤ s ^ 2 :=
  perimeter_steinerSymmetrization_sq_add_four_mul_volume_sq_le e he hs hfin (.of_forall fun _ => id)

/-- **Steiner perimeter equality forces interval sections.** If a null-measurable set `s` of finite
volume and finite perimeter satisfies `P(S_e s) = P(s)`, then for almost every `y ∈ (ℝ ∙ e)ᗮ` the
line section `{t | y + t • e ∈ s}` agrees almost everywhere with an order-connected set (an
interval, possibly empty). -/
theorem ae_exists_ordConnected_lineSection_ae_eq_of_perimeter_steinerSymmetrization_eq
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hPfin : perimeter volume ⊤ s ≠ ⊤)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  set A : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ |
    ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hpyth :=
    perimeter_steinerSymmetrization_sq_add_four_mul_volume_noninterval_sq_le e he hs hfin
  rw [heq] at hpyth
  have hP2_fin : perimeter volume ⊤ s ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hPfin
  have h0 : 4 * volume A ^ 2 = 0 := by
    have hadd : perimeter volume ⊤ s ^ 2 + 4 * volume A ^ 2 = perimeter volume ⊤ s ^ 2 + 0 :=
      le_antisymm (hpyth.trans_eq (add_zero _).symm) (by simp)
    exact (ENNReal.add_right_inj hP2_fin).1 hadd
  have hA0 : volume A = 0 := by
    rcases mul_eq_zero.1 h0 with h4 | hsq
    · norm_num at h4
    · exact sq_eq_zero_iff.1 hsq
  filter_upwards [compl_mem_ae_iff.2 hA0] with y hy
  by_contra! hbad
  exact hy hbad

end SteinerEqualityRigidity

end TauCeti
