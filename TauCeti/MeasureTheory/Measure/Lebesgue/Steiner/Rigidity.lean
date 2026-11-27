/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.BoundedVariation.Slicing.Equality
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
   noninterval-excess slicing inequality of `TauCeti.Analysis.BoundedVariation.Slicing.Equality` at
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

2. **Steiner equality forces interval sections.** When `P(s) < ∞` and `P(S_e s) = P(s)`, almost
   every line section `{t | y + t • e ∈ s}` agrees almost everywhere with an order-connected set (an
   interval, possibly empty;
   `TauCeti.ae_exists_ordConnected_lineSection_ae_eq_of_perimeter_steinerSymmetrization_eq`),
   following directly from `TauCeti.ae_lineSection_ordConnected_of_perimeter_le_iSup` and
   `TauCeti.perimeter_steinerSymmetrization_eq_iSup`. Finiteness of `P(s)` is essential: both
   `P(s)` and `P(S_e s)` can be `∞` even when noninterval sections have positive transverse measure.

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
      ENNReal.ofReal √(1 - ‖p.val y‖ ^ 2)) +
    ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM p.val y *
      volume.real {t : ℝ | (y : E) + t • e ∈ s})
  have hsup : perimeter volume ⊤ (steinerSymmetrization e he s) = ⨆ p : Φ, V p := by
    rw [perimeter_steinerSymmetrization_eq_iSup e he hs hfin, iSup_subtype]
  have hAB : A ≤ᵐ[volume] {y : (ℝ ∙ e)ᗮ |
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I} := hbad
  refine (add_le_add le_rfl (mul_le_mul_right (measure_mono_ae hAB) _)).trans ?_
  rw [hsup, ENNReal.mul_iSup, ENNReal.iSup_add]
  exact iSup_le fun p => one_sub_mul_add_two_mul_sqrt_mul_volume_le_perimeter hs hfin e he
    (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ => id)
    hδ0 hδ1 p.val p.property

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
  have hreal : p₀ ^ 2 + 4 * a ^ 2 ≤ p ^ 2 := by
    have hsq : p₀ ^ 2 + (2 * a) ^ 2 ≤ p ^ 2 := by
      refine (sq_add_sq_le_sq_iff_forall_mul_add_mul_le hp₀0 (by positivity) hp0).2
        fun c s' hc0 hs'0 hcs => ?_
      have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s']
      have hlt := ENNReal.toReal_mono hPfin
        (ofReal_mul_perimeter_steinerSymmetrization_add_le_perimeter e he hs hfin hbad
          (δ := 1 - c) (sub_nonneg.2 hc1) (by linarith))
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP₀_fin)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hA_fin)] at hlt
      have h1 : 1 - (1 - c) = c := by ring
      have h2 : 2 * (1 - c) - (1 - c) ^ 2 = s' ^ 2 := by linarith
      rw [h1, h2, Real.sqrt_sq hs'0] at hlt
      have hlt' : c * p₀ + 2 * s' * a ≤ p := by simpa [p, p₀, a, hc0, hs'0] using hlt
      linarith
    linarith
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
  refine ae_lineSection_ordConnected_of_perimeter_le_iSup hs hfin hPfin e he ?_
  rw [← perimeter_steinerSymmetrization_eq_iSup e he hs hfin, heq]

end SteinerEqualityRigidity

end TauCeti
