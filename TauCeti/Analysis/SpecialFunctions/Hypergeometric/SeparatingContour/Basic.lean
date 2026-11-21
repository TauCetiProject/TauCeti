/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Separating-contour Mellin–Barnes functional and abscissa-independence

Following DLMF §15.6(ii) (15.6.6), we define `Complex.mellinBarnesSeparatingIntegral` at `σ < 0`
as the separating-contour Mellin–Barnes functional representing `Γ(a) Γ(b) 𝐅(a, b; c; z)` (and
hence `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)`): the vertical-line integral
`(2πi)⁻¹ ∫_{Re t = σ} ... dt = (2π)⁻¹ ∫_{-∞}^∞ ... (σ + i y) dy` plus the residue sum over the
finite pole set `Complex.mellinBarnesLeftPoles a b σ` of left-family poles `-a - k`, `-b - k` that
have crossed to the right of `Re t = σ`. Using the uniform vertical-strip Stirling bound for `Γ`
and `1 / Γ`, we prove exponential vertical decay on `-z ∈ Complex.slitPlane`, vertical
integrability, and independence of the choice of pole-avoiding abscissa `σ < 0` via the rectangle
residue theorem.

## Main definitions and results

* `Complex.mellinBarnesIntegrand`, `Complex.mellinBarnesLeftPoles`,
  `Complex.mellinBarnesSeparatingIntegral`.
* `Complex.residue_mellinBarnesIntegrand_neg_sub_natCast_left`,
  `Complex.residue_mellinBarnesIntegrand_neg_sub_natCast_right`: closed-form simple-pole residues.
* `Complex.exists_norm_mellinBarnesIntegrand_vertical_le`,
  `Complex.verticalIntegrable_mellinBarnesIntegrand`: vertical decay and integrability.
* `Complex.mellinBarnesSeparatingIntegral_eq_of_lt_zero`: `σ`-independence for admissible
  `σ₁, σ₂ < 0`.

## References

* NIST DLMF, §15.6(ii), eq. 15.6.6; Whittaker & Watson, §14.5; Olver, Ch. 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace Complex

/-! ### Section 1: Separating-contour definitions and pole combinatorics -/

/-- The Mellin–Barnes kernel `Γ(a + t) Γ(b + t) Γ(-t) (Γ(c + t))⁻¹ (-z) ^ t` of the Gauss
hypergeometric function (DLMF 15.6.6), written with the entire reciprocal Gamma factor
`(Γ(c + t))⁻¹` so that all lower parameters `c : ℂ` are handled uniformly. -/
def mellinBarnesIntegrand (a b c z t : ℂ) : ℂ :=
  Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t

/-- Defining formula for `mellinBarnesIntegrand`. -/
theorem mellinBarnesIntegrand_def (a b c z t : ℂ) :
    mellinBarnesIntegrand a b c z t =
      Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t := (rfl)

/-- Symmetry of `mellinBarnesIntegrand` in the upper parameters `a` and `b`. -/
theorem mellinBarnesIntegrand_symm (a b c z t : ℂ) :
    mellinBarnesIntegrand a b c z t = mellinBarnesIntegrand b a c z t := by
  simp only [mellinBarnesIntegrand_def, mul_comm (Gamma (a + t)) (Gamma (b + t))]

/-- The finite set of candidate left-family poles `t = -a - k`, `t = -b - k` (`k : ℕ`) of the
Barnes integrand lying strictly to the right of the vertical line `Re t = σ`. -/
def mellinBarnesLeftPoles (a b : ℂ) (σ : ℝ) : Finset ℂ :=
  (((Finset.range (⌊-a.re - σ⌋₊ + 1)).image fun k : ℕ => -a - k) ∪
    ((Finset.range (⌊-b.re - σ⌋₊ + 1)).image fun k : ℕ => -b - k)).filter fun t : ℂ => σ < t.re

/-- A complex number belongs to `mellinBarnesLeftPoles a b σ` if and only if its real part exceeds
`σ` and it has the form `-a - k` or `-b - k` for some `k : ℕ`. -/
@[simp]
theorem mem_mellinBarnesLeftPoles {a b : ℂ} {σ : ℝ} {t : ℂ} :
    t ∈ mellinBarnesLeftPoles a b σ ↔
      σ < t.re ∧ ((∃ k : ℕ, t = -a - k) ∨ (∃ k : ℕ, t = -b - k)) := by
  simp only [mellinBarnesLeftPoles, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    Finset.mem_range]
  refine ⟨fun ⟨h, hσ⟩ => ⟨hσ, ?_⟩, fun ⟨hσ, h⟩ => ⟨?_, hσ⟩⟩
  · rcases h with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩ <;> [exact Or.inl ⟨k, rfl⟩; exact Or.inr ⟨k, rfl⟩]
  · rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine Or.inl ⟨k, ?_, rfl⟩
      have hlt : (k : ℝ) < -a.re - σ := by simp at hσ; linarith
      exact_mod_cast hlt.trans (Nat.lt_floor_add_one (-a.re - σ))
    · refine Or.inr ⟨k, ?_, rfl⟩
      have hlt : (k : ℝ) < -b.re - σ := by simp at hσ; linarith
      exact_mod_cast hlt.trans (Nat.lt_floor_add_one (-b.re - σ))

/-- Symmetry of `mellinBarnesLeftPoles` in `a` and `b`. -/
theorem mellinBarnesLeftPoles_symm (a b : ℂ) (σ : ℝ) :
    mellinBarnesLeftPoles a b σ = mellinBarnesLeftPoles b a σ := by
  ext t; simp [or_comm]

/-- When `-Re a ≤ σ` and `-Re b ≤ σ`, no left-family pole lies strictly to the right of
`Re t = σ`. -/
@[simp]
theorem mellinBarnesLeftPoles_eq_empty_of_neg_re_le {a b : ℂ} {σ : ℝ}
    (ha : -a.re ≤ σ) (hb : -b.re ≤ σ) :
    mellinBarnesLeftPoles a b σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rcases mem_mellinBarnesLeftPoles.1 ht with ⟨hσ, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩ <;>
    · simp only [sub_re, neg_re, natCast_re] at hσ; linarith [k.cast_nonneg (α := ℝ)]

/-- The separating-contour Mellin–Barnes functional at abscissa `σ`, representing
`Γ(a) Γ(b) 𝐅(a, b; c; z)` (hence `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)`): the vertical-line
integral `(2πi)⁻¹ ∫_{Re t = σ} ... dt = (2π)⁻¹ ∫_{-∞}^∞ ... (σ + i y) dy` plus the sum of
residues at the left-family poles strictly to the right of `Re t = σ`. -/
def mellinBarnesSeparatingIntegral (a b c z : ℂ) (σ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I)) +
    ∑ s ∈ mellinBarnesLeftPoles a b σ, TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s

/-- Defining formula for `mellinBarnesSeparatingIntegral`. -/
theorem mellinBarnesSeparatingIntegral_def (a b c z : ℂ) (σ : ℝ) :
    mellinBarnesSeparatingIntegral a b c z σ =
      (2 * π : ℂ)⁻¹ * (∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I)) +
        ∑ s ∈ mellinBarnesLeftPoles a b σ,
          TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s := (rfl)

/-- Symmetry of `mellinBarnesSeparatingIntegral` in `a` and `b`. -/
theorem mellinBarnesSeparatingIntegral_symm (a b c z : ℂ) (σ : ℝ) :
    mellinBarnesSeparatingIntegral a b c z σ = mellinBarnesSeparatingIntegral b a c z σ := by
  rw [mellinBarnesSeparatingIntegral_def, mellinBarnesSeparatingIntegral_def,
    mellinBarnesLeftPoles_symm a b σ]
  simp_rw [funext (mellinBarnesIntegrand_symm a b c z)]

/-- When `-Re a ≤ σ` and `-Re b ≤ σ`, the separating-contour functional reduces to the straight
vertical-line integral along `Re t = σ`. -/
theorem mellinBarnesSeparatingIntegral_of_neg_re_le {a b : ℂ} (c z : ℂ) {σ : ℝ}
    (ha : -a.re ≤ σ) (hb : -b.re ≤ σ) :
    mellinBarnesSeparatingIntegral a b c z σ =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I) := by
  simp [mellinBarnesSeparatingIntegral_def, mellinBarnesLeftPoles_eq_empty_of_neg_re_le ha hb]

/-! ### Section 2: Meromorphy, regular points, and simple-pole residues -/

/-- The Barnes integrand `t ↦ mellinBarnesIntegrand a b c z t` is meromorphic at every point of
the complex plane, for all parameters `a, b, c, z : ℂ`. -/
theorem meromorphicAt_mellinBarnesIntegrand (a b c z t : ℂ) :
    MeromorphicAt (mellinBarnesIntegrand a b c z) t := by
  refine (((((Meromorphic.Gamma (a + t)).comp_analyticAt
    (analyticAt_const.add analyticAt_id)).mul
    ((Meromorphic.Gamma (b + t)).comp_analyticAt (analyticAt_const.add analyticAt_id))).mul
    ((Meromorphic.Gamma (-t)).comp_analyticAt analyticAt_id.neg)).mul
    (((differentiable_one_div_Gamma.analyticAt (c + t)).comp
      (analyticAt_const.add analyticAt_id)).meromorphicAt)).mul (meromorphic_const_cpow (-z) t)

/-- Away from the pole families `-a - ℕ`, `-b - ℕ`, and `ℕ`, the Barnes integrand is analytic in
`t` for all parameters `a, b, c, z : ℂ`. -/
theorem analyticAt_mellinBarnesIntegrand (a b c z : ℂ) {t : ℂ}
    (ha : ∀ k : ℕ, t ≠ -a - k) (hb : ∀ k : ℕ, t ≠ -b - k) (ht : ∀ m : ℕ, t ≠ m) :
    AnalyticAt ℂ (mellinBarnesIntegrand a b c z) t := by
  refine (((((analyticAt_Gamma fun k h => ha k (by dsimp at h; linear_combination h)).comp
    (analyticAt_const.add analyticAt_id)).mul
    ((analyticAt_Gamma fun k h => hb k (by dsimp at h; linear_combination h)).comp
      (analyticAt_const.add analyticAt_id))).mul
    ((analyticAt_Gamma fun m h => ht m (by dsimp at h; linear_combination -h)).comp
      analyticAt_id.neg)).mul
    ((differentiable_one_div_Gamma.analyticAt (c + t)).comp
      (analyticAt_const.add analyticAt_id))).mul
    (analyticAt_id.const_cpow (Or.inr (by simpa using ht 0)))

/-- Simple-pole residue of `mellinBarnesIntegrand a b c z` at `t = -a - k` when `-a - k` avoids
both `-b - ℕ` and `ℕ`. -/
theorem residue_mellinBarnesIntegrand_neg_sub_natCast_left (a b c z : ℂ) (k : ℕ)
    (hb : ∀ m : ℕ, b - a - k ≠ -m) (ha : ∀ m : ℕ, a + k ≠ -m) :
    TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) (-a - k) =
      (-1) ^ k / (k ! : ℂ) * Gamma (b - a - k) * Gamma (a + k) *
        (Gamma (c - a - k))⁻¹ * (-z) ^ (-a - k) := by
  set t₀ : ℂ := -a - k
  have hadd_t₀ (w : ℂ) : w + t₀ = w - a - k := by dsimp [t₀]; ring
  have hneg_t₀ : -t₀ = a + k := by dsimp [t₀]; ring
  have hshift : Tendsto (fun t : ℂ => a + t) (𝓝[≠] t₀) (𝓝[≠] (-(k : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hat₀ : a + t₀ = -(k : ℂ) := by rw [hadd_t₀, sub_self, zero_sub]
      rw [← hat₀]
      exact ((continuous_const.add continuous_id).tendsto t₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [mem_compl_singleton_iff] at ht ⊢
      exact fun hEq => ht (by dsimp [t₀]; linear_combination hEq)
  have hG : Tendsto (fun t : ℂ => (t - t₀) * Gamma (a + t)) (𝓝[≠] t₀)
      (𝓝 ((-1) ^ k / (k ! : ℂ))) :=
    ((tendsto_add_natCast_mul_Gamma k).comp hshift).congr fun t => by
      dsimp [Function.comp_def, t₀]; ring
  have hrest_an : AnalyticAt ℂ
      (fun t : ℂ => Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t) t₀ :=
    ((((analyticAt_Gamma fun m h => hb m (by dsimp [t₀] at h; linear_combination h)).comp
      (analyticAt_const.add analyticAt_id)).mul
      ((analyticAt_Gamma fun m h => ha m (by dsimp [t₀] at h; linear_combination h)).comp
        analyticAt_id.neg)).mul
      ((differentiable_one_div_Gamma.analyticAt (c + t₀)).comp
        (analyticAt_const.add analyticAt_id))).mul
      (analyticAt_id.const_cpow (Or.inr
        fun h => ha 0 (by dsimp [t₀] at h; linear_combination -h)))
  have hrest : Tendsto (fun t : ℂ => Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t)
      (𝓝[≠] t₀) (𝓝 (Gamma (b - a - k) * Gamma (a + k) * (Gamma (c - a - k))⁻¹ * (-z) ^ t₀)) := by
    simpa only [hadd_t₀ b, hneg_t₀, hadd_t₀ c] using
      tendsto_nhdsWithin_of_tendsto_nhds (s := {t₀}ᶜ) hrest_an.continuousAt.tendsto
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul
    (meromorphicAt_mellinBarnesIntegrand a b c z t₀) ?_
  have hmul := hG.mul hrest
  simp only [← mul_assoc] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _; simp only [mellinBarnesIntegrand_def]; ring

/-- Simple-pole residue of `mellinBarnesIntegrand a b c z` at `t = -b - k` when `-b - k` avoids
both `-a - ℕ` and `ℕ`. -/
theorem residue_mellinBarnesIntegrand_neg_sub_natCast_right (a b c z : ℂ) (k : ℕ)
    (ha : ∀ m : ℕ, a - b - k ≠ -m) (hb : ∀ m : ℕ, b + k ≠ -m) :
    TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) (-b - k) =
      (-1) ^ k / (k ! : ℂ) * Gamma (a - b - k) * Gamma (b + k) *
        (Gamma (c - b - k))⁻¹ * (-z) ^ (-b - k) := by
  simp_rw [funext (mellinBarnesIntegrand_symm a b c z)]
  exact residue_mellinBarnesIntegrand_neg_sub_natCast_left b a c z k ha hb

/-! ### Section 3: Uniform Stirling bounds, vertical integrability, and `σ`-independence -/

/-- Uniform vertical-strip exponential decay bound for `mellinBarnesIntegrand` on bounded parameter
balls and compact sectorial subsets of `-z ∈ slitPlane`. -/
theorem exists_norm_mellinBarnesIntegrand_vertical_le {R r₁ r₂ δ : ℝ}
    (hR : 0 ≤ R) (hr₁ : 0 < r₁) (hδ : 0 < δ) :
    ∃ B Y₀ : ℝ, 0 ≤ B ∧ 1 ≤ Y₀ ∧ Integrable (fun y : ℝ => B * Real.exp (-δ * |y|)) ∧
      ∀ (a b c z : ℂ) (σ y : ℝ),
        ‖a‖ ≤ R → ‖b‖ ≤ R → ‖c‖ ≤ R → r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → |(-z).arg| ≤ π - 2 * δ →
        |σ| ≤ R → Y₀ ≤ |y| →
        ‖mellinBarnesIntegrand a b c z (σ + y * I)‖ ≤ B * Real.exp (-δ * |y|) := by
  obtain ⟨A, Y₀, hY₀, hG⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le (2 * R) (by positivity : 0 < δ / 4)
  let Mz : ℝ := max |Real.log r₁| |Real.log (max r₁ r₂)|
  have hint_exp : Integrable fun y : ℝ => Real.exp (-δ * |y|) := by
    simpa only [neg_mul] using TauCeti.integrable_exp_neg_mul_abs hδ
  refine ⟨Real.exp (4 * A + R * Mz), Y₀, (Real.exp_pos _).le, hY₀, hint_exp.const_mul _,
    fun a b c z σ y ha hb hc hzr₁ hzr₂ harg hσ hy => ?_⟩
  have hGshift {w : ℂ} (hw : ‖w‖ ≤ R) :
      ‖Gamma (w + (σ + y * I))‖ ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) ∧
        ‖(Gamma (w + (σ + y * I)))⁻¹‖ ≤ Real.exp (A + (π / 2 + δ / 4) * |y|) := by
    rw [← add_assoc]
    exact hG (w + σ) y
      (by
        simpa using ((abs_add_le w.re σ).trans
          (add_le_add ((abs_re_le_norm w).trans hw) hσ)).trans_eq (two_mul R).symm)
      (by simpa using ((abs_im_le_norm w).trans hw).trans (by linarith)) hy
  have hz_ne : -z ≠ 0 := neg_ne_zero.2 (norm_pos_iff.1 (hr₁.trans_le hzr₁))
  have hm1 : |Real.log r₁| ≤ Mz := le_max_left _ _
  have hlogz : |Real.log ‖-z‖| ≤ Mz := by
    rw [norm_neg]
    exact abs_le.2 ⟨by linarith [Real.log_le_log hr₁ hzr₁, neg_abs_le (Real.log r₁)],
      (Real.log_le_log (hr₁.trans_le hzr₁) (hzr₂.trans (le_max_right r₁ r₂))).trans
        ((le_abs_self _).trans (le_max_right _ _))⟩
  have hcpow : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ Real.exp (R * Mz + (π - 2 * δ) * |y|) := by
    rw [cpow_def_of_ne_zero hz_ne, norm_exp]
    refine Real.exp_le_exp.2 ?_
    simp only [mul_re, log_re, log_im, add_re, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    have h1 : Real.log ‖-z‖ * σ ≤ Mz * R :=
      (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul hlogz hσ (abs_nonneg _) ((abs_nonneg _).trans hlogz)))
    have h2 : -((-z).arg * y) ≤ (π - 2 * δ) * |y| :=
      (neg_le_abs _).trans ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_right harg (abs_nonneg y)))
    linarith
  have hGs : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) := by
    rw [neg_ofReal_add_mul_I]
    simpa only [abs_neg] using
      (hG ((-σ : ℝ) : ℂ) (-y) (by simpa using hσ.trans (by linarith))
        (by simp [hR]) (by simpa using hy)).1
  have hGa := (hGshift ha).1
  have hGb := (hGshift hb).1
  have hGc := (hGshift hc).2
  simp only [mellinBarnesIntegrand_def, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖ *
        ‖(Gamma (c + (σ + y * I)))⁻¹‖ * ‖(-z) ^ ((σ : ℂ) + y * I)‖
      ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (-π / 2 + δ / 4) * |y|) *
        Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (π / 2 + δ / 4) * |y|) *
        Real.exp (R * Mz + (π - 2 * δ) * |y|) := by gcongr
    _ = Real.exp (4 * A + R * Mz) * Real.exp (-δ * |y|) := by
        simp only [← Real.exp_add]; congr 1; ring

/-- Along any vertical line `Re t = σ` avoiding the poles `-Re a - ℕ`, `-Re b - ℕ`, and `ℕ`, the
Barnes integrand is vertically integrable for every `-z ∈ slitPlane`. -/
theorem verticalIntegrable_mellinBarnesIntegrand {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k) (hσ : ∀ m : ℕ, σ ≠ m)
    (hz : -z ∈ slitPlane) :
    VerticalIntegrable (mellinBarnesIntegrand a b c z) σ := by
  let R : ℝ := max (max ‖a‖ ‖b‖) (max ‖c‖ |σ|) + 1
  let δ : ℝ := (π - |(-z).arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz]
  obtain ⟨B, Y₀, _, _, hdom, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le (R := R)
    (r₂ := ‖z‖) (by positivity) (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz))) hδ
  have hcont : Continuous fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I) :=
    continuous_iff_continuousAt.2 fun y =>
      (analyticAt_mellinBarnesIntegrand a b c z
        (fun k h => ha k (by have hre := congrArg re h; simp at hre; linarith))
        (fun k h => hb k (by have hre := congrArg re h; simp at hre; linarith))
        (fun m h => hσ m (by have hre := congrArg re h; simp at hre; linarith))).continuousAt.comp
        (by fun_prop)
  have hout : IntegrableOn (fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I))
      (Icc (-Y₀) Y₀)ᶜ := by
    refine hdom.integrableOn.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with y hy
    exact htail a b c z σ y
      ((le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
      le_rfl le_rfl (by dsimp [δ]; linarith)
      ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
      (le_of_lt (not_le.1 (mt abs_le.1 (by simpa [mem_Icc] using hy))))
  rw [VerticalIntegrable, ← integrableOn_univ, ← union_compl_self (Icc (-Y₀) Y₀)]
  exact hcont.integrableOn_Icc.union hout

private theorem rectangle_mellinBarnes_eq {σ₁ σ₂ T : ℝ} (h12 : σ₁ < σ₂) (hT : 0 < T) :
    Rectangle ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I) = Icc σ₁ σ₂ ×ℂ Icc (-T) T := by
  simp [Rectangle, uIcc_of_le h12.le, uIcc_of_le (by linarith : -T ≤ T)]

private theorem im_mem_Ioo_of_leftPole {a b s : ℂ} {T : ℝ} (hTim : max |a.im| |b.im| < T)
    (h : (∃ k : ℕ, s = -a - k) ∨ (∃ k : ℕ, s = -b - k)) : s.im ∈ Ioo (-T) T :=
  abs_lt.1 (by rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp <;>
    linarith [le_max_left |a.im| |b.im|, le_max_right |a.im| |b.im|])

private theorem sum_windingNumber_rect_mellinBarnes {a b : ℂ} {σ₁ σ₂ T : ℝ} (f : ℂ → ℂ)
    (h12 : σ₁ < σ₂) (hTim : max |a.im| |b.im| < T)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k) :
    (∑ s ∈ mellinBarnesLeftPoles a b (σ₁ - 1),
      TauCeti.Contour.windingNumber (rectBoundary (σ₁ - T * I) (σ₂ + T * I)) 0 4 s *
        TauCeti.Contour.residue f s) =
      (∑ s ∈ mellinBarnesLeftPoles a b σ₁, TauCeti.Contour.residue f s) -
        ∑ s ∈ mellinBarnesLeftPoles a b σ₂, TauCeti.Contour.residue f s := by
  have hT_pos : 0 < T := (abs_nonneg a.im).trans_lt ((le_max_left _ _).trans_lt hTim)
  set zL : ℂ := (σ₁ : ℂ) - T * I
  set wR : ℂ := (σ₂ : ℂ) + T * I
  have hRect_eq : Rectangle zL wR = Icc σ₁ σ₂ ×ℂ Icc (-T) T :=
    rectangle_mellinBarnes_eq h12 hT_pos
  have hsub : mellinBarnesLeftPoles a b σ₂ ⊆ mellinBarnesLeftPoles a b σ₁ := fun s hs => by
    rw [mem_mellinBarnesLeftPoles] at hs ⊢; exact ⟨h12.trans hs.1, hs.2⟩
  have hP₁S : mellinBarnesLeftPoles a b σ₁ ⊆ mellinBarnesLeftPoles a b (σ₁ - 1) := fun s hs => by
    rw [mem_mellinBarnesLeftPoles] at hs ⊢; exact ⟨by linarith [hs.1], hs.2⟩
  have hne_line {s : ℂ} (h : (∃ k : ℕ, s = -a - k) ∨ (∃ k : ℕ, s = -b - k)) :
      s.re ≠ σ₁ ∧ s.re ≠ σ₂ := by
    rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨fun e => ha₁ k (by simp at e; linarith), fun e => ha₂ k (by simp at e; linarith)⟩
    · exact ⟨fun e => hb₁ k (by simp at e; linarith), fun e => hb₂ k (by simp at e; linarith)⟩
  rw [← Finset.sum_sdiff_eq_sub hsub]; symm
  refine (Finset.sum_congr rfl fun s hs => ?_).trans
    (Finset.sum_subset (Finset.sdiff_subset.trans hP₁S) fun s hsS hs_not => ?_)
  · rw [Finset.mem_sdiff, mem_mellinBarnesLeftPoles, mem_mellinBarnesLeftPoles] at hs
    have hlt2 : s.re < σ₂ := lt_of_le_of_ne (not_lt.1 fun h => hs.2 ⟨h, hs.1.2⟩) (hne_line hs.1.2).2
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_one
      (by simpa [zL, wR] using ⟨⟨hs.1.1, hlt2⟩, im_mem_Ioo_of_leftPole hTim hs.1.2⟩), one_mul]
  · have hs_poles := (mem_mellinBarnesLeftPoles.1 hsS).2
    have hs_out : s ∉ Rectangle zL wR := fun hsR => hs_not (by
      rw [hRect_eq] at hsR
      rw [Finset.mem_sdiff, mem_mellinBarnesLeftPoles, mem_mellinBarnesLeftPoles]
      exact ⟨⟨lt_of_le_of_ne hsR.1.1 (hne_line hs_poles).1.symm, hs_poles⟩,
        fun h => (lt_of_le_of_ne hsR.1.2 (hne_line hs_poles).2).not_gt h.1⟩)
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_zero hs_out, zero_mul]

private theorem frontier_rectangle_notMem_mellinBarnesLeftPoles {a b : ℂ} {σ₁ σ₂ T : ℝ}
    (hTim : max |a.im| |b.im| < T)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k) :
    ∀ t ∈ frontier (Rectangle ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I)),
      t ∉ (↑(mellinBarnesLeftPoles a b (σ₁ - 1)) : Set ℂ) := by
  intro t ht htS
  have hpoles := (mem_mellinBarnesLeftPoles.1 htS).2
  have htim := im_mem_Ioo_of_leftPole hTim hpoles
  rw [frontier_rectangle] at ht
  have htre : t.re = σ₁ ∨ t.re = σ₂ := by
    rcases ht with ⟨_, hmem⟩ | ⟨hmem, _⟩
    · have hmem' : t.im = -T ∨ t.im = T := by simpa using hmem
      rcases hmem' with h | h <;> linarith [htim.1, htim.2]
    · simpa using hmem
  rcases hpoles with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases htre with h1 | h2
  · exact ha₁ k (by simp at h1; linarith)
  · exact ha₂ k (by simp at h2; linarith)
  · exact hb₁ k (by simp at h1; linarith)
  · exact hb₂ k (by simp at h2; linarith)

private theorem rectBoundary_mellinBarnesIntegrand_eq {a b c z : ℂ} {σ₁ σ₂ T : ℝ}
    (h12 : σ₁ < σ₂) (hσ₂ : σ₂ < 0) (hTim : max |a.im| |b.im| < T)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k) :
    (∫ x : ℝ in σ₁..σ₂, mellinBarnesIntegrand a b c z (x - T * I)) -
      (∫ x : ℝ in σ₁..σ₂, mellinBarnesIntegrand a b c z (x + T * I)) +
      I * (∫ y : ℝ in (-T)..T, mellinBarnesIntegrand a b c z (σ₂ + y * I)) -
      I * (∫ y : ℝ in (-T)..T, mellinBarnesIntegrand a b c z (σ₁ + y * I)) =
    2 * (π : ℂ) * I *
      ((∑ s ∈ mellinBarnesLeftPoles a b σ₁,
          TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s) -
        ∑ s ∈ mellinBarnesLeftPoles a b σ₂,
          TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s) := by
  have hT_pos : 0 < T := (abs_nonneg a.im).trans_lt ((le_max_left _ _).trans_lt hTim)
  set g : ℂ → ℂ := mellinBarnesIntegrand a b c z
  set S : Finset ℂ := mellinBarnesLeftPoles a b (σ₁ - 1)
  let U : Set ℂ := {t : ℂ | σ₁ - 1 < t.re ∧ t.re < 0}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hg_diff : DifferentiableOn ℂ g (U \ (↑S : Set ℂ)) := fun t ht =>
    (analyticAt_mellinBarnesIntegrand a b c z
      (fun k hk => ht.2 (mem_mellinBarnesLeftPoles.2 ⟨ht.1.1, Or.inl ⟨k, hk⟩⟩))
      (fun k hk => ht.2 (mem_mellinBarnesLeftPoles.2 ⟨ht.1.1, Or.inr ⟨k, hk⟩⟩))
      (fun m hm => by
        have hre : t.re = m := by simp [hm]
        linarith [ht.1.2, m.cast_nonneg (α := ℝ)]))
      |>.differentiableAt.differentiableWithinAt
  set zL : ℂ := (σ₁ : ℂ) - T * I
  set wR : ℂ := (σ₂ : ℂ) + T * I
  have hRectU : Rectangle zL wR ⊆ U := fun t ht => by
    rw [rectangle_mellinBarnes_eq h12 hT_pos] at ht
    exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
  have hfr_notS := frontier_rectangle_notMem_mellinBarnesLeftPoles hTim ha₁ hb₁ ha₂ hb₂
  have hres := TauCeti.Contour.classicalResidueTheorem_nullHomologous hU hg_diff
    (fun s _ _ => meromorphicAt_mellinBarnesIntegrand a b c z s)
    (isPiecewiseC1On_rectBoundary zL wR)
    (fun t _ => hRectU (rectBoundary_mem_rectangle t)) (by simp)
    (fun t _ => hfr_notS _ (rectBoundary_mem_frontier t))
    (TauCeti.Contour.isNullHomologous_rectBoundary hRectU)
  rw [integral_rectBoundary (z := zL) (w := wR)
      (hg_diff.continuousOn.mono fun t ht =>
        ⟨hRectU ((isClosed_rectangle zL wR).closure_subset ht.1), hfr_notS t ht⟩),
    sum_windingNumber_rect_mellinBarnes g h12 hTim ha₁ hb₁ ha₂ hb₂] at hres
  simpa [zL, wR, sub_eq_add_neg, smul_eq_mul] using hres

private theorem tendsto_horizontal_mellinBarnesIntegrand_zero (a b c : ℂ) {z : ℂ} (σ₁ σ₂ : ℝ)
    (h12 : σ₁ < σ₂) (hz : -z ∈ slitPlane) {sgn : ℝ} (hsgn : |sgn| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, mellinBarnesIntegrand a b c z (x + (sgn * T) * I))
      atTop (𝓝 0) := by
  let R : ℝ := max (max ‖a‖ ‖b‖) (max ‖c‖ (max |σ₁| |σ₂|)) + 1
  let δ : ℝ := (π - |(-z).arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz]
  obtain ⟨B, Y₀, _, hY₀, _, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le (R := R)
    (r₂ := ‖z‖) (by positivity) (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz))) hδ
  have hexp : Tendsto (fun T : ℝ => B * Real.exp (-δ * T) * (σ₂ - σ₁)) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hδ))).const_mul B).mul_const (σ₂ - σ₁)
  refine tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp)
  filter_upwards [eventually_ge_atTop Y₀] with T hT
  have habs : |sgn * T| = T := by
    rw [abs_mul, hsgn, one_mul, abs_of_nonneg ((zero_lt_one.trans_le hY₀).le.trans hT)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * Real.exp (-δ * T))
    fun x hx => ?_).trans (by rw [abs_of_pos (sub_pos.2 h12)])
  rw [uIoc_of_le h12.le] at hx
  have hxR : |x| ≤ R := (abs_le_max_abs_abs hx.1.le hx.2).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
  simpa only [habs, ofReal_mul] using htail a b c z x (sgn * T)
    ((le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
    ((le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
    le_rfl le_rfl (by dsimp [δ]; linarith) hxR (habs.symm ▸ hT)

private theorem mellinBarnesSeparatingIntegral_eq_of_lt_of_lt_zero {a b : ℂ} (c : ℂ) {z : ℂ}
    {σ₁ σ₂ : ℝ} (h12 : σ₁ < σ₂) (hσ₂ : σ₂ < 0)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesSeparatingIntegral a b c z σ₁ = mellinBarnesSeparatingIntegral a b c z σ₂ := by
  set g : ℂ → ℂ := mellinBarnesIntegrand a b c z
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x - T * I)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, neg_one_mul] using
      tendsto_horizontal_mellinBarnesIntegrand_zero a b c σ₁ σ₂ h12 hz (sgn := -1) (by norm_num)
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + T * I)) atTop (𝓝 0) := by
    simpa [one_mul] using
      tendsto_horizontal_mellinBarnesIntegrand_zero a b c σ₁ σ₂ h12 hz (sgn := 1) (by norm_num)
  have hv₁ := intervalIntegral_tendsto_integral
    (verticalIntegrable_mellinBarnesIntegrand c ha₁ hb₁
      (fun m _ => by linarith [h12, hσ₂, m.cast_nonneg (α := ℝ)]) hz)
    tendsto_neg_atTop_atBot tendsto_id
  have hv₂ := intervalIntegral_tendsto_integral
    (verticalIntegrable_mellinBarnesIntegrand c ha₂ hb₂
      (fun m _ => by linarith [hσ₂, m.cast_nonneg (α := ℝ)]) hz)
    tendsto_neg_atTop_atBot tendsto_id
  let T₀ : ℝ := max |a.im| |b.im| + 1
  have heq := tendsto_nhds_unique ((((hbot.sub htop).add (hv₂.const_mul I)).sub
    (hv₁.const_mul I)).congr' (by
      filter_upwards [eventually_ge_atTop T₀] with T hT
      exact rectBoundary_mellinBarnesIntegrand_eq h12 hσ₂
        (by dsimp [T₀] at hT; linarith) ha₁ hb₁ ha₂ hb₂)) tendsto_const_nhds
  simp only [sub_zero, zero_add] at heq
  have hdiv := congrArg ((2 * (π : ℂ) * I)⁻¹ * ·) heq
  rw [inv_mul_cancel_left₀ two_pi_I_ne_zero] at hdiv
  have hI : (2 * (π : ℂ) * I)⁻¹ * I = (2 * π : ℂ)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ I_ne_zero, mul_one]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, hI] at hdiv
  rw [mellinBarnesSeparatingIntegral_def, mellinBarnesSeparatingIntegral_def]
  linear_combination -hdiv

/-- **Abscissa-independence of the separating-contour Mellin–Barnes functional.** For
`-z ∈ slitPlane`, `mellinBarnesSeparatingIntegral a b c z σ` takes the same value for every
negative abscissa `σ < 0` whose vertical line `Re t = σ` avoids the left-family poles
`-Re a - ℕ` and `-Re b - ℕ`. -/
theorem mellinBarnesSeparatingIntegral_eq_of_lt_zero {a b : ℂ} (c : ℂ) {z : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ < 0) (hσ₂ : σ₂ < 0)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesSeparatingIntegral a b c z σ₁ = mellinBarnesSeparatingIntegral a b c z σ₂ := by
  rcases lt_trichotomy σ₁ σ₂ with hlt | rfl | hgt
  · exact mellinBarnesSeparatingIntegral_eq_of_lt_of_lt_zero c hlt hσ₂ ha₁ hb₁ ha₂ hb₂ hz
  · rfl
  · exact (mellinBarnesSeparatingIntegral_eq_of_lt_of_lt_zero c hgt hσ₁ ha₂ hb₂ ha₁ hb₁ hz).symm

end Complex
