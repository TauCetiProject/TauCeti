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
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.Analysis.Contour.Residue.SimplePole
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

/-- No left-family pole lies strictly to the right of `Re t = σ` if and only if `-Re a ≤ σ` and
`-Re b ≤ σ`. -/
@[simp]
theorem mellinBarnesLeftPoles_eq_empty_iff {a b : ℂ} {σ : ℝ} :
    mellinBarnesLeftPoles a b σ = ∅ ↔ -a.re ≤ σ ∧ -b.re ≤ σ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨ha, hb⟩ t ht => ?_⟩
  · by_contra! ha
    exact h (-a) (mem_mellinBarnesLeftPoles.2 ⟨by simpa using ha, Or.inl ⟨0, by simp⟩⟩)
  · by_contra! hb
    exact h (-b) (mem_mellinBarnesLeftPoles.2 ⟨by simpa using hb, Or.inr ⟨0, by simp⟩⟩)
  · rcases mem_mellinBarnesLeftPoles.1 ht with ⟨hσ, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩
    · simp only [sub_re, neg_re, natCast_re] at hσ; linarith [ha, k.cast_nonneg (α := ℝ)]
    · simp only [sub_re, neg_re, natCast_re] at hσ; linarith [hb, k.cast_nonneg (α := ℝ)]

/-- `mellinBarnesLeftPoles a b` is antitone in the abscissa `σ`: shifting `σ` to the left only
adds left-family poles. -/
theorem mellinBarnesLeftPoles_antitone (a b : ℂ) : Antitone (mellinBarnesLeftPoles a b) :=
  fun _ _ h s hs => by
    rw [mem_mellinBarnesLeftPoles] at hs ⊢
    exact ⟨h.trans_lt hs.1, hs.2⟩

/-- A point lies in `mellinBarnesLeftPoles a b σ₁ \ mellinBarnesLeftPoles a b σ₂` if and only if
its real part lies in `(σ₁, σ₂]` and it belongs to one of the two left-pole families. -/
theorem mem_mellinBarnesLeftPoles_sdiff {a b : ℂ} {σ₁ σ₂ : ℝ} {s : ℂ} :
    s ∈ mellinBarnesLeftPoles a b σ₁ \ mellinBarnesLeftPoles a b σ₂ ↔
      s.re ∈ Ioc σ₁ σ₂ ∧ ((∃ k : ℕ, s = -a - k) ∨ (∃ k : ℕ, s = -b - k)) := by
  simp only [Finset.mem_sdiff, mem_mellinBarnesLeftPoles, mem_Ioc]
  exact ⟨fun ⟨⟨h1, hp⟩, h2⟩ => ⟨⟨h1, not_lt.1 fun h => h2 ⟨h, hp⟩⟩, hp⟩,
    fun ⟨⟨h1, h2⟩, hp⟩ => ⟨⟨h1, hp⟩, fun h => not_lt_of_ge h2 h.1⟩⟩

/-- Every pole in `mellinBarnesLeftPoles a b σ` lies in the horizontal strip
`|Im s| ≤ max |Im a| |Im b|`. -/
theorem abs_im_le_of_mem_mellinBarnesLeftPoles {a b : ℂ} {σ : ℝ} {s : ℂ}
    (hs : s ∈ mellinBarnesLeftPoles a b σ) : |s.im| ≤ max |a.im| |b.im| := by
  rcases (mem_mellinBarnesLeftPoles.1 hs).2 with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp

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
  rw [mellinBarnesSeparatingIntegral_def, mellinBarnesLeftPoles_eq_empty_iff.2 ⟨ha, hb⟩,
    Finset.sum_empty, add_zero]

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

/-- Joint analyticity of the uncurried Mellin–Barnes integrand in `(a, b, c, z, t)` away from
the pole families `-a - ℕ`, `-b - ℕ`, `ℕ` and the branch cut `-z ∉ slitPlane`. -/
theorem analyticAt_mellinBarnesIntegrand_uncurry {p : ℂ × ℂ × ℂ × ℂ} {t : ℂ}
    (ha : ∀ k : ℕ, p.1 + t ≠ -k) (hb : ∀ k : ℕ, p.2.1 + t ≠ -k) (ht : ∀ m : ℕ, -t ≠ -m)
    (hz : -p.2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ
      (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      (p, t) := by
  have hp1 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.1) (p, t) :=
    analyticAt_fst.comp analyticAt_fst
  have hp2 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.1) (p, t) :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hp3 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.2.1) (p, t) :=
    analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
  have hp4 : AnalyticAt ℂ (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ => x.1.2.2.2) (p, t) :=
    analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))
  simp_rw [mellinBarnesIntegrand_def]
  exact ((((((analyticAt_Gamma ha).comp_of_eq (hp1.add analyticAt_snd) rfl).mul
    ((analyticAt_Gamma hb).comp_of_eq (hp2.add analyticAt_snd) rfl)).mul
    ((analyticAt_Gamma ht).comp_of_eq analyticAt_snd.neg rfl)).mul
    ((differentiable_one_div_Gamma.analyticAt (p.2.2.1 + t)).comp_of_eq
      (hp3.add analyticAt_snd) rfl)).mul (hp4.neg.cpow analyticAt_snd hz))

/-- Joint analyticity of the uncurried Mellin–Barnes integrand along a vertical point `t = σ + i y`
when `Re a + σ`, `Re b + σ ∉ -ℕ`, `σ ∉ ℕ`, and `-z ∈ slitPlane`. -/
theorem analyticAt_mellinBarnesIntegrand_uncurry_vertical {p : ℂ × ℂ × ℂ × ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, p.1.re + σ ≠ -k) (hb : ∀ k : ℕ, p.2.1.re + σ ≠ -k)
    (hσ : ∀ m : ℕ, σ ≠ m) (hz : -p.2.2.2 ∈ slitPlane) (y : ℝ) :
    AnalyticAt ℂ
      (fun x : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mellinBarnesIntegrand x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)
      (p, (σ : ℂ) + y * I) :=
  analyticAt_mellinBarnesIntegrand_uncurry
    (fun k h => ha k (by have hre := congrArg re h; simp at hre; linarith))
    (fun k h => hb k (by have hre := congrArg re h; simp at hre; linarith))
    (fun m h => hσ m (by have hre := congrArg re h; simp at hre; linarith)) hz

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

private theorem exists_norm_mellinBarnesIntegrand_tail_le (a b c : ℂ) {z : ℂ}
    (hz : -z ∈ slitPlane) (σ₁ σ₂ : ℝ) :
    ∃ B Y₀ δ : ℝ, 0 ≤ B ∧ 1 ≤ Y₀ ∧ 0 < δ ∧
      Integrable (fun y : ℝ => B * Real.exp (-δ * |y|)) ∧
      ∀ x ∈ Icc σ₁ σ₂, ∀ y : ℝ, Y₀ ≤ |y| →
        ‖mellinBarnesIntegrand a b c z (x + y * I)‖ ≤ B * Real.exp (-δ * |y|) := by
  let R : ℝ := max (max ‖a‖ ‖b‖) (max ‖c‖ (max |σ₁| |σ₂|)) + 1
  let δ : ℝ := (π - |(-z).arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz]
  obtain ⟨B, Y₀, hB, hY₀, hdom, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le (R := R)
    (r₂ := ‖z‖) (by positivity) (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz))) hδ
  refine ⟨B, Y₀, δ, hB, hY₀, hδ, hdom, fun x hx y hy => ?_⟩
  have hxR : |x| ≤ R := (abs_le_max_abs_abs hx.1 hx.2).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
  exact htail a b c z x y
    ((le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
    ((le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
    le_rfl le_rfl (by dsimp [δ]; linarith) hxR hy

/-- Along any vertical line `Re t = σ` avoiding the poles `-Re a - ℕ`, `-Re b - ℕ`, and `ℕ`, the
Barnes integrand is vertically integrable for every `-z ∈ slitPlane`. -/
theorem verticalIntegrable_mellinBarnesIntegrand {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k) (hσ : ∀ m : ℕ, σ ≠ m)
    (hz : -z ∈ slitPlane) :
    VerticalIntegrable (mellinBarnesIntegrand a b c z) σ := by
  obtain ⟨B, Y₀, _, _, _, _, hdom, htail⟩ := exists_norm_mellinBarnesIntegrand_tail_le a b c hz σ σ
  have hcont : Continuous fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I) :=
    continuous_iff_continuousAt.2 fun y =>
      (analyticAt_mellinBarnesIntegrand_uncurry_vertical
        (p := (a, b, c, z)) ha hb hσ hz y).continuousAt.comp
        (f := fun y' : ℝ => ((a, b, c, z), (σ : ℂ) + y' * I)) (by fun_prop)
  have hout : IntegrableOn (fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I))
      (Icc (-Y₀) Y₀)ᶜ := by
    refine hdom.integrableOn.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with y hy
    exact htail σ (left_mem_Icc.2 le_rfl) y
      (le_of_lt (not_le.1 (mt abs_le.1 (by simpa [mem_Icc] using hy))))
  rw [VerticalIntegrable, ← integrableOn_univ, ← union_compl_self (Icc (-Y₀) Y₀)]
  exact hcont.integrableOn_Icc.union hout

private theorem mellinBarnesSeparatingIntegral_eq_of_lt_of_lt_zero {a b : ℂ} (c : ℂ) {z : ℂ}
    {σ₁ σ₂ : ℝ} (h12 : σ₁ < σ₂) (hσ₂ : σ₂ < 0)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesSeparatingIntegral a b c z σ₁ = mellinBarnesSeparatingIntegral a b c z σ₂ := by
  set g : ℂ → ℂ := mellinBarnesIntegrand a b c z
  set S : Finset ℂ := mellinBarnesLeftPoles a b σ₁ \ mellinBarnesLeftPoles a b σ₂
  obtain ⟨B₀, Y₀, δ, _, hY₀, hδ, _, htail⟩ :=
    exists_norm_mellinBarnesIntegrand_tail_le a b c hz σ₁ σ₂
  have hne_line {t : ℂ} (h : (∃ k : ℕ, t = -a - k) ∨ (∃ k : ℕ, t = -b - k)) :
      t.re ≠ σ₁ ∧ t.re ≠ σ₂ := by
    rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨fun e => ha₁ k (by simp at e; linarith), fun e => ha₂ k (by simp at e; linarith)⟩
    · exact ⟨fun e => hb₁ k (by simp at e; linarith), fun e => hb₂ k (by simp at e; linarith)⟩
  have hshift :=
    TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue_of_norm_le
      (f := g) (S := S) (B := fun T : ℝ => B₀ * Real.exp (-δ * T)) h12.le
    (fun t ht htS => analyticAt_mellinBarnesIntegrand a b c z
      (fun k hk => htS (mem_mellinBarnesLeftPoles_sdiff.2
        ⟨⟨lt_of_le_of_ne ht.1 (hne_line (Or.inl ⟨k, hk⟩)).1.symm, ht.2⟩, Or.inl ⟨k, hk⟩⟩))
      (fun k hk => htS (mem_mellinBarnesLeftPoles_sdiff.2
        ⟨⟨lt_of_le_of_ne ht.1 (hne_line (Or.inr ⟨k, hk⟩)).1.symm, ht.2⟩, Or.inr ⟨k, hk⟩⟩))
      (fun m hm => by
        have hre : t.re = m := by simp [hm]
        linarith [ht.2, hσ₂, m.cast_nonneg (α := ℝ)]))
    (fun s _ => meromorphicAt_mellinBarnesIntegrand a b c z s)
    (fun s hs => by
      obtain ⟨hs_re, hs_poles⟩ := mem_mellinBarnesLeftPoles_sdiff.1 hs
      exact ⟨hs_re.1, lt_of_le_of_ne hs_re.2 (hne_line hs_poles).2⟩)
    (verticalIntegrable_mellinBarnesIntegrand c ha₁ hb₁
      (fun m _ => by linarith [h12, hσ₂, m.cast_nonneg (α := ℝ)]) hz)
    (verticalIntegrable_mellinBarnesIntegrand c ha₂ hb₂
      (fun m _ => by linarith [hσ₂, m.cast_nonneg (α := ℝ)]) hz)
    (by
      simpa using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hδ))).const_mul B₀)
    (by
      filter_upwards [eventually_ge_atTop Y₀] with T hT x hx
      have hT0 : 0 ≤ T := (zero_lt_one.trans_le hY₀).le.trans hT
      have hpos : ‖g (x + T * I)‖ ≤ B₀ * Real.exp (-δ * T) := by
        simpa only [abs_of_nonneg hT0] using htail x hx T (by rwa [abs_of_nonneg hT0])
      have hneg : ‖g (x - T * I)‖ ≤ B₀ * Real.exp (-δ * T) := by
        have hsub : (x : ℂ) - T * I = (x : ℂ) + ((-T : ℝ) : ℂ) * I := by push_cast; ring
        simpa only [hsub, abs_neg, abs_of_nonneg hT0] using
          htail x hx (-T) (by rwa [abs_neg, abs_of_nonneg hT0])
      exact ⟨hpos, hneg⟩)
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  have hdiv := congrArg ((2 * π : ℂ)⁻¹ * ·) hshift
  dsimp only [S] at hdiv
  rw [mul_sub, inv_mul_cancel_left₀ h2pi, Finset.sum_sdiff_eq_sub
    (mellinBarnesLeftPoles_antitone a b h12.le)] at hdiv
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
