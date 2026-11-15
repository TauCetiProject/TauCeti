/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical

/-!
# Separating-contour Mellin–Barnes functional for the Gauss hypergeometric function

When `0 < Re a` and `0 < Re b`, Barnes's integral for the regularized Gauss hypergeometric function
`𝐅(a, b; c; z)` (DLMF 15.6.6) can be taken along a straight vertical line `Re t = σ` with
`-min (Re a) (Re b) < σ < 0`, which separates the left-hand poles `-a - ℕ`, `-b - ℕ` of
`Γ(a + t) Γ(b + t)` from the right-hand poles `ℕ` of `Γ(-t)`. Once `Re a ≤ 0` or `Re b ≤ 0`, no
straight vertical line separates the two families of poles: Barnes's separating contour instead
indents around the finitely many poles of `Γ(a + t) Γ(b + t)` that have crossed to the right of a
chosen abscissa `σ < 0` while avoiding the nonnegative integers.

Following DLMF §15.6(ii), we represent the separating-contour Mellin–Barnes functional at an
abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ` explicitly as the vertical-line integral at
`Re t = σ` plus the finite sum of residues `TauCeti.Contour.residue` of the Barnes integrand
`Γ(a + t) Γ(b + t) Γ(-t) / Γ(c + t) · (-z)^t` at the poles `t = -a - k`, `t = -b - k` with
`σ < Re t` (`Complex.mellinBarnesSeparating`).

Using the uniform vertical-strip Stirling asymptotic
(`TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`) for both `Γ` and `1 / Γ`, we show that on
`-z ∈ Complex.slitPlane` the Barnes integrand decays exponentially like
`exp (-(π - |arg (-z)|) |Im t|)` uniformly on compact parameter balls and bounded horizontal
strips. Applying the null-homologous residue theorem on rectangles (`[σ₁, σ₂] × [-T, T]`, `T → ∞`),
we prove that `mellinBarnesSeparating a b c z σ` is independent of the choice of admissible
abscissa `σ < 0`. Selecting a canonical admissible abscissa defines the `σ`-free continuation
`Complex.mellinBarnesContour a b c z`.

Locally around any parameter tuple `(a₀, b₀, c₀, z₀)` with `a₀, b₀ ∉ -ℕ` and `-z₀ ∈ slitPlane`,
the finite residue sum equals a sum of small circle integrals enclosing the poles above `σ` and
avoiding `ℕ`, handling both simple poles and the double poles that arise when `a - b ∈ ℤ`. Combined
with locally uniform tail convergence on vertical lines, this yields joint four-variable holomorphy
of `mellinBarnesContour` across `{a, b ∉ -ℕ} × ℂ × {-z ∈ slitPlane}`.

## Main definitions

* `Complex.mellinBarnesIntegrand`: the Barnes kernel
  `Γ(a + t) Γ(b + t) Γ(-t) (Γ(c + t))⁻¹ (-z) ^ t`.
* `Complex.mellinBarnesLeftPoles`: the finite set of poles `-a - k`, `-b - k` with `σ < Re t`.
* `Complex.mellinBarnesSeparating`: the vertical integral `(2π)⁻¹ ∫_{Re t = σ}` plus the residue
  sum over `mellinBarnesLeftPoles a b σ`.
* `Complex.mellinBarnesContour`: the canonical `σ`-independent separating-contour continuation.

## Main results

* `Complex.residue_mellinBarnesIntegrand_neg_sub_natCast_left`,
  `Complex.residue_mellinBarnesIntegrand_neg_sub_natCast_right`: closed-form simple-pole residues
  at `t = -a - k` and `t = -b - k`.
* `Complex.verticalIntegrable_mellinBarnesIntegrand`: integrability along any pole-free vertical
  line `Re t = σ` for `-z ∈ slitPlane`.
* `Complex.mellinBarnesSeparating_eq_of_lt_zero`: `σ`-independence for admissible `σ₁, σ₂ < 0`.
* `Complex.analyticOnNhd_mellinBarnesContour`: joint four-variable holomorphy on
  `{p | (∀ k : ℕ, a ≠ -k) ∧ (∀ k : ℕ, b ≠ -k) ∧ -z ∈ slitPlane}`.

## References

* NIST Digital Library of Mathematical Functions, §15.6(ii), equation 15.6.6.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5.
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
  · rcases h with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  · rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · refine Or.inl ⟨k, ?_, rfl⟩
      have hk : (k : ℝ) < -a.re - σ := by simp only [sub_re, neg_re, natCast_re] at hσ; linarith
      exact_mod_cast hk.trans (Nat.lt_floor_add_one (-a.re - σ))
    · refine Or.inr ⟨k, ?_, rfl⟩
      have hk : (k : ℝ) < -b.re - σ := by simp only [sub_re, neg_re, natCast_re] at hσ; linarith
      exact_mod_cast hk.trans (Nat.lt_floor_add_one (-b.re - σ))

/-- Symmetry of `mellinBarnesLeftPoles` in `a` and `b`. -/
theorem mellinBarnesLeftPoles_symm (a b : ℂ) (σ : ℝ) :
    mellinBarnesLeftPoles a b σ = mellinBarnesLeftPoles b a σ := by
  ext t
  simp [or_comm]

/-- When `-Re a ≤ σ` and `-Re b ≤ σ`, no left-family pole lies strictly to the right of
`Re t = σ`. -/
@[simp]
theorem mellinBarnesLeftPoles_eq_empty_of_neg_re_le {a b : ℂ} {σ : ℝ}
    (ha : -a.re ≤ σ) (hb : -b.re ≤ σ) :
    mellinBarnesLeftPoles a b σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [mem_mellinBarnesLeftPoles] at ht
  rcases ht with ⟨hσ, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩ <;>
    · simp only [sub_re, neg_re, natCast_re] at hσ
      linarith [k.cast_nonneg (α := ℝ)]

/-- The separating-contour Mellin–Barnes functional at abscissa `σ`: the vertical-line integral
`(2π)⁻¹ ∫_{Re t = σ}` plus the sum of residues at the left-family poles strictly to the right of
`Re t = σ`. -/
def mellinBarnesSeparating (a b c z : ℂ) (σ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * (∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I)) +
    ∑ s ∈ mellinBarnesLeftPoles a b σ, TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s

/-- Defining formula for `mellinBarnesSeparating`. -/
theorem mellinBarnesSeparating_def (a b c z : ℂ) (σ : ℝ) :
    mellinBarnesSeparating a b c z σ =
      (2 * π : ℂ)⁻¹ * (∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I)) +
        ∑ s ∈ mellinBarnesLeftPoles a b σ,
          TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) s := (rfl)

/-- Symmetry of `mellinBarnesSeparating` in `a` and `b`. -/
theorem mellinBarnesSeparating_symm (a b c z : ℂ) (σ : ℝ) :
    mellinBarnesSeparating a b c z σ = mellinBarnesSeparating b a c z σ := by
  rw [mellinBarnesSeparating_def, mellinBarnesSeparating_def, mellinBarnesLeftPoles_symm a b σ]
  simp_rw [funext (mellinBarnesIntegrand_symm a b c z)]

/-- When `-Re a ≤ σ` and `-Re b ≤ σ`, the separating-contour functional reduces to the straight
vertical-line integral along `Re t = σ`. -/
theorem mellinBarnesSeparating_of_neg_re_le {a b : ℂ} (c z : ℂ) {σ : ℝ}
    (ha : -a.re ≤ σ) (hb : -b.re ≤ σ) :
    mellinBarnesSeparating a b c z σ =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, mellinBarnesIntegrand a b c z (σ + y * I) := by
  simp [mellinBarnesSeparating_def, mellinBarnesLeftPoles_eq_empty_of_neg_re_le ha hb]

/-! ### Section 2: Meromorphy, regular points, and simple-pole residues -/

private theorem meromorphicAt_Gamma_all (s : ℂ) : MeromorphicAt Gamma s :=
  ((differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv).congr
    (Eventually.of_forall fun w => inv_inv (Gamma w))

private theorem analyticAt_const_cpow_of_ne_zero (w : ℂ) {t₀ : ℂ} (ht₀ : t₀ ≠ 0) :
    AnalyticAt ℂ (fun t : ℂ => w ^ t) t₀ := by
  by_cases hw : w = 0
  · subst hw
    refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [isOpen_ne.mem_nhds ht₀] with t ht
    exact (zero_cpow ht).symm
  · refine (analyticAt_cexp.comp ((analyticAt_const (v := Complex.log w)).mul analyticAt_id)).congr
      (Eventually.of_forall fun t => (cpow_def_of_ne_zero hw t).symm)

private theorem meromorphicAt_const_cpow (w t₀ : ℂ) :
    MeromorphicAt (fun t : ℂ => w ^ t) t₀ := by
  by_cases hw : w = 0
  · subst hw
    refine (analyticAt_const (v := (0 : ℂ))).meromorphicAt.congr ?_
    by_cases ht₀ : t₀ = 0
    · subst ht₀
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (zero_cpow ht).symm
    · filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht₀)] with t ht
      exact (zero_cpow ht).symm
  · exact (analyticAt_cexp.comp
      ((analyticAt_const (v := Complex.log w)).mul analyticAt_id)).meromorphicAt.congr
      (Eventually.of_forall fun t => (cpow_def_of_ne_zero hw t).symm)

/-- The Barnes integrand `t ↦ mellinBarnesIntegrand a b c z t` is meromorphic at every point of
the complex plane, for all parameters `a, b, c, z : ℂ`. -/
theorem meromorphicAt_mellinBarnesIntegrand (a b c z t : ℂ) :
    MeromorphicAt (mellinBarnesIntegrand a b c z) t := by
  have ha : MeromorphicAt (fun w : ℂ => Gamma (a + w)) t :=
    (meromorphicAt_Gamma_all (a + t)).comp_analyticAt (analyticAt_const.add analyticAt_id)
  have hb : MeromorphicAt (fun w : ℂ => Gamma (b + w)) t :=
    (meromorphicAt_Gamma_all (b + t)).comp_analyticAt (analyticAt_const.add analyticAt_id)
  have hneg : MeromorphicAt (fun w : ℂ => Gamma (-w)) t :=
    (meromorphicAt_Gamma_all (-t)).comp_analyticAt analyticAt_id.neg
  have hc : MeromorphicAt (fun w : ℂ => (Gamma (c + w))⁻¹) t :=
    ((differentiable_one_div_Gamma.analyticAt (c + t)).comp
      (analyticAt_const.add analyticAt_id)).meromorphicAt
  exact (((ha.mul hb).mul hneg).mul hc).mul (meromorphicAt_const_cpow (-z) t)

/-- Away from the pole families `-a - ℕ`, `-b - ℕ`, and `ℕ`, the Barnes integrand is analytic in
`t` for all parameters `a, b, c, z : ℂ`. -/
theorem analyticAt_mellinBarnesIntegrand (a b c z : ℂ) {t : ℂ}
    (ha : ∀ k : ℕ, t ≠ -a - k) (hb : ∀ k : ℕ, t ≠ -b - k) (ht : ∀ m : ℕ, t ≠ m) :
    AnalyticAt ℂ (mellinBarnesIntegrand a b c z) t := by
  have ha' : AnalyticAt ℂ (fun w : ℂ => Gamma (a + w)) t :=
    (analyticAt_Gamma fun k h => ha k (by linear_combination h)).comp
      (analyticAt_const.add analyticAt_id)
  have hb' : AnalyticAt ℂ (fun w : ℂ => Gamma (b + w)) t :=
    (analyticAt_Gamma fun k h => hb k (by linear_combination h)).comp
      (analyticAt_const.add analyticAt_id)
  have ht' : AnalyticAt ℂ (fun w : ℂ => Gamma (-w)) t :=
    (analyticAt_Gamma fun m h => ht m (by linear_combination -h)).comp analyticAt_id.neg
  have hc' : AnalyticAt ℂ (fun w : ℂ => (Gamma (c + w))⁻¹) t :=
    (differentiable_one_div_Gamma.analyticAt (c + t)).comp (analyticAt_const.add analyticAt_id)
  have hz' : AnalyticAt ℂ (fun w : ℂ => (-z) ^ w) t :=
    analyticAt_const_cpow_of_ne_zero (-z) (by simpa using ht 0)
  exact (((ha'.mul hb').mul ht').mul hc').mul hz'

/-- Simple-pole residue of `mellinBarnesIntegrand a b c z` at `t = -a - k` when `-a - k` avoids
both `-b - ℕ` and `ℕ`. -/
theorem residue_mellinBarnesIntegrand_neg_sub_natCast_left (a b c z : ℂ) (k : ℕ)
    (hb : ∀ m : ℕ, b - a - k ≠ -m) (ha : ∀ m : ℕ, a + k ≠ -m) :
    TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) (-a - k) =
      (-1) ^ k / (k ! : ℂ) * Gamma (b - a - k) * Gamma (a + k) *
        (Gamma (c - a - k))⁻¹ * (-z) ^ (-a - k) := by
  set t₀ : ℂ := -a - k
  have hshift : Tendsto (fun t : ℂ => a + t) (𝓝[≠] t₀) (𝓝[≠] (-(k : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℂ => a + t) (𝓝 t₀) (𝓝 (a + t₀)) :=
        ((continuous_const (y := a)).add continuous_id).tendsto t₀
      have h0 : a + t₀ = -(k : ℂ) := by dsimp [t₀]; ring
      simpa only [h0] using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [mem_compl_singleton_iff] at ht ⊢
      intro hEq
      exact ht (by dsimp [t₀]; linear_combination hEq)
  have hG : Tendsto (fun t : ℂ => (t - t₀) * Gamma (a + t)) (𝓝[≠] t₀)
      (𝓝 ((-1) ^ k / (k ! : ℂ))) := by
    refine ((tendsto_add_natCast_mul_Gamma k).comp hshift).congr fun t => ?_
    dsimp [Function.comp_def, t₀]
    ring
  have hrest_an : AnalyticAt ℂ
      (fun t : ℂ => Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t) t₀ := by
    have hb' : AnalyticAt ℂ (fun t : ℂ => Gamma (b + t)) t₀ :=
      (analyticAt_Gamma fun m h => hb m (by dsimp [t₀] at h; linear_combination h)).comp
        (analyticAt_const.add analyticAt_id)
    have ht' : AnalyticAt ℂ (fun t : ℂ => Gamma (-t)) t₀ :=
      (analyticAt_Gamma fun m h => ha m (by dsimp [t₀] at h; linear_combination h)).comp
        analyticAt_id.neg
    have hc' : AnalyticAt ℂ (fun t : ℂ => (Gamma (c + t))⁻¹) t₀ :=
      (differentiable_one_div_Gamma.analyticAt (c + t₀)).comp (analyticAt_const.add analyticAt_id)
    have hz' : AnalyticAt ℂ (fun t : ℂ => (-z) ^ t) t₀ :=
      analyticAt_const_cpow_of_ne_zero (-z) fun h =>
        ha 0 (by dsimp [t₀] at h; linear_combination -h)
    exact ((hb'.mul ht').mul hc').mul hz'
  have hrest : Tendsto (fun t : ℂ => Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (-z) ^ t)
      (𝓝[≠] t₀) (𝓝 (Gamma (b - a - k) * Gamma (a + k) * (Gamma (c - a - k))⁻¹ * (-z) ^ t₀)) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := {t₀}ᶜ) hrest_an.continuousAt.tendsto
    have hb0 : b + t₀ = b - a - k := by dsimp [t₀]; ring
    have ht0 : -t₀ = a + k := by dsimp [t₀]; ring
    have hc0 : c + t₀ = c - a - k := by dsimp [t₀]; ring
    simpa only [hb0, ht0, hc0] using h
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul
    (meromorphicAt_mellinBarnesIntegrand a b c z t₀) ?_
  have hmul := hG.mul hrest
  have hassoc : (-1 : ℂ) ^ k / (k ! : ℂ) *
      (Gamma (b - a - k) * Gamma (a + k) * (Gamma (c - a - k))⁻¹ * (-z) ^ t₀) =
      (-1) ^ k / (k ! : ℂ) * Gamma (b - a - k) * Gamma (a + k) *
        (Gamma (c - a - k))⁻¹ * (-z) ^ t₀ := by ring
  rw [hassoc] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  simp only [mellinBarnesIntegrand_def]
  ring

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

private theorem abs_arg_lt_pi_of_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : |w.arg| < π :=
  abs_lt.2 ⟨neg_pi_lt_arg w, lt_of_le_of_ne (arg_le_pi w) (slitPlane_arg_ne_pi hw)⟩

private theorem log_le_mul_sub_log {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log x ≤ ε * x - Real.log ε := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hε hx)
  rw [Real.log_mul hε.ne' hx.ne'] at h
  linarith

private theorem abs_sub_half_mul_log_le {R ε : ℝ} {s : ℂ} {y : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hs_re : s.re ∈ Icc (-2 * R) (2 * R))
    (hs_im_ge : 1 ≤ |s.im|) (hs_im_sub : |(|s.im| - |y|)| ≤ R) :
    abs ((s.re - 1 / 2) * Real.log |s.im|) ≤
      ε * |y| + ε * R + (2 * R + 1) * |Real.log (ε / (2 * R + 1))| := by
  let η : ℝ := ε / (2 * R + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hlog_ge : 0 ≤ Real.log |s.im| := Real.log_nonneg hs_im_ge
  have hsre : |s.re - 1 / 2| ≤ 2 * R + 1 :=
    abs_le.2 ⟨by linarith [hs_re.1], by linarith [hs_re.2]⟩
  have hsim_le : η * |s.im| - Real.log η ≤ η * (|y| + R) + |Real.log η| := by
    have h1 : η * |s.im| ≤ η * (|y| + R) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 hs_im_sub).2]) hη.le
    linarith [neg_le_abs (Real.log η)]
  rw [abs_mul, abs_of_nonneg hlog_ge]
  calc |s.re - 1 / 2| * Real.log |s.im|
      ≤ (2 * R + 1) * (η * |s.im| - Real.log η) :=
        mul_le_mul hsre (log_le_mul_sub_log hη (zero_lt_one.trans_le hs_im_ge)) hlog_ge
          (by positivity)
    _ ≤ (2 * R + 1) * (η * (|y| + R) + |Real.log η|) :=
        mul_le_mul_of_nonneg_left hsim_le (by positivity)
    _ = ε * |y| + ε * R + (2 * R + 1) * |Real.log η| := by
        have hmul : (2 * R + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
        linear_combination (|y| + R) * hmul

private theorem exists_norm_Gamma_shift_vertical_le (R : ℝ) {ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ (w : ℂ) (σ y : ℝ), ‖w‖ ≤ R → |σ| ≤ R → Y₀ ≤ |y| →
      ‖Gamma (w + (σ + y * I))‖ ≤ Real.exp (A + (-π / 2 + ε) * |y|) ∧
        ‖(Gamma (w + (σ + y * I)))⁻¹‖ ≤ Real.exp (A + (π / 2 + ε) * |y|) := by
  obtain ⟨C, T, hST⟩ := TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le (-2 * R) (2 * R)
  let η : ℝ := ε / (2 * R + 1)
  let Y₀ : ℝ := max 1 (max T 1 + R + 1)
  let A : ℝ := |C| + |Real.log (2 * π) / 2| + π * R / 2 + ε * R + (2 * R + 1) * |Real.log η|
  refine ⟨A, Y₀, le_max_left _ _, fun w σ y hw hσ hy => ?_⟩
  set s : ℂ := w + (σ + y * I)
  have hs_re : s.re ∈ Icc (-2 * R) (2 * R) := by
    have hw_re : |w.re| ≤ R := (abs_re_le_norm w).trans hw
    simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, mem_Icc]
    exact ⟨by linarith [(abs_le.1 hw_re).1, (abs_le.1 hσ).1],
      by linarith [(abs_le.1 hw_re).2, (abs_le.1 hσ).2]⟩
  have hs_im_sub : |(|s.im| - |y|)| ≤ R := by
    have hsim : s.im = w.im + y := by simp [s]
    rw [hsim]
    exact (abs_abs_sub_abs_le_abs_sub (w.im + y) y).trans
      (by simpa using (abs_im_le_norm w).trans hw)
  have hyT : max T 1 + R + 1 ≤ |y| := (le_max_right _ _).trans hy
  have hs_im_ge : 1 ≤ |s.im| := by linarith [(abs_le.1 hs_im_sub).1, le_max_right T 1]
  have hmain := hST s hs_re (by linarith [(abs_le.1 hs_im_sub).1, le_max_left T 1])
  have hdiv : C / |s.im| ≤ |C| := (le_abs_self _).trans (by
    rw [abs_div, abs_of_pos (zero_lt_one.trans_le hs_im_ge)]
    exact div_le_self (abs_nonneg C) hs_im_ge)
  have hlog_le := abs_sub_half_mul_log_le hR hε hs_re hs_im_ge hs_im_sub
  have hpi : |π * |s.im| / 2 - π * |y| / 2| ≤ π * R / 2 := by
    have heq : π * |s.im| / 2 - π * |y| / 2 = (π / 2) * (|s.im| - |y|) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hs_im_sub (by positivity : 0 ≤ π / 2)]
  have hpos : 0 < ‖Gamma s‖ := norm_pos_iff.2 (Gamma_ne_zero fun n hn => by
    have him0 : s.im = 0 := by simp [hn]
    rw [him0, abs_zero] at hs_im_ge
    linarith)
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_log hpos]
    refine Real.exp_le_exp.2 ?_
    dsimp only [A, η]
    linarith [(abs_le.1 hmain).2, (abs_le.1 hlog_le).2, (abs_le.1 hpi).1,
      le_abs_self (Real.log (2 * π) / 2)]
  · rw [norm_inv, ← Real.exp_log hpos, ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    dsimp only [A, η]
    linarith [(abs_le.1 hmain).1, (abs_le.1 hlog_le).1, (abs_le.1 hpi).2,
      neg_le_abs (Real.log (2 * π) / 2)]

private theorem exists_norm_mellinBarnesIntegrand_vertical_le (R : ℝ) {r₁ r₂ δ : ℝ}
    (hR : 0 ≤ R) (hr₁ : 0 < r₁) (hδ : 0 < δ) :
    ∃ B Y₀ : ℝ, 0 ≤ B ∧ 1 ≤ Y₀ ∧
      ∀ (a b c z : ℂ) (σ y : ℝ),
        ‖a‖ ≤ R → ‖b‖ ≤ R → ‖c‖ ≤ R → r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → |(-z).arg| ≤ π - 2 * δ →
        |σ| ≤ R → Y₀ ≤ |y| →
        ‖mellinBarnesIntegrand a b c z (σ + y * I)‖ ≤ B * Real.exp (-δ * |y|) := by
  obtain ⟨A, Y₀, hY₀, hG⟩ := exists_norm_Gamma_shift_vertical_le R hR (by positivity : 0 < δ / 4)
  let Mz : ℝ := max |Real.log r₁| |Real.log (max r₁ r₂)|
  refine ⟨Real.exp (4 * A + R * Mz), Y₀, (Real.exp_pos _).le, hY₀,
    fun a b c z σ y ha hb hc hzr₁ hzr₂ harg hσ hy => ?_⟩
  have hz_ne : -z ≠ 0 := neg_ne_zero.2 (norm_pos_iff.1 (hr₁.trans_le hzr₁))
  have hlogz : |Real.log ‖-z‖| ≤ Mz := by
    rw [norm_neg]
    have h1 : -Mz ≤ Real.log ‖z‖ := by
      linarith [Real.log_le_log hr₁ hzr₁, neg_abs_le (Real.log r₁),
        le_max_left |Real.log r₁| |Real.log (max r₁ r₂)|]
    have h2 : Real.log ‖z‖ ≤ Mz :=
      (Real.log_le_log (hr₁.trans_le hzr₁) (hzr₂.trans (le_max_right r₁ r₂))).trans
        ((le_abs_self _).trans (le_max_right _ _))
    exact abs_le.2 ⟨h1, h2⟩
  have hcpow : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ Real.exp (R * Mz + (π - 2 * δ) * |y|) := by
    rw [cpow_def_of_ne_zero hz_ne, norm_exp]
    refine Real.exp_le_exp.2 ?_
    have hre : (Complex.log (-z) * ((σ : ℂ) + y * I)).re =
        Real.log ‖-z‖ * σ - (-z).arg * y := by simp [mul_re, log_re, log_im]
    rw [hre]
    have h1 : Real.log ‖-z‖ * σ ≤ R * Mz := by
      calc Real.log ‖-z‖ * σ ≤ |Real.log ‖-z‖ * σ| := le_abs_self _
        _ = |Real.log ‖-z‖| * |σ| := abs_mul _ _
        _ ≤ Mz * R := mul_le_mul hlogz hσ (abs_nonneg _) ((abs_nonneg _).trans hlogz)
        _ = R * Mz := mul_comm _ _
    have h2 : -((-z).arg * y) ≤ (π - 2 * δ) * |y| := by
      calc -((-z).arg * y) ≤ |(-z).arg * y| := neg_le_abs _
        _ = |(-z).arg| * |y| := abs_mul _ _
        _ ≤ (π - 2 * δ) * |y| := mul_le_mul_of_nonneg_right harg (abs_nonneg y)
    linarith
  have hGs : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) := by
    have h0 := (hG 0 (-σ) (-y) (by simpa using hR) (by simpa using hσ) (by simpa using hy)).1
    have hneg : -((σ : ℂ) + y * I) = (0 : ℂ) + ((-σ : ℝ) + (-y : ℝ) * I) := by push_cast; ring
    rw [hneg]
    simpa only [abs_neg] using h0
  rw [mellinBarnesIntegrand_def, norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖ *
        ‖(Gamma (c + (σ + y * I)))⁻¹‖ * ‖(-z) ^ ((σ : ℂ) + y * I)‖
      ≤ Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (-π / 2 + δ / 4) * |y|) *
          Real.exp (A + (-π / 2 + δ / 4) * |y|) * Real.exp (A + (π / 2 + δ / 4) * |y|) *
          Real.exp (R * Mz + (π - 2 * δ) * |y|) :=
        mul_le_mul (mul_le_mul (mul_le_mul
          (mul_le_mul (hG a σ y ha hσ hy).1 (hG b σ y hb hσ hy).1 (norm_nonneg _) (by positivity))
          hGs (norm_nonneg _) (by positivity)) (hG c σ y hc hσ hy).2 (norm_nonneg _)
          (by positivity)) hcpow (norm_nonneg _) (by positivity)
    _ = Real.exp (4 * A + R * Mz) * Real.exp (-δ * |y|) := by
        simp only [← Real.exp_add]; congr 1; ring

private theorem integrable_exp_neg_mul_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable fun y : ℝ => Real.exp (-δ * |y|) := by
  have hright : IntegrableOn (fun y : ℝ => Real.exp (-δ * |y|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hδ) 0).congr_fun
      (fun y hy => by rw [abs_of_pos hy]) measurableSet_Ioi
  have hleft : IntegrableOn (fun y : ℝ => Real.exp (-δ * |y|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic hδ 0).congr_fun
      (fun y (hy : y ≤ 0) => by rw [abs_of_nonpos hy]; ring_nf) measurableSet_Iic
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hleft.union hright

/-- Along any vertical line `Re t = σ` avoiding the poles `-Re a - ℕ`, `-Re b - ℕ`, and `ℕ`, the
Barnes integrand is integrable for every `-z ∈ slitPlane`. -/
theorem verticalIntegrable_mellinBarnesIntegrand {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k) (hσ : ∀ m : ℕ, σ ≠ m)
    (hz : -z ∈ slitPlane) :
    Integrable fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I) := by
  let R : ℝ := max (max ‖a‖ ‖b‖) (max ‖c‖ |σ|) + 1
  let δ : ℝ := (π - |(-z).arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz]
  obtain ⟨B, Y₀, _, _, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le R (by positivity)
    (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz))) hδ
  have hcont : Continuous fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine (analyticAt_mellinBarnesIntegrand a b c z (fun k h => ?_) (fun k h => ?_)
      (fun m h => ?_)).continuousAt.comp (by fun_prop)
    · exact ha k (by have hre := congrArg re h; simp at hre; linarith)
    · exact hb k (by have hre := congrArg re h; simp at hre; linarith)
    · exact hσ m (by have hre := congrArg re h; simp at hre; linarith)
  have hout : IntegrableOn (fun y : ℝ => mellinBarnesIntegrand a b c z (σ + y * I))
      (Icc (-Y₀) Y₀)ᶜ := by
    refine ((integrable_exp_neg_mul_abs hδ).const_mul B).integrableOn.mono'
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with y hy
    have hyY : Y₀ ≤ |y| := le_of_lt (not_le.1 (mt abs_le.1 (by simpa [mem_Icc] using hy)))
    exact htail a b c z σ y
      ((le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
      le_rfl le_rfl (by dsimp [δ]; linarith)
      ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith))) hyY
  rw [← integrableOn_univ, ← union_compl_self (Icc (-Y₀) Y₀)]
  exact hcont.integrableOn_Icc.union hout

private theorem sum_windingNumber_rect_mellinBarnes {a b : ℂ} {σ₁ σ₂ T : ℝ} (f : ℂ → ℂ)
    (h12 : σ₁ < σ₂) (hT_pos : 0 < T) (hTim : max |a.im| |b.im| < T)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k) :
    (∑ s ∈ mellinBarnesLeftPoles a b (σ₁ - 1),
      TauCeti.Contour.windingNumber (rectBoundary (σ₁ - T * I) (σ₂ + T * I)) 0 4 s *
        TauCeti.Contour.residue f s) =
      (∑ s ∈ mellinBarnesLeftPoles a b σ₁, TauCeti.Contour.residue f s) -
        ∑ s ∈ mellinBarnesLeftPoles a b σ₂, TauCeti.Contour.residue f s := by
  set zL : ℂ := (σ₁ : ℂ) - T * I
  set wR : ℂ := (σ₂ : ℂ) + T * I
  have hRect_eq : Rectangle zL wR = Icc σ₁ σ₂ ×ℂ Icc (-T) T := by
    simp [Rectangle, zL, wR, uIcc_of_le h12.le, uIcc_of_le (by linarith : -T ≤ T)]
  have hsub : mellinBarnesLeftPoles a b σ₂ ⊆ mellinBarnesLeftPoles a b σ₁ := fun s hs => by
    rw [mem_mellinBarnesLeftPoles] at hs ⊢; exact ⟨h12.trans hs.1, hs.2⟩
  have hP₁S : mellinBarnesLeftPoles a b σ₁ ⊆ mellinBarnesLeftPoles a b (σ₁ - 1) := fun s hs => by
    rw [mem_mellinBarnesLeftPoles] at hs ⊢; exact ⟨by linarith [hs.1], hs.2⟩
  have him_in : ∀ {s : ℂ}, ((∃ k : ℕ, s = -a - k) ∨ (∃ k : ℕ, s = -b - k)) →
      s.im ∈ Ioo (-T) T := fun h => abs_lt.1 (by
    rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp <;>
      linarith [le_max_left |a.im| |b.im|, le_max_right |a.im| |b.im|])
  have hne_line : ∀ {s : ℂ}, ((∃ k : ℕ, s = -a - k) ∨ (∃ k : ℕ, s = -b - k)) →
      s.re ≠ σ₁ ∧ s.re ≠ σ₂ := fun h => by
    rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨fun e => ha₁ k (by simp at e; linarith), fun e => ha₂ k (by simp at e; linarith)⟩
    · exact ⟨fun e => hb₁ k (by simp at e; linarith), fun e => hb₂ k (by simp at e; linarith)⟩
  rw [← Finset.sum_sdiff_eq_sub hsub]
  symm
  refine (Finset.sum_congr rfl fun s hs => ?_).trans
    (Finset.sum_subset (Finset.sdiff_subset.trans hP₁S) fun s hsS hs_not => ?_)
  · rw [Finset.mem_sdiff, mem_mellinBarnesLeftPoles, mem_mellinBarnesLeftPoles] at hs
    have hlt2 : s.re < σ₂ := lt_of_le_of_ne (not_lt.1 fun h => hs.2 ⟨h, hs.1.2⟩) (hne_line hs.1.2).2
    have hin : s ∈ Ioo zL.re wR.re ×ℂ Ioo zL.im wR.im := by
      simpa [zL, wR] using ⟨⟨hs.1.1, hlt2⟩, him_in hs.1.2⟩
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_one hin, one_mul]
  · have hs_poles := (mem_mellinBarnesLeftPoles.1 hsS).2
    have hs_out : s ∉ Rectangle zL wR := by
      rw [hRect_eq]
      intro hsR
      apply hs_not
      rw [Finset.mem_sdiff, mem_mellinBarnesLeftPoles, mem_mellinBarnesLeftPoles]
      exact ⟨⟨lt_of_le_of_ne hsR.1.1 (hne_line hs_poles).1.symm, hs_poles⟩,
        fun h => (lt_of_le_of_ne hsR.1.2 (hne_line hs_poles).2).not_gt h.1⟩
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_zero hs_out, zero_mul]

private theorem frontier_rectangle_notMem_mellinBarnesLeftPoles {a b : ℂ} {σ₁ σ₂ T : ℝ}
    (h12 : σ₁ < σ₂) (hT_pos : 0 < T) (hTim : max |a.im| |b.im| < T)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k) :
    ∀ t ∈ frontier (Rectangle ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I)),
      t ∉ (↑(mellinBarnesLeftPoles a b (σ₁ - 1)) : Set ℂ) := by
  set zL : ℂ := (σ₁ : ℂ) - T * I
  set wR : ℂ := (σ₂ : ℂ) + T * I
  have hRect_eq : Rectangle zL wR = Icc σ₁ σ₂ ×ℂ Icc (-T) T := by
    simp [Rectangle, zL, wR, uIcc_of_le h12.le, uIcc_of_le (by linarith : -T ≤ T)]
  have hRect_closed : IsClosed (Rectangle zL wR) := hRect_eq ▸ isClosed_Icc.reProdIm isClosed_Icc
  intro t ht htS
  have htR : t ∈ Icc σ₁ σ₂ ×ℂ Icc (-T) T := hRect_eq ▸ hRect_closed.closure_subset ht.1
  have ht_nint : t ∉ Ioo σ₁ σ₂ ×ℂ Ioo (-T) T := by
    have hint : interior (Rectangle zL wR) = Ioo σ₁ σ₂ ×ℂ Ioo (-T) T := by
      simpa [zL, wR] using interior_rectangle (z := zL) (w := wR)
        (by simp [zL, wR, h12.le]) (by simp [zL, wR]; linarith)
    exact hint ▸ ht.2
  have hpoles := (mem_mellinBarnesLeftPoles.1 htS).2
  have htim : t.im ∈ Ioo (-T) T := abs_lt.1 (by
    rcases hpoles with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp <;>
      linarith [le_max_left |a.im| |b.im|, le_max_right |a.im| |b.im|])
  have htre : t.re = σ₁ ∨ t.re = σ₂ := by
    by_contra hne; push Not at hne
    exact ht_nint ⟨⟨lt_of_le_of_ne htR.1.1 hne.1.symm, lt_of_le_of_ne htR.1.2 hne.2⟩, htim⟩
  rcases hpoles with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases htre with h1 | h2
  · exact ha₁ k (by simp at h1; linarith)
  · exact ha₂ k (by simp at h2; linarith)
  · exact hb₁ k (by simp at h1; linarith)
  · exact hb₂ k (by simp at h2; linarith)

private theorem rectBoundary_mellinBarnesIntegrand_eq {a b c z : ℂ} {σ₁ σ₂ T : ℝ}
    (h12 : σ₁ < σ₂) (hσ₂ : σ₂ < 0) (hT_pos : 0 < T) (hTim : max |a.im| |b.im| < T)
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
  have hRect_eq : Rectangle zL wR = Icc σ₁ σ₂ ×ℂ Icc (-T) T := by
    simp [Rectangle, zL, wR, uIcc_of_le h12.le, uIcc_of_le (by linarith : -T ≤ T)]
  have hRect_closed : IsClosed (Rectangle zL wR) := hRect_eq ▸ isClosed_Icc.reProdIm isClosed_Icc
  have hRectU : Rectangle zL wR ⊆ U := fun t ht => by
    rw [hRect_eq] at ht; exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
  have hfr_notS :=
    frontier_rectangle_notMem_mellinBarnesLeftPoles h12 hT_pos hTim ha₁ hb₁ ha₂ hb₂
  have hres := TauCeti.Contour.classicalResidueTheorem_nullHomologous hU hg_diff
    (fun s _ _ => meromorphicAt_mellinBarnesIntegrand a b c z s)
    (isPiecewiseC1On_rectBoundary zL wR)
    (fun t _ => hRectU (rectBoundary_mem_rectangle t)) (by simp)
    (fun t _ => hfr_notS _ (rectBoundary_mem_frontier t))
    (TauCeti.Contour.isNullHomologous_rectBoundary hRectU)
  have hint_eq := integral_rectBoundary (z := zL) (w := wR)
    (hg_diff.continuousOn.mono fun t ht =>
      ⟨hRectU (hRect_closed.closure_subset ht.1), hfr_notS t ht⟩)
  rw [hint_eq, sum_windingNumber_rect_mellinBarnes g h12 hT_pos hTim ha₁ hb₁ ha₂ hb₂] at hres
  simpa [zL, wR, sub_eq_add_neg, smul_eq_mul] using hres

private theorem tendsto_horizontal_mellinBarnesIntegrand_zero (a b c : ℂ) {z : ℂ} (σ₁ σ₂ : ℝ)
    (h12 : σ₁ < σ₂) (hz : -z ∈ slitPlane) {sgn : ℝ} (hsgn : |sgn| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, mellinBarnesIntegrand a b c z (x + (sgn * T) * I))
      atTop (𝓝 0) := by
  let R : ℝ := max (max ‖a‖ ‖b‖) (max ‖c‖ (max |σ₁| |σ₂|)) + 1
  let δ : ℝ := (π - |(-z).arg|) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz]
  obtain ⟨B, Y₀, _, hY₀, htail⟩ := exists_norm_mellinBarnesIntegrand_vertical_le R (by positivity)
    (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz))) hδ
  have hexp : Tendsto (fun T : ℝ => B * Real.exp (-δ * T) * (σ₂ - σ₁)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ => Real.exp (-δ * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hδ))
    simpa using (h0.const_mul B).mul_const (σ₂ - σ₁)
  refine tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hexp)
  filter_upwards [eventually_ge_atTop Y₀] with T hT
  have hT0 : 0 ≤ T := (zero_lt_one.trans_le hY₀).le.trans hT
  have habs : |sgn * T| = T := by rw [abs_mul, hsgn, one_mul, abs_of_nonneg hT0]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * Real.exp (-δ * T))
    fun x hx => ?_).trans ?_
  · rw [uIoc_of_le h12.le] at hx
    have hxR : |x| ≤ R := (abs_le_max_abs_abs hx.1.le hx.2).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
    have h := htail a b c z x (sgn * T)
      ((le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith)))
      ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith)))
      le_rfl le_rfl (by dsimp [δ]; linarith) hxR (habs.symm ▸ hT)
    simpa only [habs, ofReal_mul] using h
  · rw [abs_of_pos (sub_pos.2 h12)]

private theorem mellinBarnesSeparating_eq_of_lt_of_lt_zero {a b : ℂ} (c : ℂ) {z : ℂ} {σ₁ σ₂ : ℝ}
    (h12 : σ₁ < σ₂) (hσ₂ : σ₂ < 0)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesSeparating a b c z σ₁ = mellinBarnesSeparating a b c z σ₂ := by
  set g : ℂ → ℂ := mellinBarnesIntegrand a b c z
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x - T * I)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, neg_one_mul] using
      tendsto_horizontal_mellinBarnesIntegrand_zero a b c σ₁ σ₂ h12 hz (sgn := -1) (by norm_num)
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + T * I)) atTop (𝓝 0) := by
    simpa [one_mul] using
      tendsto_horizontal_mellinBarnesIntegrand_zero a b c σ₁ σ₂ h12 hz (sgn := 1) (by norm_num)
  have hv₁ : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, g (σ₁ + y * I)) atTop
      (𝓝 (∫ y : ℝ, g (σ₁ + y * I))) :=
    intervalIntegral_tendsto_integral
      (verticalIntegrable_mellinBarnesIntegrand c ha₁ hb₁
        (fun m _ => by linarith [h12, hσ₂, m.cast_nonneg (α := ℝ)]) hz)
      tendsto_neg_atTop_atBot tendsto_id
  have hv₂ : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, g (σ₂ + y * I)) atTop
      (𝓝 (∫ y : ℝ, g (σ₂ + y * I))) :=
    intervalIntegral_tendsto_integral
      (verticalIntegrable_mellinBarnesIntegrand c ha₂ hb₂
        (fun m _ => by linarith [hσ₂, m.cast_nonneg (α := ℝ)]) hz)
      tendsto_neg_atTop_atBot tendsto_id
  have hlim_lhs := ((hbot.sub htop).add (hv₂.const_mul I)).sub (hv₁.const_mul I)
  let T₀ : ℝ := max |a.im| |b.im| + 1
  have heq := tendsto_nhds_unique (hlim_lhs.congr' (by
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact rectBoundary_mellinBarnesIntegrand_eq h12 hσ₂
      (by dsimp [T₀] at hT; linarith [abs_nonneg a.im, le_max_left |a.im| |b.im|])
      (by dsimp [T₀] at hT; linarith) ha₁ hb₁ ha₂ hb₂)) tendsto_const_nhds
  simp only [sub_zero, zero_add] at heq
  have h2piI : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  have hdiv := congrArg ((2 * (π : ℂ) * I)⁻¹ * ·) heq
  rw [inv_mul_cancel_left₀ h2piI] at hdiv
  have hI : (2 * (π : ℂ) * I)⁻¹ * I = (2 * π : ℂ)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ I_ne_zero, mul_one]
  have hlhs : (2 * (π : ℂ) * I)⁻¹ *
      (I * (∫ y : ℝ, g (σ₂ + y * I)) - I * (∫ y : ℝ, g (σ₁ + y * I))) =
      (2 * π : ℂ)⁻¹ * (∫ y : ℝ, g (σ₂ + y * I)) - (2 * π : ℂ)⁻¹ * (∫ y : ℝ, g (σ₁ + y * I)) := by
    calc (2 * (π : ℂ) * I)⁻¹ *
          (I * (∫ y : ℝ, g (σ₂ + y * I)) - I * (∫ y : ℝ, g (σ₁ + y * I)))
        = ((2 * (π : ℂ) * I)⁻¹ * I) * (∫ y : ℝ, g (σ₂ + y * I)) -
            ((2 * (π : ℂ) * I)⁻¹ * I) * (∫ y : ℝ, g (σ₁ + y * I)) := by ring
      _ = (2 * π : ℂ)⁻¹ * (∫ y : ℝ, g (σ₂ + y * I)) -
            (2 * π : ℂ)⁻¹ * (∫ y : ℝ, g (σ₁ + y * I)) := by rw [hI]
  rw [hlhs] at hdiv
  rw [mellinBarnesSeparating_def, mellinBarnesSeparating_def]
  linear_combination -hdiv

/-- **Abscissa-independence of the separating-contour Mellin–Barnes functional.** For
`-z ∈ slitPlane`, `mellinBarnesSeparating a b c z σ` takes the same value for every negative
abscissa `σ < 0` whose vertical line `Re t = σ` avoids the left-family poles `-Re a - ℕ` and
`-Re b - ℕ`. -/
theorem mellinBarnesSeparating_eq_of_lt_zero {a b : ℂ} (c : ℂ) {z : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ < 0) (hσ₂ : σ₂ < 0)
    (ha₁ : ∀ k : ℕ, a.re + σ₁ ≠ -k) (hb₁ : ∀ k : ℕ, b.re + σ₁ ≠ -k)
    (ha₂ : ∀ k : ℕ, a.re + σ₂ ≠ -k) (hb₂ : ∀ k : ℕ, b.re + σ₂ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesSeparating a b c z σ₁ = mellinBarnesSeparating a b c z σ₂ := by
  rcases lt_trichotomy σ₁ σ₂ with hlt | rfl | hgt
  · exact mellinBarnesSeparating_eq_of_lt_of_lt_zero c hlt hσ₂ ha₁ hb₁ ha₂ hb₂ hz
  · rfl
  · exact (mellinBarnesSeparating_eq_of_lt_of_lt_zero c hgt hσ₁ ha₂ hb₂ ha₁ hb₁ hz).symm

/-! ### Section 4: Canonical continuation and joint four-variable holomorphy -/

private theorem not_both_abscissa_poles {w : ℂ} {x₁ x₂ : ℝ}
    (hx₁ : -1 < x₁ ∧ x₁ < 0) (hx₂ : -1 < x₂ ∧ x₂ < 0) (hne : x₁ ≠ x₂)
    (h1 : ∃ k : ℕ, w.re + x₁ = -k) (h2 : ∃ k : ℕ, w.re + x₂ = -k) : False := by
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  have hdiff : (((k₂ : ℤ) - (k₁ : ℤ) : ℤ) : ℝ) = x₁ - x₂ := by push_cast; linarith
  have hlt1 : (k₂ : ℤ) - k₁ < 1 := by
    exact_mod_cast (by linarith : (((k₂ : ℤ) - k₁ : ℤ) : ℝ) < 1)
  have hgt1 : (-1 : ℤ) < (k₂ : ℤ) - k₁ := by
    exact_mod_cast (by linarith : (-1 : ℝ) < (((k₂ : ℤ) - k₁ : ℤ) : ℝ))
  have hz : (k₂ : ℤ) - k₁ = 0 := by omega
  apply hne
  rw [hz] at hdiff
  simp only [Int.cast_zero] at hdiff
  linarith

private noncomputable def mellinBarnesAbscissa (a b : ℂ) : ℝ :=
  open Classical in
  if (∀ k : ℕ, a.re + (-1 / 2 : ℝ) ≠ -k) ∧ (∀ k : ℕ, b.re + (-1 / 2 : ℝ) ≠ -k) then -1 / 2
  else if (∀ k : ℕ, a.re + (-1 / 4 : ℝ) ≠ -k) ∧ (∀ k : ℕ, b.re + (-1 / 4 : ℝ) ≠ -k) then -1 / 4
  else -3 / 4

private theorem mellinBarnesAbscissa_symm (a b : ℂ) :
    mellinBarnesAbscissa a b = mellinBarnesAbscissa b a := by
  classical
  simp only [mellinBarnesAbscissa, and_comm]

private theorem mellinBarnesAbscissa_lt_zero (a b : ℂ) : mellinBarnesAbscissa a b < 0 := by
  classical
  unfold mellinBarnesAbscissa
  split_ifs <;> norm_num

private theorem mellinBarnesAbscissa_avoid (a b : ℂ) :
    (∀ k : ℕ, a.re + mellinBarnesAbscissa a b ≠ -k) ∧
      (∀ k : ℕ, b.re + mellinBarnesAbscissa a b ≠ -k) := by
  classical
  unfold mellinBarnesAbscissa
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · by_contra h3
    rw [not_and_or] at h1 h2 h3
    push Not at h1 h2 h3
    rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b <;> rcases h3 with h3a | h3b
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1a h2a
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1a h2a
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1a h3a
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h2b h3b
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h2a h3a
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1b h3b
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1b h2b
    · exact not_both_abscissa_poles ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num) h1b h2b

/-- **Canonical separating-contour Mellin–Barnes continuation.** Evaluated at a canonical negative
abscissa avoiding `-Re a - ℕ` and `-Re b - ℕ`, this agrees with `mellinBarnesSeparating a b c z σ`
for every admissible negative abscissa `σ < 0` when `-z ∈ slitPlane`. -/
def mellinBarnesContour (a b c z : ℂ) : ℂ :=
  mellinBarnesSeparating a b c z (mellinBarnesAbscissa a b)

/-- Symmetry of `mellinBarnesContour` in `a` and `b`. -/
theorem mellinBarnesContour_symm (a b c z : ℂ) :
    mellinBarnesContour a b c z = mellinBarnesContour b a c z := by
  rw [mellinBarnesContour, mellinBarnesContour, mellinBarnesAbscissa_symm a b,
    mellinBarnesSeparating_symm a b c z]

/-- On `-z ∈ slitPlane`, `mellinBarnesContour a b c z` equals `mellinBarnesSeparating a b c z σ`
for every negative abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`. -/
theorem mellinBarnesContour_eq_mellinBarnesSeparating {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, a.re + σ ≠ -k) (hb : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesContour a b c z = mellinBarnesSeparating a b c z σ :=
  mellinBarnesSeparating_eq_of_lt_zero c (mellinBarnesAbscissa_lt_zero a b) hσ
    (mellinBarnesAbscissa_avoid a b).1 (mellinBarnesAbscissa_avoid a b).2 ha hb hz

private theorem analyticAt_mellinBarnesIntegrand_uncurry {v : Fin 4 → ℂ} {t : ℂ}
    (ha : ∀ k : ℕ, v 0 + t ≠ -k) (hb : ∀ k : ℕ, v 1 + t ≠ -k) (ht : ∀ m : ℕ, -t ≠ -m)
    (hz : -v 3 ∈ slitPlane) :
    AnalyticAt ℂ
      (fun x : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (x.1 0) (x.1 1) (x.1 2) (x.1 3) x.2)
      (v, t) := by
  have hproj : ∀ i : Fin 4, AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => x.1 i) (v, t) := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) i).comp
      (ContinuousLinearMap.fst ℂ (Fin 4 → ℂ) ℂ)).analyticAt (v, t)
  have ha' : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => Gamma (x.1 0 + x.2)) (v, t) :=
    (analyticAt_Gamma ha).comp_of_eq ((hproj 0).add analyticAt_snd) rfl
  have hb' : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => Gamma (x.1 1 + x.2)) (v, t) :=
    (analyticAt_Gamma hb).comp_of_eq ((hproj 1).add analyticAt_snd) rfl
  have ht' : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => Gamma (-x.2)) (v, t) :=
    (analyticAt_Gamma ht).comp_of_eq analyticAt_snd.neg rfl
  have hc' : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => (Gamma (x.1 2 + x.2))⁻¹) (v, t) :=
    (differentiable_one_div_Gamma.analyticAt (v 2 + t)).comp_of_eq
      ((hproj 2).add analyticAt_snd) rfl
  have hz' : AnalyticAt ℂ (fun x : (Fin 4 → ℂ) × ℂ => (-x.1 3) ^ x.2) (v, t) :=
    (hproj 3).neg.cpow analyticAt_snd hz
  exact (((ha'.mul hb').mul ht').mul hc').mul hz'

private theorem exists_ball_abscissa_avoid (w₀ : ℂ) {σ : ℝ} (hw₀ : ∀ k : ℕ, w₀.re + σ ≠ -k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ w ∈ ball w₀ δ, (∀ k : ℕ, w.re + σ ≠ -k) ∧
        (∀ k : ℕ, (-w₀ - k).re < σ → (-w - k).re < σ) := by
  let N : ℕ := ⌊-w₀.re - σ⌋₊ + 2
  have hN_nonempty : (Finset.range N).Nonempty := ⟨0, by simp [N]⟩
  let δ : ℝ := min (1 / 2) ((Finset.range N).inf' hN_nonempty fun k => |w₀.re + σ + k| / 2)
  have hδ_pos : 0 < δ := lt_min (by norm_num) ((Finset.lt_inf'_iff hN_nonempty).2 fun k _ =>
    div_pos (abs_pos.2 fun h => hw₀ k (by linarith)) (by norm_num))
  refine ⟨δ, hδ_pos, min_le_left _ _, fun w hw => ?_⟩
  have hw_re : |w.re - w₀.re| < δ :=
    (abs_re_le_norm (w - w₀)).trans_lt (mem_ball_iff_norm.1 hw)
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hlarge : ∀ {k : ℕ}, N ≤ k → 0 < w.re + σ + k := fun {k} hk => by
    have hk' : (-w₀.re - σ) + 1 < k := by
      have h1 := Nat.lt_floor_add_one (-w₀.re - σ)
      have h2 : (⌊-w₀.re - σ⌋₊ + 2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    linarith [(abs_lt.1 hw_re).1, sub_re w w₀]
  refine ⟨fun k => ?_, fun k hk0 => ?_⟩
  · by_cases hk : k < N
    · have hle : δ ≤ |w₀.re + σ + k| / 2 :=
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hk))
      intro hEq
      have habs : |w₀.re + σ + k| = |w.re - w₀.re| := by
        have hsub : w.re - w₀.re = -(w₀.re + σ + k) := by linarith
        rw [hsub, abs_neg]
      linarith [abs_nonneg (w₀.re + σ + k)]
    · intro hEq
      linarith [hlarge (not_lt.1 hk)]
  · simp only [sub_re, neg_re, natCast_re] at hk0 ⊢
    by_cases hk : k < N
    · have hle : δ ≤ |w₀.re + σ + k| / 2 :=
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hk))
      have hpos0 : 0 < w₀.re + σ + k := by linarith
      rw [abs_of_pos hpos0] at hle
      linarith [(abs_lt.1 hw_re).1]
    · linarith [hlarge (not_lt.1 hk)]

private theorem analyticAt_truncated_vertical_mellinBarnes {v : Fin 4 → ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha : ∀ k : ℕ, (v 0).re + σ ≠ -k) (hb : ∀ k : ℕ, (v 1).re + σ ≠ -k)
    (hz : -v 3 ∈ slitPlane) (n : ℕ) :
    AnalyticAt ℂ (fun q : Fin 4 → ℂ =>
      ∫ y : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand (q 0) (q 1) (q 2) (q 3) (σ + y * I)) v := by
  have hn_le : -(n : ℝ) ≤ (n : ℝ) := by linarith [n.cast_nonneg (α := ℝ)]
  let γ : ℝ → ℂ := fun y => (σ : ℂ) + (projIcc (-(n : ℝ)) n hn_le y : ℝ) * I
  let K : Set ℂ := (fun y : ℝ => (σ : ℂ) + y * I) '' Icc (-(n : ℝ)) n
  have hγ : Continuous γ :=
    continuous_const.add ((continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_projIcc)).mul continuous_const)
  have hγK : ∀ y : ℝ, γ y ∈ K := fun y => ⟨_, (projIcc (-(n : ℝ)) n hn_le y).property, rfl⟩
  have hkernel : ∀ t ∈ K, AnalyticAt ℂ
      (fun x : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (x.1 0) (x.1 1) (x.1 2) (x.1 3) x.2)
      (v, t) := by
    rintro _ ⟨y, _, rfl⟩
    refine analyticAt_mellinBarnesIntegrand_uncurry
      (fun k h => ha k (by have hre := congrArg re h; simp at hre; linarith))
      (fun k h => hb k (by have hre := congrArg re h; simp at hre; linarith))
      (fun m h => by have hre := congrArg re h; simp at hre; linarith [m.cast_nonneg (α := ℝ)]) hz
  have hweight : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ioc (-(n : ℝ)) n)) :=
    integrable_const (1 : ℂ)
  have h := TauCeti.analyticAt_integral_smul (isCompact_Icc.image (by fun_prop)) hγ hγK
    hkernel hweight
  refine h.congr (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le hn_le]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simp only [one_smul, γ, projIcc_of_mem hn_le (Ioc_subset_Icc_self hy)]

private theorem tendsto_setIntegral_compl_Ioc_zero {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ y in (Ioc (-(n : ℝ)) n)ᶜ, g y) atTop (𝓝 0) := by
  have hconv := intervalIntegral_tendsto_integral hg
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun n : ℕ => (∫ y : ℝ, g y) - ∫ y : ℝ in (-(n : ℝ))..(n : ℝ), g y)
      atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using
      (tendsto_const_nhds (x := ∫ y : ℝ, g y)).sub hconv
  refine hsub.congr fun n => ?_
  rw [intervalIntegral.integral_of_le (by linarith [n.cast_nonneg (α := ℝ)]),
    ← integral_add_compl measurableSet_Ioc hg, add_sub_cancel_left]

private theorem tendstoUniformlyOn_truncated_vertical_mellinBarnes {v₀ : Fin 4 → ℂ} {σ δ₀ δ₁ ρ : ℝ}
    (hσ : σ < 0) (hδ₀_le : δ₀ ≤ 1 / 2) (hδ₁_le : δ₁ ≤ 1 / 2)
    (hav₀ : ∀ w ∈ ball (v₀ 0) δ₀, ∀ k : ℕ, w.re + σ ≠ -k)
    (hav₁ : ∀ w ∈ ball (v₀ 1) δ₁, ∀ k : ℕ, w.re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane)
    (hz_sub : ∀ z ∈ ball (v₀ 3) ρ, -z ∈ slitPlane ∧
      ‖v₀ 3‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖v₀ 3‖ ∧ |(-z).arg| ≤ π - 2 * ((π - |(-v₀ 3).arg|) / 4)) :
    TendstoUniformlyOn
      (fun (n : ℕ) (v : Fin 4 → ℂ) =>
        ∫ y : ℝ in (-(n : ℝ))..(n : ℝ), mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I))
      (fun v : Fin 4 → ℂ =>
        ∫ y : ℝ, mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I)) atTop
      (((fun v : Fin 4 → ℂ => v 0) ⁻¹' ball (v₀ 0) δ₀ ∩
          (fun v : Fin 4 → ℂ => v 1) ⁻¹' ball (v₀ 1) δ₁) ∩
        ((fun v : Fin 4 → ℂ => v 2) ⁻¹' ball (v₀ 2) 1 ∩
          (fun v : Fin 4 → ℂ => v 3) ⁻¹' ball (v₀ 3) ρ)) := by
  let δ : ℝ := (π - |(-v₀ 3).arg|) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
  have hr₁ : 0 < ‖v₀ 3‖ / 2 := half_pos (norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀)))
  let R : ℝ := max (max (‖v₀ 0‖ + 1) (‖v₀ 1‖ + 1)) (max (‖v₀ 2‖ + 1) |σ|) + 1
  obtain ⟨B, Y₀, _, _, htail⟩ :=
    exists_norm_mellinBarnesIntegrand_vertical_le R (r₂ := 2 * ‖v₀ 3‖) (by positivity) hr₁ hδ
  have hdom : Integrable fun y : ℝ => B * Real.exp (-δ * |y|) :=
    (integrable_exp_neg_mul_abs hδ).const_mul B
  have hε_lim := tendsto_setIntegral_compl_Ioc_zero hdom
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hε_lim.eventually (gt_mem_nhds hε), eventually_ge_atTop (⌈Y₀⌉₊ + 1)]
    with n hn_ε hn_Y v hv
  rw [dist_eq_norm]
  have hint_v := verticalIntegrable_mellinBarnesIntegrand (v 2) (hav₀ (v 0) hv.1.1)
    (hav₁ (v 1) hv.1.2) (fun m hm => by linarith [m.cast_nonneg (α := ℝ)]) (hz_sub (v 3) hv.2.2).1
  rw [intervalIntegral.integral_of_le (by linarith [n.cast_nonneg (α := ℝ)]),
    ← integral_add_compl (s := Ioc (-(n : ℝ)) n) measurableSet_Ioc hint_v, add_sub_cancel_left]
  refine (norm_integral_le_integral_norm _).trans_lt ((integral_mono_ae
    hint_v.norm.integrableOn hdom.integrableOn ?_).trans_lt hn_ε)
  filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with y hy
  have hyY : Y₀ ≤ |y| := by
    have hYN : Y₀ ≤ n := (Nat.le_ceil Y₀).trans
      (by exact_mod_cast (Nat.le_add_right _ 1).trans hn_Y)
    rcases not_and_or.1 hy with h1 | h2
    · linarith [not_lt.1 h1, neg_le_abs y]
    · linarith [not_le.1 h2, le_abs_self y]
  have hv0R : ‖v 0‖ ≤ R := (norm_le_norm_sub_add _ _).trans (by
    have hM : ‖v₀ 0‖ + 1 ≤ R :=
      (le_max_left _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith))
    linarith [(mem_ball_iff_norm.1 hv.1.1).le.trans hδ₀_le])
  have hv1R : ‖v 1‖ ≤ R := (norm_le_norm_sub_add _ _).trans (by
    have hM : ‖v₀ 1‖ + 1 ≤ R :=
      (le_max_right _ _).trans ((le_max_left _ _).trans (by dsimp [R]; linarith))
    linarith [(mem_ball_iff_norm.1 hv.1.2).le.trans hδ₁_le])
  have hv2R : ‖v 2‖ ≤ R := (norm_le_norm_sub_add _ _).trans (by
    have hM : ‖v₀ 2‖ + 1 ≤ R :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith))
    linarith [(mem_ball_iff_norm.1 hv.2.1).le])
  have hσR : |σ| ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [R]; linarith))
  have hzb := hz_sub (v 3) hv.2.2
  exact htail (v 0) (v 1) (v 2) (v 3) σ y hv0R hv1R hv2R hzb.2.1 hzb.2.2.1 hzb.2.2.2 hσR hyY

private theorem exists_ball_slitPlane_arg_bound {z₀ : ℂ} (hz₀ : -z₀ ∈ slitPlane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ ball z₀ ρ, -z ∈ slitPlane ∧
      ‖z₀‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖z₀‖ ∧ |(-z).arg| ≤ π - 2 * ((π - |(-z₀).arg|) / 4) := by
  have hopen1 : IsOpen {z : ℂ | -z ∈ slitPlane} := isOpen_slitPlane.preimage continuous_neg
  obtain ⟨ρ₁, hρ₁, hsub₁⟩ := Metric.isOpen_iff.1 hopen1 z₀ hz₀
  let δ : ℝ := (π - |(-z₀).arg|) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith [abs_arg_lt_pi_of_mem_slitPlane hz₀]
  have hcont_arg : ContinuousAt (fun z : ℂ => |(-z).arg|) z₀ :=
    continuous_abs.continuousAt.comp ((continuousAt_arg hz₀).comp continuous_neg.continuousAt)
  obtain ⟨ρ₂, hρ₂, hsub₂⟩ := Metric.eventually_nhds_iff_ball.1
    (hcont_arg.eventually (gt_mem_nhds (show |(-z₀).arg| < |(-z₀).arg| + 2 * δ by linarith)))
  have hz₀_pos : 0 < ‖z₀‖ := norm_pos_iff.2 (neg_ne_zero.1 (slitPlane_ne_zero hz₀))
  let ρ : ℝ := min (‖z₀‖ / 2) (min ρ₁ ρ₂)
  refine ⟨ρ, lt_min (by positivity) (lt_min hρ₁ hρ₂), fun z hz => ?_⟩
  have hzn : ‖z - z₀‖ < ‖z₀‖ / 2 := (mem_ball_iff_norm.1 hz).trans_le (min_le_left _ _)
  have hlt := hsub₂ z (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz)
  exact ⟨hsub₁ (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz),
    by linarith [norm_sub_norm_le z₀ z, norm_sub_rev z₀ z],
    by linarith [norm_le_norm_sub_add z z₀], by dsimp [δ] at hlt ⊢; linarith⟩

private theorem analyticAt_vertical_mellinBarnes {v₀ : Fin 4 → ℂ} {σ : ℝ}
    (hσ : σ < 0) (ha₀ : ∀ k : ℕ, (v₀ 0).re + σ ≠ -k) (hb₀ : ∀ k : ℕ, (v₀ 1).re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      ∫ y : ℝ, mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) (σ + y * I)) v₀ := by
  obtain ⟨δ₀, hδ₀, hδ₀_le, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀
  obtain ⟨δ₁, hδ₁, hδ₁_le, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀
  obtain ⟨ρ, hρ, hz_sub⟩ := exists_ball_slitPlane_arg_bound hz₀
  let U : Set (Fin 4 → ℂ) :=
    ((fun v : Fin 4 → ℂ => v 0) ⁻¹' ball (v₀ 0) δ₀ ∩
      (fun v : Fin 4 → ℂ => v 1) ⁻¹' ball (v₀ 1) δ₁) ∩
    ((fun v : Fin 4 → ℂ => v 2) ⁻¹' ball (v₀ 2) 1 ∩
      (fun v : Fin 4 → ℂ => v 3) ⁻¹' ball (v₀ 3) ρ)
  have hU_open : IsOpen U :=
    ((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).inter
      ((isOpen_ball.preimage (continuous_apply 2)).inter
        (isOpen_ball.preimage (continuous_apply 3)))
  have hv₀U : v₀ ∈ U := ⟨⟨mem_ball_self hδ₀, mem_ball_self hδ₁⟩,
    ⟨mem_ball_self zero_lt_one, mem_ball_self hρ⟩⟩
  have hunif := tendstoUniformlyOn_truncated_vertical_mellinBarnes hσ hδ₀_le hδ₁_le
    (fun w hw => (hav₀ w hw).1) (fun w hw => (hav₁ w hw).1) hz₀ hz_sub
  have hF_an : ∀ n : ℕ, ∀ v ∈ U, AnalyticAt ℂ (fun q : Fin 4 → ℂ =>
      ∫ y : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand (q 0) (q 1) (q 2) (q 3) (σ + y * I)) v :=
    fun n v hv => analyticAt_truncated_vertical_mellinBarnes hσ (hav₀ (v 0) hv.1.1).1
      (hav₁ (v 1) hv.1.2).1 (hz_sub (v 3) hv.2.2).1 n
  have hG_cont := hunif.continuousOn <| (Eventually.of_forall (f := atTop) fun n : ℕ =>
    (fun v hv => (hF_an n v hv).continuousAt.continuousWithinAt : ContinuousOn _ U)).frequently
  refine hG_cont.analyticAt_of_differentiableAt_update (hU_open.mem_nhds hv₀U) fun y hy i => ?_
  let V : Set ℂ := (fun x => Function.update y i x) ⁻¹' U
  have hV_open : IsOpen V := hU_open.preimage (Continuous.update continuous_const i continuous_id)
  have hupd : Differentiable ℂ (fun x : ℂ => Function.update y i x) := by
    rw [differentiable_pi]; intro j; by_cases hj : j = i <;> simp [Function.update, hj]
  have hunifV : TendstoUniformlyOn
      (fun (n : ℕ) x => ∫ w : ℝ in (-(n : ℝ))..(n : ℝ),
        mellinBarnesIntegrand (Function.update y i x 0) (Function.update y i x 1)
          (Function.update y i x 2) (Function.update y i x 3) (σ + w * I))
      (fun x => ∫ w : ℝ,
        mellinBarnesIntegrand (Function.update y i x 0) (Function.update y i x 1)
          (Function.update y i x 2) (Function.update y i x 3) (σ + w * I)) atTop V :=
    Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      (Metric.tendstoUniformlyOn_iff.1 hunif ε hε).mono fun _ hn _ hx => hn _ hx
  have hyV : y i ∈ V := show Function.update y i (y i) ∈ U by rwa [Function.update_eq_self]
  exact (hunifV.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (f := atTop) fun (n : ℕ) x hx =>
      ((hF_an n _ hx).differentiableAt.comp x (hupd x)).differentiableWithinAt)
    hV_open).differentiableAt (hV_open.mem_nhds hyV)

private theorem exists_pos_lt_norm_sub_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ m) :
    ∃ r : ℝ, 0 < r ∧ ∀ m : ℕ, r < ‖s - m‖ := by
  let M : ℕ := ⌈‖s‖⌉₊ + 2
  have hM : (Finset.range M).Nonempty := ⟨0, by simp [M]⟩
  let r : ℝ := min (1 / 2) ((Finset.range M).inf' hM fun m => ‖s - m‖ / 2)
  have hr : 0 < r := lt_min (by norm_num) ((Finset.lt_inf'_iff hM).2 fun m _ =>
    div_pos (norm_pos_iff.2 (sub_ne_zero.2 (hs m))) (by norm_num))
  refine ⟨r, hr, fun m => ?_⟩
  by_cases hm : m < M
  · have hle : r ≤ ‖s - m‖ / 2 :=
      (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hm))
    linarith [norm_pos_iff.2 (sub_ne_zero.2 (hs m))]
  · have hm_ge : ‖s‖ + 2 ≤ m := by
      have h1 := Nat.le_ceil ‖s‖
      have h2 : (⌈‖s‖⌉₊ + 2 : ℝ) ≤ m := by exact_mod_cast not_lt.1 hm
      linarith
    have hnorm : 2 ≤ ‖s - m‖ := by
      have h := norm_sub_norm_le (m : ℂ) s
      rw [Complex.norm_natCast, norm_sub_rev] at h
      linarith
    linarith [min_le_left (1 / 2 : ℝ) ((Finset.range M).inf' hM fun m => ‖s - m‖ / 2)]

private theorem exists_isolating_radius_mellinBarnesLeftPoles {a₀ b₀ : ℂ} (σ : ℝ)
    (ha₀ : ∀ k : ℕ, a₀ ≠ -k) (hb₀ : ∀ k : ℕ, b₀ ≠ -k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, σ + r < s.re) ∧
      (∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ m : ℕ, r < ‖s - m‖) ∧
      (∀ s₁ ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ s₂ ∈ mellinBarnesLeftPoles a₀ b₀ σ,
        s₁ ≠ s₂ → 2 * r < dist s₁ s₂) := by
  set P₀ : Finset ℂ := mellinBarnesLeftPoles a₀ b₀ σ
  have hs_nat : ∀ s ∈ P₀, ∀ m : ℕ, s ≠ m := fun s hs m hEq => by
    rcases (mem_mellinBarnesLeftPoles.1 hs).2 with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ha₀ (k + m) (by push_cast; linear_combination -hEq)
    · exact hb₀ (k + m) (by push_cast; linear_combination -hEq)
  suffices ∀ Q : Finset ℂ, (∀ s ∈ Q, σ < s.re ∧ ∀ m : ℕ, s ≠ m) →
      ∃ r : ℝ, 0 < r ∧ (∀ s ∈ Q, σ + r < s.re) ∧ (∀ s ∈ Q, ∀ m : ℕ, r < ‖s - m‖) ∧
        (∀ s₁ ∈ Q, ∀ s₂ ∈ Q, s₁ ≠ s₂ → 2 * r < dist s₁ s₂) from
    this P₀ fun s hs => ⟨(mem_mellinBarnesLeftPoles.1 hs).1, hs_nat s hs⟩
  intro Q
  induction Q using Finset.cons_induction with
  | empty => exact fun _ => ⟨1, zero_lt_one, by simp, by simp, by simp⟩
  | cons s₀ Q hs₀ ih =>
    intro hQ
    obtain ⟨r₁, hr₁, hre₁, hnat₁, hsep₁⟩ := ih fun s hs => hQ s (Finset.mem_cons_of_mem hs)
    have hs₀Q := hQ s₀ (Finset.mem_cons_self s₀ Q)
    obtain ⟨r₂, hr₂, hnat₂⟩ := exists_pos_lt_norm_sub_nat hs₀Q.2
    let r₃ : ℝ := if hne : Q.Nonempty then Q.inf' hne fun s => dist s₀ s / 3 else 1
    have hr₃ : 0 < r₃ := by
      dsimp [r₃]; split_ifs with hne
      · exact (Finset.lt_inf'_iff hne).2 fun s hs =>
          div_pos (dist_pos.2 fun h => hs₀ (h ▸ hs)) (by norm_num)
      · exact zero_lt_one
    let r : ℝ := min (min r₁ r₂) (min ((s₀.re - σ) / 2) r₃)
    have hr : 0 < r := lt_min (lt_min hr₁ hr₂) (lt_min (by linarith [hs₀Q.1]) hr₃)
    have hr_le₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hr_le₂ : r ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hr_le_re : r ≤ (s₀.re - σ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hr_le₃ : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨r, hr, fun s hs => ?_, fun s hs m => ?_, fun s₁ hs₁ s₂ hs₂ hne => ?_⟩
    · rcases Finset.mem_cons.1 hs with rfl | hs
      · linarith [hs₀Q.1]
      · linarith [hre₁ s hs]
    · rcases Finset.mem_cons.1 hs with rfl | hs
      · exact hr_le₂.trans_lt (hnat₂ m)
      · exact hr_le₁.trans_lt (hnat₁ s hs m)
    · have hdist_s₀ : ∀ s ∈ Q, 2 * r < dist s₀ s := fun s hs => by
        have hneQ : Q.Nonempty := ⟨s, hs⟩
        have hle : r₃ ≤ dist s₀ s / 3 := by
          dsimp only [r₃]; rw [dite_eq_left_of_eq_true (eq_true hneQ)]; exact Finset.inf'_le _ hs
        linarith [dist_pos.2 fun h : s₀ = s => hs₀ (h ▸ hs)]
      rcases Finset.mem_cons.1 hs₁ with h1 | hs₁
      · rcases Finset.mem_cons.1 hs₂ with h2 | hs₂
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1]; exact hdist_s₀ s₂ hs₂
      · rcases Finset.mem_cons.1 hs₂ with h2 | hs₂
        · rw [h2, dist_comm]; exact hdist_s₀ s₁ hs₁
        · linarith [hsep₁ s₁ hs₁ s₂ hs₂ hne]

private theorem mellinBarnesLeftPoles_cover {a₀ b₀ a b : ℂ} {σ r : ℝ}
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    ∀ w ∈ mellinBarnesLeftPoles a b σ, ∃ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, w ∈ ball s r := by
  intro w hw
  rcases mem_mellinBarnesLeftPoles.1 hw with ⟨hw_re, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩
  · refine ⟨-a₀ - k, mem_mellinBarnesLeftPoles.2 ⟨?_, Or.inl ⟨k, rfl⟩⟩, ?_⟩
    · refine lt_of_le_of_ne (not_lt.1 fun h => hw_re.not_gt (ha_cross k h)) fun h =>
        ha₀_σ k (by simp at h; linarith)
    · rw [mem_ball_iff_norm]
      have heq : (-a - (k : ℂ)) - (-a₀ - k) = -(a - a₀) := by ring
      rw [heq, norm_neg]; linarith [norm_nonneg (a - a₀)]
  · refine ⟨-b₀ - k, mem_mellinBarnesLeftPoles.2 ⟨?_, Or.inr ⟨k, rfl⟩⟩, ?_⟩
    · refine lt_of_le_of_ne (not_lt.1 fun h => hw_re.not_gt (hb_cross k h)) fun h =>
        hb₀_σ k (by simp at h; linarith)
    · rw [mem_ball_iff_norm]
      have heq : (-b - (k : ℂ)) - (-b₀ - k) = -(b - b₀) := by ring
      rw [heq, norm_neg]; linarith [norm_nonneg (b - b₀)]

private theorem residueSum_eq_sum_circleIntegral_mellinBarnes {a₀ b₀ a b : ℂ} (c z : ℂ) {σ r : ℝ}
    (hr : 0 < r)
    (hre : ∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, σ + r < s.re)
    (hnat : ∀ s ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ m : ℕ, r < ‖s - m‖)
    (hsep : ∀ s₁ ∈ mellinBarnesLeftPoles a₀ b₀ σ, ∀ s₂ ∈ mellinBarnesLeftPoles a₀ b₀ σ,
      s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (ha₀_σ : ∀ k : ℕ, a₀.re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, b₀.re + σ ≠ -k)
    (ha_dist : ‖a - a₀‖ < r / 2) (hb_dist : ‖b - b₀‖ < r / 2)
    (ha_cross : ∀ k : ℕ, (-a₀ - k).re < σ → (-a - k).re < σ)
    (hb_cross : ∀ k : ℕ, (-b₀ - k).re < σ → (-b - k).re < σ) :
    (∑ w ∈ mellinBarnesLeftPoles a b σ,
      TauCeti.Contour.residue (mellinBarnesIntegrand a b c z) w) =
      ∑ s ∈ mellinBarnesLeftPoles a₀ b₀ σ,
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r), mellinBarnesIntegrand a b c z ζ := by
  classical
  set P₀ : Finset ℂ := mellinBarnesLeftPoles a₀ b₀ σ
  set P : Finset ℂ := mellinBarnesLeftPoles a b σ
  set g : ℂ → ℂ := mellinBarnesIntegrand a b c z
  let F : ℂ → Finset ℂ := fun s => P.filter (· ∈ ball s r)
  have hcover := mellinBarnesLeftPoles_cover ha₀_σ hb₀_σ ha_dist hb_dist ha_cross hb_cross
  have hdisj : (P₀ : Set ℂ).PairwiseDisjoint F := fun s₁ hs₁ s₂ hs₂ hne =>
    Finset.disjoint_left.2 fun w hw₁ hw₂ =>
      by linarith [mem_ball.1 (Finset.mem_filter.1 hw₁).2,
        mem_ball.1 (Finset.mem_filter.1 hw₂).2, dist_triangle_left s₁ s₂ w, hsep s₁ hs₁ s₂ hs₂ hne]
  have hbiU : P₀.biUnion F = P := by
    ext w; simp only [Finset.mem_biUnion, F, Finset.mem_filter]
    exact ⟨fun ⟨_, _, hw, _⟩ => hw, fun hw =>
      let ⟨s, hs, hws⟩ := hcover w hw; ⟨s, hs, hw, hws⟩⟩
  rw [← hbiU, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsupp : ∀ w ∈ closedBall s r, meromorphicOrderAt g w < 0 → w ∈ F s := fun w hw hord => by
    have hpole : (∃ k : ℕ, w = -a - k) ∨ (∃ k : ℕ, w = -b - k) := by
      by_contra hno; push Not at hno
      refine hord.not_ge (analyticAt_mellinBarnesIntegrand a b c z hno.1 hno.2
        fun m hm => ?_).meromorphicOrderAt_nonneg
      have h1 : ‖s - m‖ ≤ r := by rw [← dist_eq_norm, dist_comm, ← hm]; exact hw
      linarith [hnat s hs m]
    have hw_re : σ < w.re := by
      have h1 : |w.re - s.re| ≤ r := (abs_re_le_norm (w - s)).trans (mem_closedBall_iff_norm.1 hw)
      linarith [(abs_le.1 h1).1, hre s hs]
    have hwP : w ∈ P := mem_mellinBarnesLeftPoles.2 ⟨hw_re, hpole⟩
    obtain ⟨s', hs', hws'⟩ := hcover w hwP
    have hs_eq : s' = s := by
      by_contra hne
      linarith [mem_closedBall.1 hw, mem_ball.1 hws', dist_triangle_left s' s w,
        hsep s' hs' s hs hne]
    subst hs_eq; exact Finset.mem_filter.2 ⟨hwP, hws'⟩
  have hcirc := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hr (F s)
    (fun ζ _ => meromorphicAt_mellinBarnesIntegrand a b c z ζ)
    (fun ζ hζ => (Finset.mem_filter.1 hζ).2) hsupp
  have h2piI : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  rw [hcirc, inv_mul_cancel_left₀ h2piI]

private theorem analyticAt_circleIntegral_mellinBarnes_term {v₀ : Fin 4 → ℂ} {σ r : ℝ}
    (hr : 0 < r)
    (hre : ∀ s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, σ + r < s.re)
    (hnat : ∀ s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, ∀ m : ℕ, r < ‖s - m‖)
    (hsep : ∀ s₁ ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ,
      ∀ s₂ ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ, s₁ ≠ s₂ → 2 * r < dist s₁ s₂)
    (hz₀ : -v₀ 3 ∈ slitPlane)
    {s : ℂ} (hs : s ∈ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
        mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀ := by
  have hc : AnalyticAt ℂ (fun _ : Fin 4 → ℂ => (2 * (π : ℂ) * I)⁻¹) v₀ := analyticAt_const
  refine hc.mul (TauCeti.analyticAt_circleIntegral (c := s) (R := r) (p₀ := v₀)
    (f := fun p : (Fin 4 → ℂ) × ℂ => mellinBarnesIntegrand (p.1 0) (p.1 1) (p.1 2) (p.1 3) p.2)
    fun ζ hζ => ?_)
  rw [abs_of_pos hr] at hζ
  have hζ_re : σ < ζ.re := by
    have h1 : |ζ.re - s.re| ≤ r := (abs_re_le_norm (ζ - s)).trans (mem_sphere_iff_norm.1 hζ).le
    linarith [(abs_le.1 h1).1, hre s hs]
  have hnot_P₀ : ζ ∉ mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ := fun hζP => by
    by_cases heq : ζ = s
    · subst heq; simp at hζ; linarith
    · linarith [mem_sphere.1 hζ, hsep ζ hζP s hs heq]
  refine analyticAt_mellinBarnesIntegrand_uncurry
    (fun k hk => hnot_P₀ (mem_mellinBarnesLeftPoles.2
      ⟨hζ_re, Or.inl ⟨k, by linear_combination hk⟩⟩))
    (fun k hk => hnot_P₀ (mem_mellinBarnesLeftPoles.2
      ⟨hζ_re, Or.inr ⟨k, by linear_combination hk⟩⟩))
    (fun m hm => by
      have hζm : ζ = m := by linear_combination -hm
      have h1 : ‖s - m‖ = r := by rw [← dist_eq_norm, dist_comm, ← hζm]; exact hζ
      linarith [hnat s hs m]) hz₀

private theorem analyticAt_residueSum_mellinBarnes {v₀ : Fin 4 → ℂ} {σ : ℝ}
    (ha₀ : ∀ k : ℕ, v₀ 0 ≠ -k) (hb₀ : ∀ k : ℕ, v₀ 1 ≠ -k)
    (ha₀_σ : ∀ k : ℕ, (v₀ 0).re + σ ≠ -k) (hb₀_σ : ∀ k : ℕ, (v₀ 1).re + σ ≠ -k)
    (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
      ∑ w ∈ mellinBarnesLeftPoles (v 0) (v 1) σ,
        TauCeti.Contour.residue (mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3)) w) v₀ := by
  obtain ⟨r, hr, hre, hnat, hsep⟩ := exists_isolating_radius_mellinBarnesLeftPoles σ ha₀ hb₀
  obtain ⟨δ₀, hδ₀, _, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀_σ
  obtain ⟨δ₁, hδ₁, _, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀_σ
  have hsum_an : ∀ Q : Finset ℂ,
      (∀ s ∈ Q, AnalyticAt ℂ (fun v : Fin 4 → ℂ =>
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
          mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀) →
      AnalyticAt ℂ (fun v : Fin 4 → ℂ => ∑ s ∈ Q,
        (2 * (π : ℂ) * I)⁻¹ * ∮ ζ in C(s, r),
          mellinBarnesIntegrand (v 0) (v 1) (v 2) (v 3) ζ) v₀ := by
    intro Q
    induction Q using Finset.cons_induction with
    | empty => exact fun _ => by simpa using analyticAt_const
    | cons s Q hs ih =>
      intro hQ
      simp_rw [Finset.sum_cons]
      exact (hQ s (Finset.mem_cons_self s Q)).add
        (ih fun t ht => hQ t (Finset.mem_cons_of_mem ht))
  let δ_ab : ℝ := min (r / 2) (min δ₀ δ₁)
  have hδ_ab : 0 < δ_ab := lt_min (by positivity) (lt_min hδ₀ hδ₁)
  let U : Set (Fin 4 → ℂ) :=
    (fun v : Fin 4 → ℂ => v 0) ⁻¹' ball (v₀ 0) δ_ab ∩
      (fun v : Fin 4 → ℂ => v 1) ⁻¹' ball (v₀ 1) δ_ab
  have hU_nhds : U ∈ 𝓝 v₀ :=
    ((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).mem_nhds
      ⟨mem_ball_self hδ_ab, mem_ball_self hδ_ab⟩
  refine (hsum_an (mellinBarnesLeftPoles (v₀ 0) (v₀ 1) σ) fun _ hs =>
    analyticAt_circleIntegral_mellinBarnes_term hr hre hnat hsep hz₀ hs).congr ?_
  filter_upwards [hU_nhds] with v hv
  exact (residueSum_eq_sum_circleIntegral_mellinBarnes (v 2) (v 3) hr hre hnat hsep ha₀_σ hb₀_σ
    ((mem_ball_iff_norm.1 hv.1).trans_le (min_le_left _ _))
    ((mem_ball_iff_norm.1 hv.2).trans_le (min_le_left _ _))
    (hav₀ (v 0) (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hv.1)).2
    (hav₁ (v 1) (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hv.2)).2).symm

private theorem analyticAt_mellinBarnesContour_pi {v₀ : Fin 4 → ℂ}
    (ha₀ : ∀ k : ℕ, v₀ 0 ≠ -k) (hb₀ : ∀ k : ℕ, v₀ 1 ≠ -k) (hz₀ : -v₀ 3 ∈ slitPlane) :
    AnalyticAt ℂ (fun v : Fin 4 → ℂ => mellinBarnesContour (v 0) (v 1) (v 2) (v 3)) v₀ := by
  let σ : ℝ := mellinBarnesAbscissa (v₀ 0) (v₀ 1)
  have hσ : σ < 0 := mellinBarnesAbscissa_lt_zero (v₀ 0) (v₀ 1)
  obtain ⟨ha₀_σ, hb₀_σ⟩ := mellinBarnesAbscissa_avoid (v₀ 0) (v₀ 1)
  have hv_an := analyticAt_vertical_mellinBarnes hσ ha₀_σ hb₀_σ hz₀
  have hr_an := analyticAt_residueSum_mellinBarnes ha₀ hb₀ ha₀_σ hb₀_σ hz₀
  obtain ⟨δ₀, hδ₀, _, hav₀⟩ := exists_ball_abscissa_avoid (v₀ 0) ha₀_σ
  obtain ⟨δ₁, hδ₁, _, hav₁⟩ := exists_ball_abscissa_avoid (v₀ 1) hb₀_σ
  have hz_open : IsOpen {v : Fin 4 → ℂ | -v 3 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_neg.comp (continuous_apply 3))
  let U : Set (Fin 4 → ℂ) :=
    ((fun v : Fin 4 → ℂ => v 0) ⁻¹' ball (v₀ 0) δ₀ ∩
      (fun v : Fin 4 → ℂ => v 1) ⁻¹' ball (v₀ 1) δ₁) ∩
    {v : Fin 4 → ℂ | -v 3 ∈ slitPlane}
  have hU_nhds : U ∈ 𝓝 v₀ :=
    (((isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_apply 1))).inter hz_open).mem_nhds
      ⟨⟨mem_ball_self hδ₀, mem_ball_self hδ₁⟩, hz₀⟩
  have hc : AnalyticAt ℂ (fun _ : Fin 4 → ℂ => (2 * (π : ℂ))⁻¹) v₀ := analyticAt_const
  refine ((hc.mul hv_an).add hr_an).congr ?_
  filter_upwards [hU_nhds] with v hv
  exact (mellinBarnesContour_eq_mellinBarnesSeparating (v 2) hσ (hav₀ (v 0) hv.1.1).1
    (hav₁ (v 1) hv.1.2).1 hv.2).symm

/-- **Joint four-variable holomorphy of the separating-contour Mellin–Barnes continuation.** On
`{p | (∀ k : ℕ, a ≠ -k) ∧ (∀ k : ℕ, b ≠ -k) ∧ -z ∈ slitPlane}`, `mellinBarnesContour a b c z` is
jointly analytic in `(a, b, c, z)` across all lower parameters `c : ℂ` and across integer
differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesContour :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesContour p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane} := by
  intro p ⟨ha, hb, hz⟩
  let emb : ℂ × ℂ × ℂ × ℂ → Fin 4 → ℂ := fun q i =>
    match i with
    | 0 => q.1
    | 1 => q.2.1
    | 2 => q.2.2.1
    | 3 => q.2.2.2
  have hemb_diff : Differentiable ℂ emb := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> dsimp [emb] <;> fun_prop
  have hemb : AnalyticAt ℂ emb p :=
    hemb_diff.differentiableOn.analyticAt_of_finiteDimensional univ_mem
  exact ((analyticAt_mellinBarnesContour_pi (v₀ := emb p) ha hb hz).comp hemb).congr
    (Eventually.of_forall fun _ => rfl)

end Complex
