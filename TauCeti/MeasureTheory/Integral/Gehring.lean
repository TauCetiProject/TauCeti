/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
-- Proof-only: Tonelli's theorem for the exchange of the level and space integrals.
import Mathlib.MeasureTheory.Measure.Prod
-- Proof-only: the integrals of `t ^ s` over `(0, a)` and over a cut-off half-line.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The level-set integration step of Gehring's lemma

Gehring's lemma says that a nonnegative function satisfying a reverse Hölder inequality
`(⨍_B g^q)^{1/q} ≤ C ⨍_{2B} g` on all balls is integrable to a power slightly larger than `q`.
Its proof has two steps. A Calderón–Zygmund covering argument turns the reverse Hölder inequality
into an estimate on superlevel sets: for all large heights `t`,

`∫_{f > t} f^q ≤ A t^(q - 1) ∫_{f > η t} f + ∫_{h > t} h^q`,

where `0 < η ≤ 1` and `h` collects the inhomogeneous terms. This file proves the second step,
which is pure measure theory: such a level-set estimate holding for every `t ≥ t₀` already forces
`f ∈ L^(q + ε)` whenever `2 A ε ≤ (q - 1 + ε) η^(q - 1 + ε)`, with the explicit bound

`∫ f^(q + ε) ≤ 2 t₀^ε ∫ f^q + 2 ∫ h^(q + ε)`.

The proof multiplies the level-set estimate by `t^(ε - 1)` and integrates over `t₀ < t < k`.
Tonelli's theorem turns the left side into `∫ f^q min(f, k)^ε`, up to the contribution of the
heights below `t₀`, and the first term on the right into at most a fraction `1/2` of the same
integral, which is finite thanks to the truncation at `k` and can therefore be absorbed. Letting
`k → ∞` gives the bound.

## Main declarations

* `TauCeti.lintegral_rpow_add_le_of_setLIntegral_rpow_le`: higher integrability from a
  level-set estimate.

## References

* F. W. Gehring, *The `Lᵖ`-integrability of the partial derivatives of a quasiconformal
  mapping*, Acta Math. **130** (1973), 265–277.
* M. Giaquinta and L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic
  Systems, Harmonic Maps and Minimal Graphs*, 2nd ed., Theorem 6.38 (Gehring's lemma) and the
  level-set argument behind it.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Tonelli's theorem for superlevel sets.** Integrating the integrals of `F` over the
superlevel sets `{g > φ t}` against a weight `w` in `t` is integrating `F` against the integral
of `w` over the heights `t` with `φ t < g`. -/
private theorem lintegral_mul_setLIntegral_eq [SFinite μ] {g F : α → ℝ≥0∞} (hg : Measurable g)
    (hF : Measurable F) {φ : ℝ → ℝ} (hφ : Measurable φ) {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (ν : Measure ℝ) [SFinite ν] :
    ∫⁻ t, w t * ∫⁻ x in {x | ENNReal.ofReal (φ t) < g x}, F x ∂μ ∂ν =
      ∫⁻ x, F x * ∫⁻ t, {t | ENNReal.ofReal (φ t) < g x}.indicator w t ∂ν ∂μ := by
  have hS : MeasurableSet {p : ℝ × α | ENNReal.ofReal (φ p.1) < g p.2} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (hφ.comp measurable_fst))
      (hg.comp measurable_snd)
  set G : ℝ → α → ℝ≥0∞ := fun t x => if ENNReal.ofReal (φ t) < g x then w t * F x else 0
  have hG : Measurable (Function.uncurry G) :=
    Measurable.ite hS ((hw.comp measurable_fst).mul (hF.comp measurable_snd)) measurable_const
  have hleft : ∀ t, w t * ∫⁻ x in {x | ENNReal.ofReal (φ t) < g x}, F x ∂μ = ∫⁻ x, G t x ∂μ := by
    intro t
    rw [← lintegral_indicator (measurableSet_lt measurable_const hg),
      ← lintegral_const_mul _ (hF.indicator (measurableSet_lt measurable_const hg))]
    refine lintegral_congr fun x => ?_
    by_cases hx : ENNReal.ofReal (φ t) < g x <;> simp [G, hx]
  have hright : ∀ x, F x * ∫⁻ t, {t | ENNReal.ofReal (φ t) < g x}.indicator w t ∂ν =
      ∫⁻ t, G t x ∂ν := by
    intro x
    have hT : MeasurableSet {t | ENNReal.ofReal (φ t) < g x} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp hφ) measurable_const
    rw [← lintegral_const_mul _ (hw.indicator hT)]
    refine lintegral_congr fun t => ?_
    by_cases ht : ENNReal.ofReal (φ t) < g x <;> simp [G, ht, mul_comm]
  simp_rw [hleft, hright]
  exact lintegral_lintegral_swap hG.aemeasurable

/-- The superlevel-set integrals `t ↦ ∫_{g > c t} F` are antitone for `0 ≤ c`, hence
measurable. -/
private theorem measurable_setLIntegral_lt {g F : α → ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) :
    Measurable fun t : ℝ => ∫⁻ x in {x | ENNReal.ofReal (c * t) < g x}, F x ∂μ := by
  refine Antitone.measurable fun s t hst => lintegral_mono_set fun x hx => ?_
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hst hc)) hx

/-- The integral of `t ^ (s - 1)` over the heights `0 < t` with `c t < a`, for `0 < s`. This is
`TauCeti.lintegral_indicator_ofReal_rpow_Ioi` with the exponent shifted by one. -/
private theorem lintegral_Ioi_indicator_rpow_sub_one {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator (fun t => ENNReal.ofReal (t ^ (s - 1))) t =
      ENNReal.ofReal (c ^ (-s) / s) * a ^ s := by
  simpa using lintegral_indicator_ofReal_rpow_Ioi (s := s - 1) (by linarith) hc a

/-- **The truncated power through its level sets.** For `0 ≤ t₀` and `0 < ε`, the power
`min(b, k)^ε` is at most `t₀^ε` plus `ε` times the integral of `t^(ε - 1)` over the heights
`t₀ < t < k` lying below `b`. -/
private theorem min_rpow_le_add_mul_setLIntegral {t₀ ε : ℝ} (ht₀ : 0 ≤ t₀) (hε : 0 < ε)
    (b : ℝ≥0∞) (n : ℕ) :
    min b n ^ ε ≤ ENNReal.ofReal (t₀ ^ ε) + ENNReal.ofReal ε *
      ∫⁻ t in Ioo t₀ n, {t : ℝ | ENNReal.ofReal t < b}.indicator
        (fun t => ENNReal.ofReal (t ^ (ε - 1))) t := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (ε - 1))
  have hw : Measurable w := by fun_prop
  have hT : MeasurableSet {t : ℝ | ENNReal.ofReal t < b} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hTn : MeasurableSet {t : ℝ | ENNReal.ofReal (1 * t) < min b n} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_const_mul 1)) measurable_const
  -- The heights below `min(b, n)` lie below `t₀`, or between `t₀` and `n` and below `b`.
  have hsub : {t : ℝ | ENNReal.ofReal (1 * t) < min b n} ∩ Ioi 0 ⊆
      Ioc 0 t₀ ∪ {t : ℝ | ENNReal.ofReal t < b} ∩ Ioo t₀ n := by
    rintro t ⟨ht, ht0⟩
    rw [Set.mem_ofPred_eq, one_mul, lt_min_iff] at ht
    rcases le_or_gt t t₀ with htt₀ | htt₀
    · exact Or.inl ⟨ht0, htt₀⟩
    · refine Or.inr ⟨ht.1, htt₀, ?_⟩
      have := ht.2
      rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff'] at this
      exact this.1
  have hlow : ∫⁻ t in Ioc 0 t₀, w t = ENNReal.ofReal (t₀ ^ ε / ε) := by
    rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
    simpa using lintegral_ofReal_rpow_Ioo (s := ε - 1) (by linarith) ht₀
  have hbound : ENNReal.ofReal (1 / ε) * min b n ^ ε ≤ ENNReal.ofReal (t₀ ^ ε / ε) +
      ∫⁻ t in Ioo t₀ n, {t : ℝ | ENNReal.ofReal t < b}.indicator w t := by
    have h := lintegral_Ioi_indicator_rpow_sub_one hε one_pos (min b n)
    rw [Real.one_rpow] at h
    rw [← h, lintegral_indicator hTn, Measure.restrict_restrict hTn, ← hlow,
      lintegral_indicator hT, Measure.restrict_restrict hT]
    exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
  calc min b n ^ ε = ENNReal.ofReal ε * (ENNReal.ofReal (1 / ε) * min b n ^ ε) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hε.le, mul_one_div_cancel hε.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal ε * (ENNReal.ofReal (t₀ ^ ε / ε) +
          ∫⁻ t in Ioo t₀ n, {t : ℝ | ENNReal.ofReal t < b}.indicator w t) := by gcongr
    _ = _ := by
        rw [mul_add, ← ENNReal.ofReal_mul hε.le, mul_div_cancel₀ _ hε.ne']

/-- **The level integral of the `f`-term.** For `0 ≤ t₀`, `0 < η ≤ 1`, `1 ≤ q` and `0 < ε`,
the integral of `t^(q + ε - 2)` over the heights `t₀ < t < n` with `η t < b`, multiplied by `b`, is
at most `η^(-(q - 1 + ε)) / (q - 1 + ε)` times `b^q min(b, n)^ε`. -/
private theorem mul_setLIntegral_indicator_rpow_le {t₀ η q ε : ℝ} (ht₀ : 0 ≤ t₀) (hη : 0 < η)
    (hη1 : η ≤ 1) (hq : 1 ≤ q) (hε : 0 < ε) (b : ℝ≥0∞) (n : ℕ) :
    b * ∫⁻ t in Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (η * t) < b}.indicator
        (fun t => ENNReal.ofReal (t ^ (q + ε - 2))) t ≤
      ENNReal.ofReal (η ^ (-(q - 1 + ε)) / (q - 1 + ε)) * (b ^ q * min b n ^ ε) := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q + ε - 2))
  set B : ℝ := η ^ (-(q - 1 + ε)) / (q - 1 + ε)
  -- Below the height `n`, the cut-off `η t < b` is the cut-off `η t < m` for `m = min(b, η n)`.
  set m := min b (ENNReal.ofReal (η * n))
  have hmn : m ≤ min b n := by
    refine min_le_min_left _ ?_
    rw [← ENNReal.ofReal_natCast n]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (Nat.cast_nonneg n) hη1)
  have hΨ : ∫⁻ t in Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (η * t) < b}.indicator w t ≤
      ENNReal.ofReal B * m ^ (q - 1 + ε) := by
    have hmeq : ∀ t ∈ Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (η * t) < b}.indicator w t =
        {t : ℝ | ENNReal.ofReal (η * t) < m}.indicator w t := by
      intro t ht
      have hlt : ENNReal.ofReal (η * t) < ENNReal.ofReal (η * n) :=
        (ENNReal.ofReal_lt_ofReal_iff (by nlinarith [ht.1, ht.2])).2
          (mul_lt_mul_of_pos_left ht.2 hη)
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, m, lt_min_iff, hlt, and_true]
    rw [setLIntegral_congr_fun measurableSet_Ioo hmeq]
    refine (lintegral_mono_set (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi ht₀))).trans ?_
    have h := lintegral_Ioi_indicator_rpow_sub_one (by linarith : 0 < q - 1 + ε) hη m
    rw [show q - 1 + ε - 1 = q + ε - 2 by ring] at h
    exact h.le
  calc b * ∫⁻ t in Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (η * t) < b}.indicator w t
      ≤ b * (ENNReal.ofReal B * m ^ (q - 1 + ε)) := by gcongr
    _ = ENNReal.ofReal B * (b * (m ^ (q - 1) * m ^ ε)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hε.le]; ring
    _ ≤ ENNReal.ofReal B * (b * (b ^ (q - 1) * min b n ^ ε)) := by
        gcongr
        exact min_le_left _ _
    _ = ENNReal.ofReal B * (b ^ (1 : ℝ) * b ^ (q - 1) * min b n ^ ε) := by
        rw [ENNReal.rpow_one]; ring
    _ = ENNReal.ofReal B * (b ^ q * min b n ^ ε) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_nonneg.2 hq), add_sub_cancel]

/-- **The level integral of the `h`-term.** For `0 ≤ t₀`, `0 ≤ q` and `0 < ε`, the integral of
`t^(ε - 1)` over the heights `t₀ < t < n` with `t < b`, multiplied by `b^q`, is at most
`b^(q + ε) / ε`. -/
private theorem rpow_mul_setLIntegral_indicator_rpow_le {t₀ q ε : ℝ} (ht₀ : 0 ≤ t₀) (hq : 0 ≤ q)
    (hε : 0 < ε) (b : ℝ≥0∞) (n : ℕ) :
    b ^ q * ∫⁻ t in Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (1 * t) < b}.indicator
        (fun t => ENNReal.ofReal (t ^ (ε - 1))) t ≤
      ENNReal.ofReal (1 / ε) * b ^ (q + ε) := by
  have hD : Ioo t₀ (n : ℝ) ⊆ Ioi 0 := Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi ht₀)
  have hΧ := (lintegral_mono_set hD (μ := volume)
    (f := {t : ℝ | ENNReal.ofReal (1 * t) < b}.indicator
      (fun t => ENNReal.ofReal (t ^ (ε - 1))))).trans
    (lintegral_Ioi_indicator_rpow_sub_one hε one_pos b).le
  rw [Real.one_rpow] at hΧ
  calc b ^ q * ∫⁻ t in Ioo t₀ (n : ℝ), {t : ℝ | ENNReal.ofReal (1 * t) < b}.indicator
        (fun t => ENNReal.ofReal (t ^ (ε - 1))) t
      ≤ b ^ q * (ENNReal.ofReal (1 / ε) * b ^ ε) := by gcongr
    _ = ENNReal.ofReal (1 / ε) * b ^ (q + ε) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ hq hε.le]; ring

/-- The smallness condition `2 A ε ≤ (q - 1 + ε) η^(q - 1 + ε)` makes the coefficient of the
absorbed term at most `1/2`. -/
private theorem ofReal_mul_ofReal_mul_ofReal_le_inv_two {q ε A η : ℝ} (hq : 1 ≤ q) (hε : 0 < ε)
    (hη : 0 < η) (hεA : 2 * A * ε ≤ (q - 1 + ε) * η ^ (q - 1 + ε)) :
    ENNReal.ofReal ε * (ENNReal.ofReal A *
      ENNReal.ofReal (η ^ (-(q - 1 + ε)) / (q - 1 + ε))) ≤ 2⁻¹ := by
  have hs : 0 < q - 1 + ε := by linarith
  have hpow : 0 < η ^ (q - 1 + ε) := Real.rpow_pos_of_pos hη _
  rw [← ENNReal.ofReal_mul' (by positivity), ← ENNReal.ofReal_mul hε.le,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_neg hη.le, show ε * (A * ((η ^ (q - 1 + ε))⁻¹ / (q - 1 + ε))) =
    ε * A / ((q - 1 + ε) * η ^ (q - 1 + ε)) by field_simp, div_le_iff₀ (by positivity)]
  linarith

/-- The higher integrability bound for measurable functions with `∫ f^q < ∞`. -/
private theorem lintegral_rpow_add_le_of_measurable [SFinite μ] {f h : α → ℝ≥0∞}
    (hf : Measurable f) (hh : Measurable h) {q ε t₀ A η : ℝ} (hq : 1 ≤ q) (hε : 0 < ε)
    (ht₀ : 0 ≤ t₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hεA : 2 * A * ε ≤ (q - 1 + ε) * η ^ (q - 1 + ε))
    (hfq : ∫⁻ x, f x ^ q ∂μ ≠ ∞)
    (hlevel : ∀ t, t₀ ≤ t → ∫⁻ x in {x | ENNReal.ofReal t < f x}, f x ^ q ∂μ ≤
      ENNReal.ofReal (A * t ^ (q - 1)) * ∫⁻ x in {x | ENNReal.ofReal (η * t) < f x}, f x ∂μ +
        ∫⁻ x in {x | ENNReal.ofReal t < h x}, h x ^ q ∂μ) :
    ∫⁻ x, f x ^ (q + ε) ∂μ ≤
      2 * ENNReal.ofReal (t₀ ^ ε) * ∫⁻ x, f x ^ q ∂μ + 2 * ∫⁻ x, h x ^ (q + ε) ∂μ := by
  set I := ∫⁻ x, f x ^ q ∂μ
  set H := ∫⁻ x, h x ^ (q + ε) ∂μ
  set C := ENNReal.ofReal (t₀ ^ ε) * I
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  -- The truncated integrals `X n = ∫ f^q min(f, n)^ε`.
  set X : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, f x ^ q * min (f x) n ^ ε ∂μ
  have hXmeas : ∀ n : ℕ, Measurable fun x => f x ^ q * min (f x) n ^ ε := fun n => by
    fun_prop
  have hXmono : Monotone fun (n : ℕ) (x : α) => f x ^ q * min (f x) n ^ ε :=
    fun m n hmn x => by dsimp only; gcongr
  have hX : ∀ n : ℕ, X n ≤ 2 * C + 2 * H := by
    intro n
    set k : ℝ := (n : ℝ)
    set D : Set ℝ := Ioo t₀ k
    -- `X n` is finite, because of the truncation.
    have hXfin : X n ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfq
        (ENNReal.rpow_ne_top_of_nonneg hε.le (ENNReal.natCast_ne_top n))) ?_
      rw [← lintegral_mul_const _ (hf.pow_const q)]
      exact lintegral_mono fun x => by gcongr; exact min_le_right _ _
    set w₁ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (ε - 1))
    set w₂ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q + ε - 2))
    set J : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | ENNReal.ofReal (η * t) < f x}, f x ∂μ
    set K : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | ENNReal.ofReal (1 * t) < h x}, h x ^ q ∂μ
    have hJ : Measurable J := measurable_setLIntegral_lt hη.le
    have hK : Measurable K := measurable_setLIntegral_lt zero_le_one
    -- Step 1: the truncated power through its level sets.
    have hstep1 : X n ≤ C + ENNReal.ofReal ε * ∫⁻ x, f x ^ q *
        (∫⁻ t in D, {t : ℝ | ENNReal.ofReal (id t) < f x}.indicator w₁ t) ∂μ := by
      calc X n ≤ ∫⁻ x, ENNReal.ofReal (t₀ ^ ε) * f x ^ q + ENNReal.ofReal ε * (f x ^ q *
            ∫⁻ t in D, {t : ℝ | ENNReal.ofReal (id t) < f x}.indicator w₁ t) ∂μ := by
            refine lintegral_mono fun x => ?_
            calc f x ^ q * min (f x) n ^ ε ≤ f x ^ q * (ENNReal.ofReal (t₀ ^ ε) +
                ENNReal.ofReal ε * ∫⁻ t in D, {t : ℝ | ENNReal.ofReal t < f x}.indicator w₁ t) :=
                  by gcongr; exact min_rpow_le_add_mul_setLIntegral ht₀ hε (f x) n
              _ = _ := by simp only [id]; ring
        _ = C + ENNReal.ofReal ε * ∫⁻ x, f x ^ q *
            (∫⁻ t in D, {t : ℝ | ENNReal.ofReal (id t) < f x}.indicator w₁ t) ∂μ := by
            rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- Step 2: Tonelli, and the level-set estimate at every height `t ∈ D`.
    have hstep2 : ∫⁻ x, f x ^ q *
        (∫⁻ t in D, {t : ℝ | ENNReal.ofReal (id t) < f x}.indicator w₁ t) ∂μ ≤
        ENNReal.ofReal A * (∫⁻ t in D, w₂ t * J t) + ∫⁻ t in D, w₁ t * K t := by
      have hw₂J : Measurable fun t => w₂ t * J t := (by fun_prop : Measurable w₂).mul hJ
      have hAw₂J : Measurable fun t => ENNReal.ofReal A * (w₂ t * J t) :=
        measurable_const.mul hw₂J
      rw [← lintegral_mul_setLIntegral_eq hf (hf.pow_const q) measurable_id (by fun_prop)]
      calc ∫⁻ t in D, w₁ t * ∫⁻ x in {x | ENNReal.ofReal (id t) < f x}, f x ^ q ∂μ
          ≤ ∫⁻ t in D, ENNReal.ofReal A * (w₂ t * J t) + w₁ t * K t := by
            refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
            have ht0 : 0 < t := ht₀.trans_lt ht.1
            have hw : w₁ t * ENNReal.ofReal (t ^ (q - 1)) = w₂ t := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_add ht0]
              congr 2; ring
            calc w₁ t * ∫⁻ x in {x | ENNReal.ofReal (id t) < f x}, f x ^ q ∂μ
                ≤ w₁ t * (ENNReal.ofReal (A * t ^ (q - 1)) * J t + K t) := by
                  simpa [K] using mul_le_mul' (le_refl (w₁ t)) (hlevel t ht.1.le)
              _ = ENNReal.ofReal A * (w₂ t * J t) + w₁ t * K t := by
                  rw [ENNReal.ofReal_mul' (Real.rpow_nonneg ht0.le _), mul_add, ← hw]; ring
        _ = ENNReal.ofReal A * (∫⁻ t in D, w₂ t * J t) + ∫⁻ t in D, w₁ t * K t := by
            rw [lintegral_add_left hAw₂J, lintegral_const_mul _ hw₂J]
    -- Step 3: the `f`-term is at most a multiple of the truncated integral `X n`.
    set B : ℝ := η ^ (-(q - 1 + ε)) / (q - 1 + ε)
    have hstep3 : ∫⁻ t in D, w₂ t * J t ≤ ENNReal.ofReal B * X n := by
      rw [lintegral_mul_setLIntegral_eq hf hf (measurable_const_mul η) (by fun_prop),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun x => mul_setLIntegral_indicator_rpow_le ht₀ hη hη1 hq hε (f x) n
    -- Step 4: the `h`-term is at most `∫ h^(q + ε) / ε`.
    have hstep4 : ∫⁻ t in D, w₁ t * K t ≤ ENNReal.ofReal (1 / ε) * H := by
      rw [lintegral_mul_setLIntegral_eq hh (hh.pow_const q) (measurable_const_mul 1)
        (by fun_prop), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun x => rpow_mul_setLIntegral_indicator_rpow_le ht₀ hq0 hε (h x) n
    -- Step 5: absorb half of `X n` into the left side.
    have hcoef := ofReal_mul_ofReal_mul_ofReal_le_inv_two hq hε hη hεA
    have habsorb : X n ≤ C + H + 2⁻¹ * X n := by
      calc X n ≤ C + ENNReal.ofReal ε *
            (ENNReal.ofReal A * (ENNReal.ofReal B * X n) + ENNReal.ofReal (1 / ε) * H) := by
            refine hstep1.trans (add_le_add le_rfl (mul_le_mul' le_rfl (hstep2.trans ?_)))
            exact add_le_add (mul_le_mul' le_rfl hstep3) hstep4
        _ = C + (ENNReal.ofReal ε * (ENNReal.ofReal A * ENNReal.ofReal B)) * X n +
            (ENNReal.ofReal ε * ENNReal.ofReal (1 / ε)) * H := by ring
        _ ≤ C + 2⁻¹ * X n + 1 * H := by
            gcongr
            rw [← ENNReal.ofReal_mul hε.le, mul_one_div_cancel hε.ne', ENNReal.ofReal_one]
        _ = C + H + 2⁻¹ * X n := by ring
    have hhalf : 2⁻¹ * X n ≤ C + H := by
      refine ENNReal.le_of_add_le_add_right (a := 2⁻¹ * X n)
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 two_ne_zero) hXfin) ?_
      rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      exact habsorb
    calc X n = 2 * (2⁻¹ * X n) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * (C + H) := by gcongr
      _ = 2 * C + 2 * H := mul_add _ _ _
  -- Let the truncation height tend to infinity.
  have hfin : ∀ᵐ x ∂μ, f x ≠ ∞ := by
    filter_upwards [ae_lt_top (hf.pow_const q) hfq] with x hx hxtop
    rw [hxtop, ENNReal.top_rpow_of_pos (by linarith)] at hx
    exact lt_irrefl _ hx
  calc ∫⁻ x, f x ^ (q + ε) ∂μ ≤ ∫⁻ x, ⨆ n : ℕ, f x ^ q * min (f x) n ^ ε ∂μ := by
        refine lintegral_mono_ae (hfin.mono fun x hx => ?_)
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
        refine le_iSup_of_le n ?_
        rw [min_eq_left hn.le, ENNReal.rpow_add_of_nonneg _ _ hq0 hε.le]
    _ = ⨆ n : ℕ, X n := lintegral_iSup hXmeas hXmono
    _ ≤ 2 * C + 2 * H := iSup_le hX
    _ = 2 * ENNReal.ofReal (t₀ ^ ε) * I + 2 * H := by rw [mul_assoc]

/-- **The level-set integration step of Gehring's lemma.** Let `f, h ≥ 0` be almost everywhere
measurable with `∫ f^q < ∞`, where `1 ≤ q`. Suppose that for some `0 ≤ t₀`, some `A` and some
`0 < η ≤ 1`, every height `t ≥ t₀` satisfies the level-set estimate

`∫_{f > t} f^q ≤ A t^(q - 1) ∫_{f > η t} f + ∫_{h > t} h^q`.

Then for every `ε > 0` with `2 A ε ≤ (q - 1 + ε) η^(q - 1 + ε)`,

`∫ f^(q + ε) ≤ 2 t₀^ε ∫ f^q + 2 ∫ h^(q + ε)`.

In particular `f ∈ L^(q + ε)` whenever `h ∈ L^(q + ε)`. Such an `ε` exists: for `q > 1` every
`0 < ε ≤ 1` with `2 A ε ≤ (q - 1) η^q` qualifies. -/
theorem lintegral_rpow_add_le_of_setLIntegral_rpow_le [SFinite μ] {f h : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) {q ε t₀ A η : ℝ} (hq : 1 ≤ q) (hε : 0 < ε)
    (ht₀ : 0 ≤ t₀) (hη : 0 < η) (hη1 : η ≤ 1)
    (hεA : 2 * A * ε ≤ (q - 1 + ε) * η ^ (q - 1 + ε))
    (hfq : ∫⁻ x, f x ^ q ∂μ ≠ ∞)
    (hlevel : ∀ t, t₀ ≤ t → ∫⁻ x in {x | ENNReal.ofReal t < f x}, f x ^ q ∂μ ≤
      ENNReal.ofReal (A * t ^ (q - 1)) * ∫⁻ x in {x | ENNReal.ofReal (η * t) < f x}, f x ∂μ +
        ∫⁻ x in {x | ENNReal.ofReal t < h x}, h x ^ q ∂μ) :
    ∫⁻ x, f x ^ (q + ε) ∂μ ≤
      2 * ENNReal.ofReal (t₀ ^ ε) * ∫⁻ x, f x ^ q ∂μ + 2 * ∫⁻ x, h x ^ (q + ε) ∂μ := by
  -- Replace `f` and `h` by measurable modifications; the superlevel sets change by null sets.
  have hset : ∀ {g g' Φ Φ' : α → ℝ≥0∞}, g =ᵐ[μ] g' → Φ =ᵐ[μ] Φ' → ∀ c : ℝ,
      ∫⁻ x in {x | ENNReal.ofReal c < g x}, Φ x ∂μ =
        ∫⁻ x in {x | ENNReal.ofReal c < g' x}, Φ' x ∂μ := by
    intro g g' Φ Φ' hgg' hΦ c
    have hs : {x | ENNReal.ofReal c < g x} =ᵐ[μ] {x | ENNReal.ofReal c < g' x} :=
      hgg'.preimage (Ioi (ENNReal.ofReal c))
    rw [Measure.restrict_congr_set hs]
    exact lintegral_congr_ae (ae_restrict_of_ae hΦ)
  have hpow : ∀ {g g' : α → ℝ≥0∞}, g =ᵐ[μ] g' → ∀ p : ℝ,
      (fun x => g x ^ p) =ᵐ[μ] fun x => g' x ^ p := fun hgg' p =>
    hgg'.mono fun x hx => by simp only [hx]
  have hf' := hf.ae_eq_mk
  have hh' := hh.ae_eq_mk
  rw [lintegral_congr_ae (hpow hf' q)] at hfq
  rw [lintegral_congr_ae (hpow hf' (q + ε)), lintegral_congr_ae (hpow hf' q),
    lintegral_congr_ae (hpow hh' (q + ε))]
  refine lintegral_rpow_add_le_of_measurable hf.measurable_mk hh.measurable_mk hq hε ht₀ hη hη1
    hεA hfq fun t ht => ?_
  have := hlevel t ht
  rwa [hset hf' (hpow hf' q) t, hset hf' hf' (η * t), hset hh' (hpow hh' q) t] at this

end TauCeti
