/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Measurability, reciprocal continuity, and ratio asymptotics of the real Gamma function

`Real.Gamma` is smooth away from the nonpositive integers and has a pole at each of them, so it is
neither continuous nor locally bounded on all of `ℝ`. It is nevertheless Borel measurable, because
the set of its singularities is countable.

Mathlib records the analytic side of this (`Real.differentiableAt_Gamma`,
`Real.not_continuousAt_Gamma_neg_nat`) but never draws the measurability conclusion. It is needed
as soon as a formula containing `Real.Gamma s` is integrated or measured *in the variable `s`* —
for instance for the normalizing constants of the Gamma and Beta densities, which is why their
family-specific measurability modules use this result.

The reciprocal `(Real.Gamma s)⁻¹`, on the other hand, is continuous on all of `ℝ`: Mathlib's
convention `Real.Gamma (-n) = 0` makes it vanish at the poles, matching the zeros of the entire
function `1 / Γ`. It is bounded on every half-line `[a, ∞)`, which is what uniform estimates for
series with coefficients `1 / Γ(b + n)`, such as hypergeometric and Bessel series, need.

Finally, the rising factorial is recorded as a quotient of real Gamma values, and Mathlib's Euler
limit formula `Real.GammaSeq_tendsto_Gamma` is recast as the asymptotic
equivalence `Γ(n + 1 + s) ~ n ^ s * n!` along the natural numbers, valid for every real shift `s`.
This is the form in which polynomial decay of Gamma quotients such as `Γ(n + a) / Γ(n + b)` enters
summability and moment arguments for discrete laws with Beta-function masses.

## Main results

* `Real.measurable_Gamma` — `Real.Gamma` is measurable.
* `Real.continuous_inv_Gamma` — `s ↦ (Real.Gamma s)⁻¹` is continuous.
* `TauCeti.continuous_Gamma_sum_div_prod` — the finite Gamma quotient is jointly continuous on
  positive parameters.
* `Real.exists_abs_inv_Gamma_le` — `(Real.Gamma s)⁻¹` is bounded on `[a, ∞)`.
* `Real.Gamma_add_nat_div_Gamma_eq` — `Γ(x + n) / Γ x` is the rising factorial `x (x + 1) ⋯`.
* `Real.prod_range_add_mul_Gamma` — `s (s + 1) ⋯ (s + n - 1) Γ s = Γ(s + n)` for positive `s`.
* `Real.isEquivalent_Gamma_natCast_add_one_add` — `Γ(n + 1 + s) ~ n ^ s * n!` as `n → ∞`.
* `Real.tendsto_Gamma_natCast_add_div_Gamma_natCast_add_atTop` — `Γ(n + a) / Γ(n + b) → 0` for
  `a < b`.
-/

public section

open Filter Asymptotics Topology
open scoped Nat

namespace TauCeti

/-- The real Gamma function is Borel measurable on all of `ℝ`, including at its poles. -/
@[fun_prop]
theorem _root_.Real.measurable_Gamma : Measurable Real.Gamma := by
  refine measurable_of_countable_not_continuousAt (Set.Countable.mono ?_
    (Set.countable_range fun m : ℕ => -(m : ℝ)))
  intro s hs
  by_contra hrange
  exact hs (Real.differentiableAt_Gamma fun m hm => hrange ⟨m, hm.symm⟩).continuousAt

/-- The reciprocal of the real Gamma function is continuous on all of `ℝ`, including at the poles
of `Real.Gamma`, where both it and the entire function `1 / Γ` vanish. -/
@[fun_prop]
theorem _root_.Real.continuous_inv_Gamma : Continuous fun s : ℝ => (Real.Gamma s)⁻¹ := by
  have h : (fun s : ℝ => (Real.Gamma s)⁻¹) = fun s : ℝ => ((Complex.Gamma s)⁻¹).re := by
    ext s
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp
    (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal)

/-- For a nonempty finite family of positive parameters, the Gamma quotient
`Γ(∑ i, a i) / ∏ i, Γ(a i)` is jointly continuous. -/
@[fun_prop]
theorem continuous_Gamma_sum_div_prod {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (fun a : ι → Set.Ioi (0 : ℝ) ↦
      Real.Gamma (∑ i, (a i : ℝ)) / ∏ i, Real.Gamma (a i)) := by
  have hΓ := Real.differentiableOn_Gamma_Ioi.continuousOn
  have hc (i : ι) : Continuous (fun a : ι → Set.Ioi (0 : ℝ) ↦ (a i : ℝ)) := by
    fun_prop
  exact (hΓ.comp_continuous (by fun_prop)
    (fun a ↦ Finset.sum_pos (fun i _ ↦ (a i).2) Finset.univ_nonempty)).div
    (continuous_finsetProd _ fun i _ ↦ hΓ.comp_continuous (hc i) fun a ↦ (a i).2)
    (fun a ↦ Finset.prod_ne_zero_iff.mpr fun i _ ↦ (Real.Gamma_pos_of_pos (a i).2).ne')

/-- The reciprocal of the real Gamma function is bounded on every half-line `[a, ∞)`. -/
theorem _root_.Real.exists_abs_inv_Gamma_le (a : ℝ) :
    ∃ C, ∀ s, a ≤ s → |(Real.Gamma s)⁻¹| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_inv_Gamma.continuousOn (s := Set.Icc a 2))
  refine ⟨max C 1, fun s hs => ?_⟩
  rcases le_total s 2 with h | h
  · exact (hC s ⟨hs, h⟩).trans (le_max_left _ _)
  · have h1 : 1 ≤ Real.Gamma s := Real.Gamma_two ▸
      Real.Gamma_strictMonoOn_Ici.monotoneOn Set.self_mem_Ici h h
    rw [abs_inv, abs_of_pos (by linarith)]
    exact (inv_le_one_of_one_le₀ h1).trans (le_max_right _ _)

end TauCeti

namespace Real

/-- The ascending Pochhammer symbol is given by the ratio of real `Γ` values; this is the real
counterpart of `Complex.Gamma_add_nat_div_Gamma_eq`. -/
theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (x : ℝ) (hx : ∀ k : ℕ, x ≠ -k) :
    Gamma (x + n) / Gamma x = (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [Gamma_ne_zero hx]
  | succ n ih =>
    have hxn : x + n ≠ 0 := fun h => hx n (by linarith)
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_natCast, ← ih, Nat.cast_succ, ← add_assoc, Gamma_add_one hxn]
    ring

/-- The product `s (s + 1) ⋯ (s + n - 1)` times `Γ s` is `Γ (s + n)`, for positive `s`. -/
theorem prod_range_add_mul_Gamma {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∏ j ∈ Finset.range n, (s + j)) * Gamma s = Gamma (s + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, Nat.cast_succ, ← add_assoc,
      Gamma_add_one (by positivity), mul_comm]

/-- The positive-shift case of `isEquivalent_Gamma_natCast_add_one_add`, read off from Euler's
limit `GammaSeq s n → Γ s`. -/
private theorem isEquivalent_Gamma_natCast_add_one_add_of_pos {s : ℝ} (hs : 0 < s) :
    (fun n : ℕ => Gamma (n + 1 + s)) ~[atTop] fun n => (n : ℝ) ^ s * n ! := by
  refine isEquivalent_of_tendsto_one ?_
  have hΓ := (Gamma_pos_of_pos hs).ne'
  have hlim : Tendsto (fun n => Gamma s / GammaSeq s n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := Gamma s)).div (GammaSeq_tendsto_Gamma s) hΓ
    rwa [div_self hΓ] at this
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hprod := prod_range_add_mul_Gamma hs (n + 1)
  have hpos : 0 < ∏ j ∈ Finset.range (n + 1), (s + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [Pi.div_apply, GammaSeq, show (n : ℝ) + 1 + s = s + ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    ← hprod]
  field_simp

/-- **Euler's limit formula in ratio form.** For every real `s`, `Γ(n + 1 + s)` is asymptotic to
`n ^ s * n!` as the natural number `n` tends to infinity. -/
theorem isEquivalent_Gamma_natCast_add_one_add (s : ℝ) :
    (fun n : ℕ => Gamma (n + 1 + s)) ~[atTop] fun n => (n : ℝ) ^ s * n ! := by
  -- Lower the shift one unit at a time, starting from a positive value of the shift.
  suffices h : ∀ N : ℕ, ∀ s : ℝ, 0 < s + N →
      (fun n : ℕ => Gamma (n + 1 + s)) ~[atTop] fun n => (n : ℝ) ^ s * (n ! : ℝ) by
    obtain ⟨N, hN⟩ := exists_nat_gt (-s)
    exact h N s (by linarith)
  intro N
  induction N with
  | zero => exact fun s hs => isEquivalent_Gamma_natCast_add_one_add_of_pos (by simpa using hs)
  | succ N ih =>
    intro s hs
    have hshift := ih (s + 1) (by push_cast at hs; linarith)
    have hlin : (fun n : ℕ => (n : ℝ) + (1 + s)) ~[atTop] fun n => (n : ℝ) :=
      IsEquivalent.refl.add_isLittleO
        ((isLittleO_const_id_atTop (1 + s)).comp_tendsto tendsto_natCast_atTop_atTop)
    refine ((hshift.div hlin).congr_left ?_).congr_right ?_
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (-(1 + s))] with n hn
      have hne : (n : ℝ) + 1 + s ≠ 0 := by linarith
      simp only [Pi.div_apply]
      rw [show (n : ℝ) + 1 + (s + 1) = (n + 1 + s) + 1 by ring, Gamma_add_one hne, add_assoc,
        mul_div_cancel_left₀ _ (by rwa [← add_assoc])]
    · filter_upwards [eventually_ne_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [Pi.div_apply]
      rw [rpow_add_one hn'.ne']
      field_simp

/-- The Gamma quotients `Γ(n + a) / Γ(n + b)` tend to zero along the natural numbers when `a < b`,
since they decay like `n ^ (a - b)`. -/
theorem tendsto_Gamma_natCast_add_div_Gamma_natCast_add_atTop {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ => Gamma (n + a) / Gamma (n + b)) atTop (𝓝 0) := by
  have hequiv := (isEquivalent_Gamma_natCast_add_one_add (a - 1)).div
    (isEquivalent_Gamma_natCast_add_one_add (b - 1))
  have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  refine ((hequiv.symm.tendsto_nhds (hlim.congr' ?_)).congr' ?_)
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hfac : (n ! : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply, Pi.div_apply]
    rw [show -(b - a) = (a - 1) - (b - 1) by ring, rpow_sub hn']
    field_simp
  · refine Eventually.of_forall fun n => ?_
    simp only [Pi.div_apply]
    rw [show (n : ℝ) + 1 + (a - 1) = n + a by ring, show (n : ℝ) + 1 + (b - 1) = n + b by ring]

end Real
