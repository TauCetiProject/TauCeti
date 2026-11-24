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
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Measurability, reciprocal bounds, and ratio asymptotics of the Gamma function

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
For a complex parameter the corresponding estimate is the factorial decay of `1 / Γ(s + n)` on
the half-plane `1 ≤ Re s`.

Finally, the rising factorial is recorded as a quotient of real Gamma values, and the asymptotic
equivalence `Γ(n + 1 + s) ~ n ^ s * n!` along the natural numbers, valid for every real shift `s`,
is read off from the real-variable Gamma-ratio asymptotic proved from Wendel's inequalities.
This is the form in which polynomial decay of Gamma quotients such as `Γ(n + a) / Γ(n + b)` enters
summability and moment arguments for discrete laws with Beta-function masses. Euler's reflection
formula is also recorded in the reciprocal form `Γ(s) sin (π s) = π / Γ(1 - s)` for `s ∉ -ℕ`,
valid including at positive integers where both sides vanish. Over `ℂ`, Euler's
limit formula is also written with the rising factorial `(s)ₙ = s (s + 1) ⋯ (s + n - 1)`:
`n^(s - 1) n! / (s)ₙ → Γ(s)` and `(s)ₙ / (n^(s - 1) n!) → 1 / Γ(s)` for every complex `s`, both
sides of either limit being `0` at the poles `s = -k`. For `s` off the poles, where `Γ(s) ≠ 0`,
the second limit is the asymptotic equivalence `(s)ₙ ∼ n^(s - 1) n! / Γ(s)`; the normalized limit,
valid for every `s`, is the form from which the growth of hypergeometric coefficients is read off.

## Main results

* `Real.measurable_Gamma` — `Real.Gamma` is measurable.
* `Real.continuous_inv_Gamma` — `s ↦ (Real.Gamma s)⁻¹` is continuous.
* `TauCeti.continuous_Gamma_sum_div_prod` — the finite Gamma quotient is jointly continuous on
  positive parameters.
* `Real.exists_abs_inv_Gamma_le` — `(Real.Gamma s)⁻¹` is bounded on `[a, ∞)`.
* `Real.Gamma_add_nat_div_Gamma_eq` — `Γ(x + n) / Γ x` is the rising factorial `x (x + 1) ⋯`.
* `Real.prod_range_add_mul_Gamma` — `s (s + 1) ⋯ (s + n - 1) Γ s = Γ(s + n)` for positive `s`.
* `Real.Gamma_le_one_of_mem_Icc` — `Γ s ≤ 1` for `s ∈ [1, 2]`.
* `Real.Gamma_nat_add_half_eq_factorial` — `Γ(n + 1 / 2) = (2 n)! √π / (4 ^ n n!)`.
* `Real.Gamma_three_halves` — `Γ(3 / 2) = √π / 2`.
* `Real.isEquivalent_Gamma_natCast_add_one_add` — `Γ(n + 1 + s) ~ n ^ s * n!` as `n → ∞`.
* `Real.tendsto_Gamma_natCast_add_div_Gamma_natCast_add_atTop` — `Γ(n + a) / Γ(n + b) → 0` for
  `a < b`.
* `Complex.Gamma_add_natCast_eq_ascPochhammer_eval_mul` — `Γ(c + k) = (c)ₖ Γ(c)` off the poles.
* `Complex.ne_neg_natCast_of_re_pos`, `Complex.Gamma_ne_zero_of_im_ne_zero` — parameters with
  positive real part or nonzero imaginary part avoid `−ℕ`, so `Complex.Gamma` does not vanish off
  the real axis.
* `Complex.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add` and
  `Real.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add` — the pole-free reciprocal identity
  `(Γ s)⁻¹ = s (s + 1) ⋯ (s + n - 1) (Γ(s + n))⁻¹`, valid at every `s`.
* `Complex.ne_neg_natCast_of_neg_one_lt_re_of_ne_zero`,
  `Real.ne_neg_natCast_of_neg_one_lt_of_ne_zero` — a nonzero parameter strictly to the right of
  `-1` avoids `−ℕ`.
* `Real.sub_natCast_ne_neg_natCast` — a real number strictly between `0` and `1`, shifted left by
  a natural number, avoids `−ℕ`.
* `Real.neg_one_pow_div_factorial_mul_Gamma_sub_natCast` — the reflection formula at `c - k`:
  `(-1)^k / k! · Γ(c - k) = (π / sin πc) / (k! Γ(1 - c + k))` when `sin πc ≠ 0`.
* `Real.ne_neg_natCast_of_mem_Ioo` — a real number strictly between `-(k + 1)` and `-k` avoids
  `−ℕ`.
* `Complex.norm_inv_Gamma_add_natCast_le` — `‖1 / Γ(s + k)‖ ≤ ‖1 / Γ(s)‖ / k!` for `1 ≤ Re s`, the
  complex counterpart of the half-line bound used for series with coefficients `1 / Γ(b + k)`.
* `Real.inv_Gamma_add_natCast_le` — `(Γ(s + k))⁻¹ ≤ (Γ s)⁻¹ / k!` for `1 ≤ s`, the real
  specialization giving factorial decay of the reciprocal Gamma function along natural-number
  shifts on `[1, ∞)`.
* `Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast`,
  `Real.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast` — `(Γ s)⁻¹ = (s)_n (Γ(s + n))⁻¹`
  for all `s` and `n`, including at the nonpositive integer poles of `Γ`.
* `Complex.Gamma_mul_sin_pi_mul` — Euler's reflection formula in reciprocal form:
  `Γ(s) * sin (π * s) = π / Γ(1 - s)` for `s ∉ -ℕ`, including at positive integers where both
  sides vanish.
* `Complex.Gamma_one_third_mul_Gamma_two_thirds` — `Γ(1/3) Γ(2/3) = 2π/√3`.
* `Complex.tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval`:
  `n^(s - 1) n! / (s)ₙ → Γ(s)` (DLMF 5.8.1 in Pochhammer form).
* `Complex.tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial`:
  `(s)ₙ / (n^(s - 1) n!) → (Γ(s))⁻¹`.
* `Complex.isEquivalent_factorial_div_ascPochhammer_eval_succ`:
  `n! / (s)ₙ₊₁ ~ Γ(s) n^(-s)` for `s ∉ {0, -1, -2, …}`.

## References

* NIST Digital Library of Mathematical Functions, 5.8.1, <https://dlmf.nist.gov/5.8.E1>.

The two Pochhammer forms of Euler's limit formula are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Hypergeometric/Basic/GaussSeries.lean`.
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

/-- For a finite family of positive parameters, the Gamma quotient
`Γ(∑ i, a i) / ∏ i, Γ(a i)` is jointly continuous. -/
@[fun_prop]
theorem continuous_Gamma_sum_div_prod {ι : Type*} [Fintype ι] :
    Continuous (fun a : ι → Set.Ioi (0 : ℝ) ↦
      Real.Gamma (∑ i, (a i : ℝ)) / ∏ i, Real.Gamma (a i)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    -- With no parameters, the quotient is constant.
    simpa using (continuous_const : Continuous (fun _ : ι → Set.Ioi (0 : ℝ) ↦ Real.Gamma 0))
  | inr h =>
    let := h
    have hΓ := Real.differentiableOn_Gamma_Ioi.continuousOn
    have hc (i : ι) : Continuous (fun a : ι → Set.Ioi (0 : ℝ) ↦ (a i : ℝ)) := by
      fun_prop
    exact (hΓ.comp_continuous (by fun_prop)
      (fun a ↦ Finset.sum_pos (fun i _ ↦ (a i).property) Finset.univ_nonempty)).div
      (continuous_finsetProd _ fun i _ ↦ hΓ.comp_continuous (hc i) fun a ↦ (a i).property)
      (fun a ↦ Finset.prod_ne_zero_iff.mpr fun i _ ↦ (Real.Gamma_pos_of_pos (a i).property).ne')

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

/-- The real Gamma function is at most `1` on `[1, 2]`: it is convex there, with
`Γ 1 = Γ 2 = 1`. -/
theorem Gamma_le_one_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) 2) : Gamma s ≤ 1 := by
  simpa [Gamma_one, Gamma_two] using
    convexOn_Gamma.le_max_of_mem_Icc (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by norm_num) hs

/-- The half-integer value `Γ(n + 1 / 2) = (2 n)! √π / (4 ^ n n!)`, the factorial form of
`Real.Gamma_nat_add_half`, obtained from Legendre's duplication formula at `n + 1 / 2`. -/
theorem Gamma_nat_add_half_eq_factorial (n : ℕ) :
    Gamma (n + 1 / 2) = (2 * n)! * √π / (4 ^ n * n !) := by
  -- the arguments and exponent of duplication at `n + 1 / 2`, rewritten as natural-number casts
  have hshift : (n : ℝ) + 1 / 2 + 1 / 2 = n + 1 := by ring
  have hdouble : 2 * ((n : ℝ) + 1 / 2) = ((2 * n : ℕ) : ℝ) + 1 := by push_cast; ring
  have hexp : (1 : ℝ) - (((2 * n : ℕ) : ℝ) + 1) = -((2 * n : ℕ) : ℝ) := by ring
  have hfour : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have h := Gamma_mul_Gamma_add_half ((n : ℝ) + 1 / 2)
  rw [hshift, hdouble, hexp, Gamma_nat_eq_factorial, Gamma_nat_eq_factorial,
    rpow_neg zero_le_two, rpow_natCast] at h
  rw [eq_div_iff (by positivity), hfour, mul_left_comm, h]
  field_simp

/-- The half-integer value `Γ(3 / 2) = √π / 2`: the case `n = 1` of
`Real.Gamma_nat_add_half_eq_factorial`. -/
theorem Gamma_three_halves : Gamma (3 / 2) = √π / 2 := by
  have h := Gamma_nat_add_half_eq_factorial 1
  have harg : ((1 : ℕ) : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  have hval : ((2 * 1)! : ℝ) * √π / (4 ^ 1 * (1 : ℕ)!) = √π / 2 := by
    simp only [mul_one, Nat.factorial_two, Nat.factorial_one, Nat.cast_ofNat, Nat.cast_one,
      pow_one]
    ring
  rwa [harg, hval] at h

/-- **Euler's limit formula in ratio form.** For every real `s`, `Γ(n + 1 + s)` is asymptotic to
`n ^ s * n!` as the natural number `n` tends to infinity: the case `x = n` of
`Γ(x + 1)/Γ(x + (1 + s)) ∼ x^{-s}` (`Real.isEquivalent_Gamma_add_one_div_Gamma_add`), inverted
and multiplied by `Γ(n + 1) = n!`. -/
theorem isEquivalent_Gamma_natCast_add_one_add (s : ℝ) :
    (fun n : ℕ => Gamma (n + 1 + s)) ~[atTop] fun n => (n : ℝ) ^ s * n ! := by
  have h := (((isEquivalent_Gamma_add_one_div_Gamma_add (1 + s)).comp_tendsto
    tendsto_natCast_atTop_atTop).inv).mul (IsEquivalent.refl (u := fun n : ℕ => (n ! : ℝ)))
  refine (h.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall fun n => ?_
    have hfac : (n ! : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply, Pi.inv_apply, Pi.mul_apply]
    rw [Gamma_nat_eq_factorial, add_assoc]
    field_simp
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [Function.comp_apply, Pi.inv_apply, Pi.mul_apply]
    rw [sub_add_cancel_left, rpow_neg hn'.le, inv_inv]

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

namespace Complex

/-- `Γ(c + k) = (c)ₖ Γ(c)` for `c` off the poles of `Γ`. -/
theorem Gamma_add_natCast_eq_ascPochhammer_eval_mul {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) (k : ℕ) :
    Gamma (c + k) = (ascPochhammer ℂ k).eval c * Gamma c := by
  rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ (Gamma_ne_zero hc)]

/-- A complex number with positive real part is not a nonpositive integer. -/
theorem ne_neg_natCast_of_re_pos {b : ℂ} (hb : 0 < b.re) (n : ℕ) :
    b ≠ -(n : ℂ) := by
  intro h
  have heq := congrArg re h
  simp only [neg_re, natCast_re] at heq
  linarith [n.cast_nonneg (α := ℝ)]

/-- `Complex.Gamma` does not vanish off the real axis. -/
theorem Gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gamma z ≠ 0 :=
  Gamma_ne_zero fun n hn ↦ hz (by simp [hn])

/-- The reciprocal Gamma function satisfies `(Γ s)⁻¹ = s (s + 1) ⋯ (s + n - 1) (Γ(s + n))⁻¹`
for every complex `s`, including at the nonpositive integer poles where `(Γ s)⁻¹ = 0`. -/
theorem inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (s : ℂ) (n : ℕ) :
    (Gamma s)⁻¹ = (ascPochhammer ℂ n).eval s * (Gamma (s + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n), ascPochhammer_succ_eval,
      Nat.cast_succ, ← add_assoc]
    ring

/-- A nonzero complex number with `Re z > -1` is not a nonpositive integer. -/
theorem ne_neg_natCast_of_neg_one_lt_re_of_ne_zero {z : ℂ} (hz₀ : -1 < z.re) (hz : z ≠ 0)
    (n : ℕ) : z ≠ -(n : ℂ) := by
  rcases n with _ | k
  · simpa using hz
  · intro hn
    have hre := congrArg re hn
    simp only [neg_re, Nat.cast_add, Nat.cast_one, add_re, natCast_re, one_re] at hre
    linarith [k.cast_nonneg (α := ℝ)]

/-- On the half-plane `1 ≤ Re s`, the reciprocal Gamma function decays factorially along
`s + k`: `‖1 / Γ(s + k)‖ ≤ ‖1 / Γ(s)‖ / k!`. Together with the boundedness of `1 / Γ` on compact
sets, this gives locally uniform bounds for series with coefficients `1 / Γ(b + k)` as functions
of a complex parameter `b`. -/
theorem norm_inv_Gamma_add_natCast_le {s : ℂ} (hs : 1 ≤ s.re) (k : ℕ) :
    ‖(Gamma (s + k))⁻¹‖ ≤ ‖(Gamma s)⁻¹‖ / k ! := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : ℝ) ≤ ‖s + k‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      rw [add_re, natCast_re, Nat.cast_succ]
      linarith
    -- `1 / Γ(s + k) = (s + k) / Γ(s + k + 1)`
    have hrec : ‖(Gamma (s + k))⁻¹‖ = ‖s + k‖ * ‖(Gamma (s + (k + 1 : ℕ)))⁻¹‖ := by
      rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + k), norm_mul, Nat.cast_succ,
        add_assoc]
    rw [Nat.factorial_succ, Nat.cast_mul, le_div_iff₀ (by positivity)]
    calc ‖(Gamma (s + (k + 1 : ℕ)))⁻¹‖ * ((k + 1 : ℕ) * k !)
        ≤ ‖(Gamma (s + (k + 1 : ℕ)))⁻¹‖ * (‖s + k‖ * k !) := by gcongr
      _ = ‖(Gamma (s + k))⁻¹‖ * k ! := by rw [hrec]; ring
      _ ≤ ‖(Gamma s)⁻¹‖ := (le_div_iff₀ (by positivity)).1 ih

/-- For every complex `s` and natural `n`, `(Γ s)⁻¹ = (s)_n (Γ(s + n))⁻¹`, where
`(s)_n = (ascPochhammer ℂ n).eval s`. Unlike `Complex.Gamma_add_nat_div_Gamma_eq`, this holds at
the nonpositive integer poles of `Γ` as well, where Mathlib sets `Γ(-k) = 0`. -/
theorem inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast (s : ℂ) (n : ℕ) :
    (Gamma s)⁻¹ = (ascPochhammer ℂ n).eval s * (Gamma (s + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n), ascPochhammer_succ_eval,
      Nat.cast_succ, ← add_assoc, mul_assoc]

end Complex

namespace Real

/-- The reciprocal of the real Gamma function satisfies
`(Γ s)⁻¹ = s (s + 1) ⋯ (s + n - 1) (Γ(s + n))⁻¹` for every real `s`, including at the nonpositive
integer poles where `(Γ s)⁻¹ = 0`. -/
theorem inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (s : ℝ) (n : ℕ) :
    (Gamma s)⁻¹ = (ascPochhammer ℝ n).eval s * (Gamma (s + n))⁻¹ := by
  have h := Complex.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (s : ℂ) n
  have heval : (ascPochhammer ℂ n).eval (s : ℂ) = (((ascPochhammer ℝ n).eval s : ℝ) : ℂ) := by
    simpa using Polynomial.eval_map_apply Complex.ofRealHom s (p := ascPochhammer ℝ n)
  have hcast : (s : ℂ) + n = ((s + n : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.Gamma_ofReal, Complex.Gamma_ofReal, heval, ← Complex.ofReal_inv,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

/-- A nonzero real number strictly greater than `-1` is not a nonpositive integer. -/
theorem ne_neg_natCast_of_neg_one_lt_of_ne_zero {σ : ℝ} (hσ₀ : -1 < σ) (hσ : σ ≠ 0) (n : ℕ) :
    σ ≠ -(n : ℝ) := fun hn ↦
  Complex.ne_neg_natCast_of_neg_one_lt_re_of_ne_zero (z := σ) (by simpa using hσ₀)
    (Complex.ofReal_ne_zero.mpr hσ) n (by exact_mod_cast hn)

/-- A real number strictly between `0` and `1`, shifted left by a natural number, is not a
nonpositive integer: `a - N ≠ -n`. -/
theorem sub_natCast_ne_neg_natCast {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N n : ℕ) :
    a - N ≠ -n := by
  intro h
  rcases le_or_gt N n with hNn | hNn
  · have : (N : ℝ) ≤ n := by exact_mod_cast hNn
    linarith
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hNn
    linarith

open scoped Real in
/-- The reflection formula at `c - k`: when `sin πc ≠ 0`,
`(-1)^k / k! · Γ(c - k) = (π / sin πc) / (k! Γ(1 - c + k))`. -/
theorem neg_one_pow_div_factorial_mul_Gamma_sub_natCast {c : ℝ}
    (hc : sin (π * c) ≠ 0) (k : ℕ) :
    (-1) ^ k / (k ! : ℝ) * Gamma (c - k) =
      π / sin (π * c) / (k ! * Gamma (1 - c + k)) := by
  have hrefl := Gamma_mul_Gamma_one_sub (c - k)
  rw [show π * (c - k) = π * c - k * π by ring, sin_sub_nat_mul_pi,
    show 1 - (c - k) = 1 - c + k by ring] at hrefl
  have hsgn : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hG : Gamma (1 - c + k) ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hrefl
    exact div_ne_zero pi_ne_zero (mul_ne_zero hsgn hc) hrefl.symm
  rw [eq_div_iff (mul_ne_zero hsgn hc)] at hrefl
  rw [div_div, eq_div_iff (mul_ne_zero hc (mul_ne_zero (by positivity) hG)),
    div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (by positivity)]
  linear_combination (k ! : ℝ) * hrefl

/-- A real number strictly between `-(k + 1)` and `-k` is not a nonpositive integer. -/
theorem ne_neg_natCast_of_mem_Ioo {k : ℕ} {a : ℝ} (ha : a ∈ Set.Ioo (-(k + 1 : ℝ)) (-k))
    (n : ℕ) : a ≠ -n := by
  rintro rfl
  have h₁ : (n : ℝ) < k + 1 := by linarith [ha.1]
  have h₂ : (k : ℝ) < n := by linarith [ha.2]
  norm_cast at h₁ h₂
  omega

/-- On `[1, ∞)`, the reciprocal Gamma function decays factorially along natural-number shifts:
`(Γ(s + k))⁻¹ ≤ (Γ s)⁻¹ / k!`, the real specialization of
`Complex.norm_inv_Gamma_add_natCast_le`. -/
theorem inv_Gamma_add_natCast_le {s : ℝ} (hs : 1 ≤ s) (k : ℕ) :
    (Gamma (s + k))⁻¹ ≤ (Gamma s)⁻¹ / k ! := by
  have hnorm (t : ℝ) (ht : 0 < t) : ‖(Complex.Gamma t)⁻¹‖ = (Gamma t)⁻¹ := by
    rw [Complex.Gamma_ofReal, norm_inv, Complex.norm_of_nonneg (Gamma_pos_of_pos ht).le]
  have h := Complex.norm_inv_Gamma_add_natCast_le (s := s) (by simpa using hs) k
  have hcast : (s : ℂ) + k = ((s + k : ℝ) : ℂ) := by push_cast; ring
  rwa [hcast, hnorm (s + k) (by positivity), hnorm s (by positivity)] at h

/-- For every real `s` and natural `n`, `(Γ s)⁻¹ = (s)_n (Γ(s + n))⁻¹`, including at the
nonpositive integer poles of `Γ`. -/
theorem inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast (s : ℝ) (n : ℕ) :
    (Gamma s)⁻¹ = (ascPochhammer ℝ n).eval s * (Gamma (s + n))⁻¹ := by
  have h := Complex.inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast (s : ℂ) n
  have hcast : (s : ℂ) + n = ((s + n : ℝ) : ℂ) := by push_cast; ring
  have hp : (ascPochhammer ℂ n).eval (s : ℂ) = (((ascPochhammer ℝ n).eval s : ℝ) : ℂ) :=
    (ascPochhammer_eval₂ Complex.ofRealHom n (s : ℂ)).trans
      (Polynomial.eval₂_at_apply Complex.ofRealHom s)
  rw [hcast, hp, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

end Real

namespace Complex

open scoped Real in
/-- Euler's reflection formula in reciprocal form: for `s ∉ -ℕ`,
`Γ(s) * sin (π * s) = π / Γ(1 - s)`. This identity also holds at positive integers `s = n + 1`,
where both sides vanish (`sin (π * (n + 1)) = 0` and `Γ(-n) = 0`). -/
theorem Gamma_mul_sin_pi_mul {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    Gamma s * sin (π * s) = π / Gamma (1 - s) := by
  by_cases h0 : Gamma (1 - s) = 0
  · obtain ⟨n, hn⟩ := (Gamma_eq_zero_iff (1 - s)).mp h0
    have hsn : s = (n : ℂ) + 1 := by linear_combination -hn
    have hsin : sin (π * s) = 0 := by
      rw [hsn, mul_add, mul_one, sin_add_pi]
      exact neg_eq_zero.mpr (by simpa [mul_comm] using sin_nat_mul_pi n)
    rw [h0, div_zero, hsin, mul_zero]
  · have hrefl := Gamma_mul_Gamma_one_sub s
    have hsin0 : sin (π * s) ≠ 0 := fun hsin => by
      rw [hsin, div_zero] at hrefl
      exact mul_ne_zero (Gamma_ne_zero hs) h0 hrefl
    rw [eq_div_iff h0]
    calc Gamma s * sin (π * s) * Gamma (1 - s)
        = (Gamma s * Gamma (1 - s)) * sin (π * s) := by ring
      _ = (π / sin (π * s)) * sin (π * s) := by rw [hrefl]
      _ = π := div_mul_cancel₀ _ hsin0

/-- `Γ(1/3) Γ(2/3) = 2π/√3`, by the reflection formula. -/
theorem Gamma_one_third_mul_Gamma_two_thirds :
    Gamma (1 / 3) * Gamma (2 / 3) = 2 * Real.pi / (Real.sqrt 3 : ℂ) := by
  have h := Gamma_mul_Gamma_one_sub (1 / 3)
  -- The reflection formula is stated at `1 - s`; put `1 - 1/3` in the form `2/3` of the goal.
  have h23 : (1 : ℂ) - 1 / 3 = 2 / 3 := by norm_num
  rw [h23] at h
  have hs : sin (Real.pi * (1 / 3)) = (Real.sqrt 3 : ℂ) / 2 := by
    -- Write the argument as the cast of the real number `π/3`, to use `Real.sin_pi_div_three`.
    have hpi : (Real.pi : ℂ) * (1 / 3) = ((Real.pi / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [hpi, ← ofReal_sin, Real.sin_pi_div_three]
    push_cast
    ring
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by simp
  rw [h, hs]
  field_simp

open Polynomial

/-- **Euler's limit formula in Pochhammer form.** For every complex `s`,
`n^(s - 1) n! / (s)ₙ → Γ(s)` as `n → ∞`. -/
theorem tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval (s : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ (s - 1) * n ! / (ascPochhammer ℂ n).eval s) atTop
      (𝓝 (Gamma s)) := by
  have hlin : Tendsto (fun n : ℕ => s / n + 1) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat s).add_const 1
  have h := (GammaSeq_tendsto_Gamma s).mul hlin
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0,
    tendsto_natCast_atTop_cobounded.eventually_ne_cobounded (-s)] with n hn hs
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsn : s + n ≠ 0 := fun h => hs (by linear_combination h)
  -- Only the last factor `s + n` of the product cancels against the correction `(s + n) / n`.
  rw [GammaSeq, Finset.prod_range_succ, ← TauCeti.ascPochhammer_eval_eq_prod_range, ← div_div,
    div_add_one hn', div_mul_div_cancel₀ hsn, cpow_sub _ _ hn', cpow_one]
  ring

/-- **Euler's limit formula for `1 / Γ` in Pochhammer form.** For every complex `s`,
`(s)ₙ / (n^(s - 1) n!) → (Γ(s))⁻¹` as `n → ∞`; at the poles `s = -k` both sides are eventually
`0`. -/
theorem tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial (s : ℂ) :
    Tendsto (fun n : ℕ => (ascPochhammer ℂ n).eval s / ((n : ℂ) ^ (s - 1) * n !)) atTop
      (𝓝 (Gamma s)⁻¹) := by
  by_cases hs : ∀ m : ℕ, s ≠ -m
  · simpa only [inv_div] using
      (tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval s).inv₀ (Gamma_ne_zero hs)
  · push Not at hs
    obtain ⟨k, rfl⟩ := hs
    rw [Gamma_neg_nat_eq_zero, inv_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [ascPochhammer_eval_neg_natCast_of_lt hn, zero_div]

/-- **Euler's limit formula as an asymptotic equivalence.** For `s ∉ {0, -1, -2, …}`,
`n! / (s)_{n+1} ~ Γ(s) n^{-s}` as `n → ∞`. -/
theorem isEquivalent_factorial_div_ascPochhammer_eval_succ {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    (fun n : ℕ => (n ! : ℂ) / (ascPochhammer ℂ (n + 1)).eval s) ~[atTop]
      fun n => Gamma s * ((n : ℂ) ^ s)⁻¹ := by
  refine (((isEquivalent_const_iff_tendsto (Gamma_ne_zero hs)).2 (GammaSeq_tendsto_Gamma s)).mul
    (IsEquivalent.refl (u := fun n : ℕ => ((n : ℂ) ^ s)⁻¹))).congr_left ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  simp only [Pi.mul_apply, GammaSeq, ← TauCeti.ascPochhammer_eval_eq_prod_range]
  field_simp

end Complex
