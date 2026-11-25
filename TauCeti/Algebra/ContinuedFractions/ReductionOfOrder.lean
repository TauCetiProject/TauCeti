/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.Asymptotics.Sum.Divergence

/-!
# Three-term recurrences, Casoratians, and reduction-of-order convergence of continued fractions

Let `a, b : ℕ → K` be 1-indexed coefficient sequences, and let
`contFrac a b : GenContFract K` be the continued fraction `a₁ / (b₁ + a₂ / (b₂ + ⋯))` with head
`0` and `(n + 1)`-st partial numerator and denominator `(a (n + 1), b (n + 1))`. Its continuant
sequences `n ↦ Aₙ₋₁ = ((contFrac a b).contsAux n).a` and `n ↦ Bₙ₋₁ = ((contFrac a b).contsAux n).b`
form the basis of solutions of the three-term recurrence
`y(n + 1) = bₙ y(n) + aₙ y(n - 1)` (`n ≥ 1`) with initial values `(1, 0)` and `(0, 1)`.

Following Gautschi (1967, §1), every solution `f` is the linear combination
`f(n) = Aₙ₋₁ f(0) + Bₙ₋₁ f(1)`, so Mathlib's determinant formula `GenContFract.determinant` yields
the Casoratian identity
`f(m) u(m + 1) - f(m + 1) u(m) = (-1)^m (a₁ ⋯ aₘ) (f(0) u(1) - f(1) u(0))`
for any pair of recurrence solutions `f` and `u`. Dividing the Casoratian of `f` against `Bₘ₋₁`
by `f(m) f(m + 1)` telescopes `Bₙ₋₁ / f(n)`. Over a normed field, when `f(0) ≠ 0`, `f` is
eventually nonzero, and the reduction-of-order partial sums
`∑_{m = N}^{n - 1} (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))` diverge in norm, the ratio `Bₙ / f(n + 1)`
diverges in norm as well, so the denominators `Bₙ` are eventually nonzero and the convergents
`Aₙ / Bₙ` tend to `-f(1) / f(0)`. This reduction-of-order criterion gives the sufficient half
underlying Pincherle's theorem for explicit recurrence solutions.

## Main definitions

* `TauCeti.contFrac a b` — the `GenContFract K` with head `0` and 1-indexed partial numerators `a`
  and partial denominators `b`.

## Main results

* `TauCeti.eq_contsAux_of_recurrence` — any solution `f` of `f(n + 1) = bₙ f(n) + aₙ f(n - 1)`
  (`n ≥ 1`) satisfies `f(n) = Aₙ₋₁ f(0) + Bₙ₋₁ f(1)`.
* `TauCeti.contFrac_contsAux_det` — `Aₘ₋₁ Bₘ - Bₘ₋₁ Aₘ = (-1)^m ∏_{j = 1}^m aⱼ`.
* `TauCeti.casoratian_of_recurrence`, `TauCeti.casoratian_contFrac_contsAux_b` — the Casoratian
  identities for general solutions and against the denominator continuants.
* `TauCeti.contFrac_contsAux_b_div_sub` — the reduction-of-order telescoping sum for `Bₙ₋₁ / f(n)`.
* `TauCeti.tendsto_norm_contFrac_dens_div_atTop`,
  `TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum` — divergence of `‖Bₙ / f(n + 1)‖` and
  convergence of `(contFrac a b).convs` to `-f(1) / f(0)` from norm divergence of the
  reduction-of-order partial sums.

## References

* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82, §1.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti

/-! ### The continued fraction `a₁ / (b₁ + a₂ / (b₂ + ⋯))` -/

section Zero

variable {K : Type*} [Zero K]

/-- The generalized continued fraction `a₁ / (b₁ + a₂ / (b₂ + ⋯))` with head `0` and 1-indexed
partial numerators `a (n + 1)` and partial denominators `b (n + 1)`. -/
def contFrac (a b : ℕ → K) : GenContFract K :=
  ⟨0, Stream'.Seq.ofStream fun n => ⟨a (n + 1), b (n + 1)⟩⟩

/-- Unfolding `contFrac` to its head `0` and stream of 1-indexed numerator-denominator pairs. -/
theorem contFrac_def (a b : ℕ → K) :
    contFrac a b = ⟨0, Stream'.Seq.ofStream fun n => ⟨a (n + 1), b (n + 1)⟩⟩ := (rfl)

/-- The head term of `contFrac a b` is `0`. -/
@[simp]
theorem contFrac_h (a b : ℕ → K) : (contFrac a b).h = 0 := (rfl)

/-- The `n`-th 0-indexed pair of `contFrac a b` consists of `a (n + 1)` and `b (n + 1)`. -/
@[simp]
theorem contFrac_s_get? (a b : ℕ → K) (n : ℕ) :
    (contFrac a b).s.get? n = some ⟨a (n + 1), b (n + 1)⟩ := (rfl)

/-- The `n`-th 0-indexed partial numerator of `contFrac a b` is `a (n + 1)`. -/
@[simp]
theorem contFrac_partNums_get? (a b : ℕ → K) (n : ℕ) :
    (contFrac a b).partNums.get? n = some (a (n + 1)) := by
  simp [GenContFract.partNums]

/-- The `n`-th 0-indexed partial denominator of `contFrac a b` is `b (n + 1)`. -/
@[simp]
theorem contFrac_partDens_get? (a b : ℕ → K) (n : ℕ) :
    (contFrac a b).partDens.get? n = some (b (n + 1)) := by
  simp [GenContFract.partDens]

/-- The infinite continued fraction `contFrac a b` never terminates in `Stream'.Seq`. -/
@[simp]
theorem not_terminatedAt_contFrac (a b : ℕ → K) (n : ℕ) :
    ¬(contFrac a b).TerminatedAt n := by
  simp [GenContFract.terminatedAt_iff_s_none]

/-- `contFrac a b` depends only on the values of `a` and `b` at positive indices `n ≥ 1`. -/
theorem contFrac_congr {a a' b b' : ℕ → K} (ha : ∀ ⦃n : ℕ⦄, 1 ≤ n → a n = a' n)
    (hb : ∀ ⦃n : ℕ⦄, 1 ≤ n → b n = b' n) : contFrac a b = contFrac a' b' := by
  ext
  · simp
  · simp [ha (Nat.succ_pos _), hb (Nat.succ_pos _)]

end Zero

/-! ### Continuant recurrences and the linear-combination formula -/

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- The numerator continuants `Aₙ₋₁ = ((contFrac a b).contsAux n).a` satisfy the three-term
recurrence `y(n + 1) = bₙ y(n) + aₙ y(n - 1)` for `n ≥ 1`. -/
theorem contFrac_contsAux_a_recurrence (a b : ℕ → K) {n : ℕ} (hn : 1 ≤ n) :
    ((contFrac a b).contsAux (n + 1)).a =
      b n * ((contFrac a b).contsAux n).a + a n * ((contFrac a b).contsAux (n - 1)).a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 1 + m + 1 = m + 2 := by omega
  have h2 : 1 + m = m + 1 := by omega
  have h3 : m + 1 - 1 = m := by omega
  rw [h1, h2, h3, GenContFract.contsAux_recurrence (contFrac_s_get? a b m) rfl rfl]

/-- The denominator continuants `Bₙ₋₁ = ((contFrac a b).contsAux n).b` satisfy the three-term
recurrence `y(n + 1) = bₙ y(n) + aₙ y(n - 1)` for `n ≥ 1`. -/
theorem contFrac_contsAux_b_recurrence (a b : ℕ → K) {n : ℕ} (hn : 1 ≤ n) :
    ((contFrac a b).contsAux (n + 1)).b =
      b n * ((contFrac a b).contsAux n).b + a n * ((contFrac a b).contsAux (n - 1)).b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 1 + m + 1 = m + 2 := by omega
  have h2 : 1 + m = m + 1 := by omega
  have h3 : m + 1 - 1 = m := by omega
  rw [h1, h2, h3, GenContFract.contsAux_recurrence (contFrac_s_get? a b m) rfl rfl]

/-- Every solution `f` of `f(n + 1) = bₙ f(n) + aₙ f(n - 1)` (`n ≥ 1`) is the linear combination
`Aₙ₋₁ f(0) + Bₙ₋₁ f(1)` of the continuants of `contFrac a b`. -/
theorem eq_contsAux_of_recurrence {a b f : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1)) (n : ℕ) :
    f n = ((contFrac a b).contsAux n).a * f 0 + ((contFrac a b).contsAux n).b * f 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [GenContFract.zeroth_contAux_eq_one_zero]
  | one => simp [GenContFract.first_contAux_eq_h_one]
  | more m ih0 ih1 =>
    have hm2 : m + 2 = (m + 1) + 1 := by omega
    have hm1 : m + 1 - 1 = m := by omega
    rw [GenContFract.contsAux_recurrence (contFrac_s_get? a b m) rfl rfl, hm2,
      hf (Nat.succ_pos m), hm1, ih1, ih0]
    simp only [Nat.succ_eq_add_one, mul_add, add_mul, mul_assoc]
    abel

end DivisionRing

/-! ### Determinant, Casoratian, and reduction-of-order telescoping -/

section Field

variable {K : Type*} [Field K]

/-- Determinant identity for the continuants of `contFrac a b`:
`Aₘ₋₁ Bₘ - Bₘ₋₁ Aₘ = (-1)^m ∏_{j = 1}^m aⱼ`. -/
theorem contFrac_contsAux_det (a b : ℕ → K) (m : ℕ) :
    ((contFrac a b).contsAux m).a * ((contFrac a b).contsAux (m + 1)).b -
        ((contFrac a b).contsAux m).b * ((contFrac a b).contsAux (m + 1)).a =
      (-1) ^ m * ∏ j ∈ Icc 1 m, a j := by
  rcases m with _ | k
  · simp [GenContFract.zeroth_contAux_eq_one_zero, GenContFract.first_contAux_eq_h_one]
  · have hIcc : Icc 1 (k + 1) = Ico 1 (k + 1 + 1) := by
      ext
      simp only [mem_Icc, mem_Ico]
      omega
    have hshift : (∏ j ∈ Ico 1 (k + 1 + 1), a j) = ∏ i ∈ range (k + 1), a (i + 1) := by
      have h := prod_Ico_eq_prod_range a 1 (k + 1 + 1)
      have hsub : k + 1 + 1 - 1 = k + 1 := by omega
      rw [hsub] at h
      exact h.trans (prod_congr rfl fun i _ => congr_arg a (Nat.add_comm 1 i))
    simp only [← GenContFract.nth_cont_eq_succ_nth_contAux, ← GenContFract.num_eq_conts_a,
      ← GenContFract.den_eq_conts_b]
    rw [(contFrac a b).determinant, hIcc, hshift]
    simp [prod_neg]

/-- **Casoratian identity** for two solutions `f` and `u` of
`y(n + 1) = bₙ y(n) + aₙ y(n - 1)` (`n ≥ 1`):
`f(m) u(m + 1) - f(m + 1) u(m) = (-1)^m (∏_{j = 1}^m aⱼ) (f(0) u(1) - f(1) u(0))`. -/
theorem casoratian_of_recurrence {a b f u : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1))
    (hu : ∀ ⦃n : ℕ⦄, 1 ≤ n → u (n + 1) = b n * u n + a n * u (n - 1)) (m : ℕ) :
    f m * u (m + 1) - f (m + 1) * u m =
      (-1) ^ m * (∏ j ∈ Icc 1 m, a j) * (f 0 * u 1 - f 1 * u 0) := by
  rw [eq_contsAux_of_recurrence hf m, eq_contsAux_of_recurrence hf (m + 1),
    eq_contsAux_of_recurrence hu m, eq_contsAux_of_recurrence hu (m + 1)]
  linear_combination (f 0 * u 1 - f 1 * u 0) * contFrac_contsAux_det a b m

/-- Casoratian of a recurrence solution `f` against the denominator continuants `Bₘ₋₁` of
`contFrac a b`: `f(m) Bₘ - f(m + 1) Bₘ₋₁ = (-1)^m (∏_{j = 1}^m aⱼ) f(0)`. -/
theorem casoratian_contFrac_contsAux_b {a b f : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1)) (m : ℕ) :
    f m * ((contFrac a b).contsAux (m + 1)).b - f (m + 1) * ((contFrac a b).contsAux m).b =
      (-1) ^ m * (∏ j ∈ Icc 1 m, a j) * f 0 := by
  simpa [GenContFract.zeroth_contAux_eq_one_zero, GenContFract.first_contAux_eq_h_one] using
    casoratian_of_recurrence (u := fun n => ((contFrac a b).contsAux n).b) hf
      (fun _ hn => contFrac_contsAux_b_recurrence a b hn) m

/-- Reduction-of-order telescoping identity for the ratio `Bₙ₋₁ / f(n)` on a nonvanishing range:
`Bₙ₋₁ / f(n) - B_{N - 1} / f(N)` equals
`f(0) ∑_{m = N}^{n - 1} (-1)^m (∏_{j = 1}^m aⱼ) / (f(m) f(m + 1))`. -/
theorem contFrac_contsAux_b_div_sub {a b f : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1))
    {N n : ℕ} (hn : N ≤ n) (hfN : ∀ k, N ≤ k → k ≤ n → f k ≠ 0) :
    ((contFrac a b).contsAux n).b / f n - ((contFrac a b).contsAux N).b / f N =
      f 0 * ∑ m ∈ Ico N n, (-1) ^ m * (∏ j ∈ Icc 1 m, a j) / (f m * f (m + 1)) := by
  rw [← sum_Ico_sub (fun m => ((contFrac a b).contsAux m).b / f m) hn, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨hmN, hmn⟩ := mem_Ico.1 hm
  have hfm : f m ≠ 0 := hfN m hmN hmn.le
  have hfm1 : f (m + 1) ≠ 0 := hfN (m + 1) (by omega) hmn
  have hcas := casoratian_contFrac_contsAux_b hf m
  field_simp
  linear_combination hcas

end Field

/-! ### Reduction-of-order convergence over a normed field -/

section NormedField

variable {K : Type*} [NormedField K]

/-- Over a normed field, if `f` solves `f(n + 1) = bₙ f(n) + aₙ f(n - 1)` (`n ≥ 1`) with
`f(0) ≠ 0`, `f` is eventually nonzero, and the reduction-of-order partial sums diverge in norm,
then `‖(contFrac a b).dens n / f(n + 1)‖ → ∞`. -/
theorem tendsto_norm_contFrac_dens_div_atTop {a b f : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1))
    (hf0 : f 0 ≠ 0) (hne : ∀ᶠ n in atTop, f n ≠ 0) {N : ℕ}
    (hdiv : Tendsto (fun n =>
      ‖∑ m ∈ Ico N n, (-1) ^ m * (∏ j ∈ Icc 1 m, a j) / (f m * f (m + 1))‖) atTop atTop) :
    Tendsto (fun n => ‖(contFrac a b).dens n / f (n + 1)‖) atTop atTop := by
  let T : ℕ → K := fun m => (-1) ^ m * (∏ j ∈ Icc 1 m, a j) / (f m * f (m + 1))
  obtain ⟨M, hfM⟩ := eventually_atTop.1 hne
  have hdivM : Tendsto (fun n => ‖∑ m ∈ Ico M n, T m‖) atTop atTop :=
    (tendsto_norm_sum_Ico_atTop_iff N M).1 hdiv
  have hscaled := (Tendsto.const_mul_atTop (norm_pos_iff.2 hf0) hdivM).comp
    (tendsto_add_atTop_nat 1)
  have hshift := tendsto_atTop_add_const_right atTop (-‖((contFrac a b).contsAux M).b / f M‖)
    hscaled
  refine tendsto_atTop_mono' atTop ?_ hshift
  filter_upwards [eventually_ge_atTop M] with n hn
  simp only [Function.comp_apply]
  have ht := contFrac_contsAux_b_div_sub hf (n := n + 1) (by omega) fun k hk _ => hfM k hk
  rw [← GenContFract.nth_cont_eq_succ_nth_contAux, ← GenContFract.den_eq_conts_b] at ht
  have htri := norm_sub_norm_le
    ((contFrac a b).dens n / f (n + 1) - ((contFrac a b).contsAux M).b / f M)
    (-(((contFrac a b).contsAux M).b / f M))
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg, ht, norm_mul] at htri
  exact htri

/-- **Reduction-of-order convergence of `contFrac a b`**: if `f` solves
`f(n + 1) = bₙ f(n) + aₙ f(n - 1)` (`n ≥ 1`) with `f(0) ≠ 0`, `f` is eventually nonzero, and the
partial sums `∑_{m = N}^{n - 1} (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))` diverge in norm, then the
denominators `(contFrac a b).dens n` are eventually nonzero and `(contFrac a b).convs` tends to
`-f(1) / f(0)`. -/
theorem tendsto_convs_contFrac_of_tendsto_norm_sum {a b f : ℕ → K}
    (hf : ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) = b n * f n + a n * f (n - 1))
    (hf0 : f 0 ≠ 0) (hne : ∀ᶠ n in atTop, f n ≠ 0) {N : ℕ}
    (hdiv : Tendsto (fun n =>
      ‖∑ m ∈ Ico N n, (-1) ^ m * (∏ j ∈ Icc 1 m, a j) / (f m * f (m + 1))‖) atTop atTop) :
    (∀ᶠ n in atTop, (contFrac a b).dens n ≠ 0) ∧
      Tendsto (contFrac a b).convs atTop (𝓝 (-f 1 / f 0)) := by
  have hratio_norm := tendsto_norm_contFrac_dens_div_atTop hf hf0 hne hdiv
  have hdens_ne : ∀ᶠ n in atTop, (contFrac a b).dens n ≠ 0 := by
    filter_upwards [hratio_norm.eventually_gt_atTop 0] with n hn h0
    rw [h0, zero_div, norm_zero] at hn
    exact lt_irrefl 0 hn
  have hinv_zero : Tendsto (fun n => f (n + 1) / (contFrac a b).dens n) atTop (𝓝 0) := by
    have hcob : Tendsto (fun n => (contFrac a b).dens n / f (n + 1)) atTop
        (Bornology.cobounded K) :=
      tendsto_norm_atTop_iff_cobounded.1 hratio_norm
    exact (tendsto_inv₀_cobounded.comp hcob).congr fun n => by simp [inv_div]
  refine ⟨hdens_ne, ?_⟩
  have hlim : Tendsto (fun n => (f (n + 1) / (contFrac a b).dens n) / f 0 - f 1 / f 0)
      atTop (𝓝 (-f 1 / f 0)) := by
    simpa [neg_div] using (hinv_zero.div_const (f 0)).sub_const (f 1 / f 0)
  refine hlim.congr' ?_
  filter_upwards [hdens_ne] with n hdn
  have hcomb := eq_contsAux_of_recurrence hf (n + 1)
  simp only [← GenContFract.nth_cont_eq_succ_nth_contAux, ← GenContFract.num_eq_conts_a,
    ← GenContFract.den_eq_conts_b] at hcomb
  rw [GenContFract.conv_eq_num_div_den]
  field_simp [hdn, hf0]
  linear_combination hcomb

end NormedField

end TauCeti
