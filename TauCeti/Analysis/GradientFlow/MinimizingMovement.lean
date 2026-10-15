/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
public import TauCeti.Topology.EMetricSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Data.EReal.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall

/-!
# Generalized minimizing movements

De Giorgi's minimizing movement scheme approximates the gradient flow of an energy
`φ : X → EReal` on an extended metric space by the implicit Euler scheme. For a time step `τ > 0`,
a *minimizing movement sequence* `u` has each `u (n + 1)` in the resolvent `J_τ (u n)`, and its
*piecewise constant interpolant* is `t ↦ u ⌈t / τ⌉₊`. A *generalized minimizing movement* starting
at `x₀` is a pointwise limit of such interpolants along time steps `τ k → 0`, with initial points
tending to `x₀` (`TauCeti.IsGeneralizedMinimizingMovement`). Convergence is taken for an
auxiliary convergence `y_n ⇀ y` on `X`, given by filters `l y`, as in
`TauCeti.moreauYosidaResolvent_nonempty`: in the Wasserstein space it is narrow convergence,
for which bounded energy sublevels can be relatively compact (for instance over a proper
underlying space) even though they are not relatively compact for the metric.

This file proves that generalized minimizing movements exist, under the hypotheses of
Ambrosio–Gigli–Savaré: coercivity of `φ`, lower semicontinuity, compactness of bounded sublevels
for `⇀`, and joint lower semicontinuity of the distance for `⇀`. They start at `x₀` and are
`1/2`-Hölder continuous on bounded time intervals.

The proof rests on estimates for a single minimizing movement sequence that are uniform in the
time step. Summing the one-step energy estimates and applying the Cauchy–Schwarz inequality
bounds the distance travelled in `n - m` steps by the energy dissipated:
`d(u m, u n)² ≤ 2 (n - m) τ (φ (u m) - φ (u n))`. The energy is not assumed to be bounded below;
coercivity, in the form `φ_{τ'}(u 0) = A > -∞`, bounds it below by `A - d(u 0, ·)² / (2τ')`. A
discrete Gronwall argument (`TauCeti.sq_le_mul_one_add_div_pow_of_sq_le_mul_sub`) combines the
two into `d(u 0, u n)² ≤ 2τ' (E - A) (1 + 8τ / τ')ⁿ` for `4τ ≤ τ'`, where `E = φ (u 0)`. Up to a
time `T` this is at most `2τ' (E - A) exp (8 (T + τ) / τ')`, independently of `τ`
(`TauCeti.one_add_mul_pow_ceil_div_le_exp`). Hence the
interpolants are uniformly bounded, have energy at most `E`, and are asymptotically
`1/2`-Hölder:
`d(u ⌈s / τ⌉₊, u ⌈t / τ⌉₊)² ≤ 2 (t - s + τ) (E - A) (1 + exp (8 (t + τ) / τ'))`.
The refined Arzelà–Ascoli theorem `TauCeti.tendsto_subseq_of_limsup_edist_le` then extracts a
pointwise convergent subsequence.

The time steps are uniform, and the existence theorem starts every minimizing movement sequence
at `x₀` itself. Ambrosio–Gigli–Savaré also allow nonuniform partitions of the time axis; the
definition here allows approximating initial data, but not nonuniform partitions.

## Main definitions

* `TauCeti.IsGeneralizedMinimizingMovement l φ x₀ u`: `u` is a generalized minimizing movement
  for `φ` starting at `x₀`.

## Main results

* `TauCeti.apply_add_edist_sq_div_le_of_forall_mem_moreauYosidaResolvent`: the multi-step energy
  estimate `φ (u n) + d(u m, u n)² / (2 (n - m) τ) ≤ φ (u m)`.
* `TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent` and
  `TauCeti.le_apply_of_forall_mem_moreauYosidaResolvent`: the a priori bounds on the distance
  from the start and on the energy.
* `TauCeti.edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent`: the Hölder estimate for the
  piecewise constant interpolant.
* `TauCeti.tendsto_subseq_of_forall_mem_moreauYosidaResolvent`: compactness of the piecewise
  constant interpolants as the time step tends to `0`.
* `TauCeti.IsGeneralizedMinimizingMovement.apply_zero`: a generalized minimizing movement starts
  at its initial point.
* `TauCeti.exists_isGeneralizedMinimizingMovement`: existence of generalized minimizing
  movements, with `1/2`-Hölder continuity on bounded time intervals.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2 (Definition 2.0.6 and Section 2.2)
  and Chapter 3 (Sections 3.2 and 3.3).
* E. De Giorgi, *New problems on minimizing movements*, in *Boundary Value Problems for Partial
  Differential Equations and Applications*, RMA Res. Notes Appl. Math. 29, Masson 1993, 81–98.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal} {τ τ' : ℝ≥0} {u : ℕ → X}

/-- **Multi-step energy estimate.** Along a minimizing movement sequence with time step `τ`, the
`n - m` steps from `u m` to `u n` lower the energy by at least the penalty
`d(u m, u n)² / (2 (n - m) τ)` of a single step of length `(n - m) τ`. -/
theorem apply_add_edist_sq_div_le_of_forall_mem_moreauYosidaResolvent
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {m n : ℕ} (hmn : m ≤ n) :
    φ (u n) + (edist (u m) (u n) ^ 2 / (2 * ((n - m : ℕ) * τ)) : ℝ≥0∞) ≤ φ (u m) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hw i : u (m + (i + 1)) ∈ moreauYosidaResolvent φ τ (u (m + i)) := hu (m + i)
  have key := apply_add_sum_le_of_forall_mem_moreauYosidaResolvent (u := fun i ↦ u (m + i)) hw N
  simp only [add_zero] at key
  refine le_trans (add_le_add_right (EReal.coe_ennreal_le_coe_ennreal_iff.2 ?_) _) key
  rw [Nat.add_sub_cancel_left]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  -- The triangle inequality and the Cauchy–Schwarz inequality `(∑ dᵢ)² ≤ N ∑ dᵢ²`.
  set d : ℕ → ℝ≥0 := fun i ↦ (edist (u (m + i)) (u (m + (i + 1)))).toNNReal
  have hd i : (d i : ℝ≥0∞) = edist (u (m + i)) (u (m + (i + 1))) :=
    ENNReal.coe_toNNReal (edist_ne_top_of_mem_moreauYosidaResolvent (hw i))
  have htri : edist (u m) (u (m + N)) ≤ ∑ i ∈ Finset.range N, (d i : ℝ≥0∞) := by
    simpa [hd] using edist_le_range_sum_edist (fun i ↦ u (m + i)) N
  have hcs : (∑ i ∈ Finset.range N, (d i : ℝ≥0∞)) ^ 2 ≤
      N * ∑ i ∈ Finset.range N, (d i : ℝ≥0∞) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := d)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  calc edist (u m) (u (m + N)) ^ 2 / (2 * (N * τ))
      ≤ (N * ∑ i ∈ Finset.range N, (d i : ℝ≥0∞) ^ 2) / (N * (2 * τ)) := by
        rw [mul_left_comm]
        gcongr
        exact (pow_le_pow_left₀ bot_le htri 2).trans hcs
    _ = ∑ i ∈ Finset.range N, edist (u (m + i)) (u (m + (i + 1))) ^ 2 / (2 * τ) := by
        rw [ENNReal.mul_div_mul_left _ _ hN' (ENNReal.natCast_ne_top N), ENNReal.sum_div]
        simp [hd]

/-- Along a minimizing movement sequence started at energy `E` with `φ_{τ'}(u 0) = A`, every
point is at finite distance from the start and has real energy `e` with
`2τ' (A - e) ≤ d(u 0, u n)²`. -/
private theorem forall_edist_ne_top_and_exists_eq
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (hτ' : 0 < τ') {A E : ℝ}
    (hA : moreauYosida φ τ' (u 0) = A) (hE : φ (u 0) = E) (n : ℕ) :
    edist (u 0) (u n) ≠ ⊤ ∧ ∃ e : ℝ, φ (u n) = e ∧
      2 * τ' * (A - e) ≤ (edist (u 0) (u n)).toReal ^ 2 := by
  have hfin : ∀ n, edist (u 0) (u n) ≠ ⊤ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.2 ⟨ih, edist_ne_top_of_mem_moreauYosidaResolvent (hu n)⟩)
        (edist_triangle _ _ _)
  refine ⟨hfin n, ?_⟩
  have hle : φ (u n) ≤ E :=
    hE ▸ antitone_comp_of_forall_mem_moreauYosidaResolvent hu (Nat.zero_le n)
  have hP : edist (u 0) (u n) ^ 2 / (2 * τ') ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (hfin n)) (by simp [hτ'.ne'])
  have hcoer := hA ▸ moreauYosida_le φ τ' (hfin n)
  have hbot : φ (u n) ≠ ⊥ := by
    rintro h
    rw [h, EReal.bot_add] at hcoer
    exact EReal.coe_ne_bot _ (le_bot_iff.1 hcoer)
  have htop : φ (u n) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top E) hle
  refine ⟨(φ (u n)).toReal, (EReal.coe_toReal htop hbot).symm, ?_⟩
  rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_add_coe_ennreal_iff hP] at hcoer
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal] at hcoer
  have hτ'r : (0 : ℝ) < τ' := NNReal.coe_pos.2 hτ'
  have := (le_div_iff₀ (by positivity)).1 (by linarith : A - (φ (u n)).toReal ≤
    (edist (u 0) (u n)).toReal ^ 2 / (2 * τ'))
  linarith

/-- The a priori distance bound of `TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, in
real numbers, together with the real energies along the sequence. -/
private theorem toReal_edist_sq_le (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n))
    (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ') {A E : ℝ} (hA : moreauYosida φ τ' (u 0) = A)
    (hE : φ (u 0) = E) (n : ℕ) :
    edist (u 0) (u n) ≠ ⊤ ∧ ∃ e : ℝ, φ (u n) = e ∧
      2 * τ' * (A - e) ≤ (edist (u 0) (u n)).toReal ^ 2 ∧
      (edist (u 0) (u n)).toReal ^ 2 ≤ 2 * τ' * (E - A) * (1 + 8 * τ / τ') ^ n := by
  have hτ' : 0 < τ' := lt_of_lt_of_le (by positivity) hττ'
  choose hfin e he hcoer using forall_edist_ne_top_and_exists_eq hu hτ' hA hE
  have he0 : e 0 = E := by
    have := he 0
    rw [hE] at this
    exact_mod_cast this.symm
  refine ⟨hfin n, e n, he n, hcoer n, ?_⟩
  have key := sq_le_mul_one_add_div_pow_of_sq_le_mul_sub
    (D := fun n ↦ (edist (u 0) (u n)).toReal) (d := fun n ↦ (edist (u n) (u (n + 1))).toReal)
    (e := e) (τ := τ) (τ' := τ') (A := A)
    (NNReal.coe_pos.2 hτ) (by exact_mod_cast hττ') (by simp) (fun _ ↦ ENNReal.toReal_nonneg)
    (fun n ↦ ENNReal.toReal_le_add (edist_triangle _ _ _) (hfin n)
      (edist_ne_top_of_mem_moreauYosidaResolvent (hu n)))
    (fun n ↦ ?_) hcoer n
  · rwa [he0] at key
  · have h := add_toReal_sq_div_le_of_mem_moreauYosidaResolvent hτ (hu n) (z := u n) (by simp)
      (he (n + 1)) (he n)
    simp only [edist_self, ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, add_zero] at h
    have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
    have := (div_le_iff₀ (by positivity)).1 (by linarith : (edist (u n) (u (n + 1))).toReal ^ 2 /
      (2 * τ) ≤ e n - e (n + 1))
    linarith

/-- **A priori distance bound for minimizing movements.** Let `u` be a minimizing movement
sequence with time step `τ > 0`, started at energy `φ (u 0) = E`, and let `A = φ_{τ'}(u 0)` be
finite for a time step `τ' ≥ 4τ`. Then after `n` steps
`d(u 0, u n)² ≤ 2τ' (E - A) (1 + 8τ / τ')ⁿ`. For `nτ ≤ T` the right-hand side is at most
`2τ' (E - A) exp (8T / τ')`, a bound independent of the time step. -/
theorem edist_sq_le_of_forall_mem_moreauYosidaResolvent
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ')
    {A E : ℝ} (hA : moreauYosida φ τ' (u 0) = A) (hE : φ (u 0) = E) (n : ℕ) :
    edist (u 0) (u n) ^ 2 ≤ ENNReal.ofReal (2 * τ' * (E - A) * (1 + 8 * τ / τ') ^ n) := by
  obtain ⟨hfin, -, -, -, h⟩ := toReal_edist_sq_le hu hτ hττ' hA hE n
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hfin), ENNReal.toReal_pow]
  exact ENNReal.ofReal_le_ofReal h

/-- **A priori energy bound for minimizing movements.** Under the hypotheses of
`TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, the energy after `n` steps is at least
`A - (E - A) (1 + 8τ / τ')ⁿ`. -/
theorem le_apply_of_forall_mem_moreauYosidaResolvent
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ')
    {A E : ℝ} (hA : moreauYosida φ τ' (u 0) = A) (hE : φ (u 0) = E) (n : ℕ) :
    ((A - (E - A) * (1 + 8 * τ / τ') ^ n : ℝ) : EReal) ≤ φ (u n) := by
  obtain ⟨-, e, he, hcoer, h⟩ := toReal_edist_sq_le hu hτ hττ' hA hE n
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hτ' : (0 : ℝ) < τ' :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * τ) (by exact_mod_cast hττ')
  rw [he, EReal.coe_le_coe_iff]
  nlinarith

/-- **Hölder estimate for the piecewise constant interpolant.** Under the hypotheses of
`TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, the piecewise constant interpolant
`t ↦ u ⌈t / τ⌉₊` of a minimizing movement sequence satisfies, for `0 ≤ s ≤ t`,
`d(u ⌈s / τ⌉₊, u ⌈t / τ⌉₊)² ≤ 2 (t - s + τ) (E - A) (1 + exp (8 (t + τ) / τ'))`.
As `τ → 0` this becomes a `1/2`-Hölder bound on bounded time intervals. -/
theorem edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ')
    {A E : ℝ} (hA : moreauYosida φ τ' (u 0) = A) (hE : φ (u 0) = E) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    edist (u ⌈s / τ⌉₊) (u ⌈t / τ⌉₊) ^ 2 ≤
      ENNReal.ofReal (2 * (t - s + τ) * (E - A) * (1 + Real.exp (8 * (t + τ) / τ'))) := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hτ'r : (0 : ℝ) < τ' :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * τ) (by exact_mod_cast hττ')
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' (u 0)
  set m := ⌈s / τ⌉₊ with hm
  set n := ⌈t / τ⌉₊ with hn
  have hmn : m ≤ n := Nat.ceil_mono (div_le_div_of_nonneg_right hst hτr.le)
  obtain ⟨hfm, em, hem, -, -⟩ := toReal_edist_sq_le hu hτ hττ' hA hE m
  obtain ⟨hfn, en, hen, -, -⟩ := toReal_edist_sq_le hu hτ hττ' hA hE n
  have hfmn : edist (u m) (u n) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfm, hfn⟩) (edist_triangle_left _ _ _)
  rcases hmn.eq_or_lt with hmn' | hmn'
  · rw [hmn', edist_self, zero_pow two_ne_zero]
    exact zero_le
  -- The multi-step estimate, in real numbers: `d² ≤ 2 (n - m) τ (φ (u m) - φ (u n))`.
  have hC1 := apply_add_edist_sq_div_le_of_forall_mem_moreauYosidaResolvent hu hmn
  have hk : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hmn'
  have hk0 : ((n - m : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hmn').ne'
  have hP : edist (u m) (u n) ^ 2 / (2 * ((n - m : ℕ) * τ)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top hfmn)
      (mul_ne_zero two_ne_zero (mul_ne_zero hk0 (ENNReal.coe_ne_zero.2 hτ.ne')))
  rw [hem, hen, ← EReal.coe_ennreal_toReal hP, ← EReal.coe_add, EReal.coe_le_coe_iff] at hC1
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.coe_toReal] at hC1
  set D := (edist (u m) (u n)).toReal
  have hD : D ^ 2 ≤ 2 * ((n - m : ℕ) * τ) * (em - en) := by
    have := (div_le_iff₀ (by positivity)).1
      (by linarith : D ^ 2 / (2 * ((n - m : ℕ) * τ)) ≤ em - en)
    linarith
  -- `(n - m) τ ≤ t - s + τ`, `φ (u m) ≤ E`, and the a priori lower bound on `φ (u n)`.
  have hkτ : ((n - m : ℕ) : ℝ) * τ ≤ t - s + τ := by
    rw [Nat.cast_sub hmn]
    have h1 := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg (hs.trans hst) hτr.le)) hτr
    have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (s / τ)) hτr.le
    rw [add_mul, div_mul_cancel₀ _ hτr.ne', one_mul] at h1
    rw [div_mul_cancel₀ _ hτr.ne'] at h2
    linarith
  have hem' : em ≤ E := by
    have := antitone_comp_of_forall_mem_moreauYosidaResolvent hu (Nat.zero_le m)
    simp only [Function.comp_apply, hem, hE] at this
    exact_mod_cast this
  have hen' : A - (E - A) * (1 + 8 * τ / τ') ^ n ≤ en := by
    have := le_apply_of_forall_mem_moreauYosidaResolvent hu hτ hττ' hA hE n
    rw [hen] at this
    exact_mod_cast this
  have hexp : (1 + 8 * τ / τ') ^ n ≤ Real.exp (8 * (t + τ) / τ') := by
    have := one_add_mul_pow_ceil_div_le_exp (a := 8 / τ') (by positivity) hτr (hs.trans hst)
    rwa [div_mul_eq_mul_div, div_mul_eq_mul_div] at this
  have hdiff : em - en ≤ (E - A) * (1 + Real.exp (8 * (t + τ) / τ')) := by
    nlinarith [mul_le_mul_of_nonneg_left hexp (sub_nonneg.2 hAE)]
  have hD0 : 0 ≤ em - en := by
    by_contra h
    have : 2 * ((n - m : ℕ) * τ) * (em - en) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (not_le.1 h)
    nlinarith [sq_nonneg D]
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hfmn), ENNReal.toReal_pow]
  refine ENNReal.ofReal_le_ofReal (hD.trans ?_)
  calc 2 * (((n - m : ℕ) : ℝ) * τ) * (em - en) ≤ 2 * (t - s + τ) * (em - en) := by gcongr
    _ ≤ 2 * (t - s + τ) * ((E - A) * (1 + Real.exp (8 * (t + τ) / τ'))) := by gcongr
    _ = _ := by ring

end PseudoEMetricSpace

/-! ### Generalized minimizing movements -/

section Definition

variable {X : Type*} [PseudoEMetricSpace X]

/-- A curve `u` is a *generalized minimizing movement* for the energy `φ` starting at `x₀`, with
respect to the auxiliary convergence given by the filters `l y`, if it is the pointwise limit of
piecewise constant interpolants of minimizing movement sequences along time steps tending to `0`:
there are time steps `τ k > 0` with `τ k → 0` and sequences `U k` in which each `U k (n + 1)` is a
resolvent step of time `τ k` from `U k n`, whose initial points tend to `x₀` with bounded energy,
such that `U k ⌈t / τ k⌉₊ ⇀ u t` for every time `t ≥ 0`. The values of `u` at negative times play
no role. -/
def IsGeneralizedMinimizingMovement (l : X → Filter X) (φ : X → EReal) (x₀ : X) (u : ℝ → X) :
    Prop :=
  ∃ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X), (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
    (∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) ∧
    Tendsto (fun k ↦ U k 0) atTop (𝓝 x₀) ∧ (∃ S : ℝ, ∀ k, φ (U k 0) ≤ S) ∧
    ∀ t : ℝ, 0 ≤ t → Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (l (u t))

/-- The defining property of a generalized minimizing movement. -/
theorem isGeneralizedMinimizingMovement_iff {l : X → Filter X} {φ : X → EReal} {x₀ : X}
    {u : ℝ → X} :
    IsGeneralizedMinimizingMovement l φ x₀ u ↔
      ∃ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X), (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
        (∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) ∧
        Tendsto (fun k ↦ U k 0) atTop (𝓝 x₀) ∧ (∃ S : ℝ, ∀ k, φ (U k 0) ≤ S) ∧
        ∀ t : ℝ, 0 ≤ t → Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (l (u t)) :=
  Iff.rfl

end Definition

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {l : X → Filter X}

/-- A generalized minimizing movement starts at its initial point, provided constant sequences
converge for the auxiliary convergence and the distance is jointly lower semicontinuous for it. -/
theorem IsGeneralizedMinimizingMovement.apply_zero (hl : ∀ y, pure y ≤ l y)
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    {x₀ : X} {u : ℝ → X} (h : IsGeneralizedMinimizingMovement l φ x₀ u) : u 0 = x₀ := by
  obtain ⟨τ, U, -, -, -, h0, -, hconv⟩ := isGeneralizedMinimizingMovement_iff.1 h
  have h1 := hconv 0 le_rfl
  simp only [zero_div, Nat.ceil_zero] at h1
  have h2 := hd h1 (tendsto_const_pure.mono_right (hl x₀))
  have h3 : Tendsto (fun k ↦ edist (U k 0) x₀) atTop (𝓝 0) := by
    simpa using h0.edist (tendsto_const_nhds (x := x₀))
  rw [h3.liminf_eq] at h2
  exact edist_le_zero.1 h2

/-- **Compactness of minimizing movements** (Ambrosio–Gigli–Savaré, Section 3.3). Let `l y` be
the filter of an auxiliary convergence `y_n ⇀ y` for which the distance is jointly sequentially
lower semicontinuous, and in which every sequence of finite diameter with energies bounded above
by a real number has a `⇀`-convergent subsequence. Let `U k` be minimizing movement sequences
from `x₀` with time steps `τ k → 0`, where `4 τ k ≤ τ'` and both `E = φ x₀` and `A = φ_{τ'}(x₀)`
are real. Then a subsequence of the piecewise constant interpolants `t ↦ U k ⌈t / τ k⌉₊`
converges pointwise on `[0, ∞)` to a curve `u` with
`d(u s, u t)² ≤ 2 (t - s) (E - A) (1 + exp (8 (t + τ') / τ'))` for `0 ≤ s ≤ t`. -/
theorem tendsto_subseq_of_forall_mem_moreauYosidaResolvent
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    {τ' : ℝ≥0} {τ : ℕ → ℝ≥0} (hτ : ∀ k, 0 < τ k) (hττ' : ∀ k, 4 * τ k ≤ τ')
    (hτ0 : Tendsto τ atTop (𝓝 0)) {U : ℕ → ℕ → X}
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) {x₀ : X}
    (hU0 : ∀ k, U k 0 = x₀) {A E : ℝ} (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) :
    ∃ Ψ : ℕ → ℕ, StrictMono Ψ ∧ ∃ u : ℝ → X,
      (∀ t : ℝ, 0 ≤ t → Tendsto (fun n ↦ U (Ψ n) ⌈t / τ (Ψ n)⌉₊) atTop (l (u t))) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → edist (u s) (u t) ^ 2 ≤
        ENNReal.ofReal (2 * (t - s) * (E - A) * (1 + Real.exp (8 * (t + τ') / τ'))) := by
  have hτkτ' k : τ k ≤ τ' := (le_mul_of_one_le_left zero_le (by norm_num)).trans (hττ' k)
  have hτ' : (0 : ℝ) < τ' := NNReal.coe_pos.2 ((hτ 0).trans_le (hτkτ' 0))
  have hEA : 0 ≤ E - A := sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  have hAk k : moreauYosida φ τ' (U k 0) = A := by rw [hU0]; exact hA
  have hEk k : φ (U k 0) = E := by rw [hU0]; exact hE
  -- Up to time `t`, the a priori bounds hold with the constant `B t`, uniformly in `k`.
  set B : ℝ → ℝ := fun t ↦ Real.exp (8 * (t + τ') / τ') with hB
  have hexpk k (t : ℝ) : Real.exp (8 * (t + τ k) / τ') ≤ B t :=
    Real.exp_le_exp.2 (by gcongr; exact_mod_cast hτkτ' k)
  -- The interpolants `v k` take their values at time `t` in a set `K t` of bounded diameter and
  -- energy at most `E`.
  set v : ℕ → ℝ≥0 → X := fun k t ↦ U k ⌈(t : ℝ) / τ k⌉₊ with hv
  set K : ℝ≥0 → Set X :=
    fun t ↦ {y | φ y ≤ E ∧ edist x₀ y ≤ ENNReal.ofReal (2 * τ' * (E - A) * B t) ^ (2⁻¹ : ℝ)}
    with hK_def
  have hvK k t : v k t ∈ K t := by
    refine ⟨?_, (ENNReal.le_rpow_inv_iff two_pos).2 ?_⟩
    · have := antitone_comp_of_forall_mem_moreauYosidaResolvent (hU k)
        (Nat.zero_le ⌈(t : ℝ) / τ k⌉₊)
      simpa only [Function.comp_apply, hEk] using this
    · have h1 := edist_sq_le_of_forall_mem_moreauYosidaResolvent (hU k) (hτ k) (hττ' k) (hAk k)
        (hEk k) ⌈(t : ℝ) / τ k⌉₊
      rw [hU0] at h1
      rw [ENNReal.rpow_two]
      refine h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (by positivity) hEA)))
      have := one_add_mul_pow_ceil_div_le_exp (a := 8 / τ') (by positivity)
        (NNReal.coe_pos.2 (hτ k)) t.2
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at this
      exact this.trans (hexpk k t)
  have hK t ⦃w : ℕ → X⦄ (hw : ∀ n, w n ∈ K t) :
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (w ∘ ψ) atTop (l y) := by
    refine hcpt E (ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * τ' * (E - A) * B t) ^ (2⁻¹ : ℝ) +
      ENNReal.ofReal (2 * τ' * (E - A) * B t) ^ (2⁻¹ : ℝ)) (by finiteness) (Metric.ediam_le ?_))
      fun n ↦ (hw n).1
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (edist_triangle_left _ _ x₀).trans (add_le_add (hw i).2 (hw j).2)
  -- The asymptotic modulus `ω s t = (2 |t - s| (E - A) (1 + B (max s t))) ^ (1 / 2)`.
  set ω : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun s t ↦
    ENNReal.ofReal (2 * |(t : ℝ) - s| * (E - A) * (1 + B (max (s : ℝ) t))) ^ (2⁻¹ : ℝ)
    with hω_def
  have hvω_le s t (hst : s ≤ t) : limsup (fun k ↦ edist (v k s) (v k t)) atTop ≤ ω s t := by
    have hst' : (s : ℝ) ≤ t := hst
    set g : ℝ → ℝ≥0∞ :=
      fun x ↦ ENNReal.ofReal (2 * ((t : ℝ) - s + x) * (E - A) * (1 + B t)) ^ (2⁻¹ : ℝ)
    have hg : Continuous g :=
      ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp (by fun_prop))
    have hle k : edist (v k s) (v k t) ≤ g (τ k) := by
      refine (ENNReal.le_rpow_inv_iff two_pos).2 ?_
      rw [ENNReal.rpow_two]
      refine (edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent (hU k)
        (hτ k) (hττ' k) (hAk k) (hEk k) s.2 hst').trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (t : ℝ) - s + τ k := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith [hexpk k t])
        (mul_nonneg (mul_nonneg zero_le_two this) hEA)
    calc limsup (fun k ↦ edist (v k s) (v k t)) atTop
        ≤ limsup (fun k ↦ g (τ k)) atTop := limsup_le_limsup (Eventually.of_forall hle)
      _ = g 0 := ((hg.tendsto 0).comp (NNReal.tendsto_coe.2 hτ0)).limsup_eq
      _ = ω s t := by simp [g, hω_def, abs_of_nonneg (sub_nonneg.2 hst'), max_eq_right hst']
  have hvω s t : limsup (fun k ↦ edist (v k s) (v k t)) atTop ≤ ω s t := by
    rcases le_total s t with h | h
    · exact hvω_le s t h
    · have hcomm : (fun k ↦ edist (v k s) (v k t)) = fun k ↦ edist (v k t) (v k s) :=
        funext fun k ↦ edist_comm _ _
      rw [hcomm, show ω s t = ω t s by simp only [hω_def, abs_sub_comm, max_comm]]
      exact hvω_le t s h
  have hω t : Tendsto (ω t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (ω t) :=
      ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp (by fun_prop))
    simpa [hω_def] using hc.tendsto t
  -- The refined Arzelà–Ascoli theorem gives the subsequence and the limit curve.
  obtain ⟨Ψ, hΨ, u, htend, hmod⟩ := tendsto_subseq_of_limsup_edist_le hd hvK hK hvω hω
  refine ⟨Ψ, hΨ, fun t ↦ u (Real.toNNReal t), fun t ht ↦ ?_, fun s t hs hst ↦ ?_⟩
  · simpa [hv, Real.coe_toNNReal t ht] using htend (Real.toNNReal t)
  · have h := hmod (Real.toNNReal s) (Real.toNNReal t)
    simp only [hω_def, Real.coe_toNNReal s hs, Real.coe_toNNReal t (hs.trans hst),
      abs_of_nonneg (sub_nonneg.2 hst), max_eq_right hst] at h
    rw [← ENNReal.rpow_two]
    exact (ENNReal.le_rpow_inv_iff two_pos).1 h

/-- **Existence of generalized minimizing movements** (Ambrosio–Gigli–Savaré, Section 2.2).
Let `l y` be the filter of an auxiliary convergence `y_n ⇀ y` on an extended metric space `X`,
possibly weaker than that of the metric, such that

* constant sequences converge, and the distance is jointly sequentially lower semicontinuous;
* `φ` is sequentially lower semicontinuous for `⇀` along sequences of finite diameter;
* every sequence of finite diameter along which `φ` is bounded above by a real number has a
  `⇀`-convergent subsequence;

and let `φ` be coercive: `φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`. Then from every point `x₀` of finite
energy at finite distance from `x₁` starts a generalized minimizing movement `u`, with `u 0 = x₀`,
which is `1/2`-Hölder continuous on every bounded time interval `[0, T]`. -/
theorem exists_isGeneralizedMinimizingMovement (hl : ∀ y, pure y ≤ l y)
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    (hφ : ∀ ⦃v : ℕ → X⦄ ⦃y : X⦄, Metric.ediam (range v) ≠ ⊤ → Tendsto v atTop (l y) →
      φ y ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : edist x₀ x₁ ≠ ⊤) (hφx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, IsGeneralizedMinimizingMovement l φ x₀ u ∧ u 0 = x₀ ∧
      ∀ T : ℝ, ∃ C : ℝ≥0, HolderOnWith C (1 / 2) u (Icc 0 T) := by
  -- The coercivity constant `A = φ_{τ'}(x₀)` at `τ' = τ₀ / 2`, and the energy `E = φ x₀`.
  set τ' : ℝ≥0 := τ₀ / 2 with hτ'_def
  have hAbot : moreauYosida φ τ' x₀ ≠ ⊥ := moreauYosida_ne_bot_of_lt (half_lt_self hτ₀) hx₀ h₀
  have hAtop : moreauYosida φ τ' x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hφx₀ (moreauYosida_le_self φ τ' x₀)
  have hEbot : φ x₀ ≠ ⊥ := fun h ↦ hAbot (le_bot_iff.1 (h ▸ moreauYosida_le_self φ τ' x₀))
  set A := (moreauYosida φ τ' x₀).toReal
  set E := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal hAtop hAbot).symm
  have hE : φ x₀ = E := (EReal.coe_toReal hφx₀ hEbot).symm
  have hEA : 0 ≤ E - A := sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  -- The time steps `τ' / (4 (k + 1))`, and minimizing movement sequences from `x₀`.
  set τ : ℕ → ℝ≥0 := fun k ↦ τ' / (4 * (k + 1)) with hτ_def
  have hτ k : 0 < τ k := by positivity
  have hττ' k : 4 * τ k ≤ τ' := by
    rw [← NNReal.coe_le_coe]
    push_cast [hτ_def]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k), NNReal.coe_nonneg τ']
  have hτ0 : Tendsto τ atTop (𝓝 0) := by
    refine NNReal.tendsto_coe.1 ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((τ' : ℝ) / 4)
    rw [mul_zero] at this
    refine this.congr fun k ↦ ?_
    push_cast [hτ_def]
    field_simp
  choose U hU0 hU using fun k ↦ exists_forall_mem_moreauYosidaResolvent
    (fun z _ _ hv ↦ hd (tendsto_const_pure.mono_right (hl z)) hv) hφ hcpt (hτ k)
    (((le_mul_of_one_le_left zero_le (by norm_num)).trans (hττ' k)).trans_lt (half_lt_self hτ₀))
    hx₀ h₀
  -- The limit curve of a subsequence of the interpolants.
  obtain ⟨Ψ, hΨ, u, htend, hmod⟩ :=
    tendsto_subseq_of_forall_mem_moreauYosidaResolvent hd hcpt hτ hττ' hτ0 hU hU0 hA hE
  have hgmm : IsGeneralizedMinimizingMovement l φ x₀ u := isGeneralizedMinimizingMovement_iff.2
    ⟨fun k ↦ τ (Ψ k), fun k ↦ U (Ψ k), fun k ↦ hτ _, hτ0.comp hΨ.tendsto_atTop,
      fun k ↦ hU (Ψ k), by simpa only [hU0] using tendsto_const_nhds, ⟨E, fun k ↦ (hU0 _ ▸ hE).le⟩,
      htend⟩
  refine ⟨u, hgmm, hgmm.apply_zero hl hd, fun T ↦ ?_⟩
  -- The `1/2`-Hölder bound on `[0, T]`, with constant
  -- `(2 (E - A) (1 + exp (8 (T + τ') / τ'))) ^ (1 / 2)`.
  set c : ℝ := 2 * (E - A) * (1 + Real.exp (8 * (T + τ') / τ')) with hc
  have hc0 : 0 ≤ c := by positivity
  have hsq : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → edist (u s) (u t) ^ 2 ≤
      ENNReal.ofReal (c * |s - t|) := fun s hs t ht hst ↦ by
    refine (hmod s t hs.1 hst).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst), hc]
    have hB : Real.exp (8 * (t + τ') / τ') ≤ Real.exp (8 * (T + τ') / τ') :=
      Real.exp_le_exp.2 (by gcongr; exact ht.2)
    nlinarith [mul_le_mul_of_nonneg_left hB (mul_nonneg (mul_nonneg zero_le_two hEA)
      (sub_nonneg.2 hst))]
  refine ⟨c.toNNReal ^ (2⁻¹ : ℝ), fun s hs t ht ↦
    ((ENNReal.le_rpow_inv_iff (y := ENNReal.ofReal (c * |s - t|)) two_pos).2 ?_).trans_eq ?_⟩
  · rw [ENNReal.rpow_two]
    rcases le_total s t with hst | hst
    · exact hsq s hs t ht hst
    · rw [edist_comm, abs_sub_comm]
      exact hsq t ht s hs hst
  · rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ENNReal.ofNNReal_toNNReal, edist_dist,
      Real.dist_eq, show ((1 / 2 : ℝ≥0) : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_mul hc0,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

end EMetricSpace

end TauCeti
