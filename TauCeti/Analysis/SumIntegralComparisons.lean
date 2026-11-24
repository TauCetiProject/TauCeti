/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Darboux sums and decreasing integrable functions

For a nonnegative decreasing integrable function on the positive half-line, the upper and
lower uniform-mesh Darboux sums bracket its integral. Their difference is exactly the mesh
size times the value at zero. Consequently both sums converge to the integral as the mesh
tends to zero through positive values, even on the unbounded interval and without continuity.
These estimates allow step-function approximations in convolution limit theorems.
Finite uniform-mesh sums also bracket the integral on `[0, δ * N]`, including zero mesh,
and their gap vanishes under refinement of a fixed interval. For a decreasing or increasing
function on `[x₀, x₀ + a]` with `a` a natural number, the sum of its values at the right
endpoints of the unit cells differs from its integral by at most `|f x₀ - f (x₀ + a)|`.
A nonnegative decreasing integrable function on the positive half-line vanishes at infinity.

For `f` nonnegative and decreasing on `[a, ∞)`, with `a` a natural number, the differences
`∑_{a < n ≤ N} f n - ∫_a^N f` decrease (`AntitoneOn.antitoneOn_sum_Ioc_sub_integral`), while
subtracting `∫_N^{N+1} f` from them gives an increasing sequence
(`AntitoneOn.monotoneOn_sum_Ioc_sub_integral_sub_integral`). They converge to a constant `C`,
the constant of the Maclaurin–Cauchy integral test
(`AntitoneOn.exists_tendsto_sum_Ioc_sub_integral`); for every real `x ≥ a`,
`∑_{a < n ≤ x} f n - ∫_a^x f` lies within `f x` of `C`
(`AntitoneOn.abs_sum_Ioc_natFloor_sub_integral_sub_le`). Decreasing functions on `[c, ∞)` are
interval integrable between any two points of `[c, ∞)` (`AntitoneOn.intervalIntegrable_of_le`).
Euler's constant `γ` and the first Stieltjes constant arise in this way from `f x = 1 / x` and
`f x = log x / x`, once the terms with `n ≤ a` and the integral over `[1, a]` are added back.

The proofs use Mathlib's integral test (`AntitoneOn.summable_of_integrableOn_Ioi_zero`,
`AntitoneOn.tsum_add_one_le_integral`, and `AntitoneOn.integral_le_tsum`) after dilation,
and the finite comparisons `AntitoneOn.sum_le_integral`, `AntitoneOn.integral_le_sum`,
`AntitoneOn.sum_le_integral_Ico` and `AntitoneOn.integral_le_sum_Ico`.
The half-line approximation is used in Feller, *An Introduction to Probability Theory and
Its Applications*, vol. II, second edition, Chapter XI, in the key renewal theorem.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace AntitoneOn

variable {f : ℝ → ℝ}

/-- A positive-mesh sample of a nonnegative decreasing integrable function on the half-line
is summable, including its value at zero. -/
theorem summable_mul_natCast (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) : Summable (fun n : ℕ => f (δ * n)) := by
  have hanti : AntitoneOn (fun x => f (δ * x)) (Ici 0) :=
    fun x hx y hy hxy => hf (mul_nonneg hδ.le hx) (mul_nonneg hδ.le hy)
      (mul_le_mul_of_nonneg_left hxy hδ.le)
  have hint : IntegrableOn (fun x => f (δ * x)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff f 0 hδ).2 (by simpa using hi)
  exact hanti.summable_of_integrableOn_Ioi_zero hint fun x hx => hn _ (mul_pos hδ hx)

/-- Lower and upper uniform-mesh Darboux sums bracket the half-line integral. No continuity
is needed, and either sum may include values at discontinuities. -/
theorem mul_tsum_le_integral_le_mul_tsum (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) :
    δ * (∑' n : ℕ, f (δ * (n + 1))) ≤ ∫ x in Ioi 0, f x ∧
      (∫ x in Ioi 0, f x) ≤ δ * (∑' n : ℕ, f (δ * n)) := by
  have hanti : AntitoneOn (fun x => f (δ * x)) (Ici 0) :=
    fun x hx y hy hxy => hf (mul_nonneg hδ.le hx) (mul_nonneg hδ.le hy)
      (mul_le_mul_of_nonneg_left hxy hδ.le)
  have hint : IntegrableOn (fun x => f (δ * x)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff f 0 hδ).2 (by simpa using hi)
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f (δ * x) :=
    fun x hx => hn _ (mul_pos hδ hx)
  have hscale : δ * (∫ x in Ioi 0, f (δ * x)) = ∫ x in Ioi 0, f x := by
    simpa using integral_comp_mul_left_Ioi' f 0 hδ
  constructor
  · have h := mul_le_mul_of_nonneg_left (hanti.tsum_add_one_le_integral hint hnonneg) hδ.le
    simpa only [Nat.cast_add, Nat.cast_one, hscale] using h
  · have h := mul_le_mul_of_nonneg_left
      (hanti.integral_le_tsum (hf.summable_mul_natCast hi hn hδ) hnonneg) hδ.le
    rwa [hscale] at h

/-- The error in the upper half-line Darboux sum is at most the mesh times the value at zero.
In particular this controls the infinite tail as well as the bounded part of the integral. -/
theorem abs_mul_tsum_sub_integral_le (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) :
    |δ * (∑' n : ℕ, f (δ * n)) - ∫ x in Ioi 0, f x| ≤ δ * f 0 := by
  obtain ⟨hl, hu⟩ := hf.mul_tsum_le_integral_le_mul_tsum hi hn hδ
  have hsum := (hf.summable_mul_natCast hi hn hδ).tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsum
  rw [abs_of_nonneg (sub_nonneg.mpr hu), hsum, mul_add]
  linarith

/-- Upper uniform-mesh Darboux sums of a nonnegative decreasing integrable function converge
to its integral as the mesh tends to zero from above. -/
theorem tendsto_mul_tsum_integral (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto (fun δ : ℝ => δ * ∑' n : ℕ, f (δ * n)) (𝓝[>] 0)
      (𝓝 (∫ x in Ioi 0, f x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g := fun δ : ℝ => δ * f 0)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa only [Real.norm_eq_abs] using hf.abs_mul_tsum_sub_integral_le hi hn hδ
  · have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using hid.mul_const (f 0)

/-- Lower uniform-mesh Darboux sums have the same integral limit. This remains valid for
functions with jumps, including a jump at zero. -/
theorem tendsto_mul_tsum_add_one_integral (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto (fun δ : ℝ => δ * ∑' n : ℕ, f (δ * (n + 1))) (𝓝[>] 0)
      (𝓝 (∫ x in Ioi 0, f x)) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (hf.tendsto_mul_tsum_integral hi hn).sub (hid.mul_const (f 0))
  simp only [zero_mul, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hsum := (hf.summable_mul_natCast hi hn hδ).tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum, mul_add, add_sub_cancel_left]

/-- Finite uniform-mesh Darboux sums bracket the integral of a decreasing function.
The endpoints of the interval are zero and the mesh times the number of cells. -/
theorem mul_sum_le_integral_le_mul_sum {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hf : AntitoneOn f (Icc 0 (δ * N))) :
    δ * (∑ k ∈ Finset.range N, f (δ * (k + 1))) ≤ ∫ x in 0..δ * N, f x ∧
      (∫ x in 0..δ * N, f x) ≤ δ * (∑ k ∈ Finset.range N, f (δ * k)) := by
  have hg : AntitoneOn (fun x => f (δ * x)) (Icc 0 (N : ℝ)) := by
    intro x hx y hy hxy
    exact hf ⟨mul_nonneg hδ hx.1, mul_le_mul_of_nonneg_left hx.2 hδ⟩
      ⟨mul_nonneg hδ hy.1, mul_le_mul_of_nonneg_left hy.2 hδ⟩
      (mul_le_mul_of_nonneg_left hxy hδ)
  have heq : δ * (∫ x in (0 : ℝ)..N, f (δ * x)) = ∫ x in 0..δ * N, f x := by
    simpa using intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := N) f δ
  have hg' : AntitoneOn (fun x => f (δ * x)) (Icc 0 (0 + (N : ℝ))) := by
    simpa only [zero_add] using hg
  constructor
  · have hl := mul_le_mul_of_nonneg_left (hg'.sum_le_integral (x₀ := 0) (a := N)) hδ
    simpa only [zero_add, Nat.cast_add, Nat.cast_one, heq] using hl
  · have hu := mul_le_mul_of_nonneg_left (hg'.integral_le_sum (x₀ := 0) (a := N)) hδ
    simpa only [zero_add, heq] using hu

/-- Uniform-mesh sums bracket a nonnegative multiple of the integral on `[0, A]`, and
their gap tends to zero as the mesh is refined. The function can have either sign. -/
theorem uniform_mesh_darboux_bounds {A : ℝ} (hf : AntitoneOn f (Icc 0 A))
    (hA : 0 ≤ A) {r : ℝ} (hr : 0 ≤ r) :
    let δ (n : ℕ) : ℝ := A / (n + 1)
    let p (n k : ℕ) : ℝ := δ n * k
    let L (n : ℕ) : ℝ := r * δ n * ∑ k ∈ Finset.range (n + 1), f (p n (k + 1))
    let U (n : ℕ) : ℝ := r * δ n * ∑ k ∈ Finset.range (n + 1), f (p n k)
    (∀ n, L n ≤ r * ∫ x in (0 : ℝ)..A, f x ∧
      r * (∫ x in (0 : ℝ)..A, f x) ≤ U n) ∧
      Tendsto (fun n => U n - L n) atTop (𝓝 0) := by
  intro δ p L U
  have hp0 (n : ℕ) : p n 0 = 0 := by simp [p]
  have hpN (n : ℕ) : p n (n + 1) = A := by
    dsimp [p, δ]
    simp only [Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ A (by positivity)
  constructor
  · intro n
    have hend : δ n * ↑(n + 1) = A := hpN n
    have hf' : AntitoneOn f (Icc 0 (δ n * ↑(n + 1))) := by rwa [hend]
    have hb : δ n * (∑ k ∈ Finset.range (n + 1), f (δ n * (k + 1))) ≤
        ∫ x in (0 : ℝ)..A, f x ∧
        (∫ x in (0 : ℝ)..A, f x) ≤ δ n * ∑ k ∈ Finset.range (n + 1), f (δ n * k) := by
      simpa only [hend] using hf'.mul_sum_le_integral_le_mul_sum (δ := δ n)
        (div_nonneg hA (by positivity) : 0 ≤ δ n) (n + 1)
    exact ⟨by simpa only [L, p, Nat.cast_add, Nat.cast_one, mul_assoc] using
      mul_le_mul_of_nonneg_left hb.1 hr,
      by simpa only [U, p, mul_assoc] using mul_le_mul_of_nonneg_left hb.2 hr⟩
  · have hgap (n : ℕ) : U n - L n = r * δ n * (f 0 - f A) := by
      have hs := Finset.sum_range_sub' (fun k => f (p n k)) (n + 1)
      simp only [hp0, hpN] at hs
      dsimp [U, L]
      rw [← mul_sub, ← Finset.sum_sub_distrib, hs]
    have hdlim : Tendsto δ atTop (𝓝 0) := by
      simpa only [δ] using (tendsto_const_nhds (x := A)).div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
          (tendsto_const_nhds (x := (1 : ℝ))))
    simpa only [hgap, mul_zero, zero_mul] using (hdlim.const_mul r).mul_const (f 0 - f A)

/-- A nonnegative decreasing integrable function on the positive half-line vanishes at
infinity, without any continuity assumption. -/
theorem tendsto_zero_of_integrableOn_Ioi (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto f atTop (𝓝 0) := by
  have hs := (hf.summable_of_integrableOn_Ioi_zero hi hn).tendsto_atTop_zero
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ha.trans_le (hn x hx)
  · obtain ⟨n, hn'⟩ := (hs.eventually_lt_const hb).exists
    filter_upwards [eventually_ge_atTop (n : ℝ)] with x hx
    exact (hf (Nat.cast_nonneg n) ((Nat.cast_nonneg n).trans hx) hx).trans_lt hn'

/-- The sum of a decreasing function at the right endpoints of the unit cells of
`[x₀, x₀ + a]` differs from its integral by at most `f x₀ - f (x₀ + a)`. -/
theorem abs_sum_range_sub_integral_le {x₀ : ℝ} {a : ℕ} (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    |∑ i ∈ Finset.range a, f (x₀ + ↑(i + 1)) - ∫ x in x₀..x₀ + a, f x| ≤
      f x₀ - f (x₀ + a) := by
  have htel := Finset.sum_range_sub' (fun i : ℕ => f (x₀ + i)) a
  rw [Finset.sum_sub_distrib, Nat.cast_zero, add_zero] at htel
  rw [abs_le]
  constructor <;> linarith [hf.integral_le_sum, hf.sum_le_integral]

/-! ### The integral-test constant -/

section IntegralTestConstant

variable {a : ℕ}

/-- A function decreasing on `[c, ∞)` is interval integrable between any two points of
`[c, ∞)`. -/
theorem intervalIntegrable_of_le {c u v : ℝ} (hf : AntitoneOn f (Ici c)) (hu : c ≤ u)
    (hv : c ≤ v) : IntervalIntegrable f volume u v :=
  (hf.mono fun _ (ht : _ ∈ uIcc u v) => (le_inf hu hv).trans ht.1).intervalIntegrable

/-- For `f` decreasing on `[a, ∞)`, the differences `∑_{a < n ≤ N} f n - ∫_a^N f` decrease
for natural `N ≥ a`. -/
theorem antitoneOn_sum_Ioc_sub_integral (hf : AntitoneOn f (Ici (a : ℝ))) :
    AntitoneOn (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t) (Ici a) := by
  intro N (hN : a ≤ N) M (hM : a ≤ M) hNM
  have hN' : (a : ℝ) ≤ N := Nat.cast_le.2 hN
  have hM' : (a : ℝ) ≤ M := Nat.cast_le.2 hM
  -- the right-endpoint sum over `(N, M]` lies below `∫_N^M f`
  have hsum : ∑ n ∈ Finset.Ioc N M, f n ≤ ∫ t in (N : ℝ)..M, f t := by
    have h := (hf.mono fun t (ht : t ∈ Icc (N : ℝ) M) => hN'.trans ht.1).sum_le_integral_Ico hNM
    rwa [Finset.sum_Ico_add' (fun n : ℕ => f n) N M 1, Finset.Ico_add_one_add_one_eq_Ioc] at h
  simp only
  rw [← Finset.sum_Ioc_consecutive _ hN hNM, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le le_rfl hN') (hf.intervalIntegrable_of_le hN' hM')]
  linarith

/-- For `f` decreasing on `[a, ∞)`, the differences `∑_{a < n ≤ N} f n - ∫_a^N f - ∫_N^{N+1} f`
increase for natural `N ≥ a`: between `a ≤ N ≤ M`, the differences
`∑_{a < n ≤ N} f n - ∫_a^N f` decrease by at most `∫_N^{N+1} f - ∫_M^{M+1} f`. -/
theorem monotoneOn_sum_Ioc_sub_integral_sub_integral (hf : AntitoneOn f (Ici (a : ℝ))) :
    MonotoneOn (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - (∫ t in (a : ℝ)..N, f t) -
      ∫ t in (N : ℝ)..N + 1, f t) (Ici a) := by
  intro N (hN : a ≤ N) M (hM : a ≤ M) hNM
  have hN' : (a : ℝ) ≤ N := Nat.cast_le.2 hN
  have hM' : (a : ℝ) ≤ M := Nat.cast_le.2 hM
  -- the right-endpoint sum over `(N, M]` lies above `∫_{N+1}^{M+1} f`
  have hint : ∫ t in (N : ℝ) + 1..(M : ℝ) + 1, f t ≤ ∑ n ∈ Finset.Ioc N M, f n := by
    have h := (hf.mono fun t (ht : t ∈ Icc ((N + 1 : ℕ) : ℝ) (M + 1 : ℕ)) =>
      (Nat.cast_le.2 (hN.trans N.le_succ)).trans ht.1).integral_le_sum_Ico
      (Nat.add_le_add_right hNM 1)
    rw [Finset.Ico_add_one_add_one_eq_Ioc] at h
    exact_mod_cast h
  simp only
  rw [← Finset.sum_Ioc_consecutive _ hN hNM, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le le_rfl hN') (hf.intervalIntegrable_of_le hN' hM')]
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le (v := (N : ℝ) + 1) hN' (by linarith))
    (hf.intervalIntegrable_of_le (v := (M : ℝ) + 1) (by linarith) (by linarith))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le hN' hM')
    (hf.intervalIntegrable_of_le (v := (M : ℝ) + 1) hM' (by linarith))
  linarith

/-- **The integral-test constant.** For `f` nonnegative and decreasing on `[a, ∞)`, with `a` a
natural number, the differences `∑_{a < n ≤ N} f n - ∫_a^N f` converge as `N → ∞`. -/
theorem exists_tendsto_sum_Ioc_sub_integral (hf : AntitoneOn f (Ici (a : ℝ)))
    (nonneg : ∀ x ∈ Ici (a : ℝ), 0 ≤ f x) :
    ∃ C, Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t) atTop
      (𝓝 C) := by
  set e := fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t
  have hanti : Antitone fun k : ℕ => e (k + a) := antitone_nat_of_succ_le fun k =>
    hf.antitoneOn_sum_Ioc_sub_integral (Nat.le_add_left a k) (Nat.le_add_left a (k + 1))
      (by omega)
  have hbdd : BddBelow (range fun k : ℕ => e (k + a)) := by
    refine ⟨e a - ∫ t in (a : ℝ)..a + 1, f t, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h := hf.monotoneOn_sum_Ioc_sub_integral_sub_integral (le_refl a) (Nat.le_add_left a k)
      (Nat.le_add_left a k)
    have hk : (a : ℝ) ≤ (k + a : ℕ) := Nat.cast_le.2 (Nat.le_add_left a k)
    have h0 : 0 ≤ ∫ t in ((k + a : ℕ) : ℝ)..(k + a : ℕ) + 1, f t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht => nonneg t (hk.trans ht.1)
    simp only [e] at h ⊢
    linarith
  exact ⟨_, (tendsto_add_atTop_iff_nat a).1 (tendsto_atTop_ciInf hanti hbdd)⟩

/-- For `f` decreasing on `[a, ∞)`, the differences `∑_{a < n ≤ N} f n - ∫_a^N f` decrease from
`N = a` on, so they all lie above their limit. -/
theorem le_sum_Ioc_sub_integral (hf : AntitoneOn f (Ici (a : ℝ))) {C : ℝ}
    (hC : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t) atTop (𝓝 C))
    {N : ℕ} (hN : a ≤ N) : C ≤ ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t :=
  le_of_tendsto hC <| eventually_atTop.2 ⟨N, fun _ hM =>
    hf.antitoneOn_sum_Ioc_sub_integral hN (hN.trans hM) hM⟩

/-- For `f` nonnegative and decreasing on `[a, ∞)`, each difference
`∑_{a < n ≤ N} f n - ∫_a^N f` with `N ≥ a` exceeds the limit `C` by at most `∫_N^{N+1} f`. -/
theorem sum_Ioc_sub_integral_le_add_integral (hf : AntitoneOn f (Ici (a : ℝ)))
    (nonneg : ∀ x ∈ Ici (a : ℝ), 0 ≤ f x) {C : ℝ}
    (hC : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t) atTop (𝓝 C))
    {N : ℕ} (hN : a ≤ N) :
    ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t ≤ C + ∫ t in (N : ℝ)..N + 1, f t := by
  rw [← sub_le_iff_le_add]
  refine ge_of_tendsto hC <| eventually_atTop.2 ⟨N, fun M hM => ?_⟩
  have h := hf.monotoneOn_sum_Ioc_sub_integral_sub_integral hN (hN.trans hM) hM
  have hM' : (a : ℝ) ≤ M := Nat.cast_le.2 (hN.trans hM)
  have h0 : 0 ≤ ∫ t in (M : ℝ)..M + 1, f t :=
    intervalIntegral.integral_nonneg (by linarith) fun t ht => nonneg t (hM'.trans ht.1)
  linarith

/-- **Sum–integral comparison with the integral-test constant.** Let `f` be nonnegative and
decreasing on `[a, ∞)`, with `a` a natural number, and let `C` be the limit of
`∑_{a < n ≤ N} f n - ∫_a^N f`. Then for every real `x ≥ a`,
`∑_{a < n ≤ x} f n = ∫_a^x f + C + O*(f x)`. -/
theorem abs_sum_Ioc_natFloor_sub_integral_sub_le (hf : AntitoneOn f (Ici (a : ℝ)))
    (nonneg : ∀ x ∈ Ici (a : ℝ), 0 ≤ f x) {C : ℝ}
    (hC : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc a N, f n - ∫ t in (a : ℝ)..N, f t) atTop (𝓝 C))
    {x : ℝ} (hx : a ≤ x) :
    |∑ n ∈ Finset.Ioc a ⌊x⌋₊, f n - (∫ t in (a : ℝ)..x, f t) - C| ≤ f x := by
  set N := ⌊x⌋₊
  have hN : a ≤ N := Nat.le_floor hx
  have hN' : (a : ℝ) ≤ N := Nat.cast_le.2 hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (a.cast_nonneg.trans hx)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le le_rfl hN') (hf.intervalIntegrable_of_le hN' hx)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le hN' hx)
    (hf.intervalIntegrable_of_le (v := (N : ℝ) + 1) hx (by linarith))
  have hup := hf.sum_Ioc_sub_integral_le_add_integral nonneg hC hN
  have hlow := hf.le_sum_Ioc_sub_integral hC (hN.trans N.le_succ)
  rw [Finset.sum_Ioc_succ_top hN] at hlow
  push_cast at hlow
  have h₃ := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable_of_le le_rfl hN')
    (hf.intervalIntegrable_of_le (v := (N : ℝ) + 1) hN' (by linarith))
  have hI₀ : 0 ≤ ∫ t in x..N + 1, f t :=
    intervalIntegral.integral_nonneg hxN.le fun t ht => nonneg t (hx.trans ht.1)
  have hI₁ : ∫ t in x..N + 1, f t ≤ f x :=
    calc ∫ t in x..N + 1, f t ≤ ∫ _ in x..N + 1, f x :=
          intervalIntegral.integral_mono_on hxN.le (hf.intervalIntegrable_of_le hx (by linarith))
            intervalIntegrable_const fun t ht => hf hx (hx.trans ht.1) ht.1
      _ = (N + 1 - x) * f x := by simp
      _ ≤ f x := by nlinarith [nonneg x hx]
  have hfN : f (N + 1) ≤ f x := hf hx (by simp only [mem_Ici]; linarith) hxN.le
  rw [abs_le]
  constructor <;> linarith

end IntegralTestConstant

end AntitoneOn

/-- The sum of an increasing function at the right endpoints of the unit cells of
`[x₀, x₀ + a]` differs from its integral by at most `f (x₀ + a) - f x₀`. -/
theorem MonotoneOn.abs_sum_range_sub_integral_le {f : ℝ → ℝ} {x₀ : ℝ} {a : ℕ}
    (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    |∑ i ∈ Finset.range a, f (x₀ + ↑(i + 1)) - ∫ x in x₀..x₀ + a, f x| ≤
      f (x₀ + a) - f x₀ := by
  have h := hf.neg.abs_sum_range_sub_integral_le
  rwa [Finset.sum_neg_distrib, intervalIntegral.integral_neg, neg_sub_neg, abs_sub_comm,
    sub_neg_eq_add, neg_add_eq_sub] at h
