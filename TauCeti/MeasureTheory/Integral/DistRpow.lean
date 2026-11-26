/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The tail integral of a negative power of the distance

In a pseudometric measure space whose balls of radius `r > R` satisfy the growth bound
`μ (ball y r) ≤ A rⁿ` (with `A : ℝ≥0∞`), the tail integral of `x ↦ dist x y ^ (-s)` obeys,
for `n < s` and `R > 0`, the extended-valued bound

`∫_{dist x y > R} dist x y ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`

(`TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`). When `A < ∞` the right-hand side is finite, so
`dist x y ^ (-s)` is integrable on `{x | R < dist x y}`. The exponent `n` need not be an integer.
For an additive Haar measure on a finite-dimensional real normed space the growth bound holds with
`n` the dimension and `A` the measure of the unit ball
(`MeasureTheory.Measure.setLIntegral_ofReal_norm_rpow_neg_le`).

More generally, the measure may be replaced by a weight `g ≥ 0` whose mass on balls grows like a
power of the radius, `∫_{B(y, r)} g ≤ M r^λ`. Away from the pole, for `0 ≤ s` and `λ < s`,

`∫_{dist x y ≥ R} dist x y ^ (-s) g(x) dx ≤ M 2^λ R ^ (λ - s) / (1 - 2 ^ (λ - s))`

(`TauCeti.setLIntegral_ofReal_dist_rpow_neg_mul_le`), and near the pole, for `0 ≤ s < λ`,

`∫_{B(y, ρ)} dist x y ^ (-s) g(x) dx ≤ M 2^s ρ ^ (λ - s) / (1 - 2 ^ (s - λ))`

(`TauCeti.setLIntegral_ball_ofReal_dist_rpow_neg_mul_le`). These are the two halves of the
estimates for potentials of functions in Morrey spaces, where `g = |f|`.

For `0 ≤ s` the proofs split the region into dyadic annuli: `2ᵏ R ≤ dist x y < 2ᵏ⁺¹ R` away from
the pole and `2⁻ᵏ⁻¹ ρ < dist x y ≤ 2⁻ᵏ ρ` near it. On each annulus `dist x y ^ (-s)` is at most
its value on the inner sphere, and the annulus lies in a ball of mass at most `M` times a power of
its radius, so the annuli contribute a convergent geometric series. The unweighted bound is the
case `g = 1`. For `s < 0` the dyadic bound on an annulus fails and the unweighted statement is
degenerate: if `A < ∞` the growth bound forces `μ = 0`, and if `A = ∞` the right-hand side is
`∞`.

## Main declarations

* `TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`: the tail bound for `dist x y ^ (-s)`.
* `TauCeti.setLIntegral_ofReal_dist_rpow_neg_mul_le`,
  `TauCeti.setLIntegral_ball_ofReal_dist_rpow_neg_mul_le`: the bounds against a weight, away from
  and near the pole.
* `TauCeti.ofReal_dist_rpow_neg_le_tsum`: off the ball `B(c, 2 r)`, `dist z c ^ (-s)` is dominated
  by a sum over the dyadic balls `B(c, 2^(k+2) r)` of the value `(2^(k+1) r) ^ (-s)` it bounds on
  the `k`-th annulus.
* `MeasureTheory.Measure.setLIntegral_ofReal_norm_rpow_neg_le`: the tail bound for `‖x‖ ^ (-s)`
  under an additive Haar measure, for `s` above the dimension.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}

section Weighted

variable [OpensMeasurableSpace X]


/-- **A power of the distance against a weight, away from the pole.** If a weight `g` has mass
`∫_{B(y, r)} g ≤ M r^λ` on the balls about `y` of radius `r > R`, then for `λ < s`, `0 ≤ s` and
`R > 0`,

`∫_{dist x y ≥ R} dist x y ^ (-s) g(x) dx ≤ M 2^λ R^(λ - s) / (1 - 2^(λ - s))`. -/
theorem setLIntegral_ofReal_dist_rpow_neg_mul_le {y : X} {g : X → ℝ≥0∞} {M : ℝ≥0∞}
    {s lam R : ℝ} (hg : ∀ r, R < r → ∫⁻ x in ball y r, g x ∂μ ≤ M * ENNReal.ofReal (r ^ lam))
    (hs : 0 ≤ s) (hlams : lam < s) (hR : 0 < R) :
    ∫⁻ x in {x | R ≤ dist x y}, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ ≤
      M * ENNReal.ofReal (2 ^ lam / (1 - 2 ^ (lam - s)) * R ^ (lam - s)) := by
  set q : ℝ := 2 ^ (lam - s)
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq0 : 0 ≤ q := by positivity
  -- The dyadic annuli `2ᵏ R ≤ dist x y < 2ᵏ⁺¹ R` cover the region `R ≤ dist x y`.
  set S : ℕ → Set X := fun k => (fun x => dist x y) ⁻¹' Ico (2 ^ k * R) (2 ^ (k + 1) * R)
  have hcover : {x | R ≤ dist x y} ⊆ ⋃ k, S k := by
    intro x hx
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div hR).2 hx) one_lt_two
    exact mem_iUnion.2 ⟨k, (le_div_iff₀ hR).1 hk, (div_lt_iff₀ hR).1 hk'⟩
  -- On the `k`-th annulus the kernel is at most `(2ᵏ R) ^ (-s)`, and the annulus lies in the
  -- ball of radius `2ᵏ⁺¹ R`.
  have hS (k : ℕ) : ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ ≤
      M * ENNReal.ofReal (2 ^ lam * R ^ (lam - s) * q ^ k) := by
    set u : ℝ := 2 ^ k * R
    have hRu : R ≤ u := le_mul_of_one_le_left hR.le (one_le_pow₀ one_le_two)
    have hu : 0 < u := hR.trans_le hRu
    have hpow : u ^ (-s) * (2 * u) ^ lam = 2 ^ lam * R ^ (lam - s) * q ^ k := by
      have hqk : q ^ k * R ^ (lam - s) = u ^ (lam - s) := by
        rw [Real.rpow_pow_comm zero_le_two, ← Real.mul_rpow (by positivity) hR.le]
      rw [mul_assoc, mul_comm (R ^ _), hqk, sub_eq_add_neg, Real.rpow_add hu,
        Real.mul_rpow zero_le_two hu.le]
      ring
    have hSk : MeasurableSet (S k) :=
      measurableSet_Ico.preimage (continuous_id.dist continuous_const).measurable
    calc ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ
        ≤ ∫⁻ x in S k, ENNReal.ofReal (u ^ (-s)) * g x ∂μ := by
          exact setLIntegral_mono' hSk fun x hx => mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos hu hx.1 (neg_nonpos.2 hs))) _
      _ = ENNReal.ofReal (u ^ (-s)) * ∫⁻ x in S k, g x ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (u ^ (-s)) * (M * ENNReal.ofReal ((2 * u) ^ lam)) := by
          gcongr
          refine (lintegral_mono_set fun x hx => mem_ball.2 ?_).trans (hg _ (by linarith))
          exact hx.2.trans_eq (by ring)
      _ = M * ENNReal.ofReal (2 ^ lam * R ^ (lam - s) * q ^ k) := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), hpow]
  calc ∫⁻ x in {x | R ≤ dist x y}, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ
      ≤ ∫⁻ x in ⋃ k, S k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' k, M * ENNReal.ofReal (2 ^ lam * R ^ (lam - s) * q ^ k) := by gcongr with k; exact hS k
    _ = M * ENNReal.ofReal (2 ^ lam / (1 - q) * R ^ (lam - s)) := by
        rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
          ((summable_geometric_of_lt_one hq0 hq1).mul_left _), tsum_mul_left,
          tsum_geometric_of_lt_one hq0 hq1]
        congr 2
        ring

/-- **The tail of a power of the distance.** If the balls about `y` of radius `r > R` satisfy the
growth bound `μ (ball y r) ≤ A rⁿ`, then for `n < s` and `R > 0`,

`∫_{dist x y > R} dist x y ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`. -/
theorem setLIntegral_ofReal_dist_rpow_neg_le {y : X} {A : ℝ≥0∞} {n s R : ℝ}
    (hμ : ∀ r, R < r → μ (ball y r) ≤ A * ENNReal.ofReal (r ^ n))
    (hns : n < s) (hR : 0 < R) :
    ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ ≤
      A * ENNReal.ofReal (2 ^ n / (1 - 2 ^ (n - s)) * R ^ (n - s)) := by
  set q : ℝ := 2 ^ (n - s)
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- For negative `s`, the growth bound forces `μ = 0` unless `A = ⊤`, when the bound is trivial.
  rcases lt_or_ge s 0 with hs | hs
  · by_cases hA : A = ⊤
    · have hpos : 0 < 2 ^ n / (1 - q) * R ^ (n - s) :=
        mul_pos (div_pos (by positivity) (sub_pos.2 hq1)) (by positivity)
      simp [hA, hpos]
    · have hball (r : ℝ) (hr : R < r) : μ (ball y r) = 0 := by
        refine le_antisymm (ge_of_tendsto (b := μ (ball y r)) (x := Filter.atTop)
          (f := fun t : ℝ ↦ A * ENNReal.ofReal (t ^ n)) ?_ ?_) bot_le
        · have h0 : Filter.Tendsto (fun t : ℝ ↦ t ^ n) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_neg_atTop (y := -n) (by linarith)
          simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h0) (Or.inr hA)
        · filter_upwards [Filter.eventually_ge_atTop r] with t ht
          exact (measure_mono (ball_subset_ball ht)).trans (hμ t (hr.trans_le ht))
      have hμ0 : μ = 0 := by
        refine Measure.measure_univ_eq_zero.1 ?_
        have : (univ : Set X) = ⋃ k : ℕ, ball y (R + k + 1) := by
          refine (eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_).symm
          obtain ⟨k, hk⟩ := exists_nat_gt (dist x y - R)
          exact ⟨k, mem_ball.2 (by linarith)⟩
        rw [this]
        exact measure_iUnion_null fun k ↦ hball _ (by linarith [k.cast_nonneg (α := ℝ)])
      simp [hμ0]
  -- For `s ≥ 0` this is the weighted bound for the weight `1`.
  calc ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ
      ≤ ∫⁻ x in {x | R ≤ dist x y}, ENNReal.ofReal (dist x y ^ (-s)) * 1 ∂μ := by
        simp_rw [mul_one]
        exact lintegral_mono_set fun x (hx : R < dist x y) => hx.le
    _ ≤ _ := setLIntegral_ofReal_dist_rpow_neg_mul_le (g := 1)
        (fun r hr => by simpa using hμ r hr) hs hns hR

/-- On the annulus `ρ / 2^(k+1) < dist x y ≤ ρ / 2^k`, the kernel `dist x y ^ (-s)`, `s ≥ 0`, is at
most its value `(ρ / 2^(k+1)) ^ (-s)` on the inner sphere, and the annulus lies in the closed ball
of radius `ρ / 2^k`, of mass at most `M (ρ / 2^k)^λ`. -/
private theorem setLIntegral_annulus_ofReal_dist_rpow_neg_mul_le {y : X} {g : X → ℝ≥0∞}
    {M : ℝ≥0∞} {s lam ρ : ℝ}
    (hg : ∀ r, 0 < r → r ≤ ρ → ∫⁻ x in closedBall y r, g x ∂μ ≤ M * ENNReal.ofReal (r ^ lam))
    (hs : 0 ≤ s) (hρ : 0 < ρ) (k : ℕ) :
    ∫⁻ x in (fun x => dist x y) ⁻¹' Ioc (ρ / 2 ^ (k + 1)) (ρ / 2 ^ k),
        ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ ≤
      M * ENNReal.ofReal (2 ^ s * ρ ^ (lam - s) * (2 ^ (s - lam)) ^ k) := by
  set T := (fun x => dist x y) ⁻¹' Ioc (ρ / 2 ^ (k + 1)) (ρ / 2 ^ k)
  set u : ℝ := ρ / 2 ^ k
  have hu : 0 < u := by positivity
  have hpow : (u / 2) ^ (-s) * u ^ lam = 2 ^ s * ρ ^ (lam - s) * (2 ^ (s - lam)) ^ k := by
    have hqk : ρ ^ (lam - s) * ((2 : ℝ) ^ (s - lam)) ^ k = u ^ (lam - s) := by
      rw [Real.rpow_pow_comm zero_le_two, Real.div_rpow hρ.le (by positivity),
        div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_sub]
    rw [mul_assoc, hqk, Real.div_rpow hu.le zero_le_two, Real.rpow_neg zero_le_two,
      div_eq_mul_inv, inv_inv, sub_eq_add_neg, Real.rpow_add hu]
    ring
  have hT : MeasurableSet T :=
    measurableSet_Ioc.preimage (continuous_id.dist continuous_const).measurable
  calc ∫⁻ x in T, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ
      ≤ ∫⁻ x in T, ENNReal.ofReal ((u / 2) ^ (-s)) * g x ∂μ := by
        refine setLIntegral_mono' hT fun x hx => mul_le_mul_left
          (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_
            (neg_nonpos.2 hs))) _
        exact (le_of_eq (by rw [pow_succ]; ring)).trans hx.1.le
    _ = ENNReal.ofReal ((u / 2) ^ (-s)) * ∫⁻ x in T, g x ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((u / 2) ^ (-s)) * (M * ENNReal.ofReal (u ^ lam)) := by
        gcongr
        exact (lintegral_mono_set (show T ⊆ closedBall y u from
          fun x hx => mem_closedBall.2 hx.2)).trans
          (hg u hu (div_le_self hρ.le (one_le_pow₀ one_le_two)))
    _ = M * ENNReal.ofReal (2 ^ s * ρ ^ (lam - s) * (2 ^ (s - lam)) ^ k) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), hpow]

/-- **A power of the distance against a weight, near the pole.** If a weight `g` has mass
`∫_{B(y, r)} g ≤ M r^λ` on the closed balls about `y` of radius `0 < r ≤ ρ`, then for
`0 ≤ s < λ`,

`∫_{B(y, ρ)} dist x y ^ (-s) g(x) dx ≤ M 2^s ρ^(λ - s) / (1 - 2^(s - λ))`. -/
theorem setLIntegral_ball_ofReal_dist_rpow_neg_mul_le {y : X} {g : X → ℝ≥0∞} {M : ℝ≥0∞}
    {s lam ρ : ℝ}
    (hg : ∀ r, 0 < r → r ≤ ρ → ∫⁻ x in closedBall y r, g x ∂μ ≤ M * ENNReal.ofReal (r ^ lam))
    (hs : 0 ≤ s) (hslam : s < lam) (hρ : 0 < ρ) :
    ∫⁻ x in ball y ρ, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ ≤
      M * ENNReal.ofReal (2 ^ s / (1 - 2 ^ (s - lam)) * ρ ^ (lam - s)) := by
  set q : ℝ := 2 ^ (s - lam)
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq0 : 0 ≤ q := by positivity
  rcases hs.eq_or_lt with rfl | hs
  · -- For `s = 0` the kernel is `1`.
    calc ∫⁻ x in ball y ρ, ENNReal.ofReal (dist x y ^ (-0 : ℝ)) * g x ∂μ
        = ∫⁻ x in ball y ρ, g x ∂μ := by simp
      _ ≤ ∫⁻ x in closedBall y ρ, g x ∂μ := lintegral_mono_set ball_subset_closedBall
      _ ≤ M * ENNReal.ofReal (ρ ^ lam) := hg ρ hρ le_rfl
      _ ≤ _ := by
          gcongr
          rw [Real.rpow_zero, sub_zero, one_div]
          exact le_mul_of_one_le_left (by positivity)
            (one_le_inv₀ (by linarith) |>.2 (by linarith))
  -- The annuli `ρ / 2^(k+1) < dist x y ≤ ρ / 2^k` cover the ball off the zero-distance set.
  set T : ℕ → Set X := fun k => (fun x => dist x y) ⁻¹' Ioc (ρ / 2 ^ (k + 1)) (ρ / 2 ^ k)
  set Z : Set X := {x | dist x y = 0}
  have hcover : ball y ρ ⊆ Z ∪ ⋃ k, T k := by
    intro x hx
    rcases (dist_nonneg (x := x) (y := y)).eq_or_lt with h | h
    · exact Or.inl h.symm
    · obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div h).2 (mem_ball.1 hx).le) one_lt_two
      refine Or.inr (mem_iUnion.2 ⟨k, ?_, ?_⟩)
      · rw [div_lt_iff₀ (by positivity)]
        have := (div_lt_iff₀ h).1 hk'
        linarith
      · rw [le_div_iff₀ (by positivity)]
        have := (le_div_iff₀ h).1 hk
        linarith
  -- On the zero-distance set the kernel vanishes.
  have hZ : ∫⁻ x in Z, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ = 0 := by
    refine le_antisymm ((setLIntegral_mono' ?_ fun x hx => ?_).trans_eq (lintegral_zero))
      bot_le
    · exact (isClosed_eq (continuous_id.dist continuous_const) continuous_const).measurableSet
    · simp [show dist x y = 0 from hx, Real.zero_rpow (neg_ne_zero.2 hs.ne')]
  have hT (k : ℕ) := setLIntegral_annulus_ofReal_dist_rpow_neg_mul_le (μ := μ) hg hs.le hρ k
  calc ∫⁻ x in ball y ρ, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ
      ≤ ∫⁻ x in Z ∪ ⋃ k, T k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ x in Z, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ +
          ∫⁻ x in ⋃ k, T k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ := lintegral_union_le _ _ _
    _ ≤ 0 + ∑' k, ∫⁻ x in T k, ENNReal.ofReal (dist x y ^ (-s)) * g x ∂μ :=
        add_le_add hZ.le (lintegral_iUnion_le _ _)
    _ ≤ 0 + ∑' k, M * ENNReal.ofReal (2 ^ s * ρ ^ (lam - s) * q ^ k) := by gcongr with k; exact hT k
    _ = M * ENNReal.ofReal (2 ^ s / (1 - q) * ρ ^ (lam - s)) := by
        rw [zero_add, ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
          (fun _ => by positivity) ((summable_geometric_of_lt_one hq0 hq1).mul_left _),
          tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        congr 2
        ring

end Weighted

omit [MeasurableSpace X] in
/-- **Dyadic annuli.** Off the ball `B(c, 2 r)`, the power `dist z c ^ (-s)`, `s ≥ 0`, is
dominated by the sum over `k` of `(2^(k+1) r) ^ (-s)` times the indicator of `B(c, 2^(k+2) r)`. -/
theorem ofReal_dist_rpow_neg_le_tsum {c z : X} {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hz : 2 * r ≤ dist z c) :
    ENNReal.ofReal (dist z c ^ (-s)) ≤ ∑' k : ℕ,
      (ball c (2 ^ (k + 2) * r)).indicator
        (fun _ => ENNReal.ofReal ((2 ^ (k + 1) * r) ^ (-s))) z := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := dist z c / (2 * r))
    ((one_le_div (by positivity)).2 hz) one_lt_two
  rw [le_div_iff₀ (by positivity)] at hk1
  rw [div_lt_iff₀ (by positivity)] at hk2
  have hmem : z ∈ ball c (2 ^ (k + 2) * r) := mem_ball.2 (hk2.trans_eq (by ring))
  refine le_trans ?_ (le_tsum _ k)
  rw [indicator_of_mem hmem]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity)
    ((le_of_eq (by ring)).trans hk1) (by linarith))

end TauCeti

namespace MeasureTheory.Measure

open Metric

/-- **The tail of a negative power of the norm.** For an additive Haar measure `μ` on a
finite-dimensional real normed space of dimension `n`, `n < s` and `R > 0`,

`∫_{‖x‖ > R} ‖x‖ ^ (-s) dx ≤ μ (B(0, 1)) 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`. -/
theorem setLIntegral_ofReal_norm_rpow_neg_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : ℝ} (hs : Module.finrank ℝ E < s) {R : ℝ}
    (hR : 0 < R) :
    ∫⁻ x in {x | R < ‖x‖}, ENNReal.ofReal (‖x‖ ^ (-s)) ∂μ ≤
      μ (ball 0 1) * ENNReal.ofReal (2 ^ (Module.finrank ℝ E : ℝ) /
        (1 - 2 ^ (Module.finrank ℝ E - s)) * R ^ (Module.finrank ℝ E - s)) := by
  simpa using TauCeti.setLIntegral_ofReal_dist_rpow_neg_le (y := 0) (μ := μ) (A := μ (ball 0 1))
    (fun r hr ↦ by rw [Measure.addHaar_ball_of_pos μ 0 (hR.trans hr), mul_comm, Real.rpow_natCast])
    hs hR

end MeasureTheory.Measure
