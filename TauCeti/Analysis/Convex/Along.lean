/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Convexity along curves

Convexity along a curve gives a quadratic lower bound at its initial point if that
point minimizes the energy on the curve. Convex interpolation from a point of local
lower semicontinuity also gives a global lower bound. These estimates apply to
extended-real energies on pseudometric spaces without any geodesic assumptions.

The midpoint and Cauchy estimates below are used for minimizing sequences, as in
Ambrosio, Gigli and Savaré, *Gradient Flows in Metric Spaces and in the Space of
Probability Measures*, 2nd ed., Section 2.4, Lemma 4.1.1 and Theorem 4.1.2.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- If a quadratic interpolation bound stays above its initial value `a`, its
endpoint value `b` exceeds `a` by at least the interpolation coefficient `D`. -/
theorem add_le_of_le_affine_sub {a b D : ℝ}
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, a ≤ (1 - t) * a + t * b - t * (1 - t) * D) :
    a + D ≤ b := by
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1, a + (1 - t) * D ≤ b := by
    intro t ht
    exact le_of_mul_le_mul_left (by linarith [h t ht]) ht.1
  have hc : Continuous (fun t : ℝ ↦ a + (1 - t) * D) := by fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsGT zero_lt_one) hbound)

/-- Comparing a common lower bound with a midpoint interpolation bound controls its
penalty by the average endpoint gap. -/
theorem div_four_le_sub_of_le_midpoint {a b c D : ℝ}
    (h : a ≤ (1 - 1 / 2) * b + (1 / 2) * c - (1 / 2) * (1 - 1 / 2) * D) :
    D / 4 ≤ (b + c) / 2 - a := by linarith

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {φ : X → EReal} {γ : ℝ → X}

/-- A sequence is Cauchy if a distance penalty bounded away from zero off every
neighborhood of zero is controlled by average objective gaps tending to zero. -/
theorem cauchySeq_of_le_average_sub {u : ℕ → X} {g : ℕ → ℝ} {a : ℝ} {ω : ℝ → ℝ}
    (hω : ∀ ε > 0, ∃ c > 0, ∀ r ≥ ε, c ≤ ω r)
    (hgap : ∀ n k, ω (dist (u n) (u k)) / 4 ≤ (g n + g k) / 2 - a)
    (hlim : Tendsto g atTop (𝓝 a)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  obtain ⟨c, hc, hωc⟩ := hω ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (show a < a + c / 4 by linarith)))
  refine ⟨N, fun n hn k hk ↦ lt_of_not_ge fun hd ↦ ?_⟩
  linarith [hωc _ hd, hgap n k, hN n hn, hN k hk]

/-- The energy `φ` is *`m`-convex along* the curve `γ`, read on `[0, 1]`: for every `t ∈ [0, 1]`,
`φ (γ t) ≤ (1 - t) φ (γ 0) + t φ (γ 1) - (m / 2) t (1 - t) d(γ 0, γ 1)²`. -/
@[expose]
def ConvexAlong (m : ℝ) (φ : X → EReal) (γ : ℝ → X) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ (γ 0) + (t : EReal) * φ (γ 1) -
    ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal)

/-- The defining inequality of convexity along a curve. -/
theorem convexAlong_def :
    ConvexAlong m φ γ ↔ ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ (γ 0) +
      (t : EReal) * φ (γ 1) - ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal) :=
  Iff.rfl

/-- **Quadratic growth away from a minimum along a curve of convexity.** If `φ` is `m`-convex
along `γ` and its smallest value along `γ` on `[0, 1]` is attained at `γ 0`, then
`φ (γ 0) + (m / 2) d(γ 0, γ 1)² ≤ φ (γ 1)`. Comparing `φ (γ 0)` with the convexity bound at time
`t` and letting `t → 0` gives the inequality; `m` may be negative. -/
theorem ConvexAlong.apply_add_le_of_forall_le (h : ConvexAlong m φ γ)
    (hmin : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ 0) ≤ φ (γ t)) :
    φ (γ 0) + ((m / 2 * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal) ≤ φ (γ 1) := by
  have h₁ := hmin 1 (right_mem_Icc.2 zero_le_one)
  induction hb : φ (γ 1) using EReal.rec with
  | top => exact le_top
  | bot =>
    rw [hb, le_bot_iff] at h₁
    simp [h₁]
  | coe b =>
    induction ha : φ (γ 0) using EReal.rec with
    | bot => simp
    | top => simp [ha, hb] at h₁
    | coe a =>
      have hbound : a + m / 2 * dist (γ 0) (γ 1) ^ 2 ≤ b := by
        apply add_le_of_le_affine_sub
        intro t ht
        have ht' := Ioo_subset_Icc_self ht
        have h' := (hmin t ht').trans (h t ht')
        rw [ha, hb] at h'
        have hr : a ≤ (1 - t) * a + t * b - m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 := by
          exact_mod_cast h'
        convert hr using 1
        ring
      exact_mod_cast hbound

/-- The quantitative midpoint bound for a convex curve with real endpoint values.
A real lower bound at its midpoint forces a corresponding gap at the endpoints. -/
theorem ConvexAlong.mul_dist_sq_div_four_le_sub (h : ConvexAlong m φ γ)
    {a b c : ℝ} (hb : φ (γ 0) = b) (hc : φ (γ 1) = c)
    (hlow : (a : EReal) ≤ φ (γ (1 / 2))) :
    (m / 2 * dist (γ 0) (γ 1) ^ 2) / 4 ≤ (b + c) / 2 - a := by
  have hmid := hlow.trans (h (1 / 2) (by norm_num))
  rw [hb, hc] at hmid
  apply div_four_le_sub_of_le_midpoint
  have hr : a ≤ (1 - 1 / 2) * b + (1 / 2) * c -
      m / 2 * (1 / 2) * (1 - 1 / 2) * dist (γ 0) (γ 1) ^ 2 := by
    exact_mod_cast hmid
  convert hr using 1
  ring

-- Complete the square to bound the quadratic penalty minus the linear term.
private theorem quadratic_coercivity_bound {κ δ R t : ℝ}
    (hκ : 0 < κ) (hδ : 0 < δ) (ht : t ≤ 1 / 2) :
    2 * R / δ - 4 / (κ * δ ^ 2) ≤ κ / 2 * (1 - t) * R ^ 2 := by
  have hquad : κ / 4 * R ^ 2 ≤ κ / 2 * (1 - t) * R ^ 2 := by
    calc κ / 4 * R ^ 2 = 1 / 4 * (κ * R ^ 2) := by ring
      _ ≤ (1 - t) / 2 * (κ * R ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [ht]) (by positivity)
      _ = κ / 2 * (1 - t) * R ^ 2 := by ring
  have hsq : -(4 / (κ * δ ^ 2)) ≤ κ / 4 * R ^ 2 - 2 * R / δ := by
    rw [← sub_nonneg]
    calc κ / 4 * R ^ 2 - 2 * R / δ - -(4 / (κ * δ ^ 2))
        = (κ * δ * R - 4) ^ 2 / (4 * κ * δ ^ 2) := by field_simp; ring
      _ ≥ 0 := div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- **Metric coercivity from local lower semicontinuity and `κ`-convex interpolation**
(Ambrosio–Gigli–Savaré, Lemma 2.4.8). Let `Ψ : X → EReal` be lower semicontinuous and finite at a
point `x₀`, and let `κ > 0`. Suppose that every point `z` with `Ψ z ≠ ⊤` can be interpolated
towards `x₀` at some scale `R : ℝ` so that for every `t ∈ [0, 1]` there is a point `y` at distance
at most `t R` from `x₀` satisfying
`Ψ y ≤ (1 - t) Ψ x₀ + t Ψ z - (κ / 2) t (1 - t) R ^ 2`.
Then `Ψ` is bounded below by a real constant; in particular `⨅ z, Ψ z ≠ ⊥`. -/
theorem iInf_ne_bot_of_lowerSemicontinuousAt {Ψ : X → EReal} {x₀ : X} {κ : ℝ}
    (hΨ : LowerSemicontinuousAt Ψ x₀) (htop : Ψ x₀ ≠ ⊤) (hbot : Ψ x₀ ≠ ⊥) (hκ : 0 < κ)
    (hinterp : ∀ z, Ψ z ≠ ⊤ → ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y, dist x₀ y ≤ t * R ∧
      Ψ y ≤ ((1 - t : ℝ) : EReal) * Ψ x₀ + (t : EReal) * Ψ z -
        ((κ / 2 * t * (1 - t) * R ^ 2 : ℝ) : EReal)) :
    (⨅ z, Ψ z) ≠ ⊥ := by
  -- Local boundedness below near `x₀` extends to a global lower bound by choosing `t = 1` when
  -- `R < δ` and `t = δ / (2R)` when `R ≥ δ`, then completing the square against `(κ / 4) R²`.
  set a : ℝ := (Ψ x₀).toReal
  have ha : Ψ x₀ = a := (EReal.coe_toReal htop hbot).symm
  have hnhds : ∀ᶠ y in 𝓝 x₀, ((a - 1 : ℝ) : EReal) < Ψ y :=
    hΨ _ (by simp only [gt_iff_lt, ha, EReal.coe_lt_coe_iff]; exact sub_one_lt a)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.eventually_iff.1 hnhds
  set L : ℝ := min (a - 1) (a - 4 / (κ * δ ^ 2))
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_iInf fun z ↦ ?_)
  rcases eq_or_ne (Ψ z) ⊤ with hztop | hztop
  · exact hztop ▸ le_top
  obtain ⟨R, hinterp_z⟩ := hinterp z hztop
  rcases lt_or_ge R δ with hR | hR
  · obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z 1 ⟨zero_le_one, le_rfl⟩
    have hy_ball : y ∈ Metric.ball x₀ δ :=
      Metric.mem_ball'.2 (hy_dist.trans_lt (by simpa only [one_mul] using hR))
    have h1 : Ψ y ≤ Ψ z := by simpa [ha] using hy_le
    exact (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans ((hball hy_ball).le.trans h1)
  have hRpos : 0 < R := hδ.trans_le hR
  set t : ℝ := δ / (2 * R)
  have htpos : 0 < t := by positivity
  have ht12 : t ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) two_pos).2 (by linarith)
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht12.trans (by norm_num)⟩
  obtain ⟨y, hy_dist, hy_le⟩ := hinterp_z t htIcc
  have hy_ball : y ∈ Metric.ball x₀ δ := by
    rw [Metric.mem_ball']
    have htR : t * R = δ / 2 := by dsimp [t]; field_simp
    linarith
  have hlow : ((a - 1 : ℝ) : EReal) < Ψ y := hball hy_ball
  have hzbot : Ψ z ≠ ⊥ := fun hzbot ↦ by
    rw [hzbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot, EReal.bot_sub, le_bot_iff] at hy_le
    exact not_lt_bot (hy_le ▸ hlow)
  set b : ℝ := (Ψ z).toReal
  have hb : Ψ z = b := (EReal.coe_toReal hztop hzbot).symm
  rw [ha, hb] at hy_le
  norm_cast at hy_le
  have hmid : a - 1 ≤ (1 - t) * a + t * b - κ / 2 * t * (1 - t) * R ^ 2 := by
    exact_mod_cast hlow.le.trans hy_le
  have hslope : a - 2 * R / δ ≤ b - κ / 2 * (1 - t) * R ^ 2 := by
    refine le_of_mul_le_mul_left ?_ htpos
    have : t * (2 * R / δ) = 1 := by dsimp [t]; field_simp
    linarith
  have hquad := quadratic_coercivity_bound (R := R) hκ hδ ht12
  rw [hb]
  exact EReal.coe_le_coe_iff.2 ((min_le_right _ _).trans (by linarith))

end TauCeti
