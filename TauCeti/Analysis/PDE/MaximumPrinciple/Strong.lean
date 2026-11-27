/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Harnack
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Integral.Average.RpowVanishing
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The strong maximum principle for weak subsolutions

Let `a` be measurable and uniformly elliptic on a connected open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with
constants `0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. This file proves the **strong maximum
principle**: if `u ≤ M` almost everywhere on `Ω`, `c M ≥ 0` almost everywhere on `Ω`, and `u`
comes essentially arbitrarily close to `M` near some point of `Ω`, then `u = M` almost everywhere
on `Ω`. No regularity of the coefficients beyond measurability is assumed, so `u` has no pointwise
values and the maximum is an essential one. Two forms of the hypothesis on `M` are provided:

* near a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, the set `{u > M - ε}`
  meets `B(y, ρ)` in positive measure, that is, the essential supremum of `u` on every ball about
  `y` is `M`;
* on a compact `K ⊆ Ω`: the essential supremum of `u` on `K` is `M`. This is the form of
  Gilbarg–Trudinger, Theorem 8.19, where `K` is the closure of a ball compactly contained in `Ω`.

The sign condition `c M ≥ 0` holds in the two cases of Gilbarg–Trudinger's theorem: without a mass
term, `c = 0`, for every `M`; and for `c ≥ 0` when `M ≥ 0`. Some such condition is needed: on
`(0, π)`, `u = sin x` solves `-u'' - u = 0`, so it is a weak subsolution for `c = -1`, and it
attains its maximum `M = 1` at `π / 2` without being constant. No smallness of the drift is
needed. Supersolutions satisfy the corresponding strong minimum principle, under `c m ≤ 0`.

The input is Moser's weak Harnack inequality at a small exponent `p₀`
(`TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`), which holds for a
mass coefficient of either sign. It applies to `w = M - u` on a ball `B(y, 8√n r) ⊆ Ω` with
`βr ≤ λ` and `γr² ≤ λ`: `a(M - u, v) = -a(u, v) + ∫ c M v ≥ 0` for nonnegative `v`, so `w` is a
nonnegative weak supersolution
(`TauCeti.PDE.energyFormH1_restrictL_add_const_nonneg_of_mul_nonneg`), and

`(⨍_{B(y, 2r)} (M - u)^{p₀})^{1/p₀} ≤ C (M - u)(x)` for almost every `x ∈ B(y, r)`.

If `M - u` takes values below every `ε > 0` on subsets of `B(y, r)` of positive measure, the left
side vanishes, so `u = M` almost everywhere on `B(y, r)`. The set of points near which `u = M`
almost everywhere is therefore open, and relatively closed in `Ω`: a point of `Ω` in its closure
has a ball `B(y, r)` meeting a ball on which `u = M`, in an open set of positive measure.
Connectedness of `Ω` does the rest.

Connectedness is needed: on the union of two disjoint balls, a function equal to `0` on one and
to `-1` on the other is a weak solution which attains its maximum without being constant.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_lowerOrder`: the strong
  maximum principle for weak subsolutions, with the essential maximum attained near a point.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_of_isCompact_lowerOrder`: the
  same, with the essential maximum attained on a compact subset of `Ω`.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_lowerOrder` and
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_of_isCompact_lowerOrder`: the
  strong minimum principle for weak supersolutions.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt`,
  `ae_value_eq_of_frequently_sub_lt_of_isCompact`, `ae_value_eq_of_frequently_lt_add` and
  `ae_value_eq_of_frequently_lt_add_of_isCompact` (in the same namespace): the four principles for
  `-∂ᵢ(aⁱʲ ∂ⱼu)`, without lower-order terms and with no condition on `M`.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.19.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {M : ℝ}

/-- The local step of the strong maximum principle. If `u ≤ M` is a weak subsolution on `Ω` with
`c M ≥ 0`, `B(y, 8√n r) ⊆ Ω`, `βr ≤ λ` and `γr² ≤ λ`, and `u` exceeds `M - ε` on a subset of
`B(y, r)` of positive measure for every `ε > 0`, then `u = M` almost everywhere on `B(y, r)`. -/
private theorem UniformlyEllipticOn.ae_ball_value_eq_of_frequently_sub_lt_lowerOrder [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hcM : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x * M)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {y : EuclideanSpace ℝ ι} {r : ℝ}
    (hball : ball y (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hβ : beta * r ≤ lam) (hγ : gamma * r ^ 2 ≤ lam)
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y r), M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict (ball y r), W1p.value u x = M := by
  obtain ⟨p₀, hp₀, hp₀2, C, -, hH⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder (ι := ι) (mu := mu)
      (lam := lam) (Lam := Lam) 1
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(y, 8√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball y (8 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hUm : mu.restrict U ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  have h2U : ball y (2 * r) ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have hr2 : ball y r ⊆ ball y (2 * r) := ball_subset_ball (by linarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `w = M - u` is nonnegative on `U`.
  have hneg := W1p.value_neg_ae u
  set w := W1p.restrictL hU (-u) + W1p.const M
  have hwv : ∀ᵐ x ∂mu.restrict U, W1p.value w x = M - W1p.value u x := by
    filter_upwards [W1p.value_restrictL_add_const_ae hU (-u) M,
      ae_restrict_of_ae_restrict_of_subset hball hneg] with x h1 h3
    rw [h1, h3, Pi.neg_apply]
    ring
  have hw0 : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value w x := by
    filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hball hM] with x h1 h2
    rw [h1]
    linarith
  -- `w` is a weak supersolution on `U`, since `-u` is one and `c M ≥ 0`.
  have hsuper := energyFormH1_restrictL_add_const_nonneg_of_mul_nonneg hU (u := -u)
    (memLp_energyIntegrand_of_bounds (Omega := U) (c := 0) (gamma := 0) h.upper_nonneg
      (ha.mono_measure hUm) (hb.mono_measure hUm) aestronglyMeasurable_const
      (fun x hx => h.upper_bound (hball hx)) (fun x hx => hb_bound x (hball hx))
      (fun _ _ => by simp))
    (memLp_top_of_bound (hc.mono_measure hUm) gamma
      ((ae_restrict_mem U.isOpen.measurableSet).mono fun x hx => hc_bound x (hball hx)))
    (fun v hv => by
      rw [energyFormH1_neg_left]
      linarith [hu v hv]) (ae_restrict_of_ae_restrict_of_subset hball hcM)
  -- The weak Harnack inequality for `w`: its `L^{p₀}` average is at most `C w(x)` on `B(y, r)`.
  have hHw := hH (h.mono_set hball) (ha.mono_measure hUm) (hb.mono_measure hUm)
    (hc.mono_measure hUm) (fun x hx => hb_bound x (hball hx)) (fun x hx => hc_bound x (hball hx))
    hsuper hw0 (x₀ := y) (r := r) subset_rfl (by rwa [one_mul]) (by rwa [one_mul])
  have hwv' := ae_restrict_of_ae_restrict_of_subset (hr2.trans h2U) hwv
  have hzero := ae_eq_zero_of_frequently_lt_of_ae_setAverage_rpow_le hr2 measure_ball_lt_top.ne hp₀
    ((ENNReal.ofReal_le_ofReal hp₀2).trans_eq (ENNReal.ofReal_ofNat 2))
    ((Lp.memLp _).mono_measure (Measure.restrict_mono h2U le_rfl))
    (ae_restrict_of_ae_restrict_of_subset h2U hw0) hHw fun ε hε =>
      ((hfreq ε hε).and_eventually hwv').mono fun x ⟨h1, h2⟩ => by rw [h2]; linarith [h1]
  filter_upwards [hzero, hwv'] with x h1 h2
  linarith

omit [DecidableEq ι] in
/-- Every point `z` of `Ω` is the centre of a ball `B(z, r)` with `B(z, 8√n r) ⊆ Ω`, `βr ≤ λ` and
`γr² ≤ λ`, for `λ > 0` and `β, γ ≥ 0`. -/
private theorem exists_pos_ball_subset_and_mul_le [Nonempty ι] (hlam : 0 < lam) (hβ0 : 0 ≤ beta)
    (hγ0 : 0 ≤ gamma) {z : EuclideanSpace ℝ ι} (hz : z ∈ Omega) :
    ∃ r > 0, ball z (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) ∧
      beta * r ≤ lam ∧ gamma * r ^ 2 ≤ lam := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen z hz
  have hc : 0 < 8 * √(Fintype.card ι : ℝ) :=
    mul_pos (by norm_num) (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos))
  have hd : 0 < beta + gamma + 1 := by linarith
  set r := min (R / (8 * √(Fintype.card ι))) (min 1 (lam / (beta + gamma + 1)))
  have hr0 : 0 < r := lt_min (div_pos hR hc) (lt_min one_pos (div_pos hlam hd))
  have hrR : r ≤ R / (8 * √(Fintype.card ι)) := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrd : r * (beta + gamma + 1) ≤ lam :=
    (le_div_iff₀ hd).1 ((min_le_right _ _).trans (min_le_right _ _))
  have hγr : gamma * r * r ≤ gamma * r := mul_le_of_le_one_right (mul_nonneg hγ0 hr0.le) hr1
  refine ⟨r, hr0, (ball_subset_ball ?_).trans hRΩ, ?_, ?_⟩
  · rwa [le_div_iff₀' hc] at hrR
  · nlinarith [mul_nonneg hγ0 hr0.le]
  · nlinarith [mul_nonneg hβ0 hr0.le]

/-- **The strong maximum principle for weak subsolutions with lower-order terms.** Let `a` be
measurable and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, let `b` and
`c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `u ≤ M` and `c M ≥ 0` almost everywhere on `Ω`, and that `M` is the essential
supremum of `u` on every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every
`ε > 0`, `u > M - ε` on a subset of `B(y, ρ)` of positive measure. Then `u = M` almost everywhere
on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_lowerOrder [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M)
    (hcM : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x * M) {y : EuclideanSpace ℝ ι} (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M := by
  -- Every point of `Ω` is the centre of a ball `B(z, r)` with `B(z, 8√n r) ⊆ Ω` on which the
  -- lower-order terms are small: `βr ≤ λ` and `γr² ≤ λ`.
  have hrad : ∀ z ∈ Omega, ∃ r > 0,
      ball z (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) ∧
        beta * r ≤ lam ∧ gamma * r ^ 2 ≤ lam := fun z hz =>
    exists_pos_ball_subset_and_mul_le h.pos ((norm_nonneg _).trans (hb_bound y hy))
      ((norm_nonneg _).trans (hc_bound y hy)) hz
  have hloc := fun {z : EuclideanSpace ℝ ι} {r : ℝ} =>
    h.ae_ball_value_eq_of_frequently_sub_lt_lowerOrder ha hb hc hb_bound hc_bound hcM hu hM
      (y := z) (r := r)
  -- `S` is the set of points near which `u = M` almost everywhere.
  set S := {z | ∃ ρ > 0, ∀ᵐ x ∂mu.restrict (ball z ρ), W1p.value u x = M}
  have hSo : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨ρ, hρ, hz⟩ => ?_
    filter_upwards [ball_mem_nhds z hρ] with z' hz'
    have hsub : ball z' (ρ - dist z' z) ⊆ ball z ρ := ball_subset_ball' (by linarith)
    exact ⟨ρ - dist z' z, sub_pos.2 hz', ae_restrict_of_ae_restrict_of_subset hsub hz⟩
  -- `S` contains `y`, by the local step.
  have hyS : y ∈ S := by
    obtain ⟨r, hr, hball, hβ, hγ⟩ := hrad y hy
    have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
      Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
    exact ⟨r, hr, hloc hball hβ hγ
      (hfreq r hr ((ball_subset_ball (by nlinarith)).trans hball))⟩
  -- A point of `Ω` in the closure of `S` lies in `S`: a ball about it meets a ball on which
  -- `u = M` in an open set of positive measure, and the local step applies.
  have hcl : closure S ∩ Omega ⊆ S := by
    rintro z ⟨hzS, hzΩ⟩
    obtain ⟨r, hr, hball, hβ, hγ⟩ := hrad z hzΩ
    obtain ⟨z', ⟨ρ, hρ, hz'⟩, hzz'⟩ := Metric.mem_closure_iff.1 hzS r hr
    have hV : mu (ball z r ∩ ball z' ρ) ≠ 0 := ((isOpen_ball.inter isOpen_ball).measure_pos mu
      ⟨z', by rwa [mem_ball, dist_comm], mem_ball_self hρ⟩).ne'
    refine ⟨r, hr, hloc hball hβ hγ fun ε hε => ?_⟩
    have := ae_restrict_neBot.2 hV
    exact ((ae_restrict_of_ae_restrict_of_subset inter_subset_right hz').mono fun x hx => by
      rw [hx]; linarith).frequently.filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
  have hΩS : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ S :=
    hΩ.subset_of_closure_inter_subset hSo ⟨y, hy, hyS⟩ hcl
  -- `Ω` is covered by balls on which `u = M` almost everywhere.
  rw [ae_restrict_iff' Omega.isOpen.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun z hz => ?_
  obtain ⟨ρ, hρ, hzρ⟩ := hΩS (not_imp.1 hz).1
  rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hzρ
  refine ⟨_, inter_mem_nhdsWithin _ (ball_mem_nhds z hρ), measure_mono_null (fun x hx => ?_) hzρ⟩
  exact not_imp.2 ⟨hx.2, (not_imp.1 hx.1).2⟩

/-- **The strong maximum principle for weak subsolutions with lower-order terms, compact form.**
Let `a` be measurable and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, let
`b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. If `u ≤ M` and `c M ≥ 0` almost everywhere on
`Ω` and the essential supremum of `u` on a compact `K ⊆ Ω` is `M`, that is, `u > M - ε` on a
subset of `K` of positive measure for every `ε > 0`, then `u = M` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_of_isCompact_lowerOrder [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M)
    (hcM : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x * M) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M := by
  -- Some point of `K` has `M` as the essential supremum of `u` on every ball about it.
  by_contra hne
  have hloc : ∀ y ∈ K, ∃ ρ > 0, ∃ ε > 0, ∀ᵐ x ∂mu.restrict (ball y ρ), W1p.value u x ≤ M - ε := by
    intro y hy
    by_contra hy'
    simp only [not_exists, not_and, Filter.not_eventually, not_le] at hy'
    exact hne (h.ae_value_eq_of_frequently_sub_lt_lowerOrder ha hb hc hb_bound hc_bound hΩ hu hM
      hcM (hKΩ hy) fun ρ hρ _ ε hε => (hy' ρ hρ ε hε).mono fun x hx => by linarith)
  -- Otherwise compactness gives a single `ε` with `u ≤ M - ε` almost everywhere on `K`.
  obtain ⟨ε, hε, hK'⟩ : ∃ ε > 0, ∀ᵐ x ∂mu.restrict K, W1p.value u x ≤ M - ε := by
    refine hK.induction_on (p := fun s => ∃ ε > 0, ∀ᵐ x ∂mu.restrict s, W1p.value u x ≤ M - ε)
      ⟨1, one_pos, by simp⟩ (fun s t hst ⟨ε, hε, ht⟩ =>
        ⟨ε, hε, ae_restrict_of_ae_restrict_of_subset hst ht⟩)
      (fun s t ⟨ε, hε, hs⟩ ⟨δ, hδ, ht⟩ => ⟨min ε δ, lt_min hε hδ, ?_⟩) fun y hy => ?_
    · rw [ae_restrict_union_iff]
      exact ⟨hs.mono fun x hx => hx.trans (by gcongr; exact min_le_left _ _),
        ht.mono fun x hx => hx.trans (by gcongr; exact min_le_right _ _)⟩
    · obtain ⟨ρ, hρ, ε, hε, hyρ⟩ := hloc y hy
      exact ⟨ball y ρ, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hρ), ε, hε, hyρ⟩
  obtain ⟨x, hx1, hx2⟩ := ((hfreq ε hε).and_eventually hK').exists
  linarith

/-- **The strong minimum principle for weak supersolutions with lower-order terms.** Let `a` be
measurable and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, let `b` and
`c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution
of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `m ≤ u` and `c m ≤ 0` almost everywhere on `Ω`, and that `m` is the essential infimum
of `u` on every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`,
`u < m + ε` on a subset of `B(y, ρ)` of positive measure. Then `u = m` almost everywhere on
`Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_lowerOrder [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    (hcm : ∀ᵐ x ∂mu.restrict Omega, c x * m ≤ 0) {y : EuclideanSpace ℝ ι} (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m := by
  -- Apply the strong maximum principle to the subsolution `-u ≤ -m`.
  have hneg := W1p.value_neg_ae u
  have hmax := h.ae_value_eq_of_frequently_sub_lt_lowerOrder ha hb hc hb_bound hc_bound hΩ
    (u := -u) (M := -m) (fun v hv => by
      rw [energyFormH1_neg_left]
      linarith [hu v hv])
    (by filter_upwards [hm, hneg] with x hx hxn; rw [hxn, Pi.neg_apply]; linarith)
    (hcm.mono fun x hx => by linarith) hy
    fun ρ hρ hρΩ ε hε => ((hfreq ρ hρ hρΩ ε hε).and_eventually
      (ae_restrict_of_ae_restrict_of_subset hρΩ hneg)).mono fun x ⟨_, hxn⟩ => by
        rw [hxn, Pi.neg_apply]; linarith
  filter_upwards [hmax, hneg] with x hx hxn
  rw [hxn, Pi.neg_apply] at hx
  linarith

/-- **The strong minimum principle for weak supersolutions with lower-order terms, compact form.**
Let `a` be measurable and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, let
`b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`. If `m ≤ u` and `c m ≤ 0` almost everywhere on
`Ω` and the essential infimum of `u` on a compact `K ⊆ Ω` is `m`, that is, `u < m + ε` on a subset
of `K` of positive measure for every `ε > 0`, then `u = m` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_of_isCompact_lowerOrder [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    (hcm : ∀ᵐ x ∂mu.restrict Omega, c x * m ≤ 0) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m := by
  -- Apply the compact strong maximum principle to the subsolution `-u ≤ -m`.
  have hneg := W1p.value_neg_ae u
  have hmax := h.ae_value_eq_of_frequently_sub_lt_of_isCompact_lowerOrder ha hb hc hb_bound
    hc_bound hΩ (u := -u) (M := -m)
    (fun v hv => by
      rw [energyFormH1_neg_left]
      linarith [hu v hv])
    (by filter_upwards [hm, hneg] with x hx hxn; rw [hxn, Pi.neg_apply]; linarith)
    (hcm.mono fun x hx => by linarith) hK hKΩ
    fun ε hε => ((hfreq ε hε).and_eventually (ae_restrict_of_ae_restrict_of_subset hKΩ hneg)).mono
      fun x ⟨_, hxn⟩ => by rw [hxn, Pi.neg_apply]; linarith
  filter_upwards [hmax, hneg] with x hx hxn
  rw [hxn, Pi.neg_apply] at hx
  linarith

/-! ### Without lower-order terms -/

/-- **The strong maximum principle for weak subsolutions.** Let `a` be measurable and uniformly
elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `u ≤ M` almost everywhere on `Ω`, and that `M` is the essential supremum of `u` on
every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, `u > M - ε` on
a subset of `B(y, ρ)` of positive measure. Then `u = M` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {y : EuclideanSpace ℝ ι} (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M :=
  h.ae_value_eq_of_frequently_sub_lt_lowerOrder (b := 0) (c := 0) (beta := 0) (gamma := 0) ha
    aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) hΩ hu hM (.of_forall fun _ => by simp) hy hfreq

/-- **The strong maximum principle for weak subsolutions, compact form.** Let `a` be measurable
and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`. If `u ≤ M` almost everywhere on `Ω` and the essential
supremum of `u` on a compact `K ⊆ Ω` is `M`, that is, `u > M - ε` on a subset of `K` of positive
measure for every `ε > 0`, then `u = M` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_of_isCompact [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M :=
  h.ae_value_eq_of_frequently_sub_lt_of_isCompact_lowerOrder (b := 0) (c := 0) (beta := 0)
    (gamma := 0) ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) hΩ hu hM (.of_forall fun _ => by simp) hK hKΩ hfreq

/-- **The strong minimum principle for weak supersolutions.** Let `a` be measurable and uniformly
elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `m ≤ u` almost everywhere on `Ω`, and that `m` is the essential infimum of `u` on
every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, `u < m + ε` on
a subset of `B(y, ρ)` of positive measure. Then `u = m` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m :=
  h.ae_value_eq_of_frequently_lt_add_lowerOrder (b := 0) (c := 0) (beta := 0) (gamma := 0) ha
    aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) hΩ hu hm (.of_forall fun _ => by simp) hy hfreq

/-- **The strong minimum principle for weak supersolutions, compact form.** Let `a` be measurable
and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`. If `m ≤ u` almost everywhere on `Ω` and the essential
infimum of `u` on a compact `K ⊆ Ω` is `m`, that is, `u < m + ε` on a subset of `K` of positive
measure for every `ε > 0`, then `u = m` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_of_isCompact [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m :=
  h.ae_value_eq_of_frequently_lt_add_of_isCompact_lowerOrder (b := 0) (c := 0) (beta := 0)
    (gamma := 0) ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) hΩ hu hm (.of_forall fun _ => by simp) hK hKΩ hfreq

end PDE

end TauCeti
