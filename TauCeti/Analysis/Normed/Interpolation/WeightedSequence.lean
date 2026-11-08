/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Count
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Real interpolation of weighted sequence spaces

For a normed space `A`, a real weight `s` and `1 ≤ q ≤ ∞`, the weighted sequence space `ℓ^q_s(A)`
consists of the sequences `a : ℕ → A` for which `(2 ^ (s j) a j)_j` lies in `ℓ^q(A)`, normed by
`‖(2 ^ (s j) ‖a j‖)_j‖_{ℓ^q}`. Through `b ↦ (2 ^ (-s j) b j)_j` it is a copy of `ℓ^q(A)` inside the
space `ℕ → A` of all sequences. Two such spaces form the compatible couple
`TauCeti.CompatibleCouple.weightedLp 𝕜 A q₀ q₁ s₀ s₁`, with ambient space `ℕ → A`.

The main result is the **interpolation formula for weighted sequence spaces**: for distinct
weights `s₀ ≠ s₁`, `0 < θ < 1` and any `1 ≤ q₀, q₁, q ≤ ∞`,

`(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))_{θ,q} = ℓ^q_{s_θ}(A)`, where `s_θ = (1 - θ) s₀ + θ s₁`,

with equivalent norms. The exponents `q₀`, `q₁` of the couple do not matter, only the weights do.
Weighted sequence spaces are the discrete model of Besov spaces: the dyadic Littlewood–Paley
blocks `(Δⱼ u)_j` of a distribution `u` form a sequence, with values in `L^p`, whose weighted
`ℓ^q` norm is the Besov norm of `u`. This formula is the sequence-space step in identifying real
interpolation spaces of Bessel potential spaces with Besov spaces.

## Main results

* `CompatibleCouple.ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp`: the lower bound
  `c ‖(2 ^ (s_θ j) a j)_j‖_{ℓ^q} ≤ ‖a‖_{θ,q}` for every element `a` of the sum space.
* `CompatibleCouple.kMethodENorm_weightedLp_le`: the upper bound
  `‖a‖_{θ,q} ≤ C ‖(2 ^ (s_θ j) a j)_j‖_{ℓ^q}`.
* `CompatibleCouple.mem_range_sumSpaceEmbed_weightedLp`: every sequence with finite weighted
  `ℓ^q` norm lies in the sum space.
* `CompatibleCouple.mem_kMethod_weightedLp_iff`: membership in the real interpolation space is
  membership of the weighted sequence in `ℓ^q`.
* `CompatibleCouple.weightedLpKMethodEquiv`: the resulting isomorphism of the real interpolation
  space with `ℓ^q(A)`, sending `a` to `(2 ^ (s_θ j) a j)_j`.

## Implementation notes

Both bounds compare `t ^ (-θ) K(t, a)` with the functions `φ(t 2 ^ ((s₁ - s₀) j))`, where
`φ(r) = r ^ (-θ) min 1 r` is the function whose `L^q(dt / t)` norm is `kMethodConst θ q`. Splitting
each coordinate of `a` into the cheaper of the two endpoint spaces gives
`t ^ (-θ) K(t, a) ≤ ∑ j, 2 ^ (s_θ j) ‖a j‖ φ(t 2 ^ ((s₁ - s₀) j))`, and evaluating `K` on a single
coordinate gives the reverse inequality termwise. Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) turns the first bound into the upper estimate. The second,
integrated over the disjoint intervals on which `φ(t 2 ^ ((s₁ - s₀) j))` is comparable to `1`
(`TauCeti.ofReal_rpow_mul_eLpNorm_count_le_eLpNorm_multHaar`), gives the lower estimate. Sequence
norms are written as `L^q` seminorms for the counting measure; `lp.eLpNorm_count` identifies them
with the norm of `lp`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.6 (Theorem 5.6.1).
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace CompatibleCouple

variable (𝕜 A : Type*) [RCLike 𝕜] [NormedAddCommGroup A] [NormedSpace 𝕜 A]

private theorem weight_ne_zero {𝕜 : Type*} [RCLike 𝕜] (x : ℝ) : (((2 : ℝ) ^ x : ℝ) : 𝕜) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (by positivity)

/-- The compatible couple `(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))` of weighted sequence spaces. Both
endpoints are `ℓ^q(A)`, embedded into the space `ℕ → A` of all sequences by
`b ↦ (2 ^ (-s j) b j)_j`, so that the norm of a sequence `a` in the `i`-th endpoint is
`‖(2 ^ (sᵢ j) a j)_j‖_{ℓ^{qᵢ}}`. -/
def weightedLp (q₀ q₁ : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (s₀ s₁ : ℝ) :
    CompatibleCouple 𝕜 (lp (fun _ : ℕ ↦ A) q₀) (lp (fun _ : ℕ ↦ A) q₁) (ℕ → A) where
  embed₀ := ContinuousLinearMap.pi fun j ↦
    (((2 : ℝ) ^ (s₀ * j) : ℝ) : 𝕜)⁻¹ • lp.evalCLM 𝕜 (fun _ : ℕ ↦ A) q₀ j
  embed₁ := ContinuousLinearMap.pi fun j ↦
    (((2 : ℝ) ^ (s₁ * j) : ℝ) : 𝕜)⁻¹ • lp.evalCLM 𝕜 (fun _ : ℕ ↦ A) q₁ j
  embed₀_injective b b' h := lp.ext <| funext fun j ↦ by
    have hj := congr_fun h j
    simp only [ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply,
      lp.evalCLM_apply] at hj
    exact smul_right_injective A (inv_ne_zero (weight_ne_zero _)) hj
  embed₁_injective b b' h := lp.ext <| funext fun j ↦ by
    have hj := congr_fun h j
    simp only [ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply,
      lp.evalCLM_apply] at hj
    exact smul_right_injective A (inv_ne_zero (weight_ne_zero _)) hj

variable {𝕜 A} {q₀ q₁ : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {s₀ s₁ s θ : ℝ} {q : ℝ≥0∞}

@[simp]
theorem weightedLp_embed₀_apply (b : lp (fun _ : ℕ ↦ A) q₀) (j : ℕ) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).embed₀ b j = (((2 : ℝ) ^ (s₀ * j) : ℝ) : 𝕜)⁻¹ • b j :=
  (rfl)

@[simp]
theorem weightedLp_embed₁_apply (b : lp (fun _ : ℕ ↦ A) q₁) (j : ℕ) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).embed₁ b j = (((2 : ℝ) ^ (s₁ * j) : ℝ) : 𝕜)⁻¹ • b j :=
  (rfl)

/-! ### Pointwise bounds for the `K`-functional -/

/-- The function `φ(r) = r ^ (-θ) min 1 r`, whose `L^q(dt / t)` norm is `kMethodConst θ q`. -/
private def phi (θ r : ℝ) : ℝ := r ^ (-θ) * min 1 r

private theorem phi_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ phi θ r :=
  mul_nonneg (Real.rpow_nonneg hr _) (le_min zero_le_one hr)

private theorem measurable_phi : Measurable (phi θ) :=
  (measurable_id.pow_const _).mul (measurable_const.min measurable_id)

/-- `φ` changes by at most the factor `R ^ θ` on an interval `[x, x R]`. -/
private theorem rpow_neg_mul_phi_le (hθ : 0 ≤ θ) {x r R : ℝ} (hx : 0 < x) (hxr : x ≤ r)
    (hrR : r ≤ x * R) : R ^ (-θ) * phi θ x ≤ phi θ r := by
  have hR : 0 < R := pos_of_mul_pos_right (hx.trans_le (hxr.trans hrR)) hx.le
  rw [phi, phi, ← mul_assoc, ← Real.mul_rpow hR.le hx.le, mul_comm R]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (hx.trans_le hxr) hrR (neg_nonpos.2 hθ))
    (min_le_min_left 1 hxr) (le_min zero_le_one hx.le) (Real.rpow_nonneg (hx.trans_le hxr).le _)

/-- The cost `min (2 ^ (s₀ j)) (t 2 ^ (s₁ j))` of the cheaper endpoint, in terms of `φ`. -/
private theorem min_rpow_eq (hs : s = (1 - θ) * s₀ + θ * s₁) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    min ((2 : ℝ) ^ (s₀ * j)) (t * 2 ^ (s₁ * j)) =
      t ^ θ * ((2 : ℝ) ^ (s * j) * phi θ (t * 2 ^ ((s₁ - s₀) * j))) := by
  set x : ℝ := 2 ^ (s₀ * j)
  set ρ : ℝ := 2 ^ ((s₁ - s₀) * j)
  have hx : 0 < x := by positivity
  have hρ : 0 < ρ := by positivity
  have h₁ : (2 : ℝ) ^ (s₁ * j) = x * ρ := by
    rw [← Real.rpow_add two_pos]
    ring_nf
  have h : (2 : ℝ) ^ (s * j) = x * ρ ^ θ := by
    rw [← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos, hs]
    ring_nf
  have htρ : t ^ θ * ρ ^ θ * (t * ρ) ^ (-θ) = 1 := by
    rw [← Real.mul_rpow ht.le hρ.le, Real.rpow_neg (by positivity),
      mul_inv_cancel₀ (by positivity)]
  have hmin : min x (x * (t * ρ)) = x * min 1 (t * ρ) := by
    rw [mul_min_of_nonneg _ _ hx.le, mul_one]
  rw [h₁, h, phi, ← mul_assoc t, mul_comm t x, mul_assoc x, hmin]
  linear_combination (-(x * min 1 (t * ρ))) * htρ

/-- **Termwise lower bound.** Restricting a decomposition to the `j`-th coordinate bounds
`2 ^ (s j) ‖a j‖ φ(t 2 ^ ((s₁ - s₀) j))` by `t ^ (-θ) K(t, a)`. -/
private theorem mul_phi_le_kFunctional (hs : s = (1 - θ) * s₀ + θ * s₁) {t : ℝ} (ht : 0 < t)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace) (j : ℕ) :
    (2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ *
        phi θ (t * 2 ^ ((s₁ - s₀) * j)) ≤
      t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u := by
  obtain ⟨m, hm_def⟩ : ∃ m, m = min ((2 : ℝ) ^ (s₀ * j)) (t * 2 ^ (s₁ * j)) := ⟨_, rfl⟩
  have hm : t ^ (-θ) * m = (2 : ℝ) ^ (s * j) * phi θ (t * 2 ^ ((s₁ - s₀) * j)) := by
    rw [hm_def, min_rpow_eq hs ht, ← mul_assoc, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero,
      one_mul]
  rw [mul_right_comm, ← hm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
  refine (CompatibleCouple.le_kFunctional_iff ht.le).2 fun x₀ x₁ hx ↦ ?_
  have ha : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j =
      (((2 : ℝ) ^ (s₀ * j) : ℝ) : 𝕜)⁻¹ • x₀ j + (((2 : ℝ) ^ (s₁ * j) : ℝ) : 𝕜)⁻¹ • x₁ j := by
    rw [← hx, map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum]
    simp
  have hw₀ : (0 : ℝ) < 2 ^ (s₀ * j) := by positivity
  have hw₁ : (0 : ℝ) < 2 ^ (s₁ * j) := by positivity
  have hm0 : 0 ≤ m := hm_def ▸ le_min hw₀.le (by positivity)
  have hq₀ : q₀ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq₁ : q₁ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  calc m * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖
      ≤ m * ((2 ^ (s₀ * j))⁻¹ * ‖x₀ j‖ + (2 ^ (s₁ * j))⁻¹ * ‖x₁ j‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hm0
        rw [ha, ← RCLike.ofReal_inv, ← RCLike.ofReal_inv]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, RCLike.norm_ofReal, norm_smul, RCLike.norm_ofReal,
          abs_of_pos (inv_pos.2 hw₀), abs_of_pos (inv_pos.2 hw₁)]
    _ = m / 2 ^ (s₀ * j) * ‖x₀ j‖ + m / (t * 2 ^ (s₁ * j)) * t * ‖x₁ j‖ := by
        field_simp
    _ ≤ 1 * ‖x₀‖ + 1 * t * ‖x₁‖ := by
        gcongr
        · exact (div_le_one hw₀).2 (hm_def ▸ min_le_left _ _)
        · exact lp.norm_apply_le_norm hq₀ x₀ j
        · exact (div_le_one (by positivity)).2 (hm_def ▸ min_le_right _ _)
        · exact lp.norm_apply_le_norm hq₁ x₁ j
    _ = ‖x₀‖ + t * ‖x₁‖ := by ring

/-- **Splitting into the cheaper endpoint.** Putting each coordinate of `a` into the endpoint
with the smaller weight `min (2 ^ (s₀ j)) (t 2 ^ (s₁ j))` gives a decomposition of `a` whose cost
`‖x₀‖ + t ‖x₁‖` is at most `t ^ θ ∑ j, 2 ^ (s j) ‖a j‖ φ(t 2 ^ ((s₁ - s₀) j))`, provided the
weighted coordinates are bounded and the `φ`-sum converges. -/
private theorem exists_decomposition (hs : s = (1 - θ) * s₀ + θ * s₁) {t : ℝ} (ht : 0 < t)
    (a : ℕ → A) {B : ℝ} (hB : ∀ j : ℕ, (2 : ℝ) ^ (s * j) * ‖a j‖ ≤ B)
    (hφ : Summable fun j : ℕ ↦ phi θ (t * 2 ^ ((s₁ - s₀) * j))) :
    ∃ (x₀ : lp (fun _ : ℕ ↦ A) q₀) (x₁ : lp (fun _ : ℕ ↦ A) q₁),
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).embed₀ x₀ + (weightedLp 𝕜 A q₀ q₁ s₀ s₁).embed₁ x₁ = a ∧
      ‖x₀‖ + t * ‖x₁‖ ≤
        t ^ θ * ∑' j : ℕ, (2 : ℝ) ^ (s * j) * ‖a j‖ * phi θ (t * 2 ^ ((s₁ - s₀) * j)) := by
  classical
  -- the cost of the `j`-th coordinate
  set c : ℕ → ℝ := fun j ↦ min ((2 : ℝ) ^ (s₀ * j)) (t * 2 ^ (s₁ * j)) * ‖a j‖ with hc_def
  have hc (j : ℕ) :
      c j = t ^ θ * ((2 : ℝ) ^ (s * j) * ‖a j‖ * phi θ (t * 2 ^ ((s₁ - s₀) * j))) := by
    simp only [hc_def]
    rw [min_rpow_eq hs ht]
    ring
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  -- the costs are dominated by the convergent series `t ^ θ B ∑ j, φ(t 2 ^ ((s₁ - s₀) j))`
  have hsum : Summable c := by
    refine Summable.of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_) ((hφ.mul_left B).mul_left (t ^ θ))
    · exact mul_nonneg (le_min (by positivity) (by positivity)) (norm_nonneg _)
    · rw [hc]
      gcongr
      · exact phi_nonneg (by positivity)
      · exact hB j
  -- the two pieces, with `a j` placed in the endpoint of smaller weight
  set f₀ : ℕ → A := fun j ↦
    if (2 : ℝ) ^ (s₀ * j) ≤ t * 2 ^ (s₁ * j) then (((2 : ℝ) ^ (s₀ * j) : ℝ) : 𝕜) • a j else 0
  set f₁ : ℕ → A := fun j ↦
    if (2 : ℝ) ^ (s₀ * j) ≤ t * 2 ^ (s₁ * j) then 0 else (((2 : ℝ) ^ (s₁ * j) : ℝ) : 𝕜) • a j
  have hcost (j : ℕ) : ‖f₀ j‖ + t * ‖f₁ j‖ = c j := by
    simp only [f₀, f₁, hc_def]
    split_ifs with h
    · rw [norm_zero, mul_zero, add_zero, min_eq_left h, norm_smul, RCLike.norm_ofReal,
        abs_of_pos (by positivity)]
    · rw [norm_zero, zero_add, min_eq_right (not_le.1 h).le, norm_smul, RCLike.norm_ofReal,
        abs_of_pos (by positivity), mul_assoc]
  -- both pieces are summable, hence lie in every `ℓ^q` with `1 ≤ q`
  have hf₀ : Summable fun j ↦ ‖f₀ j‖ :=
    hsum.of_nonneg_of_le (fun j ↦ norm_nonneg _) fun j ↦ by
      rw [← hcost]
      exact le_add_of_nonneg_right (by positivity)
  have hf₁ : Summable fun j ↦ ‖f₁ j‖ :=
    (hsum.div_const t).of_nonneg_of_le (fun j ↦ norm_nonneg _) fun j ↦ by
      rw [← hcost, le_div_iff₀ ht]
      linarith [norm_nonneg (f₀ j)]
  have hmem {q' : ℝ≥0∞} [Fact (1 ≤ q')] {f : ℕ → A} (hf : Summable fun j ↦ ‖f j‖) :
      Memℓp f q' :=
    (memℓp_gen (p := 1) (by simpa using hf)).of_exponent_ge Fact.out
  refine ⟨⟨f₀, hmem hf₀⟩, ⟨f₁, hmem hf₁⟩, funext fun j ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, weightedLp_embed₀_apply, weightedLp_embed₁_apply, f₀, f₁]
    split_ifs <;> simp [inv_smul_smul₀ (weight_ne_zero (𝕜 := 𝕜) _)]
  · calc ‖(⟨f₀, hmem hf₀⟩ : lp (fun _ : ℕ ↦ A) q₀)‖ + t * ‖(⟨f₁, hmem hf₁⟩ : lp _ q₁)‖
        ≤ ∑' j, ‖f₀ j‖ + t * ∑' j, ‖f₁ j‖ := by
          gcongr
          · exact lp.norm_le_tsum_norm _ hf₀
          · exact lp.norm_le_tsum_norm _ hf₁
      _ = ∑' j, c j := by
          rw [← tsum_mul_left, ← hf₀.tsum_add (hf₁.mul_left t)]
          exact tsum_congr hcost
      _ = _ := by
          rw [← tsum_mul_left]
          exact tsum_congr hc

/-! ### The row and column integrals of the kernel `φ(t 2 ^ ((s₁ - s₀) j))` -/

private theorem lintegral_ofReal_phi :
    ∫⁻ r, ENNReal.ofReal (phi θ r) ∂multHaar = kMethodConst θ 1 := by
  -- `kMethodConst θ 1` is the `L¹(dt / t)` norm of `φ`, written as a lambda
  have hφ : (fun t : ℝ ↦ t ^ (-θ) * min 1 t) = phi θ := rfl
  rw [kMethodConst_def, hφ, eLpNorm_one_eq_lintegral_enorm measurable_phi.aestronglyMeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with r hr
  exact (Real.enorm_of_nonneg (phi_nonneg hr.le)).symm

/-- Each column integral of the kernel is `kMethodConst θ 1`, by dilation invariance. -/
private theorem lintegral_ofReal_phi_mul (ρ : ℝ) (hρ : 0 < ρ) :
    ∫⁻ t, ENNReal.ofReal (phi θ (t * ρ)) ∂multHaar = kMethodConst θ 1 := by
  have hmp : MeasurePreserving (ρ * ·) multHaar multHaar :=
    ⟨measurable_const_mul ρ, map_multHaar_mul_left hρ⟩
  simp_rw [mul_comm (_ : ℝ) ρ]
  rw [hmp.lintegral_comp measurable_phi.ennreal_ofReal, lintegral_ofReal_phi]

/-- The row sums of the kernel are bounded:
`|μ| log 2 ∑ j, φ(t 2 ^ (μ j)) ≤ 2 ^ (θ |μ|) c_{θ,1}`. -/
private theorem ofReal_mul_tsum_ofReal_phi_le (hθ : 0 ≤ θ) {μ : ℝ} {t : ℝ}
    (ht : 0 < t) :
    ENNReal.ofReal (|μ| * Real.log 2) * ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j))) ≤
      ENNReal.ofReal (2 ^ (θ * |μ|)) * kMethodConst θ 1 := by
  have hR : (2 : ℝ) ^ (θ * |μ|) * 2 ^ (-(θ * |μ|)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  calc ENNReal.ofReal (|μ| * Real.log 2) * ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j)))
      = ENNReal.ofReal (2 ^ (θ * |μ|)) * (ENNReal.ofReal (|μ| * Real.log 2) *
          ∑' j : ℕ, ENNReal.ofReal (2 ^ (-(θ * |μ|)) * phi θ (t * 2 ^ (μ * j)))) := by
        have hsum : ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j))) =
            ENNReal.ofReal (2 ^ (θ * |μ|)) *
              ∑' j : ℕ, ENNReal.ofReal (2 ^ (-(θ * |μ|)) * phi θ (t * 2 ^ (μ * j))) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun j ↦ ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, hR, one_mul]
        rw [hsum, mul_left_comm]
    _ ≤ ENNReal.ofReal (2 ^ (θ * |μ|)) * kMethodConst θ 1 := by
        gcongr
        rw [← lintegral_ofReal_phi]
        refine ofReal_mul_tsum_le_lintegral_multHaar one_le_two ht fun j r hr ↦
          ENNReal.ofReal_le_ofReal ?_
        have h2 : (2 : ℝ) ^ (-(θ * |μ|)) = (2 ^ |μ|) ^ (-θ) := by
          rw [← Real.rpow_mul two_pos.le]
          ring_nf
        rw [h2]
        refine rpow_neg_mul_phi_le hθ (by positivity) hr.1 (hr.2.le.trans_eq ?_)
        rw [Real.rpow_add two_pos, mul_assoc]

/-- The row sums of the kernel: `∑ j, φ(t 2 ^ (μ j)) ≤ 2 ^ (θ |μ|) / (|μ| log 2) c_{θ,1}`. -/
private theorem tsum_ofReal_phi_le (hθ : 0 ≤ θ) {μ : ℝ} (hμ : μ ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j))) ≤
      ENNReal.ofReal (2 ^ (θ * |μ|) / (|μ| * Real.log 2)) * kMethodConst θ 1 := by
  have hL : 0 < |μ| * Real.log 2 := mul_pos (abs_pos.2 hμ) (Real.log_pos one_lt_two)
  have hL0 : ENNReal.ofReal (|μ| * Real.log 2) ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
  calc ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j)))
      = (ENNReal.ofReal (|μ| * Real.log 2))⁻¹ * (ENNReal.ofReal (|μ| * Real.log 2) *
          ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j)))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (|μ| * Real.log 2))⁻¹ * (ENNReal.ofReal (2 ^ (θ * |μ|)) *
          kMethodConst θ 1) := by
        exact mul_le_mul_of_nonneg_left (ofReal_mul_tsum_ofReal_phi_le hθ ht) (by positivity)
    _ = ENNReal.ofReal (2 ^ (θ * |μ|) / (|μ| * Real.log 2)) * kMethodConst θ 1 := by
        rw [ENNReal.ofReal_div_of_pos hL, div_eq_mul_inv]
        ring

private theorem summable_phi (hθ : θ ∈ Ioo 0 1) {μ : ℝ} (hμ : μ ≠ 0) {t : ℝ} (ht : 0 < t) :
    Summable fun j : ℕ ↦ phi θ (t * 2 ^ (μ * j)) := by
  have hfin : ∑' j : ℕ, ENNReal.ofReal (phi θ (t * 2 ^ (μ * j))) ≠ ∞ :=
    ((tsum_ofReal_phi_le hθ.1.le hμ ht).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (kMethodConst_lt_top hθ 1))).ne
  exact (ENNReal.summable_toReal hfin).congr fun j ↦ ENNReal.toReal_ofReal
    (phi_nonneg (by positivity))

private theorem norm_weight_smul (s : ℝ) (j : ℕ) (v : A) :
    ‖(((2 : ℝ) ^ (s * j) : ℝ) : 𝕜) • v‖ = (2 : ℝ) ^ (s * j) * ‖v‖ := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity)]

/-- Finiteness of the weighted `ℓ^q` norm bounds the weighted coordinates. -/
private theorem rpow_mul_norm_le_toReal (hq : q ≠ 0) {a : ℕ → A}
    (ha : eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (s * j) : ℝ) : 𝕜) • a j) q Measure.count < ∞)
    (j : ℕ) :
    (2 : ℝ) ^ (s * j) * ‖a j‖ ≤
      (eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (s * j) : ℝ) : 𝕜) • a j) q Measure.count).toReal := by
  rw [← norm_weight_smul (𝕜 := 𝕜), ← toReal_enorm]
  exact ENNReal.toReal_mono ha.ne
    (enorm_le_eLpNorm_count (fun j : ℕ ↦ (((2 : ℝ) ^ (s * j) : ℝ) : 𝕜) • a j) j hq)

/-- On the interval `[2 ^ (-μ j), 2 ^ (-μ j + |μ|))`, with `μ = s₁ - s₀`, the function
`t ↦ φ(t 2 ^ (μ j))` is at least `2 ^ (-θ |μ|)`, so `t ^ (-θ) K(t, a)` dominates
`2 ^ (-θ |μ|) 2 ^ (s j) ‖a j‖`. -/
private theorem rpow_mul_le_rpow_neg_mul_kFunctional (hs : s = (1 - θ) * s₀ + θ * s₁)
    (hθ : 0 ≤ θ) (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ico (1 * 2 ^ (-(s₁ - s₀) * j)) (1 * 2 ^ (-(s₁ - s₀) * j + |-(s₁ - s₀)|))) :
    (2 : ℝ) ^ (-(θ * |s₁ - s₀|)) *
        ((2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖) ≤
      t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u := by
  set μ := s₁ - s₀
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  set x := t * 2 ^ (μ * j)
  have hx1 : 1 ≤ x := by
    have := mul_le_mul_of_nonneg_right ht.1 (by positivity : (0 : ℝ) ≤ 2 ^ (μ * j))
    rwa [one_mul, ← Real.rpow_add two_pos, neg_mul, neg_add_cancel, Real.rpow_zero] at this
  have hxR : x ≤ 1 * 2 ^ |μ| := by
    have := mul_le_mul_of_nonneg_right ht.2.le (by positivity : (0 : ℝ) ≤ 2 ^ (μ * j))
    rwa [one_mul, ← Real.rpow_add two_pos, abs_neg, neg_mul, neg_add_cancel_comm, ← one_mul
      ((2 : ℝ) ^ |μ|)] at this
  have hphi : (2 : ℝ) ^ (-(θ * |μ|)) ≤ phi θ x := by
    have h := rpow_neg_mul_phi_le (R := 2 ^ |μ|) hθ one_pos hx1 hxR
    rw [show phi θ 1 = 1 by simp [phi], mul_one, ← Real.rpow_mul two_pos.le] at h
    exact (le_of_eq (by ring_nf)).trans h
  calc (2 : ℝ) ^ (-(θ * |μ|)) * ((2 : ℝ) ^ (s * j) *
        ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖)
      ≤ (2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ * phi θ x := by
        rw [mul_comm]
        gcongr
    _ ≤ t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u :=
        mul_phi_le_kFunctional hs ht0 u j

/-- **The pointwise upper bound.** If the weighted coordinates `2 ^ (s j) ‖a j‖` are bounded,
then `t ^ (-θ) K(t, a) ≤ ∑ j, 2 ^ (s j) ‖a j‖ φ(t 2 ^ ((s₁ - s₀) j))`, a convergent series. -/
private theorem rpow_neg_mul_kFunctional_le_tsum (hs : s = (1 - θ) * s₀ + θ * s₁)
    (hs₀₁ : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace) {B : ℝ}
    (hB : ∀ j : ℕ, (2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ ≤ B)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ *
        phi θ (t * 2 ^ ((s₁ - s₀) * j))) ∧
      t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u ≤
        ∑' j : ℕ, (2 : ℝ) ^ (s * j) * ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ *
          phi θ (t * 2 ^ ((s₁ - s₀) * j)) := by
  have hφ := summable_phi hθ (sub_ne_zero.2 hs₀₁.symm) ht
  obtain ⟨x₀, x₁, hx, hcost⟩ :=
    exists_decomposition (𝕜 := 𝕜) (q₀ := q₀) (q₁ := q₁) hs ht _ hB hφ
  have hu : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).fstToSum x₀ +
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sndToSum x₁ = u :=
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpace_ext
      (by rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, hx])
  refine ⟨(hφ.mul_left B).of_nonneg_of_le (fun j ↦ mul_nonneg (by positivity)
    (phi_nonneg (by positivity))) fun j ↦
      mul_le_mul_of_nonneg_right (hB j) (phi_nonneg (by positivity)), ?_⟩
  calc t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u
      ≤ t ^ (-θ) * (t ^ θ * ∑' j : ℕ, (2 : ℝ) ^ (s * j) *
          ‖(weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j‖ * phi θ (t * 2 ^ ((s₁ - s₀) * j))) := by
        gcongr
        exact (kFunctional_le ht.le hu).trans hcost
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, one_mul]

/-! ### The interpolation formula -/

/-- **Lower bound of the weighted interpolation formula.** For distinct weights `s₀ ≠ s₁`, every
element `a` of the sum space of `(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))` satisfies
`c ‖(2 ^ (s_θ j) a j)_j‖_{ℓ^q} ≤ ‖a‖_{θ,q}`, where `s_θ = (1 - θ) s₀ + θ s₁` and
`c = (|s₁ - s₀| log 2) ^ (1 / q) 2 ^ (-θ |s₁ - s₀|)`. The `ℓ^q` norm is written as the `L^q`
seminorm for the counting measure (see `lp.eLpNorm_count`). -/
theorem ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp (hs : s₀ ≠ s₁) (hθ : 0 ≤ θ) (hq : q ≠ 0)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace) :
    ENNReal.ofReal ((|s₁ - s₀| * Real.log 2) ^ q.toReal⁻¹ * 2 ^ (-(θ * |s₁ - s₀|))) *
        eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
          (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j) q Measure.count ≤
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kMethodENorm θ q u := by
  set v : ℕ → A := fun j ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = 2 ^ (-(θ * |s₁ - s₀|)) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ by positivity
  -- integrate the termwise bound over the intervals `[2 ^ (-μ j), 2 ^ (-μ j + |μ|))`
  have key := ofReal_rpow_mul_eLpNorm_count_le_eLpNorm_multHaar (c := 1) (μ := -(s₁ - s₀))
    one_lt_two one_pos (neg_ne_zero.2 (sub_ne_zero.2 hs.symm)) hq
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)
    (g := fun j ↦ ‖((r : ℝ) : 𝕜) • v j‖ₑ) fun j t ht ↦ by
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      rw [← ofReal_norm, norm_smul, RCLike.norm_ofReal, abs_of_pos hr, norm_weight_smul,
        Real.enorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (kFunctional_nonneg ht0.le)),
        hr_def]
      exact ENNReal.ofReal_le_ofReal (rpow_mul_le_rpow_neg_mul_kFunctional rfl hθ u j ht)
  have hg : eLpNorm (fun j ↦ ‖((r : ℝ) : 𝕜) • v j‖ₑ) q Measure.count =
      ENNReal.ofReal r * eLpNorm v q Measure.count := by
    rw [eLpNorm_enorm (fun j ↦ ((r : ℝ) : 𝕜) • v j) .of_discrete,
      show ENNReal.ofReal r = ‖((r : ℝ) : 𝕜)‖ₑ by
        rw [← ofReal_norm, RCLike.norm_ofReal, abs_of_pos hr]]
    exact eLpNorm_const_smul _ _ _ _
  rw [abs_neg, hg] at key
  rw [kMethodENorm_def, ← hr_def, ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), mul_assoc]
  exact key

/-- **Upper bound of the weighted interpolation formula.** For distinct weights `s₀ ≠ s₁`,
`0 < θ < 1` and `1 ≤ q`, every element `a` of the sum space of
`(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))` satisfies `‖a‖_{θ,q} ≤ C ‖(2 ^ (s_θ j) a j)_j‖_{ℓ^q}`, where
`s_θ = (1 - θ) s₀ + θ s₁` and `C = (2 ^ (θ |s₁ - s₀|) / (|s₁ - s₀| log 2)) ^ (1 - 1 / q) c_{θ,1}`,
with `c_{θ,1} = kMethodConst θ 1 = (θ (1 - θ))⁻¹`. -/
theorem kMethodENorm_weightedLp_le (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kMethodENorm θ q u ≤
      ENNReal.ofReal (2 ^ (θ * |s₁ - s₀|) / (|s₁ - s₀| * Real.log 2)) ^ (1 - q.toReal⁻¹) *
        kMethodConst θ 1 *
        eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
          (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j) q Measure.count := by
  set μ := s₁ - s₀
  set v : ℕ → A := fun j ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j
  set K := kMethodConst θ 1
  set D := ENNReal.ofReal (2 ^ (θ * |μ|) / (|μ| * Real.log 2))
  have hμ : μ ≠ 0 := sub_ne_zero.2 hs.symm
  have hK0 : K ≠ 0 := kMethodConst_ne_zero θ one_ne_zero
  rcases eq_or_ne (eLpNorm v q Measure.count) ∞ with hv | hv
  · -- an infinite right-hand side
    have hL : 0 < |μ| * Real.log 2 := mul_pos (abs_pos.2 hμ) (Real.log_pos one_lt_two)
    rw [hv, ENNReal.mul_top (mul_ne_zero (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity))
      ENNReal.ofReal_ne_top).ne' hK0)]
    exact le_top
  -- Schur's test for the kernel `k t j = φ(t 2 ^ (μ j))` and the sequence `‖v j‖`
  set k : ℝ → ℕ → ℝ≥0∞ := fun t j ↦ ENNReal.ofReal (phi θ (t * 2 ^ (μ * j)))
  have hk : AEMeasurable (Function.uncurry k) (multHaar.prod Measure.count) :=
    (measurable_phi.comp (measurable_fst.mul ((measurable_from_nat
      (f := fun j : ℕ ↦ (2 : ℝ) ^ (μ * j))).comp measurable_snd))).ennreal_ofReal.aemeasurable
  have hrow : ∀ᵐ t ∂multHaar, ∫⁻ j, k t j ∂Measure.count ≤ D * K := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [lintegral_count]
    exact tsum_ofReal_phi_le hθ.1.le hμ ht
  have hcol : ∀ᵐ j ∂Measure.count, ∫⁻ t, k t j ∂multHaar ≤ K :=
    Filter.Eventually.of_forall fun j ↦ (lintegral_ofReal_phi_mul _ (by positivity)).le
  have hpt : ∀ᵐ t ∂multHaar, ‖t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u‖ₑ ≤
      ‖∫⁻ j, k t j * ‖v j‖ₑ ∂Measure.count‖ₑ := by
    filter_upwards [ae_pos_multHaar] with t ht
    obtain ⟨hsum, hle⟩ := rpow_neg_mul_kFunctional_le_tsum rfl hs hθ u
      (rpow_mul_norm_le_toReal (𝕜 := 𝕜) (zero_lt_one.trans_le hq).ne' (lt_top_iff_ne_top.2 hv)) ht
    rw [enorm_eq_self, lintegral_count, Real.enorm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]
    refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j ↦ mul_nonneg (by positivity)
      (phi_nonneg (by positivity))) hsum]
    refine tsum_congr fun j ↦ ?_
    rw [mul_comm, ENNReal.ofReal_mul (phi_nonneg (by positivity)), ← norm_weight_smul (𝕜 := 𝕜),
      ofReal_norm]
  rw [kMethodENorm_def]
  calc eLpNorm (fun t ↦ t ^ (-θ) * (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kFunctional t u) q multHaar
      ≤ eLpNorm (fun t ↦ ∫⁻ j, k t j * ‖v j‖ₑ ∂Measure.count) q multHaar :=
        eLpNorm_mono_enorm_ae (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) hpt
    _ ≤ (D * K) ^ (1 - q.toReal⁻¹) * K ^ q.toReal⁻¹ * eLpNorm (fun j ↦ ‖v j‖ₑ) q Measure.count :=
        TauCeti.eLpNorm_lintegral_mul_le hk measurable_from_nat.aemeasurable hq hrow hcol
    _ = D ^ (1 - q.toReal⁻¹) * K * eLpNorm v q Measure.count := by
        rw [eLpNorm_enorm _ .of_discrete,
          ENNReal.mul_rpow_of_nonneg _ _ (TauCeti.one_sub_toReal_inv_nonneg hq), mul_assoc (D ^ _),
          ← ENNReal.rpow_add _ _ hK0 (kMethodConst_lt_top hθ 1).ne, sub_add_cancel,
          ENNReal.rpow_one]

/-- Every sequence whose weighted sequence `(2 ^ (s_θ j) a j)_j` has finite `ℓ^q` norm lies in the
sum space of `(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))`, for distinct weights `s₀ ≠ s₁` and
`0 < θ < 1`. -/
theorem mem_range_sumSpaceEmbed_weightedLp (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : q ≠ 0)
    {a : ℕ → A}
    (ha : eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) • a j) q
      Measure.count < ∞) :
    a ∈ range (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed := by
  obtain ⟨x₀, x₁, hx, -⟩ := exists_decomposition (𝕜 := 𝕜) (q₀ := q₀) (q₁ := q₁) rfl one_pos a
    (rpow_mul_norm_le_toReal hq ha) (summable_phi hθ (sub_ne_zero.2 hs.symm) one_pos)
  exact ⟨(weightedLp 𝕜 A q₀ q₁ s₀ s₁).fstToSum x₀ + (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sndToSum x₁,
    by rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, hx]⟩

/-- **The weighted interpolation formula**, membership form: for distinct weights `s₀ ≠ s₁`,
`0 < θ < 1` and `1 ≤ q`, an element `a` of the sum space of `(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))`
lies in the real interpolation space exactly when `(2 ^ (s_θ j) a j)_j ∈ ℓ^q(A)`, where
`s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem mem_kMethod_weightedLp_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).SumSpace} :
    u ∈ (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kMethod θ q ↔
      Memℓp (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
        (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed u j) q := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hμ : 0 < |s₁ - s₀| * Real.log 2 :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 hs.symm)) (Real.log_pos one_lt_two)
  rw [memℓp_iff_eLpNorm_count_lt_top hq0, mem_kMethod_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle := ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp hs hθ.1.le hq0 u
    refine lt_top_iff_ne_top.2 fun htop ↦ ?_
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne'] at hle
    exact h.ne (top_le_iff.1 hle)
  · refine (kMethodENorm_weightedLp_le hs hθ hq u).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (TauCeti.one_sub_toReal_inv_nonneg hq)
        ENNReal.ofReal_ne_top) (kMethodConst_lt_top hθ 1)) h)

/-! ### The isomorphism with `ℓ^q` -/

section Equiv

variable [Fact (1 ≤ q)]

open KMethodSpace

/-- The weighted sequence `(2 ^ (s_θ j) a j)_j` of an element of the real interpolation space, as
an element of `ℓ^q(A)`. -/
private def toWeightedLp (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q →ₗ[𝕜] lp (fun _ : ℕ ↦ A) q where
  toFun u := ⟨fun j ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u) j,
    (mem_kMethod_weightedLp_iff hs hθ Fact.out).1 (toSumₗ_mem u)⟩
  map_add' u v := lp.ext <| funext fun j ↦ by
    rw [lp.coeFn_add, Pi.add_apply]
    simp [smul_add]
  map_smul' c u := lp.ext <| funext fun j ↦ by
    rw [lp.coeFn_smul, Pi.smul_apply]
    simp [smul_comm c]

private theorem toWeightedLp_apply (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q) (j : ℕ) :
    toWeightedLp hs hθ u j = (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u) j :=
  rfl

private theorem eLpNorm_toWeightedLp (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q) :
    eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u) j) q Measure.count =
      ‖toWeightedLp hs hθ u‖ₑ := by
  rw [← lp.eLpNorm_count]
  congr 1

private theorem toWeightedLp_bijective (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    Function.Bijective (toWeightedLp (𝕜 := 𝕜) (A := A) (q₀ := q₀) (q₁ := q₁) (q := q) hs hθ) := by
  have hq : 1 ≤ q := Fact.out
  refine ⟨fun u v h ↦ KMethodSpace.ext ((weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed_injective
    (funext fun j ↦ ?_)), fun c ↦ ?_⟩
  · have hj := congr_arg (· j) h
    simp only [toWeightedLp_apply] at hj
    exact smul_right_injective A (weight_ne_zero _) hj
  · -- the preimage of `c` is the sequence `(2 ^ (-s_θ j) c j)_j`
    set a : ℕ → A := fun j ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜)⁻¹ • c j
    have hwa : (fun j : ℕ ↦ (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) • a j) = ⇑c :=
      funext fun j ↦ smul_inv_smul₀ (weight_ne_zero _) _
    obtain ⟨u, hu⟩ := mem_range_sumSpaceEmbed_weightedLp (q₀ := q₀) (q₁ := q₁) hs hθ
      (zero_lt_one.trans_le hq).ne' (a := a) (by rw [hwa, lp.eLpNorm_count]; exact enorm_lt_top)
    have hmem : u ∈ (weightedLp 𝕜 A q₀ q₁ s₀ s₁).kMethod θ q := by
      rw [mem_kMethod_weightedLp_iff hs hθ hq, hu, hwa]
      exact lp.memℓp c
    refine ⟨KMethodSpace.mk u hmem, lp.ext (funext fun j ↦ ?_)⟩
    rw [toWeightedLp_apply, toSumₗ_mk, hu]
    exact congr_fun hwa j

private def toWeightedLpEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q ≃ₗ[𝕜] lp (fun _ : ℕ ↦ A) q :=
  LinearEquiv.ofBijective (toWeightedLp hs hθ) (toWeightedLp_bijective hs hθ)

/-- **The weighted interpolation formula.** For distinct weights `s₀ ≠ s₁` and `0 < θ < 1`, the
real interpolation space `(ℓ^{q₀}_{s₀}(A), ℓ^{q₁}_{s₁}(A))_{θ,q}` is isomorphic to `ℓ^q(A)` by
`a ↦ (2 ^ (s_θ j) a j)_j`, where `s_θ = (1 - θ) s₀ + θ s₁`; that is, it is `ℓ^q_{s_θ}(A)` with an
equivalent norm. The norm bounds of the two directions are
`ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp` and `kMethodENorm_weightedLp_le`. -/
def weightedLpKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q ≃L[𝕜] lp (fun _ : ℕ ↦ A) q :=
  (toWeightedLpEquiv hs hθ).toContinuousLinearEquivOfBounds
    ((|s₁ - s₀| * Real.log 2) ^ q.toReal⁻¹ * 2 ^ (-(θ * |s₁ - s₀|)))⁻¹
    (ENNReal.ofReal (2 ^ (θ * |s₁ - s₀|) / (|s₁ - s₀| * Real.log 2)) ^ (1 - q.toReal⁻¹) *
      kMethodConst θ 1).toReal
    (fun u ↦ by
      have hL : 0 < (|s₁ - s₀| * Real.log 2) ^ q.toReal⁻¹ * (2 : ℝ) ^ (-(θ * |s₁ - s₀|)) :=
        mul_pos (Real.rpow_pos_of_pos (mul_pos (abs_pos.2 (sub_ne_zero.2 hs.symm))
          (Real.log_pos one_lt_two)) _) (by positivity)
      have h := ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp hs hθ.1.le
        (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' (toSumₗ u)
      rw [eLpNorm_toWeightedLp hs hθ, ← KMethodSpace.ofReal_norm u, ← _root_.ofReal_norm,
        ← ENNReal.ofReal_mul hL.le,
        ENNReal.ofReal_le_ofReal_iff (norm_nonneg u)] at h
      exact (le_inv_mul_iff₀ hL).2 h)
    (fun c ↦ by
      set u := (toWeightedLpEquiv (𝕜 := 𝕜) (A := A) (q₀ := q₀) (q₁ := q₁) hs hθ).symm c
      have hc : toWeightedLp hs hθ u = c := (toWeightedLpEquiv hs hθ).apply_symm_apply c
      have hU : ENNReal.ofReal (2 ^ (θ * |s₁ - s₀|) / (|s₁ - s₀| * Real.log 2)) ^
          (1 - q.toReal⁻¹) * kMethodConst θ 1 ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
          (TauCeti.one_sub_toReal_inv_nonneg Fact.out) ENNReal.ofReal_ne_top)
          (kMethodConst_lt_top hθ 1).ne
      have h := kMethodENorm_weightedLp_le hs hθ (Fact.out : 1 ≤ q) (toSumₗ u)
      rw [eLpNorm_toWeightedLp hs hθ, hc, ← KMethodSpace.ofReal_norm u, ← _root_.ofReal_norm,
        ← ENNReal.ofReal_toReal hU,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
      exact h)

@[simp]
theorem weightedLpKMethodEquiv_apply (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (weightedLp 𝕜 A q₀ q₁ s₀ s₁).KMethodSpace θ q) (j : ℕ) :
    weightedLpKMethodEquiv hs hθ u j = (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜) •
      (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u) j :=
  (rfl)

/-- The inverse of `weightedLpKMethodEquiv` sends `c ∈ ℓ^q(A)` to the sequence
`(2 ^ (-s_θ j) c j)_j`. -/
@[simp]
theorem sumSpaceEmbed_toSumₗ_weightedLpKMethodEquiv_symm_apply (hs : s₀ ≠ s₁)
    (hθ : θ ∈ Ioo 0 1) (c : lp (fun _ : ℕ ↦ A) q) (j : ℕ) :
    (weightedLp 𝕜 A q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ ((weightedLpKMethodEquiv hs hθ).symm c))
      j = (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : 𝕜)⁻¹ • c j := by
  have h := congr_arg (· j)
    ((weightedLpKMethodEquiv (𝕜 := 𝕜) (q₀ := q₀) (q₁ := q₁) hs hθ).apply_symm_apply c)
  simp only [weightedLpKMethodEquiv_apply] at h
  rw [← h, inv_smul_smul₀ (weight_ne_zero _)]

end Equiv

end CompatibleCouple

end TauCeti
