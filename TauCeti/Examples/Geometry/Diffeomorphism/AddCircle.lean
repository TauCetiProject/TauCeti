/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.AddCircle
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.AddCircle
import TauCeti.Topology.MetricSpace.Pseudo.Basic

/-!
# Examples: circle diffeomorphisms converging in `C¹` but not in `C^∞`

On the circle `S¹ = ℝ / 2πℤ`, with angle `θ`, the maps

`θ ↦ θ + sin (k θ) / k²`, `k ≥ 2`,

are analytic diffeomorphisms: their derivative `1 + cos (k θ) / k` is at least `1 - 1 / k > 0`.
They tend to the identity in the `C¹` topology, since `sin (k θ) / k²` and its derivative
`cos (k θ) / k` tend to `0` uniformly (`TauCeti.tendsto_sinPerturbation_one`). They do not tend to
the identity in the `C^n` topology for any `n ≥ 2`, in particular not in `Diff(S¹)` with its `C^∞`
weak Whitney topology (`TauCeti.not_tendsto_sinPerturbation_one`): their second derivatives
`-sin (k θ)` have supremum `1`, attained at `θ = π / (2 k)`, which tends to `0`
(`TauCeti.iteratedDeriv_two_sinPerturbationLift`).

The convergence and its failure are read off the normalized lifts through
`ContMDiffMap.tendsto_addCircle_addCircle_iff_lift`. The family is indexed by `k : ℕ` through
`k + 2`, so that every member is a diffeomorphism.
-/

public section

noncomputable section

open Filter Topology Real
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney

namespace TauCeti

local instance sinPerturbationTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The lift `x ↦ x + sin ((k + 2) x) / (k + 2) ^ 2` of the `k`-th perturbation of the
identity of the circle `ℝ / 2πℤ`. -/
def sinPerturbationLift (k : ℕ) (x : ℝ) : ℝ := x + sin ((k + 2) * x) / ((k : ℝ) + 2) ^ 2

/-- The defining formula of `sinPerturbationLift`, whose body is not exposed. -/
theorem sinPerturbationLift_apply (k : ℕ) (x : ℝ) :
    sinPerturbationLift k x = x + sin ((k + 2) * x) / ((k : ℝ) + 2) ^ 2 :=
  (rfl)

theorem contDiff_sinPerturbationLift {n : ℕ∞ω} (k : ℕ) : ContDiff ℝ n (sinPerturbationLift k) :=
  contDiff_id.add ((contDiff_sin.comp (contDiff_const.mul contDiff_id)).div_const _)

@[simp]
theorem sinPerturbationLift_zero (k : ℕ) : sinPerturbationLift k 0 = 0 := by
  simp [sinPerturbationLift]

theorem sinPerturbationLift_add_two_pi (k : ℕ) (x : ℝ) :
    sinPerturbationLift k (x + 2 * π) = sinPerturbationLift k x + 2 * π := by
  have h : ((k : ℝ) + 2) * (x + 2 * π) = (k + 2) * x + ((k + 2 : ℕ) : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [sinPerturbationLift, h, sin_add_nat_mul_two_pi, sinPerturbationLift]
  ring

/-- The derivative of the lift is `1 + cos ((k + 2) x) / (k + 2)`. -/
theorem deriv_sinPerturbationLift (k : ℕ) (x : ℝ) :
    deriv (sinPerturbationLift k) x = 1 + cos ((k + 2) * x) / ((k : ℝ) + 2) := by
  have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
  have h : HasDerivAt (sinPerturbationLift k)
      (1 + cos ((k + 2) * x) * ((k + 2) * 1) / ((k : ℝ) + 2) ^ 2) x :=
    (hasDerivAt_id' x).add ((((hasDerivAt_id' x).const_mul ((k : ℝ) + 2)).sin).div_const _)
  rw [h.deriv]
  field_simp

theorem deriv_sinPerturbationLift_pos (k : ℕ) (x : ℝ) : 0 < deriv (sinPerturbationLift k) x := by
  rw [deriv_sinPerturbationLift]
  have hk : (0 : ℝ) < k + 2 := by positivity
  have : -(1 / 2 : ℝ) ≤ cos ((k + 2) * x) / ((k : ℝ) + 2) := by
    rw [le_div_iff₀ hk]
    nlinarith [neg_one_le_cos ((k + 2) * x), k.cast_nonneg (α := ℝ)]
  linarith

/-- The `k`-th perturbation `θ ↦ θ + sin ((k + 2) θ) / (k + 2) ^ 2` of the identity of the circle
`ℝ / 2πℤ`, as a `C^n` diffeomorphism, `n ≠ 0`. -/
def sinPerturbation {n : ℕ∞ω} (hn : n ≠ 0) (k : ℕ) : Diff 𝓘(ℝ) (AddCircle (2 * π)) n :=
  (AddCircle.diffeotopyOfLift (contDiff_sinPerturbationLift k) hn
    (sinPerturbationLift_add_two_pi k) (deriv_sinPerturbationLift_pos k)).final

@[simp]
theorem sinPerturbation_apply_coe {n : ℕ∞ω} (hn : n ≠ 0) (k : ℕ) (x : ℝ) :
    sinPerturbation hn k x = (sinPerturbationLift k x : AddCircle (2 * π)) :=
  AddCircle.diffeotopyOfLift_final_apply_coe _ _ _ _ x

/-- The lift minus the identity, `x ↦ sin ((k + 2) x) / (k + 2) ^ 2`, has `m`-th derivative
`(k + 2) ^ m sin⁽ᵐ⁾ ((k + 2) x) / (k + 2) ^ 2`. -/
private theorem iteratedDeriv_sinPerturbationLift_sub_id (k m : ℕ) (x : ℝ) :
    iteratedDeriv m (sinPerturbationLift k - id) x =
      ((k : ℝ) + 2) ^ m * iteratedDeriv m sin ((k + 2) * x) / ((k : ℝ) + 2) ^ 2 := by
  have h : sinPerturbationLift k - id = fun y ↦ sin ((k + 2) * y) / ((k : ℝ) + 2) ^ 2 := by
    funext y
    simp [sinPerturbationLift]
  rw [h, iteratedDeriv_div_const, iteratedDeriv_comp_const_mul contDiff_sin]

/-- **The second derivatives.** The second derivative of the `k`-th lift is `-sin ((k + 2) x)`. -/
theorem iteratedDeriv_two_sinPerturbationLift (k : ℕ) (x : ℝ) :
    iteratedDeriv 2 (sinPerturbationLift k) x = -sin ((k + 2) * x) := by
  -- The identity has vanishing second derivative, so this is the case `m = 2` of
  -- `iteratedDeriv_sinPerturbationLift_sub_id`.
  have h := iteratedDeriv_sinPerturbationLift_sub_id k 2 x
  rw [iteratedDeriv_sub (contDiff_sinPerturbationLift k).contDiffAt contDiff_id.contDiffAt,
    iteratedDeriv_id, mul_div_cancel_left₀ _ (by positivity)] at h
  simpa using h

/-- The distance between the `m`-th derivatives of the `k`-th lift and of the identity. -/
private theorem dist_iteratedFDeriv_sinPerturbationLift (k m : ℕ) (x : ℝ) :
    dist (iteratedFDeriv ℝ m (sinPerturbationLift k) x) (iteratedFDeriv ℝ m id x) =
      |((k : ℝ) + 2) ^ m * iteratedDeriv m sin ((k + 2) * x) / ((k : ℝ) + 2) ^ 2| := by
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply (contDiff_sinPerturbationLift k).contDiffAt
    contDiff_id.contDiffAt, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_sinPerturbationLift_sub_id, Real.norm_eq_abs]

/-- The distance between the second derivatives of the `k`-th lift and of the identity is
`|sin ((k + 2) x)|`, since the identity has vanishing second derivative. -/
private theorem dist_iteratedFDeriv_two_sinPerturbationLift (k : ℕ) (x : ℝ) :
    dist (iteratedFDeriv ℝ 2 (sinPerturbationLift k) x) (iteratedFDeriv ℝ 2 id x) =
      |sin ((k + 2) * x)| := by
  rw [dist_iteratedFDeriv_sinPerturbationLift, mul_div_cancel_left₀ _ (by positivity)]
  simp

/-- The values at `0` of the perturbations are `0`. -/
private theorem sinPerturbation_apply_zero {n : ℕ∞ω} (hn : n ≠ 0) (k : ℕ) :
    sinPerturbation hn k 0 = 0 := by
  rw [← AddCircle.coe_zero, sinPerturbation_apply_coe, sinPerturbationLift_zero]

/-- **Convergence in `C¹`.** The perturbations `θ ↦ θ + sin ((k + 2) θ) / (k + 2) ^ 2` tend to the
identity in the `C¹` weak Whitney topology on the `C¹` diffeomorphisms of the circle. -/
theorem tendsto_sinPerturbation_one :
    Tendsto (sinPerturbation (n := 1) one_ne_zero) atTop (𝓝 1) := by
  -- Convergence of the underlying `C¹` maps, read through their lifts; the underlying map of
  -- `Diffeomorph.toContMDiffMap` is the diffeomorphism itself.
  rw [Diffeomorph.isEmbedding_toContMDiffMap.isInducing.tendsto_nhds_iff]
  refine (ContMDiffMap.tendsto_addCircle_addCircle_iff_lift le_rfl (F := sinPerturbationLift)
    (G := id) (fun k ↦ (contDiff_sinPerturbationLift (n := 1) k).continuous) continuous_id
    (fun k x ↦ by
      rw [Function.comp_apply, Diffeomorph.coe_toContMDiffMap, sinPerturbation_apply_coe])
    (fun x ↦ by rw [Diffeomorph.coe_toContMDiffMap, Diffeomorph.one_apply, id])).2
    ⟨?_, fun m hm ↦ ?_⟩
  · simp only [Function.comp_def, Diffeomorph.coe_toContMDiffMap, sinPerturbation_apply_zero,
      Diffeomorph.one_apply]
    exact tendsto_const_nhds
  · have hm' : m ≤ 1 := by exact_mod_cast hm
    simp only [sinPerturbationLift_zero, id_eq, sub_zero, ← Function.id_def]
    -- The `m`-th derivatives, `m ≤ 1`, are within `1 / (k + 1)` of those of the identity.
    refine (tendstoUniformlyOn_univ.1 (TauCeti.tendstoUniformlyOn_of_dist_le
      (u := fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall fun k x _ ↦ ?_))).tendstoLocallyUniformly
    have hk : (0 : ℝ) < k + 2 := by positivity
    have hs := Real.abs_iteratedDeriv_sin_le_one m ((k + 2) * x)
    rw [dist_iteratedFDeriv_sinPerturbationLift, abs_div, abs_mul, abs_of_pos (pow_pos hk _),
      abs_of_pos (pow_pos hk _), div_le_div_iff₀ (pow_pos hk _) (by positivity)]
    have hpow : ((k : ℝ) + 2) ^ m ≤ (k : ℝ) + 2 := by
      calc ((k : ℝ) + 2) ^ m ≤ ((k : ℝ) + 2) ^ 1 :=
            pow_le_pow_right₀ (by linarith) hm'
        _ = (k : ℝ) + 2 := pow_one _
    calc ((k : ℝ) + 2) ^ m * |iteratedDeriv m sin ((k + 2) * x)| * ((k : ℝ) + 1)
        ≤ ((k : ℝ) + 2) * 1 * ((k : ℝ) + 2) := by gcongr; linarith
      _ = 1 * ((k : ℝ) + 2) ^ 2 := by ring

/-- **No convergence in `C^n`, `n ≥ 2`.** The perturbations
`θ ↦ θ + sin ((k + 2) θ) / (k + 2) ^ 2` do not tend to the identity in the `C^n` weak Whitney
topology on the `C^n` diffeomorphisms of the circle for any `n ≥ 2`, in particular not in
`Diff(S¹)` with its `C^∞` topology: their second derivatives have supremum `1`. -/
theorem not_tendsto_sinPerturbation_one {n : ℕ∞ω} (hn : 2 ≤ n) :
    ¬ Tendsto (sinPerturbation (zero_lt_two.trans_le hn).ne') atTop (𝓝 1) := by
  intro h
  -- Read the convergence through the lifts, as in `tendsto_sinPerturbation_one`.
  rw [Diffeomorph.isEmbedding_toContMDiffMap.isInducing.tendsto_nhds_iff] at h
  have h₂ := ((ContMDiffMap.tendsto_addCircle_addCircle_iff_lift (one_le_two.trans hn)
    (F := sinPerturbationLift) (G := id)
    (fun k ↦ (contDiff_sinPerturbationLift (n := 0) k).continuous)
    continuous_id (fun k x ↦ by
      rw [Function.comp_apply, Diffeomorph.coe_toContMDiffMap, sinPerturbation_apply_coe])
    (fun x ↦ by rw [Diffeomorph.coe_toContMDiffMap, Diffeomorph.one_apply, id])).1 h).2 2 hn
  simp only [sinPerturbationLift_zero, id_eq, sub_zero, ← Function.id_def] at h₂
  -- Near `0` the second derivatives would be uniformly close to `0`, but at `π / (2 (k + 2))`
  -- they are `-1`.
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformly_iff.1 h₂ 1 one_pos 0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hx : Tendsto (fun k : ℕ ↦ π / (2 * ((k : ℝ) + 2))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop two_pos
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  obtain ⟨k, hk₁, hk₂⟩ := (hev.and (hx.eventually (Metric.ball_mem_nhds 0 hδ))).exists
  have hk := hk₁ _ (hball hk₂)
  have hk0 : (0 : ℝ) < k + 2 := by positivity
  rw [dist_comm, dist_iteratedFDeriv_two_sinPerturbationLift,
    show ((k : ℝ) + 2) * (π / (2 * ((k : ℝ) + 2))) = π / 2 by field_simp, sin_pi_div_two,
    abs_one] at hk
  exact lt_irrefl _ hk

end TauCeti
