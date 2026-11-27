/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import TauCeti.Analysis.Normed.Operator.CompletelyContinuous
import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Continuous maps of ring-scalar operator norm zero

On finitely supported sequences over trivially normed integers, the vector `eₙ` has weight `2⁻ⁿ`.
The shift `u(eₙ) = e_(n / 2)` and its complement `1 - u` are continuous but have no uniform bound.
Their ring-scalar operator norms are zero because both sets of uniform bounds are empty.
`exists_add_eq_id_ringOpNorm_eq_zero` shows that neither summand is completely continuous:
uniform finite-rank approximation cannot be replaced by approximation in the ring-scalar norm.
`one_le_ringOpNorm_id_sub` gives a lower bound of one on the ring-scalar operator distance
from the identity to every continuous finite-rank map.
-/

public section

open Topology
open scoped NNReal TauCeti.RingOpNorm

namespace TauCeti.Examples.TrivialNorm

/-- The integers with their trivial absolute value. -/
abbrev R := WithAbs (AbsoluteValue.trivial : AbsoluteValue ℤ ℝ)

/-- Finitely supported integer sequences used for the weighted norm example. -/
abbrev E := ℕ →₀ R

/-- The dyadic weight of the coordinate vector at index `n`. -/
noncomputable abbrev weight (n : ℕ) : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ n

/-- The real dyadic power formula for the weight, independent of the coercion implementation. -/
private theorem coe_weight (n : ℕ) : (weight n : ℝ) = (2⁻¹ : ℝ) ^ n := by
  simp [weight]

private theorem weight_pos (n : ℕ) : 0 < (weight n : ℝ) := by
  positivity

/-- The norm given by the maximum of the weights of the nonzero coordinates. -/
noncomputable scoped instance : NormedAddCommGroup E :=
  let f : AddGroupNorm E :=
    { toFun x := (x.support.sup weight : ℝ≥0)
      map_zero' := by simp
      neg' x := by rw [Finsupp.support_neg]
      add_le' x y := by
        exact_mod_cast (Finset.sup_mono Finsupp.support_add).trans
          (Finset.sup_union.trans_le (max_le_add_of_nonneg bot_le bot_le))
      eq_zero_of_map_eq_zero' x hx := by
        ext i
        by_contra hi
        have h := Finset.le_sup (f := weight) (Finsupp.mem_support_iff.mpr hi)
        exact (weight_pos i).not_ge (hx ▸ NNReal.coe_le_coe.mpr h) }
  f.toNormedAddCommGroup

/-- The defining formula for the norm, including zero for the empty support. -/
theorem norm_eq (x : E) : ‖x‖ = (x.support.sup weight : ℝ≥0) := (rfl)

private theorem weight_le_norm {x : E} {i : ℕ} (hi : x i ≠ 0) : (weight i : ℝ) ≤ ‖x‖ := by
  rw [norm_eq, NNReal.coe_le_coe]
  exact Finset.le_sup (Finsupp.mem_support_iff.mpr hi)

private theorem norm_single_one (i : ℕ) : ‖(Finsupp.single i (1 : R) : E)‖ = weight i := by
  simp only [norm_eq, Finsupp.support_single _ one_ne_zero, Finset.sup_singleton]

private theorem weight_antitone : Antitone weight :=
  fun _ _ h ↦ pow_le_pow_right_of_le_one' (by norm_num) h

private theorem lt_index_of_norm_lt_weight {x : E} {N i : ℕ}
    (hx : ‖x‖ < weight N) (hi : x i ≠ 0) : N < i :=
  lt_of_not_ge fun h ↦
    hx.not_ge ((NNReal.coe_le_coe.mpr (weight_antitone h)).trans (weight_le_norm hi))

private noncomputable def halveIndex : E →L[R] E :=
  { Finsupp.lmapDomain R R (fun n : ℕ ↦ n / 2) with
    cont := by
      let f := Finsupp.lmapDomain R R (fun n : ℕ ↦ n / 2)
      refine continuous_of_tendsto_nhds_zero f (Metric.tendsto_nhds_nhds.2 fun ε hε ↦ ?_)
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
      have hN' : (weight N : ℝ) < ε := by rwa [coe_weight]
      refine ⟨weight (2 * N), weight_pos _, fun x hx ↦ ?_⟩
      rw [dist_zero_right] at hx ⊢
      refine lt_of_le_of_lt ?_ hN'
      rw [norm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finsupp.lmapDomain_apply]
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hi)
      have hjN := lt_index_of_norm_lt_weight hx (Finsupp.mem_support_iff.mp hj)
      exact weight_antitone (by lia) }

private theorem halveIndex_single (i : ℕ) :
    halveIndex (Finsupp.single i 1) = Finsupp.single (i / 2) 1 :=
  Finsupp.mapDomain_single

private theorem exists_cutoff_of_isFiniteRank {g : E →L[R] E} (hg : (g : E →ₗ[R] E).IsFiniteRank) :
    ∃ N : ℕ, ∀ x i, N ≤ i → g x i = 0 := by
  obtain ⟨Q, hQfg, hQ⟩ := LinearMap.isFiniteRank_iff_forall_mem.mp hg
  obtain ⟨N, hN⟩ := hQfg.exists_le_supported_Iio
  refine ⟨N, fun x i hi ↦ (Finsupp.mem_supported' R (g x)).1 (hN (hQ x)) i ?_⟩
  exact fun hi' ↦ hi.not_gt (Set.mem_Iio.mp hi')

private theorem not_exists_bound_add {d : E →L[R] E}
    (h : ∃ N : ℕ, ∀ k ≥ N, d (Finsupp.single (2 * k) 1) k = 0) :
    ¬ ∃ C, ∀ x, ‖(halveIndex + d) x‖ ≤ C * ‖x‖ := by
  obtain ⟨N, hN⟩ := h
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  let k := max N m
  let x := Finsupp.single (2 * k) (1 : R)
  have hcoord : (halveIndex + d) x k = 1 := by
    simp only [x, add_apply, Finsupp.add_apply, halveIndex_single, Nat.mul_div_cancel_left k
      (by norm_num : 0 < 2), Finsupp.single_eq_same, hN k (le_max_left _ _), add_zero]
  have hratio : C * (weight k : ℝ) < 1 := by
    have hk : C < (2 : ℝ) ^ k := hm.trans_le (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
    rw [coe_weight, inv_pow]
    exact (mul_inv_lt_iff₀ (by positivity)).2 (by simpa only [one_mul] using hk)
  have hinput : ‖x‖ = (weight k : ℝ) ^ 2 := by
    simpa only [x, norm_single_one, coe_weight] using (pow_mul' (2⁻¹ : ℝ) 2 k)
  have hbound := (weight_le_norm (ne_zero_of_eq_one hcoord)).trans (hC x)
  rw [hinput] at hbound
  nlinarith only [hbound, mul_pos (sub_pos.mpr hratio) (weight_pos k)]

/-- The identity is at ring-scalar operator distance at least one from every continuous
finite-rank map on the dyadically normed sequence space. -/
theorem one_le_ringOpNorm_id_sub {g : E →L[R] E} (hg : (g : E →ₗ[R] E).IsFiniteRank) :
    1 ≤ ‖ContinuousLinearMap.id R E - g‖ := by
  obtain ⟨N, hN⟩ := exists_cutoff_of_isFiniteRank hg
  -- Continuity and the support cutoff force `g` to vanish on a ball.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (g.continuous.tendsto 0
    (by rw [map_zero]; exact Metric.ball_mem_nhds 0 (weight_pos N)))
  have hg_bound (x : E) : ‖g x‖ ≤ r⁻¹ * ‖x‖ := by
    by_cases hx : ‖x‖ < r
    · have hsmall := mem_ball_zero_iff.mp (hball (mem_ball_zero_iff.mpr hx))
      have hz : g x = 0 := by
        ext i
        by_cases hi : N ≤ i
        · exact hN x i hi
        by_contra h
        exact hi (lt_index_of_norm_lt_weight hsmall h).le
      rw [hz, norm_zero]
      positivity
    refine (le_trans ?_ ((one_le_inv_mul₀ hr).2 (le_of_not_gt hx)))
    rw [norm_eq, ← NNReal.coe_one, NNReal.coe_le_coe, Finset.sup_le_iff]
    exact fun i _ ↦ (weight_antitone (Nat.zero_le i)).trans_eq (pow_zero _)
  have hb := ContinuousLinearMap.le_ringOpNorm_of_exists_bound (ContinuousLinearMap.id R E - g)
    ⟨1 + r⁻¹, fun x ↦ by
      simpa only [sub_apply, ContinuousLinearMap.id_apply, add_mul, one_mul]
        using (norm_sub_le x (g x)).trans (add_le_add_right (hg_bound x) _)⟩
  let x := Finsupp.single N (1 : R)
  have hcoord : ((ContinuousLinearMap.id R E - g) x) N = 1 := by
    simp only [sub_apply, ContinuousLinearMap.id_apply, Finsupp.sub_apply,
      hN x N le_rfl, sub_zero]
    exact Finsupp.single_eq_same
  have hx : ‖x‖ = weight N := norm_single_one _
  have hle := (weight_le_norm (ne_zero_of_eq_one hcoord)).trans (hb x)
  exact le_of_mul_le_mul_right (by simpa only [one_mul, hx] using hle) (weight_pos N)

/-- Two continuous endomorphisms of ring-scalar operator norm zero can sum to the identity
on the dyadically normed sequence space. Neither summand is completely continuous. -/
theorem exists_add_eq_id_ringOpNorm_eq_zero :
    ∃ u v : E →L[R] E, u + v = ContinuousLinearMap.id R E ∧
      ‖u‖ = 0 ∧ ‖v‖ = 0 ∧ ¬u.IsCompletelyContinuous ∧ ¬v.IsCompletelyContinuous := by
  have key (d : E →L[R] E) (hd : ∀ k > 0, d (Finsupp.single (2 * k) 1) k = 0) :
      ‖halveIndex + d‖ = 0 ∧ ¬(halveIndex + d).IsCompletelyContinuous := by
    constructor
    · exact (halveIndex + d).ringOpNorm_eq_zero_of_not_exists_bound
        (not_exists_bound_add ⟨1, fun k hk ↦ hd k (by lia)⟩)
    · intro h
      obtain ⟨g, hg, hC⟩ := ContinuousLinearMap.isCompletelyContinuous_iff.mp h 1 one_pos
      obtain ⟨N, hN⟩ := exists_cutoff_of_isFiniteRank hg
      refine not_exists_bound_add (d := d - g) ⟨N + 1, fun k hk ↦ ?_⟩ ⟨1, fun x ↦ ?_⟩
      · simp only [sub_apply, Finsupp.sub_apply, hd k (by lia), hN _ k (by lia), sub_zero]
      · simpa only [sub_apply, add_apply, add_sub_assoc] using hC x
  have hzero := key 0 (by simp)
  have hid := key (-ContinuousLinearMap.id R E) (fun k hk ↦ by
    simp only [neg_apply, ContinuousLinearMap.id_apply, Finsupp.neg_apply, neg_eq_zero]
    exact Finsupp.single_eq_of_ne (by lia))
  rw [add_zero] at hzero
  rw [← sub_eq_add_neg, ← neg_sub, ContinuousLinearMap.ringOpNorm_neg,
    ContinuousLinearMap.IsCompletelyContinuous.neg_iff] at hid
  exact ⟨halveIndex, _, add_sub_cancel _ _, hzero.1, hid.1, hzero.2, hid.2⟩

end TauCeti.Examples.TrivialNorm
