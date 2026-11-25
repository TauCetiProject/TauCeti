/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
public import TauCeti.Examples.Analysis.Variational.WeakLowerSemicontinuity
public import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Checks: weakly convergent sequences of unit vectors in `ℓ²`

Checks of the direct method that use the weak convergence `eₙ ⇀ 0` of the unit vectors of `ℓ²`
(`TauCeti.VariationalChecks.tendsto_toWeakSpace_e`).

* The sequence `u_{2n} = eₙ`, `u_{2n+1} = 2 eₙ` converges weakly to `0`
  (`tendsto_toWeakSpace_mixed`), with `liminf ‖uₖ‖² = 1` and `limsup ‖uₖ‖² = 4`
  (`liminf_norm_sq_mixed`, `limsup_norm_sq_mixed`), and every tail contains a vector of energy `4`
  (`exists_ge_norm_sq_mixed_eq_four`): Mazur's lemma on the tails of the whole sequence only
  bounds `‖0‖²` by `4`, while along the subsequence `(eₙ)` realizing the lower limit it gives the
  lower-semicontinuity inequality `‖0‖² ≤ 1`.
* `j = id` fails the conclusion that compact maps send weakly convergent sequences to norm
  convergent ones: `eₙ ⇀ 0` but `eₙ ↛ 0` in norm (`not_tendsto_e`).
* The unbounded sequence `(n + 1) eₙ` does not converge weakly (`not_tendsto_toWeakSpace_smul_e`),
  since weakly convergent sequences are bounded.
* The unit sphere of `ℓ²` is bounded but not weakly sequentially closed, since `eₙ ⇀ 0`
  (`not_isSeqClosed_toWeakSpace_sphere`): the closedness hypothesis of the direct method cannot be
  dropped.
* For `E(u) = ‖u‖` on `ℓ²`, `uₙ = eₙ/(n + 1)` is a bounded minimizing sequence: `E(uₙ) → 0`, the
  infimum, which is attained at the limit `0` (`tendsto_norm_e_div`, `isMinOn_norm`,
  `tendsto_e_div`); the unbounded `(n + 1) eₙ` is not minimizing, with `E = n + 1`
  (`norm_smul_e`).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti.VariationalChecks

local notation "L2" => lp (fun _ : ℕ ↦ ℝ) 2

/-- The unit vectors of `ℓ²` have norm `1`. -/
theorem norm_e (n : ℕ) : ‖e n‖ = 1 :=
  e.orthonormal.1 n

/-! ### A weakly convergent sequence with two energy levels -/

/-- The sequence `u_{2n} = eₙ`, `u_{2n+1} = 2 eₙ`. -/
noncomputable def mixed (k : ℕ) : L2 :=
  (if Even k then (1 : ℝ) else 2) • e (k / 2)

/-- `‖u_{2n}‖² = 1`. -/
theorem norm_sq_mixed_two_mul (n : ℕ) : ‖mixed (2 * n)‖ ^ 2 = 1 := by
  simp [mixed, norm_e]

/-- `‖u_{2n+1}‖² = 4`. -/
theorem norm_sq_mixed_two_mul_add_one (n : ℕ) : ‖mixed (2 * n + 1)‖ ^ 2 = 4 := by
  have h : (2 * n + 1) / 2 = n := by omega
  simp only [mixed, Nat.not_even_two_mul_add_one, ↓reduceIte, h, norm_smul, norm_e]
  norm_num

/-- The energies `‖uₖ‖²` lie between `1` and `4`. -/
theorem norm_sq_mixed_mem (k : ℕ) : ‖mixed k‖ ^ 2 ∈ Icc (1 : ℝ) 4 := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [norm_sq_mixed_two_mul]
    norm_num
  · rw [norm_sq_mixed_two_mul_add_one]
    norm_num

/-- **The sequence `u_{2n} = eₙ`, `u_{2n+1} = 2 eₙ` converges weakly to `0`.** -/
theorem tendsto_toWeakSpace_mixed :
    Tendsto (fun k ↦ toWeakSpace ℝ L2 (mixed k)) atTop (𝓝 (toWeakSpace ℝ L2 0)) := by
  refine TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun f ↦ ?_
  have he := TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.1
    (tendsto_toWeakSpace_e.comp (Nat.tendsto_div_const_atTop two_ne_zero)) f
  rw [map_zero] at he ⊢
  -- `f uₖ = cₖ f e_{k/2}` with `|cₖ| ≤ 2` and `f e_{k/2} → 0`.
  refine (he.zero_mul_isBoundedUnder_le (f := fun k : ℕ ↦ f (e (k / 2)))
    (g := fun k : ℕ ↦ if Even k then (1 : ℝ) else 2) ?_).congr fun k ↦ ?_
  · refine isBoundedUnder_of ⟨2, fun k ↦ ?_⟩
    simp only [Function.comp_apply]
    split_ifs <;> norm_num
  · unfold mixed
    split_ifs <;> simp [mul_comm]

/-- Every tail of `(uₖ)` contains a vector of energy `‖uₖ‖² = 4`. -/
theorem exists_ge_norm_sq_mixed_eq_four (N : ℕ) : ∃ k ≥ N, ‖mixed k‖ ^ 2 = 4 :=
  ⟨2 * N + 1, by omega, norm_sq_mixed_two_mul_add_one N⟩

/-- `liminf ‖uₖ‖² = 1`, the energy of the subsequence `(eₙ)`. -/
theorem liminf_norm_sq_mixed : liminf (fun k ↦ ‖mixed k‖ ^ 2) atTop = 1 := by
  have hb : IsBoundedUnder (· ≤ ·) atTop fun k ↦ ‖mixed k‖ ^ 2 :=
    isBoundedUnder_of ⟨4, fun k ↦ (norm_sq_mixed_mem k).2⟩
  have hb' : IsBoundedUnder (· ≥ ·) atTop fun k ↦ ‖mixed k‖ ^ 2 :=
    isBoundedUnder_of ⟨1, fun k ↦ (norm_sq_mixed_mem k).1⟩
  refine le_antisymm (liminf_le_of_frequently_le ?_ hb') (le_liminf_of_le hb.isCoboundedUnder_ge
    (Eventually.of_forall fun k ↦ (norm_sq_mixed_mem k).1))
  exact frequently_atTop.2 fun N ↦ ⟨2 * N, by omega, (norm_sq_mixed_two_mul N).le⟩

/-- `limsup ‖uₖ‖² = 4`. -/
theorem limsup_norm_sq_mixed : limsup (fun k ↦ ‖mixed k‖ ^ 2) atTop = 4 := by
  have hb : IsBoundedUnder (· ≤ ·) atTop fun k ↦ ‖mixed k‖ ^ 2 :=
    isBoundedUnder_of ⟨4, fun k ↦ (norm_sq_mixed_mem k).2⟩
  have hb' : IsBoundedUnder (· ≥ ·) atTop fun k ↦ ‖mixed k‖ ^ 2 :=
    isBoundedUnder_of ⟨1, fun k ↦ (norm_sq_mixed_mem k).1⟩
  refine le_antisymm (limsup_le_of_le hb'.isCoboundedUnder_le
    (Eventually.of_forall fun k ↦ (norm_sq_mixed_mem k).2)) (le_limsup_of_frequently_le ?_ hb)
  exact frequently_atTop.2 fun N ↦ ⟨2 * N + 1, by omega, (norm_sq_mixed_two_mul_add_one N).ge⟩

/-! ### Weak versus norm convergence -/

/-- **The identity of `ℓ²` does not send weakly convergent sequences to norm convergent ones**:
`eₙ ⇀ 0`, but `eₙ` does not converge to `0` in norm, since `‖eₙ‖ = 1`. -/
theorem not_tendsto_e : ¬ Tendsto (fun n ↦ e n) atTop (𝓝 0) := by
  intro h
  have h1 := (continuous_norm.tendsto (0 : L2)).comp h
  simp only [Function.comp_def, norm_e, norm_zero] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- `‖(n + 1) eₙ‖ = n + 1`. -/
theorem norm_smul_e (n : ℕ) : ‖((n : ℝ) + 1) • e n‖ = n + 1 := by
  rw [norm_smul, norm_e, mul_one, Real.norm_of_nonneg (by positivity)]

/-- **The unbounded sequence `(n + 1) eₙ` does not converge weakly** to any limit, since weakly
convergent sequences are bounded. -/
theorem not_tendsto_toWeakSpace_smul_e (x : L2) :
    ¬ Tendsto (fun n : ℕ ↦ toWeakSpace ℝ L2 (((n : ℝ) + 1) • e n)) atTop
      (𝓝 (toWeakSpace ℝ L2 x)) := by
  intro h
  obtain ⟨C, hC⟩ := (h.isBounded_range_of_toWeakSpace).exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC _ ⟨n, rfl⟩
  rw [norm_smul_e] at this
  linarith

/-- **The unit sphere of `ℓ²` is not weakly sequentially closed**: `eₙ` lies on it and `eₙ ⇀ 0`,
which does not. -/
theorem not_isSeqClosed_toWeakSpace_sphere :
    ¬ IsSeqClosed (toWeakSpace ℝ L2 '' Metric.sphere 0 1) := by
  intro h
  have h0 := h (fun n ↦ ⟨e n, by simp [norm_e], rfl⟩) tendsto_toWeakSpace_e
  obtain ⟨u, hu, hu0⟩ := h0
  rw [(toWeakSpace ℝ L2).injective hu0] at hu
  simp at hu

/-! ### A bounded minimizing sequence -/

/-- The norm attains its infimum `0` on `ℓ²` at `0`. -/
theorem isMinOn_norm : IsMinOn (fun u : L2 ↦ ‖u‖) univ 0 :=
  fun u _ ↦ by simp

/-- **`eₙ/(n + 1)` is a minimizing sequence of the norm**: `‖eₙ/(n + 1)‖ = 1/(n + 1) → 0`, the
infimum of the norm. -/
theorem tendsto_norm_e_div :
    Tendsto (fun n : ℕ ↦ ‖((n : ℝ) + 1)⁻¹ • e n‖) atTop (𝓝 0) := by
  have h : (fun n : ℕ ↦ ‖((n : ℝ) + 1)⁻¹ • e n‖) = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := by
    funext n
    rw [norm_smul, norm_e, mul_one, Real.norm_of_nonneg (by positivity), one_div]
  rw [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The minimizing sequence `eₙ/(n + 1)` converges to the minimizer `0`, here even in norm. -/
theorem tendsto_e_div : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • e n) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 tendsto_norm_e_div

end TauCeti.VariationalChecks
