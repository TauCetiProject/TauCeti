/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Cardinality
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.Wkp.Gluing
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Classical
import TauCeti.Analysis.Sobolev.Wkp.SmoothMultiplication
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `W^{k,∞}(Ω)` is not separable, and smooth functions are not dense in it

Let `Ω` be a nonempty open subset of a finite-dimensional real inner product space `E` of positive
dimension. For finite `p` the Sobolev space `W^{k,p}(Ω)` is separable
(`TauCeti.Wkp.instSecondCountableTopology`), and the functions smooth on `Ω` are dense in it
(Meyers–Serrin, `TauCeti.Wkp.dense_contDiffOn_representatives`). At the infinite exponent both
fail, at every order `k` and on every such `Ω`:

* `W^{k,∞}(Ω)` is not separable (`TauCeti.Wkp.not_separableSpace_top`);
* the elements of `W^{k,∞}(Ω)` with a representative of class `Cᵏ` on `Ω`, in particular those
  with a representative smooth on `Ω`, are not dense in it
  (`TauCeti.Wkp.not_dense_contDiffOn_representatives_top`).

At `k = 0` these are the statements for `L^∞(Ω)`. On a bounded interval, the case `k = 1` of the
first is `TauCeti.W1p.not_separableSpace_Ioo_top`, and the second gives
`TauCeti.Wkp.not_dense_contDiff_representatives_Ioo_top` for globally smooth representatives.

## The argument

Fix a ball `B = B(x₀, r) ⊆ Ω` and a unit vector `e`. For `t ∈ ℝ` and `k ≥ 1` the truncated power
`x ↦ (⟪e, x⟫ - t)₊ᵏ` is locally Lipschitz, with derivative `k (⟪e, x⟫ - t)₊ᵏ⁻¹ e` off the
hyperplane `⟪e, x⟫ = t`, which is a null set; for `k = 0` it is the Heaviside function of
`⟪e, x⟫ - t`. So its weak directional derivatives are again truncated powers, and by the
description of the Sobolev scale through first derivatives
(`TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`) it lies in `W^{k,∞}(B)`, with
`k`-th weak derivative in the direction `e` equal to `k!` times the Heaviside function of
`⟪e, x⟫ - t`. Multiplying by a smooth bump equal to one on `B(x₀, r / 2)` and supported in
`B(x₀, 3r / 4)`, and gluing with zero outside (`TauCeti.Wkp.exists_glue`), gives an element `v_t`
of `W^{k,∞}(Ω)` with the same `k`-th derivative on `B(x₀, r / 2)`.

The `k`-th directional derivative on `B(x₀, r / 2)`, composed with restriction, is a bounded
operator `T : W^{k,∞}(Ω) → L^∞(B(x₀, r / 2))`.

* For `s < t` near `⟪e, x₀⟫`, the functions `T v_s` and `T v_t` differ by `k!` on the slab
  `s < ⟪e, x⟫ < t`, which meets `B(x₀, r / 2)` in a set of positive measure. So the uncountable
  family `v_t` is uniformly separated, and `W^{k,∞}(Ω)` is not separable.
* If `w` has a representative `f` of class `Cᵏ` on `Ω`, then `T w` is represented by the continuous
  function `x ↦ D^k f(x)(e, …, e)`. A continuous function cannot be uniformly within less than
  `k! / 2` of `k!` times a jump across a hyperplane through `x₀`, so `w` stays at distance at least
  `k! / (2 ‖T‖)` from the element `v_t` with `t = ⟪e, x₀⟫`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the distinction between
  finite and infinite exponents in separability and smooth approximation.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped ENNReal RealInnerProductSpace Nat ContDiff Topology

namespace TauCeti.Wkp

/-! ### Truncated powers -/

/-- The truncated power `s₊ʲ`, equal to `sʲ` for `s > 0` and to `0` otherwise. At `j = 0` it is the
Heaviside function. -/
private def truncPow (j : ℕ) (s : ℝ) : ℝ := if 0 < s then s ^ j else 0

private theorem truncPow_of_pos {j : ℕ} {s : ℝ} (hs : 0 < s) : truncPow j s = s ^ j := by
  simp [truncPow, hs]

private theorem truncPow_of_nonpos {j : ℕ} {s : ℝ} (hs : s ≤ 0) : truncPow j s = 0 := by
  simp [truncPow, hs.not_gt]

private theorem measurable_truncPow (j : ℕ) : Measurable (truncPow j) :=
  Measurable.ite measurableSet_Ioi (measurable_id.pow_const j) measurable_const

private theorem abs_truncPow_le (j : ℕ) (s : ℝ) : |truncPow j s| ≤ |s| ^ j := by
  rcases lt_or_ge 0 s with hs | hs
  · rw [truncPow_of_pos hs, abs_pow]
  · rw [truncPow_of_nonpos hs, abs_zero]
    positivity

private theorem locallyLipschitz_truncPow_succ (j : ℕ) : LocallyLipschitz (truncPow (j + 1)) := by
  have h : truncPow (j + 1) = (fun s : ℝ => s ^ (j + 1)) ∘ fun s => max s 0 := by
    funext s
    rcases lt_or_ge 0 s with hs | hs
    · rw [truncPow_of_pos hs, Function.comp_apply, max_eq_left hs.le]
    · rw [truncPow_of_nonpos hs, Function.comp_apply, max_eq_right hs, zero_pow j.succ_ne_zero]
  have hpow : ContDiff ℝ 1 fun s : ℝ => s ^ (j + 1) := contDiff_id.pow _
  rw [h]
  exact hpow.locallyLipschitz.comp (LipschitzWith.id.max_const 0).locallyLipschitz

/-- Away from the origin, `s₊ʲ⁺¹` has derivative `(j + 1) s₊ʲ`. -/
private theorem hasDerivAt_truncPow_succ (j : ℕ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (truncPow (j + 1)) ((j + 1) * truncPow j s) s := by
  rcases hs.lt_or_gt with hs | hs
  · rw [truncPow_of_nonpos hs.le, mul_zero]
    exact (hasDerivAt_const s 0).congr_of_eventuallyEq
      ((eventually_lt_nhds hs).mono fun y hy => truncPow_of_nonpos hy.le)
  · rw [truncPow_of_pos hs]
    have h := (hasDerivAt_pow (j + 1) s).congr_of_eventuallyEq
      ((eventually_gt_nhds hs).mono fun y hy => truncPow_of_pos (j := j + 1) hy)
    simpa using h

/-! ### Truncated powers of an affine function -/

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

/-- The weak directional derivatives of `x ↦ (⟪e, x⟫ - t)₊ʲ⁺¹` are
`(j + 1) ⟪v, e⟫ (⟪e, x⟫ - t)₊ʲ`. -/
private theorem hasWeakLineDerivOn_truncPow_succ {e : E} (he : e ≠ 0) (U : Opens E) (t : ℝ)
    (j : ℕ) (v : E) :
    HasWeakLineDerivOn mu U (fun x => truncPow (j + 1) (⟪e, x⟫ - t))
      (fun x => ((j + 1) * ⟪v, e⟫) * truncPow j (⟪e, x⟫ - t)) v := by
  have ha : ContDiff ℝ 1 fun x : E => ⟪e, x⟫ - t := (contDiff_const.inner ℝ contDiff_id).sub
    contDiff_const
  have hlip : LocallyLipschitzOn U (fun x => truncPow (j + 1) (⟪e, x⟫ - t)) :=
    ((locallyLipschitz_truncPow_succ j).comp ha.locallyLipschitz).locallyLipschitzOn
  have hd : ∀ᵐ x ∂mu, x ∈ U → HasFDerivAt (fun x => truncPow (j + 1) (⟪e, x⟫ - t))
      (((j + 1) * truncPow j (⟪e, x⟫ - t)) • innerSL ℝ e) x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (mu.addHaar_setOf_inner_eq he t)] with x hx _
    have hx' : ⟪e, x⟫ - t ≠ 0 := sub_ne_zero.2 fun h => hx ((real_inner_comm e x).trans h)
    exact (hasDerivAt_truncPow_succ j hx').comp_hasFDerivAt x
      ((innerSL ℝ e).hasFDerivAt.sub_const t)
  refine ((hlip.hasWeakFDerivOn hd).hasWeakLineDerivOn v).congr_ae_deriv (ae_of_all _ fun x => ?_)
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_comm v e]
  ring

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- On a ball, `x ↦ (⟪e, x⟫ - t)₊ʲ` is essentially bounded. -/
private theorem memLp_truncPow_ball {e : E} (he : ‖e‖ = 1) (x₀ : E) (r t : ℝ) (j : ℕ) :
    MemLp (fun x : E => truncPow j (⟪e, x⟫ - t)) ∞ (mu.restrict (ball x₀ r)) := by
  refine memLp_top_of_bound ((measurable_truncPow j).comp
    ((continuous_const.inner continuous_id).sub continuous_const).measurable).aestronglyMeasurable
    ((‖x₀‖ + r + |t|) ^ j) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs]
  refine (abs_truncPow_le j _).trans (pow_le_pow_left₀ (abs_nonneg _) ?_ j)
  have hx' : ‖x‖ ≤ ‖x₀‖ + r := by
    have := norm_le_norm_add_norm_sub' x x₀
    rw [mem_ball_iff_norm] at hx
    linarith
  calc |⟪e, x⟫ - t| ≤ |⟪e, x⟫| + |t| := abs_sub _ _
    _ ≤ ‖e‖ * ‖x‖ + |t| := by gcongr; exact abs_real_inner_le_norm e x
    _ ≤ ‖x₀‖ + r + |t| := by rw [he, one_mul]; linarith

/-- On a ball, `x ↦ (⟪e, x⟫ - t)₊ᵏ` lies in `W^{k,∞}`, and for a unit vector `e` its `k`-th weak
derivative in the direction `e` is `k!` times the Heaviside function of `⟪e, x⟫ - t`. -/
private theorem exists_value_truncPow_ball {e : E} (he : ‖e‖ = 1) (x₀ : E) (r t : ℝ) :
    ∀ k : ℕ, ∃ u : Wkp mu ⟨ball x₀ r, isOpen_ball⟩ ∞ k,
      (value k u : E → ℝ) =ᵐ[mu.restrict (ball x₀ r)] (fun x => truncPow k (⟪e, x⟫ - t)) ∧
      (iteratedLineDerivZeroL k (fun _ => e) u : E → ℝ) =ᵐ[mu.restrict (ball x₀ r)]
        fun x => (k ! : ℝ) * truncPow 0 (⟪e, x⟫ - t) := by
  have hmem := memLp_truncPow_ball (mu := mu) he x₀ r t
  intro k
  induction k with
  | zero =>
    refine ⟨(hmem 0).toLp _, ?_, ?_⟩
    · rw [value_zero]
      exact (hmem 0).coeFn_toLp
    · rw [iteratedLineDerivZeroL_zero, ContinuousLinearMap.id_apply]
      filter_upwards [(hmem 0).coeFn_toLp] with x hx
      rw [hx, Nat.factorial_zero, Nat.cast_one, one_mul]
  | succ k ih =>
    obtain ⟨u, hu, hD⟩ := ih
    -- The directional derivatives of the truncated power of order `k + 1` are multiples of `u`.
    let d : E → Wkp mu ⟨ball x₀ r, isOpen_ball⟩ ∞ k := fun v => (((k : ℝ) + 1) * ⟪v, e⟫) • u
    have hd (v : E) : HasWeakLineDerivOn mu ⟨ball x₀ r, isOpen_ball⟩
        (fun x => truncPow (k + 1) (⟪e, x⟫ - t)) (value k (d v)) v := by
      refine (hasWeakLineDerivOn_truncPow_succ (norm_ne_zero_iff.1 (he ▸ one_ne_zero)) _ t k
        v).congr_ae_deriv ?_
      filter_upwards [value_smul_ae k (((k : ℝ) + 1) * ⟪v, e⟫) u, hu] with x h₁ h₂
      rw [h₁, Pi.smul_apply, h₂, smul_eq_mul]
    obtain ⟨W, hW⟩ := exists_value_ae_eq_of_forall_hasWeakLineDerivOn k (hmem (k + 1)) d hd
    have hlin : lineDerivL e k W = ((k : ℝ) + 1) • u := by
      rw [lineDerivL_eq_of_hasWeakLineDerivOn ((hd e).congr_ae hW.symm)]
      simp only [d, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
    refine ⟨W, hW, ?_⟩
    have htail : Fin.tail (fun _ : Fin (k + 1) => e) = fun _ => e := rfl
    rw [iteratedLineDerivZeroL_succ, ContinuousLinearMap.comp_apply, hlin, htail, map_smul]
    filter_upwards [Lp.coeFn_smul ((k : ℝ) + 1) (iteratedLineDerivZeroL k (fun _ => e) u), hD]
      with x h₁ h₂
    rw [h₁, Pi.smul_apply, h₂, smul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

/-- For a ball `B(x₀, r) ⊆ Ω` and every `t`, some `v ∈ W^{k,∞}(Ω)` has, on `B(x₀, r / 2)`, `k`-th
weak derivative in the unit direction `e` equal to `k!` times the Heaviside function of
`⟪e, x⟫ - t`. -/
private theorem exists_iteratedLineDerivZeroL_restrictL_ae_eq {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hsub : ball x₀ r ⊆ Omega) (hB : (⟨ball x₀ (r / 2), isOpen_ball⟩ : Opens E) ≤ Omega) {e : E}
    (he : ‖e‖ = 1) (k : ℕ) (t : ℝ) :
    ∃ v : Wkp mu Omega ∞ k,
      (iteratedLineDerivZeroL k (fun _ => e) (restrictL hB k v) : E → ℝ)
        =ᵐ[mu.restrict (ball x₀ (r / 2))] fun x => (k ! : ℝ) * truncPow 0 (⟪e, x⟫ - t) := by
  obtain ⟨u, hu, -⟩ := exists_value_truncPow_ball (mu := mu) he x₀ r t k
  obtain ⟨u', hu', hD'⟩ := exists_value_truncPow_ball (mu := mu) he x₀ (r / 2) t k
  -- A smooth cutoff equal to one on `B(x₀, r / 2)` and supported in `B(x₀, 3r / 4)`.
  let ζ : ContDiffBump x₀ := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hcomp : IsCompact (closure (ball x₀ r)) :=
    (isCompact_closedBall x₀ r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  let B : Opens E := ⟨ball x₀ r, isOpen_ball⟩
  let V : Opens E := ⟨(Omega : Set E) ∩ (closedBall x₀ (3 * r / 4))ᶜ,
    Omega.isOpen.inter isClosed_closedBall.isOpen_compl⟩
  let w₁ : Wkp mu B ∞ k :=
    contDiffOnSMulL uniqueDiffOn_univ hcomp (subset_univ _) k ζ.contDiff.contDiffOn u
  let F : E → ℝ := fun x => ζ x * truncPow k (⟪e, x⟫ - t)
  have hle : ∀ b : Bool, cond b B V ≤ Omega := by
    rintro (_ | _)
    · rw [Bool.cond_false, ← SetLike.coe_subset_coe, Opens.coe_mk]
      exact inter_subset_left
    · exact hsub
  have hcov : Omega ≤ ⨆ b : Bool, cond b B V := by
    intro x hx
    rw [Opens.mem_iSup]
    by_cases hxB : x ∈ ball x₀ r
    · exact ⟨true, hxB⟩
    · refine ⟨false, hx, fun hxc => hxB ?_⟩
      have := mem_closedBall.1 hxc
      rw [mem_ball]
      linarith
  obtain ⟨v, hv, -, -⟩ := exists_glue hle hcov k
    (fun b => match b with | true => w₁ | false => 0) (u := F) (by
      rintro (_ | _)
      · filter_upwards [value_zero_ae (mu := mu) (Omega := V) (p := ∞) k,
          ae_restrict_mem V.isOpen.measurableSet] with x h₁ h₂
        have hζ : ζ x = 0 := Function.notMem_support.1 fun hx => h₂.2 (by
          rw [ζ.support_eq] at hx
          exact ball_subset_closedBall hx)
        rw [h₁, Pi.zero_apply]
        simp only [F, hζ, zero_mul]
      · filter_upwards [value_contDiffOnSMulL_ae uniqueDiffOn_univ hcomp (subset_univ _) k
          ζ.contDiff.contDiffOn u, hu] with x h₁ h₂
        rw [h₁, h₂])
  refine ⟨v, ?_⟩
  have hres : restrictL hB k v = u' := by
    refine restrictL_eq_of_value_ae_eq_restrict hB k hv (hu'.trans ?_)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [F, ζ.one_of_mem_closedBall (ball_subset_closedBall hx), one_mul]
  rw [hres]
  exact hD'

/-- The setting shared by both theorems: a ball `B(x₀, ρ) ⊆ Ω`, a unit vector `e`, and the bounded
operator `T : W^{k,∞}(Ω) → L^∞(B(x₀, ρ))` taking the `k`-th weak derivative in the direction `e` on
the ball. For every `t`, some `v` has `T v` equal to `k!` times the Heaviside function of
`⟪e, x⟫ - t`; and if `w` has a representative `f` of class `Cᵏ` on `Ω`, then `T w` is represented
by `x ↦ D^k f(x)(e, …, e)`. -/
private theorem exists_ball_clm_ae_eq [Nontrivial E] (hΩ : (Omega : Set E).Nonempty) (k : ℕ) :
    ∃ (x₀ : E) (ρ : ℝ) (e : E) (T : Wkp mu Omega ∞ k →L[ℝ] Lp ℝ ∞ (mu.restrict (ball x₀ ρ))),
      0 < ρ ∧ ball x₀ ρ ⊆ Omega ∧ ‖e‖ = 1 ∧
      (∀ t : ℝ, ∃ v, (T v : E → ℝ) =ᵐ[mu.restrict (ball x₀ ρ)]
        fun x => (k ! : ℝ) * truncPow 0 (⟪e, x⟫ - t)) ∧
      ∀ (w : Wkp mu Omega ∞ k) {f : E → ℝ}, ContDiffOn ℝ k f Omega →
        (value k w : E → ℝ) =ᵐ[mu.restrict Omega] f →
        (T w : E → ℝ) =ᵐ[mu.restrict (ball x₀ ρ)] fun x => iteratedFDeriv ℝ k f x fun _ => e := by
  obtain ⟨x₀, hx₀⟩ := hΩ
  obtain ⟨r, hr, hsub⟩ := isOpen_iff.1 Omega.isOpen x₀ hx₀
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have hB : (⟨ball x₀ (r / 2), isOpen_ball⟩ : Opens E) ≤ Omega :=
    (ball_subset_ball (half_le_self hr.le)).trans hsub
  refine ⟨x₀, r / 2, e, (iteratedLineDerivZeroL k fun _ => e).comp (restrictL hB k), half_pos hr,
    hB, he, exists_iteratedLineDerivZeroL_restrictL_ae_eq hr hsub hB he k, fun w f hf hwf => ?_⟩
  exact iteratedLineDerivZeroL_ae_eq_of_contDiffOn k _ _ (hf.mono hB)
    ((value_restrictL_ae hB k w).trans (ae_restrict_of_ae_restrict_of_subset hB hwf))

/-- A bounded operator `T` into `L^∞(ν)` moves values, almost everywhere, by at most
`‖T‖ dist a b`. -/
private theorem ae_dist_le_opNorm_mul_dist {α F : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : F →L[ℝ] Lp ℝ ∞ ν) (a b : F) :
    ∀ᵐ x ∂ν, dist (T a x) (T b x) ≤ ‖T‖ * dist a b :=
  (Lp.ae_dist_le_dist_top (T a) (T b)).mono fun _ h => h.trans (T.lipschitzWith.dist_le_mul a b)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The point `x₀ + s e`, for a unit vector `e` and `|s| < ρ`, lies in `B(x₀, ρ)` and has
`⟪e, x₀ + s e⟫ = ⟪e, x₀⟫ + s`. -/
private theorem add_smul_mem_ball_and_inner_eq {e : E} (he : ‖e‖ = 1) (x₀ : E) {s ρ : ℝ}
    (hs : |s| < ρ) : x₀ + s • e ∈ ball x₀ ρ ∧ ⟪e, x₀ + s • e⟫ = ⟪e, x₀⟫ + s := by
  refine ⟨?_, ?_⟩
  · rwa [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs]
  · rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If a property holds almost everywhere on `B(x₀, ρ)` and some point of the ball lies in the open
slab `s < ⟪e, x⟫ < t`, then some point of the ball in that slab has the property. -/
private theorem exists_mem_ball_inner_mem_Ioo_of_ae {x₀ y e : E} {ρ s t : ℝ} {P : E → Prop}
    (h : ∀ᵐ x ∂mu.restrict (ball x₀ ρ), P x) (hy : y ∈ ball x₀ ρ) (hys : ⟪e, y⟫ ∈ Ioo s t) :
    ∃ x ∈ ball x₀ ρ, ⟪e, x⟫ ∈ Ioo s t ∧ P x := by
  obtain ⟨x, ⟨hx, hxs⟩, hPx⟩ := mu.exists_mem_of_measure_ne_zero_of_ae
    ((isOpen_ball.inter (isOpen_Ioo.preimage (continuous_const.inner continuous_id))
      ).measure_ne_zero mu ⟨y, hy, hys⟩)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left h)
  exact ⟨x, hx, hxs, hPx⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A function continuous at a point `x₀` of the hyperplane `⟪e, x⟫ = ⟪e, x₀⟫` is not, almost
everywhere near `x₀`, within `β < a / 2` of `a` times the Heaviside function of `⟪e, x⟫ - ⟪e, x₀⟫`:
it would have to be close to `a` on one side of the hyperplane and to `0` on the other. -/
private theorem not_ae_abs_mul_truncPow_sub_le {e x₀ : E} (he : ‖e‖ = 1) {ρ a β : ℝ}
    (hρ : 0 < ρ) {g : E → ℝ} (hg : ContinuousAt g x₀) (hβ : β < a / 2) :
    ¬ ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |a * truncPow 0 (⟪e, x⟫ - ⟪e, x₀⟫) - g x| ≤ β := by
  intro h
  obtain ⟨η, hη, hgη⟩ := Metric.continuousAt_iff.1 hg ((a / 2 - β) / 2) (by linarith)
  -- Test the bound at points of `B(x₀, min η ρ)` on both sides of the hyperplane.
  have hη' : 0 < min η ρ := lt_min hη hρ
  have h' := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (min_le_right η ρ)) h
  have hhalf : |min η ρ / 2| < min η ρ := by
    rw [abs_of_pos (half_pos hη')]
    exact half_lt_self hη'
  obtain ⟨hp, hpc⟩ := add_smul_mem_ball_and_inner_eq he x₀ hhalf
  obtain ⟨hm, hmc⟩ := add_smul_mem_ball_and_inner_eq he x₀ (s := -(min η ρ / 2))
    (by rwa [abs_neg])
  obtain ⟨yp, hyp, ⟨hyps, -⟩, hypc⟩ := exists_mem_ball_inner_mem_Ioo_of_ae h' hp
    (s := ⟪e, x₀⟫) (t := ⟪e, x₀⟫ + min η ρ) (by rw [hpc]; constructor <;> linarith)
  obtain ⟨ym, hym, ⟨-, hyms⟩, hymc⟩ := exists_mem_ball_inner_mem_Ioo_of_ae h' hm
    (s := ⟪e, x₀⟫ - min η ρ) (t := ⟪e, x₀⟫) (by rw [hmc]; constructor <;> linarith)
  simp only [truncPow_of_pos (sub_pos.2 hyps), pow_zero, mul_one] at hypc
  simp only [truncPow_of_nonpos (sub_nonpos.2 hyms.le), mul_zero, zero_sub, abs_neg] at hymc
  have hgp := hgη (mem_ball.1 (ball_subset_ball (min_le_left η ρ) hyp))
  have hgm := hgη (mem_ball.1 (ball_subset_ball (min_le_left η ρ) hym))
  rw [Real.dist_eq] at hgp hgm
  have := abs_sub_lt_iff.1 hgp
  have := abs_sub_lt_iff.1 hgm
  have := abs_le.1 hypc
  have := abs_le.1 hymc
  linarith

/-! ### Nonseparability and failure of smooth density -/

variable [Nontrivial E]

/-- **`W^{k,∞}(Ω)` is not separable.** On every nonempty open subset `Ω` of a space of positive
dimension and at every order `k`, the Sobolev space `W^{k,∞}(Ω)` is not separable, unlike
`W^{k,p}(Ω)` for finite `p`. -/
theorem not_separableSpace_top (hΩ : (Omega : Set E).Nonempty) (k : ℕ) :
    ¬ SeparableSpace (Wkp mu Omega ∞ k) := by
  intro hsep
  obtain ⟨x₀, ρ, e, T, hρ, -, he, hv, -⟩ := exists_ball_clm_ae_eq (mu := mu) hΩ k
  choose v hv using hv
  set c := ⟪e, x₀⟫
  set δ := (k ! : ℝ) / (‖T‖ + 1)
  have hδ : 0 < δ := div_pos (mod_cast k.factorial_pos) (by positivity)
  -- Two members with nearby parameters differ by `k!` on a slab through the ball.
  have hfar {s t : ℝ} (hs : c - ρ < s) (hst : s < t) (ht : t < c + ρ) : δ ≤ dist (v s) (v t) := by
    obtain ⟨hy, hyc⟩ := add_smul_mem_ball_and_inner_eq he x₀ (s := (s + t) / 2 - c) (ρ := ρ)
      (by rw [abs_lt]; constructor <;> linarith)
    obtain ⟨x, -, ⟨hxs, hxt⟩, hTs, hTt, hle⟩ := exists_mem_ball_inner_mem_Ioo_of_ae
      ((hv s).and ((hv t).and (ae_dist_le_opNorm_mul_dist T (v s) (v t)))) hy (s := s) (t := t)
      (by rw [hyc]; constructor <;> linarith)
    simp only [hTs, hTt, truncPow_of_pos (sub_pos.2 hxs), truncPow_of_nonpos (sub_nonpos.2 hxt.le),
      pow_zero, mul_one, mul_zero, Real.dist_eq, sub_zero, Nat.abs_cast] at hle
    rw [div_le_iff₀ (by positivity)]
    nlinarith [dist_nonneg (x := v s) (y := v t)]
  -- So the open balls of radius `δ / 2` around the members are pairwise disjoint.
  have hdisj : Pairwise fun a b : Ioo (c - ρ) (c + ρ) =>
      Disjoint (ball (v a) (δ / 2)) (ball (v b) (δ / 2)) := by
    intro a b hab
    refine ball_disjoint_ball ?_
    rw [add_halves]
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hab) with h | h
    · exact hfar a.property.1 h b.property.2
    · rw [dist_comm]
      exact hfar b.property.1 h a.property.2
  have hcount := hdisj.countable_of_isOpen_disjoint (fun _ => isOpen_ball)
    fun a => ⟨v a, mem_ball_self (half_pos hδ)⟩
  have := Cardinal.Real.Ioo_countable_iff.1 (countable_coe_iff.1 hcount)
  linarith

/-- **Smooth functions are not dense in `W^{k,∞}(Ω)`.** On every nonempty open subset `Ω` of a
space of positive dimension and at every order `k`, the elements of `W^{k,∞}(Ω)` represented by a
function of class `Cᵏ` on `Ω` are not dense; in particular neither are those represented by a
function smooth on `Ω`, unlike for finite exponents
(`TauCeti.Wkp.dense_contDiffOn_representatives`). -/
theorem not_dense_contDiffOn_representatives_top (hΩ : (Omega : Set E).Nonempty) (k : ℕ) :
    ¬ Dense {u : Wkp mu Omega ∞ k | ∃ f : E → ℝ, ContDiffOn ℝ k f Omega ∧
      (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f} := by
  intro hd
  obtain ⟨x₀, ρ, e, T, hρ, hBΩ, he, hv, hTw⟩ := exists_ball_clm_ae_eq (mu := mu) hΩ k
  obtain ⟨v, hv⟩ := hv ⟪e, x₀⟫
  have hk : (0 : ℝ) < k ! := mod_cast k.factorial_pos
  set δ := (k ! : ℝ) / (2 * (‖T‖ + 1))
  obtain ⟨w, hwv, f, hf, hwf⟩ := Metric.dense_iff.1 hd v δ (div_pos hk (by positivity))
  -- `T w` is represented on the ball by the continuous function `x ↦ D^k f(x)(e, …, e)`.
  have hg : ContinuousAt (fun x => iteratedFDeriv ℝ k f x fun _ => e) x₀ :=
    ((continuous_eval_const _).comp_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin le_rfl Omega.isOpen.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen k Omega.isOpen).symm)).continuousAt
      (Omega.isOpen.mem_nhds (hBΩ (mem_ball_self hρ)))
  -- `T v` jumps by `k!` across the hyperplane through `x₀`, and `T w` stays within `‖T‖ δ` of it.
  have hβ : ‖T‖ * dist v w < k ! / 2 := by
    have hδ : 0 < δ := div_pos hk (by positivity)
    have h₁ : (‖T‖ + 1) * δ = k ! / 2 := by
      simp only [δ]
      field_simp
    have h₂ : ‖T‖ * dist v w ≤ ‖T‖ * δ :=
      mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact (mem_ball.1 hwv).le) (norm_nonneg T)
    linarith
  refine not_ae_abs_mul_truncPow_sub_le (mu := mu) he hρ hg hβ ?_
  filter_upwards [hv, hTw w hf hwf, ae_dist_le_opNorm_mul_dist T v w] with x h₁ h₂ h₃
  rwa [h₁, h₂, Real.dist_eq] at h₃

end TauCeti.Wkp
