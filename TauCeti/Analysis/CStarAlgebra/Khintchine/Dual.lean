/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.SquareFunction
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Analysis.CStarAlgebra.Matrix.HermitianDilation
import TauCeti.Analysis.CStarAlgebra.RademacherSum

/-!
# Dual `L^∞` Rademacher factorization in C⋆-algebras

This file proves the dual `L^∞` Rademacher factorization in arbitrary non-unital C⋆-algebras
underlying the `p = 1` noncommutative Khintchine inequality with the explicit Haagerup–Musat /
Pisier constant `√3`:

1. **Square-function Bessel bounds**: using the sign-cube orthogonality bounds from
   `TauCeti.Analysis.CStarAlgebra.RademacherSum`, Rademacher Fourier coefficients
   `y_k = rademacherCoeff ℝ Φ k` satisfy `max ‖columnSquare y‖ ‖rowSquare y‖ ≤ sup_ε ‖Φ(ε)‖`.
2. **Iterative truncation and `2 × 2` Hermitian dilation**: using the fourth-moment estimate
   `TauCeti.norm_card_inv_smul_sum_sum_units_smul_mul_self_mul_mul_self_le`, for self-adjoint `x`
   normalized by `‖∑_i x_i^2‖ ≤ 1`, truncating `∑_i ε_i • x_i` at `√3 / 2` leaves a remainder `r`
   with `‖∑_i r_i^2‖ ≤ 1 / 4`, whose rescaled iterates form a geometric series; `2 × 2` Hermitian
   dilation then extends the factorization with constant `√3` to arbitrary `x : ι → A`.

## Main declarations

* `TauCeti.norm_columnSquare_rademacherCoeff_le`, `TauCeti.norm_rowSquare_rademacherCoeff_le`
* `TauCeti.exists_isSelfAdjoint_rademacherCoeff_eq_and_norm_le`,
  `TauCeti.exists_rademacherCoeff_eq_and_norm_le`

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, Theorem 2.11.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  Theorem 9.1.
-/

public section

noncomputable section

open Filter Topology
open scoped BigOperators ComplexStarModule

namespace TauCeti

/-! ### Square-function Bessel bounds on the sign cube -/

section Bessel

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- If `‖Φ ε‖ ≤ C` for all `ε`, then `‖columnSquare (rademacherCoeff ℝ Φ)‖ ≤ C`. -/
theorem norm_columnSquare_rademacherCoeff_le {Φ : (ι → ℤˣ) → A} {C : ℝ}
    (hΦ : ∀ ε, ‖Φ ε‖ ≤ C) : ‖columnSquare (rademacherCoeff ℝ Φ)‖ ≤ C := by
  rw [norm_columnSquare]
  simpa only [rademacherCoeff_apply, Real.sqrt_sq ((norm_nonneg (Φ 1)).trans (hΦ 1))] using
    Real.sqrt_le_sqrt (norm_sum_star_mul_le_of_norm_le hΦ)

/-- If `‖Φ ε‖ ≤ C` for all `ε`, then `‖rowSquare (rademacherCoeff ℝ Φ)‖ ≤ C`. -/
theorem norm_rowSquare_rademacherCoeff_le {Φ : (ι → ℤˣ) → A} {C : ℝ}
    (hΦ : ∀ ε, ‖Φ ε‖ ≤ C) : ‖rowSquare (rademacherCoeff ℝ Φ)‖ ≤ C := by
  rw [norm_rowSquare]
  simpa only [rademacherCoeff_apply, Real.sqrt_sq ((norm_nonneg (Φ 1)).trans (hΦ 1))] using
    Real.sqrt_le_sqrt (norm_sum_mul_star_le_of_norm_le hΦ)

end Bessel

/-! ### Functional-calculus truncation and dual Rademacher factorization -/

section Factorization

private theorem norm_apply_le_sqrt_norm_sum_mul_self {ι A : Type*} [Fintype ι]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) (i : ι) : ‖x i‖ ≤ √‖∑ k, x k * x k‖ :=
  (norm_apply_le_norm_columnSquare x i).trans_eq <| by
    rw [norm_columnSquare, Finset.sum_congr rfl fun k _ => by rw [(hx k).star_eq]]

private def pisierCutoff (t : ℝ) : ℝ := max (-(Real.sqrt 3 / 2)) (min (Real.sqrt 3 / 2) t)

private theorem continuous_pisierCutoff : Continuous pisierCutoff :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem pisierCutoff_zero : pisierCutoff 0 = 0 := by
  have h : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  simp [pisierCutoff, min_eq_right h, max_eq_right (neg_nonpos.mpr h)]

private theorem pisierCutoff_neg (t : ℝ) : pisierCutoff (-t) = -pisierCutoff t := by
  unfold pisierCutoff; simp only [min_def, max_def]; split_ifs <;> linarith [Real.sqrt_nonneg 3]

private theorem abs_pisierCutoff_le (t : ℝ) : |pisierCutoff t| ≤ Real.sqrt 3 / 2 :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [Real.sqrt_nonneg 3]) (min_le_left _ _)⟩

private theorem sub_pisierCutoff_sq_le (t : ℝ) :
    (t - pisierCutoff t) ^ 2 ≤ (1 / 12 : ℝ) * t ^ 4 := by
  wlog ht : 0 ≤ t generalizing t
  · have h := this (-t) (by linarith); rw [pisierCutoff_neg] at h; linarith [h]
  set c₀ : ℝ := Real.sqrt 3 / 2
  have hc₀ : 0 ≤ c₀ := by positivity
  have hc₀_sq : c₀ ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  rcases le_or_gt t c₀ with hle | hgt
  · have hcut : pisierCutoff t = t := by
      simp [pisierCutoff, c₀, min_eq_right hle, max_eq_right (by linarith : -c₀ ≤ t)]
    rw [hcut, sub_self, zero_pow two_ne_zero]; positivity
  · have hcut : pisierCutoff t = c₀ := by
      simp [pisierCutoff, c₀, min_eq_left hgt.le, max_eq_right (by linarith : -c₀ ≤ c₀)]
    rw [hcut]
    have hfac : 0 ≤ t ^ 2 + 4 * c₀ * t - 4 * c₀ ^ 2 := by nlinarith [sq_nonneg t]
    have hdiff : (1 / 12 : ℝ) * t ^ 4 - (t - c₀) ^ 2 =
        (1 / 12 : ℝ) * (t - 2 * c₀) ^ 2 * (t ^ 2 + 4 * c₀ * t - 4 * c₀ ^ 2) := by
      linear_combination (4 / 3) * (t - c₀) ^ 2 * hc₀_sq
    nlinarith [sq_nonneg (t - 2 * c₀)]

section TruncationStep

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

private def pisierTruncate (x : ι → A) (ε : ι → ℤˣ) : A := cfcₙ pisierCutoff (∑ i, ε i • x i)

private def pisierRemainder (x : ι → A) : ι → A :=
  x - rademacherCoeff ℝ (pisierTruncate x)

omit [DecidableEq ι] [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierTruncate (x : ι → A) (ε : ι → ℤˣ) :
    IsSelfAdjoint (pisierTruncate x ε) := cfcₙ_predicate pisierCutoff _

omit [DecidableEq ι] [PartialOrder A] [StarOrderedRing A] in
private theorem norm_pisierTruncate_le (x : ι → A) (ε : ι → ℤˣ) :
    ‖pisierTruncate x ε‖ ≤ Real.sqrt 3 / 2 :=
  norm_cfcₙ_le fun t _ => by simpa only [Real.norm_eq_abs] using abs_pisierCutoff_le t

omit [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierRemainder {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) (i : ι) :
    IsSelfAdjoint (pisierRemainder x i) := by
  rw [pisierRemainder, Pi.sub_apply]
  exact (hx i).sub (isSelfAdjoint_rademacherCoeff (isSelfAdjoint_pisierTruncate x) i)

omit [Fintype ι] [DecidableEq ι] in
private theorem sub_cfcₙ_pisierCutoff_sq_le {s : A} (hsa : IsSelfAdjoint s) :
    (s - cfcₙ pisierCutoff s) * (s - cfcₙ pisierCutoff s) ≤ (1 / 12 : ℝ) • (s * s * s * s) := by
  have hsub : ContinuousOn (fun t : ℝ => t - pisierCutoff t) (quasispectrum ℝ s) :=
    continuousOn_id.sub continuous_pisierCutoff.continuousOn
  have hsq : ContinuousOn (fun t : ℝ => t * t) (quasispectrum ℝ s) :=
    continuousOn_id.mul continuousOn_id
  have hS_id : cfcₙ (fun t : ℝ => t) s = s := cfcₙ_id' ℝ s hsa
  have hδ : cfcₙ (fun t : ℝ => t - pisierCutoff t) s = s - cfcₙ pisierCutoff s := by
    rw [cfcₙ_sub (fun t : ℝ => t) pisierCutoff s continuousOn_id rfl
      continuous_pisierCutoff.continuousOn pisierCutoff_zero, hS_id]
  have hδ2 : cfcₙ (fun t : ℝ => (t - pisierCutoff t) ^ 2) s =
      (s - cfcₙ pisierCutoff s) * (s - cfcₙ pisierCutoff s) := by
    rw [cfcₙ_congr fun t _ => sq (t - pisierCutoff t),
      cfcₙ_mul _ _ s hsub (by simp [pisierCutoff_zero]) hsub (by simp [pisierCutoff_zero]), hδ]
  have hS2 : cfcₙ (fun t : ℝ => t * t) s = s * s := by
    rw [cfcₙ_mul (fun t : ℝ => t) (fun t : ℝ => t) s continuousOn_id rfl continuousOn_id rfl, hS_id]
  have h4 : cfcₙ (fun t : ℝ => t ^ 4) s = s * s * s * s := by
    rw [cfcₙ_congr fun t _ => (by ring : t ^ 4 = (t * t) * (t * t)),
      cfcₙ_mul _ _ s hsq (mul_zero _) hsq (mul_zero _), hS2, ← mul_assoc]
  have hS4 : cfcₙ (fun t : ℝ => (1 / 12 : ℝ) * t ^ 4) s = (1 / 12 : ℝ) • (s * s * s * s) := by
    rw [cfcₙ_const_mul (1 / 12 : ℝ) _ s (continuous_pow 4).continuousOn (by simp), h4]
  rw [← hδ2, ← hS4]
  exact cfcₙ_mono (fun t _ => sub_pisierCutoff_sq_le t)
    ((continuous_id.sub continuous_pisierCutoff).pow 2).continuousOn
    (continuous_const.mul (continuous_pow 4)).continuousOn (by simp [pisierCutoff_zero]) (by simp)

private theorem norm_sum_pisierRemainder_sq_le {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) : ‖∑ i, pisierRemainder x i * pisierRemainder x i‖ ≤ 1 / 4 := by
  set c : ℝ := (Fintype.card (ι → ℤˣ) : ℝ)⁻¹
  set S : (ι → ℤˣ) → A := fun ε => ∑ i, ε i • x i
  set δ : (ι → ℤˣ) → A := S - pisierTruncate x
  have hS_sa (ε : ι → ℤˣ) : IsSelfAdjoint (S ε) := isSelfAdjoint_sum_units_smul hx ε
  have hrem_eq : pisierRemainder x = rademacherCoeff ℝ δ := by
    rw [pisierRemainder, map_sub, rademacherCoeff_sum_units_smul]
  have hbessel : ∑ i, pisierRemainder x i * pisierRemainder x i ≤ c • ∑ ε : ι → ℤˣ, δ ε * δ ε := by
    have hbes := sum_star_mul_le_card_inv_smul_sum_star_mul δ
    simp_rw [← rademacherCoeff_apply] at hbes
    refine (Finset.sum_congr rfl fun i _ => by
      rw [← hrem_eq, (isSelfAdjoint_pisierRemainder hx i).star_eq]).symm.trans_le <|
      hbes.trans_eq <| congrArg (c • ·) <|
        Finset.sum_congr rfl fun ε _ => by
          dsimp only [δ]
          rw [Pi.sub_apply, ((hS_sa ε).sub (isSelfAdjoint_pisierTruncate x ε)).star_eq]
  have hchain : ∑ i, pisierRemainder x i * pisierRemainder x i ≤
      (1 / 12 : ℝ) • (c • ∑ ε : ι → ℤˣ, S ε * S ε * (S ε * S ε)) := hbessel.trans <| by
    rw [smul_comm (1 / 12 : ℝ), Finset.smul_sum (r := (1 / 12 : ℝ))]
    refine smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun ε _ => ?_) (by positivity)
    dsimp only [δ]
    rw [Pi.sub_apply, ← mul_assoc]
    exact sub_cfcₙ_pisierCutoff_sq_le (hS_sa ε)
  calc _ ≤ ‖(1 / 12 : ℝ) • (c • ∑ ε : ι → ℤˣ, S ε * S ε * (S ε * S ε))‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hchain (Finset.sum_nonneg fun i _ => by
          simpa only [(isSelfAdjoint_pisierRemainder hx i).star_eq] using
            star_mul_self_nonneg (pisierRemainder x i))
    _ = (1 / 12 : ℝ) * ‖c • ∑ ε : ι → ℤˣ, S ε * S ε * (S ε * S ε)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    _ ≤ (1 / 12 : ℝ) * (3 * ‖∑ i, x i * x i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (norm_card_inv_smul_sum_sum_units_smul_mul_self_mul_mul_self_le hx) (by norm_num)
    _ ≤ (1 / 12 : ℝ) * (3 * 1 ^ 2) := by gcongr
    _ = 1 / 4 := by norm_num

private def pisierIter (x : ι → A) : ℕ → ι → A
  | 0 => x
  | m + 1 => (2 : ℝ) • pisierRemainder (pisierIter x m)

omit [PartialOrder A] [StarOrderedRing A] in
private theorem isSelfAdjoint_pisierIter {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ∀ m i, IsSelfAdjoint (pisierIter x m i)
  | 0, i => hx i
  | m + 1, i => by
    rw [pisierIter, Pi.smul_apply, IsSelfAdjoint, star_smul, star_trivial,
      (isSelfAdjoint_pisierRemainder (isSelfAdjoint_pisierIter hx m) i).star_eq]

private theorem norm_sum_pisierIter_sq_le_one {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) : ∀ m, ‖∑ i, pisierIter x m i * pisierIter x m i‖ ≤ 1
  | 0 => hnorm
  | m + 1 => by
    have hrem := norm_sum_pisierRemainder_sq_le (isSelfAdjoint_pisierIter hx m)
      (norm_sum_pisierIter_sq_le_one hx hnorm m)
    have hsum : ∑ i, pisierIter x (m + 1) i * pisierIter x (m + 1) i =
        (4 : ℝ) • ∑ i, pisierRemainder (pisierIter x m) i * pisierRemainder (pisierIter x m) i := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by
        rw [pisierIter, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_smul]; norm_num
    rw [hsum, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith

omit [PartialOrder A] [StarOrderedRing A] in
private theorem pisierIter_step (x : ι → A) (i : ι) (m : ℕ) :
    rademacherCoeff ℝ (((1 / 2 : ℝ) ^ m) • pisierTruncate (pisierIter x m)) i =
      ((1 / 2 : ℝ) ^ m) • pisierIter x m i -
        ((1 / 2 : ℝ) ^ (m + 1)) • pisierIter x (m + 1) i := by
  rw [map_smul, Pi.smul_apply]
  have hrec : rademacherCoeff ℝ (pisierTruncate (pisierIter x m)) i =
      pisierIter x m i - pisierRemainder (pisierIter x m) i := by
    rw [pisierRemainder, Pi.sub_apply, sub_sub_cancel]
  rw [hrec, smul_sub, pisierIter, Pi.smul_apply, smul_smul, pow_succ, mul_assoc]
  norm_num

private theorem tendsto_pisierIter_tail {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i))
    (hnorm : ‖∑ i, x i * x i‖ ≤ 1) (i : ι) :
    Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ N) • pisierIter x N i) atTop (𝓝 0) :=
  squeeze_zero_norm (fun N => by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) <|
      (norm_apply_le_sqrt_norm_sum_mul_self (isSelfAdjoint_pisierIter hx N) i).trans
        (Real.sqrt_le_one.mpr (norm_sum_pisierIter_sq_le_one hx hnorm N)))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (1 / 2 : ℝ) < 1))

private theorem exists_isSelfAdjoint_rademacherCoeff_eq_of_norm_le_one
    {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) (hnorm : ‖∑ i, x i * x i‖ ≤ 1) :
    ∃ Φ : (ι → ℤˣ) → A, (∀ ε, IsSelfAdjoint (Φ ε)) ∧
      rademacherCoeff ℝ Φ = x ∧ ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 := by
  -- Geometric truncation series with summand norm `≤ (1 / 2)^m * (√3 / 2)`.
  let g : ℕ → (ι → ℤˣ) → A := fun m => ((1 / 2 : ℝ) ^ m) • pisierTruncate (pisierIter x m)
  have hgeom : HasSum (fun m : ℕ => ((1 / 2 : ℝ) ^ m) * (Real.sqrt 3 / 2)) (Real.sqrt 3) := by
    simpa [mul_div_cancel₀ _ (two_ne_zero' ℝ)] using
      hasSum_geometric_two.mul_right (Real.sqrt 3 / 2)
  have hg_norm (m : ℕ) (ε : ι → ℤˣ) : ‖g m ε‖ ≤ ((1 / 2 : ℝ) ^ m) * (Real.sqrt 3 / 2) := by
    dsimp only [g]
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pisierTruncate_le _ ε) (by positivity)
  have hg_summ (ε : ι → ℤˣ) : Summable (fun m => g m ε) :=
    Summable.of_norm_bounded hgeom.summable fun m => hg_norm m ε
  refine ⟨fun ε => ∑' m, g m ε, fun ε => ?_, funext fun i => ?_,
    fun ε => tsum_of_norm_bounded hgeom fun m => hg_norm m ε⟩
  -- Self-adjointness passes through the convergent `tsum`.
  · exact ((hg_summ ε).hasSum.star.congr_fun fun m => by
      simp [g, Pi.smul_apply, (isSelfAdjoint_pisierTruncate _ ε).star_eq]).unique
      (hg_summ ε).hasSum
  -- Termwise Rademacher averaging telescopes to `x i - (1 / 2)^N • pisierIter x N i → x i`.
  · have hsum_hasSum : HasSum (fun m => ∑ ε : ι → ℤˣ, ε i • g m ε)
        (∑ ε : ι → ℤˣ, ε i • ∑' m, g m ε) := by
      simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
      exact hasSum_sum fun ε _ => (hg_summ ε).hasSum.const_smul ((ε i : ℤ) : ℝ)
    have hpart : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N,
        rademacherCoeff ℝ (g m) i) atTop (𝓝 (x i)) := by
      simp_rw [g, pisierIter_step,
        Finset.sum_range_sub' (fun m => ((1 / 2 : ℝ) ^ m) • pisierIter x m i)]
      simpa [pisierIter] using tendsto_const_nhds.sub (tendsto_pisierIter_tail hx hnorm i)
    rw [rademacherCoeff_apply]
    exact tendsto_nhds_unique (hsum_hasSum.const_smul _).tendsto_sum_nat
      (by simpa only [rademacherCoeff_apply] using hpart)

/-- **Dual Rademacher factorization for self-adjoint families**: for self-adjoint `x : ι → A`,
there exists self-adjoint `Φ` with `rademacherCoeff ℝ Φ = x` and
`‖Φ ε‖ ≤ √3 * √‖∑ i, x i * x i‖`. -/
theorem exists_isSelfAdjoint_rademacherCoeff_eq_and_norm_le
    {x : ι → A} (hx : ∀ i, IsSelfAdjoint (x i)) :
    ∃ Φ : (ι → ℤˣ) → A, (∀ ε, IsSelfAdjoint (Φ ε)) ∧
      rademacherCoeff ℝ Φ = x ∧ ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 * √‖∑ i, x i * x i‖ := by
  set s : ℝ := √‖∑ i, x i * x i‖
  by_cases hs : s = 0
  · refine ⟨0, fun _ => IsSelfAdjoint.zero _, ?_, fun _ => by simp [hs]⟩
    ext i
    simpa [map_zero] using
      (norm_le_zero_iff.mp ((norm_apply_le_sqrt_norm_sum_mul_self hx i).trans_eq hs)).symm
  · let y : ι → A := s⁻¹ • x
    have hscale : (∑ i, y i * y i) = (s⁻¹ ^ 2) • ∑ i, x i * x i := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp [y, Pi.smul_apply, sq, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hy_norm : ‖∑ i, y i * y i‖ ≤ 1 := by
      rw [hscale, norm_smul, Real.norm_of_nonneg (by positivity),
        ← Real.sq_sqrt (norm_nonneg (∑ i, x i * x i)), inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs)]
    obtain ⟨Ψ, hΨ_sa, hΨ_avg, hΨ_norm⟩ :=
      exists_isSelfAdjoint_rademacherCoeff_eq_of_norm_le_one
        (fun i => by simp [y, Pi.smul_apply, IsSelfAdjoint, (hx i).star_eq]) hy_norm
    refine ⟨s • Ψ, fun ε => by simp [Pi.smul_apply, IsSelfAdjoint, (hΨ_sa ε).star_eq], ?_,
      fun ε => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hΨ_norm ε) (Real.sqrt_nonneg _)⟩
    rw [map_smul, hΨ_avg]
    ext i
    rw [Pi.smul_apply]
    exact smul_inv_smul₀ hs (x i)

/-- **Dual Rademacher factorization in a non-unital C⋆-algebra** (Haagerup–Musat, Pisier): for any
`x : ι → A`, there exists `Φ` with `rademacherCoeff ℝ Φ = x` and
`‖Φ ε‖ ≤ √3 * max ‖columnSquare x‖ ‖rowSquare x‖`. -/
theorem exists_rademacherCoeff_eq_and_norm_le (x : ι → A) :
    ∃ Φ : (ι → ℤˣ) → A, rademacherCoeff ℝ Φ = x ∧
      ∀ ε, ‖Φ ε‖ ≤ Real.sqrt 3 * max ‖columnSquare x‖ ‖rowSquare x‖ := by
  let X : ι → CStarMatrix (Fin 2) (Fin 2) A := fun i => CStarMatrix.hermitianDilation (x i)
  have hX_sa (i : ι) : IsSelfAdjoint (X i) := CStarMatrix.isSelfAdjoint_hermitianDilation (x i)
  have hX_norm : √‖∑ i, X i * X i‖ = max ‖columnSquare x‖ ‖rowSquare x‖ := by
    rw [CStarMatrix.norm_sum_hermitianDilation_mul_hermitianDilation Finset.univ x x,
      Real.sqrt_monotone.map_max, max_comm, ← norm_columnSquare, ← norm_rowSquare]
  obtain ⟨Ψ, _, hΨ_avg, hΨ_norm⟩ := exists_isSelfAdjoint_rademacherCoeff_eq_and_norm_le hX_sa
  refine ⟨fun ε => Ψ ε 0 1, funext fun i => ?_, fun ε =>
    CStarMatrix.norm_entry_le_norm.trans ((hΨ_norm ε).trans_eq (by rw [hX_norm]))⟩
  have h := congrArg (CStarMatrix.entryLinearMap ℝ A (0 : Fin 2) 1) (congrFun hΨ_avg i)
  rw [map_rademacherCoeff] at h
  simpa [X] using h

end TruncationStep

end Factorization

end TauCeti
