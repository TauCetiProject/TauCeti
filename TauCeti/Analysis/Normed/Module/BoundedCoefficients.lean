/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# Finite sums with bounded coefficients

Let `v` be a family of vectors in a real or complex normed space such that every subsum
`∑ i ∈ u, v i` over a subset `u` of a finite set `s` has norm at most `S`. Then bounded
coefficients change the norm of `∑ i ∈ s, a i • v i` by a bounded factor:

* `TauCeti.norm_sum_ofReal_smul_le_of_nonneg`: real coefficients in `[0, t]` give `t * S`;
* `TauCeti.norm_sum_ofReal_smul_le_two_mul`: real coefficients of absolute value at most `t`
  give `2 * t * S`;
* `TauCeti.norm_sum_smul_le_four_mul`: scalar coefficients of norm at most `t` give `4 * t * S`.

Conversely, if every `±1`-signed combination `∑ i ∈ s, ε i • v i` has norm at most `S`, then any
subsum over `u ⊆ s` has norm at most `(‖∑ i ∈ s, v i‖ + S) / 2`
(`TauCeti.norm_sum_subset_le_of_forall_abs_eq_one`), real coefficients of absolute value at most
`t` give `t * S` without losing a factor of `2`
(`TauCeti.norm_sum_ofReal_smul_le_of_forall_abs_eq_one`), and scalar coefficients of norm at most
`t` give `2 * t * S` (`TauCeti.norm_sum_smul_le_two_mul_of_forall_abs_eq_one`). For a sequence
indexed by `ℕ`, a uniform bound `S` on `±1`-signed combinations along initial segments
`Finset.range N` gives the same bounds `t * S` and `2 * t * S` over arbitrary finite sets
(`TauCeti.norm_sum_ofReal_smul_le_of_forall_range_abs_eq_one` and
`TauCeti.norm_sum_smul_le_two_mul_of_forall_range_abs_eq_one`).

For a family `x` all of whose finite subsums have norm at most `C`, these estimates hold over
every finite set, with the following consequences:

* `TauCeti.sum_norm_apply_le_of_forall_norm_sum_le` and
  `TauCeti.summable_norm_apply_of_forall_norm_sum_le`: every continuous linear functional `f` is
  absolutely summable along `x`, with absolute sums at most `4 * C * ‖f‖`;
* `TauCeti.summable_smul_of_forall_norm_sum_le`: in a complete space, `∑ i, a i • x i` converges
  unconditionally for coefficients `a` tending to zero along the cofinite filter;
* `TauCeti.norm_tsum_smul_le_of_forall_norm_sum_le`: for coefficients of norm at most `M`, the
  sum `∑' i, a i • x i` has norm at most `4 * C * M`, also without completeness.

The first estimate peels off the smallest coefficient, which multiplies the full sum; the others
split coefficients into positive and negative parts, into signs and magnitudes, and into real and
imaginary parts (`TauCeti.norm_sum_smul_le_norm_sum_re_add_norm_sum_im`). These are the
estimates by which the coordinate projections and signed multipliers of an unconditional basis
control its bounded coordinate multipliers.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Section 3.1.
-/

public section

namespace TauCeti

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {v : ι → E} {s : Finset ι} {S t : ℝ}

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with real coefficients in `[0, t]` has norm at most `t * S`. -/
theorem norm_sum_ofReal_smul_le_of_nonneg (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → ℝ} (ha₀ : ∀ i ∈ s, 0 ≤ a i) (ha : ∀ i ∈ s, a i ≤ t) :
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ t * S := by
  classical
  induction s using Finset.strongInduction generalizing a t with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using mul_nonneg ht (by simpa using hS ∅ (Finset.empty_subset _))
  -- Peel off the smallest coefficient `a j`, which multiplies the full sum; the remaining
  -- coefficients lie in `[0, t - a j]` and are supported on `s.erase j`.
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image a hs
  have hsplit : ∑ i ∈ s, (a i : 𝕜) • v i =
      (a j : 𝕜) • ∑ i ∈ s, v i + ∑ i ∈ s.erase j, ((a i - a j : ℝ) : 𝕜) • v i := by
    rw [Finset.sum_erase _ (by simp), Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [RCLike.ofReal_sub, sub_smul, add_sub_cancel]
  have hrest := ih (s.erase j) (Finset.erase_ssubset hj)
    (fun u hu ↦ hS u (hu.trans (Finset.erase_subset _ _))) (sub_nonneg.2 (ha j hj))
    (fun i hi ↦ sub_nonneg.2 (hmin i (Finset.mem_of_mem_erase hi)))
    (fun i hi ↦ sub_le_sub_right (ha i (Finset.mem_of_mem_erase hi)) _)
  calc
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ a j * S + (t - a j) * S := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ hrest)
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (ha₀ j hj)]
      exact mul_le_mul_of_nonneg_left (hS s subset_rfl) (ha₀ j hj)
    _ = t * S := by ring

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with real coefficients of absolute value at most `t` has norm at most `2 * t * S`. -/
theorem norm_sum_ofReal_smul_le_two_mul (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → ℝ} (ha : ∀ i ∈ s, |a i| ≤ t) :
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ 2 * t * S := by
  -- Split each coefficient into its positive and negative parts, both in `[0, t]`.
  have hpos (i : ι) (hi : i ∈ s) : (a i)⁺ ≤ t :=
    (le_add_of_nonneg_right (negPart_nonneg (a i))).trans ((posPart_add_negPart _).trans_le
      (ha i hi))
  have hneg (i : ι) (hi : i ∈ s) : (a i)⁻ ≤ t :=
    (le_add_of_nonneg_left (posPart_nonneg (a i))).trans ((posPart_add_negPart _).trans_le
      (ha i hi))
  have hsplit : ∑ i ∈ s, (a i : 𝕜) • v i =
      ∑ i ∈ s, (((a i)⁺ : ℝ) : 𝕜) • v i - ∑ i ∈ s, (((a i)⁻ : ℝ) : 𝕜) • v i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← sub_smul, ← RCLike.ofReal_sub, posPart_sub_negPart]
  calc
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ t * S + t * S := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (add_le_add
        (norm_sum_ofReal_smul_le_of_nonneg hS ht (fun i _ ↦ posPart_nonneg _) hpos)
        (norm_sum_ofReal_smul_le_of_nonneg hS ht (fun i _ ↦ negPart_nonneg _) hneg))
    _ = 2 * t * S := by ring

/-- If every subsum of `v` over a subset of `s` has norm at most `S`, then a combination of the
`v i` with scalar coefficients of norm at most `t` has norm at most `4 * t * S`. -/
theorem norm_sum_smul_le_four_mul (hS : ∀ u ⊆ s, ‖∑ i ∈ u, v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → 𝕜} (ha : ∀ i ∈ s, ‖a i‖ ≤ t) :
    ‖∑ i ∈ s, a i • v i‖ ≤ 4 * t * S :=
  calc
    ‖∑ i ∈ s, a i • v i‖ ≤ 2 * t * S + 2 * t * S :=
      norm_sum_smul_le_norm_sum_re_add_norm_sum_im.trans (add_le_add
        (norm_sum_ofReal_smul_le_two_mul hS ht fun i hi ↦
          (RCLike.abs_re_le_norm _).trans (ha i hi))
        (norm_sum_ofReal_smul_le_two_mul hS ht fun i hi ↦
          (RCLike.abs_im_le_norm _).trans (ha i hi)))
    _ = 4 * t * S := by ring

/-- If every signed combination `∑ i ∈ s, ε i • v i` with `|ε i| = 1` has norm at most `S`, then
every combination of the `v i` over `s` with real coefficients of absolute value at most `t` has
norm at most `t * S`. -/
theorem norm_sum_ofReal_smul_le_of_forall_abs_eq_one
    (hS : ∀ ε : ι → ℝ, (∀ i, |ε i| = 1) → ‖∑ i ∈ s, (ε i : 𝕜) • v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → ℝ} (ha : ∀ i ∈ s, |a i| ≤ t) :
    ‖∑ i ∈ s, (a i : 𝕜) • v i‖ ≤ t * S := by
  classical
  -- Factor `a i = |a i| * σ i` with `σ i = ±1`; every subsum of `σ i • v i` over `u ⊆ s` is the
  -- midpoint of two full `±1`-combinations over `s`.
  let σ : ι → ℝ := fun i ↦ if 0 ≤ a i then 1 else -1
  have hσ (i : ι) : |σ i| = 1 := by
    dsimp only [σ]
    split_ifs <;> norm_num
  have haσ (i : ι) : a i = |a i| * σ i := by
    dsimp only [σ]
    rcases le_or_gt 0 (a i) with h | h
    · simp [h, abs_of_nonneg h]
    · simp [h.not_ge, abs_of_neg h]
  have hw : ∀ u ⊆ s, ‖∑ i ∈ u, (σ i : 𝕜) • v i‖ ≤ S := fun u hu ↦ by
    let ε₁ : ι → ℝ := fun i ↦ if i ∈ u then σ i else 1
    let ε₂ : ι → ℝ := fun i ↦ if i ∈ u then σ i else -1
    have hε₁ (i : ι) : |ε₁ i| = 1 := by dsimp only [ε₁]; split_ifs <;> simp [hσ]
    have hε₂ (i : ι) : |ε₂ i| = 1 := by dsimp only [ε₂]; split_ifs <;> simp [hσ]
    have hmid : ∑ i ∈ u, (σ i : 𝕜) • v i =
        (2 : 𝕜)⁻¹ • (∑ i ∈ s, (ε₁ i : 𝕜) • v i + ∑ i ∈ s, (ε₂ i : 𝕜) • v i) := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_subset hu]
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        simp only [ε₁, ε₂, hi, ↓reduceIte]
        rw [smul_add, ← add_smul]
        norm_num
      · intro i _ hiu
        simp [ε₁, ε₂, hiu]
    rw [hmid]
    exact norm_two_inv_smul_add_le (hS ε₁ hε₁) (hS ε₂ hε₂)
  have heq : ∑ i ∈ s, (a i : 𝕜) • v i = ∑ i ∈ s, ((|a i| : ℝ) : 𝕜) • (σ i : 𝕜) • v i :=
    Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul, ← RCLike.ofReal_mul, ← haσ]
  rw [heq]
  exact norm_sum_ofReal_smul_le_of_nonneg hw ht (fun i _ ↦ abs_nonneg _) ha

/-- If every signed combination `∑ i ∈ s, ε i • v i` with `|ε i| = 1` has norm at most `S`, then
every combination of the `v i` over `s` with scalar coefficients of norm at most `t` has norm at
most `2 * t * S`. -/
theorem norm_sum_smul_le_two_mul_of_forall_abs_eq_one
    (hS : ∀ ε : ι → ℝ, (∀ i, |ε i| = 1) → ‖∑ i ∈ s, (ε i : 𝕜) • v i‖ ≤ S) (ht : 0 ≤ t)
    {a : ι → 𝕜} (ha : ∀ i ∈ s, ‖a i‖ ≤ t) :
    ‖∑ i ∈ s, a i • v i‖ ≤ 2 * t * S :=
  calc
    ‖∑ i ∈ s, a i • v i‖ ≤ t * S + t * S :=
      norm_sum_smul_le_norm_sum_re_add_norm_sum_im.trans (add_le_add
        (norm_sum_ofReal_smul_le_of_forall_abs_eq_one hS ht fun i hi ↦
          (RCLike.abs_re_le_norm _).trans (ha i hi))
        (norm_sum_ofReal_smul_le_of_forall_abs_eq_one hS ht fun i hi ↦
          (RCLike.abs_im_le_norm _).trans (ha i hi)))
    _ = 2 * t * S := by ring

/-- If every `±1`-signed combination `∑ i ∈ s, ε i • v i` with `|ε i| = 1` has norm at most `S`,
then any subsum over `u ⊆ s` has norm at most `(‖∑ i ∈ s, v i‖ + S) / 2`. -/
theorem norm_sum_subset_le_of_forall_abs_eq_one {u : Finset ι} (hu : u ⊆ s)
    (hS : ∀ ε : ι → ℝ, (∀ i, |ε i| = 1) → ‖∑ i ∈ s, (ε i : 𝕜) • v i‖ ≤ S) :
    ‖∑ i ∈ u, v i‖ ≤ (‖∑ i ∈ s, v i‖ + S) / 2 := by
  classical
  -- Averaging the full sum and the signed combination `+1` on `u`, `-1` on `s \ u` isolates `u`.
  let ε : ι → ℝ := fun i ↦ if i ∈ u then 1 else -1
  have hε (i : ι) : |ε i| = 1 := by dsimp only [ε]; split_ifs <;> norm_num
  have h2 : ∑ i ∈ s, v i + ∑ i ∈ s, (ε i : 𝕜) • v i = (2 : 𝕜) • ∑ i ∈ u, v i := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_subset hu fun i _ hi ↦ by simp [ε, hi]]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp [ε, hi, ← one_add_one_eq_two, add_smul]
  have hnorm2 : ‖(2 : 𝕜) • ∑ i ∈ u, v i‖ = 2 * ‖∑ i ∈ u, v i‖ := by
    rw [norm_smul, RCLike.norm_ofNat]
  have hle : 2 * ‖∑ i ∈ u, v i‖ ≤ ‖∑ i ∈ s, v i‖ + S := by
    calc 2 * ‖∑ i ∈ u, v i‖ = ‖∑ i ∈ s, v i + ∑ i ∈ s, (ε i : 𝕜) • v i‖ := by
          rw [h2, hnorm2]
      _ ≤ ‖∑ i ∈ s, v i‖ + ‖∑ i ∈ s, (ε i : 𝕜) • v i‖ := norm_add_le _ _
      _ ≤ ‖∑ i ∈ s, v i‖ + S := add_le_add_right (hS ε hε) _
  linarith

section InitialSegments

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {v : ℕ → E} {S t : ℝ}

/-- If every `±1`-signed combination of `v` along an initial segment `Finset.range N` has norm at
most `S`, then every combination of `v` over an arbitrary finite set `A` with real coefficients of
absolute value at most `t` has norm at most `t * S`. -/
theorem norm_sum_ofReal_smul_le_of_forall_range_abs_eq_one
    (hS : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • v n‖ ≤ S)
    (A : Finset ℕ) (ht : 0 ≤ t) {a : ℕ → ℝ} (ha : ∀ n ∈ A, |a n| ≤ t) :
    ‖∑ n ∈ A, (a n : 𝕜) • v n‖ ≤ t * S := by
  classical
  -- Embed `A` in `Finset.range (A.sup id).succ` and extend `a` by `0` outside `A`.
  let N := (A.sup id).succ
  let a' : ℕ → ℝ := fun n ↦ if n ∈ A then a n else 0
  have heq : ∑ n ∈ A, (a n : 𝕜) • v n = ∑ n ∈ Finset.range N, (a' n : 𝕜) • v n := by
    rw [← Finset.sum_subset (Finset.subset_range_sup_succ A)]
    · exact Finset.sum_congr rfl fun n hn ↦ by simp [a', hn]
    · intro n _ hn
      simp [a', hn]
  rw [heq]
  refine norm_sum_ofReal_smul_le_of_forall_abs_eq_one (hS N) ht fun n _ ↦ ?_
  dsimp only [a']
  split_ifs with hn
  · exact ha n hn
  · simpa using ht

/-- If every `±1`-signed combination of `v` along an initial segment `Finset.range N` has norm at
most `S`, then every combination of `v` over an arbitrary finite set `A` with scalar coefficients
of norm at most `t` has norm at most `2 * t * S`. -/
theorem norm_sum_smul_le_two_mul_of_forall_range_abs_eq_one
    (hS : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • v n‖ ≤ S)
    (A : Finset ℕ) (ht : 0 ≤ t) {a : ℕ → 𝕜} (ha : ∀ n ∈ A, ‖a n‖ ≤ t) :
    ‖∑ n ∈ A, a n • v n‖ ≤ 2 * t * S :=
  norm_sum_smul_le_two_mul_of_forall_abs_eq_one
    (fun ε hε ↦ by
      simpa using norm_sum_ofReal_smul_le_of_forall_range_abs_eq_one hS A zero_le_one
        fun n _ ↦ (hε n).le)
    ht ha

end InitialSegments

section FiniteSubsums

open Filter Topology

/-- If every finite subsum of a family `x` has norm at most `C`, then the values of a continuous
linear functional `f` along `x` have absolute sums at most `4 * C * ‖f‖`. -/
theorem sum_norm_apply_le_of_forall_norm_sum_le {x : ι → E} {C : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) (f : StrongDual 𝕜 E) (s : Finset ι) :
    ∑ i ∈ s, ‖f (x i)‖ ≤ 4 * C * ‖f‖ := by
  -- Rotate each value `f (x i)` onto the nonnegative real axis.
  choose c hc hfc using fun i ↦ RCLike.exists_norm_eq_mul_self (f (x i))
  calc ∑ i ∈ s, ‖f (x i)‖ = RCLike.re (f (∑ i ∈ s, c i • x i)) := by
        simp only [map_sum, map_smul, smul_eq_mul, ← hfc, RCLike.ofReal_re]
    _ ≤ ‖f (∑ i ∈ s, c i • x i)‖ := RCLike.re_le_norm _
    _ ≤ ‖f‖ * ‖∑ i ∈ s, c i • x i‖ := f.le_opNorm _
    _ ≤ ‖f‖ * (4 * 1 * C) := by
        gcongr
        exact norm_sum_smul_le_four_mul (fun u _ ↦ hx u) zero_le_one fun i _ ↦ (hc i).le
    _ = 4 * C * ‖f‖ := by ring

/-- A family with uniformly bounded finite subsums is absolutely summable against every continuous
linear functional. -/
theorem summable_norm_apply_of_forall_norm_sum_le {x : ι → E} {C : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) (f : StrongDual 𝕜 E) :
    Summable fun i ↦ ‖f (x i)‖ :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_apply_le_of_forall_norm_sum_le hx f)

/-- If the finite subsums of `x` are bounded, then the series `∑ i, a i • x i` with coefficients
tending to zero along the cofinite filter converges unconditionally in a complete space. -/
theorem summable_smul_of_forall_norm_sum_le [CompleteSpace E] {x : ι → E} {C : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) {a : ι → 𝕜} (ha : Tendsto a cofinite (𝓝 0)) :
    Summable fun i ↦ a i • x i := by
  classical
  have hC : 0 ≤ C := by simpa using hx ∅
  refine summable_iff_vanishing_norm.2 fun δ hδ ↦ ?_
  -- Only finitely many coefficients exceed `η`; the remaining terms have small sums.
  set η := δ / (4 * C + 1) with hη
  have hη0 : 0 < η := by positivity
  have hfin : {i | ¬‖a i‖ ≤ η}.Finite := eventually_cofinite.1 <|
    (tendsto_zero_iff_norm_tendsto_zero.1 ha).eventually (eventually_le_nhds hη0)
  refine ⟨hfin.toFinset, fun t ht ↦ ?_⟩
  have hat (i : ι) (hi : i ∈ t) : ‖a i‖ ≤ η :=
    not_not.1 fun h ↦ Finset.disjoint_left.1 ht hi (hfin.mem_toFinset.2 h)
  calc ‖∑ i ∈ t, a i • x i‖ ≤ 4 * η * C := norm_sum_smul_le_four_mul (fun u _ ↦ hx u) hη0.le hat
    _ = δ * (4 * C / (4 * C + 1)) := by rw [hη]; field_simp
    _ < δ * 1 := by gcongr; exact (div_lt_one (by positivity)).2 (lt_add_one _)
    _ = δ := mul_one δ

/-- If the finite subsums of `x` have norm at most `C` and the coefficients `a i` have norm at most
`M`, then `‖∑' i, a i • x i‖ ≤ 4 * C * M`. No completeness is needed, since a series that does not
converge has sum zero. -/
theorem norm_tsum_smul_le_of_forall_norm_sum_le {x : ι → E} {C M : ℝ}
    (hx : ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) {a : ι → 𝕜} (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) :
    ‖∑' i, a i • x i‖ ≤ 4 * C * M := by
  by_cases hs : Summable fun i ↦ a i • x i
  · exact le_of_tendsto' hs.hasSum.norm fun s ↦
      (norm_sum_smul_le_four_mul (fun u _ ↦ hx u) hM fun i _ ↦ ha i).trans_eq (by ring)
  · have hC : 0 ≤ C := by simpa using hx ∅
    rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    positivity

end FiniteSubsums

end TauCeti
