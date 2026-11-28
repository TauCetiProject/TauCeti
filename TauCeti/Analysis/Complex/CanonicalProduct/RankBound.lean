/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct

/-!
# Rank bounds of subsets of the complex plane

A set `Λ ⊆ ℂ` has *rank bound* `p` (`Set.HasRankBound Λ p`) when the series
`∑ λ ∈ Λ \ {0}, ‖λ‖ ^ -(p + 1)` converges. This is the convergence condition under which the
canonical product of genus `p` over `Λ` converges to an entire function with simple zeros
exactly at `Λ`. The series runs over the subtype of nonzero points, so the origin is excluded
and a set carries no enumeration multiplicities. A set has finite rank when it has some rank
bound, and its rank is the least one.

## Main results

* `Set.HasRankBound.subset`, `Set.HasRankBound.mono_exponent`: rank bounds pass to subsets and
  to larger exponents.
* `Set.HasRankBound.countable`: a rank-bounded set is countable.
* `Set.HasRankBound.finite_inter_closedBall`: a rank-bounded set has finitely many points in each
  closed disk about the origin.
* `Set.hasRankBound_range_iff`: for an injective family, the rank bound is summability of the
  family's inverse powers, the origin contributing the junk value `0⁻¹ = 0`.
* `Set.hasRankBound_range_intCast_iff`: the integers have rank bound `p` exactly when `0 < p`, so
  their rank is `1`.

## References

* R. Beuzart-Plessis, Y. Liu, W. Zhang, X. Zhu, *Isolation of cuspidal spectrum, with application
  to the Gan–Gross–Prasad conjecture*, Ann. of Math. (2) **194** (2021), §2.1, Definition 2.1.
-/

public section

open Filter Metric

namespace Set

/-- A set `Λ ⊆ ℂ` has rank bound `p` when the inverse `(p + 1)`-st powers of the norms of its
nonzero points are summable. -/
def HasRankBound (Λ : Set ℂ) (p : ℕ) : Prop :=
  Summable fun w : ↥(Λ \ {0}) ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹

variable {Λ Λ' : Set ℂ} {p q : ℕ}

/-- The defining summability condition of a rank bound. -/
theorem hasRankBound_def :
    Λ.HasRankBound p ↔ Summable fun w : ↥(Λ \ {0}) ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹ :=
  Iff.rfl

/-- The rank bound as summability over all of `Λ`: the origin contributes the junk value
`0⁻¹ = 0`. -/
theorem hasRankBound_iff_summable :
    Λ.HasRankBound p ↔ Summable fun w : Λ ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹ := by
  refine (inclusion_injective (sdiff_subset (s := Λ) (t := {0}))).summable_iff
    (f := fun w : Λ ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹) fun w hw ↦ ?_
  have hw0 : (w : ℂ) = 0 := by
    by_contra h
    exact hw ⟨⟨w, w.property, h⟩, rfl⟩
  simp [hw0]

/-- For an injective family, the rank bound of its range is summability of the family's inverse
powers. -/
theorem hasRankBound_range_iff {ι : Type*} {a : ι → ℂ} (ha : Function.Injective a) :
    (range a).HasRankBound p ↔ Summable fun i ↦ (‖a i‖ ^ (p + 1))⁻¹ := by
  rw [hasRankBound_iff_summable]
  exact ((Equiv.ofInjective a ha).summable_iff
    (f := fun w : range a ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹)).symm

/-- A rank bound gives summability of `(R / ‖w‖) ^ (p + 1)` over the nonzero points `w` for
every real `R`, the convergence hypothesis of the genus-`p` primary product. -/
theorem HasRankBound.summable_div_pow (h : Λ.HasRankBound p) (R : ℝ) :
    Summable fun w : ↥(Λ \ {0}) ↦ (R / ‖(w : ℂ)‖) ^ (p + 1) := by
  rw [hasRankBound_def] at h
  refine (h.mul_left (R ^ (p + 1))).congr fun w ↦ ?_
  rw [div_pow, div_eq_mul_inv]

/-- A rank bound passes to subsets. -/
theorem HasRankBound.subset (h : Λ.HasRankBound p) (hΛ : Λ' ⊆ Λ) : Λ'.HasRankBound p := by
  rw [hasRankBound_def] at h ⊢
  exact (h.comp_injective (inclusion_injective (sdiff_subset_sdiff_left (t := {0}) hΛ))).congr
    fun _ ↦ by rw [Function.comp_apply, coe_inclusion]

/-- A rank bound passes to every larger exponent: the finitely many points of norm below one do
not affect summability, and beyond them the summands decrease with the exponent. -/
theorem HasRankBound.mono_exponent (h : Λ.HasRankBound p) (hpq : p ≤ q) : Λ.HasRankBound q := by
  rw [hasRankBound_def] at h ⊢
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)] with w hw
  have h0 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.property.2
  have h1 : 1 ≤ ‖(w : ℂ)‖ := by
    by_contra! hlt
    have hpow : ‖(w : ℂ)‖ ^ (p + 1) < 1 := pow_lt_one₀ h0.le hlt (by omega)
    exact (one_lt_inv₀ (by positivity)).mpr hpow |>.not_gt hw
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))

/-- Every finite set has every rank bound. -/
theorem _root_.Set.Finite.hasRankBound (hΛ : Λ.Finite) : Λ.HasRankBound p :=
  have := (hΛ.sdiff (t := {0})).to_subtype
  .of_finite

/-- The empty set has every rank bound. -/
@[simp]
theorem hasRankBound_empty : (∅ : Set ℂ).HasRankBound p :=
  finite_empty.hasRankBound

/-- A rank-bounded set is countable: the summands are positive, so the nonzero points form the
countable support of a summable family. -/
theorem HasRankBound.countable (h : Λ.HasRankBound p) : Λ.Countable := by
  rw [hasRankBound_def] at h
  have hsupp : Function.support (fun w : ↥(Λ \ {0}) ↦ (‖(w : ℂ)‖ ^ (p + 1))⁻¹) = univ := by
    ext w
    simp [show (w : ℂ) ≠ 0 from w.property.2]
  have hdiff : (Λ \ {0}).Countable :=
    countable_coe_iff.mp (countable_univ_iff.mp (hsupp ▸ h.countable_support))
  exact (hdiff.union (countable_singleton 0)).mono
    (by rw [sdiff_union_self]; exact subset_union_left)

/-- A rank-bounded set has only finitely many points in each closed disk about the origin. -/
theorem HasRankBound.finite_inter_closedBall (h : Λ.HasRankBound p) (R : ℝ) :
    (Λ ∩ closedBall 0 R).Finite := by
  have hfin : {w : ↥(Λ \ {0}) | ¬R < ‖(w : ℂ)‖}.Finite :=
    (Complex.tendsto_norm_cofinite_atTop_of_summable_div_pow (p := fun _ ↦ p)
      (fun w ↦ w.property.2) fun R _ ↦ h.summable_div_pow R).eventually_gt_atTop R
  refine ((hfin.image Subtype.val).union (finite_singleton 0)).subset ?_
  rintro z ⟨hzΛ, hzR⟩
  by_cases hz : z = 0
  · exact Or.inr hz
  · exact Or.inl ⟨⟨z, hzΛ, hz⟩, not_lt.mpr (mem_closedBall_zero_iff.mp hzR), rfl⟩

/-- The integers have rank bound `p` exactly when `0 < p`: the harmonic series over `ℤ` diverges
and the series of inverse squares converges, so their rank is `1`. -/
theorem hasRankBound_range_intCast_iff :
    (range ((↑) : ℤ → ℂ)).HasRankBound p ↔ 0 < p := by
  rw [hasRankBound_range_iff Int.cast_injective]
  have hfun : (fun n : ℤ ↦ (‖(n : ℂ)‖ ^ (p + 1))⁻¹) = fun n : ℤ ↦ |1 / (n : ℝ) ^ (p + 1)| := by
    ext n
    simp [abs_inv, abs_pow, Complex.norm_intCast]
  rw [hfun, summable_abs_iff, Real.summable_one_div_int_pow]
  omega

end Set
