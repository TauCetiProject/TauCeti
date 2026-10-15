/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.NestedDiscPoint
public import TauCeti.RingTheory.Valuation.ValuativeRel.RankLeOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RankLeOne

/-!
# The rank of the points of the closed unit disc

Let `K` be a complete nontrivially normed nonarchimedean field and `X = Spa (K⟨T⟩, K⟨T⟩°)` the
closed unit disc. Wedhorn's Example 7.57 sorts the points of `X`, for algebraically closed `K`,
into five types, and the types differ in rank: the points of types (1) to (4) are valuations of
rank one, while those of type (5) have rank two. This file proves the part of that statement which
separates the types: the points of types (1) to (4) have rank at most one, and those of type (5)
do not. Rank at most one is `ValuativeRel.IsRankLeOne` for the valuative relation of the point,
that is, its value group embeds into the positive reals.

* The classical points `x_a` (type (1)), the points `η_{a,r}` (types (2) and (3)) and the points
  `η` of decreasing sequences of discs (type (4)) compare series as a valuation with values in
  `ℝ≥0` does, so they have rank at most one. None of this needs `K` algebraically closed, and the
  classical points are treated on the polydisc of any dimension.
* The points `η_{a,r⁺}` and `η_{a,r⁻}` (type (5)) do not have rank at most one when `r = ‖c‖` for
  some `c ∈ K`. Just above `r`, the value of `T - a` exceeds that of `c`, yet every power
  `(T - a)ⁿ` stays below `cⁿ d` for a constant `‖d‖ > 1`, because their Gauss norms `rⁿ` and
  `rⁿ ‖d‖` already compare strictly. Just below `r` the roles of `T - a` and `c` are exchanged.
  `ValuativeRel.not_isRankLeOne_of_forall_pow_vle` turns this into the failure of rank at most
  one.

For radii outside `|Kˣ|` the points `η_{a,r±}` need not differ from `η_{a,r}`, so the hypothesis
`r = ‖c‖` cannot be dropped from the second statement.

The points of rank at most one form a Hausdorff subspace of the polydisc, as they do in the adic
spectrum of every Tate ring (`TauCeti.ValuationSpectrum.t2Space_spa_isRankLeOne`). In the closed
unit disc this subspace contains the points of types (1) to (4) and none of type (5). Since the
five types exhaust the disc over an algebraically closed field (Wedhorn, Example 7.57), it is
the Berkovich disc there.

## Main results

* `TauCeti.ValuationSpectrum.isRankLeOne_classicalPoint`: the classical points of the closed
  polydisc have rank at most one.
* `TauCeti.ValuationSpectrum.isRankLeOne_discPoint`: the points `η_{a,r}` have rank at most one.
* `TauCeti.ValuationSpectrum.isRankLeOne_nestedDiscPoint`: the points of decreasing sequences of
  discs have rank at most one.
* `TauCeti.ValuationSpectrum.not_isRankLeOne_discPointAbove` and
  `TauCeti.ValuationSpectrum.not_isRankLeOne_discPointBelow`: for `r` the norm of an element of
  `K`, the points `η_{a,r⁺}` and `η_{a,r⁻}` do not have rank at most one.
* `TauCeti.ValuationSpectrum.t2Space_closedPolydisc_isRankLeOne`: the points of the closed
  polydisc of rank at most one form a Hausdorff subspace.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20, for the rank of
  the points of type (5).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight

/-! ### Points of rank at most one -/

section Classical

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] {k : ℕ}

/-- **The classical points have rank at most one**: the classical point at `a` compares `f` and
`g` by the norms of `f(a)` and `g(a)`. This holds on the polydisc of any dimension. -/
@[simp]
theorem isRankLeOne_classicalPoint (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    @ValuativeRel.IsRankLeOne _ _ (classicalPoint x a ha).1.toValuativeRel :=
  letI := (classicalPoint x a ha).1.toValuativeRel
  haveI : ((NormedField.valuation (K := K)).comap (evalAtHom a ha)).Compatible :=
    ⟨fun f g ↦ by
      simpa only [Valuation.comap_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe,
        coe_nnnorm] using (classicalPoint_vle x a ha f g).trans
          (vle_iff_norm_le_of_mem_spa x.2 _ _)⟩
  ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean
    ((NormedField.valuation (K := K)).comap (evalAtHom a ha))

end Classical

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K] {r : ℝ}

/-- **The points `η_{a,r}` have rank at most one**: they compare series by a Gauss norm, which
takes values in `ℝ≥0`. These are the points of types (2) and (3). -/
@[simp]
theorem isRankLeOne_discPoint (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    @ValuativeRel.IsRankLeOne _ _ (discPoint a ha hr₀ hr₁).1.toValuativeRel :=
  letI := (discPoint a ha hr₀ hr₁).1.toValuativeRel
  haveI : ((closedDiscGaussValuation hr₀ hr₁).comap
      (taylorHom (fun _ ↦ a) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha)).Compatible :=
    ⟨fun f g ↦ discPoint_vle_iff a ha hr₀ hr₁ f g⟩
  ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean
    ((closedDiscGaussValuation hr₀ hr₁).comap
      (taylorHom (fun _ ↦ a) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr ha))

/-- **The points of decreasing sequences of discs have rank at most one**: they compare series by
the infimum of the Gauss norms of the discs, which takes values in `ℝ≥0`. When `K` is
algebraically closed and the discs have no common point in `K`, these are the points of
type (4). -/
@[simp]
theorem isRankLeOne_nestedDiscPoint (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K)
    (hc₀ : ∀ n, c n ≠ 0) (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
    (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖) :
    @ValuativeRel.IsRankLeOne _ _ (nestedDiscPoint a ha c hc₀ hc₁ hac hcc).1.toValuativeRel :=
  letI := (nestedDiscPoint a ha c hc₀ hc₁ hac hcc).1.toValuativeRel
  haveI : (nestedDiscValuation a ha c hc₀ hc₁ hac hcc).Compatible :=
    ⟨nestedDiscPoint_vle_iff a ha c hc₀ hc₁ hac hcc⟩
  ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean
    (nestedDiscValuation a ha c hc₀ hc₁ hac hcc)

/-! ### The points of type (5) -/

/-- **The points `η_{a,r⁺}` do not have rank at most one** when `r` is the norm of an element `c`
of `K`. The value of `T - a` is larger than that of `c`, but every power `(T - a)ⁿ` is at most
`cⁿ d` for a constant `‖d‖ > 1`. For algebraically closed `K` these are points of type (5). -/
@[simp]
theorem not_isRankLeOne_discPointAbove (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1)
    (hr : ∃ c : K, ‖c‖ = r) :
    ¬ @ValuativeRel.IsRankLeOne _ _ (discPointAbove a ha hr₀ hr₁).1.toValuativeRel := by
  obtain ⟨c, hc⟩ := hr
  obtain ⟨d, hd⟩ := NormedField.exists_one_lt_norm K
  let := (discPointAbove a ha hr₀ hr₁).1.toValuativeRel
  refine ValuativeRel.not_isRankLeOne_of_forall_pow_vle (f := T - C a) (g := C c) (h := C d)
    (ValuativeRel.not_vle.mp ?_) fun n ↦ ?_
  · -- translation by `a` sends `T - a` to `T`, which lies strictly above `c` just above `r`
    rw [discPointAbove_vle_iff]
    simpa only [map_sub, taylorHom_weightedX, taylorHom_weightedC, add_sub_cancel_right,
      closedDiscGaussValuationAbove_weightedX_le_iff, not_lt] using hc.le
  · -- the Gauss norms of `Tⁿ` and `cⁿ d` are `rⁿ < rⁿ ‖d‖`
    have hlt := closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le
      ((closedDiscGaussValuation_weightedX_pow hr₀ hr₁.le hc n).trans_lt
        (closedDiscGaussValuation_lt_mul_weightedC hr₀ hr₁.le hd
          (closedDiscGaussValuation_weightedC_pow_pos hr₀ hr₁.le hc n)))
    rw [discPointAbove_vle_iff]
    simpa only [map_pow, map_mul, map_sub, taylorHom_weightedX, taylorHom_weightedC,
      add_sub_cancel_right] using hlt.le

/-- **The points `η_{a,r⁻}` do not have rank at most one** when `r` is the norm of an element `c`
of `K`. The value of `c` is larger than that of `T - a`, but every power `cⁿ` is at most
`(T - a)ⁿ d` for a constant `‖d‖ > 1`. For algebraically closed `K` these are points of
type (5). -/
@[simp]
theorem not_isRankLeOne_discPointBelow (a : K) (ha : ‖a‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (hr : ∃ c : K, ‖c‖ = r) :
    ¬ @ValuativeRel.IsRankLeOne _ _ (discPointBelow a ha hr₀ hr₁).1.toValuativeRel := by
  obtain ⟨c, hc⟩ := hr
  obtain ⟨d, hd⟩ := NormedField.exists_one_lt_norm K
  let := (discPointBelow a ha hr₀ hr₁).1.toValuativeRel
  refine ValuativeRel.not_isRankLeOne_of_forall_pow_vle (f := C c) (g := T - C a) (h := C d)
    (ValuativeRel.not_vle.mp ?_) fun n ↦ ?_
  · -- translation by `a` sends `T - a` to `T`, which lies strictly below `c` just below `r`
    rw [discPointBelow_vle_iff]
    simpa only [map_sub, taylorHom_weightedX, taylorHom_weightedC, add_sub_cancel_right,
      closedDiscGaussValuationBelow_weightedC_le_iff, not_lt] using hc.ge
  · -- the Gauss norms of `cⁿ` and `Tⁿ d` are `rⁿ < rⁿ ‖d‖`
    have hpos := closedDiscGaussValuation_weightedC_pow_pos hr₀ hr₁ hc n
    rw [← closedDiscGaussValuation_weightedX_pow hr₀ hr₁ hc n] at hpos
    have hlt := closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁
      ((closedDiscGaussValuation_weightedX_pow hr₀ hr₁ hc n).symm.trans_lt
        (closedDiscGaussValuation_lt_mul_weightedC hr₀ hr₁ hd hpos))
    rw [discPointBelow_vle_iff]
    simpa only [map_pow, map_mul, map_sub, taylorHom_weightedX, taylorHom_weightedC,
      add_sub_cancel_right] using hlt.le

/-! ### The points of rank at most one -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The points of the closed polydisc of rank at most one form a Hausdorff subspace.** In the
closed unit disc over an algebraically closed field these are the points of types (1) to (4), so
this subspace is the Berkovich disc, which Wedhorn's Example 7.57 notes is Hausdorff. -/
theorem t2Space_closedPolydisc_isRankLeOne (k : ℕ) :
    T2Space {x : closedPolydisc k K // @ValuativeRel.IsRankLeOne _ _ x.1.toValuativeRel} := by
  -- a constant `c` with `0 < ‖c‖ < 1` is a topologically nilpotent unit of `K⟨T₁, …, Tₖ⟩`
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K
  have hc := (IsPseudoUniformizer.of_norm_lt_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hc₀))
    hc₁).map (continuous_weightedC (isWeightFamily_one_weight (k := k)))
  rw [closedPolydisc_def]
  exact t2Space_spa_isRankLeOne hc _

end TauCeti.ValuationSpectrum
