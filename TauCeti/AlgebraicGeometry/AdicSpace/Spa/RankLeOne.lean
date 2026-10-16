/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Basic

import Mathlib.GroupTheory.ArchimedeanDensely
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The points of rank at most one of `Spa(A, A⁺)` form a Hausdorff subspace

The adic spectrum `Spa(A, A⁺)` of a Tate ring `A` is rarely Hausdorff, because a point of rank one
can have points of higher rank in its closure: in the closed unit disc, the points of type (5) lie
in the closure of a point of type (2). Discarding the points of higher rank repairs this. The
points of rank at most one, those whose value group embeds into the positive reals, form a
Hausdorff subspace. In the closed unit disc over an algebraically closed field these are the points
of types (1) to (4) of Wedhorn's Example 7.57, which make up the Berkovich disc, and Wedhorn notes
there that this subspace is Hausdorff.

The separation uses a topologically nilpotent unit `π`, so that `0 < v(π) < 1` at every point `v`.
Let `x ≠ y` be points of rank at most one. Since their valuative relations differ, after swapping
`x` and `y` there are `f` and `g` with `x(f) ≤ x(g)` and `y(g) < y(f)`. As the value group of `y`
is archimedean, some power of the ratio `y(g) / y(f)` drops below `y(π)²`, so

```text
x(π fⁿ) ≤ x(gⁿ)    and    y(gⁿ) ≤ y(π² fⁿ)
```

for some `n`. These say that `x` and `y` lie in the basic opens `{v : v(π fⁿ) ≤ v(gⁿ) ≠ 0}` and
`{v : v(gⁿ) ≤ v(π² fⁿ) ≠ 0}`. At a point `v` of both, `v(π fⁿ) ≤ v(π² fⁿ) ≠ 0` forces `1 ≤ v(π)`,
so no point with `v(π) < 1` lies in both. If `x(g) = 0`, the first set does not contain `x`; then
`g` is replaced by a power `πᵏ` with `y(πᵏ) < y(f)`, which exists because `y` has rank at most
one. Only the point with the strict inequality uses its rank, but either point may be that one,
so both need rank at most one. This is necessary: the points of type (5) of the closed unit disc
cannot be separated from the point of type (2) in whose closure they lie.

## Main results

* `TauCeti.ValuationSpectrum.exists_isOpen_inter_subset_setOf_one_vle_of_ne`: two distinct
  points `x` and `y` of `Spv A` of rank at most one, with `0 < x(π), y(π) < 1`, have open
  neighbourhoods meeting only at points `v` with `1 ≤ v(π)`.
* `TauCeti.ValuationSpectrum.t2Space_spa_isRankLeOne`: if `A` has a topologically nilpotent unit,
  then the points of `Spa(A, A⁺)` of rank at most one form a Hausdorff subspace.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, Theorem 1.2.1, for the Hausdorff property
  of the Berkovich spectrum.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Separating along one comparison.** If `x(f) ≤ x(g) ≠ 0` and `y(g) < y(f)`, where `y` has
rank at most one, `0 < y(π)` and `x(π) ≤ 1`, then `x` and `y` have open neighbourhoods meeting
only at points `v` with `1 ≤ v(π)`. -/
private theorem exists_isOpen_of_le_of_ne_zero {π f g : A} {x y : Spv A}
    (hy : @ValuativeRel.IsRankLeOne A _ y.toValuativeRel) (hxπ : x.valuation π ≤ 1)
    (hyπ : y.valuation π ≠ 0) (hfg : x.valuation f ≤ x.valuation g) (hg : x.valuation g ≠ 0)
    (hgf : y.valuation g < y.valuation f) :
    ∃ U V : Set (Spv A), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      U ∩ V ⊆ {v | v.toValuativeRel.vle 1 π} := by
  let := y.toValuativeRel
  have hf : y.valuation f ≠ 0 := (zero_le.trans_lt hgf).ne'
  -- the value group of `y` is archimedean, so `(y(g) / y(f))ⁿ < y(π)²` for some `n`
  obtain ⟨n, hn⟩ := exists_pow_lt₀ ((div_lt_one₀ (zero_lt_iff.mpr hf)).mpr hgf)
    (Units.mk0 _ (pow_ne_zero 2 hyπ))
  rw [Units.val_mk0, div_pow, div_lt_iff₀ (pow_pos (zero_lt_iff.mpr hf) n)] at hn
  refine ⟨basicOpen (π * f ^ n) (g ^ n), basicOpen (g ^ n) (π ^ 2 * f ^ n), isOpen_basicOpen _ _,
    isOpen_basicOpen _ _, ?_, ?_, ?_⟩
  · rw [mem_basicOpen_iff_valuation, map_mul, map_pow, map_pow]
    exact ⟨(mul_le_of_le_one_left' hxπ).trans (pow_le_pow_left₀ zero_le hfg n), pow_ne_zero n hg⟩
  · rw [mem_basicOpen_iff_valuation, map_mul, map_pow, map_pow, map_pow]
    exact ⟨hn.le, mul_ne_zero (pow_ne_zero 2 hyπ) (pow_ne_zero n hf)⟩
  · rintro v ⟨hU, hV⟩
    rw [mem_basicOpen_iff_valuation] at hU hV
    -- `v(π fⁿ) ≤ v(gⁿ) ≤ v(π² fⁿ) = v(π fⁿ) v(π)` with `v(π fⁿ) ≠ 0`
    have hne : v.valuation (π * f ^ n) ≠ 0 := by
      rw [pow_two, mul_assoc, map_mul] at hV
      exact right_ne_zero_of_mul hV.2
    have hle : v.valuation (π * f ^ n) * 1 ≤ v.valuation (π * f ^ n) * v.valuation π := by
      rw [mul_one, ← map_mul, mul_comm _ π, ← mul_assoc, ← pow_two]
      exact hU.1.trans hV.1
    rw [Set.mem_ofPred_eq, ← valuation_le_iff, map_one]
    exact le_of_mul_le_mul_left hle (zero_lt_iff.mpr hne)

/-- **Separating along one comparison, in general.** If `x(f) ≤ x(g)` and `y(g) < y(f)`, where `y`
has rank at most one, `0 < x(π) ≤ 1` and `0 < y(π) < 1`, then `x` and `y` have open
neighbourhoods meeting only at points `v` with `1 ≤ v(π)`. When `x(g) = 0`, a power `πᵏ` with
`y(πᵏ) < y(f)` takes the place of `g`. -/
private theorem exists_isOpen_of_le_of_lt {π f g : A} {x y : Spv A}
    (hy : @ValuativeRel.IsRankLeOne A _ y.toValuativeRel) (hxπ₀ : x.valuation π ≠ 0)
    (hxπ : x.valuation π ≤ 1) (hyπ₀ : y.valuation π ≠ 0) (hyπ : y.valuation π < 1)
    (hfg : x.valuation f ≤ x.valuation g) (hgf : y.valuation g < y.valuation f) :
    ∃ U V : Set (Spv A), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      U ∩ V ⊆ {v | v.toValuativeRel.vle 1 π} := by
  rcases eq_or_ne (x.valuation g) 0 with hg | hg
  · let := y.toValuativeRel
    have hf : y.valuation f ≠ 0 := (zero_le.trans_lt hgf).ne'
    obtain ⟨k, hk⟩ := exists_pow_lt₀ hyπ (Units.mk0 _ hf)
    rw [Units.val_mk0] at hk
    refine exists_isOpen_of_le_of_ne_zero (g := π ^ (k + 1)) hy hxπ hyπ₀
      (hfg.trans (hg ▸ zero_le)) (by rw [map_pow]; exact pow_ne_zero _ hxπ₀) ?_
    rw [map_pow, pow_succ]
    exact (mul_le_of_le_one_right' hyπ.le).trans_lt hk
  · exact exists_isOpen_of_le_of_ne_zero hy hxπ hyπ₀ hfg hg hgf

/-- **Distinct points of rank at most one are separated off the locus `1 ≤ v(π)`.** If `x ≠ y` are
points of `Spv A` of rank at most one with `0 < x(π) < 1` and `0 < y(π) < 1`, then they have open
neighbourhoods `U` and `V` whose intersection contains only points `v` with `1 ≤ v(π)`. In
particular `U` and `V` are disjoint on any set of points at which `π` has value below `1`. -/
theorem exists_isOpen_inter_subset_setOf_one_vle_of_ne {π : A} {x y : Spv A} (hxy : x ≠ y)
    (hx : @ValuativeRel.IsRankLeOne A _ x.toValuativeRel)
    (hy : @ValuativeRel.IsRankLeOne A _ y.toValuativeRel)
    (hxπ₀ : ¬ x.toValuativeRel.vle π 0) (hxπ : x.toValuativeRel.vlt π 1)
    (hyπ₀ : ¬ y.toValuativeRel.vle π 0) (hyπ : y.toValuativeRel.vlt π 1) :
    ∃ U V : Set (Spv A), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      U ∩ V ⊆ {v | v.toValuativeRel.vle 1 π} := by
  rw [← valuation_le_iff, map_zero, le_zero_iff] at hxπ₀ hyπ₀
  rw [← valuation_lt_iff, map_one] at hxπ hyπ
  -- the two valuative relations differ at some pair `(f, g)`
  obtain ⟨f, g, hfg⟩ :
      ∃ f g : A, ¬ (x.valuation f ≤ x.valuation g ↔ y.valuation f ≤ y.valuation g) := by
    by_contra! h
    exact hxy (ext' fun f g ↦ by simpa only [valuation_le_iff] using h f g)
  by_cases hxfg : x.valuation f ≤ x.valuation g
  · exact exists_isOpen_of_le_of_lt hy hxπ₀ hxπ.le hyπ₀ hyπ hxfg
      (not_le.mp fun h ↦ hfg (iff_of_true hxfg h))
  · obtain ⟨V, U, hV, hU, hyV, hxU, hVU⟩ := exists_isOpen_of_le_of_lt hx hyπ₀ hyπ.le hxπ₀ hxπ
      (of_not_not fun h ↦ hfg (iff_of_false hxfg h)) (not_le.mp hxfg)
    exact ⟨U, V, hU, hV, hxU, hyV, Set.inter_comm U V ▸ hVU⟩

variable [TopologicalSpace A]

/-- **The points of `Spa(A, A⁺)` of rank at most one form a Hausdorff subspace** when `A` has a
topologically nilpotent unit, as every Tate ring does. For the closed unit disc over an
algebraically closed field this subspace is the Berkovich disc of Wedhorn's Example 7.57. -/
theorem t2Space_spa_isRankLeOne {π : A} (hπ : Huber.IsPseudoUniformizer π)
    (Aplus : Subring A) :
    T2Space {x : spa Aplus // @ValuativeRel.IsRankLeOne A _ x.1.toValuativeRel} := by
  -- at every point of `Spa(A, A⁺)`, `0 < v(π) < 1`
  have hπv (v : spa Aplus) : ¬ v.1.toValuativeRel.vle π 0 ∧ v.1.toValuativeRel.vlt π 1 := by
    have hcont := (isContinuous_def v.1).mp ((mem_spa_iff Aplus v.1).mp v.2).1
    rw [← valuation_le_iff, ← valuation_lt_iff, map_zero, map_one, le_zero_iff]
    exact ⟨(hπ.isUnit.map v.1.valuation).ne_zero,
      hcont.lt_one_of_isTopologicallyNilpotent hπ.isTopologicallyNilpotent⟩
  refine ⟨fun x y hxy ↦ ?_⟩
  have hne : x.1.1 ≠ y.1.1 := fun h ↦ hxy (Subtype.ext (Subtype.ext h))
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := exists_isOpen_inter_subset_setOf_one_vle_of_ne hne
    x.2 y.2 (hπv x.1).1 (hπv x.1).2 (hπv y.1).1 (hπv y.1).2
  have hc := (continuous_subtype_val (p := (· ∈ spa Aplus))).comp
    (continuous_subtype_val (p := fun x : spa Aplus ↦
      @ValuativeRel.IsRankLeOne A _ x.1.toValuativeRel))
  refine ⟨_, _, hU.preimage hc, hV.preimage hc, hxU, hyV,
    Set.disjoint_left.mpr fun z hzU hzV ↦ ?_⟩
  exact (hπv z.1).2 (hUV ⟨hzU, hzV⟩)

end TauCeti.ValuationSpectrum
