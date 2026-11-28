/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Pair
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The adic spectrum of a normed field

For a normed field `K` with an ultrametric norm, every point `v` of `Spa (K, K°)` compares
elements of `K` exactly as the norm does: `v(x) ≤ v(y)` if and only if `‖x‖ ≤ ‖y‖`. The plus ring
`K°` is the closed unit ball, which gives one direction, and continuity of `v` gives the other,
since an element of norm less than one is topologically nilpotent.

This is how points of `Spa (K, K°)` enter computations on spaces over `K`: whenever a point of
an adic spectrum over `K` pulls back to `Spa (K, K°)`, as every point of the closed polydisc does
along the constant embedding, it compares constants by their norms.

For a nontrivially normed field `K` with a nonarchimedean topology and a ring of integral elements
`K⁺`, the point of `Spv K` given by a valuation subring `O` lies in `Spa (K, K⁺)` exactly when
`K⁺ ⊆ O ≠ K`. The trivial valuation is excluded because `K` has topologically nilpotent units,
and every other `O` containing `K⁺` gives a continuous valuation: an element of norm less than one
has `O`-valuation less than one, for otherwise the powers of its inverse would carry all of `K`
into `O`.

## Main results

* `TauCeti.ValuationSpectrum.vle_iff_norm_le_of_mem_spa`: every point of `Spa (K, K°)` compares
  elements of `K` by their norms.
* `TauCeti.ValuationSpectrum.ofValuation_valuation_mem_spa_iff`: the points of `Spa (K, K⁺)` are
  the valuation subrings `O` with `K⁺ ⊆ O ≠ K`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 and
  Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section Ultrametric

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Every point of `Spa (K, K°)` compares elements of `K` by their norms.** If `‖x‖ ≤ ‖y‖`
then `x / y` is power-bounded, so `v(x / y) ≤ 1`. If `‖y‖ < ‖x‖` then `y / x` is topologically
nilpotent, so `v(y / x) < 1` by continuity. -/
theorem vle_iff_norm_le_of_mem_spa {v : Spv K} (hv : v ∈ spa (powerBoundedSubring K))
    (x y : K) : v.toValuativeRel.vle x y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← valuation_le_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hlt
    have hx : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hlt)
    have hnil : IsTopologicallyNilpotent (y / x) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        rwa [norm_div, div_lt_one (norm_pos_iff.mpr hx)])
    have hlt' := ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hv).1
      ).lt_one_of_isTopologicallyNilpotent hnil
    have hvx : v.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rw [map_div₀, div_lt_one₀ (pos_iff_ne_zero.mpr hvx)] at hlt'
    exact hlt'.not_ge h
  · rcases eq_or_ne y 0 with rfl | hy
    · rw [norm_zero, norm_le_zero_iff] at h
      rw [h]
    have hxy : x / y ∈ powerBoundedSubring K := by
      rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg y)
    have hle := valuation_le_one_of_mem_spa hv hxy
    rwa [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hy))] at hle

end Ultrametric

section Nonarchimedean

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K] {Kplus : Subring K}

/-- An element of norm less than one is topologically nilpotent, so it lies in every ring of
integral elements. -/
private theorem mem_of_norm_lt_one (hK : IsRingOfIntegralElements Kplus) {a : K} (ha : ‖a‖ < 1) :
    a ∈ Kplus :=
  hK.mem_of_isTopologicallyNilpotent (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha)

/-- For a valuation subring `O ≠ K` containing a ring of integral elements, an element of norm
less than one has `O`-valuation less than one: were it a unit of `O`, the powers of its inverse
would carry every element of `K` into `O`. -/
private theorem valuation_lt_one_of_norm_lt_one (hK : IsRingOfIntegralElements Kplus)
    {O : ValuationSubring K} (hle : Kplus ≤ O.toSubring) (hO : O ≠ ⊤) {a : K} (ha : ‖a‖ < 1) :
    O.valuation a < 1 := by
  refine ((O.valuation_le_one_iff a).mpr (hle (mem_of_norm_lt_one hK ha))).lt_of_ne
    fun h1 ↦ hO (eq_top_iff.mpr fun y _ ↦ ?_)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at h1
  have hinv : a⁻¹ ∈ O := (O.valuation_le_one_iff _).mp (by rw [map_inv₀, h1, inv_one])
  -- some `y * aⁿ` has norm less than one, hence lies in `K⁺ ⊆ O`
  obtain ⟨n, hn⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).const_mul
    ‖y‖).eventually (gt_mem_nhds (by simp : ‖y‖ * 0 < 1))).exists
  have hyn : y * a ^ n ∈ O := hle (mem_of_norm_lt_one hK (by rwa [norm_mul, norm_pow]))
  have hy : y = y * a ^ n * a⁻¹ ^ n := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, mul_one]
  rw [hy]
  exact mul_mem hyn (pow_mem hinv n)

/-- **The points of `Spa(K, K⁺)` are the valuation subrings between `K⁺` and `K`.** For a ring
of integral elements `K⁺` of a nontrivially normed field `K` with a nonarchimedean topology, the
point of `Spv K` given by a valuation subring `O` lies in `Spa(K, K⁺)` exactly when `K⁺ ⊆ O` and
`O ≠ K`. -/
theorem ofValuation_valuation_mem_spa_iff (hK : IsRingOfIntegralElements Kplus)
    (O : ValuationSubring K) :
    ofValuation O.valuation ∈ spa Kplus ↔ Kplus ≤ O.toSubring ∧ O ≠ ⊤ := by
  simp only [mem_spa_iff, isContinuous_ofValuation_iff, vle_ofValuation, map_one,
    O.valuation_le_one_iff]
  refine ⟨fun ⟨hc, hle⟩ ↦ ⟨fun a ha ↦ hle a ha, ?_⟩, fun ⟨hle, hO⟩ ↦ ⟨?_, fun a ha ↦ hle ha⟩⟩
  · -- the trivial valuation of `K` is not continuous, as `K` has topologically nilpotent units
    rintro rfl
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
    have hlt :=
      hc.lt_one_of_isTopologicallyNilpotent (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)
    have hinv : (⊤ : ValuationSubring K).valuation c⁻¹ ≤ 1 :=
      ((⊤ : ValuationSubring K).valuation_le_one_iff _).mpr trivial
    have h1 := mul_lt_one_of_lt_of_le hlt hinv
    rw [← map_mul, mul_inv_cancel₀ (norm_pos_iff.mp hc0), map_one] at h1
    exact lt_irrefl _ h1
  · -- the open balls `{‖y - x‖ < ‖b‖}` witness continuity
    refine (Valuation.isContinuous_iff_forall_ne_zero _).mpr fun b hb ↦
      isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    have hb0 : b ≠ 0 := fun h ↦ hb (by simp [h])
    filter_upwards [Metric.ball_mem_nhds x (norm_pos_iff.mpr hb0)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : O.valuation ((y - x) / b) < 1 := valuation_lt_one_of_norm_lt_one hK hle hO
      (by rwa [norm_div, div_lt_one (norm_pos_iff.mpr hb0)])
    rw [map_div₀, div_lt_one₀ (pos_iff_ne_zero.mpr hb)] at h1
    calc O.valuation y = O.valuation ((y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (O.valuation (y - x)) (O.valuation x) := O.valuation.map_add _ _
      _ < O.valuation b := max_lt h1 hx

end Nonarchimedean

end TauCeti.ValuationSpectrum
