/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The closed unit disc with the smallest plus ring

Let `K` be a nontrivially normed nonarchimedean field and `A = K⟨T⟩`. Besides `A°`, the ring
`A` has a smallest ring of integral elements containing the constants `K°`: the integral closure
`A⁺` of `K° + A°°` (`TauCeti.ValuationSpectrum.closedDiscMinimalPlus`). This file shows, as stated
at the end of Wedhorn's Example 7.57, that `Spa(A, A⁺)` has exactly one point more than the closed
unit disc `Spa(A, A°)`: the rank-two point `x_{>1}`, the Gauss norm at a radius infinitesimally
larger than `1`.

The point `x_{>1}` is the valuation `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove` at
`r = 1`, which records the Gauss norm of `f` together with the last degree attaining it. It is
continuous and at most `1` on `K°` and on `A°°`, hence on `A⁺`, but it gives `T` a value larger
than `1`, so it is not a point of `Spa(A, A°)`.

Conversely let `v` be a point of `Spa(A, A⁺)` with `v(T) > 1`. Then `v(c Tᵏ) < 1` for every `k`
and every `‖c‖ < 1`, since `c Tᵏ` is topologically nilpotent, so `v(T)` is infinitesimally larger
than `1`, and `v` compares constants by their norms. On a polynomial whose coefficient of
largest norm last occurs in degree `s`, the monomial of degree `s` therefore dominates all others,
and approximating by polynomials shows the same for every element of `A`: `v(f) = v(aₛ) v(T)ˢ`
where `aₛ` is the last coefficient of `f` of maximal norm. These values compare as the pairs
`(‖aₛ‖, s)` compare lexicographically, which determines `v`; so `v = x_{>1}`. The points `v` with
`v(T) ≤ 1` are at most `1` on all of `A°`, again by polynomial approximation, so they lie in the
closed disc.

Topologically, `x_{>1}` is a specialization of the Gauss point `η_1`, because its valuation
refines the Gauss norm. The closed unit disc is the open subset `{v : v(T) ≤ 1}` of
`Spa(A, A⁺)`, so it is an open dense subspace and `x_{>1}` is a closed point. This is the
closed-disc case of the last assertion of Wedhorn's Example 7.58: `Spa(A, A⁺)` contains
`Spa(A, A°)` as an open dense subset.

Neither completeness nor algebraic closedness of `K` is needed, although Wedhorn assumes both.

## Main definitions

* `TauCeti.ValuationSpectrum.closedDiscMinimalPlus`: the smallest ring of integral elements of
  `K⟨T⟩` containing the constants of norm at most `1`.
* `TauCeti.ValuationSpectrum.gaussPointAboveOne`: the point `x_{>1}`.

## Main results

* `TauCeti.ValuationSpectrum.isRingOfIntegralElements_closedDiscMinimalPlus` and
  `TauCeti.ValuationSpectrum.closedDiscMinimalPlus_le`: it is the smallest ring of integral
  elements containing `K°`; it does not contain `T`
  (`TauCeti.ValuationSpectrum.weightedX_notMem_closedDiscMinimalPlus`).
* `TauCeti.ValuationSpectrum.mem_closedPolydisc_iff_weightedX_vle_one`: a point of
  `Spa(K⟨T⟩, K⟨T⟩⁺)` lies in the closed disc exactly when `v(T) ≤ 1`.
* `TauCeti.ValuationSpectrum.gaussPointAboveOne_mem_spa_closedDiscMinimalPlus` and
  `TauCeti.ValuationSpectrum.gaussPointAboveOne_notMem_closedPolydisc`.
* `TauCeti.ValuationSpectrum.spa_closedDiscMinimalPlus`:
  `Spa(K⟨T⟩, K⟨T⟩⁺) = Spa(K⟨T⟩, K⟨T⟩°) ∪ {x_{>1}}`.
* `TauCeti.ValuationSpectrum.gaussPoint_specializes_gaussPointAboveOne`: `x_{>1}` lies in the
  closure of the Gauss point `η_1`.
* `TauCeti.ValuationSpectrum.isOpenEmbedding_inclusion_closedPolydisc_spa_closedDiscMinimalPlus`
  and `TauCeti.ValuationSpectrum.denseRange_inclusion_closedPolydisc_spa_closedDiscMinimalPlus`:
  the closed unit disc is an open dense subspace of `Spa(K⟨T⟩, K⟨T⟩⁺)`.
* `TauCeti.ValuationSpectrum.isClosed_singleton_gaussPointAboveOne`: `x_{>1}` is a closed point of
  `Spa(K⟨T⟩, K⟨T⟩⁺)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.15 and Examples 7.57
  and 7.58.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-! ### The plus ring -/

variable (K) in
/-- **The smallest ring of integral elements of `K⟨T⟩` containing `K°`**: the integral closure of
`K° + K⟨T⟩°°` (Wedhorn, Remark 7.15 and Example 7.57). It lies in `K⟨T⟩°` but does not contain
`T` (`TauCeti.ValuationSpectrum.weightedX_notMem_closedDiscMinimalPlus`). -/
noncomputable def closedDiscMinimalPlus : Subring 𝒯 :=
  plusClosure (C '' Metric.closedBall 0 1)

/-- The defining equation of `closedDiscMinimalPlus`, whose body is not exposed. -/
theorem closedDiscMinimalPlus_def :
    closedDiscMinimalPlus K = plusClosure (C '' Metric.closedBall 0 1) :=
  (rfl)

/-- A constant of norm at most `1` lies in `closedDiscMinimalPlus K`. -/
theorem weightedC_mem_closedDiscMinimalPlus {c : K} (hc : ‖c‖ ≤ 1) :
    C c ∈ closedDiscMinimalPlus K :=
  subset_plusClosure _ ⟨c, mem_closedBall_zero_iff.mpr hc, rfl⟩

/-- **`closedDiscMinimalPlus K` is the smallest ring of integral elements containing `K°`.** -/
theorem closedDiscMinimalPlus_le {S : Subring 𝒯} (hS : IsRingOfIntegralElements S)
    (hC : ∀ c : K, ‖c‖ ≤ 1 → C c ∈ S) : closedDiscMinimalPlus K ≤ S :=
  have := hS.isIntegrallyClosedIn
  plusClosure_le hS.isOpen (by rintro _ ⟨c, hc, rfl⟩; exact hC c (mem_closedBall_zero_iff.mp hc))

/-- **The points of `Spa(K⟨T⟩, K⟨T⟩⁺)`** are the continuous valuations at most `1` on the
constants of norm at most `1`. -/
theorem mem_spa_closedDiscMinimalPlus_iff (v : Spv 𝒯) :
    v ∈ spa (closedDiscMinimalPlus K) ↔
      v.IsContinuous ∧ ∀ c : K, ‖c‖ ≤ 1 → v.toValuativeRel.vle (C c) 1 := by
  rw [closedDiscMinimalPlus_def, mem_spa_plusClosure_iff]
  simp

/-! ### Approximation by polynomials -/

/-- **Polynomial approximation at a continuous point**: every `f ∈ K⟨T⟩` is a polynomial up to an
error of value less than `v(b) ≠ 0` whose coefficients have norm less than `ε`. -/
private theorem exists_polynomial_approx {v : Spv 𝒯} (hv : v.IsContinuous) (f : 𝒯) {b : 𝒯}
    (hb : v.valuation b ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial K, v.valuation (f - Polynomial.eval₂ C T p) < v.valuation b ∧
      ∀ n : ℕ, ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) K) -
        p.coeff n‖ < ε := by
  have hnhds : {h : 𝒯 | v.valuation h < v.valuation b} ∈ nhds (0 : 𝒯) :=
    (Valuation.isContinuous_def.mp ((isContinuous_def v).mp hv) b).mem_nhds
      (by rw [Set.mem_ofPred_eq, map_zero]; exact zero_lt_iff.mpr hb)
  obtain ⟨U, -, hU⟩ :=
    (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_iff.mp hnhds
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (Metric.ball_mem_nhds (0 : K) hε)
  have hopen : IsOpen {g : 𝒯 | f - g ∈ weightedNhd _ isWeightFamily_one_weight
      (U ⊓ V).toAddSubgroup} :=
    (isOpen_weightedNhd isWeightFamily_one_weight (U ⊓ V).isOpen).preimage
      (continuous_const.sub continuous_id)
  obtain ⟨p, hp⟩ :=
    (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight).exists_mem_open hopen ⟨f, by simp⟩
  refine ⟨p, hU (weightedNhd_mono inf_le_left hp), fun n ↦ ?_⟩
  have h := mem_weightedNhd.mp hp (Finsupp.single 0 n)
  simp only [weightMul_one_weight, AddSubgroupClass.coe_sub, map_sub,
    Polynomial.coe_eval₂RingHom, coeff_eval₂_weightedC_weightedX] at h
  exact mem_ball_zero_iff.mp (hV (inf_le_right (a := U) h))

/-! ### Values of a point of `Spa(K⟨T⟩, K⟨T⟩⁺)` -/

variable [IsUltrametricDist K]

omit [NonarchimedeanRing K] in
/-- The ultrametric bound `‖b‖ ≤ max ‖a‖ ‖a - b‖`, used to compare the coefficients of a series
with those of an approximating polynomial. -/
private theorem norm_le_max_norm_sub (a b : K) : ‖b‖ ≤ max ‖a‖ ‖a - b‖ := by
  simpa [norm_sub_rev] using IsUltrametricDist.norm_add_le_max a (b - a)

/-- The leading coefficient `aₛ` of a series that is distinguished of degree `s` at the unit
radius is nonzero. -/
private theorem coeff_ne_zero_of_isDistinguished {f : 𝒯} {s : ℕ}
    (hs : TauCeti.PowerSeries.IsDistinguished 1 s
      (weightedRestrictedSubringOneEquiv f : PowerSeries K)) :
    MvPowerSeries.coeff (Finsupp.single 0 s) (f : MvPowerSeries (Fin 1) K) ≠ 0 :=
  coeff_weightedRestrictedSubringOneEquiv f s ▸ hs.coeff_ne_zero

/-- `closedDiscMinimalPlus K` is a ring of integral elements of `K⟨T⟩`. -/
theorem isRingOfIntegralElements_closedDiscMinimalPlus :
    IsRingOfIntegralElements (closedDiscMinimalPlus K) := by
  refine isRingOfIntegralElements_plusClosure ?_
  rintro _ ⟨c, hc, rfl⟩
  exact mem_powerBoundedSubring.mpr (isPowerBounded_weightedC _
    (isPowerBounded_iff_norm_le_one.mpr (mem_closedBall_zero_iff.mp hc)))

/-- The closed unit disc lies in `Spa(K⟨T⟩, K⟨T⟩⁺)`. -/
theorem closedPolydisc_subset_spa_closedDiscMinimalPlus :
    closedPolydisc 1 K ⊆ spa (closedDiscMinimalPlus K) := by
  rw [closedPolydisc_def]
  refine spa_antitone (closedDiscMinimalPlus_le ?_ fun c hc ↦ mem_powerBoundedSubring.mpr
    (isPowerBounded_weightedC _ (isPowerBounded_iff_norm_le_one.mpr hc)))
  simpa using (Pair.powerBounded 𝒯).isRingOfIntegralElements

/-- A point of `Spa(K⟨T⟩, K⟨T⟩⁺)` compares constants by their norms. -/
private theorem valuation_weightedC_le_iff {v : Spv 𝒯} (hv : v ∈ spa (closedDiscMinimalPlus K))
    (a b : K) : v.valuation (C a) ≤ v.valuation (C b) ↔ ‖a‖ ≤ ‖b‖ := by
  have h := comap_mem_spa (continuous_weightedC isWeightFamily_one_weight)
    (fun c hc ↦ weightedC_mem_closedDiscMinimalPlus
      (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp hc))) hv
  rw [valuation_le_iff, ← vle_iff_norm_le_of_mem_spa h, comap_vle]

private theorem valuation_weightedC_ne_zero {v : Spv 𝒯} (hv : v ∈ spa (closedDiscMinimalPlus K))
    {a : K} (ha : a ≠ 0) : v.valuation (C a) ≠ 0 := fun h ↦
  ha (norm_le_zero_iff.mp (by simpa using (valuation_weightedC_le_iff hv a 0).mp (by simp [h])))

/-- **`v(a) v(T)ᵏ < v(b)` whenever `‖a‖ < ‖b‖`**, at a point of `Spa(K⟨T⟩, K⟨T⟩⁺)`: with
`a = b c` and `‖c‖ < 1`, the monomial `c Tᵏ` is topologically nilpotent, so `v(c Tᵏ) < 1`. -/
private theorem valuation_weightedC_mul_pow_lt {v : Spv 𝒯}
    (hv : v ∈ spa (closedDiscMinimalPlus K)) {a b : K} (hb : b ≠ 0) (hab : ‖a‖ < ‖b‖) (k : ℕ) :
    v.valuation (C a) * v.valuation T ^ k < v.valuation (C b) := by
  have hc : ‖b⁻¹ * a‖ < 1 := by
    rwa [norm_mul, norm_inv, inv_mul_lt_one₀ (norm_pos_iff.mpr hb)]
  -- `c Tᵏ` is topologically nilpotent: `c` is, and `Tᵏ` is power-bounded
  have hnil : IsTopologicallyNilpotent (C (b⁻¹ * a) * T ^ k) := by
    rw [mul_comm]
    exact (mem_powerBoundedSubring.mp (pow_mem (mem_powerBoundedSubring.mpr
      (isPowerBounded_weightedX_one_weight 0)) k)).isTopologicallyNilpotent_mul
      (IsTopologicallyNilpotent.map (continuous_weightedC isWeightFamily_one_weight)
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc))
  have hlt := Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent
    ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hv).1) hnil
  rw [← mul_inv_cancel_left₀ hb a, map_mul, map_mul, mul_assoc, ← map_pow, ← map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.mpr (valuation_weightedC_ne_zero hv hb)) hlt

/-- At a point of `Spa(K⟨T⟩, K⟨T⟩⁺)` with `v(T) > 1`, the dominant monomial of a polynomial
determines its value: if `aₛ` is the last coefficient of `p` of maximal norm, then
`v(p) = v(aₛ) v(T)ˢ`. -/
private theorem valuation_eval₂_eq {v : Spv 𝒯} (hv : v ∈ spa (closedDiscMinimalPlus K))
    (hT : 1 < v.valuation T) {p : Polynomial K} {s : ℕ} (hs : p.coeff s ≠ 0)
    (hle : ∀ n, ‖p.coeff n‖ ≤ ‖p.coeff s‖) (hlt : ∀ n, s < n → ‖p.coeff n‖ < ‖p.coeff s‖) :
    v.valuation (Polynomial.eval₂ C T p) = v.valuation (C (p.coeff s)) * v.valuation T ^ s := by
  have hpos : 0 < v.valuation (C (p.coeff s)) := zero_lt_iff.mpr (valuation_weightedC_ne_zero hv hs)
  have hTpos : 0 < v.valuation T := zero_lt_one.trans hT
  have hmem : s ∈ Finset.range (p.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hs))
  rw [Polynomial.eval₂_eq_sum_range, ← Finset.add_sum_erase _ _ hmem,
    Valuation.map_add_eq_of_lt_left _ ?_, map_mul, map_pow]
  rw [map_mul, map_pow]
  refine Valuation.map_sum_lt _ (mul_pos hpos (pow_pos hTpos s)).ne' fun n hn ↦ ?_
  rw [map_mul, map_pow]
  rcases lt_or_gt_of_ne (Finset.mem_erase.mp hn).1 with h | h
  · -- a lower degree: `v(aₙ) ≤ v(aₛ)` and `v(T)ⁿ < v(T)ˢ`
    calc v.valuation (C (p.coeff n)) * v.valuation T ^ n
        ≤ v.valuation (C (p.coeff s)) * v.valuation T ^ n :=
          mul_le_mul_left ((valuation_weightedC_le_iff hv _ _).mpr (hle n)) _
      _ < v.valuation (C (p.coeff s)) * v.valuation T ^ s :=
          mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hT h) hpos
  · -- a higher degree: `v(aₙ) v(T)ⁿ⁻ˢ < v(aₛ)`
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [pow_add, mul_left_comm, mul_comm (v.valuation T ^ s)]
    exact mul_lt_mul_of_pos_right (valuation_weightedC_mul_pow_lt hv hs (hlt _ h) k)
      (pow_pos hTpos s)

/-- At a point of `Spa(K⟨T⟩, K⟨T⟩⁺)` with `v(T) > 1`, the dominant monomial of every series
determines its value: if `f` is distinguished of degree `s` at the unit radius, so that `aₛ` is
its last coefficient of maximal norm, then `v(f) = v(aₛ) v(T)ˢ`. -/
private theorem valuation_eq_of_isDistinguished {v : Spv 𝒯}
    (hv : v ∈ spa (closedDiscMinimalPlus K)) (hT : 1 < v.valuation T) {f : 𝒯} {s : ℕ}
    (hs : TauCeti.PowerSeries.IsDistinguished 1 s
      (weightedRestrictedSubringOneEquiv f : PowerSeries K)) :
    v.valuation f = v.valuation (C (MvPowerSeries.coeff (Finsupp.single 0 s)
      (f : MvPowerSeries (Fin 1) K))) * v.valuation T ^ s := by
  set a : ℕ → K := fun n ↦ MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) K)
  have hcoeff (n : ℕ) : PowerSeries.coeff n
      (weightedRestrictedSubringOneEquiv f : PowerSeries K) = a n :=
    coeff_weightedRestrictedSubringOneEquiv f n
  have has : a s ≠ 0 := coeff_ne_zero_of_isDistinguished hs
  have hle (n : ℕ) : ‖a n‖ ≤ ‖a s‖ := by
    simpa [hcoeff, ← hs.norm_coeff_mul_pow_eq] using
      PowerSeries.le_gaussNorm norm 1 _ hs.hasGaussNorm n
  have hlt (n : ℕ) (hn : s < n) : ‖a n‖ < ‖a s‖ := by
    simpa [hcoeff, ← hs.norm_coeff_mul_pow_eq] using hs.norm_coeff_mul_pow_lt n hn
  obtain ⟨p, hp, hpa⟩ := exists_polynomial_approx ((mem_spa_iff _ v).mp hv).1 f
    (valuation_weightedC_ne_zero hv has) (norm_pos_iff.mpr has)
  -- the coefficients of `p` are within `‖aₛ‖` of those of `f`, so `p` has the same dominant term
  have hpa' (n : ℕ) : ‖p.coeff n - a n‖ < ‖a s‖ := by rw [norm_sub_rev]; exact hpa n
  have hps : ‖p.coeff s‖ = ‖a s‖ := by
    rw [← add_sub_cancel (a s) (p.coeff s),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hpa' s).ne', max_eq_left (hpa' s).le]
  have hp0 : p.coeff s ≠ 0 := norm_ne_zero_iff.mp (hps ▸ norm_ne_zero_iff.mpr has)
  have hvp := valuation_eval₂_eq hv hT hp0
    (fun n ↦ hps ▸ (norm_le_max_norm_sub _ _).trans (max_le (hle n) (hpa n).le))
    fun n hn ↦ hps ▸ (norm_le_max_norm_sub _ _).trans_lt (max_lt (hlt n hn) (hpa n))
  have hC : v.valuation (C (p.coeff s)) = v.valuation (C (a s)) :=
    le_antisymm ((valuation_weightedC_le_iff hv _ _).mpr hps.le)
      ((valuation_weightedC_le_iff hv _ _).mpr hps.ge)
  rw [hC] at hvp
  have herr : v.valuation (f - Polynomial.eval₂ C T p) < v.valuation (Polynomial.eval₂ C T p) :=
    hvp ▸ hp.trans_le (le_mul_of_one_le_right' (one_le_pow₀ hT.le))
  calc v.valuation f = v.valuation (Polynomial.eval₂ C T p + (f - Polynomial.eval₂ C T p)) := by
        rw [add_sub_cancel]
    _ = v.valuation (Polynomial.eval₂ C T p) := Valuation.map_add_eq_of_lt_left _ herr
    _ = _ := hvp

/-- At a point of `Spa(K⟨T⟩, K⟨T⟩⁺)` with `v(T) > 1`, the values `v(a) v(T)ˢ` of nonzero
monomials compare as the pairs `(‖a‖, s)` compare lexicographically. -/
private theorem valuation_mul_pow_le_iff {v : Spv 𝒯} (hv : v ∈ spa (closedDiscMinimalPlus K))
    (hT : 1 < v.valuation T) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (s t : ℕ) :
    v.valuation (C a) * v.valuation T ^ s ≤ v.valuation (C b) * v.valuation T ^ t ↔
      ‖a‖ < ‖b‖ ∨ ‖a‖ = ‖b‖ ∧ s ≤ t := by
  have hTpos : 0 < v.valuation T := zero_lt_one.trans hT
  rcases le_or_gt s t with hst | hts
  · -- cancel `v(T)ˢ`: the comparison is `v(a) ≤ v(b) v(T)ᵏ`, which holds iff `‖a‖ ≤ ‖b‖`
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
    rw [pow_add, mul_left_comm, mul_comm (v.valuation T ^ s),
      mul_le_mul_iff_of_pos_right (pow_pos hTpos s)]
    simp only [le_add_iff_nonneg_right, zero_le, and_true, ← le_iff_lt_or_eq]
    refine ⟨fun h ↦ not_lt.mp fun hba ↦ h.not_gt (valuation_weightedC_mul_pow_lt hv ha hba k),
      fun h ↦ ((valuation_weightedC_le_iff hv a b).mpr h).trans
        (le_mul_of_one_le_right' (one_le_pow₀ hT.le))⟩
  · -- cancel `v(T)ᵗ`: the comparison is `v(a) v(T)ᵏ ≤ v(b)` with `k > 0`, which holds iff
    -- `‖a‖ < ‖b‖`
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hts.le
    rw [pow_add, mul_left_comm, mul_comm (v.valuation T ^ t),
      mul_le_mul_iff_of_pos_right (pow_pos hTpos t)]
    simp only [show ¬ t + k ≤ t by omega, and_false, or_false]
    refine ⟨fun h ↦ not_le.mp fun hba ↦ h.not_gt ?_,
      fun h ↦ (valuation_weightedC_mul_pow_lt hv hb h _).le⟩
    exact ((valuation_weightedC_le_iff hv b a).mpr hba).trans_lt
      (lt_mul_of_one_lt_right (zero_lt_iff.mpr (valuation_weightedC_ne_zero hv ha))
        (one_lt_pow₀ hT (by omega)))

/-- **Two points of `Spa(K⟨T⟩, K⟨T⟩⁺)` at which `T` has value larger than `1` are equal.** -/
private theorem eq_of_one_lt_valuation_weightedX {v w : Spv 𝒯}
    (hv : v ∈ spa (closedDiscMinimalPlus K)) (hw : w ∈ spa (closedDiscMinimalPlus K))
    (hvT : 1 < v.valuation T) (hwT : 1 < w.valuation T) : v = w := by
  have hdist {f : 𝒯} (hf : f ≠ 0) : ∃ s, TauCeti.PowerSeries.IsDistinguished 1 s
      (weightedRestrictedSubringOneEquiv f : PowerSeries K) :=
    TauCeti.PowerSeries.exists_isDistinguished one_pos (weightedRestrictedSubringOneEquiv f).2
      (by simpa using hf)
  have hne {u : Spv 𝒯} (hu : u ∈ spa (closedDiscMinimalPlus K)) (huT : 1 < u.valuation T)
      {f : 𝒯} (hf : f ≠ 0) : u.valuation f ≠ 0 := by
    obtain ⟨s, hs⟩ := hdist hf
    rw [valuation_eq_of_isDistinguished hu huT hs]
    exact mul_ne_zero (valuation_weightedC_ne_zero hu (coeff_ne_zero_of_isDistinguished hs))
      (pow_ne_zero _ (zero_lt_one.trans huT).ne')
  -- both points compare `f` and `g` through the dominant monomials of `f` and `g`
  refine ext' fun f g ↦ ?_
  rw [← valuation_le_iff, ← valuation_le_iff]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp [hne hv hvT hf, hne hw hwT hf]
  obtain ⟨s, hs⟩ := hdist hf
  obtain ⟨t, ht⟩ := hdist hg
  have has := coeff_ne_zero_of_isDistinguished hs
  have hat := coeff_ne_zero_of_isDistinguished ht
  rw [valuation_eq_of_isDistinguished hv hvT hs, valuation_eq_of_isDistinguished hv hvT ht,
    valuation_eq_of_isDistinguished hw hwT hs, valuation_eq_of_isDistinguished hw hwT ht,
    valuation_mul_pow_le_iff hv hvT has hat, valuation_mul_pow_le_iff hw hwT has hat]

/-- At a point of `Spa(K⟨T⟩, K⟨T⟩⁺)` with `v(T) ≤ 1`, every power-bounded element has value at
most `1`. -/
private theorem valuation_le_one_of_isPowerBounded {v : Spv 𝒯}
    (hv : v ∈ spa (closedDiscMinimalPlus K)) (hT : v.valuation T ≤ 1) {f : 𝒯}
    (hf : IsPowerBounded f) : v.valuation f ≤ 1 := by
  have hcoeff (n : ℕ) :
      ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) K)‖ ≤ 1 := by
    simpa using (norm_coeff_mul_pow_le_closedDiscGaussValuation one_pos le_rfl f n).trans
      (NNReal.coe_le_one.mpr (closedDiscGaussValuation_le_one_of_isPowerBounded one_pos le_rfl hf))
  -- `f` is a polynomial with coefficients in `K°` up to an error of value less than `1`
  obtain ⟨p, hp, hpa⟩ :=
    exists_polynomial_approx ((mem_spa_iff _ v).mp hv).1 f (b := 1) (by simp) one_pos
  rw [map_one] at hp
  rw [← add_sub_cancel (Polynomial.eval₂ C T p) f]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ hp.le)
  rw [Polynomial.eval₂_eq_sum_range]
  refine Valuation.map_sum_le _ fun n _ ↦ ?_
  rw [map_mul, map_pow]
  refine mul_le_one' (valuation_le_one_of_mem_spa hv (weightedC_mem_closedDiscMinimalPlus ?_))
    (pow_le_one' hT n)
  -- `p.coeff n` is within distance `1` of the coefficient `aₙ` of `f`, which has norm `≤ 1`
  exact (norm_le_max_norm_sub _ _).trans (max_le (hcoeff n) (hpa n).le)

/-! ### The closed disc and the point `x_{>1}` -/

/-- **A point of `Spa(K⟨T⟩, K⟨T⟩⁺)` lies in the closed unit disc exactly when `v(T) ≤ 1`.** -/
theorem mem_closedPolydisc_iff_weightedX_vle_one {v : Spv 𝒯}
    (hv : v ∈ spa (closedDiscMinimalPlus K)) :
    v ∈ closedPolydisc 1 K ↔ v.toValuativeRel.vle T 1 := by
  refine ⟨fun h ↦ ((mem_closedPolydisc_iff 1 K v).mp h).2 T
    (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0)), fun hT ↦
    (mem_closedPolydisc_iff 1 K v).mpr ⟨((mem_spa_iff _ v).mp hv).1, fun f hf ↦ ?_⟩⟩
  rw [← valuation_le_iff, map_one] at hT ⊢
  exact valuation_le_one_of_isPowerBounded hv hT (mem_powerBoundedSubring.mp hf)

variable (K) in
/-- **Wedhorn's point `x_{>1}`**: the Gauss norm at a radius infinitesimally larger than `1`,
`f ↦ (|f|₁, s)` where `s` is the last degree in which `f` attains its Gauss norm
(`TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove` at `r = 1`). It is a point of
`Spa(K⟨T⟩, K⟨T⟩⁺)` but not of the closed unit disc. -/
noncomputable def gaussPointAboveOne : Spv 𝒯 :=
  ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
    (closedDiscGaussValuationAbove (R := K) one_pos le_rfl)

/-- The defining equation of `gaussPointAboveOne`, whose body is not exposed. -/
theorem gaussPointAboveOne_def :
    gaussPointAboveOne K = ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
      (closedDiscGaussValuationAbove (R := K) one_pos le_rfl) :=
  (rfl)

/-- The point `x_{>1}` compares two series by their Gauss valuations just above `1`. -/
@[simp]
theorem gaussPointAboveOne_vle_iff (f g : 𝒯) :
    (gaussPointAboveOne K).toValuativeRel.vle f g ↔
      closedDiscGaussValuationAbove one_pos le_rfl f ≤
        closedDiscGaussValuationAbove one_pos le_rfl g :=
  vle_ofValuation _ f g

/-- `x_{>1}` is a point of `Spa(K⟨T⟩, K⟨T⟩⁺)`: it is continuous, and constants of norm at most `1`
have value at most `1`. -/
theorem gaussPointAboveOne_mem_spa_closedDiscMinimalPlus :
    gaussPointAboveOne K ∈ spa (closedDiscMinimalPlus K) := by
  refine (mem_spa_closedDiscMinimalPlus_iff _).mpr ⟨(isContinuous_ofValuation_iff _).mpr
    (isContinuous_closedDiscGaussValuationAbove one_pos le_rfl), fun c hc ↦ ?_⟩
  rw [gaussPointAboveOne_vle_iff, ← map_one C,
    closedDiscGaussValuationAbove_weightedC_le_weightedC_iff, norm_one]
  exact hc

/-- `x_{>1}` is not a point of the closed unit disc: it gives the power-bounded variable `T` a
value larger than `1`. -/
theorem gaussPointAboveOne_notMem_closedPolydisc : gaussPointAboveOne K ∉ closedPolydisc 1 K := by
  rw [mem_closedPolydisc_iff_weightedX_vle_one gaussPointAboveOne_mem_spa_closedDiscMinimalPlus,
    gaussPointAboveOne_vle_iff, ← map_one C]
  exact not_closedDiscGaussValuationAbove_weightedX_le one_pos le_rfl norm_one

/-- The variable `T` does not lie in `closedDiscMinimalPlus K`, which is therefore strictly
smaller than `K⟨T⟩°`: the point `x_{>1}` gives `T` a value larger than `1`. -/
theorem weightedX_notMem_closedDiscMinimalPlus : T ∉ closedDiscMinimalPlus K := fun h ↦
  gaussPointAboveOne_notMem_closedPolydisc <|
    (mem_closedPolydisc_iff_weightedX_vle_one gaussPointAboveOne_mem_spa_closedDiscMinimalPlus).mpr
      (((mem_spa_iff _ _).mp gaussPointAboveOne_mem_spa_closedDiscMinimalPlus).2 T h)

/-- **Wedhorn's Example 7.57**: the adic spectrum of `K⟨T⟩` with the smallest plus ring
containing `K°` is the closed unit disc together with the single point `x_{>1}`,

```text
Spa(K⟨T⟩, K⟨T⟩⁺) = Spa(K⟨T⟩, K⟨T⟩°) ∪ {x_{>1}}.
```
-/
theorem spa_closedDiscMinimalPlus :
    spa (closedDiscMinimalPlus K) = insert (gaussPointAboveOne K) (closedPolydisc 1 K) := by
  refine (Set.insert_subset gaussPointAboveOne_mem_spa_closedDiscMinimalPlus
    closedPolydisc_subset_spa_closedDiscMinimalPlus).antisymm' fun v hv ↦ ?_
  have hone {u : Spv 𝒯} (hu : u ∈ spa (closedDiscMinimalPlus K)) (hu' : u ∉ closedPolydisc 1 K) :
      1 < u.valuation T := by
    rw [mem_closedPolydisc_iff_weightedX_vle_one hu, ← valuation_le_iff, map_one, not_le] at hu'
    exact hu'
  by_cases h : v ∈ closedPolydisc 1 K
  · exact Or.inr h
  · exact Or.inl (eq_of_one_lt_valuation_weightedX hv
      gaussPointAboveOne_mem_spa_closedDiscMinimalPlus (hone hv h)
      (hone gaussPointAboveOne_mem_spa_closedDiscMinimalPlus
        gaussPointAboveOne_notMem_closedPolydisc))

/-! ### The closed disc as an open dense subspace -/

/-- **`x_{>1}` is a specialization of the Gauss point `η_1`**: it lies in the closure of `η_1` in
`Spv K⟨T⟩`, since its valuation refines the Gauss norm. -/
theorem gaussPoint_specializes_gaussPointAboveOne :
    (gaussPoint (K := K) one_pos le_rfl).1 ⤳ gaussPointAboveOne K :=
  gaussPoint_specializes_of_lt
    (fun _ _ h ↦ by
      rw [gaussPointAboveOne_vle_iff, not_le]
      exact closedDiscGaussValuationAbove_lt_of_lt one_pos le_rfl h)

/-- Inside `Spa(K⟨T⟩, K⟨T⟩⁺)`, the closed unit disc is the open subset `{v : v(T) ≤ 1}`. -/
theorem isOpen_closedPolydisc_spa_closedDiscMinimalPlus :
    IsOpen (((↑) : spa (closedDiscMinimalPlus K) → Spv 𝒯) ⁻¹' closedPolydisc 1 K) := by
  have h : ((↑) : spa (closedDiscMinimalPlus K) → Spv 𝒯) ⁻¹' closedPolydisc 1 K =
      ((↑) : spa (closedDiscMinimalPlus K) → Spv 𝒯) ⁻¹' basicOpen T 1 := by
    ext v
    simp [basicOpen_one_right, mem_closedPolydisc_iff_weightedX_vle_one v.2]
  rw [h]
  exact (isOpen_basicOpen T 1).preimage continuous_subtype_val

/-- **Wedhorn's Example 7.58 for the closed unit disc**: `Spa(K⟨T⟩, K⟨T⟩°)` is an open subspace of
`Spa(K⟨T⟩, K⟨T⟩⁺)`. -/
theorem isOpenEmbedding_inclusion_closedPolydisc_spa_closedDiscMinimalPlus :
    Topology.IsOpenEmbedding (Set.inclusion (closedPolydisc_subset_spa_closedDiscMinimalPlus
      (K := K))) :=
  .inclusion _ isOpen_closedPolydisc_spa_closedDiscMinimalPlus

/-- **Wedhorn's Example 7.58 for the closed unit disc**: `Spa(K⟨T⟩, K⟨T⟩°)` is dense in
`Spa(K⟨T⟩, K⟨T⟩⁺)`. The only further point `x_{>1}` lies in the closure of the Gauss point. -/
theorem denseRange_inclusion_closedPolydisc_spa_closedDiscMinimalPlus :
    DenseRange (Set.inclusion (closedPolydisc_subset_spa_closedDiscMinimalPlus (K := K))) := by
  rw [denseRange_inclusion_iff, spa_closedDiscMinimalPlus]
  refine Set.insert_subset ?_ subset_closure
  exact closure_mono (Set.singleton_subset_iff.mpr (gaussPoint one_pos le_rfl).2)
    (specializes_iff_mem_closure.mp gaussPoint_specializes_gaussPointAboveOne)

/-- **`x_{>1}` is a closed point of `Spa(K⟨T⟩, K⟨T⟩⁺)`**: its complement is the closed unit
disc, which is open. -/
theorem isClosed_singleton_gaussPointAboveOne :
    IsClosed ({⟨gaussPointAboveOne K, gaussPointAboveOne_mem_spa_closedDiscMinimalPlus⟩} :
      Set (spa (closedDiscMinimalPlus K))) := by
  refine isOpen_compl_iff.mp ?_
  convert isOpen_closedPolydisc_spa_closedDiscMinimalPlus (K := K) using 1
  ext v
  have hv : (v : Spv 𝒯) ∈ insert (gaussPointAboveOne K) (closedPolydisc 1 K) :=
    spa_closedDiscMinimalPlus (K := K) ▸ v.2
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
  exact ⟨hv.resolve_left, fun h h' ↦ gaussPointAboveOne_notMem_closedPolydisc (h' ▸ h)⟩

end TauCeti.ValuationSpectrum
