/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Holder.Little
public import TauCeti.Analysis.Holder.Zygmund.Equiv
import TauCeti.Analysis.Distribution.SchwartzSpace.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Little Hölder–Zygmund spaces and vanishing small-scale moduli

The little Hölder–Zygmund space `c^{k+α}` is `TauCeti.BesovSpace.littleBesov F φ (k + α) ∞`, the
closure of the Schwartz functions in `𝒞^{k+α} = B^{k+α}_{∞,∞}`. By
`TauCeti.BesovSpace.mem_littleBesov_iff`, an element `u ∈ 𝒞^{k+α}` belongs to `c^{k+α}` exactly
when

1. its weighted Littlewood–Paley blocks vanish at high frequency, `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0`, and
2. every block `Δⱼ u` lies in the `L^∞` closure of the Schwartz functions.

This file translates both conditions into classical pointwise properties of the `C_b^{k,α}`
function representing `u`, for non-integer orders `k + α` (`k : ℕ`, `0 < α < 1`):

* **High-frequency block decay is little Hölder regularity:** `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` holds
  exactly when the `k`-th derivative `D^k f` of the representing function `f` is little `α`-Hölder
  (`TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_memLittleHolder`; and for `k = 0`,
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_mem_littleHolder`). The direction from little
  Hölder regularity to block decay holds for every `α < 1`, including `α = 0` (uniform continuity).
* **Membership in `c^{k+α}` is little Hölder regularity plus vanishing at infinity:** `u ∈ c^{k+α}`
  holds exactly when `D^k f` is little `α`-Hölder and `f` vanishes at infinity along the cocompact
  filter (`TauCeti.BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact`). For
  compactly supported `C_b^{k,α}` functions, vanishing at infinity is automatic, so membership in
  `c^{k+α}` reduces to little `α`-Hölder regularity of `D^k f`
  (`TauCeti.CkHolderSpace.toBesovSpace_mem_littleBesov_iff_of_hasCompactSupport`).

## The argument

A bounded continuous function lies in the `L^∞` closure of the Schwartz functions exactly when it
vanishes at infinity (`BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`),
and Littlewood–Paley blocks preserve this closure
(`TemperedDistribution.littlewoodPaleyBlock_mem_closure_range_schwartz_toLp`).

If a bounded continuous function `f` is little `α`-Hölder with `α < 1`, then for every `ε > 0`
there is `δ > 0` such that the global increment bound
`‖f (x - y) - f x‖ ≤ ε ‖y‖^α + (2 ‖f‖ / δ) ‖y‖` holds for all `x, y`. The kernel cancellation
estimate `TemperedDistribution.norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le` then bounds
`2^{α(j+1)} ‖Δ_{j+1} f‖_∞` by a constant times `ε` plus a multiple of `(2^{α - 1})^j`, which tends
to zero because `α < 1`. For higher order `k`, weighted reverse Bernstein
(`TauCeti.CkHolderSpace.exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional`)
transfers this decay from the directional `k`-th derivatives
`CkHolderSpace.directionalIteratedFDeriv` to `Δ_{j+1} f`.

Conversely, if `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` for `0 < α < 1`, then the low-pass truncations
`S_N u = ∑_{j ≤ N} Δⱼ u` approximate `u` in `𝒞^{k+α}`
(`TauCeti.BesovSpace.exists_toDistr_eq_sum_block_and_norm_sub_le`). Each `S_N u` has only finitely
many nonzero blocks, so it lies in `𝒞^{k+β}` for `β = (α + 1) / 2 > α`; its `k`-th derivative is
therefore `β`-Hölder and hence little `α`-Hölder (`HolderWith.memLittleHolder`). Passing to the
limit in the closed subspace `TauCeti.HolderSpace.littleHolder` yields little `α`-Hölder regularity
of `D^k f`.

## Main declarations

* `TauCeti.HolderSpace.tendsto_rpow_mul_norm_block_toBesovSpace` and
  `TauCeti.CkHolderSpace.tendsto_rpow_mul_norm_block_toBesovSpace`: little `α`-Hölder regularity of
  `D^k f` implies `2^{(k+α)j} ‖Δⱼ f‖_∞ → 0` for every `α < 1`.
* `TauCeti.BesovSpace.memLittleHolder_iteratedFDeriv_toCkHolderSpace`,
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_memLittleHolder`, and
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_mem_littleHolder`: for `0 < α < 1`,
  `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` iff `D^k f` is little `α`-Hölder.
* `TauCeti.BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact` and
  `TauCeti.BesovSpace.mem_littleBesov_iff_mem_littleHolder_and_tendsto_cocompact`: for `0 < α < 1`,
  `u ∈ c^{k+α}` iff `D^k f` is little `α`-Hölder and `f` vanishes at infinity.
* `TauCeti.CkHolderSpace.toBesovSpace_mem_littleBesov_iff`,
  `TauCeti.CkHolderSpace.toBesovSpace_mem_littleBesov_iff_of_hasCompactSupport`,
  `TauCeti.HolderSpace.toBesovSpace_mem_littleBesov_iff`, and
  `TauCeti.HolderSpace.toBesovSpace_mem_littleBesov_iff_of_hasCompactSupport`: the corresponding
  characterisations for `CkHolderSpace` and `HolderSpace` elements, with vanishing at infinity
  discharged under compact support.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Birkhäuser,
  1995, Chapter 0.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution BoundedContinuousFunction Module Filter
open scoped ENNReal NNReal SchwartzMap Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### Little Hölder regularity implies high-frequency block decay -/

section LittleHolderToDecay

/-- For `α < 1`, if a bounded continuous function `f` is little `α`-Hölder, then its weighted
dyadic blocks satisfy `2^{α j} ‖Δⱼ f‖_∞ → 0`. -/
private theorem tendsto_rpow_mul_norm_littlewoodPaleyBlock_of_memLittleHolder
    (φ : ContDiffBump (0 : E)) {α : ℝ≥0} (hα1 : α < 1) {f : E →ᵇ F} (hf : MemLittleHolder α f)
    {v : ℕ → Lp F ∞ (volume : Measure E)}
    (hv : ∀ j, littlewoodPaleyBlock F φ j (toLpTop volume ℂ f : 𝓢'(E, F)) = v j) :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖v j‖) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  set Mα : ℝ :=
    ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set M1 : ℝ :=
    ∫ y, ‖y‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set η : ℝ := ε / (2 * (2 ^ (α : ℝ) * Mα + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδf⟩ := memLittleHolder_iff.1 hf η hη
  -- Global increment bound combining the small-scale `η`-Hölder bound and the global sup bound.
  have hinc : ∀ x y, ‖f (x - y) - f x‖ ≤ η * ‖y‖ ^ (α : ℝ) + (2 * ‖f‖ / δ) * ‖y‖ := fun x y ↦ by
    rcases lt_or_ge ‖y‖ δ with hy | hy
    · have hd : dist (x - y) x < δ := by
        rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      have h := hδf (x - y) x hd
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h
      exact h.trans (le_add_of_nonneg_right (by positivity))
    · have h2f : ‖f (x - y) - f x‖ ≤ 2 * ‖f‖ :=
        (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (x - y), f.norm_coe_le_norm x])
      have hlarge : 2 * ‖f‖ ≤ (2 * ‖f‖ / δ) * ‖y‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        exact mul_le_mul_of_nonneg_left hy (by positivity)
      exact (h2f.trans hlarge).trans (le_add_of_nonneg_left (by positivity))
  -- The second term decays geometrically with ratio `q = 2^{α - 1} < 1`.
  set q : ℝ := (2 : ℝ) ^ ((α : ℝ) - 1)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hα1)
  have htend : Tendsto (fun j : ℕ ↦ ((2 * ‖f‖ / δ) * 2 ^ (α : ℝ) * M1) * q ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
      ((2 * ‖f‖ / δ) * 2 ^ (α : ℝ) * M1)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htend (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)]
  have hNj := hN j hj
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hNj
  have hblock := norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ α.coe_nonneg hη.le
    (by positivity) hinc (hv (j + 1))
  have hpow : (2 : ℝ) ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) =
      2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j) := by
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.rpow_add two_pos, mul_comm]
  have hratio : 2 ^ ((α : ℝ) * j) * ((2 : ℝ) ^ j)⁻¹ = q ^ j := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_neg zero_le_two, ← Real.rpow_add two_pos,
      ← Real.rpow_mul_natCast zero_le_two]
    congr 1
    ring
  have hfirst : η * (2 ^ (α : ℝ) * Mα) < ε / 2 := by
    have hlt : 2 ^ (α : ℝ) * Mα < 2 ^ (α : ℝ) * Mα + 1 := lt_add_one _
    calc η * (2 ^ (α : ℝ) * Mα)
        < η * (2 ^ (α : ℝ) * Mα + 1) := mul_lt_mul_of_pos_left hlt hη
      _ = ε / 2 := by
          simp only [η]
          have hpos : 2 ^ (α : ℝ) * Mα + 1 ≠ 0 := by positivity
          field_simp
  calc 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖v (j + 1)‖
      ≤ 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          (η * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα + (2 * ‖f‖ / δ) * ((2 : ℝ) ^ j)⁻¹ * M1) := by
        gcongr
    _ = η * (2 ^ (α : ℝ) * Mα) + ((2 * ‖f‖ / δ) * 2 ^ (α : ℝ) * M1) * q ^ j := by
        rw [hpow, mul_add, ← hratio]
        have h2αj : (2 : ℝ) ^ ((α : ℝ) * j) ≠ 0 := by positivity
        field_simp
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hNj
    _ = ε := add_halves ε

namespace HolderSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Little `α`-Hölder functions have vanishing high-frequency blocks**, for every `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_toBesovSpace (hα1 : α < 1) {f : HolderSpace α E F}
    (hf : f ∈ littleHolder α E F) :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖(toBesovSpace φ f).block j‖) atTop (𝓝 0) :=
  tendsto_rpow_mul_norm_littlewoodPaleyBlock_of_memLittleHolder φ hα1
    (f := f.toBoundedContinuousFunction)
    (by
      have hfun : ⇑f.toBoundedContinuousFunction = ⇑f := funext f.toBoundedContinuousFunction_apply
      rw [hfun]
      exact mem_littleHolder_iff.1 hf)
    fun j ↦ by rw [← toDistr_toBesovSpace, (toBesovSpace φ f).coe_block]

end HolderSpace

namespace CkHolderSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- **Bounded `C^{k,α}` maps with little `α`-Hölder `k`-th derivative have vanishing
high-frequency blocks**, for every `k : ℕ` and `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_toBesovSpace (hα1 : α < 1) {f : CkHolderSpace k α E F}
    (hf : MemLittleHolder α (_root_.iteratedFDeriv ℝ k f)) :
    Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖(toBesovSpace φ f).block j‖) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, _, hrev⟩ :=
    exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional (F := F) φ b
  have hnorm_b : ∀ (i : Fin k → Fin (finrank ℝ E)), ∏ r, ‖b (i r)‖ = 1 := fun i ↦
    Finset.prod_eq_one fun r _ ↦ b.orthonormal.1 (i r)
  choose w hw _ using fun (i : Fin k → Fin (finrank ℝ E)) (j : ℕ) ↦
    hC₀ j (toLpTop volume ℂ (f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i)))
  have hgLH (i : Fin k → Fin (finrank ℝ E)) :
      MemLittleHolder α (f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i)) := by
    rw [memLittleHolder_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := memLittleHolder_iff.1 hf ε hε
    refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
    rw [dist_eq_norm]
    calc ‖f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) x -
            f.directionalIteratedFDeriv (Fin.last k) (⇑b ∘ i) y‖
        ≤ ‖_root_.iteratedFDeriv ℝ k f x - _root_.iteratedFDeriv ℝ k f y‖ * ∏ r, ‖b (i r)‖ :=
          f.norm_directionalIteratedFDeriv_sub_le (Fin.last k) (⇑b ∘ i) x y
      _ = dist (_root_.iteratedFDeriv ℝ k f x) (_root_.iteratedFDeriv ℝ k f y) := by
          rw [hnorm_b i, mul_one, dist_eq_norm]
      _ ≤ ε * dist x y ^ (α : ℝ) := hδf x y hxy
  have hwtend (i : Fin k → Fin (finrank ℝ E)) :
      Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i (j + 1)‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 <|
      tendsto_rpow_mul_norm_littlewoodPaleyBlock_of_memLittleHolder φ hα1 (hgLH i) (hw i)
  have hsum_tend :
      Tendsto (fun j : ℕ ↦ Cr ^ k *
        ∑ i : Fin k → Fin (finrank ℝ E), 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖w i (j + 1)‖)
        atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ fun i _ ↦ hwtend i).const_mul (Cr ^ k)
  refine squeeze_zero (fun j ↦ by positivity) (fun j ↦ ?_) hsum_tend
  exact hrev k f (α : ℝ) j ((toBesovSpace φ f).block (j + 1)) (fun i ↦ w i (j + 1))
    (by rw [← toDistr_toBesovSpace, (toBesovSpace φ f).coe_block])
    (fun i ↦ hw i (j + 1))

end CkHolderSpace

end LittleHolderToDecay

/-! ### High-frequency block decay is equivalent to little Hölder regularity -/

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- **Vanishing high-frequency blocks imply little Hölder regularity.** For `k : ℕ` and
`0 < α < 1`, if `u ∈ 𝒞^{k+α}` satisfies `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0`, then the `k`-th derivative of
`toCkHolderSpace F φ k hα0 hα1 u` is little `α`-Hölder. -/
theorem memLittleHolder_iteratedFDeriv_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ (k + α) ∞ ∞}
    (hdecay : Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖u.block j‖) atTop (𝓝 0)) :
    MemLittleHolder α (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1 u)) := by
  set T : BesovSpace F φ (k + α) ∞ ∞ →L[ℝ] HolderSpace α E (E [×k]→L[ℝ] F) :=
    CkHolderSpace.iteratedFDerivHolderL.comp (toCkHolderSpace F φ k hα0 hα1)
  suffices hmem : T u ∈ HolderSpace.littleHolder α E (E [×k]→L[ℝ] F) by
    simpa only [T, ContinuousLinearMap.comp_apply, CkHolderSpace.iteratedFDerivHolderL_apply,
      HolderSpace.mem_littleHolder_iff, CkHolderSpace.coe_iteratedFDerivHolder] using hmem
  rw [← SetLike.mem_coe, ← HolderSpace.isClosed_littleHolder.closure_eq]
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  set η : ℝ := ε / (2 * (‖T‖ + 1))
  have hη : 0 < η := by positivity
  obtain ⟨N, v, hvw, huv⟩ := exists_toDistr_eq_sum_block_and_norm_sub_le hdecay hη
  refine ⟨T v, ?_, ?_⟩
  · -- The band-limited truncation `v` lies in `𝒞^{k+β}` for `β = (α + 1) / 2 > α`, so its
    -- `k`-th derivative is `β`-Hölder and hence little `α`-Hölder.
    set β : ℝ≥0 := (α + 1) / 2
    have hβ0 : 0 < β := by positivity
    have hβ1 : β < 1 := by
      have : (α : ℝ) < 1 := hα1
      exact_mod_cast (by linarith : ((α : ℝ) + 1) / 2 < 1)
    have hαβ : α < β := by
      have : (α : ℝ) < 1 := hα1
      exact_mod_cast (by linarith : (α : ℝ) < ((α : ℝ) + 1) / 2)
    obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
    obtain ⟨_, -, hBL⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
    set w : Lp F ∞ (volume : Measure E) := ∑ j ∈ Finset.range (N + 1), u.block j
    obtain ⟨v', hv'w, -⟩ := hBL (k + β) (N + L) w fun m hm ↦ by
      simp only [w, Lp.toTemperedDistribution_sum, coe_block]
      exact (hL m N).2 hm u.toDistr
    have hfg : (toCkHolderSpace F φ k hα0 hα1 v).toBoundedContinuousFunction =
        (toCkHolderSpace F φ k hβ0 hβ1 v').toBoundedContinuousFunction :=
      toTemperedDistribution_toLpTop_injective (μ := volume) <| by
        simp only [toLpTop_toCkHolderSpace, hvw, hv'w]
    have hfun : ⇑(toCkHolderSpace F φ k hα0 hα1 v) = ⇑(toCkHolderSpace F φ k hβ0 hβ1 v') := by
      ext x
      simpa only [CkHolderSpace.coe_toBoundedContinuousFunction] using DFunLike.congr_fun hfg x
    have hLH : MemLittleHolder α (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1 v)) := by
      rw [hfun]
      exact (toCkHolderSpace F φ k hβ0 hβ1 v').memHolder_iteratedFDeriv.holderWith.memLittleHolder
        hαβ
    simpa only [SetLike.mem_coe, T, ContinuousLinearMap.comp_apply,
      CkHolderSpace.iteratedFDerivHolderL_apply, HolderSpace.mem_littleHolder_iff,
      CkHolderSpace.coe_iteratedFDerivHolder] using hLH
  · rw [dist_eq_norm, ← map_sub]
    calc ‖T (u - v)‖ ≤ ‖T‖ * ‖u - v‖ := T.le_opNorm (u - v)
      _ ≤ ‖T‖ * η := mul_le_mul_of_nonneg_left huv (norm_nonneg T)
      _ < (‖T‖ + 1) * η := mul_lt_mul_of_pos_right (lt_add_one _) hη
      _ = ε / 2 := by
          simp only [η]
          have hpos : ‖T‖ + 1 ≠ 0 := by positivity
          field_simp
      _ < ε := half_lt_self hε

/-- **High-frequency block decay characterises little Hölder regularity.** For `k : ℕ` and
`0 < α < 1`, an element `u ∈ 𝒞^{k+α}` has `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` exactly when the `k`-th
derivative of its `C_b^{k,α}` representative is little `α`-Hölder. -/
theorem tendsto_rpow_mul_norm_block_iff_memLittleHolder (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ (k + α) ∞ ∞} :
    Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖u.block j‖) atTop (𝓝 0) ↔
      MemLittleHolder α (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1 u)) :=
  ⟨memLittleHolder_iteratedFDeriv_toCkHolderSpace φ k hα0 hα1, fun hLH ↦ by
    simpa only [toBesovSpace_toCkHolderSpace] using
      CkHolderSpace.tendsto_rpow_mul_norm_block_toBesovSpace φ hα1 hLH⟩

/-- The order-zero `CkHolderSpace` representative of `u ∈ 𝒞^α` (viewed in `𝒞^{0+α}`) has the same
underlying function as `toHolderSpace F φ hα0 hα1 u`. -/
private theorem coe_toCkHolderSpace_zero_inclusion (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ α ∞ ∞) :
    ⇑(toCkHolderSpace F φ 0 hα0 hα1 (inclusion F φ ∞ (by simp) le_rfl u)) =
      ⇑(toHolderSpace F φ hα0 hα1 u) := by
  have hfg :
      (toCkHolderSpace F φ 0 hα0 hα1
        (inclusion F φ ∞ (by simp) le_rfl u)).toBoundedContinuousFunction =
      (toHolderSpace F φ hα0 hα1 u).toBoundedContinuousFunction :=
    toTemperedDistribution_toLpTop_injective (μ := volume) <| by simp
  ext x
  simpa only [CkHolderSpace.coe_toBoundedContinuousFunction,
    HolderSpace.toBoundedContinuousFunction_apply] using DFunLike.congr_fun hfg x

/-- **Order-zero block decay characterises little Hölder regularity.** For `0 < α < 1`, an element
`u ∈ 𝒞^α` has `2^{α j} ‖Δⱼ u‖_∞ → 0` exactly when its `C^{0,α}` representative lies in the little
Hölder space `h^{0,α}`. -/
theorem tendsto_rpow_mul_norm_block_iff_mem_littleHolder (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) ↔
      toHolderSpace F φ hα0 hα1 u ∈ HolderSpace.littleHolder α E F := by
  set u0 : BesovSpace F φ ((0 : ℕ) + α) ∞ ∞ := inclusion F φ ∞ (by simp) le_rfl u
  have hLH_iff : MemLittleHolder α (iteratedFDeriv ℝ 0 (toCkHolderSpace F φ 0 hα0 hα1 u0)) ↔
      toHolderSpace F φ hα0 hα1 u ∈ HolderSpace.littleHolder α E F := by
    simp only [u0, coe_toCkHolderSpace_zero_inclusion, HolderSpace.mem_littleHolder_iff,
      memLittleHolder_iff, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.dist_map]
  simpa only [u0, Nat.cast_zero, zero_add, block_inclusion] using
    (tendsto_rpow_mul_norm_block_iff_memLittleHolder φ 0 hα0 hα1 (u := u0)).trans hLH_iff

/-! ### Characterisation of the little Hölder–Zygmund space `c^{k+α}` -/

/-- **Characterisation of the little Hölder–Zygmund space `c^{k+α}`.** For `k : ℕ` and
`0 < α < 1`, an element `u ∈ 𝒞^{k+α}` lies in the little space `c^{k+α}` (the closure of the
Schwartz functions in `𝒞^{k+α}`) exactly when the `k`-th derivative of its `C_b^{k,α}`
representative `f` is little `α`-Hölder and `f` vanishes at infinity. -/
theorem mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact (k : ℕ) (hα0 : 0 < α)
    (hα1 : α < 1) {u : BesovSpace F φ (k + α) ∞ ∞} :
    u ∈ littleBesov F φ (k + α) ∞ ↔
      MemLittleHolder α (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1 u)) ∧
        Tendsto (toCkHolderSpace F φ k hα0 hα1 u) (cocompact E) (𝓝 0) := by
  constructor
  · intro hu
    refine ⟨(tendsto_rpow_mul_norm_block_iff_memLittleHolder φ k hα0 hα1).1
      (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu), ?_⟩
    set Φ : BesovSpace F φ (k + α) ∞ ∞ →L[ℝ] (E →ᵇ F) :=
      CkHolderSpace.toBoundedContinuousFunctionCLM.comp (toCkHolderSpace F φ k hα0 hα1)
    have hΦ_schwartz (g : 𝓢(E, F)) :
        Φ (SchwartzMap.toBesovSpaceCLM F φ (k + α) ∞ ∞ g) = g.toBoundedContinuousFunction :=
      toTemperedDistribution_toLpTop_injective (μ := volume) <| by
        simp only [Φ, ContinuousLinearMap.comp_apply,
          CkHolderSpace.toBoundedContinuousFunctionCLM_apply, toLpTop_toCkHolderSpace,
          SchwartzMap.toDistr_toBesovSpaceCLM]
        rw [← Lp.toTemperedDistribution_toLp_eq (p := ∞) (μ := volume) g,
          g.toLp_top_eq_toLpTop (𝕜 := ℂ)]
    rw [← SetLike.mem_coe, coe_littleBesov] at hu
    have hmem : Φ u ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toBoundedContinuousFunction) :=
      map_mem_closure Φ.continuous hu fun _ ⟨g, hg⟩ ↦ ⟨g, hg ▸ (hΦ_schwartz g).symm⟩
    have hLp : toLpTop (volume : Measure E) ℂ (Φ u) ∈
          closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ (volume : Measure E)) :=
      map_mem_closure (toLpTop (volume : Measure E) ℂ).continuous hmem fun _ ⟨g, hg⟩ ↦
        ⟨g, hg ▸ g.toLp_top_eq_toLpTop (𝕜 := ℂ)⟩
    simpa only [Φ, ContinuousLinearMap.comp_apply,
      CkHolderSpace.toBoundedContinuousFunctionCLM_apply,
      CkHolderSpace.coe_toBoundedContinuousFunction] using
      (Φ u).toLpTop_mem_closure_range_schwartz_toLp_top_iff.1 hLp
  · rintro ⟨hLH, h0⟩
    rw [mem_littleBesov_iff]
    refine ⟨(tendsto_rpow_mul_norm_block_iff_memLittleHolder φ k hα0 hα1).2 hLH, fun j ↦ ?_⟩
    have hf_cl : toLpTop (volume : Measure E) ℂ
        (toCkHolderSpace F φ k hα0 hα1 u).toBoundedContinuousFunction ∈
          closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ (volume : Measure E)) :=
      (toCkHolderSpace F φ k hα0 hα1 u).toBoundedContinuousFunction
        |>.toLpTop_mem_closure_range_schwartz_toLp_top_iff.2 (by
          simpa only [CkHolderSpace.coe_toBoundedContinuousFunction] using h0)
    exact littlewoodPaleyBlock_mem_closure_range_schwartz_toLp φ hf_cl <| by
      rw [toLpTop_toCkHolderSpace, coe_block]

/-- **Characterisation of the little Hölder–Zygmund space `c^α` at order `0 < α < 1`.** An element
`u ∈ 𝒞^α` lies in `c^α` exactly when its `C^{0,α}` representative lies in `h^{0,α}` and vanishes
at infinity. -/
theorem mem_littleBesov_iff_mem_littleHolder_and_tendsto_cocompact (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} :
    u ∈ littleBesov F φ α ∞ ↔
      toHolderSpace F φ hα0 hα1 u ∈ HolderSpace.littleHolder α E F ∧
        Tendsto (toHolderSpace F φ hα0 hα1 u) (cocompact E) (𝓝 0) := by
  set u0 : BesovSpace F φ ((0 : ℕ) + α) ∞ ∞ := inclusion F φ ∞ (by simp) le_rfl u
  have hu0_iff : u ∈ littleBesov F φ α ∞ ↔ u0 ∈ littleBesov F φ ((0 : ℕ) + α) ∞ :=
    ⟨fun hu ↦ inclusion_mem_littleBesov (by simp) hu, fun hu0 ↦ by
      have h := inclusion_mem_littleBesov (s' := (α : ℝ)) (by simp) hu0
      have heq : inclusion F φ ∞ (by simp : (α : ℝ) ≤ (0 : ℕ) + α) le_rfl u0 = u :=
        ext (by simp [u0])
      rwa [heq] at h⟩
  rw [hu0_iff, mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact φ 0 hα0 hα1]
  simp only [u0, coe_toCkHolderSpace_zero_inclusion, HolderSpace.mem_littleHolder_iff,
    memLittleHolder_iff, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.dist_map]

end BesovSpace

namespace CkHolderSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- A bounded `C^{k,α}` map (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^{k+α}`
exactly when its `k`-th derivative is little `α`-Hölder and the map vanishes at infinity. -/
theorem toBesovSpace_mem_littleBesov_iff (hα0 : 0 < α) (hα1 : α < 1) (f : CkHolderSpace k α E F) :
    toBesovSpace φ f ∈ BesovSpace.littleBesov F φ (k + α) ∞ ↔
      MemLittleHolder α (_root_.iteratedFDeriv ℝ k f) ∧ Tendsto f (cocompact E) (𝓝 0) := by
  simpa only [BesovSpace.toCkHolderSpace_toBesovSpace] using
    BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact φ k hα0 hα1
      (u := toBesovSpace φ f)

/-- **Compactly supported `C^{k,α}` maps in `c^{k+α}`.** A compactly supported bounded `C^{k,α}`
map (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^{k+α}` exactly when its `k`-th
derivative is little `α`-Hölder. -/
theorem toBesovSpace_mem_littleBesov_iff_of_hasCompactSupport (hα0 : 0 < α) (hα1 : α < 1)
    {f : CkHolderSpace k α E F} (hf : HasCompactSupport f) :
    toBesovSpace φ f ∈ BesovSpace.littleBesov F φ (k + α) ∞ ↔
      MemLittleHolder α (_root_.iteratedFDeriv ℝ k f) := by
  rw [toBesovSpace_mem_littleBesov_iff φ hα0 hα1 f, and_iff_left hf.is_zero_at_infty]

end CkHolderSpace

namespace HolderSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- A bounded `α`-Hölder function (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^α`
exactly when it lies in `h^{0,α}` and vanishes at infinity. -/
theorem toBesovSpace_mem_littleBesov_iff (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    toBesovSpace φ f ∈ BesovSpace.littleBesov F φ α ∞ ↔
      f ∈ littleHolder α E F ∧ Tendsto f (cocompact E) (𝓝 0) := by
  simpa only [BesovSpace.toHolderSpace_toBesovSpace] using
    BesovSpace.mem_littleBesov_iff_mem_littleHolder_and_tendsto_cocompact φ hα0 hα1
      (u := toBesovSpace φ f)

/-- **Compactly supported Hölder functions in `c^α`.** A compactly supported bounded `α`-Hölder
function (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^α` exactly when it lies in
`h^{0,α}`. -/
theorem toBesovSpace_mem_littleBesov_iff_of_hasCompactSupport (hα0 : 0 < α) (hα1 : α < 1)
    {f : HolderSpace α E F} (hf : HasCompactSupport f) :
    toBesovSpace φ f ∈ BesovSpace.littleBesov F φ α ∞ ↔ f ∈ littleHolder α E F := by
  rw [toBesovSpace_mem_littleBesov_iff φ hα0 hα1 f, and_iff_left hf.is_zero_at_infty]

end HolderSpace

end TauCeti
