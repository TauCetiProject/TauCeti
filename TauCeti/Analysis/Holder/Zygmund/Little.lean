/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Holder.Little
public import TauCeti.Analysis.Holder.Zygmund.Basic
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
  filter (`TauCeti.BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact`).

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

Conversely, if `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` for `0 < α < 1`, then the dyadic partial sums
`partialSumCLM F φ (k + α) ∞ ∞ N u` converge to `u` in `𝒞^{k+α}`
(`TauCeti.BesovSpace.tendsto_partialSumCLM_top_of_tendsto`). Each partial sum is band-limited and
therefore lies in `𝒞^{k+β}` for `β = (α + 1) / 2 > α`
(`TauCeti.BesovSpace.memBesov_toDistr_partialSumCLM`); its `k`-th derivative is therefore
`β`-Hölder and hence little `α`-Hölder (`HolderWith.memLittleHolder`). Passing to the limit in
the closed subspace `TauCeti.HolderSpace.littleHolder` yields little `α`-Hölder regularity of
`D^k f`.

## Main declarations

* `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_ofHolderSpace` and
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_ofCkHolderSpace`: little `α`-Hölder regularity of
  `D^k f` implies `2^{(k+α)j} ‖Δⱼ f‖_∞ → 0` for every `α < 1`.
* `TauCeti.BesovSpace.memLittleHolder_iteratedFDeriv_toCkHolderSpace`,
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_memLittleHolder`, and
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_mem_littleHolder`: for `0 < α < 1`,
  `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` iff `D^k f` is little `α`-Hölder.
* `TauCeti.BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact` and
  `TauCeti.BesovSpace.mem_littleBesov_iff_mem_littleHolder_and_tendsto_cocompact`: for `0 < α < 1`,
  `u ∈ c^{k+α}` iff `D^k f` is little `α`-Hölder and `f` vanishes at infinity.
* `TauCeti.BesovSpace.ofCkHolderSpace_mem_littleBesov_iff` and
  `TauCeti.BesovSpace.ofHolderSpace_mem_littleBesov_iff`: the corresponding characterisations for
  `CkHolderSpace` and `HolderSpace` elements.

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

/-! ### Little Hölder regularity implies high-frequency block decay -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

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
  obtain ⟨B, hB, hinc⟩ := exists_norm_sub_le_of_memLittleHolder hf hη
  -- The second term decays geometrically with ratio `q = 2^{α - 1} < 1`.
  set q : ℝ := (2 : ℝ) ^ ((α : ℝ) - 1)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hα1)
  have htend : Tendsto (fun j : ℕ ↦ (B * 2 ^ (α : ℝ) * M1) * q ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (B * 2 ^ (α : ℝ) * M1)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htend (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)]
  have hNj := hN j hj
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hNj
  have hfirst : η * (2 ^ (α : ℝ) * Mα) < ε / 2 := by
    have hlt : 2 ^ (α : ℝ) * Mα < 2 ^ (α : ℝ) * Mα + 1 := lt_add_one _
    calc η * (2 ^ (α : ℝ) * Mα)
        < η * (2 ^ (α : ℝ) * Mα + 1) := mul_lt_mul_of_pos_left hlt hη
      _ = ε / 2 := by
          simp only [η]
          have hpos : 2 ^ (α : ℝ) * Mα + 1 ≠ 0 := by positivity
          field_simp
  calc 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖v (j + 1)‖
      ≤ η * (2 ^ (α : ℝ) * Mα) + (B * 2 ^ (α : ℝ) * M1) * q ^ j :=
        rpow_mul_norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ hη.le hB hinc (hv (j + 1))
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hNj
    _ = ε := add_halves ε

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- **Little `α`-Hölder functions have vanishing high-frequency blocks**, for every `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_ofHolderSpace (hα1 : α < 1) {f : HolderSpace α E F}
    (hf : f ∈ HolderSpace.littleHolder α E F) :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖(ofHolderSpace F φ α f).block j‖) atTop (𝓝 0) :=
  tendsto_rpow_mul_norm_littlewoodPaleyBlock_of_memLittleHolder φ hα1
    (f := f.toBoundedContinuousFunction)
    (by
      have hfun : ⇑f.toBoundedContinuousFunction = ⇑f := funext f.toBoundedContinuousFunction_apply
      rw [hfun]
      exact HolderSpace.mem_littleHolder_iff.1 hf)
    fun j ↦ by rw [← toDistr_ofHolderSpace, (ofHolderSpace F φ α f).coe_block]

/-- **Bounded `C^{k,α}` maps with little `α`-Hölder `k`-th derivative have vanishing
high-frequency blocks**, for every `k : ℕ` and `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_ofCkHolderSpace (hα1 : α < 1) {f : CkHolderSpace k α E F}
    (hf : MemLittleHolder α (_root_.iteratedFDeriv ℝ k f)) :
    Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖(ofCkHolderSpace F φ k α f).block j‖)
      atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, _, hrev⟩ :=
    CkHolderSpace.exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_sum_directional (F := F) φ b
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
        ≤ ‖_root_.iteratedFDeriv ℝ k f x - _root_.iteratedFDeriv ℝ k f y‖ * ∏ r, ‖b (i r)‖ := by
          simpa only [Fin.val_last, Function.comp_apply] using
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
  exact hrev k f (α : ℝ) j ((ofCkHolderSpace F φ k α f).block (j + 1)) (fun i ↦ w i (j + 1))
    (by rw [← toDistr_ofCkHolderSpace, (ofCkHolderSpace F φ k α f).coe_block])
    (fun i ↦ hw i (j + 1))

end BesovSpace

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
  rw [← SetLike.mem_coe]
  refine HolderSpace.isClosed_littleHolder.mem_of_tendsto
    ((T.continuous.tendsto u).comp (tendsto_partialSumCLM_top_of_tendsto hdecay))
    (Eventually.of_forall fun N ↦ ?_)
  -- Each partial sum `S_N u` lies in `𝒞^{k+β}` for `β = (α + 1) / 2 > α`, so its `k`-th
  -- derivative is `β`-Hölder and hence little `α`-Hölder.
  set β : ℝ≥0 := (α + 1) / 2
  have hβ0 : 0 < β := by positivity
  have hβ1 : β < 1 := by
    have : (α : ℝ) < 1 := hα1
    exact_mod_cast (by linarith : ((α : ℝ) + 1) / 2 < 1)
  have hαβ : α < β := by
    have : (α : ℝ) < 1 := hα1
    exact_mod_cast (by linarith : (α : ℝ) < ((α : ℝ) + 1) / 2)
  have hmemβ := memBesov_toDistr_partialSumCLM (k + β) ∞ N u
  set v' : BesovSpace F φ (k + β) ∞ ∞ := hmemβ.toBesovSpace
  have hfg : (toCkHolderSpace F φ k hα0 hα1
        (partialSumCLM F φ (k + α) ∞ ∞ N u)).toBoundedContinuousFunction =
      (toCkHolderSpace F φ k hβ0 hβ1 v').toBoundedContinuousFunction :=
    toTemperedDistribution_toLpTop_injective (μ := volume) <| by
      simp [v']
  have hfun : ⇑(toCkHolderSpace F φ k hα0 hα1 (partialSumCLM F φ (k + α) ∞ ∞ N u)) =
      ⇑(toCkHolderSpace F φ k hβ0 hβ1 v') := by
    ext x
    simpa only [CkHolderSpace.coe_toBoundedContinuousFunction] using DFunLike.congr_fun hfg x
  have hLH : MemLittleHolder α
      (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1
        (partialSumCLM F φ (k + α) ∞ ∞ N u))) := by
    rw [hfun]
    exact (toCkHolderSpace F φ k hβ0 hβ1 v').memHolder_iteratedFDeriv.holderWith.memLittleHolder hαβ
  simpa only [Function.comp_apply, SetLike.mem_coe, T, ContinuousLinearMap.comp_apply,
    CkHolderSpace.iteratedFDerivHolderL_apply, HolderSpace.mem_littleHolder_iff,
    CkHolderSpace.coe_iteratedFDerivHolder] using hLH

/-- **High-frequency block decay characterises little Hölder regularity.** For `k : ℕ` and
`0 < α < 1`, an element `u ∈ 𝒞^{k+α}` has `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` exactly when the `k`-th
derivative of its `C_b^{k,α}` representative is little `α`-Hölder. -/
theorem tendsto_rpow_mul_norm_block_iff_memLittleHolder (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ (k + α) ∞ ∞} :
    Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖u.block j‖) atTop (𝓝 0) ↔
      MemLittleHolder α (iteratedFDeriv ℝ k (toCkHolderSpace F φ k hα0 hα1 u)) :=
  ⟨memLittleHolder_iteratedFDeriv_toCkHolderSpace φ k hα0 hα1, fun hLH ↦ by
    simpa only [ofCkHolderSpace_toCkHolderSpace] using
      tendsto_rpow_mul_norm_block_ofCkHolderSpace φ hα1 hLH⟩

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
    set Φ : BesovSpace F φ (k + α) ∞ ∞ →L[ℝ] Lp F ∞ (volume : Measure E) :=
      ((toLpTop (volume : Measure E) ℂ).restrictScalars ℝ).comp
        (CkHolderSpace.toBoundedContinuousFunctionCLM.comp (toCkHolderSpace F φ k hα0 hα1))
    have hΦ (v : BesovSpace F φ (k + α) ∞ ∞) :
        Φ v = toLpTop (volume : Measure E) ℂ
          (toCkHolderSpace F φ k hα0 hα1 v).toBoundedContinuousFunction := by
      simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
        CkHolderSpace.toBoundedContinuousFunctionCLM_apply]
    have hΦ_schwartz (g : 𝓢(E, F)) :
        Φ (SchwartzMap.toBesovSpaceCLM F φ (k + α) ∞ ∞ g) = g.toLp ∞ (volume : Measure E) :=
      Lp.toTemperedDistribution_injective <| by
        simp only [hΦ, toLpTop_toCkHolderSpace, SchwartzMap.toDistr_toBesovSpaceCLM,
          Lp.toTemperedDistribution_toLp_eq]
    rw [← SetLike.mem_coe, coe_littleBesov] at hu
    have hmem : Φ u ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ (volume : Measure E)) :=
      map_mem_closure Φ.continuous hu fun _ ⟨g, hg⟩ ↦ ⟨g, hg ▸ (hΦ_schwartz g).symm⟩
    rw [hΦ, toLpTop_mem_closure_range_schwartz_toLp_top_iff] at hmem
    simpa only [CkHolderSpace.coe_toBoundedContinuousFunction] using hmem
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

/-- A bounded `C^{k,α}` map (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^{k+α}`
exactly when its `k`-th derivative is little `α`-Hölder and the map vanishes at infinity. -/
theorem ofCkHolderSpace_mem_littleBesov_iff (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    ofCkHolderSpace F φ k α f ∈ littleBesov F φ (k + α) ∞ ↔
      MemLittleHolder α (_root_.iteratedFDeriv ℝ k f) ∧ Tendsto f (cocompact E) (𝓝 0) := by
  simpa only [toCkHolderSpace_ofCkHolderSpace] using
    mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact φ k hα0 hα1
      (u := ofCkHolderSpace F φ k α f)

/-- A bounded `α`-Hölder function (`0 < α < 1`) lies in the little Hölder–Zygmund space `c^α`
exactly when it lies in `h^{0,α}` and vanishes at infinity. -/
theorem ofHolderSpace_mem_littleBesov_iff (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    ofHolderSpace F φ α f ∈ littleBesov F φ α ∞ ↔
      f ∈ HolderSpace.littleHolder α E F ∧ Tendsto f (cocompact E) (𝓝 0) := by
  simpa only [toHolderSpace_ofHolderSpace] using
    mem_littleBesov_iff_mem_littleHolder_and_tendsto_cocompact φ hα0 hα1
      (u := ofHolderSpace F φ α f)

end BesovSpace

end TauCeti
