/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Holder.Little.Basic
public import TauCeti.Analysis.Holder.Zygmund.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Holder.LowOrder
import TauCeti.Topology.MetricSpace.Holder

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
  `TauCeti.BesovSpace.memLittleHolder_iff_tendsto_rpow_mul_norm_block`). The direction from little
  Hölder regularity to block decay holds for every `α < 1`, including `α = 0` (uniform continuity).
* **Membership in `c^{k+α}` is little Hölder regularity plus vanishing at infinity:** `u ∈ c^{k+α}`
  holds exactly when `D^k f` is little `α`-Hölder and `f` vanishes at infinity along the cocompact
  filter (`TauCeti.BesovSpace.mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact`).

## The argument

A bounded continuous function lies in the `L^∞` closure of the Schwartz functions exactly when it
vanishes at infinity (`BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`),
and Littlewood–Paley blocks preserve this closure
(`TemperedDistribution.littlewoodPaleyBlock_mem_closure_range_schwartz_toLp`).

For `α < 1`, the little Hölder space `h^{k,α}` is the closure in `C_b^{k,α}` of the smooth maps
with all derivatives bounded (`TauCeti.CkHolderSpace.littleHolder_eq_closure`). Each such smooth
map has bounded `(k + 1)`-th derivative and therefore lies in `𝒞^{k+1}`; because `k + α < k + 1`,
its weighted blocks of order `k + α` vanish at high frequency, and this decay passes to the
`C_b^{k,α}` closure.

Conversely, if `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` for `0 < α < 1`, then the dyadic partial sums
`partialSumCLM F φ (k + α) ∞ ∞ N u` converge to `u` in `𝒞^{k+α}`
(`TauCeti.BesovSpace.tendsto_partialSumCLM_top_of_tendsto`). Each partial sum is band-limited and
therefore lies in `𝒞^{k+β}` for `β = (α + 1) / 2 > α`
(`TauCeti.BesovSpace.memBesov_toDistr_partialSumCLM`); its `k`-th derivative is therefore
`β`-Hölder and hence little `α`-Hölder (`HolderWith.memLittleHolder`). Passing to the limit in
the closed subspace `TauCeti.HolderSpace.littleHolder` yields little `α`-Hölder regularity of
`D^k f`.

## Main declarations

* `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_ofCkHolderSpace` and
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_ofHolderSpace`: little `α`-Hölder regularity of
  `D^k f` implies `2^{(k+α)j} ‖Δⱼ f‖_∞ → 0` for every `α < 1`.
* `TauCeti.BesovSpace.memLittleHolder_iteratedFDeriv_toCkHolderSpace` and
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_iff_memLittleHolder`: for `0 < α < 1`,
  `2^{(k+α)j} ‖Δⱼ u‖_∞ → 0` iff `D^k f` is little `α`-Hölder.
* `TauCeti.BesovSpace.memLittleHolder_iff_tendsto_rpow_mul_norm_block` and
  `TauCeti.BesovSpace.memLittleHolder_of_mem_littleBesov`: for `0 < α < 1`, a bounded continuous
  representative of `u ∈ 𝒞^α` is little `α`-Hölder iff `2^{jα} ‖Δⱼ u‖_∞ → 0`, and in particular
  representatives of `c^α` are little `α`-Hölder.
* `TauCeti.BesovSpace.not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow` and
  `TauCeti.BesovSpace.notMem_littleBesov_of_eqOn_norm_rpow`: the cusp `x ↦ ‖x‖^α` near `0` has
  non-vanishing weighted blocks and lies outside `c^α`.
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

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- **Bounded `C^{k,α}` maps with little `α`-Hölder `k`-th derivative have vanishing
high-frequency blocks**, for every `k : ℕ` and `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_ofCkHolderSpace (hα1 : α < 1) {f : CkHolderSpace k α E F}
    (hf : MemLittleHolder α (_root_.iteratedFDeriv ℝ k f)) :
    Tendsto (fun j : ℕ ↦ 2 ^ (((k : ℝ) + α) * j) * ‖(ofCkHolderSpace F φ k α f).block j‖)
      atTop (𝓝 0) := by
  have hf_mem : f ∈ (CkHolderSpace.littleHolder k α E F : Set (CkHolderSpace k α E F)) :=
    CkHolderSpace.mem_littleHolder_iff.2 hf
  rw [CkHolderSpace.littleHolder_eq_closure hα1] at hf_mem
  refine isClosed_setOf_tendsto_rpow_mul_norm_block.closure_subset
    (map_mem_closure (ofCkHolderSpace F φ k α).continuous hf_mem fun g hg ↦ ?_)
  obtain ⟨hg_cd, hg_bd⟩ := CkHolderSpace.mem_smoothBoundedDerivatives_iff.1 hg
  choose B hB using hg_bd
  set M : ℝ≥0 := ∑ i ∈ Finset.range (k + 2), (B i).toNNReal
  have hM (i : ℕ) (hi : i ≤ k + 1) (x : E) : ‖_root_.iteratedFDeriv ℝ i g x‖ ≤ M := by
    calc ‖_root_.iteratedFDeriv ℝ i g x‖
        ≤ B i := hB i x
      _ ≤ ((B i).toNNReal : ℝ) := Real.le_coe_toNNReal (B i)
      _ ≤ (M : ℝ) := NNReal.coe_le_coe.2 <|
        Finset.single_le_sum (f := fun j ↦ (B j).toNNReal) (fun _ _ ↦ zero_le)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  obtain ⟨_, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := F) φ (k + 1) 0
  obtain ⟨w, hw, -⟩ := hC g.toBoundedContinuousFunction
    (by
      rw [CkHolderSpace.coe_toBoundedContinuousFunction]
      exact hg_cd.of_le (by exact_mod_cast le_top))
    (M := M) (H := 2 * M)
    (by rw [CkHolderSpace.coe_toBoundedContinuousFunction]; exact hM)
    (holderWith_zero_of_nnnorm_le fun x ↦ by
      rw [CkHolderSpace.coe_toBoundedContinuousFunction, ← NNReal.coe_le_coe, coe_nnNorm]
      exact hM (k + 1) le_rfl x)
  have hlt : ((k : ℝ) + α) < ((k + 1 : ℕ) : ℝ) + ((0 : ℝ≥0) : ℝ) := by
    have hα : (α : ℝ) < 1 := hα1
    push_cast
    linarith
  have hblock (j : ℕ) : (ofCkHolderSpace F φ k α g).block j = w.block j :=
    block_eq_of_toDistr_eq ((toDistr_ofCkHolderSpace φ k g).trans hw.symm) j
  simpa only [Set.mem_ofPred_eq, block_inclusionOfLT, hblock] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top (inclusionOfLT F φ ∞ ∞ 1 hlt w)

/-- **Little `α`-Hölder functions have vanishing high-frequency blocks**, for every `α < 1`. -/
theorem tendsto_rpow_mul_norm_block_ofHolderSpace (hα1 : α < 1) {f : HolderSpace α E F}
    (hf : f ∈ HolderSpace.littleHolder α E F) :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖(ofHolderSpace F φ α f).block j‖) atTop (𝓝 0) := by
  set g : CkHolderSpace 0 α E F := CkHolderSpace.equivHolderSpace.symm f
  have hg : MemLittleHolder α (_root_.iteratedFDeriv ℝ 0 g) := by
    rw [memLittleHolder_iteratedFDeriv_zero_iff, CkHolderSpace.coe_equivHolderSpace_symm]
    exact HolderSpace.mem_littleHolder_iff.1 hf
  have hfg : f.toBoundedContinuousFunction = g.toBoundedContinuousFunction := by
    ext x
    rw [HolderSpace.toBoundedContinuousFunction_apply,
      CkHolderSpace.coe_toBoundedContinuousFunction, CkHolderSpace.coe_equivHolderSpace_symm]
  have hblock (j : ℕ) : (ofHolderSpace F φ α f).block j = (ofCkHolderSpace F φ 0 α g).block j :=
    block_eq_of_toDistr_eq (by rw [toDistr_ofHolderSpace, toDistr_ofCkHolderSpace, hfg]) j
  simpa only [Nat.cast_zero, zero_add, hblock] using
    tendsto_rpow_mul_norm_block_ofCkHolderSpace φ hα1 hg

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
  have hfun : ⇑(toCkHolderSpace F φ k hα0 hα1 (partialSumCLM F φ (k + α) ∞ ∞ N u)) =
      ⇑(toCkHolderSpace F φ k hβ0 hβ1 v') :=
    (coe_toCkHolderSpace_eq_of_toDistr_eq φ hα0 hα1
      ((toLpTop_toCkHolderSpace φ k hβ0 hβ1 v').trans hmemβ.toDistr_toBesovSpace)).trans
      (CkHolderSpace.coe_toBoundedContinuousFunction _)
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

/-- **Little Hölder continuity is block decay.** Let `0 < α < 1` and let `f` be
a bounded continuous function representing `u ∈ 𝒞^α = B^α_{∞,∞}`. Then `f` is little
`α`-Hölder, its `α`-Hölder difference quotients tending to zero at small scales, exactly when the
weighted blocks of `u` vanish at high frequency, `2^{jα} ‖Δⱼ u‖_∞ → 0`. -/
theorem memLittleHolder_iff_tendsto_rpow_mul_norm_block (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) :
    MemLittleHolder α f ↔ Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) := by
  set u0 : BesovSpace F φ ((0 : ℕ) + α) ∞ ∞ := inclusion F φ ∞ (by simp) le_rfl u
  have hcoe : ⇑(toCkHolderSpace F φ 0 hα0 hα1 u0) = ⇑f :=
    coe_toCkHolderSpace_eq_of_toDistr_eq φ hα0 hα1
      (hf.trans (toDistr_inclusion (by rw [Nat.cast_zero, zero_add]) le_rfl u).symm)
  simpa only [u0, Nat.cast_zero, zero_add, block_inclusion, hcoe,
    memLittleHolder_iteratedFDeriv_zero_iff] using
    (tendsto_rpow_mul_norm_block_iff_memLittleHolder φ 0 hα0 hα1 (u := u0)).symm

/-- **Elements of the little Hölder–Zygmund space `c^α` are little Hölder.** For `0 < α < 1`, a
bounded continuous function representing an element of `c^α`, the closure of the Schwartz
functions in `𝒞^α`, is little `α`-Hölder. -/
theorem memLittleHolder_of_mem_littleBesov (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} (hu : u ∈ littleBesov F φ α ∞) {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) : MemLittleHolder α f :=
  (memLittleHolder_iff_tendsto_rpow_mul_norm_block φ hα0 hα1 hf).2
    (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

/-- **The cusp has weighted blocks that do not vanish at high frequency.** Let `0 < α < 1` and let
`u ∈ 𝒞^α` be represented by a bounded continuous function `f` with `‖f x‖ = ‖x‖ ^ α` near `0`,
such as the cusp truncated at height `1`. The weighted blocks `2^{jα} ‖Δⱼ u‖_∞` are bounded by
`‖u‖`, but they do not tend to zero. -/
theorem not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow [Nontrivial E] (hα0 : 0 < α)
    (hα1 : α < 1) {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) {r : ℝ} (hr : 0 < r)
    (hfr : Set.EqOn (fun x ↦ ‖f x‖) (fun x ↦ ‖x‖ ^ (α : ℝ)) (Metric.ball 0 r)) :
    ¬ Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) := fun h ↦
  not_memLittleHolder_of_eqOn_norm_rpow hα0 hr hfr (lipschitzWith_one_norm.comp_memLittleHolder
    ((memLittleHolder_iff_tendsto_rpow_mul_norm_block φ hα0 hα1 hf).2 h))

/-- **The cusp is not in the little Hölder–Zygmund space.** For `0 < α < 1`, an element of `𝒞^α`
represented by a bounded continuous function `f` with `‖f x‖ = ‖x‖ ^ α` near `0` does not lie in
`c^α`, the closure of the Schwartz functions in `𝒞^α`. -/
theorem notMem_littleBesov_of_eqOn_norm_rpow [Nontrivial E] (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F} (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr)
    {r : ℝ} (hr : 0 < r)
    (hfr : Set.EqOn (fun x ↦ ‖f x‖) (fun x ↦ ‖x‖ ^ (α : ℝ)) (Metric.ball 0 r)) :
    u ∉ littleBesov F φ α ∞ := fun hu ↦
  not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow φ hα0 hα1 hf hr hfr
    (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

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
  rw [hu0_iff, mem_littleBesov_iff_memLittleHolder_and_tendsto_cocompact φ 0 hα0 hα1,
    coe_toCkHolderSpace_zero_inclusion, memLittleHolder_iteratedFDeriv_zero_iff,
    HolderSpace.mem_littleHolder_iff]

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
