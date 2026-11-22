/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.PlaneWave
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.One
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Basic
public import TauCeti.MeasureTheory.Function.Lp.One
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.RealInterpolation
import TauCeti.MeasureTheory.Function.Holder

/-!
# Bony's decomposition for factors with a single Littlewood–Paley block

Bony's decomposition `u v = T_u v + T_v u + R(u, v)` (`TauCeti.BesovSpace.lowPass_smul_lowPass`)
sorts the products `Δₖ u · Δₗ v` of Littlewood–Paley blocks by the relative size of the two
frequencies: with gap `N`, the paraproduct `T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` collects the pairs with
`k + N < l`, the paraproduct `T_v u = ∑ⱼ Δⱼ u · S_{j-N} v` those with `l + N < k`, and the resonant
part `R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` those with `|k - l| ≤ N`. Here
`S_m = ∑_{k < m} Δₖ` (`TauCeti.BesovSpace.lowPass`), so for `N = 1` the cut-off `S_{j-1}` sums the
blocks of index at most `j - 2`, the convention of Bahouri–Chemin–Danchin. When a factor has a
single nonzero block the three series can be computed exactly, and this file does so for the two
basic examples.

* **Two factors at the same frequency.** If `u` and `v` each have only the block of index `m`,
  then every term of both paraproducts vanishes and the resonant part is the single product
  `Δₘ u · Δₘ v` (`TauCeti.BesovSpace.hasSum_block_smul_sum_block_of_block_eq_zero`). For the plane
  wave `e_ξ(x) = 𝐞 ⟪x, ξ⟫` with `2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`, which is its own block of
  index `j + 1` (`TauCeti.BesovSpace.block_eq_ite_of_toDistr_eq_fourierInv_delta`), this says that
  `T_{e_ξ} e_ξ = 0` and that the resonant part carries the whole product
  `e_ξ · e_ξ = e_{2ξ}`, of twice the frequency
  (`TauCeti.BesovSpace.hasSum_block_smul_sum_block_of_toDistr_eq_fourierInv_delta`).
* **The constant `1`.** The constant function `1` is its own low-frequency block `Δ₀`
  (`TauCeti.BesovSpace.block_eq_ite_of_toDistr_eq_volume`), so `S_m 1 = 1` for `m ≥ 1` and
  `S_0 1 = 0`. Hence, for every `v`, `T_1 v = ∑_{j > N} Δⱼ v`, every term of `T_v 1` vanishes, and
  `R(1, v) = ∑_{k ≤ N} Δₖ v`; the three series add up to `v`
  (`TauCeti.BesovSpace.hasSum_paraproduct_add_paraproduct_add_resonant_of_toDistr_eq_volume`).
  For `N = 1` this is `T_1 v = ∑_{j ≥ 2} Δⱼ v` and `R(1, v) = Δ₀ v + Δ₁ v`. The check pins the
  convention for the cut-offs: with `S'_j = ∑_{k ≤ j} Δₖ` in place of `S_j`, the paraproduct
  would be `∑_{j ≥ 1} Δⱼ v` and the three terms would add up to `v + Δ₁ v`, counting the pairs of
  adjacent indices twice.

Each example has a single block, which is a bounded function, so it lies in `B^s_{∞,q}` for every
`s` and `q` (`TemperedDistribution.memBesov_of_littlewoodPaleyBlock_eq_ite`), in particular in
every Hölder–Zygmund space `𝒞^s = B^s_{∞,∞}`
(`TemperedDistribution.memBesov_toTemperedDistribution_volume`,
`TemperedDistribution.memBesov_fourierInv_delta`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.6
  (Bony's decomposition).
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Real
open scoped ENNReal SchwartzMap RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s s' : ℝ} {p q q' : ℝ≥0∞} [Fact (1 ≤ p)]

section SingleBlock

variable {p₁ p₂ r : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [p₁.HolderTriple p₂ r]

/-- **The paraproduct `T_u v` of two factors at the same frequency vanishes term by term.** If `u`
and `v` each have only the block of index `m`, then `S_{j-N} u · Δⱼ v = 0` for every `j`. -/
theorem lowPass_smul_block_eq_zero_of_block_eq_zero (N : ℕ) {u : BesovSpace ℂ φ s p₁ q}
    {v : BesovSpace F φ s' p₂ q'} {m : ℕ} (hu : ∀ k, k ≠ m → u.block k = 0)
    (hv : ∀ k, k ≠ m → v.block k = 0) (j : ℕ) :
    (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) = 0 := by
  rcases eq_or_ne j m with rfl | hjm
  · rw [lowPass_eq_ite_of_block_eq_zero hu, ite_eq_right (by omega), Lp.zero_smul]
  · rw [hv j hjm, Lp.smul_zero]

/-- **The paraproduct `T_v u` of two factors at the same frequency vanishes term by term.** If `u`
and `v` each have only the block of index `m`, then `Δⱼ u · S_{j-N} v = 0` for every `j`. -/
theorem block_smul_lowPass_eq_zero_of_block_eq_zero (N : ℕ) {u : BesovSpace ℂ φ s p₁ q}
    {v : BesovSpace F φ s' p₂ q'} {m : ℕ} (hu : ∀ k, k ≠ m → u.block k = 0)
    (hv : ∀ k, k ≠ m → v.block k = 0) (j : ℕ) :
    (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) = 0 := by
  rcases eq_or_ne j m with rfl | hjm
  · rw [lowPass_eq_ite_of_block_eq_zero hv, ite_eq_right (by omega), Lp.smul_zero]
  · rw [hu j hjm, Lp.zero_smul]

/-- **The terms of the resonant part of two factors at the same frequency.** If `u` and `v` each
have only the block of index `m`, then the `j`-th term `Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` of `R(u, v)`
is `Δₘ u · Δₘ v` for `j = m` and vanishes otherwise. -/
theorem block_smul_sum_block_eq_ite_of_block_eq_zero (N : ℕ) {u : BesovSpace ℂ φ s p₁ q}
    {v : BesovSpace F φ s' p₂ q'} {m : ℕ} (hu : ∀ k, k ≠ m → u.block k = 0)
    (hv : ∀ k, k ≠ m → v.block k = 0) (j : ℕ) :
    (u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k : Lp F r (volume : Measure E)) =
      if j = m then (u.block m • v.block m : Lp F r (volume : Measure E)) else 0 := by
  split_ifs with hjm
  · subst hjm
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_Icc.2 ⟨Nat.sub_le j N, Nat.le_add_right j N⟩)
      fun k _ hk ↦ hv k hk]
  · rw [hu j hjm, Lp.zero_smul]

/-- **The resonant part of two factors at the same frequency is their product.** If `u` and `v`
each have only the block of index `m`, then for every gap `N` the resonant part
`R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` is the product `Δₘ u · Δₘ v`, while both paraproducts
vanish term by term (`TauCeti.BesovSpace.lowPass_smul_block_eq_zero_of_block_eq_zero`,
`TauCeti.BesovSpace.block_smul_lowPass_eq_zero_of_block_eq_zero`). -/
theorem hasSum_block_smul_sum_block_of_block_eq_zero [Fact (1 ≤ r)] (N : ℕ)
    {u : BesovSpace ℂ φ s p₁ q}
    {v : BesovSpace F φ s' p₂ q'} {m : ℕ} (hu : ∀ k, k ≠ m → u.block k = 0)
    (hv : ∀ k, k ≠ m → v.block k = 0) :
    HasSum (fun j ↦ ((u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
        Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      ((u.block m • v.block m : Lp F r (volume : Measure E)) : 𝓢'(E, F)) := by
  simp_rw [block_smul_sum_block_eq_ite_of_block_eq_zero N hu hv, apply_ite (fun f :
    Lp F r (volume : Measure E) ↦ (f : 𝓢'(E, F))), Lp.toTemperedDistribution_zero]
  exact hasSum_ite_eq m _

end SingleBlock

section PlaneWave

/-- **The blocks of a plane wave of dyadic frequency.** If the tempered distribution of
`u ∈ B^s_{∞,q}` is the plane wave `e_ξ = 𝓕⁻ δ_ξ` with `2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`, then
`Δ_{j+1} u` is the bounded function `x ↦ 𝐞 ⟪x, ξ⟫` and all other blocks of `u` vanish. -/
theorem block_eq_ite_of_toDistr_eq_fourierInv_delta {u : BesovSpace ℂ φ s ∞ q} {ξ : E}
    (hu : u.toDistr = 𝓕⁻ (delta ξ)) {j : ℕ} (h₁ : 2 ^ j * φ.rOut ≤ ‖ξ‖)
    (h₂ : ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rIn) (k : ℕ) :
    u.block k = if k = j + 1 then (memLp_top_fourierChar_inner ξ).toLp _ else 0 :=
  Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, hu, littlewoodPaleyBlock_fourierInv_delta_of_le_norm_of_norm_le φ h₁ h₂]
    split_ifs
    · exact (TauCeti.toTemperedDistribution_toLp_fourierChar_inner ξ).symm
    · simp

/-- **A plane wave of dyadic frequency lies in every Hölder–Zygmund space.** If
`2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`, then the plane wave `e_ξ = 𝓕⁻ δ_ξ` lies in `B^s_{∞,q}` for
every `s` and `q`. -/
theorem _root_.TemperedDistribution.memBesov_fourierInv_delta {ξ : E} {j : ℕ}
    (h₁ : 2 ^ j * φ.rOut ≤ ‖ξ‖) (h₂ : ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rIn) (s : ℝ) (q : ℝ≥0∞) :
    (𝓕⁻ (delta ξ) : 𝓢'(E, ℂ)).MemBesov φ s ∞ q :=
  memBesov_of_littlewoodPaleyBlock_eq_ite (m := j + 1) (p := ∞)
    (f := (memLp_top_fourierChar_inner ξ).toLp _) fun k ↦ by
      rw [littlewoodPaleyBlock_fourierInv_delta_of_le_norm_of_norm_le φ h₁ h₂,
        TauCeti.toTemperedDistribution_toLp_fourierChar_inner]

/-- **Two plane waves at the same frequency: the resonant term carries the product**
(Bahouri–Chemin–Danchin, §2.6). Let `2^j φ.rOut ≤ ‖ξ‖ ≤ 2^{j+1} φ.rIn`, and let
`u ∈ B^s_{∞,q}` and `v ∈ B^{s'}_{∞,q'}` both be the plane wave `e_ξ`, which is its own block
`Δ_{j+1}`. Then for every gap `N` the terms of both paraproducts `T_u v` and `T_v u` vanish
(`TauCeti.BesovSpace.lowPass_smul_block_eq_zero_of_block_eq_zero`,
`TauCeti.BesovSpace.block_smul_lowPass_eq_zero_of_block_eq_zero`), and the resonant part
`R(u, v)` is the whole product `e_ξ · e_ξ = e_{2ξ}`. -/
theorem hasSum_block_smul_sum_block_of_toDistr_eq_fourierInv_delta (N : ℕ)
    {u : BesovSpace ℂ φ s ∞ q} {v : BesovSpace ℂ φ s' ∞ q'} {ξ : E}
    (hu : u.toDistr = 𝓕⁻ (delta ξ)) (hv : v.toDistr = 𝓕⁻ (delta ξ)) {j : ℕ}
    (h₁ : 2 ^ j * φ.rOut ≤ ‖ξ‖) (h₂ : ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rIn) :
    HasSum (fun k ↦ ((u.block k • ∑ l ∈ Finset.Icc (k - N) (k + N), v.block l :
        Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E, ℂ))) (𝓕⁻ (delta ((2 : ℝ) • ξ))) := by
  have hu' := block_eq_ite_of_toDistr_eq_fourierInv_delta hu h₁ h₂
  have hv' := block_eq_ite_of_toDistr_eq_fourierInv_delta hv h₁ h₂
  have hm : (u.block (j + 1) • v.block (j + 1) : Lp ℂ ∞ (volume : Measure E)) =
      (memLp_top_fourierChar_inner ((2 : ℝ) • ξ)).toLp _ := by
    simp only [hu', hv', ↓reduceIte]
    rw [toLp_fourierChar_inner_smul_toLp_fourierChar_inner, two_smul]
  convert hasSum_block_smul_sum_block_of_block_eq_zero (r := ∞) (u := u) (v := v) (m := j + 1) N
    (fun k hk ↦ by simp only [hu', hk, ↓reduceIte]) (fun k hk ↦ by simp only [hv', hk, ↓reduceIte])
    using 1
  rw [hm, TauCeti.toTemperedDistribution_toLp_fourierChar_inner]

end PlaneWave

section Constant

variable {u : BesovSpace ℂ φ s ∞ q} (hu : u.toDistr = (volume : Measure E).toTemperedDistribution)
  (N : ℕ) (v : BesovSpace F φ s' p q')
include hu

/-- **The paraproduct `T_1 v`, term by term.** If `u` is the constant `1`, then the `j`-th term
`S_{j-N} u · Δⱼ v` of `T_u v` is `Δⱼ v` for `j > N` and vanishes for `j ≤ N`. -/
theorem lowPass_smul_block_eq_ite_of_toDistr_eq_volume (j : ℕ) :
    (u.lowPass (j - N) • v.block j : Lp F p (volume : Measure E)) =
      if N < j then v.block j else 0 := by
  rw [lowPass_eq_ite_of_block_eq_zero (m := 0)
    (fun k hk ↦ by rw [block_eq_ite_of_toDistr_eq_volume hu, ite_eq_right hk])]
  by_cases hj : N < j
  · rw [ite_eq_left (by omega), ite_eq_left hj, block_eq_ite_of_toDistr_eq_volume hu,
      ite_eq_left rfl, Lp.one_smul]
  · rw [ite_eq_right (by omega), ite_eq_right hj, Lp.zero_smul]

/-- **The paraproduct `T_v 1` vanishes term by term.** If `u` is the constant `1`, then
`Δⱼ u · S_{j-N} v = 0` for every `j`: the only nonzero block of `u` is `Δ₀ u`, and `S_0 v = 0`. -/
theorem block_smul_lowPass_eq_zero_of_toDistr_eq_volume (j : ℕ) :
    (u.block j • v.lowPass (j - N) : Lp F p (volume : Measure E)) = 0 := by
  rw [block_eq_ite_of_toDistr_eq_volume hu]
  split_ifs with hj
  · rw [hj, Nat.zero_sub, lowPass_zero_right, Lp.smul_zero]
  · rw [Lp.zero_smul]

/-- **The resonant part `R(1, v)`, term by term.** If `u` is the constant `1`, then the `j`-th
term `Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` of `R(u, v)` is `∑_{k ≤ N} Δₖ v` for `j = 0` and vanishes
otherwise. -/
theorem block_smul_sum_block_eq_ite_of_toDistr_eq_volume (j : ℕ) :
    (u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k : Lp F p (volume : Measure E)) =
      if j = 0 then ∑ k ∈ Finset.range (N + 1), v.block k else 0 := by
  rw [block_eq_ite_of_toDistr_eq_volume hu]
  split_ifs with hj
  · rw [Lp.one_smul, hj, Nat.zero_sub, zero_add, Nat.range_succ_eq_Icc_zero]
  · rw [Lp.zero_smul]

/-- **The resonant part `R(1, v)`** (Bahouri–Chemin–Danchin, §2.6). If `u` is the constant `1`,
then `R(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` is `∑_{k ≤ N} Δₖ v`. -/
theorem hasSum_block_smul_sum_block_of_toDistr_eq_volume :
    HasSum (fun j ↦ ((u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
        Lp F p (volume : Measure E)) : 𝓢'(E, F)))
      (∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ k v.toDistr) := by
  simp_rw [block_smul_sum_block_eq_ite_of_toDistr_eq_volume hu, apply_ite (fun f :
    Lp F p (volume : Measure E) ↦ (f : 𝓢'(E, F))), Lp.toTemperedDistribution_zero,
    Lp.toTemperedDistribution_sum, coe_block]
  exact hasSum_ite_eq 0 _

variable [Fact (1 ≤ q')]

/-- **The paraproduct `T_1 v`** (Bahouri–Chemin–Danchin, §2.6). If `u` is the constant `1`, then
`T_u v = ∑ⱼ S_{j-N} u · Δⱼ v` is `v - ∑_{k ≤ N} Δₖ v = ∑_{j > N} Δⱼ v`. -/
theorem hasSum_lowPass_smul_block_of_toDistr_eq_volume :
    HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j : Lp F p (volume : Measure E)) : 𝓢'(E, F)))
      (v.toDistr - ∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ k v.toDistr) := by
  have hlow : HasSum (fun j ↦ if j < N + 1 then littlewoodPaleyBlock F φ j v.toDistr else 0)
      (∑ k ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ k v.toDistr) := by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := Finset.range (N + 1))
      (f := fun j ↦ if j < N + 1 then littlewoodPaleyBlock F φ j v.toDistr else 0)
      fun j hj ↦ ite_eq_right (by simpa using hj)
    rwa [Finset.sum_congr rfl fun k hk ↦ ite_eq_left (Finset.mem_range.1 hk)] at h
  refine ((hasSum_littlewoodPaleyBlock_toDistr v).sub hlow).congr_fun fun j ↦ ?_
  rw [lowPass_smul_block_eq_ite_of_toDistr_eq_volume hu]
  split_ifs <;> first | omega | simp [coe_block]

/-- **Bony's decomposition of `1 · v`** (Bahouri–Chemin–Danchin, §2.6). If `u` is the constant
`1`, then the three series `T_u v = ∑_{j > N} Δⱼ v`, `T_v u = 0` and `R(u, v) = ∑_{k ≤ N} Δₖ v`
add up to `v`: each block `Δₖ v` is counted exactly once. -/
theorem hasSum_paraproduct_add_paraproduct_add_resonant_of_toDistr_eq_volume :
    HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j + u.block j • v.lowPass (j - N) +
        u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :
          Lp F p (volume : Measure E)) : 𝓢'(E, F))) v.toDistr := by
  have h := ((hasSum_lowPass_smul_block_of_toDistr_eq_volume hu N v).add hasSum_zero).add
    (hasSum_block_smul_sum_block_of_toDistr_eq_volume hu N v)
  rw [add_zero, sub_add_cancel] at h
  refine h.congr_fun fun j ↦ ?_
  rw [block_smul_lowPass_eq_zero_of_toDistr_eq_volume hu, Lp.toTemperedDistribution_add,
    Lp.toTemperedDistribution_add, Lp.toTemperedDistribution_zero]

end Constant

end TauCeti.BesovSpace
