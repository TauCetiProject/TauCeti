/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Delta

/-!
# Little Besov spaces

At the endpoint `q = ∞`, the inhomogeneous Besov space `B^s_{p,∞}(E, F)` consists of tempered
distributions whose weighted Littlewood–Paley block norms `2^{js} ‖Δⱼ u‖_p` are bounded. Unlike
`B^s_{p,q}` with `q < ∞`, the dyadic partial sums `S_N u = ∑_{j < N} Δⱼ u` need not converge in the
`B^s_{p,∞}` norm, and smooth functions are not dense in positive dimension.

The **little Besov space** `b^s_{p,∞}(E, F)` (`TemperedDistribution.MemLittleBesov` as a predicate
on `𝓢'(E, F)`, and `TauCeti.BesovSpace.littleBesov` as a `ℂ`-submodule of `B^s_{p,∞}(E, F)`)
consists of those `u ∈ B^s_{p,∞}(E, F)` whose weighted block norms vanish at high frequencies:
`2^{js} ‖Δⱼ u‖_p → 0` as `j → ∞` (replacing `ℓ^∞` by `c₀`).

## Main declarations and results

* `TemperedDistribution.MemLittleBesov` and `TauCeti.BesovSpace.littleBesov`: the unbundled
  predicate on `𝓢'(E, F)` and the bundled submodule of `B^s_{p,∞}(E, F)`. Its isometric inclusion
  into `B^s_{p,∞}(E, F)` is `(littleBesov F φ s p).subtypeₗᵢ`.
* `TauCeti.BesovSpace.isClosed_littleBesov` and `CompleteSpace (littleBesov F φ s p)`: the little
  Besov space is closed in `B^s_{p,∞}(E, F)`, hence a Banach space.
* `TauCeti.BesovSpace.mem_littleBesov_iff_tendsto_partialSumCLM`: for all `1 ≤ p ≤ ∞`, `u` lies in
  `b^s_{p,∞}(E, F)` if and only if `S_N u → u` in `B^s_{p,∞}(E, F)` as `N → ∞`.
* `TauCeti.BesovSpace.littleBesov_eq_closure_range_inclusionOfLT`: for all `1 ≤ p, q ≤ ∞` and
  `s < s'`, `b^s_{p,∞}(E, F)` is the closure in `B^s_{p,∞}(E, F)` of `B^{s'}_{p,q}(E, F)`.
* Independence and invariance: `b^s_{p,∞}` is independent of the Littlewood–Paley bump `φ` up to
  Banach-space isomorphism (`TauCeti.BesovSpace.littleBesovBumpEquiv`), and is preserved by the
  Bernstein embedding (`TauCeti.BesovSpace.inclusionOfExponentLE_mem_littleBesov`), fiberwise
  continuous linear maps (`TauCeti.BesovSpace.postcomp_mem_littleBesov`), Fourier multipliers and
  Bessel-potential lifting (`TauCeti.BesovSpace.fourierMultiplierCLM_mem_littleBesov`,
  `TauCeti.BesovSpace.littleBesovBesselPotentialEquiv`), and multiplication by smooth functions of
  temperate growth with bounded derivatives up to order `⌊|s|⌋₊ + 1`
  (`TauCeti.BesovSpace.smulLeftCLM_mem_littleBesov`).
* `TauCeti.BesovSpace.littleBesov_eq_closure_range_toBesovSpaceCLM`,
  `TauCeti.BesovSpace.littleBesov_eq_closure_image_hasCompactSupport`,
  `SchwartzMap.denseRange_toLittleBesovCLM`: for `1 ≤ p < ∞`, `b^s_{p,∞}(E, F)` is the closure in
  `B^s_{p,∞}(E, F)` of `𝓢(E, F)` and of compactly supported smooth functions.
* `TemperedDistribution.memLittleBesov_delta_zero_iff`, `TauCeti.BesovSpace.littleBesov_ne_top`, and
  `SchwartzMap.not_denseRange_toBesovSpaceCLM_top`: in positive dimension `n ≥ 1`, `δ₀ ∈ b^s_{p,∞}`
  if and only if `s < -n (1 - 1/p)` (failing at the critical exponent `s = -n (1 - 1/p)` where
  `δ₀ ∈ B^s_{p,∞}`), so for every `s ∈ ℝ`, `1 ≤ p ≤ ∞` and nontrivial `F`, `b^s_{p,∞}(E, F)` is a
  proper closed subspace of `B^s_{p,∞}(E, F)` and `𝓢(E, F)` is not dense in `B^s_{p,∞}(E, F)`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 3.4.2(c) and
  Theorem 6.2.4.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7.
-/

public section

noncomputable section

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace TemperedDistribution

section Predicate

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **little Besov space** `b^s_{p,∞}` built from the
Littlewood–Paley partition of `φ` if every block `Δⱼ u` is an `Lᵖ` function `fⱼ` and the weighted
norms `2^{js} ‖fⱼ‖_p` tend to `0` as `j → ∞`. -/
def MemLittleBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ f : ℕ → Lp F p (volume : Measure E),
    (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
      Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) atTop (𝓝 0)

variable {φ s p}

theorem memLittleBesov_iff {u : 𝓢'(E, F)} :
    u.MemLittleBesov φ s p ↔ ∃ f : ℕ → Lp F p (volume : Measure E),
      (∀ j, littlewoodPaleyBlock F φ j u = f j) ∧
        Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) atTop (𝓝 0) :=
  Iff.rfl

/-- If the Littlewood–Paley blocks `Δⱼ u` are the `Lᵖ` functions `fⱼ`, then `u ∈ b^s_{p,∞}` if and
only if `2^{js} ‖fⱼ‖_p → 0` as `j → ∞`. -/
theorem memLittleBesov_iff_tendsto {u : 𝓢'(E, F)} {f : ℕ → Lp F p (volume : Measure E)}
    (hf : ∀ j, littlewoodPaleyBlock F φ j u = f j) :
    u.MemLittleBesov φ s p ↔ Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) atTop (𝓝 0) := by
  refine ⟨fun ⟨g, hg, ht⟩ ↦ ?_, fun ht ↦ ⟨f, hf, ht⟩⟩
  have hgf : g = f := funext fun j ↦
    Lp.toTemperedDistribution_injective (by dsimp only; rw [← hg j, hf j])
  rwa [hgf] at ht

/-- Every element of the little Besov space `b^s_{p,∞}` lies in `B^s_{p,∞}`: a sequence tending to
`0` is bounded. -/
theorem MemLittleBesov.memBesov {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    u.MemBesov φ s p ∞ := by
  obtain ⟨f, hf, ht⟩ := hu
  exact memBesov_iff.2 ⟨f, hf, memℓp_infty ht.norm.bddAbove_range⟩

theorem MemLittleBesov.zero : (0 : 𝓢'(E, F)).MemLittleBesov φ s p :=
  ⟨0, fun j ↦ by simp, by simp⟩

theorem MemLittleBesov.add {u v : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (hv : v.MemLittleBesov φ s p) : (u + v).MemLittleBesov φ s p := by
  obtain ⟨f, hf, htf⟩ := hu
  obtain ⟨g, hg, htg⟩ := hv
  refine ⟨f + g, fun j ↦ by rw [Pi.add_apply, Lp.toTemperedDistribution_add, ← hf, ← hg, map_add],
    squeeze_zero (fun _ ↦ by positivity) (fun j ↦ ?_) (by simpa using htf.add htg)⟩
  calc (2 : ℝ) ^ (s * j) * ‖(f + g) j‖
      ≤ 2 ^ (s * j) * (‖f j‖ + ‖g j‖) := by gcongr; exact norm_add_le _ _
    _ = 2 ^ (s * j) * ‖f j‖ + 2 ^ (s * j) * ‖g j‖ := mul_add _ _ _

theorem MemLittleBesov.smul {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) (c : ℂ) :
    (c • u).MemLittleBesov φ s p := by
  obtain ⟨f, hf, ht⟩ := hu
  refine ⟨c • f, fun j ↦ by rw [Pi.smul_apply, Lp.toTemperedDistribution_smul, ← hf, map_smul], ?_⟩
  have hc := ht.const_mul ‖c‖
  rw [mul_zero] at hc
  refine hc.congr fun j ↦ ?_
  rw [Pi.smul_apply, norm_smul]
  ring

theorem MemLittleBesov.neg {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    (-u).MemLittleBesov φ s p := by
  simpa using hu.smul (-1)

theorem MemLittleBesov.sub {u v : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p)
    (hv : v.MemLittleBesov φ s p) : (u - v).MemLittleBesov φ s p := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- **Monotonicity of little Besov spaces.** For `s' ≤ s`, `b^s_{p,∞} ⊆ b^{s'}_{p,∞}`. -/
theorem MemLittleBesov.mono {u : 𝓢'(E, F)} {s' : ℝ} (hu : u.MemLittleBesov φ s p) (hs : s' ≤ s) :
    u.MemLittleBesov φ s' p := by
  obtain ⟨f, hf, ht⟩ := hu
  refine ⟨f, hf, squeeze_zero (fun _ ↦ by positivity) (fun j ↦ ?_) ht⟩
  gcongr
  exact one_le_two

/-- **Every `B^s_{p,q}` with `q < ∞` lies in `b^s_{p,∞}`.** -/
theorem MemBesov.memLittleBesov_of_ne_top {u : 𝓢'(E, F)} {q : ℝ≥0∞} (hu : u.MemBesov φ s p q)
    (hq : q ≠ ∞) : u.MemLittleBesov φ s p := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine ⟨f, hf, ?_⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Nat.cofinite_eq_atTop ▸ (memℓp_zero_iff.1 hmem).compl_mem_cofinite] with j hj
    exact (not_not.1 hj).symm
  · have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
    have ht := (hmem.summable hqpos).tendsto_atTop_zero
    have hcont : Tendsto (fun x : ℝ ↦ x ^ q.toReal⁻¹) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow (inv_ne_zero hqpos.ne')] using
        (Real.continuous_rpow_const (inv_nonneg.2 hqpos.le)).tendsto 0
    refine (hcont.comp ht).congr fun j ↦ ?_
    dsimp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_mul (by positivity),
      mul_inv_cancel₀ hqpos.ne', Real.rpow_one]

/-- **Strict order inclusion into little Besov spaces.** For `s' < s` and *every* fine index `q`
(including `q = ∞`), `B^s_{p,q} ⊆ b^{s'}_{p,∞}`: a strict loss of smoothness turns bounded weighted
blocks into geometrically decaying ones. -/
theorem MemBesov.memLittleBesov_of_lt {u : 𝓢'(E, F)} {s' : ℝ} {q : ℝ≥0∞}
    (hu : u.MemBesov φ s p q) (hs : s' < s) : u.MemLittleBesov φ s' p :=
  (hu.of_lt hs one_ne_zero).memLittleBesov_of_ne_top ENNReal.one_ne_top

end Predicate

end TemperedDistribution

namespace SchwartzMap

/-- Every Schwartz function lies in every little Besov space `b^s_{p,∞}` (`1 ≤ p ≤ ∞`). -/
theorem memLittleBesov (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    (f : 𝓢'(E, F)).MemLittleBesov φ s p :=
  (f.memBesov φ s p one_ne_zero).memLittleBesov_of_ne_top ENNReal.one_ne_top

end SchwartzMap

namespace TauCeti.BesovSpace

open TemperedDistribution

section Submodule

variable (F) in
/-- **The little Besov space** `b^s_{p,∞}(E, F)`, as a `ℂ`-submodule of `B^s_{p,∞}(E, F)`: the
distributions whose weighted Littlewood–Paley block norms `2^{js} ‖Δⱼ u‖_p` tend to `0` as `j → ∞`.
Its isometric inclusion into `B^s_{p,∞}(E, F)` is `(littleBesov F φ s p).subtypeₗᵢ`. -/
def littleBesov (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℂ (BesovSpace F φ s p ∞) where
  carrier := {u | u.toDistr.MemLittleBesov φ s p}
  zero_mem' := by rw [Set.mem_ofPred_eq, toDistr_zero]; exact MemLittleBesov.zero
  add_mem' hu hv := by rw [Set.mem_ofPred_eq, toDistr_add]; exact hu.add hv
  smul_mem' c _ hu := by rw [Set.mem_ofPred_eq, toDistr_smul]; exact hu.smul c

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp]
theorem mem_littleBesov_iff {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ u.toDistr.MemLittleBesov φ s p :=
  Iff.rfl

/-- A tempered distribution `u ∈ B^s_{p,∞}` bundled into `BesovSpace` lies in `littleBesov` if and
only if `u` satisfies `MemLittleBesov`. -/
theorem _root_.TemperedDistribution.MemBesov.toBesovSpace_mem_littleBesov_iff {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ s p ∞) :
    hu.toBesovSpace ∈ littleBesov F φ s p ↔ u.MemLittleBesov φ s p := by
  rw [mem_littleBesov_iff, hu.toDistr_toBesovSpace]

/-- `u ∈ b^s_{p,∞}` if and only if `2^{js} ‖Δⱼ u‖_p → 0` as `j → ∞`. -/
theorem mem_littleBesov_iff_tendsto {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) :=
  memLittleBesov_iff_tendsto fun j ↦ (coe_block u j).symm

/-- `u ∈ b^s_{p,∞}` if and only if `‖u.weightedBlocks j‖ → 0` as `j → ∞`. -/
theorem mem_littleBesov_iff_weightedBlocks {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun j : ℕ ↦ ‖u.weightedBlocks j‖) atTop (𝓝 0) := by
  simp_rw [mem_littleBesov_iff_tendsto, norm_weightedBlocks_apply]

/-- **The little Besov space is closed** in `B^s_{p,∞}(E, F)`: uniform limits (in the `ℓ^∞`
supremum over `j`) of sequences vanishing at infinity still vanish at infinity. -/
theorem isClosed_littleBesov : IsClosed (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) := by
  refine isClosed_of_closure_subset fun u hu ↦ mem_littleBesov_iff_tendsto.2 ?_
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.1 hu (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mem_littleBesov_iff_tendsto.1 hv) (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [dist_eq_norm] at huv
  have hvj := hN j hj
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hvj ⊢
  have hblk : u.block j = (u - v).block j + v.block j := by rw [block_sub, sub_add_cancel]
  calc (2 : ℝ) ^ (s * j) * ‖u.block j‖
      ≤ 2 ^ (s * j) * (‖(u - v).block j‖ + ‖v.block j‖) := by
        rw [hblk]; gcongr; exact norm_add_le _ _
    _ = 2 ^ (s * j) * ‖(u - v).block j‖ + 2 ^ (s * j) * ‖v.block j‖ := mul_add _ _ _
    _ ≤ ‖u - v‖ + 2 ^ (s * j) * ‖v.block j‖ :=
        add_le_add_left (rpow_mul_norm_block_le (u - v) j) _
    _ < ε / 2 + ε / 2 := add_lt_add huv hvj
    _ = ε := add_halves ε

/-- **The little Besov space is a Banach space.** -/
instance : CompleteSpace (littleBesov F φ s p) :=
  isClosed_littleBesov.completeSpace_coe

/-- For `s' ≤ s` and `q < ∞`, the inclusion `B^s_{p,q} → B^{s'}_{p,∞}` lands in `b^{s'}_{p,∞}`. -/
theorem inclusion_mem_littleBesov {s' : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] (hs : s' ≤ s) (hq : q ≠ ∞)
    (u : BesovSpace F φ s p q) :
    inclusion F φ p hs le_top u ∈ littleBesov F φ s' p := by
  rw [mem_littleBesov_iff, toDistr_inclusion]
  exact (u.memBesov_toDistr.memLittleBesov_of_ne_top hq).mono hs

/-- For `s' < s` and any `1 ≤ q ≤ ∞`, the inclusion `B^s_{p,q} → B^{s'}_{p,∞}` lands in
`b^{s'}_{p,∞}`. -/
theorem inclusionOfLT_mem_littleBesov {s' : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] (hs : s' < s)
    (u : BesovSpace F φ s p q) :
    inclusionOfLT F φ p q ∞ hs u ∈ littleBesov F φ s' p := by
  rw [mem_littleBesov_iff, toDistr_inclusionOfLT]
  exact u.memBesov_toDistr.memLittleBesov_of_lt hs

/-- Every Schwartz function embeds into `b^s_{p,∞}(E, F)`. -/
theorem toBesovSpaceCLM_mem_littleBesov (f : 𝓢(E, F)) :
    f.toBesovSpaceCLM φ s p ∞ ∈ littleBesov F φ s p := by
  simp [f.memLittleBesov φ s p]

/-- Every dyadic partial sum `S_N u` lies in `b^s_{p,∞}(E, F)`. -/
theorem partialSumCLM_mem_littleBesov (N : ℕ) (u : BesovSpace F φ s p ∞) :
    partialSumCLM F φ s p ∞ N u ∈ littleBesov F φ s p := by
  rw [mem_littleBesov_iff]
  exact (memBesov_toDistr_partialSumCLM s 1 N u).memLittleBesov_of_ne_top ENNReal.one_ne_top

/-- **Dyadic partial-sum characterization of `b^s_{p,∞}`.** For every `1 ≤ p ≤ ∞`, an element
`u ∈ B^s_{p,∞}(E, F)` lies in the little Besov space `b^s_{p,∞}(E, F)` if and only if its dyadic
partial sums `S_N u` converge to `u` in the `B^s_{p,∞}` norm as `N → ∞`. -/
theorem mem_littleBesov_iff_tendsto_partialSumCLM {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun N ↦ partialSumCLM F φ s p ∞ N u) atTop (𝓝 u) :=
  ⟨fun hu ↦ tendsto_partialSumCLM_top_of_tendsto (mem_littleBesov_iff_tendsto.1 hu),
    fun ht ↦ isClosed_littleBesov.mem_of_tendsto ht
      (Eventually.of_forall fun N ↦ partialSumCLM_mem_littleBesov N u)⟩

/-- **Closure of higher-regularity Besov spaces (Bergh–Löfström, Theorem 3.4.2(c)).** For all
`1 ≤ p, q ≤ ∞` and `s < s'`, the little Besov space `b^s_{p,∞}(E, F)` is the closure in
`B^s_{p,∞}(E, F)` of the image of `B^{s'}_{p,q}(E, F)`. -/
theorem littleBesov_eq_closure_range_inclusionOfLT {s' : ℝ} (hs : s < s') (q : ℝ≥0∞)
    [Fact (1 ≤ q)] :
    (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
      closure (Set.range (inclusionOfLT F φ p q ∞ hs)) := by
  refine Set.Subset.antisymm (fun u hu ↦ ?_) ?_
  · exact mem_closure_of_tendsto (mem_littleBesov_iff_tendsto_partialSumCLM.1 hu)
      (Eventually.of_forall fun N ↦ partialSumCLM_mem_range_inclusionOfLT hs q N u)
  · refine closure_minimal ?_ isClosed_littleBesov
    rintro _ ⟨v, rfl⟩
    exact inclusionOfLT_mem_littleBesov hs v

end Submodule

section Invariance

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any continuous linear map `B^s_{p,∞}(E, F) →L[ℂ] B^{s'}_{p',∞}(E, G)` that intertwines
`inclusionOfLT` from some higher-regularity spaces `r > s` and `r' > s'` maps `b^s_{p,∞}(E, F)`
into `b^{s'}_{p',∞}(E, G)`: `B^r_{p,∞}` is dense in `b^s_{p,∞}`, `B^{r'}_{p',∞}` lands inside
`b^{s'}_{p',∞}`, and `b^{s'}_{p',∞}` is closed. -/
private theorem map_mem_littleBesov_of_inclusionOfLT
    {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' : ℝ≥0∞} [Fact (1 ≤ p')]
    (T : BesovSpace F φ s p ∞ →L[ℂ] BesovSpace G φ' s' p' ∞)
    {r r' : ℝ} (hr : s < r) (hr' : s' < r')
    (hT : ∀ v : BesovSpace F φ r p ∞,
      ∃ w : BesovSpace G φ' r' p' ∞,
        T (inclusionOfLT F φ p ∞ ∞ hr v) = inclusionOfLT G φ' p' ∞ ∞ hr' w)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    T u ∈ littleBesov G φ' s' p' := by
  have hu' : u ∈ closure (Set.range (inclusionOfLT F φ p ∞ ∞ hr)) := by
    rwa [← littleBesov_eq_closure_range_inclusionOfLT hr ∞]
  refine closure_minimal ?_ isClosed_littleBesov
    (image_closure_subset_closure_image T.continuous (Set.mem_image_of_mem T hu'))
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := hT v
  rw [hw]
  exact inclusionOfLT_mem_littleBesov hr' w

/-- `bumpEquiv` maps `b^s_{p,∞}` into `b^s_{p,∞}` for any other bump `φ'`. -/
theorem bumpEquiv_mem_littleBesov (φ' : ContDiffBump (0 : E)) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    bumpEquiv F φ φ' s p ∞ u ∈ littleBesov F φ' s p :=
  map_mem_littleBesov_of_inclusionOfLT (bumpEquiv F φ φ' s p ∞ : _ →L[ℂ] _)
    (lt_add_one s) (lt_add_one s)
    (fun v ↦ ⟨bumpEquiv F φ φ' (s + 1) p ∞ v, ext (by simp)⟩) hu

theorem bumpEquiv_mem_littleBesov_iff (φ' : ContDiffBump (0 : E)) {u : BesovSpace F φ s p ∞} :
    bumpEquiv F φ φ' s p ∞ u ∈ littleBesov F φ' s p ↔ u ∈ littleBesov F φ s p :=
  ⟨fun h ↦ by simpa using bumpEquiv_mem_littleBesov φ h, bumpEquiv_mem_littleBesov φ'⟩

/-- **Independence of the bump function.** A tempered distribution in the little Besov space
`b^s_{p,∞}` built from `φ` lies in the little Besov space `b^s_{p,∞}` built from any other bump
function `φ'`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.of_bump {u : 𝓢'(E, F)}
    (hu : u.MemLittleBesov φ s p) (φ' : ContDiffBump (0 : E)) :
    u.MemLittleBesov φ' s p := by
  have h := bumpEquiv_mem_littleBesov φ' (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_bumpEquiv, hu.memBesov.toDistr_toBesovSpace] at h

variable (F) in
/-- **Equivalence of little Besov norms across Littlewood–Paley partitions.** Two smooth bump
functions `φ` and `φ'` define canonically isomorphic Banach spaces `b^s_{p,∞}`. -/
def littleBesovBumpEquiv (φ φ' : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    littleBesov F φ s p ≃L[ℂ] littleBesov F φ' s p :=
  (bumpEquiv F φ φ' s p ∞).ofSubmodules _ _ <| by
    ext v
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact ⟨fun ⟨u, hu, huv⟩ ↦ huv ▸ bumpEquiv_mem_littleBesov φ' hu,
      fun hv ↦ ⟨_, bumpEquiv_mem_littleBesov φ hv, by
        rw [← bumpEquiv_symm, ContinuousLinearEquiv.symm_apply_apply]⟩⟩

@[simp]
theorem coe_littleBesovBumpEquiv_apply (φ' : ContDiffBump (0 : E)) (u : littleBesov F φ s p) :
    (littleBesovBumpEquiv F φ φ' s p u : BesovSpace F φ' s p ∞) = bumpEquiv F φ φ' s p ∞ u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem littleBesovBumpEquiv_symm (φ' : ContDiffBump (0 : E)) :
    (littleBesovBumpEquiv F φ φ' s p).symm = littleBesovBumpEquiv F φ' φ s p :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ Subtype.ext <| by simp [littleBesovBumpEquiv]

/-- **The Bernstein embedding on little Besov spaces.** For `p ≤ r`,
`b^s_{p,∞} ⊆ b^{s - n (1/p - 1/r)}_{r,∞}` where `n = finrank ℝ E`. -/
theorem inclusionOfExponentLE_mem_littleBesov {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpr : p ≤ r)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    inclusionOfExponentLE F φ ∞ hpr u ∈
      littleBesov F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r :=
  map_mem_littleBesov_of_inclusionOfLT (inclusionOfExponentLE F φ ∞ hpr) (lt_add_one s)
    (by linarith : s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹) <
      (s + 1) - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹))
    (fun v ↦ ⟨inclusionOfExponentLE F φ ∞ hpr v, ext (by simp)⟩) hu

/-- Unbundled Bernstein embedding on `MemLittleBesov`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.mono_exponent {u : 𝓢'(E, F)} {r : ℝ≥0∞}
    [Fact (1 ≤ r)] (hu : u.MemLittleBesov φ s p) (hpr : p ≤ r) :
    u.MemLittleBesov φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r := by
  have h := inclusionOfExponentLE_mem_littleBesov hpr
    (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_inclusionOfExponentLE, hu.memBesov.toDistr_toBesovSpace] at h

/-- `BesovSpace.postcomp` maps `b^s_{p,∞}(E, F)` into `b^s_{p,∞}(E, G)`. -/
theorem postcomp_mem_littleBesov (L : F →L[ℂ] G) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    postcomp φ s p ∞ L u ∈ littleBesov G φ s p :=
  map_mem_littleBesov_of_inclusionOfLT (postcomp φ s p ∞ L) (lt_add_one s) (lt_add_one s)
    (fun v ↦ ⟨postcomp φ (s + 1) p ∞ L v, ext <| by ext ψ; simp⟩) hu

/-- Applying a continuous linear map `L : F →L[ℂ] G` to the values of a distribution in
`b^s_{p,∞}(E, F)` produces a distribution in `b^s_{p,∞}(E, G)`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.postcomp {u : 𝓢'(E, F)}
    (hu : u.MemLittleBesov φ s p) (L : F →L[ℂ] G) :
    MemLittleBesov φ s p (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u : 𝓢'(E, G)) := by
  have h := postcomp_mem_littleBesov L (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_postcomp, hu.memBesov.toDistr_toBesovSpace] at h

variable (φ s p) in
/-- A continuous linear equivalence `e : F ≃L[ℂ] G` on the fiber induces an isomorphism of little
Besov spaces `b^s_{p,∞}(E, F) ≃L[ℂ] b^s_{p,∞}(E, G)`. -/
def littleBesovPostcompEquiv (e : F ≃L[ℂ] G) :
    littleBesov F φ s p ≃L[ℂ] littleBesov G φ s p :=
  (postcompEquiv φ s p ∞ e).ofSubmodules _ _ <| by
    ext v
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      postcompEquiv_apply]
    exact ⟨fun ⟨u, hu, huv⟩ ↦ huv ▸ postcomp_mem_littleBesov (e : F →L[ℂ] G) hu,
      fun hv ↦ ⟨_, postcomp_mem_littleBesov (e.symm : G →L[ℂ] F) hv, by simp⟩⟩

@[simp]
theorem coe_littleBesovPostcompEquiv_apply (e : F ≃L[ℂ] G) (u : littleBesov F φ s p) :
    (littleBesovPostcompEquiv φ s p e u : BesovSpace G φ s p ∞) = postcompEquiv φ s p ∞ e u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem littleBesovPostcompEquiv_symm (e : F ≃L[ℂ] G) :
    (littleBesovPostcompEquiv φ s p e).symm = littleBesovPostcompEquiv φ s p e.symm :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦ Subtype.ext <| by simp [littleBesovPostcompEquiv]

open scoped ContDiff in
/-- **Fourier multipliers on little Besov spaces.** A smooth symbol `g` of order `m` maps
`b^s_{p,∞}` into `b^{s - m}_{p,∞}`. -/
theorem fourierMultiplierCLM_mem_littleBesov {g : E → ℂ} {m s' : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    (hs : s' = s - m) {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    fourierMultiplierCLM F φ p ∞ hg hgm hs u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov_of_inclusionOfLT (fourierMultiplierCLM F φ p ∞ hg hgm hs)
    (lt_add_one s) (lt_add_one s')
    (fun v ↦ ⟨fourierMultiplierCLM F φ p ∞ hg hgm (by linarith : s' + 1 = s + 1 - m) v,
      ext (by simp)⟩) hu

open scoped ContDiff in
/-- Unbundled Fourier multiplier theorem on `MemLittleBesov`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.fourierMultiplierCLM {g : E → ℂ} {m : ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hgm : ∀ i : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) :
    (TemperedDistribution.fourierMultiplierCLM F g u).MemLittleBesov φ (s - m) p := by
  have h := fourierMultiplierCLM_mem_littleBesov hg hgm rfl
    (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_fourierMultiplierCLM, hu.memBesov.toDistr_toBesovSpace] at h

/-- `besselPotentialEquiv` maps `b^s_{p,∞}` into `b^{s - t}_{p,∞}`. -/
theorem besselPotentialEquiv_mem_littleBesov (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    besselPotentialEquiv F φ p ∞ t hs u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov_of_inclusionOfLT (besselPotentialEquiv F φ p ∞ t hs : _ →L[ℂ] _)
    (lt_add_one s) (lt_add_one s')
    (fun v ↦ ⟨besselPotentialEquiv F φ p ∞ t (by linarith : s' + 1 = s + 1 - t) v,
      ext (by simp)⟩) hu

/-- The Bessel potential `J^t` maps `b^s_{p,∞}` to `b^{s - t}_{p,∞}`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.besselPotential {u : 𝓢'(E, F)}
    (hu : u.MemLittleBesov φ s p) (t : ℝ) :
    (besselPotential E F t u).MemLittleBesov φ (s - t) p := by
  have h := besselPotentialEquiv_mem_littleBesov t rfl
    (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_besselPotentialEquiv, hu.memBesov.toDistr_toBesovSpace] at h

/-- **The lifting property of little Besov spaces.** `J^t u ∈ b^s_{p,∞}` if and only if
`u ∈ b^{t + s}_{p,∞}`. -/
@[simp]
theorem _root_.TemperedDistribution.memLittleBesov_besselPotential_iff {u : 𝓢'(E, F)} {t : ℝ} :
    (besselPotential E F t u).MemLittleBesov φ s p ↔ u.MemLittleBesov φ (t + s) p :=
  ⟨fun h ↦ by simpa [add_comm s t] using h.besselPotential (-t),
    fun hu ↦ by simpa using hu.besselPotential t⟩

theorem besselPotentialEquiv_mem_littleBesov_iff (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    {u : BesovSpace F φ s p ∞} :
    besselPotentialEquiv F φ p ∞ t hs u ∈ littleBesov F φ s' p ↔ u ∈ littleBesov F φ s p := by
  subst hs
  simp [add_sub_cancel]

variable (F φ p) in
/-- **Bessel-potential lifting isomorphism on little Besov spaces.** For `s' = s - t`, `J^t`
restricts to a continuous linear equivalence `b^s_{p,∞}(E, F) ≃L[ℂ] b^{s'}_{p,∞}(E, F)`. -/
def littleBesovBesselPotentialEquiv (t : ℝ) {s s' : ℝ} (hs : s' = s - t) :
    littleBesov F φ s p ≃L[ℂ] littleBesov F φ s' p :=
  (besselPotentialEquiv F φ p ∞ t hs).ofSubmodules _ _ <| by
    ext v
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact ⟨fun ⟨u, hu, huv⟩ ↦ huv ▸ besselPotentialEquiv_mem_littleBesov t hs hu,
      fun hv ↦ ⟨_, besselPotentialEquiv_mem_littleBesov (-t)
        (by rw [hs, sub_neg_eq_add, sub_add_cancel]) hv, by
        rw [← besselPotentialEquiv_symm t hs, ContinuousLinearEquiv.apply_symm_apply]⟩⟩

@[simp]
theorem coe_littleBesovBesselPotentialEquiv_apply (t : ℝ) {s' : ℝ} (hs : s' = s - t)
    (u : littleBesov F φ s p) :
    (littleBesovBesselPotentialEquiv F φ p t hs u : BesovSpace F φ s' p ∞) =
      besselPotentialEquiv F φ p ∞ t hs u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

@[simp]
theorem littleBesovBesselPotentialEquiv_symm (t : ℝ) {s' : ℝ} (hs : s' = s - t) :
    (littleBesovBesselPotentialEquiv F φ p t hs).symm =
      littleBesovBesselPotentialEquiv F φ p (-t) (by rw [hs, sub_neg_eq_add, sub_add_cancel]) :=
  ContinuousLinearEquiv.ext <| funext fun _ ↦
    Subtype.ext <| by simp [littleBesovBesselPotentialEquiv]

/-- **Smooth multipliers of little Besov spaces.** Multiplication by a function `g : E → ℂ` of
temperate growth with bounded derivatives up to order `⌊|s|⌋₊ + 1` maps `b^s_{p,∞}(E, F)` into
itself. -/
theorem smulLeftCLM_mem_littleBesov {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    smulLeftCLM F φ s p ∞ g hg hbd u ∈ littleBesov F φ s p := by
  -- Since `|s| < ⌊|s|⌋₊ + 1` is strict, choose `r > s` with `⌊|r|⌋₊ ≤ ⌊|s|⌋₊` so `g` already acts
  -- boundedly on `B^r_{p,∞}`.
  have hlt : |s| < (⌊|s|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one |s|
  set r : ℝ := s + ((⌊|s|⌋₊ : ℝ) + 1 - |s|) / 2
  have hsr : s < r := by dsimp only [r]; linarith
  have habs : |r| < ((⌊|s|⌋₊ + 1 : ℕ) : ℝ) := by
    have hδ : 0 ≤ ((⌊|s|⌋₊ : ℝ) + 1 - |s|) / 2 := by linarith
    have hle := abs_add_le s (((⌊|s|⌋₊ : ℝ) + 1 - |s|) / 2)
    rw [abs_of_nonneg hδ] at hle
    push_cast
    dsimp only [r]
    linarith
  have hfl : ⌊|r|⌋₊ + 1 ≤ ⌊|s|⌋₊ + 1 := Nat.succ_le_of_lt ((Nat.floor_lt (abs_nonneg r)).2 habs)
  have hbd' : ∀ n ≤ ⌊|r|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C :=
    fun n hn ↦ hbd n (hn.trans hfl)
  exact map_mem_littleBesov_of_inclusionOfLT (smulLeftCLM F φ s p ∞ g hg hbd) hsr hsr
    (fun v ↦ ⟨smulLeftCLM F φ r p ∞ g hg hbd' v, ext (by simp)⟩) hu

/-- Unbundled smooth multiplier theorem on `MemLittleBesov`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.smulLeftCLM {u : 𝓢'(E, F)}
    (hu : u.MemLittleBesov φ s p) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    (TemperedDistribution.smulLeftCLM F g u).MemLittleBesov φ s p := by
  have h := smulLeftCLM_mem_littleBesov hg hbd
    (hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu)
  rwa [mem_littleBesov_iff, toDistr_smulLeftCLM, hu.memBesov.toDistr_toBesovSpace] at h

end Invariance

section SmoothClosure

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **For `1 ≤ p < ∞`, the little Besov space `b^s_{p,∞}(E, F)` is the closure of `𝓢(E, F)` in
`B^s_{p,∞}(E, F)`.** -/
theorem littleBesov_eq_closure_range_toBesovSpaceCLM (hp : p ≠ ∞) :
    (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
      closure (Set.range (SchwartzMap.toBesovSpaceCLM φ s p ∞)) := by
  refine Set.Subset.antisymm (fun u hu ↦ ?_) ?_
  · exact isClosed_closure.mem_of_tendsto (mem_littleBesov_iff_tendsto_partialSumCLM.1 hu)
      (Eventually.of_forall fun N ↦ partialSumCLM_mem_closure_range_toBesovSpaceCLM hp N u)
  · refine closure_minimal ?_ isClosed_littleBesov
    rintro _ ⟨f, rfl⟩
    exact toBesovSpaceCLM_mem_littleBesov f

/-- **For `1 ≤ p < ∞`, `b^s_{p,∞}(E, F)` is the closure of compactly supported smooth functions in
`B^s_{p,∞}(E, F)`.** -/
theorem littleBesov_eq_closure_image_hasCompactSupport (hp : p ≠ ∞) :
    (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
      closure (SchwartzMap.toBesovSpaceCLM φ s p ∞ ''
        {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) := by
  rw [closure_image_toBesovSpaceCLM_hasCompactSupport,
    littleBesov_eq_closure_range_toBesovSpaceCLM hp]

/-- Explicit norm approximation in `b^s_{p,∞}(E, F)` (`1 ≤ p < ∞`) by compactly supported Schwartz
functions. -/
theorem exists_hasCompactSupport_norm_sub_lt_of_mem_littleBesov (hp : p ≠ ∞)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E, F), HasCompactSupport (f : E → F) ∧
      ‖u - f.toBesovSpaceCLM φ s p ∞‖ < ε := by
  rw [SetLike.mem_coe.symm, littleBesov_eq_closure_image_hasCompactSupport hp] at hu
  obtain ⟨_, ⟨f, hf, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hu ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hdist⟩

/-- The continuous linear inclusion of Schwartz functions into the little Besov space
`b^s_{p,∞}(E, F)`. -/
def _root_.SchwartzMap.toLittleBesovCLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : 𝓢(E, F) →L[ℂ] littleBesov F φ s p :=
  (SchwartzMap.toBesovSpaceCLM φ s p ∞).codRestrict (littleBesov F φ s p)
    toBesovSpaceCLM_mem_littleBesov

@[simp]
theorem _root_.SchwartzMap.coe_toLittleBesovCLM_apply (f : 𝓢(E, F)) :
    (f.toLittleBesovCLM φ s p : BesovSpace F φ s p ∞) = f.toBesovSpaceCLM φ s p ∞ :=
  (rfl)

/-- **Schwartz functions are dense in `b^s_{p,∞}(E, F)`** for `1 ≤ p < ∞`. -/
theorem _root_.SchwartzMap.denseRange_toLittleBesovCLM (φ : ContDiffBump (0 : E)) (s : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (SchwartzMap.toLittleBesovCLM (E := E) (F := F) φ s p) := by
  refine Metric.denseRange_iff.2 fun u ε hε ↦ ?_
  obtain ⟨f, -, hf⟩ := exists_hasCompactSupport_norm_sub_lt_of_mem_littleBesov hp u.2 hε
  exact ⟨f, by simpa [Subtype.dist_eq, dist_eq_norm] using hf⟩

/-- **Compactly supported smooth functions are dense in `b^s_{p,∞}(E, F)`** for `1 ≤ p < ∞`. -/
theorem _root_.SchwartzMap.dense_image_toLittleBesovCLM_hasCompactSupport
    (φ : ContDiffBump (0 : E)) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense (SchwartzMap.toLittleBesovCLM φ s p ''
      {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) := by
  refine Metric.dense_iff.2 fun u ε hε ↦ ?_
  obtain ⟨f, hsupp, hf⟩ := exists_hasCompactSupport_norm_sub_lt_of_mem_littleBesov hp u.2 hε
  refine ⟨f.toLittleBesovCLM φ s p, ?_, ⟨f, hsupp, rfl⟩⟩
  rw [Metric.mem_ball, Subtype.dist_eq, dist_comm, dist_eq_norm]
  exact hf

/-- Continuous semilinear maps out of `b^s_{p,∞}(E, F)` (`1 ≤ p < ∞`) into a Hausdorff space are
determined by their values on compactly supported Schwartz functions. -/
theorem littleBesov_continuousLinearMap_ext_hasCompactSupport {R : Type*} [Semiring R]
    {σ : ℂ →+* R} {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) {T T' : littleBesov F φ s p →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      T (f.toLittleBesovCLM φ s p) = T' (f.toLittleBesovCLM φ s p)) :
    T = T' := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  refine (SchwartzMap.dense_image_toLittleBesovCLM_hasCompactSupport φ s hp).induction ?_
    (isClosed_eq T.continuous T'.continuous) u
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- Continuous semilinear maps out of `b^s_{p,∞}(E, F)` (`1 ≤ p < ∞`) into a Hausdorff space are
determined by their values on Schwartz functions. -/
theorem littleBesov_continuousLinearMap_ext {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) {T T' : littleBesov F φ s p →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), T (f.toLittleBesovCLM φ s p) = T' (f.toLittleBesovCLM φ s p)) :
    T = T' :=
  littleBesov_continuousLinearMap_ext_hasCompactSupport hp fun f _ ↦ h f

end SmoothClosure

end TauCeti.BesovSpace

section DiracAndNonDensity

open TemperedDistribution Module

/-- **At the critical regularity `s = -n (1 - 1/p)`, the Dirac mass does not lie in `b^s_{p,∞}`**
in positive dimension `n ≥ 1`: its weighted Littlewood–Paley block norms for `j ≥ 1` are a nonzero
constant independent of `j`, whereas `δ₀ ∈ B^s_{p,∞}` by `TemperedDistribution.memBesov_delta_zero`.
-/
theorem TemperedDistribution.not_memLittleBesov_delta_zero [Nontrivial E]
    (φ : ContDiffBump (0 : E)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ (delta (0 : E)).MemLittleBesov φ (-(finrank ℝ E * (1 - p.toReal⁻¹))) p := by
  set m : ℝ := finrank ℝ E * (1 - p.toReal⁻¹)
  set f : ℕ → Lp ℂ p (volume : Measure E) :=
    fun j ↦ (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).toLp p
  have hf (j : ℕ) : littlewoodPaleyBlock ℂ φ j (delta 0) = f j := by
    rw [Lp.toTemperedDistribution_toLp_eq, littlewoodPaleyBlock_delta_zero]
  have hfae1 : f 1 =ᵐ[volume] 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ) := by
    filter_upwards [(𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz 1)).coeFn_toLp p] with x hx
    rw [hx, SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  have hc : 0 < ‖f 1‖ := by
    refine ENNReal.toReal_pos ?_ (Lp.eLpNorm_ne_top _)
    rw [eLpNorm_congr_ae hfae1]
    exact φ.eLpNorm_fourierInv_inhomogeneousLittlewoodPaley_ne_zero 1
      (zero_lt_one.trans_le Fact.out).ne'
  have hconst (j : ℕ) : (2 : ℝ) ^ (-m * (j + 1 : ℕ)) * ‖f (j + 1)‖ = 2 ^ (-m) * ‖f 1‖ := by
    rw [φ.norm_toLp_fourierInv_inhomogeneousLittlewoodPaleySchwartz_succ, ← mul_assoc,
      ← Real.rpow_add two_pos]
    congr 2
    push_cast
    ring
  intro hu
  have ht := ((memLittleBesov_iff_tendsto hf).1 hu).comp (tendsto_add_atTop_nat 1)
  have ht' : Tendsto (fun _ : ℕ ↦ (2 : ℝ) ^ (-m) * ‖f 1‖) atTop (𝓝 0) :=
    ht.congr fun j ↦ hconst j
  have hzero : (2 : ℝ) ^ (-m) * ‖f 1‖ = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  linarith [mul_pos (Real.rpow_pos_of_pos two_pos (-m)) hc]

/-- **Exact little-Besov regularity of the Dirac mass.** On a finite-dimensional real inner product
space of positive dimension `n ≥ 1`, for `1 ≤ p ≤ ∞`, `δ₀ ∈ b^s_{p,∞}` if and only if
`s < -n (1 - 1/p)` (with `1/∞ = 0`). -/
theorem TemperedDistribution.memLittleBesov_delta_zero_iff [Nontrivial E]
    (φ : ContDiffBump (0 : E)) {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (delta (0 : E)).MemLittleBesov φ s p ↔ s < -(finrank ℝ E * (1 - p.toReal⁻¹)) :=
  ⟨fun hu ↦ by
    by_contra! hle
    exact not_memLittleBesov_delta_zero φ p (hu.mono hle),
    fun hs ↦ ((memBesov_delta_zero_iff φ one_ne_zero).2 (Or.inl hs)).memLittleBesov_of_ne_top
      ENNReal.one_ne_top⟩

namespace TauCeti.BesovSpace

/-- **The little Besov space is a proper subspace of `B^s_{p,∞}(E, F)`** for every smoothness order
`s : ℝ` and every `1 ≤ p ≤ ∞` whenever `E` and `F` are nontrivial. -/
theorem littleBesov_ne_top [Nontrivial E] [Nontrivial F] (φ : ContDiffBump (0 : E)) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    littleBesov F φ s p ≠ ⊤ := by
  -- Shift `δ₀` from `-n (1 - 1/p)` to order `s` via `besselPotentialEquiv`, then embed `ℂ` as a
  -- complemented summand of `F` via Hahn–Banach.
  set s₀ : ℝ := -(finrank ℝ E * (1 - p.toReal⁻¹))
  let u₀ : BesovSpace ℂ φ s₀ p ∞ := (memBesov_delta_zero φ p).toBesovSpace
  have hu₀ : u₀ ∉ littleBesov ℂ φ s₀ p :=
    (memBesov_delta_zero φ p).toBesovSpace_mem_littleBesov_iff.not.2
      (not_memLittleBesov_delta_zero φ p)
  let u₁ : BesovSpace ℂ φ s p ∞ := besselPotentialEquiv ℂ φ p ∞ (s₀ - s) (by ring) u₀
  have hu₁ : u₁ ∉ littleBesov ℂ φ s p := by
    rwa [besselPotentialEquiv_mem_littleBesov_iff]
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector (𝕜 := ℂ) v hvn
  let ι : ℂ →L[ℂ] F := ContinuousLinearMap.toSpanSingleton ℂ (((‖v‖ : ℂ)⁻¹) • v)
  have hcomp : ℓ.comp ι = ContinuousLinearMap.id ℂ ℂ := by
    ext1
    simp [ι, hℓv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hvn)]
  intro htop
  have hmem : postcomp φ s p ∞ ι u₁ ∈ littleBesov F φ s p := htop ▸ Submodule.mem_top
  have hback := postcomp_mem_littleBesov ℓ hmem
  rw [postcomp_comp_apply, hcomp, postcomp_id, ContinuousLinearMap.id_apply] at hback
  exact hu₁ hback

/-- **Schwartz functions are NOT dense in `B^s_{p,∞}(E, F)`** in positive dimension with nontrivial
fiber, for any `s ∈ ℝ` and any `1 ≤ p ≤ ∞`: their range is contained in the proper closed subspace
`b^s_{p,∞}(E, F)`. -/
theorem _root_.SchwartzMap.not_denseRange_toBesovSpaceCLM_top [Nontrivial E] [Nontrivial F]
    (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ DenseRange (SchwartzMap.toBesovSpaceCLM (E := E) (F := F) φ s p ∞) := by
  intro hd
  refine littleBesov_ne_top (F := F) φ s p (Submodule.eq_top_iff'.2 fun u ↦ ?_)
  exact closure_minimal (by rintro _ ⟨f, rfl⟩; exact toBesovSpaceCLM_mem_littleBesov f)
    isClosed_littleBesov (hd u)

end TauCeti.BesovSpace

end DiracAndNonDensity
