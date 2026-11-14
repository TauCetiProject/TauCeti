/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.Normed.Interpolation.WeightedSequence
import TauCeti.Analysis.Distribution.TemperedDistribution.DyadicSymbol
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Real interpolation of inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space `E`,
with inhomogeneous Littlewood–Paley blocks `Δⱼ` (`j ≥ 0`), and let `F` be a complex Banach space.
For `1 ≤ p, q₀, q₁, q ≤ ∞`, distinct smoothness orders `s₀ ≠ s₁`, and `0 < θ < 1`, the real
interpolation space of two Besov spaces with the same integrability exponent `p` is again a Besov
space:

`(B^{s₀}_{p,q₀}(E, F), B^{s₁}_{p,q₁}(E, F))_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}(E, F)`,

where `s_θ = (1 - θ) s₀ + θ s₁`, regardless of the fine indices `q₀` and `q₁`.

The proof follows Bergh–Löfström, Theorems 6.4.3 and 6.4.5(1), by exhibiting the couple
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` as a retract of the weighted sequence couple
`(ℓ^{q₀}_{s₀}(Lᵖ), ℓ^{q₁}_{s₁}(Lᵖ))` (`TauCeti.CompatibleCouple.weightedLp`):

* **Analysis** (`TauCeti.BesovSpace.weightedBlocksₗᵢ`,
  `TauCeti.CompatibleCouple.besovToWeightedLpSum`): sending `u` to its weighted blocks
  `(2^{jsᵢ} Δⱼ u)ⱼ ∈ ℓ^{qᵢ}(ℕ, Lᵖ)` is a linear isometry on each endpoint, and on the ambient
  sequences both routes send `u` to its unweighted blocks `(Δⱼ u)ⱼ`.
* **Synthesis** (`TauCeti.BesovSpace.ofWeightedBlocksCLM`,
  `TauCeti.CompatibleCouple.weightedLpToBesovSum`): if `Δₘ Δⱼ = 0` for `|m - j| ≥ L`, the enlarged
  multipliers `Δ'ⱼ = ∑_{j - L ≤ m < j + L} Δₘ` satisfy `Δ'ⱼ Δⱼ = Δⱼ` and `Δₖ Δ'ⱼ = 0` for
  `|k - j| ≥ 2 L`. For `b ∈ ℓ^q(ℕ, Lᵖ)`, the series `∑ⱼ Δ'ⱼ (2^{-js} bⱼ)` converges in `𝓢'(E, F)`
  because `J^{s-1} Δ'ⱼ (2^{-js} bⱼ)` has `Lᵖ` norm `O(2^{-j} ‖b‖)`, and bounded overlap controls
  its Besov norm by a constant multiple of `‖b‖` independent of `p` and `q`. On a distribution
  `u ∈ B^s_{p,q}` the terms become `Δ'ⱼ Δⱼ u = Δⱼ u`, which sum back to `u`.
* **Interpolation** (`TauCeti.CompatibleCouple.besovKMethodEquiv`): transferring
  `TauCeti.CompatibleCouple.weightedLpKMethodEquiv` across this couple retraction identifies both
  membership (`TauCeti.CompatibleCouple.mem_kMethod_besov_iff`) and the `K`-method norm up to
  equivalence.

## Main declarations

* `TauCeti.BesovSpace.weightedBlocksₗᵢ`: the isometric linear embedding `B^s_{p,q} →ₗᵢ[ℂ] ℓ^q(Lᵖ)`.
* `TauCeti.BesovSpace.ofWeightedBlocksCLM`: the Littlewood–Paley synthesis retraction
  `ℓ^q(Lᵖ) →L[ℂ] B^s_{p,q}`, left inverse to `weightedBlocksₗᵢ`
  (`TauCeti.BesovSpace.ofWeightedBlocksCLM_weightedBlocks`), with operator norm bounded uniformly in
  `p` and `q` (`TauCeti.BesovSpace.exists_norm_ofWeightedBlocksCLM_le`).
* `TauCeti.CompatibleCouple.besov`: the compatible couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` inside
  `𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besovToWeightedLpSum` and
  `TauCeti.CompatibleCouple.weightedLpToBesovSum`: the analysis and synthesis morphisms between the
  Besov sum space and the weighted `ℓ^q(Lᵖ)` sum space, with
  `TauCeti.CompatibleCouple.leftInverse_weightedLpToBesovSum`.
* `TauCeti.CompatibleCouple.mem_range_sumSpaceEmbed_besov` and
  `TauCeti.CompatibleCouple.mem_kMethod_besov_iff`: for `s₀ ≠ s₁` and `0 < θ < 1`, membership in
  `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` is `MemBesov φ ((1 - θ) s₀ + θ s₁) p q`.
* `TauCeti.CompatibleCouple.besovKMethodEquiv`: the continuous linear equivalence
  `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}`, together with the
  explicit lower bound `TauCeti.CompatibleCouple.mul_norm_besovKMethodEquiv_le`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, Theorems 6.4.3 and 6.4.5(1).
* H. Triebel, *Theory of Function Spaces*, Section 2.4.2.
-/

public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

namespace BesovSpace

open TemperedDistribution

/-! ### Analysis and synthesis between `B^s_{p,q}` and `ℓ^q(ℕ, Lᵖ)` -/

section Retraction

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F φ s p q) in
/-- The weighted Littlewood–Paley blocks `u ↦ (2^{js} Δⱼ u)ⱼ`, as a linear isometry from
`B^s_{p,q}` into `ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksₗᵢ :
    BesovSpace F φ s p q →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q where
  toLinearMap := weightedBlocksₗ F φ s p q
  norm_map' u := by rw [weightedBlocksₗ_apply, norm_weightedBlocks]

@[simp]
theorem weightedBlocksₗᵢ_apply (u : BesovSpace F φ s p q) :
    weightedBlocksₗᵢ F φ s p q u = u.weightedBlocks :=
  weightedBlocksₗ_apply u

theorem toDistrCLM_injective : Function.Injective (toDistrCLM F φ s p q) :=
  fun _ _ h ↦ ext <| by simpa only [toDistrCLM_apply] using h

omit [Fact (1 ≤ q)] in
private theorem inv_weight_smul_weightedBlocks_apply (u : BesovSpace F φ s p q) (j : ℕ) :
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • u.weightedBlocks j = u.block j := by
  rw [u.weightedBlocks_apply, inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

/-- The index separation beyond which pieces of the inhomogeneous Littlewood–Paley partition of
`φ` have disjoint supports. Kept private so that `Classical.choose` never enters public types. -/
private def overlapWidth (φ : ContDiffBump (0 : E)) : ℕ :=
  (φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ).choose

omit [MeasurableSpace E] [BorelSpace E] in
private theorem inhomogeneousLittlewoodPaley_mul_eq_zero_of_overlapWidth
    (φ : ContDiffBump (0 : E)) {j k : ℕ} (hjk : j + overlapWidth φ ≤ k) (ξ : E) :
    φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0 :=
  (φ.exists_inhomogeneousLittlewoodPaley_mul_eq_zero φ).choose_spec j k hjk ξ

omit [CompleteSpace F] in
private theorem littlewoodPaleyBlock_littlewoodPaleyBlock_eq_zero
    (φ : ContDiffBump (0 : E)) {j k : ℕ}
    (hjk : j + overlapWidth φ ≤ k ∨ k + overlapWidth φ ≤ j) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k u) = 0 := by
  have hzero {a b : ℕ} (hab : a + overlapWidth φ ≤ b) (v : 𝓢'(E, F)) :
      littlewoodPaleyBlock F φ a (littlewoodPaleyBlock F φ b v) = 0 := by
    change (littlewoodPaleyBlock F φ a ∘L littlewoodPaleyBlock F φ b) v = 0
    rw [littlewoodPaleyBlock_compL_littlewoodPaleyBlock]
    simp_rw [inhomogeneousLittlewoodPaley_mul_eq_zero_of_overlapWidth φ hab,
      Complex.ofReal_zero, fourierMultiplierCLM_const, zero_smul]
    rfl
  rcases hjk with hjk | hkj
  · exact hzero hjk u
  · rw [littlewoodPaleyBlock_comm]
    exact hzero hkj u

/-- The enlarged Littlewood–Paley multiplier `Δ'ⱼ = ∑_{j - L ≤ m < j + L} Δₘ`, corresponding to an
enlarged cutoff `ContDiffBump.enlargedLittlewoodPaley` that equals `1` on the support of `ψⱼ`. -/
private def enlargedBlock (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (φ : ContDiffBump (0 : E)) (j : ℕ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  ∑ m ∈ Finset.Ico (j - overlapWidth φ) (j + overlapWidth φ), littlewoodPaleyBlock F φ m

omit [CompleteSpace F] in
/-- `Δ'ⱼ Δⱼ = Δⱼ`: every block outside `[j - L, j + L)` annihilates `Δⱼ u`, so the window sum
reconstructs `Δⱼ u`. -/
private theorem enlargedBlock_littlewoodPaleyBlock (φ : ContDiffBump (0 : E)) (j : ℕ)
    (u : 𝓢'(E, F)) :
    enlargedBlock F φ j (littlewoodPaleyBlock F φ j u) = littlewoodPaleyBlock F φ j u := by
  rw [enlargedBlock, _root_.sum_apply]
  refine sum_littlewoodPaleyBlock_eq_self φ _ fun m hm ↦ ?_
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hm
  refine littlewoodPaleyBlock_littlewoodPaleyBlock_eq_zero φ ?_ u
  rcases hm with hm | hm
  · exact Or.inl (by omega)
  · exact Or.inr hm

omit [CompleteSpace F] in
/-- `Δₖ Δ'ⱼ = 0` when `|k - j| ≥ 2 L`. -/
private theorem littlewoodPaleyBlock_enlargedBlock_eq_zero (φ : ContDiffBump (0 : E)) {j k : ℕ}
    (hjk : k + 2 * overlapWidth φ ≤ j ∨ j + 2 * overlapWidth φ ≤ k) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ k (enlargedBlock F φ j u) = 0 := by
  rw [enlargedBlock, _root_.sum_apply, map_sum]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [Finset.mem_Ico] at hm
  refine littlewoodPaleyBlock_littlewoodPaleyBlock_eq_zero φ ?_ u
  rcases hjk with hjk | hjk
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- The enlarged multipliers `Δ'ⱼ` are bounded on `Lᵖ`, uniformly in `j` and `p`. -/
private theorem exists_enlargedBlock_eq_and_norm_le (φ : ContDiffBump (0 : E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        enlargedBlock F φ j (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set L := overlapWidth φ
  refine ⟨2 * L * max C₀ 0, by positivity, fun {p} _ j f ↦ ?_⟩
  choose g hg hgC using fun m ↦ hC₀ (p := p) m f
  refine ⟨∑ m ∈ Finset.Ico (j - L) (j + L), g m, ?_, ?_⟩
  · rw [enlargedBlock, _root_.sum_apply, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun m _ ↦ hg m
  · calc ‖∑ m ∈ Finset.Ico (j - L) (j + L), g m‖
        ≤ ∑ _ ∈ Finset.Ico (j - L) (j + L), max C₀ 0 * ‖f‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦
            (hgC m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)))
      _ = (Finset.Ico (j - L) (j + L)).card * (max C₀ 0 * ‖f‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * L * (max C₀ 0 * ‖f‖) := by
          gcongr
          rw [Nat.card_Ico]
          exact_mod_cast (by omega)
      _ = 2 * L * max C₀ 0 * ‖f‖ := by ring

/-- `J^t Δ'ⱼ` acts on `Lᵖ` with norm `O(2^{jt})`, uniformly in `j` and `p`. -/
private theorem exists_besselPotential_enlargedBlock_eq_and_norm_le
    (φ : ContDiffBump (0 : E)) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ g : Lp F p (volume : Measure E),
        besselPotential E F t (enlargedBlock F φ j (f : 𝓢'(E, F))) = g ∧
          ‖g‖ ≤ C * 2 ^ (t * j) * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁, hJ⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ t
  set L := overlapWidth φ
  set K : ℝ := C₁ * 2 ^ (|t| * L) * max C₀ 0
  refine ⟨2 * L * K, by positivity, fun {p} _ j f ↦ ?_⟩
  choose u hu huC using fun m ↦ hC₀ (p := p) m f
  choose g hg hgC using fun m ↦ hJ (p := p) m (f : 𝓢'(E, F)) (u m) (hu m)
  refine ⟨∑ m ∈ Finset.Ico (j - L) (j + L), g m, ?_, ?_⟩
  · rw [enlargedBlock, _root_.sum_apply, map_sum, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun m _ ↦ hg m
  · have hgm (m : ℕ) (hm : m ∈ Finset.Ico (j - L) (j + L)) : ‖g m‖ ≤ K * 2 ^ (t * j) * ‖f‖ := by
      calc ‖g m‖ ≤ C₁ * 2 ^ (t * m) * ‖u m‖ := hgC m
        _ ≤ C₁ * (2 ^ (|t| * L) * 2 ^ (t * j)) * (max C₀ 0 * ‖f‖) := by
          gcongr
          · exact Real.rpow_mul_natCast_le_of_mem_Ico one_le_two t hm
          · exact (huC m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f))
        _ = K * 2 ^ (t * j) * ‖f‖ := by ring
    calc ‖∑ m ∈ Finset.Ico (j - L) (j + L), g m‖
        ≤ ∑ _ ∈ Finset.Ico (j - L) (j + L), K * 2 ^ (t * j) * ‖f‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hgm)
      _ = (Finset.Ico (j - L) (j + L)).card * (K * 2 ^ (t * j) * ‖f‖) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * L * (K * 2 ^ (t * j) * ‖f‖) := by
          gcongr
          rw [Nat.card_Ico]
          exact_mod_cast (by omega)
      _ = 2 * L * K * 2 ^ (t * j) * ‖f‖ := by ring

/-- **Convergence and Besov bound for the Littlewood–Paley synthesis series.** For every `b` in
`ℓ^q(ℕ, Lᵖ)`, the series `∑ⱼ Δ'ⱼ (2^{-js} bⱼ)` converges in `𝓢'(E, F)` to an element of `B^s_{p,q}`
whose norm is bounded by `C ‖b‖`, with `C ≥ 0` depending only on `φ` and `s` (not on `p` or `q`). -/
private theorem exists_hasSum_enlargedBlock_and_norm_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q),
      ∃ v : BesovSpace F φ s p q,
        HasSum (fun j ↦ enlargedBlock F φ j
          (((((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j : Lp F p (volume : Measure E)) : 𝓢'(E, F)))
          v.toDistr ∧
        ‖v‖ ≤ C * ‖b‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_enlargedBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₂, hC₂0, hJ⟩ := exists_besselPotential_enlargedBlock_eq_and_norm_le (F := F) φ (s - 1)
  set L := overlapWidth φ
  set K : ℝ := max C₀ 0 * C₁
  set M : ℝ := K * 2 ^ (|s| * (2 * L : ℕ))
  refine ⟨M * (2 * (2 * L : ℕ)), by positivity, fun {p q} _ _ b ↦ ?_⟩
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a : ℕ → Lp F p (volume : Measure E) := fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j
  have ha_norm (j : ℕ) : (2 : ℝ) ^ (s * j) * ‖a j‖ = ‖b j‖ := by
    rw [norm_smul, norm_inv, Complex.norm_of_nonneg (by positivity),
      mul_inv_cancel_left₀ (by positivity)]
  -- Convergence of `∑ⱼ Δ'ⱼ (a j)` in `𝓢'(E, F)` via `J^{s-1}`, where the terms decay as `2^{-j}`.
  choose z hz hzn using fun j ↦ hJ (p := p) j (a j)
  have hz_bound (j : ℕ) : ‖z j‖ ≤ C₂ * ‖b‖ * (1 / 2) ^ j := by
    have h2 : (2 : ℝ) ^ ((s - 1) * j) = (1 / 2) ^ j * 2 ^ (s * j) := by
      rw [sub_mul, one_mul, Real.rpow_sub two_pos, Real.rpow_natCast, div_eq_inv_mul, ← inv_pow,
        one_div]
    calc ‖z j‖ ≤ C₂ * 2 ^ ((s - 1) * j) * ‖a j‖ := hzn j
      _ = C₂ * (1 / 2) ^ j * (2 ^ (s * j) * ‖a j‖) := by rw [h2]; ring
      _ = C₂ * (1 / 2) ^ j * ‖b j‖ := by rw [ha_norm]
      _ ≤ C₂ * (1 / 2) ^ j * ‖b‖ := by gcongr; exact lp.norm_apply_le_norm hq0 b j
      _ = C₂ * ‖b‖ * (1 / 2) ^ j := by ring
  have hz_sum : Summable z :=
    Summable.of_norm_bounded (summable_geometric_two.mul_left (C₂ * ‖b‖)) hz_bound
  set U : 𝓢'(E, F) := besselPotential E F (1 - s) ((∑' j, z j : Lp F p (volume : Measure E)))
  have hHasSum : HasSum (fun j ↦ enlargedBlock F φ j (a j : 𝓢'(E, F))) U := by
    have hmap := hz_sum.hasSum.map
      (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p)
      (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p).continuous
    refine hmap.congr_fun fun j ↦ ?_
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      Lp.toTemperedDistributionCLM_apply, ← hz j, besselPotential_besselPotential_apply,
      show s - 1 + (1 - s) = 0 by ring, besselPotential_zero, ContinuousLinearMap.id_apply]
  -- Each block `Δₖ U` is a finite window sum of `Lᵖ` pieces `Δₖ Δ'ⱼ (a j)` over `[k - 2L, k + 2L)`.
  choose h hh hhn using fun j ↦ hC₁ (p := p) j (a j)
  choose w hw hwn using fun k j ↦ hC₀ (p := p) k (h j)
  have hwkj (k j : ℕ) : ‖w k j‖ ≤ K * ‖a j‖ := by
    calc ‖w k j‖ ≤ max C₀ 0 * ‖h j‖ :=
          (hwn k j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      _ ≤ max C₀ 0 * (C₁ * ‖a j‖) := by gcongr; exact hhn j
      _ = K * ‖a j‖ := by ring
  set g : ℕ → Lp F p (volume : Measure E) :=
    fun k ↦ ∑ j ∈ Finset.Ico (k - 2 * L) (k + 2 * L), w k j
  have hgU (k : ℕ) : littlewoodPaleyBlock F φ k U = g k := by
    rw [littlewoodPaleyBlock_eq_sum_Ico_of_hasSum φ hHasSum
      (fun j k' hjk ↦ littlewoodPaleyBlock_enlargedBlock_eq_zero (F := F) φ hjk (a j)) k,
      Lp.toTemperedDistribution_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hh j, hw k j]
  have hg_bound (k : ℕ) :
      (2 : ℝ) ^ (s * k) * ‖g k‖ ≤ M * ∑ j ∈ Finset.Ico (k - 2 * L) (k + 2 * L), ‖b j‖ := by
    have hwin := TauCeti.two_rpow_mul_norm_sum_Ico_le s (hwkj k) k (2 * L)
    have hK0 : 0 ≤ K := by positivity
    rw [max_eq_left hK0] at hwin
    refine hwin.trans_eq ?_
    simp_rw [ha_norm]
    rfl
  -- Bound the `ℓ^q` norm of the window majorant by `M * 4 L * ‖b‖`.
  set bnorm : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun j ↦ ‖b j‖, (lp.memℓp b).norm⟩
  set wsum : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - 2 * L) (k + 2 * L), bnorm j,
      (lp.memℓp bnorm).sum_Ico_sub_add (2 * L)⟩
  obtain ⟨v, hvU, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq g (M • wsum)
    hgU fun k ↦ hg_bound k
  refine ⟨v, hvU ▸ hHasSum, hvn.trans ?_⟩
  have hM0 : 0 ≤ M := by positivity
  have hbnorm : ‖bnorm‖ ≤ ‖b‖ := lp.norm_mono hq0 fun j ↦ (Real.norm_of_nonneg (norm_nonneg _)).le
  have hwsum : ‖wsum‖ ≤ 2 * (2 * L : ℕ) * ‖bnorm‖ :=
    lp.norm_le_of_forall_eq_sum_Ico_sub_add (2 * L) fun _ ↦ rfl
  calc ‖M • wsum‖ = M * ‖wsum‖ := by rw [norm_smul, Real.norm_of_nonneg hM0]
    _ ≤ M * (2 * (2 * L : ℕ) * ‖b‖) := by gcongr; exact hwsum.trans (by gcongr)
    _ = M * (2 * (2 * L : ℕ)) * ‖b‖ := by ring

variable (F φ s p q) in
/-- **The Littlewood–Paley synthesis retraction** (Bergh–Löfström, Theorem 6.4.3). Sends a sequence
`b ∈ ℓ^q(ℕ, Lᵖ)` to the sum `∑ⱼ Δ'ⱼ (2^{-js} bⱼ)` in `B^s_{p,q}`, where `Δ'ⱼ` is an enlarged
Littlewood–Paley multiplier equal to `1` on the support of `ψⱼ`. It is a continuous left inverse to
`weightedBlocksₗᵢ` (`ofWeightedBlocksCLM_weightedBlocks`), with operator norm bounded uniformly in
`p` and `q` (`exists_norm_ofWeightedBlocksCLM_le`). -/
def ofWeightedBlocksCLM :
    lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q →L[ℂ] BesovSpace F φ s p q :=
  let hS := (exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose_spec.2
  LinearMap.mkContinuous
    { toFun b := (hS b).choose
      map_add' b₁ b₂ := ext <| ((hS (b₁ + b₂)).choose_spec.1).unique <| by
        refine (((hS b₁).choose_spec.1).add ((hS b₂).choose_spec.1)).congr_fun fun j ↦ ?_
        rw [lp.coeFn_add, Pi.add_apply, smul_add, Lp.toTemperedDistribution_add, map_add]
      map_smul' c b := ext <| ((hS (c • b)).choose_spec.1).unique <| by
        have hsmul := ((hS b).choose_spec.1).map (c • ContinuousLinearMap.id ℂ 𝓢'(E, F))
          (c • ContinuousLinearMap.id ℂ 𝓢'(E, F)).continuous
        refine hsmul.congr_fun fun j ↦ ?_
        simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
          lp.coeFn_smul, Pi.smul_apply]
        rw [smul_comm, Lp.toTemperedDistribution_smul, map_smul] }
    (exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose
    fun b ↦ (hS b).choose_spec.2

private theorem hasSum_enlargedBlock_ofWeightedBlocksCLM
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) :
    HasSum (fun j ↦ enlargedBlock F φ j
      (((((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j : Lp F p (volume : Measure E)) : 𝓢'(E, F)))
      (ofWeightedBlocksCLM F φ s p q b).toDistr :=
  ((exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose_spec.2 b).choose_spec.1

/-- `ofWeightedBlocksCLM` reconstructs every element of `B^s_{p,q}` from its weighted blocks. -/
@[simp]
theorem ofWeightedBlocksCLM_weightedBlocks (u : BesovSpace F φ s p q) :
    ofWeightedBlocksCLM F φ s p q u.weightedBlocks = u := by
  ext1
  have hsum : HasSum (fun j ↦ littlewoodPaleyBlock F φ j u.toDistr)
      (ofWeightedBlocksCLM F φ s p q u.weightedBlocks).toDistr := by
    refine (hasSum_enlargedBlock_ofWeightedBlocksCLM u.weightedBlocks).congr_fun fun j ↦ ?_
    rw [inv_weight_smul_weightedBlocks_apply, u.coe_block, enlargedBlock_littlewoodPaleyBlock]
  exact tendsto_nhds_unique hsum.tendsto_sum_nat (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)

theorem leftInverse_ofWeightedBlocksCLM :
    Function.LeftInverse (ofWeightedBlocksCLM F φ s p q) (weightedBlocksₗᵢ F φ s p q) :=
  fun u ↦ by rw [weightedBlocksₗᵢ_apply, ofWeightedBlocksCLM_weightedBlocks]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- **Uniformity of the synthesis bound.** The operator norm of `ofWeightedBlocksCLM` is bounded by
a constant depending only on `φ` and `s`, independent of the exponents `p` and `q`. -/
theorem exists_norm_ofWeightedBlocksCLM_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q),
      ‖ofWeightedBlocksCLM F φ s p q b‖ ≤ C * ‖b‖ :=
  ⟨(exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose,
    (exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose_spec.1,
    fun b ↦ ((exists_hasSum_enlargedBlock_and_norm_le (F := F) φ s).choose_spec.2 b).choose_spec.2⟩

omit [Fact (1 ≤ q)] in
/-- Two sequences with the same unweighted `Lᵖ` coordinates `(2^{-jsᵢ} bⱼ)ⱼ` synthesize to the
same tempered distribution, regardless of the smoothness orders `s₀, s₁` and fine indices `q₀, q₁`.
This is the compatibility by which `ofWeightedBlocksCLM` glues across a couple. -/
theorem toDistr_ofWeightedBlocksCLM_eq_of_forall {s₀ s₁ : ℝ} {q₀ q₁ : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    {b₀ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₀}
    {b₁ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₁}
    (h : ∀ j : ℕ, (((2 : ℝ) ^ (s₀ * j) : ℝ) : ℂ)⁻¹ • b₀ j =
      (((2 : ℝ) ^ (s₁ * j) : ℝ) : ℂ)⁻¹ • b₁ j) :
    (ofWeightedBlocksCLM F φ s₀ p q₀ b₀).toDistr =
      (ofWeightedBlocksCLM F φ s₁ p q₁ b₁).toDistr :=
  (hasSum_enlargedBlock_ofWeightedBlocksCLM b₀).unique <|
    (hasSum_enlargedBlock_ofWeightedBlocksCLM b₁).congr_fun fun j ↦ by rw [← h j]

end Retraction

end BesovSpace

/-! ### The Besov compatible couple and real interpolation -/

namespace CompatibleCouple

open TemperedDistribution KMethodSpace

section Couple

variable (F) (φ : ContDiffBump (0 : E)) (s₀ s₁ : ℝ) (p q₀ q₁ : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

/-- The compatible couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` of inhomogeneous Besov spaces, with both
endpoints continuously embedded in the ambient space `𝓢'(E, F)` of tempered distributions. -/
def besov :
    CompatibleCouple ℂ (BesovSpace F φ s₀ p q₀) (BesovSpace F φ s₁ p q₁) 𝓢'(E, F) where
  embed₀ := BesovSpace.toDistrCLM F φ s₀ p q₀
  embed₁ := BesovSpace.toDistrCLM F φ s₁ p q₁
  embed₀_injective := BesovSpace.toDistrCLM_injective
  embed₁_injective := BesovSpace.toDistrCLM_injective

variable {F φ s₀ s₁ p q₀ q₁}

@[simp]
theorem besov_embed₀ : (besov F φ s₀ s₁ p q₀ q₁).embed₀ = BesovSpace.toDistrCLM F φ s₀ p q₀ :=
  (rfl)

@[simp]
theorem besov_embed₁ : (besov F φ s₀ s₁ p q₀ q₁).embed₁ = BesovSpace.toDistrCLM F φ s₁ p q₁ :=
  (rfl)

/-- A pair `(u₀, u₁)` lies in the intersection of `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` if and only if
`u₀` and `u₁` represent the same tempered distribution. -/
theorem mem_besov_inter_iff {x : BesovSpace F φ s₀ p q₀ × BesovSpace F φ s₁ p q₁} :
    x ∈ (besov F φ s₀ s₁ p q₀ q₁).inter ↔ x.1.toDistr = x.2.toDistr := by
  simp [mem_inter_iff]

/-- Two decompositions in `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` agree if and only if their sums agree in
`𝓢'(E, F)`. -/
theorem besov_fstToSum_add_sndToSum_eq_iff
    {u₀ v₀ : BesovSpace F φ s₀ p q₀} {u₁ v₁ : BesovSpace F φ s₁ p q₁} :
    (besov F φ s₀ s₁ p q₀ q₁).fstToSum u₀ + (besov F φ s₀ s₁ p q₀ q₁).sndToSum u₁ =
        (besov F φ s₀ s₁ p q₀ q₁).fstToSum v₀ + (besov F φ s₀ s₁ p q₀ q₁).sndToSum v₁ ↔
      u₀.toDistr + u₁.toDistr = v₀.toDistr + v₁.toDistr := by
  rw [← (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed_injective.eq_iff]
  simp

private theorem besovToWeightedLpSum_compat (x : (besov F φ s₀ s₁ p q₀ q₁).inter) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum
        ((BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).toContinuousLinearMap
          ((besov F φ s₀ s₁ p q₀ q₁).interFst x)) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum
        ((BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).toContinuousLinearMap
          ((besov F φ s₀ s₁ p q₀ q₁).interSnd x)) := by
  have hx : ((besov F φ s₀ s₁ p q₀ q₁).interFst x).toDistr =
      ((besov F φ s₀ s₁ p q₀ q₁).interSnd x).toDistr := by
    simpa using (besov F φ s₀ s₁ p q₀ q₁).embed₀_interFst x
  refine (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpace_ext (funext fun j ↦ ?_)
  simp_rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, weightedLp_embed₀_apply,
    weightedLp_embed₁_apply, LinearIsometry.coe_toContinuousLinearMap,
    BesovSpace.weightedBlocksₗᵢ_apply]
  exact ((BesovSpace.inv_weight_smul_weightedBlocks_apply _ j).trans
    (BesovSpace.block_eq_of_toDistr_eq hx j)).trans
    (BesovSpace.inv_weight_smul_weightedBlocks_apply _ j).symm

private theorem weightedLpToBesovSum_compat (φ : ContDiffBump (0 : E))
    (y : (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).inter) :
    (besov F φ s₀ s₁ p q₀ q₁).fstToSum
        (BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀
          ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).interFst y)) =
      (besov F φ s₀ s₁ p q₀ q₁).sndToSum
        (BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁
          ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).interSnd y)) := by
  have hy := (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).embed₀_interFst y
  refine (besov F φ s₀ s₁ p q₀ q₁).sumSpace_ext ?_
  simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
    BesovSpace.toDistrCLM_apply]
  exact BesovSpace.toDistr_ofWeightedBlocksCLM_eq_of_forall fun j ↦ by
    have hj := congr_fun hy j
    rw [weightedLp_embed₀_apply, weightedLp_embed₁_apply] at hj
    exact hj

/-- **The Littlewood–Paley analysis morphism** on sum spaces: sends
`u ∈ B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` to its sequence of unweighted blocks `(Δⱼ u)ⱼ` in
`ℓ^{q₀}_{s₀}(Lᵖ) + ℓ^{q₁}_{s₁}(Lᵖ)`. -/
def besovToWeightedLpSum :
    (besov F φ s₀ s₁ p q₀ q₁).SumSpace →L[ℂ]
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace :=
  (besov F φ s₀ s₁ p q₀ q₁).sumLift
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum.comp
      (BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).toContinuousLinearMap)
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum.comp
      (BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).toContinuousLinearMap)
    besovToWeightedLpSum_compat

@[simp]
theorem besovToWeightedLpSum_fstToSum (u₀ : BesovSpace F φ s₀ p q₀) :
    besovToWeightedLpSum ((besov F φ s₀ s₁ p q₀ q₁).fstToSum u₀) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum u₀.weightedBlocks := by
  rw [besovToWeightedLpSum]
  exact ((besov F φ s₀ s₁ p q₀ q₁).sumLift_fstToSum _ _ _ u₀).trans (by simp)

@[simp]
theorem besovToWeightedLpSum_sndToSum (u₁ : BesovSpace F φ s₁ p q₁) :
    besovToWeightedLpSum ((besov F φ s₀ s₁ p q₀ q₁).sndToSum u₁) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum u₁.weightedBlocks := by
  rw [besovToWeightedLpSum]
  exact ((besov F φ s₀ s₁ p q₀ q₁).sumLift_sndToSum _ _ _ u₁).trans (by simp)

/-- In the ambient space of sequences, `besovToWeightedLpSum u` has `j`-th coordinate `Δⱼ u`. -/
@[simp]
theorem coe_sumSpaceEmbed_besovToWeightedLpSum
    (u : (besov F φ s₀ s₁ p q₀ q₁).SumSpace) (j : ℕ) :
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed
        (besovToWeightedLpSum u) j : 𝓢'(E, F)) =
      littlewoodPaleyBlock F φ j ((besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed u) := by
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ s₀ s₁ p q₀ q₁).exists_fstToSum_add_sndToSum_eq u
  rw [map_add, besovToWeightedLpSum_fstToSum, besovToWeightedLpSum_sndToSum, map_add,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply, weightedLp_embed₀_apply,
    weightedLp_embed₁_apply, Lp.toTemperedDistribution_add, map_add, sumSpaceEmbed_fstToSum,
    sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁, BesovSpace.toDistrCLM_apply,
    BesovSpace.toDistrCLM_apply, map_add]
  congr 1
  · exact (congr_arg Lp.toTemperedDistribution
      (BesovSpace.inv_weight_smul_weightedBlocks_apply u₀ j)).trans (u₀.coe_block j)
  · exact (congr_arg Lp.toTemperedDistribution
      (BesovSpace.inv_weight_smul_weightedBlocks_apply u₁ j)).trans (u₁.coe_block j)

/-- **The Littlewood–Paley synthesis morphism** on sum spaces: glues
`BesovSpace.ofWeightedBlocksCLM` on the two endpoints into a left inverse of
`besovToWeightedLpSum`. -/
def weightedLpToBesovSum (φ : ContDiffBump (0 : E)) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace →L[ℂ]
      (besov F φ s₀ s₁ p q₀ q₁).SumSpace :=
  (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift
    ((besov F φ s₀ s₁ p q₀ q₁).fstToSum.comp (BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀))
    ((besov F φ s₀ s₁ p q₀ q₁).sndToSum.comp (BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁))
    (weightedLpToBesovSum_compat φ)

@[simp]
theorem weightedLpToBesovSum_fstToSum (φ : ContDiffBump (0 : E))
    (b₀ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₀) :
    weightedLpToBesovSum φ
        ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum b₀) =
      (besov F φ s₀ s₁ p q₀ q₁).fstToSum (BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀ b₀) := by
  rw [weightedLpToBesovSum]
  exact ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift_fstToSum _ _ _ b₀).trans
    (by simp)

@[simp]
theorem weightedLpToBesovSum_sndToSum (φ : ContDiffBump (0 : E))
    (b₁ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₁) :
    weightedLpToBesovSum φ
        ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum b₁) =
      (besov F φ s₀ s₁ p q₀ q₁).sndToSum (BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁ b₁) := by
  rw [weightedLpToBesovSum]
  exact ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift_sndToSum _ _ _ b₁).trans
    (by simp)

/-- **The Besov couple is a retract of the weighted sequence couple** (Bergh–Löfström,
Theorem 6.4.3). -/
theorem leftInverse_weightedLpToBesovSum (φ : ContDiffBump (0 : E)) :
    Function.LeftInverse
      (weightedLpToBesovSum φ (F := F) (s₀ := s₀) (s₁ := s₁) (p := p) (q₀ := q₀) (q₁ := q₁))
      besovToWeightedLpSum := by
  intro u
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ s₀ s₁ p q₀ q₁).exists_fstToSum_add_sndToSum_eq u
  simp

/-- When `w` in the weighted sequence sum space represents the unweighted blocks `(Δⱼ v)ⱼ` of a
Besov element `v`, `weightedLpToBesovSum φ w` represents `v.toDistr`. -/
private theorem sumSpaceEmbed_weightedLpToBesovSum_eq_toDistr {s' : ℝ} {q' : ℝ≥0∞}
    {w : (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace}
    {v : BesovSpace F φ s' p q'}
    (hw : ∀ j, (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed w j =
      v.block j) :
    (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed (weightedLpToBesovSum φ w) = v.toDistr := by
  obtain ⟨b₀, b₁, rfl⟩ :=
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).exists_fstToSum_add_sndToSum_eq w
  have hsum :=
    (BesovSpace.hasSum_enlargedBlock_ofWeightedBlocksCLM (F := F) (φ := φ) (s := s₀) b₀).add
      (BesovSpace.hasSum_enlargedBlock_ofWeightedBlocksCLM (F := F) (φ := φ) (s := s₁) b₁)
  have hsum' : HasSum (fun j ↦ littlewoodPaleyBlock F φ j v.toDistr)
      ((besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed
        (weightedLpToBesovSum φ
          ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum b₀ +
            (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum b₁))) := by
    simp only [map_add, weightedLpToBesovSum_fstToSum, weightedLpToBesovSum_sndToSum,
      sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
      BesovSpace.toDistrCLM_apply]
    refine hsum.congr_fun fun j ↦ ?_
    have hj : (((2 : ℝ) ^ (s₀ * j) : ℝ) : ℂ)⁻¹ • b₀ j +
        (((2 : ℝ) ^ (s₁ * j) : ℝ) : ℂ)⁻¹ • b₁ j = v.block j := by
      have h := hw j
      rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply,
        weightedLp_embed₀_apply, weightedLp_embed₁_apply] at h
      exact h
    rw [← map_add, ← Lp.toTemperedDistribution_add, hj, v.coe_block,
      BesovSpace.enlargedBlock_littlewoodPaleyBlock]
  exact tendsto_nhds_unique hsum'.tendsto_sum_nat (tendsto_sum_littlewoodPaleyBlock φ v.toDistr)

end Couple

/-! ### The real interpolation theorem for Besov spaces -/

section Interpolation

variable {φ : ContDiffBump (0 : E)} {s₀ s₁ θ : ℝ} {p q₀ q₁ q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]

/-- Every tempered distribution in `B^{(1 - θ) s₀ + θ s₁}_{p,q}` lies in the sum space of
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` when `s₀ ≠ s₁` and `0 < θ < 1`: the interpolated smoothness lies
strictly above `min s₀ s₁`, so `B^{(1 - θ) s₀ + θ s₁}_{p,q}` is already contained in the rougher
endpoint. -/
theorem mem_range_sumSpaceEmbed_besov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q) :
    u ∈ range (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed := by
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · have hs₀ : s₀ < (1 - θ) * s₀ + θ * s₁ := by nlinarith [hθ.1]
    exact ⟨(besov F φ s₀ s₁ p q₀ q₁).fstToSum
      (hu.of_lt hs₀ (zero_lt_one.trans_le Fact.out).ne').toBesovSpace, by simp⟩
  · have hs₁ : s₁ < (1 - θ) * s₀ + θ * s₁ := by nlinarith [hθ.2]
    exact ⟨(besov F φ s₀ s₁ p q₀ q₁).sndToSum
      (hu.of_lt hs₁ (zero_lt_one.trans_le Fact.out).ne').toBesovSpace, by simp⟩

/-- **Real interpolation of Besov spaces**, membership form (Bergh–Löfström, Theorem 6.4.5(1)):
for `s₀ ≠ s₁`, `0 < θ < 1`, and `1 ≤ q`, an element of `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` lies in
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` if and only if its ambient tempered distribution lies in
`B^{(1 - θ) s₀ + θ s₁}_{p,q}`. -/
theorem mem_kMethod_besov_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besov F φ s₀ s₁ p q₀ q₁).SumSpace} :
    u ∈ (besov F φ s₀ s₁ p q₀ q₁).kMethod θ q ↔
      ((besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed u).MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q := by
  have hret := kMethod_eq_comap_of_leftInverse (θ := θ) (q := q)
    (besovToWeightedLpSum (F := F) (φ := φ) (s₀ := s₀) (s₁ := s₁) (p := p)
      (q₀ := q₀) (q₁ := q₁)).toLinearMap
    (I₀ := (BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).toContinuousLinearMap)
    (I₁ := (BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).toContinuousLinearMap)
    (fun x ↦ by simp) (fun x ↦ by simp)
    (weightedLpToBesovSum φ (F := F) (s₀ := s₀) (s₁ := s₁) (p := p)
      (q₀ := q₀) (q₁ := q₁)).toLinearMap
    (P₀ := BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀)
    (P₁ := BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁)
    (fun y ↦ by simp) (fun y ↦ by simp)
    (leftInverse_weightedLpToBesovSum φ)
  have hmem := congr_arg (u ∈ ·) hret
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    mem_kMethod_weightedLp_iff hs hθ hq] at hmem
  rw [hmem, memBesov_iff_memℓp (fun j ↦ (coe_sumSpaceEmbed_besovToWeightedLpSum u j).symm)]
  refine ⟨fun h ↦ h.norm.mono fun j ↦ ?_, fun h ↦ h.mono fun j ↦ ?_⟩
  · rw [Real.norm_of_nonneg (by positivity), norm_smul, RCLike.norm_of_nonneg (by positivity)]
  · rw [norm_smul, RCLike.norm_of_nonneg (by positivity)]

section Equiv

variable [Fact (1 ≤ q)]

/-- The induced `K`-method map from `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` to the weighted
sequence interpolation space; it is norm-nonincreasing because both endpoint maps are isometries. -/
private def besovToWeightedLpKMethod :
    (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q →L[ℂ]
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).KMethodSpace θ q :=
  KMethodSpace.map
    (besovToWeightedLpSum (F := F) (φ := φ) (s₀ := s₀) (s₁ := s₁) (p := p)
      (q₀ := q₀) (q₁ := q₁)).toLinearMap
    (T₀ := (BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).toContinuousLinearMap)
    (T₁ := (BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).toContinuousLinearMap)
    (fun x ↦ by simp) (fun x ↦ by simp)

/-- The induced `K`-method retraction from the weighted sequence interpolation space back to
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}`. -/
private def weightedLpToBesovKMethod (φ : ContDiffBump (0 : E)) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).KMethodSpace θ q →L[ℂ]
      (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q :=
  KMethodSpace.map
    (weightedLpToBesovSum φ (F := F) (s₀ := s₀) (s₁ := s₁) (p := p)
      (q₀ := q₀) (q₁ := q₁)).toLinearMap
    (T₀ := BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀)
    (T₁ := BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁)
    (fun y ↦ by simp) (fun y ↦ by simp)

private def besovKMethodToBesov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q →L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  let W : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q →L[ℂ]
      lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q :=
    (weightedLpKMethodEquiv hs hθ).toContinuousLinearMap.comp besovToWeightedLpKMethod
  LinearMap.mkContinuous
    { toFun u :=
        { toDistr := (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed (toSumₗ u)
          weightedBlocks := W u
          coe_weightedBlocks_apply j := by
            change (weightedLpKMethodEquiv hs hθ (besovToWeightedLpKMethod u) j : 𝓢'(E, F)) = _
            rw [weightedLpKMethodEquiv_apply, besovToWeightedLpKMethod, toSumₗ_map,
              ContinuousLinearMap.coe_coe, Lp.toTemperedDistribution_smul,
              coe_sumSpaceEmbed_besovToWeightedLpSum]
            rfl }
      map_add' u v := BesovSpace.ext (by simp)
      map_smul' c u := BesovSpace.ext (by simp) }
    ‖W‖ fun u ↦ by
      rw [← BesovSpace.norm_weightedBlocks]
      exact W.le_opNorm u

@[simp]
private theorem toDistr_besovKMethodToBesov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q) :
    (besovKMethodToBesov hs hθ u).toDistr =
      (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed (toSumₗ u) :=
  rfl

@[simp]
private theorem weightedBlocks_besovKMethodToBesov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q) :
    (besovKMethodToBesov hs hθ u).weightedBlocks =
      weightedLpKMethodEquiv hs hθ (besovToWeightedLpKMethod u) :=
  rfl

private def besovToBesovKMethod (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q →L[ℂ]
      (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q :=
  (weightedLpToBesovKMethod φ).comp <|
    (weightedLpKMethodEquiv hs hθ).symm.toContinuousLinearMap.comp
      (BesovSpace.weightedBlocksₗᵢ F φ ((1 - θ) * s₀ + θ * s₁) p q).toContinuousLinearMap

/-- **Real interpolation of inhomogeneous Besov spaces** (Bergh–Löfström, Theorem 6.4.5(1)). For
distinct smoothness orders `s₀ ≠ s₁`, `0 < θ < 1`, and `1 ≤ p, q₀, q₁, q ≤ ∞`, the real
interpolation space `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` is isomorphic as a Banach space to
`B^{(1 - θ) s₀ + θ s₁}_{p,q}` via the ambient tempered distribution. -/
def besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.equivOfInverse
    (besovKMethodToBesov hs hθ)
    (besovToBesovKMethod hs hθ)
    (fun u ↦ by
      have hleft := KMethodSpace.leftInverse_map (θ := θ) (q := q)
        (besovToWeightedLpSum (F := F) (φ := φ) (s₀ := s₀) (s₁ := s₁) (p := p)
          (q₀ := q₀) (q₁ := q₁)).toLinearMap
        (I₀ := (BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).toContinuousLinearMap)
        (I₁ := (BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).toContinuousLinearMap)
        (fun x ↦ by simp) (fun x ↦ by simp)
        (weightedLpToBesovSum φ (F := F) (s₀ := s₀) (s₁ := s₁) (p := p)
          (q₀ := q₀) (q₁ := q₁)).toLinearMap
        (P₀ := BesovSpace.ofWeightedBlocksCLM F φ s₀ p q₀)
        (P₁ := BesovSpace.ofWeightedBlocksCLM F φ s₁ p q₁)
        (fun y ↦ by simp) (fun y ↦ by simp)
        (leftInverse_weightedLpToBesovSum φ) u
      simpa [besovToBesovKMethod, besovToWeightedLpKMethod, weightedLpToBesovKMethod] using hleft)
    (fun v ↦ BesovSpace.ext <| by
      have hsum : toSumₗ (besovToBesovKMethod (q₀ := q₀) (q₁ := q₁) hs hθ v) =
          weightedLpToBesovSum φ (q₀ := q₀) (q₁ := q₁)
            (toSumₗ ((weightedLpKMethodEquiv (q₀ := q₀) (q₁ := q₁) hs hθ).symm
              v.weightedBlocks)) := by
        simp [besovToBesovKMethod, weightedLpToBesovKMethod]
      rw [toDistr_besovKMethodToBesov, hsum]
      exact sumSpaceEmbed_weightedLpToBesovSum_eq_toDistr fun j ↦ by
        rw [sumSpaceEmbed_toSumₗ_weightedLpKMethodEquiv_symm_apply]
        exact BesovSpace.inv_weight_smul_weightedBlocks_apply v j)

@[simp]
theorem toDistr_besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q) :
    (besovKMethodEquiv hs hθ u).toDistr =
      (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed (toSumₗ u) := by
  simp [besovKMethodEquiv]

@[simp]
theorem weightedBlocks_besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q) (j : ℕ) :
    (besovKMethodEquiv hs hθ u).weightedBlocks j =
      (((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j) : ℝ) : ℂ) •
        (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed
          (besovToWeightedLpSum (toSumₗ u)) j := by
  simp [besovKMethodEquiv, besovToWeightedLpKMethod]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besovKMethodEquiv_symm (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besov F φ s₀ s₁ p q₀ q₁).sumSpaceEmbed (toSumₗ ((besovKMethodEquiv hs hθ).symm v)) =
      v.toDistr := by
  rw [← toDistr_besovKMethodEquiv hs hθ, ContinuousLinearEquiv.apply_symm_apply]

/-- **Explicit lower bound on the Besov `K`-method norm.** Because the analysis map into the
weighted sequence couple is isometric on both endpoints, the lower bound of
`ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp` transfers with constant `1`:
`(|s₁ - s₀| log 2)^{1/q} 2^{-θ |s₁ - s₀|} ‖u‖_{B^{s_θ}_{p,q}} ≤ ‖u‖_{θ,q}`, with a constant
independent of `φ`, `p`, `q₀`, and `q₁`. -/
theorem mul_norm_besovKMethodEquiv_le (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ s₀ s₁ p q₀ q₁).KMethodSpace θ q) :
    (|s₁ - s₀| * Real.log 2) ^ q.toReal⁻¹ * 2 ^ (-(θ * |s₁ - s₀|)) *
        ‖besovKMethodEquiv hs hθ u‖ ≤
      ‖u‖ := by
  set c : ℝ := (|s₁ - s₀| * Real.log 2) ^ q.toReal⁻¹ * 2 ^ (-(θ * |s₁ - s₀|))
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos
    (mul_pos (abs_pos.2 (sub_ne_zero.2 hs.symm)) (Real.log_pos one_lt_two)) _) (by positivity)
  have hI : ‖besovToWeightedLpKMethod u‖ ≤ ‖u‖ :=
    KMethodSpace.norm_map_le_of_norm_le _ _ _
      (fun x ↦ (BesovSpace.weightedBlocksₗᵢ F φ s₀ p q₀).norm_map x |>.le)
      (fun x ↦ (BesovSpace.weightedBlocksₗᵢ F φ s₁ p q₁).norm_map x |>.le) u
  have hW := ofReal_mul_eLpNorm_le_kMethodENorm_weightedLp (q := q) hs hθ.1.le
    (toSumₗ (besovToWeightedLpKMethod u))
  have heq : eLpNorm (fun j : ℕ ↦ RCLike.ofReal (K := ℂ)
      ((2 : ℝ) ^ (((1 - θ) * s₀ + θ * s₁) * j)) •
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed
        (toSumₗ (besovToWeightedLpKMethod u)) j) q Measure.count =
      ‖(besovKMethodEquiv hs hθ u).weightedBlocks‖ₑ := by
    rw [← lp.eLpNorm_count]
    congr 1
    ext j
    rw [weightedBlocks_besovKMethodEquiv, besovToWeightedLpKMethod, toSumₗ_map,
      ContinuousLinearMap.coe_coe]
    rfl
  rw [heq, ← KMethodSpace.ofReal_norm (besovToWeightedLpKMethod u), ← _root_.ofReal_norm,
    BesovSpace.norm_weightedBlocks, ← ENNReal.ofReal_mul hc.le,
    ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hW
  exact hW.trans hI

end Equiv

end Interpolation

end CompatibleCouple

end TauCeti
