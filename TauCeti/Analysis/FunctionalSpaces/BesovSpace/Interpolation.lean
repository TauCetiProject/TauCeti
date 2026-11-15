/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.Normed.Interpolation.WeightedSequence
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Annulus
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Dyadic retraction and real interpolation of Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space, and let
`Δⱼ` (`j ≥ 0`) be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). By definition, the Besov norm on `B^s_{p,q}` is the
`ℓ^q(ℕ, Lᵖ)` norm of the sequence of weighted blocks `u ↦ (2^{js} Δⱼ u)ⱼ`. This file constructs a
bounded left inverse to that dyadic analysis map, exhibiting `B^s_{p,q}` as a Banach-space retract
of `ℓ^q(ℕ, Lᵖ)` uniformly in `1 ≤ p, q ≤ ∞`, and deduces the real interpolation formula for Besov
spaces from the weighted sequence interpolation theorem
(`TauCeti.CompatibleCouple.weightedLpKMethodEquiv`).

## Dyadic analysis and synthesis

Choose the self-overlap window `L` of `φ` so that `Δₖ u = ∑_{k - L ≤ j < k + L} Δₖ Δⱼ u` for every
`k` and every tempered distribution `u`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico`).
Given a sequence `b ∈ ℓ^q(ℕ, Lᵖ)` with unweighted terms `aⱼ = 2^{-js} bⱼ`, the `k`-th synthesis
piece is

`vₖ = Δₖ (∑_{k - L ≤ j < k + L} aⱼ) ∈ Lᵖ`.

Because `vₖ` is itself an image of `Δₖ`, its Fourier transform vanishes outside the low-frequency
ball `closedBall 0 φ.rOut` when `k = 0` and outside the dyadic annulus
`2^{k-1} φ.rIn ≤ ‖ξ‖ ≤ 2^k φ.rOut` when `k ≥ 1`. Its `Lᵖ` norm satisfies
`2^{ks} ‖vₖ‖_p ≤ C₀ 2^{|s| L} ∑_{k - L ≤ j < k + L} ‖bⱼ‖_p`, so the series `∑ₖ vₖ` converges in
`𝓢'(E, F)` to an element `synthesisCLM F φ s p q b` of `B^s_{p,q}` of norm at most `C ‖b‖`, with
`C` depending only on `E`, `F`, `φ` and `s`, and not on `p` or `q`
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`).

Crucially, the pieces `vₖ` depend only on the unweighted sequence `a = (2^{-js} bⱼ)ⱼ`, not on `s`
or `q`, and when `aⱼ = Δⱼ u` they equal `Δₖ u`, whose partial sums reconstruct `u` in `𝓢'(E, F)`.
Thus `(weightedBlocksCLM, synthesisCLM)` lifts to a retraction between the compatible couple
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` in `𝓢'(E, F)` and the weighted sequence couple
`(ℓ^{q₀}_{s₀}(Lᵖ), ℓ^{q₁}_{s₁}(Lᵖ))` in `ℕ → Lᵖ`. For distinct smoothness orders `s₀ ≠ s₁`,
`0 < θ < 1` and `1 ≤ p, q₀, q₁, q ≤ ∞`, transferring `weightedLpKMethodEquiv` across this
retraction yields

`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}`.

## Main declarations

* `TauCeti.BesovSpace.weightedBlocksₗᵢ`, `TauCeti.BesovSpace.weightedBlocksCLM`: the dyadic
  analysis map `B^s_{p,q} → ℓ^q(ℕ, Lᵖ)` as a linear isometry and continuous linear map.
* `TauCeti.BesovSpace.synthesisCLM`: the bounded dyadic synthesis map
  `ℓ^q(ℕ, Lᵖ) →L[ℂ] B^s_{p,q}`, a left inverse to `weightedBlocksCLM`
  (`TauCeti.BesovSpace.synthesisCLM_weightedBlocksCLM`) with operator norm bounded independently of
  `p` and `q` (`TauCeti.BesovSpace.exists_norm_synthesisCLM_le`).
* `TauCeti.CompatibleCouple.besov`: the compatible couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` inside
  `𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besovToWeightedLpSum`, `TauCeti.CompatibleCouple.weightedLpToBesovSum`,
  `TauCeti.CompatibleCouple.leftInverse_weightedLpToBesovSum`: the retraction of sum spaces onto the
  weighted sequence couple.
* `TauCeti.CompatibleCouple.mem_range_sumSpaceEmbed_besov`,
  `TauCeti.CompatibleCouple.mem_kMethod_besov_iff`: unbundled sum-space and real-interpolation
  membership characterisations for `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})`.
* `TauCeti.CompatibleCouple.besovKMethodEquiv`: the real interpolation equivalence
  `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}` for `s₀ ≠ s₁` and
  `0 < θ < 1`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, §6.2 and §6.4 (Theorems 6.4.3 and 6.4.5(2)).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.4.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren 343, Springer, 2011, §2.7.
-/

public noncomputable section

open Filter Topology MeasureTheory FourierTransform Distribution TemperedDistribution Metric Set
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti.BesovSpace

section Analysis

variable [CompleteSpace F] (F) (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The dyadic analysis map `u ↦ (2^{js} Δⱼ u)ⱼ`, as a linear isometry from `B^s_{p,q}` into
`ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksₗᵢ :
    BesovSpace F φ s p q →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q where
  __ := weightedBlocksₗ F φ s p q
  norm_map' u := by rw [weightedBlocksₗ_apply, norm_weightedBlocks]

/-- The dyadic analysis map `u ↦ (2^{js} Δⱼ u)ⱼ`, as a continuous linear map from `B^s_{p,q}` into
`ℓ^q(ℕ, Lᵖ)`. -/
def weightedBlocksCLM :
    BesovSpace F φ s p q →L[ℂ] lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q :=
  (weightedBlocksₗᵢ F φ s p q).toContinuousLinearMap

variable {F φ s p q}

@[simp]
theorem weightedBlocksₗᵢ_apply (u : BesovSpace F φ s p q) :
    weightedBlocksₗᵢ F φ s p q u = u.weightedBlocks :=
  weightedBlocksₗ_apply u

@[simp]
theorem weightedBlocksCLM_apply (u : BesovSpace F φ s p q) :
    weightedBlocksCLM F φ s p q u = u.weightedBlocks :=
  weightedBlocksₗᵢ_apply u

theorem norm_weightedBlocksCLM (u : BesovSpace F φ s p q) :
    ‖weightedBlocksCLM F φ s p q u‖ = ‖u‖ :=
  (weightedBlocksₗᵢ F φ s p q).norm_map u

theorem weightedBlocksCLM_injective :
    Function.Injective (weightedBlocksCLM F φ s p q) :=
  (weightedBlocksₗᵢ F φ s p q).injective

end Analysis

section Synthesis

/-- The self-overlap window of `φ`, chosen once from
`TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico` independently of smoothness and
integrability exponents. -/
private def synthesisWindow (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (φ : ContDiffBump (0 : E)) : ℕ :=
  (exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ).choose

private theorem synthesisWindow_spec (φ : ContDiffBump (0 : E)) (k : ℕ) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ k u =
      ∑ j ∈ Finset.Ico (k - synthesisWindow F φ) (k + synthesisWindow F φ),
        littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) :=
  (exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ).choose_spec k u

/-- The unweighted sequence `aⱼ = 2^{-js} bⱼ` associated to `b ∈ ℓ^q(ℕ, Lᵖ)`. This matches the
ambient embedding of `CompatibleCouple.weightedLp`. -/
private def unweight (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) (j : ℕ) :
    Lp F p (volume : Measure E) :=
  (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j

private theorem rpow_mul_norm_unweight (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) (j : ℕ) :
    2 ^ (s * j) * ‖unweight s b j‖ = ‖b j‖ := by
  dsimp only [unweight]
  rw [norm_smul, norm_inv, Complex.norm_of_nonneg (by positivity),
    mul_inv_cancel_left₀ (by positivity)]

private theorem unweight_add (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (b b' : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) :
    unweight s (b + b') = unweight s b + unweight s b' := by
  funext j
  simp only [unweight, lp.coeFn_add, Pi.add_apply, smul_add]

private theorem unweight_smul (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℂ)
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) :
    unweight s (c • b) = c • unweight s b := by
  funext j
  dsimp only [unweight, Pi.smul_apply]
  rw [lp.coeFn_smul, Pi.smul_apply, smul_comm]

variable [CompleteSpace F]

/-- The `k`-th localized synthesis piece `Δₖ (∑_{k - L ≤ j < k + L} aⱼ)` in `𝓢'(E, F)` attached
to an unweighted sequence `a : ℕ → Lᵖ`. It depends only on `φ`, `p` and `a`. -/
private def synthesisPieceDistr (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : ℕ → Lp F p (volume : Measure E)) (k : ℕ) : 𝓢'(E, F) :=
  littlewoodPaleyBlock F φ k
    ((∑ j ∈ Finset.Ico (k - synthesisWindow F φ) (k + synthesisWindow F φ), a j :
      Lp F p (volume : Measure E)) : 𝓢'(E, F))

private theorem synthesisPieceDistr_add (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a a' : ℕ → Lp F p (volume : Measure E)) (k : ℕ) :
    synthesisPieceDistr φ (a + a') k = synthesisPieceDistr φ a k + synthesisPieceDistr φ a' k := by
  simp only [synthesisPieceDistr, Pi.add_apply, Finset.sum_add_distrib,
    Lp.toTemperedDistribution_add, map_add]

private theorem synthesisPieceDistr_smul (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : ℂ) (a : ℕ → Lp F p (volume : Measure E)) (k : ℕ) :
    synthesisPieceDistr φ (c • a) k = c • synthesisPieceDistr φ a k := by
  simp only [synthesisPieceDistr, Pi.smul_apply, ← Finset.smul_sum,
    Lp.toTemperedDistribution_smul, map_smul]

/-- When the sequence `a` consists of the Littlewood–Paley blocks of a tempered distribution `u`,
the `k`-th synthesis piece reproduces `Δₖ u`. -/
private theorem synthesisPieceDistr_eq_littlewoodPaleyBlock (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : 𝓢'(E, F)} {a : ℕ → Lp F p (volume : Measure E)}
    (ha : ∀ j, littlewoodPaleyBlock F φ j u = a j) (k : ℕ) :
    synthesisPieceDistr φ a k = littlewoodPaleyBlock F φ k u := by
  rw [synthesisPieceDistr, Lp.toTemperedDistribution_sum, map_sum, synthesisWindow_spec φ k u]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [ha j]

/-- Scaling the `j`-th weighted block of `u ∈ B^s_{p,q}` by `2^{-js}` recovers `u.block j`. -/
@[simp]
theorem inv_smul_weightedBlocks_apply {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : BesovSpace F φ s p q) (j : ℕ) :
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • u.weightedBlocks j = u.block j := by
  rw [u.weightedBlocks_apply, inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

private theorem unweight_weightedBlocks {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : BesovSpace F φ s p q) :
    unweight s u.weightedBlocks = u.block :=
  funext (inv_smul_weightedBlocks_apply u)

/-- **Convergence and uniform Besov bound for dyadic synthesis.** There is `C ≥ 0`, depending only
on `E`, `F`, `φ` and `s` (and not on `p` or `q`), such that for every `b ∈ ℓ^q(ℕ, Lᵖ)` the series
of localized pieces `synthesisPieceDistr φ (unweight s b)` converges in `𝓢'(E, F)` to an element of
`B^s_{p,q}` of norm at most `C ‖b‖`. -/
private theorem exists_hasSum_synthesisPieceDistr_and_norm_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q),
      ∃ v : BesovSpace F φ s p q,
        HasSum (synthesisPieceDistr φ (unweight s b)) v.toDistr ∧ ‖v‖ ≤ C * ‖b‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁⟩ :=
    exists_hasSum_toDistr_and_norm_le_of_annulus (F := F) φ s (half_pos φ.rIn_pos) φ.rOut
  set L := synthesisWindow F φ
  set K : ℝ := max C₀ 0 * 2 ^ (|s| * L)
  have hK : 0 ≤ K := by positivity
  refine ⟨max C₁ 0 * (K * (2 * L)), by positivity, fun {p q} _ _ b ↦ ?_⟩
  set a := unweight s b
  choose g hg hgn using fun k ↦ hC₀ (p := p) k (∑ j ∈ Finset.Ico (k - L) (k + L), a j)
  have hgb (k : ℕ) : IsVanishingOn (𝓕 (g k : 𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ k * φ.rOut))ᶜ := by
    rw [← hg k]
    exact isVanishingOn_fourier_littlewoodPaleyBlock φ k _
  have hga (k : ℕ) (hk : 0 < k) : IsVanishingOn (𝓕 (g k : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 (2 ^ k * (φ.rIn / 2))) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.2 hk
    rw [← hg (m + 1)]
    refine (isVanishingOn_fourier_littlewoodPaleyBlock_succ φ m _).mono ?_
    intro ξ hξ h
    refine h.2 ?_
    convert hξ using 2
    ring
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set B : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun j ↦ ‖b j‖, (lp.memℓp b).norm⟩
  have hBn : ‖B‖ ≤ ‖b‖ := lp.norm_mono hq0 fun j ↦ (norm_norm _).le
  set W : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - L) (k + L), B j, (lp.memℓp B).sum_Ico_sub_add L⟩
  -- The entries of the anonymous `lp` elements `B` and `W` are their defining sequences by `rfl`.
  have hW (k : ℕ) : W k = ∑ j ∈ Finset.Ico (k - L) (k + L), ‖b j‖ := rfl
  have hgk (k : ℕ) : 2 ^ (s * k) * ‖g k‖ ≤ (K • W) k := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hW]
    have hsum := TauCeti.two_rpow_mul_norm_sum_Ico_le s
      (g := a) (x := a) (fun j ↦ (one_mul ‖a j‖).symm.le) k L
    rw [max_eq_left zero_le_one, one_mul,
      Finset.sum_congr rfl fun j _ ↦ rpow_mul_norm_unweight s b j] at hsum
    calc 2 ^ (s * k) * ‖g k‖
        ≤ 2 ^ (s * k) * (max C₀ 0 * ‖∑ j ∈ Finset.Ico (k - L) (k + L), a j‖) := by
          gcongr
          exact (hgn k).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
      _ = max C₀ 0 * (2 ^ (s * k) * ‖∑ j ∈ Finset.Ico (k - L) (k + L), a j‖) := by ring
      _ ≤ max C₀ 0 * (2 ^ (|s| * L) * ∑ j ∈ Finset.Ico (k - L) (k + L), ‖b j‖) :=
          mul_le_mul_of_nonneg_left hsum (le_max_right C₀ 0)
      _ = K * ∑ j ∈ Finset.Ico (k - L) (k + L), ‖b j‖ := by ring
  obtain ⟨v, hv, hvn⟩ := hC₁ g (K • W) hgb hga hgk
  refine ⟨v, ?_, ?_⟩
  · refine hv.congr_fun fun k ↦ ?_
    dsimp only [synthesisPieceDistr, a, L]
    exact hg k
  · calc ‖v‖ ≤ C₁ * ‖K • W‖ := hvn
      _ ≤ max C₁ 0 * ‖K • W‖ :=
          mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (norm_nonneg _)
      _ = max C₁ 0 * (K * ‖W‖) := by rw [norm_smul, Real.norm_of_nonneg hK]
      _ ≤ max C₁ 0 * (K * (2 * L * ‖B‖)) := by
          gcongr
          exact lp.norm_le_of_forall_eq_sum_Ico_sub_add L fun _ ↦ rfl
      _ ≤ max C₁ 0 * (K * (2 * L * ‖b‖)) := by gcongr
      _ = max C₁ 0 * (K * (2 * L)) * ‖b‖ := by ring

variable (F) (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Dyadic synthesis on Besov spaces** (Bergh–Löfström, Theorem 6.4.3). The continuous linear map
`ℓ^q(ℕ, Lᵖ) →L[ℂ] B^s_{p,q}` sending a weighted sequence `b` to
`∑ₖ Δₖ (∑_{k - L ≤ j < k + L} 2^{-js} bⱼ)` in `𝓢'(E, F)`. It is a left inverse to
`weightedBlocksCLM` (`TauCeti.BesovSpace.synthesisCLM_weightedBlocksCLM`) with operator norm
bounded independently of `p` and `q` (`TauCeti.BesovSpace.exists_norm_synthesisCLM_le`). -/
def synthesisCLM :
    lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q →L[ℂ] BesovSpace F φ s p q :=
  let hC := (exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose_spec
  LinearMap.mkContinuous
    { toFun b := (hC.2 b).choose
      map_add' b b' := ext <| by
        rw [toDistr_add]
        refine ((hC.2 (b + b')).choose_spec.1).unique ?_
        convert ((hC.2 b).choose_spec.1).add ((hC.2 b').choose_spec.1) using 2 with k
        rw [unweight_add, synthesisPieceDistr_add]
      map_smul' c b := ext <| by
        rw [RingHom.id_apply, toDistr_smul]
        refine ((hC.2 (c • b)).choose_spec.1).unique ?_
        convert ((hC.2 b).choose_spec.1).const_smul c using 2 with k
        rw [unweight_smul, synthesisPieceDistr_smul] }
    (exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose
    fun b ↦ (hC.2 b).choose_spec.2

variable {F φ s p q}

private theorem hasSum_synthesisPieceDistr_synthesisCLM (φ : ContDiffBump (0 : E)) (s : ℝ)
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q) :
    HasSum (synthesisPieceDistr φ (unweight s b)) (synthesisCLM F φ s p q b).toDistr := by
  rw [synthesisCLM, LinearMap.mkContinuous_apply]
  exact ((exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose_spec.2 b).choose_spec.1

variable (F φ s) in
/-- **Uniform boundedness of dyadic synthesis.** The operator norm of
`synthesisCLM F φ s p q : ℓ^q(ℕ, Lᵖ) →L[ℂ] B^s_{p,q}` is bounded by a constant depending only on
`E`, `F`, `φ` and `s`, and not on `p` or `q`. -/
theorem exists_norm_synthesisCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)],
      ‖synthesisCLM F φ s p q‖ ≤ C := by
  refine ⟨(exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose,
    (exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose_spec.1,
    fun {p q} _ _ ↦ ?_⟩
  rw [synthesisCLM]
  exact LinearMap.mkContinuous_norm_le _
    (exists_hasSum_synthesisPieceDistr_and_norm_le (F := F) φ s).choose_spec.1 _

/-- **Besov spaces are retracts of `ℓ^q(ℕ, Lᵖ)`.** Synthesising the weighted Littlewood–Paley
blocks of `u ∈ B^s_{p,q}` recovers `u`. -/
@[simp]
theorem synthesisCLM_weightedBlocks (u : BesovSpace F φ s p q) :
    synthesisCLM F φ s p q u.weightedBlocks = u := by
  ext1
  have hsum := hasSum_synthesisPieceDistr_synthesisCLM φ s u.weightedBlocks
  have hpiece : synthesisPieceDistr φ (unweight s u.weightedBlocks) =
      fun k ↦ littlewoodPaleyBlock F φ k u.toDistr := by
    funext k
    rw [unweight_weightedBlocks]
    exact synthesisPieceDistr_eq_littlewoodPaleyBlock φ (fun j ↦ (u.coe_block j).symm) k
  rw [hpiece] at hsum
  exact tendsto_nhds_unique hsum.tendsto_sum_nat (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)

theorem synthesisCLM_weightedBlocksCLM (u : BesovSpace F φ s p q) :
    synthesisCLM F φ s p q (weightedBlocksCLM F φ s p q u) = u := by
  rw [weightedBlocksCLM_apply, synthesisCLM_weightedBlocks]

theorem leftInverse_synthesisCLM_weightedBlocksCLM :
    Function.LeftInverse (synthesisCLM F φ s p q) (weightedBlocksCLM F φ s p q) :=
  synthesisCLM_weightedBlocksCLM

@[simp]
theorem synthesisCLM_comp_weightedBlocksCLM :
    (synthesisCLM F φ s p q).comp (weightedBlocksCLM F φ s p q) = ContinuousLinearMap.id ℂ _ := by
  ext1 u
  exact synthesisCLM_weightedBlocksCLM u

theorem synthesisCLM_surjective : Function.Surjective (synthesisCLM F φ s p q) :=
  leftInverse_synthesisCLM_weightedBlocksCLM.surjective

/-- Two weighted sequences with the same unweighted `Lᵖ` sequence synthesise to the same tempered
distribution, regardless of the smoothness orders and fine indices. -/
theorem toDistr_synthesisCLM_eq_of_unweighted_eq {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')]
    {b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q}
    {b' : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q'}
    (h : ∀ j : ℕ, (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • b j =
      (((2 : ℝ) ^ (s' * j) : ℝ) : ℂ)⁻¹ • b' j) :
    (synthesisCLM F φ s p q b).toDistr = (synthesisCLM F φ s' p q' b').toDistr := by
  have hunw : unweight s b = unweight s' b' := funext h
  exact (hasSum_synthesisPieceDistr_synthesisCLM φ s b).unique
    (hunw ▸ hasSum_synthesisPieceDistr_synthesisCLM φ s' b')

/-- If the unweighted sequences of `b₀ ∈ ℓ^{q₀}` and `b₁ ∈ ℓ^{q₁}` sum to the Littlewood–Paley
blocks of a tempered distribution `u`, then the tempered distributions synthesised from `b₀` and
`b₁` sum to `u`. -/
theorem toDistr_synthesisCLM_add_eq_of_littlewoodPaleyBlock_eq {s₀ s₁ : ℝ} {q₀ q₁ : ℝ≥0∞}
    [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    (b₀ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₀)
    (b₁ : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₁) {u : 𝓢'(E, F)}
    (hu : ∀ j : ℕ, littlewoodPaleyBlock F φ j u =
      ((((2 : ℝ) ^ (s₀ * j) : ℝ) : ℂ)⁻¹ • b₀ j + (((2 : ℝ) ^ (s₁ * j) : ℝ) : ℂ)⁻¹ • b₁ j :
        Lp F p (volume : Measure E))) :
    (synthesisCLM F φ s₀ p q₀ b₀).toDistr + (synthesisCLM F φ s₁ p q₁ b₁).toDistr = u := by
  have hsum := (hasSum_synthesisPieceDistr_synthesisCLM φ s₀ b₀).add
    (hasSum_synthesisPieceDistr_synthesisCLM φ s₁ b₁)
  have hpiece : (fun k ↦ synthesisPieceDistr φ (unweight s₀ b₀) k +
        synthesisPieceDistr φ (unweight s₁ b₁) k) =
      fun k ↦ littlewoodPaleyBlock F φ k u := by
    funext k
    rw [← synthesisPieceDistr_add]
    exact synthesisPieceDistr_eq_littlewoodPaleyBlock φ hu k
  rw [hpiece] at hsum
  exact tendsto_nhds_unique hsum.tendsto_sum_nat (tendsto_sum_littlewoodPaleyBlock φ u)

end Synthesis

end TauCeti.BesovSpace

namespace TauCeti.CompatibleCouple

section BesovCouple

variable [CompleteSpace F]

section Defs

variable (F) (φ : ContDiffBump (0 : E)) (p q₀ q₁ : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] (s₀ s₁ : ℝ)

/-- The compatible couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` of inhomogeneous Besov spaces, embedded
into the common ambient space `𝓢'(E, F)` of tempered distributions by
`TauCeti.BesovSpace.toDistrCLM`. -/
def besov : CompatibleCouple ℂ (BesovSpace F φ s₀ p q₀) (BesovSpace F φ s₁ p q₁) 𝓢'(E, F) where
  embed₀ := BesovSpace.toDistrCLM F φ s₀ p q₀
  embed₁ := BesovSpace.toDistrCLM F φ s₁ p q₁
  embed₀_injective _ _ h := BesovSpace.ext (by simpa using h)
  embed₁_injective _ _ h := BesovSpace.ext (by simpa using h)

end Defs

variable {φ : ContDiffBump (0 : E)} {p q₀ q₁ : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {s₀ s₁ : ℝ}

@[simp]
theorem besov_embed₀ :
    (besov F φ p q₀ q₁ s₀ s₁).embed₀ = BesovSpace.toDistrCLM F φ s₀ p q₀ :=
  (rfl)

@[simp]
theorem besov_embed₁ :
    (besov F φ p q₀ q₁ s₀ s₁).embed₁ = BesovSpace.toDistrCLM F φ s₁ p q₁ :=
  (rfl)

@[simp]
theorem besov_swap :
    (besov F φ p q₀ q₁ s₀ s₁).swap = besov F φ p q₁ q₀ s₁ s₀ := by
  ext <;> rfl

/-- The intersection of `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` consists of pairs with the same tempered
distribution. -/
theorem mem_besov_inter_iff {x : BesovSpace F φ s₀ p q₀ × BesovSpace F φ s₁ p q₁} :
    x ∈ (besov F φ p q₀ q₁ s₀ s₁).inter ↔ x.1.toDistr = x.2.toDistr := by
  rw [mem_inter_iff, besov_embed₀, besov_embed₁, BesovSpace.toDistrCLM_apply,
    BesovSpace.toDistrCLM_apply]

/-- Two decompositions in `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` agree exactly when their sums in
`𝓢'(E, F)` agree. -/
theorem besov_fstToSum_add_sndToSum_eq_iff {u₀ v₀ : BesovSpace F φ s₀ p q₀}
    {u₁ v₁ : BesovSpace F φ s₁ p q₁} :
    (besov F φ p q₀ q₁ s₀ s₁).fstToSum u₀ + (besov F φ p q₀ q₁ s₀ s₁).sndToSum u₁ =
        (besov F φ p q₀ q₁ s₀ s₁).fstToSum v₀ + (besov F φ p q₀ q₁ s₀ s₁).sndToSum v₁ ↔
      u₀.toDistr + u₁.toDistr = v₀.toDistr + v₁.toDistr := by
  rw [← (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed_injective.eq_iff]
  simp

/-! ### Couple retraction onto weighted sequence spaces -/

private theorem besovToWeightedLp_compat
    (x : (besov F φ p q₀ q₁ s₀ s₁).inter) :
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum
        (BesovSpace.weightedBlocksCLM F φ s₀ p q₀ ((besov F φ p q₀ q₁ s₀ s₁).interFst x)) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum
        (BesovSpace.weightedBlocksCLM F φ s₁ p q₁ ((besov F φ p q₀ q₁ s₀ s₁).interSnd x)) := by
  apply (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpace_ext
  simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, BesovSpace.weightedBlocksCLM_apply]
  funext j
  simp only [weightedLp_embed₀_apply, weightedLp_embed₁_apply, RCLike.ofReal_eq_complex_ofReal,
    BesovSpace.inv_smul_weightedBlocks_apply, interFst_apply, interSnd_apply]
  exact BesovSpace.block_eq_of_toDistr_eq (mem_besov_inter_iff.1 x.2) j

variable (F φ p q₀ q₁ s₀ s₁) in
/-- The dyadic analysis map on sum spaces, sending `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` to
`ℓ^{q₀}_{s₀}(Lᵖ) + ℓ^{q₁}_{s₁}(Lᵖ)` via `BesovSpace.weightedBlocksCLM` on each endpoint. -/
def besovToWeightedLpSum :
    (besov F φ p q₀ q₁ s₀ s₁).SumSpace →L[ℂ]
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace :=
  (besov F φ p q₀ q₁ s₀ s₁).sumLift
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum.comp
      (BesovSpace.weightedBlocksCLM F φ s₀ p q₀))
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum.comp
      (BesovSpace.weightedBlocksCLM F φ s₁ p q₁))
    besovToWeightedLp_compat

@[simp]
theorem besovToWeightedLpSum_fstToSum (u : BesovSpace F φ s₀ p q₀) :
    besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁ ((besov F φ p q₀ q₁ s₀ s₁).fstToSum u) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum
        (BesovSpace.weightedBlocksCLM F φ s₀ p q₀ u) :=
  (besov F φ p q₀ q₁ s₀ s₁).sumLift_fstToSum _ _ _ u

@[simp]
theorem besovToWeightedLpSum_sndToSum (u : BesovSpace F φ s₁ p q₁) :
    besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁ ((besov F φ p q₀ q₁ s₀ s₁).sndToSum u) =
      (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum
        (BesovSpace.weightedBlocksCLM F φ s₁ p q₁ u) :=
  (besov F φ p q₀ q₁ s₀ s₁).sumLift_sndToSum _ _ _ u

/-- On ambient spaces, `besovToWeightedLpSum` computes the Littlewood–Paley blocks of the
underlying tempered distribution. -/
theorem coe_sumSpaceEmbed_besovToWeightedLpSum
    (u : (besov F φ p q₀ q₁ s₀ s₁).SumSpace) (j : ℕ) :
    ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed
        (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁ u) j : 𝓢'(E, F)) =
      littlewoodPaleyBlock F φ j ((besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed u) := by
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ p q₀ q₁ s₀ s₁).exists_fstToSum_add_sndToSum_eq u
  simp only [map_add, besovToWeightedLpSum_fstToSum, besovToWeightedLpSum_sndToSum,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
    BesovSpace.toDistrCLM_apply, BesovSpace.weightedBlocksCLM_apply, Pi.add_apply,
    weightedLp_embed₀_apply, weightedLp_embed₁_apply, RCLike.ofReal_eq_complex_ofReal,
    BesovSpace.inv_smul_weightedBlocks_apply, Lp.toTemperedDistribution_add,
    BesovSpace.coe_block]

private theorem weightedLpToBesov_compat
    (y : (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).inter) :
    (besov F φ p q₀ q₁ s₀ s₁).fstToSum
        (BesovSpace.synthesisCLM F φ s₀ p q₀
          ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).interFst y)) =
      (besov F φ p q₀ q₁ s₀ s₁).sndToSum
        (BesovSpace.synthesisCLM F φ s₁ p q₁
          ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).interSnd y)) := by
  apply (besov F φ p q₀ q₁ s₀ s₁).sumSpace_ext
  simp only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
    BesovSpace.toDistrCLM_apply]
  refine BesovSpace.toDistr_synthesisCLM_eq_of_unweighted_eq fun j ↦ ?_
  have hy :=
    congr_fun ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).mem_inter_iff.1 y.2) j
  simpa only [weightedLp_embed₀_apply, weightedLp_embed₁_apply, RCLike.ofReal_eq_complex_ofReal,
    interFst_apply, interSnd_apply] using hy

variable (F φ p q₀ q₁ s₀ s₁) in
/-- The dyadic synthesis map on sum spaces, sending `ℓ^{q₀}_{s₀}(Lᵖ) + ℓ^{q₁}_{s₁}(Lᵖ)` to
`B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` via `BesovSpace.synthesisCLM` on each endpoint. -/
def weightedLpToBesovSum :
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace →L[ℂ]
      (besov F φ p q₀ q₁ s₀ s₁).SumSpace :=
  (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift
    ((besov F φ p q₀ q₁ s₀ s₁).fstToSum.comp (BesovSpace.synthesisCLM F φ s₀ p q₀))
    ((besov F φ p q₀ q₁ s₀ s₁).sndToSum.comp (BesovSpace.synthesisCLM F φ s₁ p q₁))
    weightedLpToBesov_compat

@[simp]
theorem weightedLpToBesovSum_fstToSum
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₀) :
    weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁
        ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).fstToSum b) =
      (besov F φ p q₀ q₁ s₀ s₁).fstToSum (BesovSpace.synthesisCLM F φ s₀ p q₀ b) :=
  (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift_fstToSum _ _ _ b

@[simp]
theorem weightedLpToBesovSum_sndToSum
    (b : lp (fun _ : ℕ ↦ Lp F p (volume : Measure E)) q₁) :
    weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁
        ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sndToSum b) =
      (besov F φ p q₀ q₁ s₀ s₁).sndToSum (BesovSpace.synthesisCLM F φ s₁ p q₁ b) :=
  (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumLift_sndToSum _ _ _ b

/-- If the ambient sequence of `z ∈ ℓ^{q₀}_{s₀}(Lᵖ) + ℓ^{q₁}_{s₁}(Lᵖ)` consists of the
Littlewood–Paley blocks of `u ∈ 𝓢'(E, F)`, then `weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁ z` has
ambient tempered distribution `u`. -/
theorem sumSpaceEmbed_weightedLpToBesovSum_eq_of_littlewoodPaleyBlock_eq
    (z : (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).SumSpace) {u : 𝓢'(E, F)}
    (hu : ∀ j : ℕ, littlewoodPaleyBlock F φ j u =
      ((weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).sumSpaceEmbed z j : 𝓢'(E, F))) :
    (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed (weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁ z) = u := by
  obtain ⟨b₀, b₁, rfl⟩ :=
    (weightedLp ℂ (Lp F p (volume : Measure E)) q₀ q₁ s₀ s₁).exists_fstToSum_add_sndToSum_eq z
  simp only [map_add, weightedLpToBesovSum_fstToSum, weightedLpToBesovSum_sndToSum,
    sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
    BesovSpace.toDistrCLM_apply]
  refine BesovSpace.toDistr_synthesisCLM_add_eq_of_littlewoodPaleyBlock_eq b₀ b₁ fun j ↦ ?_
  simpa only [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, Pi.add_apply,
    weightedLp_embed₀_apply, weightedLp_embed₁_apply, RCLike.ofReal_eq_complex_ofReal] using hu j

/-- **Retraction of Besov couples onto weighted sequence couples** (Bergh–Löfström, Theorem 6.4.3).
Dyadic synthesis `weightedLpToBesovSum` is a left inverse to dyadic analysis
`besovToWeightedLpSum` on sum spaces. -/
theorem leftInverse_weightedLpToBesovSum :
    Function.LeftInverse
      (weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁) (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁) :=
  leftInverse_sumLift _ _ besovToWeightedLp_compat _ _ weightedLpToBesov_compat
    BesovSpace.leftInverse_synthesisCLM_weightedBlocksCLM
    BesovSpace.leftInverse_synthesisCLM_weightedBlocksCLM

@[simp]
theorem weightedLpToBesovSum_besovToWeightedLpSum
    (u : (besov F φ p q₀ q₁ s₀ s₁).SumSpace) :
    weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁ (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁ u) = u :=
  leftInverse_weightedLpToBesovSum u

/-! ### Real interpolation of Besov spaces -/

section Interpolation

variable {θ : ℝ} {q : ℝ≥0∞}

/-- Every tempered distribution in `B^{s_θ}_{p,q}`, where `s_θ = (1 - θ) s₀ + θ s₁`, lies in the
sum space `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` for distinct `s₀ ≠ s₁`, `0 < θ < 1` and `q ≠ 0`. -/
theorem mem_range_sumSpaceEmbed_besov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : q ≠ 0)
    {u : 𝓢'(E, F)} (hu : u.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q) :
    u ∈ range (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed := by
  obtain ⟨a, ha, hmem⟩ := memBesov_iff.1 hu
  set s := (1 - θ) * s₀ + θ * s₁
  have hmem' : Memℓp (fun j : ℕ ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • a j) q :=
    hmem.mono fun j ↦ le_of_eq <| by
      rw [norm_smul, Complex.norm_of_nonneg (by positivity)]
  have ha_lt : eLpNorm (fun j : ℕ ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • a j) q Measure.count < ∞ :=
    (memℓp_iff_eLpNorm_count_lt_top hq).1 hmem'
  obtain ⟨z, hz⟩ := mem_range_sumSpaceEmbed_weightedLp (𝕜 := ℂ)
    (A := Lp F p (volume : Measure E)) (q₀ := q₀) (q₁ := q₁) hs hθ hq ha_lt
  refine ⟨weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁ z,
    sumSpaceEmbed_weightedLpToBesovSum_eq_of_littlewoodPaleyBlock_eq z fun j ↦ ?_⟩
  rw [hz]
  exact ha j

/-- **Real interpolation of Besov spaces**, membership form: for distinct `s₀ ≠ s₁`, `0 < θ < 1`
and `1 ≤ q`, an element `u` of `B^{s₀}_{p,q₀} + B^{s₁}_{p,q₁}` lies in
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` exactly when its underlying tempered distribution lies in
`B^{(1 - θ) s₀ + θ s₁}_{p,q}`. -/
theorem mem_kMethod_besov_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besov F φ p q₀ q₁ s₀ s₁).SumSpace} :
    u ∈ (besov F φ p q₀ q₁ s₀ s₁).kMethod θ q ↔
      ((besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed u).MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q := by
  have hret := kMethod_eq_comap_of_leftInverse (θ := θ) (q := q)
    (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁).toLinearMap
    besovToWeightedLpSum_fstToSum besovToWeightedLpSum_sndToSum
    (weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁).toLinearMap
    weightedLpToBesovSum_fstToSum weightedLpToBesovSum_sndToSum
    leftInverse_weightedLpToBesovSum
  rw [hret, Submodule.mem_comap, ContinuousLinearMap.coe_coe, mem_kMethod_weightedLp_iff hs hθ hq,
    memBesov_iff_memℓp fun j ↦ (coe_sumSpaceEmbed_besovToWeightedLpSum u j).symm]
  refine ⟨fun h ↦ h.norm.mono fun j ↦ le_of_eq ?_, fun h ↦ h.mono fun j ↦ le_of_eq ?_⟩
  · rw [RCLike.ofReal_eq_complex_ofReal, Real.norm_of_nonneg (by positivity), norm_smul,
      Complex.norm_of_nonneg (by positivity)]
  · rw [RCLike.ofReal_eq_complex_ofReal, norm_smul, Complex.norm_of_nonneg (by positivity)]

section Equiv

variable [Fact (1 ≤ q)]

open KMethodSpace

/-- The forward continuous linear map `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} →L[ℂ] B^{s_θ}_{p,q}`,
sending `u` to the element whose weighted block sequence is `weightedLpKMethodEquiv` of
`besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁ u`. -/
private def besovKMethodToBesov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q →L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  let T := (weightedLpKMethodEquiv (𝕜 := ℂ) (A := Lp F p (volume : Measure E))
      (q₀ := q₀) (q₁ := q₁) (q := q) hs hθ).toContinuousLinearMap.comp
    (KMethodSpace.map (θ := θ) (q := q) (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁).toLinearMap
      besovToWeightedLpSum_fstToSum besovToWeightedLpSum_sndToSum)
  LinearMap.mkContinuous
    { toFun u :=
        { toDistr := (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u)
          weightedBlocks := T u
          coe_weightedBlocks_apply j := by
            simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
              weightedLpKMethodEquiv_apply, toSumₗ_map, ContinuousLinearMap.coe_coe,
              RCLike.ofReal_eq_complex_ofReal, Lp.toTemperedDistribution_smul,
              coe_sumSpaceEmbed_besovToWeightedLpSum] }
      map_add' u v := BesovSpace.ext (by simp)
      map_smul' c u := BesovSpace.ext (by simp) }
    ‖T‖ fun u ↦ by
      rw [← BesovSpace.norm_weightedBlocks]
      exact T.le_opNorm u

private theorem toDistr_besovKMethodToBesov (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q) :
    (besovKMethodToBesov hs hθ u).toDistr =
      (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ u) := by
  simp [besovKMethodToBesov]

/-- The backward continuous linear map `B^{s_θ}_{p,q} →L[ℂ] (B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}`,
synthesising the inverse of `weightedLpKMethodEquiv` applied to `weightedBlocksCLM`. -/
private def besovToBesovKMethod (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q →L[ℂ]
      (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q :=
  (KMethodSpace.map (θ := θ) (q := q) (weightedLpToBesovSum F φ p q₀ q₁ s₀ s₁).toLinearMap
      weightedLpToBesovSum_fstToSum weightedLpToBesovSum_sndToSum).comp
    ((weightedLpKMethodEquiv (𝕜 := ℂ) (A := Lp F p (volume : Measure E))
        (q₀ := q₀) (q₁ := q₁) (q := q) hs hθ).symm.toContinuousLinearMap.comp
      (BesovSpace.weightedBlocksCLM F φ ((1 - θ) * s₀ + θ * s₁) p q))

private theorem sumSpaceEmbed_toSumₗ_besovToBesovKMethod (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed (toSumₗ (besovToBesovKMethod hs hθ v)) =
      v.toDistr := by
  simp only [besovToBesovKMethod, ContinuousLinearMap.comp_apply, toSumₗ_map,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    BesovSpace.weightedBlocksCLM_apply]
  refine sumSpaceEmbed_weightedLpToBesovSum_eq_of_littlewoodPaleyBlock_eq _ fun j ↦ ?_
  rw [sumSpaceEmbed_toSumₗ_weightedLpKMethodEquiv_symm_apply, RCLike.ofReal_eq_complex_ofReal,
    BesovSpace.inv_smul_weightedBlocks_apply, v.coe_block]

/-- **Real interpolation of Besov spaces** (Bergh–Löfström, Theorem 6.4.5(2)). For distinct
smoothness orders `s₀ ≠ s₁`, `0 < θ < 1` and `1 ≤ p, q₀, q₁, q ≤ ∞`, the real interpolation space
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q}` is isomorphic to `B^{(1 - θ) s₀ + θ s₁}_{p,q}`, preserving
the underlying tempered distribution (`toDistr_besovKMethodEquiv`). -/
def besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.equivOfInverse
    (besovKMethodToBesov hs hθ)
    (besovToBesovKMethod hs hθ)
    (fun u ↦ KMethodSpace.ext <| (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed_injective <| by
      rw [sumSpaceEmbed_toSumₗ_besovToBesovKMethod, toDistr_besovKMethodToBesov])
    (fun v ↦ BesovSpace.ext <| by
      rw [toDistr_besovKMethodToBesov, sumSpaceEmbed_toSumₗ_besovToBesovKMethod])

@[simp]
theorem toDistr_besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q) :
    (besovKMethodEquiv hs hθ u).toDistr =
      (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed (KMethodSpace.toSumₗ u) :=
  toDistr_besovKMethodToBesov hs hθ u

@[simp]
theorem sumSpaceEmbed_toSumₗ_besovKMethodEquiv_symm (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besov F φ p q₀ q₁ s₀ s₁).sumSpaceEmbed
        (KMethodSpace.toSumₗ ((besovKMethodEquiv hs hθ).symm v)) =
      v.toDistr :=
  sumSpaceEmbed_toSumₗ_besovToBesovKMethod hs hθ v

@[simp]
theorem weightedBlocks_besovKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besov F φ p q₀ q₁ s₀ s₁).KMethodSpace θ q) :
    (besovKMethodEquiv hs hθ u).weightedBlocks =
      weightedLpKMethodEquiv hs hθ
        (KMethodSpace.map (besovToWeightedLpSum F φ p q₀ q₁ s₀ s₁).toLinearMap
          besovToWeightedLpSum_fstToSum besovToWeightedLpSum_sndToSum u) := by
  simp [besovKMethodEquiv, besovKMethodToBesov]

end Equiv

end Interpolation

end BesovCouple

end TauCeti.CompatibleCouple
