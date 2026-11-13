/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Bessel-potential spaces between Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space, with
inhomogeneous Littlewood–Paley blocks `Δⱼ`, and let `1 ≤ p ≤ ∞`. For every real `s`, Mathlib's
Bessel-potential space `H^{s,p}` lies between two Besov spaces built from `φ`:

`B^s_{p,1} ⊆ H^{s,p} ⊆ B^s_{p,∞}`,

with continuous inclusions that keep the underlying tempered distribution. The fine index `q`
of `B^s_{p,q}` is what separates the three spaces; the smoothness `s` and the integrability `p`
are the same.

Both inclusions rest on the localized estimate `‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖Δⱼ u‖_p` for the
Bessel potential `J^s` on a single block, with `C` independent of `j` and `p`
(`TemperedDistribution.exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le`).

* If `J^s u = f ∈ Lᵖ`, then `Δⱼ u = J^{-s} Δⱼ f`, because the blocks commute with the Bessel
  potentials. The blocks are bounded on `Lᵖ` uniformly in `j`, so the localized estimate of order
  `-s` gives `2^{js} ‖Δⱼ u‖_p ≤ C ‖f‖_p` for every `j`: this is `u ∈ B^s_{p,∞}`.
* If the weighted blocks `2^{js} ‖Δⱼ u‖_p` are summable, then by the localized estimate of order
  `s` the series `∑ⱼ J^s Δⱼ u` converges absolutely in `Lᵖ`. Since `u = ∑ⱼ Δⱼ u` in the tempered
  distributions and `J^s` is continuous there, its sum is `J^s u`, which is therefore an `Lᵖ`
  function: this is `u ∈ H^{s,p}`.

## Main declarations

* `TemperedDistribution.MemSobolev.memBesov`: `H^{s,p} ⊆ B^s_{p,∞}` for tempered distributions.
* `TemperedDistribution.MemBesov.memSobolev`: `B^s_{p,1} ⊆ H^{s,p}` for tempered distributions.
* `BesselPotentialSpace.toBesovSpace`: the inclusion `H^{s,p} → B^s_{p,∞}` as a continuous
  linear map.
* `TauCeti.BesovSpace.toBesselPotentialSpace`: the inclusion `B^s_{p,1} → H^{s,p}` as a
  continuous linear map.
* `SchwartzMap.memBesov`: Schwartz functions lie in every Besov space `B^s_{p,q}`, `q ≠ 0`, since
  they lie in `H^{s+1,p} ⊆ B^{s+1}_{p,∞}`.
* `SchwartzMap.toBesovSpaceLM`: the inclusion of the Schwartz functions in `B^s_{p,q}`, with
  blocks computed by `TauCeti.BesovSpace.block_toBesovSpaceLM`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 6.2.4.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.3, Proposition 2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace TemperedDistribution

variable (φ s) in
/-- The quantitative form of `H^{s,p} ⊆ B^s_{p,∞}`: if `J^s u = f ∈ Lᵖ`, then every block
`Δⱼ u` is an `Lᵖ` function `g` with `2^{js} ‖g‖_p ≤ C ‖f‖_p`, for a constant `C` independent of
`p` and `j`. -/
private theorem exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_besselPotential_eq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢'(E, F))
      (f : Lp F p (volume : Measure E)), besselPotential E F s u = f → ∀ j : ℕ,
      ∃ g : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j u = g ∧ 2 ^ (s * j) * ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨C₁, hC₁⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₂, hC₂, hJ⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ (-s)
  refine ⟨C₂ * max C₁ 0, by positivity, fun {p} _ u f hf j ↦ ?_⟩
  -- `Δⱼ f` is an `Lᵖ` function `f₁`, and `Δⱼ u = J^{-s} Δⱼ f` is the `Lᵖ` function `g`.
  obtain ⟨f₁, hf₁, hf₁f⟩ := hC₁ j f
  obtain ⟨g, hg, hgf₁⟩ := hJ j (f : 𝓢'(E, F)) f₁ hf₁
  have hu : u = besselPotential E F (-s) f := ((besselPotential_neg_apply_eq_iff s _ _).2 hf).symm
  refine ⟨g, by rw [hu, littlewoodPaleyBlock_besselPotential_comm, hg], ?_⟩
  -- The weights `2^{js}` and `2^{-js}` cancel.
  have hcancel : (2 : ℝ) ^ (s * j) * 2 ^ (-s * j) = 1 := by
    rw [← Real.rpow_add two_pos, neg_mul, add_neg_cancel, Real.rpow_zero]
  calc 2 ^ (s * j) * ‖g‖ ≤ 2 ^ (s * j) * (C₂ * 2 ^ (-s * j) * ‖f₁‖) := by gcongr
    _ = C₂ * ‖f₁‖ := by linear_combination C₂ * ‖f₁‖ * hcancel
    _ ≤ C₂ * (max C₁ 0 * ‖f‖) := by
        gcongr
        exact hf₁f.trans (by gcongr; exact le_max_left _ _)
    _ = C₂ * max C₁ 0 * ‖f‖ := by ring

/-- **`H^{s,p} ⊆ B^s_{p,∞}`.** A tempered distribution in the Bessel-potential space `H^{s,p}`
lies in the Besov space `B^s_{p,∞}` built from any Littlewood–Paley partition. -/
theorem MemSobolev.memBesov {u : 𝓢'(E, F)} (hu : u.MemSobolev s p) (φ : ContDiffBump (0 : E)) :
    u.MemBesov φ s p ∞ := by
  obtain ⟨C, -, hC⟩ :=
    exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_besselPotential_eq (F := F) φ s
  obtain ⟨f, hf⟩ := hu
  choose g hg hgf using hC u f hf
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty ⟨C * ‖f‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgf j

variable (φ s) in
/-- The quantitative form of `B^s_{p,1} ⊆ H^{s,p}`: if the blocks `Δⱼ u` are `Lᵖ` functions `fⱼ`
with `∑ⱼ 2^{js} ‖fⱼ‖_p < ∞`, then `J^s u` is an `Lᵖ` function `g` with
`‖g‖_p ≤ C ∑ⱼ 2^{js} ‖fⱼ‖_p`, for a constant `C` independent of `p`. -/
private theorem exists_besselPotential_eq_and_norm_le_of_summable :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢'(E, F))
      (f : ℕ → Lp F p (volume : Measure E)), (∀ j, littlewoodPaleyBlock F φ j u = f j) →
      Summable (fun j : ℕ ↦ 2 ^ (s * j) * ‖f j‖) →
      ∃ g : Lp F p (volume : Measure E), besselPotential E F s u = g ∧
        ‖g‖ ≤ C * ∑' j : ℕ, 2 ^ (s * j) * ‖f j‖ := by
  obtain ⟨C, hC, hJ⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ s
  refine ⟨C, hC, fun {p} _ u f hf hsum ↦ ?_⟩
  -- `J^s Δⱼ u` is the `Lᵖ` function `h j`, and these are absolutely summable in `Lᵖ`.
  choose h hh hhf using fun j ↦ hJ j u (f j) (hf j)
  have hbound (j : ℕ) : ‖h j‖ ≤ C * (2 ^ (s * j) * ‖f j‖) := (hhf j).trans_eq (by ring)
  have hsum' : Summable fun j ↦ ‖h j‖ :=
    (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  set g := ∑' j, h j
  refine ⟨g, ?_, ?_⟩
  · -- Both sides are limits of `J^s ∑_{j < N} Δⱼ u = ∑_{j < N} h j` in the tempered
    -- distributions.
    have hlim₁ : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (h j : 𝓢'(E, F))) atTop
        (𝓝 (g : 𝓢'(E, F))) := by
      have hg := hsum'.of_norm.hasSum.map (Lp.toTemperedDistributionCLM F volume p)
        (Lp.toTemperedDistributionCLM F volume p).continuous
      exact hg.tendsto_sum_nat
    have hlim₂ := ((besselPotential E F s).continuous.tendsto u).comp
      (tendsto_sum_littlewoodPaleyBlock φ u)
    refine tendsto_nhds_unique hlim₂ ?_
    convert hlim₁ using 2 with N
    simp [hh]
  · calc ‖g‖ ≤ ∑' j, ‖h j‖ := norm_tsum_le_tsum_norm hsum'
      _ ≤ ∑' j : ℕ, C * (2 ^ (s * j) * ‖f j‖) :=
        hsum'.tsum_le_tsum hbound (hsum.mul_left C)
      _ = C * ∑' j : ℕ, 2 ^ (s * j) * ‖f j‖ := tsum_mul_left

/-- **`B^s_{p,1} ⊆ H^{s,p}`.** A tempered distribution in the Besov space `B^s_{p,1}` lies in the
Bessel-potential space `H^{s,p}`. -/
theorem MemBesov.memSobolev {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p 1) : u.MemSobolev s p := by
  obtain ⟨C, -, hC⟩ := exists_besselPotential_eq_and_norm_le_of_summable (F := F) φ s
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  have hsum : Summable fun j : ℕ ↦ 2 ^ (s * j) * ‖f j‖ := by
    refine ((memℓp_gen_iff (by simp)).1 hmem).congr fun j ↦ ?_
    rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg (by positivity)]
  obtain ⟨g, hg, -⟩ := hC u f hf hsum
  exact ⟨g, hg⟩

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution TauCeti

variable (φ) in
/-- **The inclusion `H^{s,p} ⊆ B^s_{p,∞}`**, as a continuous linear map from Mathlib's
Bessel-potential space to the Besov space built from `φ`. It keeps the underlying tempered
distribution (`BesselPotentialSpace.toDistr_toBesovSpace`). -/
def toBesovSpace : H^{s, p}(E, F) →L[ℂ] BesovSpace F φ s p ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memSobolev_toDistr.memBesov φ).toBesovSpace
      map_add' u v := BesovSpace.ext (by simp)
      map_smul' c u := BesovSpace.ext (by simp) } <| by
    obtain ⟨C, -, hC⟩ :=
      exists_littlewoodPaleyBlock_eq_and_rpow_mul_norm_le_of_besselPotential_eq (F := F) φ s
    refine ⟨C, fun u ↦ ?_⟩
    set v := (u.memSobolev_toDistr.memBesov φ).toBesovSpace
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ← norm_toLp_eq]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgf⟩ := hC u.toDistr u.toLp u.bessel_toDistr_eq_toLp j
    -- The block of `v` is the `Lᵖ` function `g`, since both represent `Δⱼ u`.
    have hvg : v.block j = g := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
        BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
    rw [hvg]
    exact hgf

@[simp]
theorem toDistr_toBesovSpace (u : H^{s, p}(E, F)) : (toBesovSpace φ u).toDistr = u.toDistr := by
  simp [toBesovSpace]

end BesselPotentialSpace

namespace SchwartzMap

open TemperedDistribution

/-- **Schwartz functions lie in every Besov space.** A Schwartz function lies in `H^{s+1,p}`,
hence in `B^{s+1}_{p,∞}`, hence in `B^s_{p,q}` for every fine index `q ≠ 0`. -/
theorem memBesov (f : 𝓢(E, F)) (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {q : ℝ≥0∞} (hq : q ≠ 0) : (f : 𝓢'(E, F)).MemBesov φ s p q :=
  ((f.memSobolev (s := s + 1) (p := p)).memBesov φ).of_lt (lt_add_one s) hq

variable (F) in
/-- The inclusion of the Schwartz functions in the Besov space `B^s_{p,q}`. -/
def toBesovSpaceLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] : 𝓢(E, F) →ₗ[ℂ] TauCeti.BesovSpace F φ s p q where
  toFun f := (f.memBesov φ s p (zero_lt_one.trans_le Fact.out).ne').toBesovSpace
  map_add' f g := TauCeti.BesovSpace.ext <| by
    simp only [TauCeti.BesovSpace.toDistr_add, MemBesov.toDistr_toBesovSpace, map_add]
  map_smul' c f := TauCeti.BesovSpace.ext <| by
    simp only [TauCeti.BesovSpace.toDistr_smul, MemBesov.toDistr_toBesovSpace, map_smul,
      RingHom.id_apply]

@[simp]
theorem toDistr_toBesovSpaceLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (f : 𝓢(E, F)) : (toBesovSpaceLM F φ s p q f).toDistr = f :=
  MemBesov.toDistr_toBesovSpace _

end SchwartzMap

namespace TauCeti.BesovSpace

open TemperedDistribution

/-- **The inclusion `B^s_{p,1} ⊆ H^{s,p}`**, as a continuous linear map from the Besov space built
from `φ` to Mathlib's Bessel-potential space. It keeps the underlying tempered distribution
(`TauCeti.BesovSpace.toDistr_toBesselPotentialSpace`). -/
def toBesselPotentialSpace : BesovSpace F φ s p 1 →L[ℂ] H^{s, p}(E, F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := u.memBesov_toDistr.memSobolev.toBesselPotentialSpace
      map_add' u v := BesselPotentialSpace.ext (by simp)
      map_smul' c u := BesselPotentialSpace.ext (by simp) } <| by
    obtain ⟨C, -, hC⟩ := exists_besselPotential_eq_and_norm_le_of_summable (F := F) φ s
    refine ⟨C, fun u ↦ ?_⟩
    set w := u.memBesov_toDistr.memSobolev.toBesselPotentialSpace
    have hsum : Summable fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖ := by
      have h := (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp u.weightedBlocks)
      simpa [norm_weightedBlocks_apply] using h
    obtain ⟨g, hg, hgf⟩ := hC u.toDistr u.block (fun j ↦ (coe_block u j).symm) hsum
    -- The `Lᵖ` part of `w` is `g`, since both represent `J^s u`.
    have hwg : w.toLp = g := LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
        ← w.bessel_toDistr_eq_toLp, ← hg, w, MemSobolev.toBesselPotentialSpace_toDistr]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ← BesselPotentialSpace.norm_toLp_eq]
    rw [hwg, norm_eq_tsum_rpow ENNReal.one_ne_top]
    simpa using hgf

@[simp]
theorem toDistr_toBesselPotentialSpace (u : BesovSpace F φ s p 1) :
    (toBesselPotentialSpace u).toDistr = u.toDistr := by
  simp [toBesselPotentialSpace]

/-- The `j`-th block of a Schwartz function `f` is the Schwartz function `𝓕⁻ (ψⱼ • 𝓕 f)`, where
`ψⱼ` is the `j`-th piece of the Littlewood–Paley partition. -/
@[simp]
theorem block_toBesovSpaceLM {q : ℝ≥0∞} [Fact (1 ≤ q)] (f : 𝓢(E, F)) (j : ℕ) :
    (SchwartzMap.toBesovSpaceLM F φ s p q f).block j =
      (SchwartzMap.fourierMultiplierCLM F
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f).toLp p :=
  Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, SchwartzMap.toDistr_toBesovSpaceLM,
      littlewoodPaleyBlock_toTemperedDistributionCLM_eq, Lp.toTemperedDistribution_toLp_eq]

end TauCeti.BesovSpace
