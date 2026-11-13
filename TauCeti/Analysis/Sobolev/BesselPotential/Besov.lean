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

At `p = q = 2` the inclusions close up: for a complex Hilbert space `H`, the Besov space
`B^s_{2,2}` and the Bessel-potential space `H^{s,2}` contain the same tempered distributions, with
equivalent norms,

`‖u‖_{H^s}² = ‖J^s u‖₂² ≍ ∑ⱼ 2^{2js} ‖Δⱼ u‖₂² = ‖u‖_{B^s_{2,2}}²`,

with constants depending on `φ` and `s`. The order `0` case is Plancherel's theorem for the blocks:
the blocks of an `L²` function are square summable in `L²`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_sum_norm_sq_le`), and a tempered
distribution whose blocks are square-summable `L²` functions is an `L²` function
(`TemperedDistribution.exists_eq_and_norm_sq_le_of_littlewoodPaleyBlock_eq`). The localized
estimate at `p = 2` for `J^s` and `J^{-s}` reduces every order to order `0`. Thus at `p = q = 2`
the Besov scale is the Sobolev scale, which is how statements proved for Besov spaces (dyadic
estimates, paraproducts) specialize to `H^s`.

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
* `TemperedDistribution.memBesov_two_two_iff_memSobolev`: `u ∈ B^s_{2,2}` if and only if
  `u ∈ H^{s,2}`.
* `TauCeti.BesovSpace.besselPotentialSpaceEquiv`: the identity on tempered distributions as an
  isomorphism of normed spaces `B^s_{2,2} ≃L[ℂ] H^{s,2}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 6.2.4.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Chapter 2 (the Littlewood–Paley decomposition and Besov spaces).
* H. Triebel, *Theory of Function Spaces*, Section 2.3.3, Proposition 2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
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
    have hvg : v.block j = g := Lp.toTemperedDistribution_injective <| by
      simp only [BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
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
    have hwg : w.toLp = g := Lp.toTemperedDistribution_injective <| by
      simp only [← w.bessel_toDistr_eq_toLp, ← hg, w, MemSobolev.toBesselPotentialSpace_toDistr]
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

/-! ### `B^s_{2,2} = H^{s,2}` -/

namespace TemperedDistribution

variable (φ s) in
/-- `∑ⱼ (2^{sj} ‖fⱼ‖)²` controls `‖J^s u‖²` when the `fⱼ` are the blocks of `u`. -/
private theorem exists_besselPotential_eq_and_norm_sq_le :
    ∃ C : ℝ, ∀ (u : 𝓢'(E, H)) (f : ℕ → Lp H 2 (volume : Measure E)),
      (∀ j, littlewoodPaleyBlock H φ j u = f j) →
        Summable (fun j : ℕ ↦ (2 ^ (s * j) * ‖f j‖) ^ 2) →
          ∃ w : Lp H 2 (volume : Measure E), besselPotential E H s u = w ∧
            ‖w‖ ^ 2 ≤ C * ∑' j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 := by
  obtain ⟨C₁, -, hC₁⟩ := exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := H) φ s
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_eq_and_norm_sq_le_of_littlewoodPaleyBlock_eq (H := H) φ
  refine ⟨C₂ * C₁ ^ 2, fun u f hf hsum ↦ ?_⟩
  choose g hg hgf using fun j ↦ hC₁ (p := 2) j u (f j) (hf j)
  have hgf' : ∀ j, ‖g j‖ ^ 2 ≤ C₁ ^ 2 * (2 ^ (s * j) * ‖f j‖) ^ 2 := fun j ↦ by
    rw [← mul_pow, ← mul_assoc]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgf j) 2
  have hsum' : Summable fun j ↦ ‖g j‖ ^ 2 :=
    (hsum.mul_left (C₁ ^ 2)).of_nonneg_of_le (fun j ↦ by positivity) hgf'
  obtain ⟨w, hw, hwg⟩ :=
    hC₂ _ g (fun j ↦ (littlewoodPaleyBlock_besselPotential_comm φ s j u).trans (hg j)) hsum'
  refine ⟨w, hw, hwg.trans ?_⟩
  calc C₂ * ∑' j, ‖g j‖ ^ 2 ≤ C₂ * ∑' j : ℕ, C₁ ^ 2 * (2 ^ (s * j) * ‖f j‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (hsum'.tsum_le_tsum hgf' (hsum.mul_left _)) hC₂0
    _ = C₂ * C₁ ^ 2 * ∑' j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 := by rw [tsum_mul_left, mul_assoc]

variable (φ s) in
/-- `‖J^s u‖²` controls `∑ⱼ (2^{sj} ‖Δⱼ u‖)²`. -/
private theorem exists_littlewoodPaleyBlock_eq_and_sum_sq_le :
    ∃ C : ℝ, ∀ (u : 𝓢'(E, H)) (w : Lp H 2 (volume : Measure E)), besselPotential E H s u = w →
      ∃ f : ℕ → Lp H 2 (volume : Measure E), (∀ j, littlewoodPaleyBlock H φ j u = f j) ∧
        ∀ t : Finset ℕ, ∑ j ∈ t, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨C₁, -, hC₁⟩ :=
    exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := H) φ (-s)
  obtain ⟨C₂, -, hC₂⟩ := exists_littlewoodPaleyBlock_eq_and_sum_norm_sq_le (H := H) φ
  refine ⟨C₁ ^ 2 * C₂, fun u w hw ↦ ?_⟩
  obtain ⟨g, hg, hgw⟩ := hC₂ w
  have hu : besselPotential E H (-s) (w : 𝓢'(E, H)) = u :=
    (besselPotential_neg_apply_eq_iff s _ _).2 hw
  choose f hf hfg using fun j ↦ hC₁ (p := 2) j w (g j) (hg j)
  refine ⟨f, fun j ↦ hu ▸ (littlewoodPaleyBlock_besselPotential_comm φ _ j _).trans (hf j),
    fun t ↦ ?_⟩
  have hfg' : ∀ j : ℕ, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ C₁ ^ 2 * ‖g j‖ ^ 2 := fun j ↦ by
    have h2 : (2 : ℝ) ^ (s * j) * 2 ^ (-s * j) = 1 := by
      rw [← Real.rpow_add two_pos, neg_mul, add_neg_cancel, Real.rpow_zero]
    calc (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ (2 ^ (s * j) * (C₁ * 2 ^ (-s * j) * ‖g j‖)) ^ 2 := by
          gcongr
          exact hfg j
      _ = C₁ ^ 2 * ‖g j‖ ^ 2 := by
          rw [show (2 : ℝ) ^ (s * j) * (C₁ * 2 ^ (-s * j) * ‖g j‖) =
            C₁ * ((2 : ℝ) ^ (s * j) * 2 ^ (-s * j)) * ‖g j‖ by ring, h2]
          ring
  calc ∑ j ∈ t, (2 ^ (s * j) * ‖f j‖) ^ 2 ≤ ∑ j ∈ t, C₁ ^ 2 * ‖g j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ hfg' j
    _ ≤ C₁ ^ 2 * C₂ * ‖w‖ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hgw t) (sq_nonneg C₁)

variable (φ) in
/-- **`B^s_{2,2} = H^{s,2}`.** A tempered distribution lies in the Besov space `B^s_{2,2}` built
from any bump function `φ` exactly when it lies in the Bessel-potential space `H^{s,2}`, that is,
when `J^s u = 𝓕⁻ ((1 + ‖ξ‖²)^{s/2} 𝓕 u)` is an `L²` function. -/
theorem memBesov_two_two_iff_memSobolev {u : 𝓢'(E, H)} :
    u.MemBesov φ s 2 2 ↔ u.MemSobolev s 2 := by
  have memℓp_two_iff_summable_sq : ∀ {a : ℕ → ℝ}, Memℓp a 2 ↔ Summable fun j ↦ a j ^ 2 := by
    intro a
    rw [memℓp_gen_iff (by simp)]
    simp
  constructor
  · intro hu
    obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
    obtain ⟨C, hC⟩ := exists_besselPotential_eq_and_norm_sq_le (H := H) φ s
    obtain ⟨w, hw, -⟩ := hC u f hf (memℓp_two_iff_summable_sq.1 hmem)
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_sum_sq_le (H := H) φ s
    obtain ⟨f, hf, hfw⟩ := hC u w hw
    exact memBesov_iff.2 ⟨f, hf, memℓp_two_iff_summable_sq.2
      (summable_of_sum_le (fun j ↦ by positivity) hfw)⟩

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable (φ s) in
/-- The `H^{s,2}` norm is bounded by a multiple of the `B^s_{2,2}` norm. -/
private theorem exists_norm_le_of_toDistr_eq :
    ∃ C : ℝ, ∀ (u : BesovSpace H φ s 2 2) (v : BesselPotentialSpace E H s 2),
      v.toDistr = u.toDistr → ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_eq_and_norm_sq_le (H := H) φ s
  refine ⟨√C, fun u v huv ↦ ?_⟩
  obtain ⟨w, hw, hwu⟩ :=
    hC u.toDistr u.block (fun j ↦ (u.coe_block j).symm) (hasSum_norm_sq u).summable
  have hv : v.toLp = w := Lp.toTemperedDistribution_injective <| by
    simp only [← v.bessel_toDistr_eq_toLp, huv, hw]
  rw [← BesselPotentialSpace.norm_toLp_eq, hv, ← Real.sqrt_sq (norm_nonneg u),
    ← Real.sqrt_mul' _ (sq_nonneg _), ← (hasSum_norm_sq u).tsum_eq]
  exact Real.le_sqrt_of_sq_le hwu

variable (φ s) in
/-- The `B^s_{2,2}` norm is bounded by a multiple of the `H^{s,2}` norm. -/
private theorem exists_norm_le_of_toDistr_eq' :
    ∃ C : ℝ, ∀ (v : BesselPotentialSpace E H s 2) (u : BesovSpace H φ s 2 2),
      u.toDistr = v.toDistr → ‖u‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_sum_sq_le (H := H) φ s
  refine ⟨√C, fun v u huv ↦ ?_⟩
  obtain ⟨f, hf, hfv⟩ := hC v.toDistr v.toLp v.bessel_toDistr_eq_toLp
  have hu : ∀ j, u.block j = f j := fun j ↦ Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, huv, hf]
  rw [← BesselPotentialSpace.norm_toLp_eq, ← Real.sqrt_sq (norm_nonneg v.toLp),
    ← Real.sqrt_mul' _ (sq_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← (hasSum_norm_sq u).tsum_eq]
  simp_rw [hu] at hfv ⊢
  exact Summable.tsum_le_of_sum_le ((hasSum_norm_sq u).summable.congr fun j ↦ by rw [hu]) hfv

variable (H φ s) in
/-- **`B^s_{2,2} = H^{s,2}` with equivalent norms.** The identity on tempered distributions is an
isomorphism of normed spaces between the Besov space `B^s_{2,2}` built from `φ` and the
Bessel-potential space `H^{s,2}`. -/
def besselPotentialSpaceEquiv : BesovSpace H φ s 2 2 ≃L[ℂ] BesselPotentialSpace E H s 2 :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun u := ((memBesov_two_two_iff_memSobolev φ).1 u.memBesov_toDistr).toBesselPotentialSpace
      invFun v := ((memBesov_two_two_iff_memSobolev φ).2 v.memSobolev_toDistr).toBesovSpace
      map_add' _ _ := BesselPotentialSpace.ext (by simp)
      map_smul' _ _ := BesselPotentialSpace.ext (by simp)
      left_inv _ := BesovSpace.ext (by simp)
      right_inv _ := BesselPotentialSpace.ext (by simp) }
    _ _ (fun u ↦ (exists_norm_le_of_toDistr_eq (H := H) φ s).choose_spec u _ (by simp))
    fun v ↦ (exists_norm_le_of_toDistr_eq' (H := H) φ s).choose_spec v _ (by simp)

@[simp]
theorem toDistr_besselPotentialSpaceEquiv (u : BesovSpace H φ s 2 2) :
    (besselPotentialSpaceEquiv H φ s u).toDistr = u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

@[simp]
theorem toDistr_besselPotentialSpaceEquiv_symm (v : BesselPotentialSpace E H s 2) :
    ((besselPotentialSpaceEquiv H φ s).symm v).toDistr = v.toDistr :=
  MemBesov.toDistr_toBesovSpace _

end TauCeti.BesovSpace
