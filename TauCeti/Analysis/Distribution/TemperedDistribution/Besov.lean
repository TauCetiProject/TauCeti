/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution

/-!
# Inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space `E` of
dimension `n`, and let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). For `s ∈ ℝ`, `1 ≤ p ≤ ∞` and `q ∈ [0, ∞]`, a
tempered distribution `u` lies in the **inhomogeneous Besov space** `B^s_{p,q}` when every block
`Δⱼ u` is an `Lᵖ` function and

`(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0} ∈ ℓ^q`

(`TemperedDistribution.MemBesov`). The `ℓ^q` norm of this sequence is the Besov norm; the
parameter `s` measures smoothness, `p` integrability and `q` is a fine index. The Bessel-potential
spaces `H^{s,p}` of Mathlib (`TemperedDistribution.MemSobolev`) sit between two Besov spaces:

`B^s_{p,1} ⊆ H^{s,p} ⊆ B^s_{p,∞}`, `1 ≤ p ≤ ∞`.

Both inclusions come from the kernel bound `‖J^t Δⱼ‖_{Lᵖ → Lᵖ} ≤ C 2^{jt}` for the Bessel potential
`J^t` on a block (`TemperedDistribution.exists_besselPotential_compL_littlewoodPaleyBlock_eq`). If
`J^s u = g ∈ Lᵖ`, then `Δⱼ u = J^{-s} Δⱼ g`, so `2^{js} ‖Δⱼ u‖_p ≤ C ‖g‖_p`. Conversely, if
`Σⱼ 2^{js} ‖Δⱼ u‖_p < ∞`, then the series `Σⱼ J^s Δⱼ u` converges absolutely in `Lᵖ`, and in `𝓢'`
it sums to `J^s u` because `u = Σⱼ Δⱼ u` there. In particular Schwartz functions lie in every
Besov space.

The spaces decrease in `s` and increase in `q`, and lowering the smoothness by any positive
amount absorbs every change of `q`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s`. Since `Δⱼ u` is
band-limited to the ball of radius `2^j φ.rOut`, Bernstein's inequality
`‖Δⱼ u‖_r ≤ C 2^{jn(1/p - 1/r)} ‖Δⱼ u‖_p` gives the embedding
`B^s_{p,q} ⊆ B^{s - n(1/p - 1/r)}_{r,q}` for `p ≤ r`.

## Main declarations

* `TemperedDistribution.MemBesov`: membership in the inhomogeneous Besov space `B^s_{p,q}`.
* `TemperedDistribution.memBesov_iff`: the defining property.
* `TemperedDistribution.MemBesov.memℓp`: the weighted block norms of a Besov distribution lie in
  `ℓ^q`.
* `TemperedDistribution.MemBesov.add`, `TemperedDistribution.MemBesov.smul`: `B^s_{p,q}` is a
  linear subspace of `𝓢'(E, F)`.
* `TemperedDistribution.MemBesov.mono`, `TemperedDistribution.MemBesov.of_le_summability`,
  `TemperedDistribution.MemBesov.of_lt`: monotonicity in `s` and `q`.
* `TemperedDistribution.MemBesov.of_le_integrability`: the Bernstein embedding
  `B^s_{p,q} ⊆ B^{s - n(1/p - 1/r)}_{r,q}`.
* `TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le`,
  `TemperedDistribution.MemSobolev.memBesov`: `H^{s,p} ⊆ B^s_{p,∞}`, with the block bound.
* `TemperedDistribution.exists_besselPotential_eq_and_norm_le_tsum`,
  `TemperedDistribution.MemBesov.memSobolev`: `B^s_{p,1} ⊆ H^{s,p}`, with the norm bound.
* `SchwartzMap.memBesov`: Schwartz functions lie in every Besov space with `q ≠ 0`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Propositions 2.71 and 2.79.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2 and
  Theorem 6.2.4.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal FourierTransform SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

/-- A tempered distribution `u` lies in the **inhomogeneous Besov space** `B^s_{p,q}`, built from
the Littlewood–Paley blocks `Δⱼ` of `φ`, if every block `Δⱼ u` is an `Lᵖ` function `gⱼ` and the
sequence `(2^{js} ‖gⱼ‖_p)ⱼ` lies in `ℓ^q`. The `ℓ^q` norm of that sequence is the Besov norm
of `u`. -/
def MemBesov (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E, F)) :
    Prop :=
  ∃ g : ℕ → Lp F p (volume : Measure E), (∀ j, littlewoodPaleyBlock F φ j u = g j) ∧
    Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖) q

variable {φ : ContDiffBump (0 : E)} {s s' : ℝ} {p q q' r : ℝ≥0∞} [Fact (1 ≤ p)] {u v : 𝓢'(E, F)}

/-- Unfolding `TemperedDistribution.MemBesov`. -/
theorem memBesov_iff : MemBesov φ s p q u ↔
    ∃ g : ℕ → Lp F p (volume : Measure E), (∀ j, littlewoodPaleyBlock F φ j u = g j) ∧
      Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖) q :=
  Iff.rfl

/-- **Elimination for `MemBesov`.** If `u ∈ B^s_{p,q}`, then for *any* choice of `Lᵖ` functions
`gⱼ` representing the blocks `Δⱼ u`, the sequence `(2^{js} ‖gⱼ‖_p)ⱼ` lies in `ℓ^q`. -/
theorem MemBesov.memℓp (hu : MemBesov φ s p q u) {g : ℕ → Lp F p (volume : Measure E)}
    (hg : ∀ j, littlewoodPaleyBlock F φ j u = g j) :
    Memℓp (fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖) q := by
  obtain ⟨g', hg', hm⟩ := hu
  have : g = g' := funext fun j ↦ Lp.toTemperedDistribution_injective ((hg j).symm.trans (hg' j))
  rwa [this]

/-- The zero distribution lies in every Besov space. -/
@[simp]
theorem memBesov_zero : MemBesov φ s p q (0 : 𝓢'(E, F)) :=
  ⟨0, fun j ↦ by
    simpa using (map_zero (Lp.toTemperedDistributionCLM F (volume : Measure E) p)).symm, by
    simpa using (zero_mem_ℓp' : Memℓp (fun _ : ℕ ↦ (0 : ℝ)) q)⟩

/-- Besov spaces are closed under addition. -/
theorem MemBesov.add (hu : MemBesov φ s p q u) (hv : MemBesov φ s p q v) :
    MemBesov φ s p q (u + v) := by
  obtain ⟨g, hg, hgm⟩ := hu
  obtain ⟨h, hh, hhm⟩ := hv
  refine ⟨g + h, fun j ↦ ?_, (hgm.add hhm).mono fun j ↦ ?_⟩
  · simpa [hg, hh] using (map_add (Lp.toTemperedDistributionCLM F volume p) (g j) (h j)).symm
  · dsimp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity), ← mul_add]
    gcongr
    exact norm_add_le _ _

/-- Besov spaces are closed under scalar multiplication. -/
theorem MemBesov.smul (c : ℂ) (hu : MemBesov φ s p q u) : MemBesov φ s p q (c • u) := by
  obtain ⟨g, hg, hgm⟩ := hu
  refine ⟨c • g, fun j ↦ ?_, (hgm.const_mul ‖c‖).mono fun j ↦ ?_⟩
  · have h := map_smul (Lp.toTemperedDistributionCLM F (volume : Measure E) p) c (g j)
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply] at h
    rw [map_smul, hg, Pi.smul_apply, h]
  · dsimp only [Pi.smul_apply]
    rw [Real.norm_of_nonneg (by positivity), norm_smul]
    exact le_of_eq (by ring)

/-- Besov spaces are closed under negation. -/
theorem MemBesov.neg (hu : MemBesov φ s p q u) : MemBesov φ s p q (-u) := by
  simpa using hu.smul (-1)

/-- Besov spaces are closed under subtraction. -/
theorem MemBesov.sub (hu : MemBesov φ s p q u) (hv : MemBesov φ s p q v) :
    MemBesov φ s p q (u - v) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- `B^s_{p,q} ⊆ B^{s'}_{p,q}` for `s' ≤ s`: the Besov spaces decrease in the smoothness index. -/
theorem MemBesov.mono (hu : MemBesov φ s p q u) (hs : s' ≤ s) : MemBesov φ s' p q u := by
  obtain ⟨g, hg, hgm⟩ := hu
  refine ⟨g, hg, hgm.mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  exact one_le_two

/-- `B^s_{p,q} ⊆ B^s_{p,q'}` for `q ≤ q'`: the Besov spaces increase in the summability
index. -/
theorem MemBesov.of_le_summability (hu : MemBesov φ s p q u) (hq : q ≤ q') :
    MemBesov φ s p q' u := by
  obtain ⟨g, hg, hgm⟩ := hu
  exact ⟨g, hg, hgm.of_exponent_ge hq⟩

/-- `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s` and every `q' ≠ 0`: lowering the smoothness index by
any positive amount absorbs every change of the summability index. -/
theorem MemBesov.of_lt (hu : MemBesov φ s p q u) (hs : s' < s) (hq' : q' ≠ 0) :
    MemBesov φ s' p q' u := by
  obtain ⟨g, hg, hgm⟩ := hu
  obtain ⟨M, hM⟩ := (hgm.of_exponent_ge le_top).bddAbove
  have hρ₁ : (2 : ℝ) ^ (s' - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (sub_neg.2 hs)
  refine ⟨g, hg, ((memℓp_geometric_of_lt_one (by positivity) hρ₁ hq').const_mul M).mono fun j ↦ ?_⟩
  have hMj : (2 : ℝ) ^ (j * s) * ‖g j‖ ≤ M := by
    simpa [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (j * s) * ‖g j‖)] using
      hM ⟨j, rfl⟩
  have hsplit : (2 : ℝ) ^ (j * s') = ((2 : ℝ) ^ (s' - s)) ^ j * (2 : ℝ) ^ (j * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add zero_lt_two]
    ring_nf
  rw [Real.norm_of_nonneg (by positivity), hsplit, mul_assoc, mul_comm M]
  gcongr

/-- **The Bernstein embedding** `B^s_{p,q} ⊆ B^{s - n(1/p - 1/r)}_{r,q}` for `p ≤ r`, where `n`
is the dimension of `E`: trading integrability for smoothness, every block of `u` is an `Lʳ`
function and the weighted `Lʳ` norms of the blocks lie in `ℓ^q`. -/
theorem MemBesov.of_le_integrability [Fact (1 ≤ r)] (hu : MemBesov φ s p q u) (hpr : p ≤ r) :
    MemBesov φ (s - finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q u := by
  obtain ⟨g, hg, hgm⟩ := hu
  obtain ⟨C, hC, hB⟩ :=
    TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
      hpr
  set d : ℝ := finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)
  have hR (j : ℕ) : 0 < (2 : ℝ) ^ j * φ.rOut := by have := φ.rOut_pos; positivity
  choose h hh hhn using fun j ↦ hB 0 Fin.elim0 (hR j) (g j)
    (by rw [← hg j]; exact isVanishingOn_fourier_littlewoodPaleyBlock φ j u)
  refine ⟨h, fun j ↦ ?_, (hgm.const_mul (C * φ.rOut ^ d)).mono fun j ↦ ?_⟩
  · rw [hg j, ← hh j, LineDeriv.iteratedLineDerivOp_fin_zero]
  · have hhj := hhn j
    simp only [CharP.cast_eq_zero, zero_add, pow_one, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one] at hhj
    have hsplit : (2 : ℝ) ^ (j * (s - d)) * ((2 : ℝ) ^ j * φ.rOut) ^ d =
        φ.rOut ^ d * (2 : ℝ) ^ (j * s) := by
      rw [Real.mul_rpow (by positivity) φ.rOut_pos.le, ← Real.rpow_natCast_mul zero_le_two,
        ← mul_assoc, ← Real.rpow_add zero_lt_two, ← mul_add, sub_add_cancel, mul_comm]
    rw [Real.norm_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ (j * (s - d)) * ‖h j‖
        ≤ (2 : ℝ) ^ (j * (s - d)) * (C * ((2 : ℝ) ^ j * φ.rOut) ^ d * ‖g j‖) := by gcongr
      _ = C * ((2 : ℝ) ^ (j * (s - d)) * ((2 : ℝ) ^ j * φ.rOut) ^ d) * ‖g j‖ := by ring
      _ = C * φ.rOut ^ d * ((2 : ℝ) ^ (j * s) * ‖g j‖) := by
        rw [hsplit]
        ring

section Sobolev

/-- **`H^{s,p} ⊆ B^s_{p,∞}`, quantitatively.** There is `C`, depending only on `φ` and `s`, such
that for every `1 ≤ p ≤ ∞`, if the Bessel potential `J^s u` is an `Lᵖ` function `g`, then every
block `Δⱼ u` is an `Lᵖ` function `h` with `2^{js} ‖h‖_p ≤ C ‖g‖_p`. -/
theorem exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le (φ : ContDiffBump (0 : E))
    (s : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) {u : 𝓢'(E, F)}
      (g : Lp F p (volume : Measure E)), besselPotential E F s u = g →
      ∃ h : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j u = h ∧
        (2 : ℝ) ^ (j * s) * ‖h‖ ≤ C * ‖g‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨C₁, hC₁⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ (-s)
  refine ⟨C₁ * C₀, fun {p} _ j u g hg ↦ ?_⟩
  obtain ⟨σ, hσ, hσn⟩ := hC₁ j
  obtain ⟨g', hg', hg'n⟩ := hC₀ j g
  obtain ⟨h, hh, hhn⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ g'
  refine ⟨h, ?_, ?_⟩
  · -- `Δⱼ u = Δⱼ J^{-s} g = J^{-s} Δⱼ g = T_σ Δⱼ g`.
    have hu : u = besselPotential E F (-s) g := by
      rw [← hg, besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
        ContinuousLinearMap.id_apply]
    rw [hu, littlewoodPaleyBlock_besselPotential_comm, ← ContinuousLinearMap.comp_apply, hσ,
      ContinuousLinearMap.comp_apply, hg', hh]
  · have hK : (2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ ≤ C₁ := by
      calc (2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖
          ≤ (2 : ℝ) ^ (j * s) * (C₁ * ((2 : ℝ) ^ j) ^ (-s)) := by gcongr
        _ = C₁ := by
          rw [← Real.rpow_natCast_mul zero_le_two, mul_left_comm, ← Real.rpow_add zero_lt_two,
            mul_neg, add_neg_cancel,
            Real.rpow_zero, mul_one]
    have hg'0 : 0 ≤ C₀ * ‖g‖ := (norm_nonneg _).trans hg'n
    calc (2 : ℝ) ^ (j * s) * ‖h‖
        ≤ (2 : ℝ) ^ (j * s) * ((∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * (C₀ * ‖g‖)) := by
          gcongr
          exact hhn.trans (mul_le_mul_of_nonneg_left hg'n (integral_nonneg fun _ ↦ norm_nonneg _))
      _ = ((2 : ℝ) ^ (j * s) * ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * (C₀ * ‖g‖) := by ring
      _ ≤ C₁ * (C₀ * ‖g‖) := by gcongr
      _ = C₁ * C₀ * ‖g‖ := by ring

/-- **`H^{s,p} ⊆ B^s_{p,∞}`.** A tempered distribution in the Bessel-potential space `H^{s,p}`
lies in the Besov space `B^s_{p,∞}`. -/
theorem MemSobolev.memBesov (φ : ContDiffBump (0 : E)) (hu : MemSobolev s p u) :
    MemBesov φ s p ∞ u := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le (F := F) φ s
  choose h hh hhn using fun j ↦ hC j g hg
  refine ⟨h, hh, memℓp_infty ⟨C * ‖g‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hhn j

/-- **`B^s_{p,1} ⊆ H^{s,p}`, quantitatively.** There is `C`, depending only on `φ` and `s`, such
that for every `1 ≤ p ≤ ∞`, if the blocks `Δⱼ u` are `Lᵖ` functions `gⱼ` with
`Σⱼ 2^{js} ‖gⱼ‖_p < ∞`, then the Bessel potential `J^s u` is an `Lᵖ` function `h` with
`‖h‖_p ≤ C Σⱼ 2^{js} ‖gⱼ‖_p`. -/
theorem exists_besselPotential_eq_and_norm_le_tsum (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (g : ℕ → Lp F p (volume : Measure E)), (∀ j, littlewoodPaleyBlock F φ j u = g j) →
      Summable (fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖) →
      ∃ h : Lp F p (volume : Measure E), besselPotential E F s u = h ∧
        ‖h‖ ≤ C * ∑' j : ℕ, (2 : ℝ) ^ (j * s) * ‖g j‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_compL_littlewoodPaleyBlock_eq (F := F) φ s
  refine ⟨C, fun {p} _ u g hg hsum ↦ ?_⟩
  choose σ hσ hσn using hC
  -- The pieces `J^s Δⱼ u = T_{σⱼ} gⱼ` are `Lᵖ` functions with `‖J^s Δⱼ u‖_p ≤ C 2^{js} ‖gⱼ‖_p`.
  choose k hk hkn using fun j ↦ exists_fourierMultiplierCLM_eq_and_norm_le (σ j) (g j)
  have hkJ (j : ℕ) : besselPotential E F s (littlewoodPaleyBlock F φ j u) = k j := by
    rw [← ContinuousLinearMap.comp_apply, hσ, ContinuousLinearMap.comp_apply, hg, hk]
  have hkn' (j : ℕ) : ‖k j‖ ≤ C * ((2 : ℝ) ^ (j * s) * ‖g j‖) := by
    calc ‖k j‖ ≤ (∫ x, ‖𝓕⁻ (σ j : E → ℂ) x‖) * ‖g j‖ := hkn j
      _ ≤ C * ((2 : ℝ) ^ j) ^ s * ‖g j‖ := by gcongr; exact hσn j
      _ = C * ((2 : ℝ) ^ (j * s) * ‖g j‖) := by rw [← Real.rpow_natCast_mul zero_le_two, mul_assoc]
  -- The series `Σⱼ J^s Δⱼ u` converges absolutely in `Lᵖ`.
  have hksum : Summable fun j ↦ ‖k j‖ :=
    (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hkn'
  have hH := hksum.of_norm.hasSum
  refine ⟨∑' j, k j, ?_, ?_⟩
  · -- In `𝓢'` the same series sums to `J^s u`, since `u = Σⱼ Δⱼ u` there.
    have h₁ : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (k j : 𝓢'(E, F))) atTop
        (𝓝 ((∑' j, k j : Lp F p (volume : Measure E)) : 𝓢'(E, F))) := by
      have := ((Lp.toTemperedDistributionCLM F volume p).hasSum hH).tendsto_sum_nat
      simpa only [Lp.toTemperedDistributionCLM_apply] using this
    have h₂ : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (k j : 𝓢'(E, F))) atTop
        (𝓝 (besselPotential E F s u)) := by
      simp_rw [← hkJ, ← map_sum]
      exact ((besselPotential E F s).continuous.tendsto u).comp
        (tendsto_sum_littlewoodPaleyBlock φ u)
    exact tendsto_nhds_unique h₂ h₁
  · calc ‖∑' j, k j‖ ≤ ∑' j : ℕ, ‖k j‖ := norm_tsum_le_tsum_norm hksum
      _ ≤ ∑' j : ℕ, C * ((2 : ℝ) ^ (j * s) * ‖g j‖) :=
        hksum.tsum_le_tsum hkn' (hsum.mul_left C)
      _ = C * ∑' j : ℕ, (2 : ℝ) ^ (j * s) * ‖g j‖ := tsum_mul_left

/-- **`B^s_{p,1} ⊆ H^{s,p}`.** A tempered distribution in the Besov space `B^s_{p,1}` lies in the
Bessel-potential space `H^{s,p}`. -/
theorem MemBesov.memSobolev (hu : MemBesov φ s p 1 u) : MemSobolev s p u := by
  obtain ⟨g, hg, hgm⟩ := hu
  obtain ⟨C, hC⟩ := exists_besselPotential_eq_and_norm_le_tsum (F := F) φ s
  have hsum : Summable fun j : ℕ ↦ (2 : ℝ) ^ (j * s) * ‖g j‖ := by
    have := hgm.summable (by simp)
    simp only [ENNReal.toReal_one, Real.rpow_one] at this
    exact this.congr fun j ↦ Real.norm_of_nonneg (by positivity)
  obtain ⟨h, hh, -⟩ := hC g hg hsum
  exact ⟨h, hh⟩

end Sobolev

end TemperedDistribution

/-- **Schwartz functions lie in every Besov space** `B^s_{p,q}` with `q ≠ 0`. -/
theorem SchwartzMap.memBesov (φ : ContDiffBump (0 : E)) {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (hq : q ≠ 0) (f : 𝓢(E, F)) : TemperedDistribution.MemBesov φ s p q (f : 𝓢'(E, F)) :=
  (f.memSobolev.memBesov φ).of_lt (lt_add_one s) hq
