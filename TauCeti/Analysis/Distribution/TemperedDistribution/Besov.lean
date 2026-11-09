/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.BesselPotential

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
`J^s u = g ∈ Lᵖ`, then `Δⱼ u = J^{-s} Δⱼ g`, so `2^{js} ‖Δⱼ u‖_p ≤ C ‖g‖_p`
(`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_two_rpow_mul_norm_le`). Conversely, if
`Σⱼ 2^{js} ‖Δⱼ u‖_p < ∞`, then `J^s u ∈ Lᵖ`
(`TemperedDistribution.exists_besselPotential_eq_and_norm_le_tsum`). In particular Schwartz
functions lie in every Besov space with `q ≠ 0`; for `q = 0` membership requires all but finitely
many blocks to vanish.

The spaces decrease in `s` and increase in `q`, and lowering the smoothness by any positive
amount absorbs every change of `q` to a nonzero target: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s`
and `q' ≠ 0`. Since `Δⱼ u` is band-limited to the ball of radius `2^j φ.rOut`, Bernstein's
inequality `‖Δⱼ u‖_r ≤ C 2^{jn(1/p - 1/r)} ‖Δⱼ u‖_p` gives the embedding
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
* `TemperedDistribution.MemSobolev.memBesov`: `H^{s,p} ⊆ B^s_{p,∞}`.
* `TemperedDistribution.MemBesov.memSobolev`: `B^s_{p,1} ⊆ H^{s,p}`.
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
  have : g = g' := funext fun j ↦ LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
    ((hg j).symm.trans (hg' j))
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
  have hρ : ‖(2 : ℝ) ^ (s' - s)‖ < 1 := by rwa [Real.norm_of_nonneg (by positivity)]
  refine ⟨g, hg, ((TauCeti.memℓp_geometric_of_norm_lt_one hρ hq').const_mul M).mono fun j ↦ ?_⟩
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
