/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ENorm
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Inhomogeneous Besov spaces

Let `φ` be a smooth bump function on a finite-dimensional real inner product space `E` and let
`Δⱼ` be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). For `s : ℝ` and `1 ≤ p, q ≤ ∞` the
**inhomogeneous Besov norm** of a tempered distribution `u` is the weighted `ℓ^q` norm of the
`Lᵖ` norms of its blocks,

`‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}`,

in `ℝ≥0∞`; a block that is not an `Lᵖ` function has `Lᵖ` norm `∞`
(`TemperedDistribution.eLpNorm`). The Besov space `B^s_{p,q}` consists of the tempered
distributions of finite Besov norm (`TemperedDistribution.MemBesov`).

The Besov norm is a norm on `B^s_{p,q}` for `1 ≤ q`: it vanishes only at `0`, because every
tempered distribution is the sum of its Littlewood–Paley blocks, and it is homogeneous and
subadditive, by the triangle inequalities in `Lᵖ` and in `ℓ^q`. The scale is ordered: `B^s_{p,q}`
decreases in the smoothness `s` and increases in the summability `q`, and a strict loss of
smoothness absorbs any change of `q`,
`‖u‖_{B^{s'}_{p,q'}} ≤ ‖(2^{-(s - s') j})_j‖_{ℓ^{q'}} ‖u‖_{B^s_{p,q}}` for `s' < s`, where the
geometric constant is finite. Finally `Lᵖ ⊆ B⁰_{p,∞}` for every `1 ≤ p ≤ ∞`, since the blocks
are bounded on `Lᵖ` uniformly in `j`.

## Main declarations

* `TemperedDistribution.besovENorm`: the Besov norm `‖u‖_{B^s_{p,q}}` in `ℝ≥0∞`.
* `TemperedDistribution.MemBesov`: membership in the Besov space `B^s_{p,q}`.
* `TemperedDistribution.besovENorm_eq_zero_iff`, `TemperedDistribution.besovENorm_add_le`,
  `TemperedDistribution.besovENorm_smul`: the norm axioms.
* `TemperedDistribution.besovENorm_le_of_smoothness_le`,
  `TemperedDistribution.besovENorm_le_of_exponent_le`: monotonicity in `s` and in `q`.
* `TemperedDistribution.besovENorm_le_mul_of_smoothness_lt`: `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for
  `s' < s`, with an explicit finite constant.
* `TemperedDistribution.exists_besovENorm_le_mul_enorm`: `Lᵖ ⊆ B⁰_{p,∞}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Proposition 2.71.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
-/

public section

noncomputable section

open Filter Topology
open MeasureTheory (Lp Measure)
open scoped ENNReal NNReal SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (φ : ContDiffBump (0 : E)) {s s' : ℝ} {p q q' : ℝ≥0∞} [Fact (1 ≤ p)]

variable (s p q) in
/-- The **inhomogeneous Besov norm** `‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_j‖_{ℓ^q}` of a tempered
distribution, in `ℝ≥0∞`, for the Littlewood–Paley blocks `Δⱼ` built from `φ`. -/
def besovENorm (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm
    (fun j : ℕ ↦ 2 ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j u)) q .count

variable (s p q) in
/-- A tempered distribution lies in the **Besov space** `B^s_{p,q}` when its Besov norm is finite.
-/
def MemBesov (u : 𝓢'(E, F)) : Prop :=
  besovENorm φ s p q u < ∞

theorem memBesov_iff {u : 𝓢'(E, F)} : MemBesov φ s p q u ↔ besovENorm φ s p q u < ∞ :=
  Iff.rfl

/-- For `q = ∞` the Besov norm is the supremum `sup_j 2^{js} ‖Δⱼ u‖_p`. -/
theorem besovENorm_top (u : 𝓢'(E, F)) :
    besovENorm φ s p ∞ u = ⨆ j : ℕ, 2 ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j u) := by
  rw [besovENorm, MeasureTheory.eLpNorm_exponent_top
    (MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable),
    MeasureTheory.eLpNormEssSup_count]
  simp

/-- For `0 < q < ∞` the Besov norm is `(∑ⱼ (2^{js} ‖Δⱼ u‖_p)^q)^{1/q}`. -/
theorem besovENorm_eq_tsum (hq0 : q ≠ 0) (hq : q ≠ ∞) (u : 𝓢'(E, F)) :
    besovENorm φ s p q u = (∑' j : ℕ,
      (2 ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j u)) ^ q.toReal) ^ (1 / q.toReal) := by
  rw [besovENorm, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq
    (MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable),
    MeasureTheory.lintegral_count]
  simp

/-- Each weighted block is bounded by the Besov norm: `2^{js} ‖Δⱼ u‖_p ≤ ‖u‖_{B^s_{p,q}}`. -/
theorem rpow_mul_eLpNorm_le_besovENorm (hq : q ≠ 0) (u : 𝓢'(E, F)) (j : ℕ) :
    2 ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j u) ≤ besovENorm φ s p q u := by
  simpa [besovENorm] using MeasureTheory.enorm_le_eLpNorm_count
    (fun j : ℕ ↦ (2 : ℝ≥0∞) ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j u)) j hq

@[simp]
theorem besovENorm_zero : besovENorm φ s p q (0 : 𝓢'(E, F)) = 0 := by
  simp [besovENorm]

/-- The Besov norm vanishes only at `0`, since a tempered distribution is the sum of its
Littlewood–Paley blocks. -/
theorem besovENorm_eq_zero_iff (hq : q ≠ 0) {u : 𝓢'(E, F)} :
    besovENorm φ s p q u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ besovENorm_zero (p := p) φ⟩
  have hblock (j : ℕ) : littlewoodPaleyBlock F φ j u = 0 := by
    have := rpow_mul_eLpNorm_le_besovENorm (s := s) (p := p) φ hq u j
    rw [h, nonpos_iff_eq_zero, mul_eq_zero] at this
    simpa [ENNReal.rpow_eq_zero_iff] using this
  have := tendsto_sum_littlewoodPaleyBlock φ u
  simp only [hblock, Finset.sum_const_zero] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

/-- The **triangle inequality** for the Besov norm, for `1 ≤ q`. -/
theorem besovENorm_add_le (hq : 1 ≤ q) (u v : 𝓢'(E, F)) :
    besovENorm φ s p q (u + v) ≤ besovENorm φ s p q u + besovENorm φ s p q v := by
  unfold besovENorm
  refine (MeasureTheory.eLpNorm_mono_enorm
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable fun j ↦ ?_).trans
    (MeasureTheory.eLpNorm_add_le (g := fun j : ℕ ↦
      (2 : ℝ≥0∞) ^ (s * j) * eLpNorm p (littlewoodPaleyBlock F φ j v)) hq)
  simp only [enorm_eq_self, map_add, Pi.add_apply, ← mul_add]
  gcongr
  exact eLpNorm_add_le _ _

/-- The Besov norm is **homogeneous**. -/
theorem besovENorm_smul (c : ℂ) (u : 𝓢'(E, F)) :
    besovENorm φ s p q (c • u) = ‖c‖ₑ * besovENorm φ s p q u := by
  simp only [besovENorm, map_smul, eLpNorm_smul, mul_left_comm _ ‖c‖ₑ]
  exact MeasureTheory.eLpNorm_const_mul_ennreal
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable

@[simp]
theorem besovENorm_neg (u : 𝓢'(E, F)) : besovENorm φ s p q (-u) = besovENorm φ s p q u := by
  simpa using besovENorm_smul φ (s := s) (p := p) (q := q) (-1) u

/-- The Besov norm **decreases with the smoothness**: `‖u‖_{B^{s'}_{p,q}} ≤ ‖u‖_{B^s_{p,q}}` for
`s' ≤ s`. -/
theorem besovENorm_le_of_smoothness_le (hs : s' ≤ s) (u : 𝓢'(E, F)) :
    besovENorm φ s' p q u ≤ besovENorm φ s p q u := by
  refine MeasureTheory.eLpNorm_mono_enorm
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable fun j ↦ ?_
  simp only [enorm_eq_self]
  gcongr
  norm_num

/-- The Besov norm **decreases with the summability exponent**: `‖u‖_{B^s_{p,q'}} ≤ ‖u‖_{B^s_{p,q}}`
for `0 < q ≤ q'`. -/
theorem besovENorm_le_of_exponent_le (hq : q ≠ 0) (hqq' : q ≤ q') (u : 𝓢'(E, F)) :
    besovENorm φ s p q' u ≤ besovENorm φ s p q u :=
  MeasureTheory.eLpNorm_count_le_of_exponent_le hq hqq'

/-- **Strict loss of smoothness absorbs the summability exponent.** For `s' < s` and any `q, q'`,
`‖u‖_{B^{s'}_{p,q'}} ≤ ‖(2^{(s' - s) j})_j‖_{ℓ^{q'}} ‖u‖_{B^s_{p,q}}`; the geometric constant is
finite (`MeasureTheory.eLpNorm_pow_count_lt_top`). -/
theorem besovENorm_le_mul_of_smoothness_lt (hq : q ≠ 0) (u : 𝓢'(E, F)) :
    besovENorm φ s' p q' u ≤
      MeasureTheory.eLpNorm (fun j : ℕ ↦ ((2 : ℝ≥0∞) ^ (s' - s)) ^ j) q' .count *
        besovENorm φ s p q u := by
  rw [mul_comm, ← MeasureTheory.eLpNorm_const_mul_ennreal
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable]
  refine MeasureTheory.eLpNorm_mono_enorm
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable fun j ↦ ?_
  simp only [enorm_eq_self]
  -- Split the weight `2^{s' j} = 2^{(s' - s) j} 2^{s j}` and bound the second factor by the norm.
  have hsplit : (2 : ℝ≥0∞) ^ (s' * j) = ((2 : ℝ≥0∞) ^ (s' - s)) ^ j * 2 ^ (s * j) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ two_ne_zero
      ENNReal.ofNat_ne_top]
    ring_nf
  rw [hsplit, mul_assoc, mul_comm (besovENorm φ s p q u)]
  gcongr
  exact rpow_mul_eLpNorm_le_besovENorm φ hq u j

/-- **`Lᵖ ⊆ B⁰_{p,∞}`.** There is `C`, depending only on `φ`, such that for every `1 ≤ p ≤ ∞` the
Besov norm `‖f‖_{B⁰_{p,∞}} = sup_j ‖Δⱼ f‖_p` of `f ∈ Lᵖ` is at most `C ‖f‖_p`. -/
theorem exists_besovENorm_le_mul_enorm :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp F p (MeasureTheory.volume : Measure E)),
      besovENorm φ 0 p ∞ (f : 𝓢'(E, F)) ≤ C * ‖f‖ₑ := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨C.toNNReal, fun {p} _ f ↦ ?_⟩
  rw [besovENorm_top]
  refine iSup_le fun j ↦ ?_
  obtain ⟨g, hg, hgf⟩ := hC j f
  rw [zero_mul, ENNReal.rpow_zero, one_mul, hg, eLpNorm_toTemperedDistribution,
    ← ofReal_norm, ← ofReal_norm, ENNReal.ofNNReal_toNNReal,
    ← ENNReal.ofReal_mul' (norm_nonneg f)]
  exact ENNReal.ofReal_le_ofReal hgf

/-! ### The Besov spaces -/

@[simp]
theorem memBesov_zero : MemBesov φ s p q (0 : 𝓢'(E, F)) := by
  simp [MemBesov]

theorem MemBesov.add (hq : 1 ≤ q) {u v : 𝓢'(E, F)} (hu : MemBesov φ s p q u)
    (hv : MemBesov φ s p q v) : MemBesov φ s p q (u + v) :=
  (besovENorm_add_le φ hq u v).trans_lt (ENNReal.add_ne_top.2 ⟨hu.ne, hv.ne⟩).lt_top

theorem MemBesov.smul (c : ℂ) {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) :
    MemBesov φ s p q (c • u) := by
  rw [MemBesov, besovENorm_smul]
  exact ENNReal.mul_lt_top enorm_lt_top hu

theorem MemBesov.neg {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) : MemBesov φ s p q (-u) := by
  rwa [MemBesov, besovENorm_neg]

theorem MemBesov.sub (hq : 1 ≤ q) {u v : 𝓢'(E, F)} (hu : MemBesov φ s p q u)
    (hv : MemBesov φ s p q v) : MemBesov φ s p q (u - v) := by
  simpa [sub_eq_add_neg] using hu.add φ hq hv.neg

/-- `B^s_{p,q} ⊆ B^{s'}_{p,q}` for `s' ≤ s`. -/
theorem MemBesov.of_smoothness_le (hs : s' ≤ s) {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) :
    MemBesov φ s' p q u :=
  (besovENorm_le_of_smoothness_le φ hs u).trans_lt hu

/-- `B^s_{p,q} ⊆ B^s_{p,q'}` for `0 < q ≤ q'`. -/
theorem MemBesov.of_exponent_le (hq : q ≠ 0) (hqq' : q ≤ q') {u : 𝓢'(E, F)}
    (hu : MemBesov φ s p q u) : MemBesov φ s p q' u :=
  (besovENorm_le_of_exponent_le φ hq hqq' u).trans_lt hu

/-- `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s` and any `q ≠ 0`, `q'`. -/
theorem MemBesov.of_smoothness_lt (hs : s' < s) (hq : q ≠ 0) (q' : ℝ≥0∞) {u : 𝓢'(E, F)}
    (hu : MemBesov φ s p q u) : MemBesov φ s' p q' u := by
  refine (besovENorm_le_mul_of_smoothness_lt φ hq u).trans_lt (ENNReal.mul_lt_top ?_ hu)
  refine MeasureTheory.eLpNorm_pow_count_lt_top ?_ q'
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.2 hs)

/-- **`Lᵖ ⊆ B⁰_{p,∞}`**: every `Lᵖ` function lies in the Besov space `B⁰_{p,∞}`. -/
theorem memBesov_toTemperedDistribution (f : Lp F p (MeasureTheory.volume : Measure E)) :
    MemBesov φ 0 p ∞ (f : 𝓢'(E, F)) := by
  obtain ⟨C, hC⟩ := exists_besovENorm_le_mul_enorm (F := F) φ
  exact (hC f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top enorm_lt_top)

end TemperedDistribution
