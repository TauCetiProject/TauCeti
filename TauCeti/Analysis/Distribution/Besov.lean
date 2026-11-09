/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Inhomogeneous Besov spaces

Let `φ` be a smooth bump function on a finite-dimensional real inner product space `E`, and let
`Δⱼ = 𝓕⁻ (ψⱼ • 𝓕 ·)`, `j ≥ 0`, be the inhomogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.littlewoodPaleyBlock`). For `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`, the
**inhomogeneous Besov space** `B^s_{p,q}` consists of the tempered distributions `u` whose
blocks are `Lᵖ` functions with

`‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q} < ∞`.

The index `s` measures smoothness, `p` integrability, and `q` is a fine summability index.

To state this without first knowing that the blocks lie in `Lᵖ`, the block norms are the
extended `Lᵖ` norms `TemperedDistribution.lpENorm p (Δⱼ u)`, equal to `‖g‖_p` when `Δⱼ u` is the
tempered distribution of `g ∈ Lᵖ` and to `∞` otherwise. The Besov norm
`TemperedDistribution.besovENorm φ s p q u` is the `ℓ^q` norm, taken against the counting measure
on `ℕ`, of the weighted extended norms `2^{js} lpENorm p (Δⱼ u)`, and
`TemperedDistribution.MemBesov φ s p q u` says that it is finite.

The basic properties proved here are:

* `besovENorm φ s p q` (for `1 ≤ q`) satisfies the triangle inequality and is absolutely
  homogeneous, so `MemBesov φ s p q` is closed under the vector space operations;
* the Besov norm increases with `s` and decreases with `q`, and lowering the smoothness by any
  positive amount absorbs every change of the summability index:
  `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s` and all `q, q' ≥ 1`;
* at smoothness `0` the Besov scale brackets `Lᵖ`: `B^0_{p,1} ⊆ Lᵖ ⊆ B^0_{p,∞}`, with
  `‖u‖_p ≤ ‖u‖_{B^0_{p,1}}` and `‖u‖_{B^0_{p,∞}} ≤ C ‖u‖_p` for a constant `C` depending only on
  `φ`. The first inclusion sums the blocks in `Lᵖ` and identifies the sum with `u` through the
  Littlewood–Paley reconstruction `u = ∑ⱼ Δⱼ u` in `𝓢'`; the second is the uniform `Lᵖ`
  boundedness of the blocks. In terms of the Bessel-potential spaces, whose order-zero member is
  `Lᵖ`, this is `B^0_{p,1} ⊆ H^{0,p} ⊆ B^0_{p,∞}`.

## Main declarations

* `TemperedDistribution.besovENorm`: the Besov norm `‖u‖_{B^s_{p,q}}`.
* `TemperedDistribution.MemBesov`: membership in `B^s_{p,q}`.
* `TemperedDistribution.besovENorm_add_le`, `TemperedDistribution.besovENorm_smul`: the Besov
  norm is a seminorm.
* `TemperedDistribution.besovENorm_mono_smoothness`,
  `TemperedDistribution.besovENorm_mono_summability`, `TemperedDistribution.besovENorm_one_le`:
  the elementary embeddings between Besov spaces.
* `TemperedDistribution.lpENorm_le_besovENorm_zero_one`: `B^0_{p,1} ⊆ Lᵖ`.
* `TemperedDistribution.exists_besovENorm_zero_top_le`: `Lᵖ ⊆ B^0_{p,∞}`.
* `TemperedDistribution.MemBesov.memSobolev_zero`,
  `TemperedDistribution.MemSobolev.memBesov_zero_top`: `B^0_{p,1} ⊆ H^{0,p} ⊆ B^0_{p,∞}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Proposition 2.71.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.1 and Proposition 2.3.2/2.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
-/

public section

open Filter Topology MeasureTheory
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution


/-! ### The Besov norm -/

section Besov

variable {φ : ContDiffBump (0 : E)} {s s' : ℝ} {p q r : ℝ≥0∞} [Fact (1 ≤ p)]

variable (φ s p q) in
/-- The **inhomogeneous Besov norm** `‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}` of a
tempered distribution, built from the Littlewood–Paley blocks `Δⱼ` of the bump function `φ`.
A block that is not an `Lᵖ` function contributes `∞` (`TemperedDistribution.lpENorm`). The
summability index is meant to satisfy `1 ≤ q`; for `q = 0` the `ℓ^q` norm, and hence this norm,
vanishes identically. -/
noncomputable def besovENorm (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  eLpNorm (fun j : ℕ ↦ (2 : ℝ≥0∞) ^ (s * j) * lpENorm p (littlewoodPaleyBlock F φ j u)) q .count

theorem besovENorm_def (u : 𝓢'(E, F)) :
    besovENorm φ s p q u =
      eLpNorm (fun j : ℕ ↦ (2 : ℝ≥0∞) ^ (s * j) * lpENorm p (littlewoodPaleyBlock F φ j u)) q
        .count :=
  (rfl)

variable (φ s p q) in
/-- A tempered distribution lies in the **inhomogeneous Besov space** `B^s_{p,q}` built from the
Littlewood–Paley blocks of `φ` if its Besov norm is finite. -/
def MemBesov (u : 𝓢'(E, F)) : Prop :=
  besovENorm φ s p q u < ∞

theorem memBesov_iff {u : 𝓢'(E, F)} : MemBesov φ s p q u ↔ besovENorm φ s p q u < ∞ :=
  Iff.rfl

/-- Each weighted block norm `2^{js} ‖Δⱼ u‖_p` is at most the Besov norm. -/
theorem two_rpow_mul_lpENorm_le_besovENorm (hq : q ≠ 0) (u : 𝓢'(E, F)) (j : ℕ) :
    2 ^ (s * j) * lpENorm p (littlewoodPaleyBlock F φ j u) ≤ besovENorm φ s p q u :=
  enorm_le_eLpNorm_count
    (fun j : ℕ ↦ (2 : ℝ≥0∞) ^ (s * j) * lpENorm p (littlewoodPaleyBlock F φ j u)) j hq

/-- The Littlewood–Paley blocks of a distribution in `B^s_{p,q}` are `Lᵖ` functions. -/
theorem MemBesov.exists_littlewoodPaleyBlock_eq {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u)
    (hq : q ≠ 0) (j : ℕ) :
    ∃ g : Lp F p (volume : Measure E), littlewoodPaleyBlock F φ j u = g := by
  refine lpENorm_lt_top_iff.1 <| lt_top_iff_ne_top.2 fun h ↦ ?_
  have := (two_rpow_mul_lpENorm_le_besovENorm hq u j).trans_lt hu
  rw [h, ENNReal.mul_top (ENNReal.rpow_pos (by norm_num) ENNReal.ofNat_ne_top).ne'] at this
  exact this.ne rfl

@[simp]
theorem besovENorm_zero : besovENorm φ s p q (0 : 𝓢'(E, F)) = 0 := by
  simp [besovENorm_def]

theorem besovENorm_add_le (hq : 1 ≤ q) (u v : 𝓢'(E, F)) :
    besovENorm φ s p q (u + v) ≤ besovENorm φ s p q u + besovENorm φ s p q v := by
  simp only [besovENorm_def]
  refine (eLpNorm_mono_enorm .of_discrete fun j ↦ ?_).trans
    (eLpNorm_add_le hq)
  simp only [map_add, enorm_eq_self, Pi.add_apply, ← mul_add]
  gcongr
  exact lpENorm_add_le _ _

/-- The Besov norm is absolutely homogeneous. -/
theorem besovENorm_smul (c : ℂ) (u : 𝓢'(E, F)) :
    besovENorm φ s p q (c • u) = ‖c‖ₑ * besovENorm φ s p q u := by
  simp only [besovENorm_def, map_smul, lpENorm_smul, mul_left_comm _ ‖c‖ₑ]
  exact eLpNorm_const_mul_ennreal .of_discrete

@[simp]
theorem besovENorm_neg (u : 𝓢'(E, F)) : besovENorm φ s p q (-u) = besovENorm φ s p q u := by
  simpa using besovENorm_smul (φ := φ) (s := s) (p := p) (q := q) (-1) u

theorem memBesov_zero : MemBesov φ s p q (0 : 𝓢'(E, F)) := by
  simp [MemBesov]

theorem MemBesov.add (hq : 1 ≤ q) {u v : 𝓢'(E, F)} (hu : MemBesov φ s p q u)
    (hv : MemBesov φ s p q v) : MemBesov φ s p q (u + v) :=
  (besovENorm_add_le hq u v).trans_lt (ENNReal.add_lt_top.2 ⟨hu, hv⟩)

theorem MemBesov.smul (c : ℂ) {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) :
    MemBesov φ s p q (c • u) := by
  rw [MemBesov, besovENorm_smul]
  exact ENNReal.mul_lt_top enorm_lt_top hu

theorem MemBesov.neg {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) : MemBesov φ s p q (-u) := by
  rwa [MemBesov, besovENorm_neg]

theorem MemBesov.sub (hq : 1 ≤ q) {u v : 𝓢'(E, F)} (hu : MemBesov φ s p q u)
    (hv : MemBesov φ s p q v) : MemBesov φ s p q (u - v) := by
  simpa [sub_eq_add_neg] using hu.add hq hv.neg

/-! ### Embeddings between Besov spaces -/

/-- **The Besov norm increases with the smoothness index**: `B^s_{p,q} ⊆ B^{s'}_{p,q}` for
`s' ≤ s`. -/
theorem besovENorm_mono_smoothness (hs : s' ≤ s) (u : 𝓢'(E, F)) :
    besovENorm φ s' p q u ≤ besovENorm φ s p q u := by
  simp only [besovENorm_def]
  refine eLpNorm_mono_enorm .of_discrete fun j ↦ ?_
  simp only [enorm_eq_self]
  gcongr
  exact one_le_two

/-- **The Besov norm decreases with the summability index**: `B^s_{p,q} ⊆ B^s_{p,r}` for
`0 < q ≤ r`. -/
theorem besovENorm_mono_summability (hq : q ≠ 0) (hqr : q ≤ r) (u : 𝓢'(E, F)) :
    besovENorm φ s p r u ≤ besovENorm φ s p q u :=
  eLpNorm_count_le_of_exponent_le hq hqr

theorem MemBesov.mono_smoothness (hs : s' ≤ s) {u : 𝓢'(E, F)} (hu : MemBesov φ s p q u) :
    MemBesov φ s' p q u :=
  (besovENorm_mono_smoothness hs u).trans_lt hu

theorem MemBesov.mono_summability (hq : q ≠ 0) (hqr : q ≤ r) {u : 𝓢'(E, F)}
    (hu : MemBesov φ s p q u) : MemBesov φ s p r u :=
  (besovENorm_mono_summability hq hqr u).trans_lt hu

/-- **Lowering the smoothness absorbs the summability index.** The geometric decay of
`2^{-j(s - s')}` gives `‖u‖_{B^{s'}_{p,1}} ≤ (1 - 2^{-(s - s')})⁻¹ ‖u‖_{B^s_{p,∞}}`. The constant
is finite exactly when `s' < s`. -/
theorem besovENorm_one_le (s' s : ℝ) (u : 𝓢'(E, F)) :
    besovENorm φ s' p 1 u ≤ (1 - 2 ^ (s' - s))⁻¹ * besovENorm φ s p ∞ u := by
  set M := besovENorm φ s p ∞ u
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  rw [besovENorm_def, eLpNorm_one_eq_lintegral_enorm .of_discrete, lintegral_count,
    ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_right]
  refine tsum_le_tsum fun j ↦ ?_
  -- `2^{js'} = 2^{-j(s - s')} 2^{js}`, and `2^{js} ‖Δⱼ u‖_p ≤ M`.
  have hj : (2 : ℝ≥0∞) ^ (s' * j) = (2 ^ (s' - s)) ^ j * 2 ^ (s * j) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ h2 h2']
    ring_nf
  rw [enorm_eq_self, hj, mul_assoc]
  gcongr
  exact two_rpow_mul_lpENorm_le_besovENorm ENNReal.top_ne_zero u j

/-- **`B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' < s`**, for all summability indices `q ≠ 0` and
`q' ≥ 1`. -/
theorem MemBesov.of_lt (hs : s' < s) (hq : q ≠ 0) {q' : ℝ≥0∞} (hq' : 1 ≤ q') {u : 𝓢'(E, F)}
    (hu : MemBesov φ s p q u) : MemBesov φ s' p q' u := by
  refine ((besovENorm_mono_summability one_ne_zero hq' u).trans
    (besovENorm_one_le s' s u)).trans_lt (ENNReal.mul_lt_top ?_ <|
      (besovENorm_mono_summability hq le_top u).trans_lt hu)
  refine ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 ?_)
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.2 hs)

/-! ### Besov spaces of smoothness zero and `Lᵖ` -/

/-- **`B^0_{p,1} ⊆ Lᵖ`.** The `Lᵖ` norm of a tempered distribution is at most its
`B^0_{p,1}` norm `∑ⱼ ‖Δⱼ u‖_p`: when the latter is finite, the blocks are summable in `Lᵖ`, and
their sum is `u` by the Littlewood–Paley reconstruction `u = ∑ⱼ Δⱼ u` in `𝓢'`. -/
theorem lpENorm_le_besovENorm_zero_one (u : 𝓢'(E, F)) :
    lpENorm p u ≤ besovENorm φ 0 p 1 u := by
  rcases eq_top_or_lt_top (besovENorm φ 0 p 1 u) with hu | hu
  · simp [hu]
  have hb : besovENorm φ 0 p 1 u = ∑' j, lpENorm p (littlewoodPaleyBlock F φ j u) := by
    rw [besovENorm_def, eLpNorm_one_eq_lintegral_enorm .of_discrete, lintegral_count]
    simp
  choose g hg using (show MemBesov φ 0 p 1 u from hu).exists_littlewoodPaleyBlock_eq one_ne_zero
  simp_rw [hg, lpENorm_toTemperedDistribution] at hb
  -- The blocks are absolutely summable in `Lᵖ`.
  have hsum : Summable g := by
    refine Summable.of_norm ?_
    exact ENNReal.summable_toReal (hb ▸ hu.ne) |>.congr fun j ↦ toReal_enorm _
  -- Their sum represents `u`, by uniqueness of limits in `𝓢'`.
  have hu_eq : u = (∑' j, g j : Lp F p (volume : Measure E)) := by
    refine tendsto_nhds_unique (tendsto_sum_littlewoodPaleyBlock φ u) ?_
    simp_rw [hg, ← Lp.toTemperedDistributionCLM_apply, ← map_sum]
    exact ((Lp.toTemperedDistributionCLM F volume p).continuous.tendsto _).comp
      hsum.hasSum.tendsto_sum_nat
  rw [hb, hu_eq, lpENorm_toTemperedDistribution]
  exact enorm_tsum_le_tsum_enorm

/-- A distribution in `B^0_{p,1}` is an `Lᵖ` function. -/
theorem MemBesov.exists_eq_toTemperedDistribution {u : 𝓢'(E, F)} (hu : MemBesov φ 0 p 1 u) :
    ∃ g : Lp F p (volume : Measure E), u = g :=
  lpENorm_lt_top_iff.1 ((lpENorm_le_besovENorm_zero_one u).trans_lt hu)

/-- A distribution in `B^0_{p,1}` lies in the Bessel-potential space `H^{0,p} = Lᵖ`. -/
theorem MemBesov.memSobolev_zero {u : 𝓢'(E, F)} (hu : MemBesov φ 0 p 1 u) : MemSobolev 0 p u :=
  memSobolev_zero_iff.2 hu.exists_eq_toTemperedDistribution

variable (φ) in
/-- **`Lᵖ ⊆ B^0_{p,∞}`.** There is a constant `C`, depending only on `φ`, such that
`‖u‖_{B^0_{p,∞}} = supⱼ ‖Δⱼ u‖_p ≤ C ‖u‖_p` for every `1 ≤ p ≤ ∞` and every tempered
distribution `u`: the Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j`. -/
theorem exists_besovENorm_zero_top_le :
    ∃ C : NNReal, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢'(E, F)),
      besovENorm φ 0 p ∞ u ≤ C * lpENorm p u := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  -- The constant is taken `≥ 1`, so that it does not vanish against `lpENorm p u = ∞`.
  refine ⟨(max C 1).toNNReal, fun {p} _ u ↦ ?_⟩
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  rcases eq_top_or_lt_top (lpENorm p u) with hu | hu
  · rw [hu, ENNReal.mul_top (by simp)]
    exact le_top
  obtain ⟨f, rfl⟩ := lpENorm_lt_top_iff.1 hu
  rw [besovENorm_def, eLpNorm_exponent_top .of_discrete, lpENorm_toTemperedDistribution]
  refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun j ↦ ?_)
  obtain ⟨g, hg, hgf⟩ := hC j f
  simp only [zero_mul, ENNReal.rpow_zero, one_mul, enorm_eq_self, hg,
    lpENorm_toTemperedDistribution]
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    Real.coe_toNNReal _ (zero_le_one.trans hC1), ← ENNReal.ofReal_mul (zero_le_one.trans hC1)]
  exact ENNReal.ofReal_le_ofReal (hgf.trans (by gcongr; exact le_max_left _ _))

/-- A distribution in the Bessel-potential space `H^{0,p} = Lᵖ` lies in `B^0_{p,∞}`. -/
theorem MemSobolev.memBesov_zero_top {u : 𝓢'(E, F)} (hu : MemSobolev 0 p u) :
    MemBesov φ 0 p ∞ u := by
  obtain ⟨C, hC⟩ := exists_besovENorm_zero_top_le (F := F) φ
  obtain ⟨g, rfl⟩ := memSobolev_zero_iff.1 hu
  refine (hC _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
  rw [lpENorm_toTemperedDistribution]
  exact enorm_lt_top

end Besov

end TemperedDistribution
