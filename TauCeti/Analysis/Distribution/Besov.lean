/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ELpNorm
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.MeasureTheory.Function.LpSeminorm.Count

/-!
# Inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and
let `Δⱼ u = 𝓕⁻ (ψⱼ • 𝓕 u)` be the Littlewood–Paley blocks of a tempered distribution `u` built
from the inhomogeneous partition `ψ₀ = φ`, `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)`, `j ≥ 1`
(`TemperedDistribution.littlewoodPaleyBlock`). For `s ∈ ℝ` and `1 ≤ p ≤ ∞`, `0 < q ≤ ∞`, the
**inhomogeneous Besov space** `B^s_{p,q}` consists of the tempered distributions with finite
norm

`‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}`.

The block `Δⱼ u` has its frequencies at `|ξ| ≈ 2^j`, so `s` measures smoothness, `p` the
integrability of each frequency piece and `q` how the pieces are summed. This file sets up the
Besov norm as an `ℝ≥0∞`-valued function on all of `𝓢'(E, F)`, in the manner of
`MeasureTheory.eLpNorm`: the size of a block is its extended `Lᵖ` norm
`TemperedDistribution.eLpNorm`, which is `∞` when the block is not an `Lᵖ` function, and the
blocks are summed with the `ℓ^q` seminorm `MeasureTheory.eLpNorm · q count` on `ℕ`.

* `B^s_{p,q}` is a linear subspace of `𝓢'(E, F)` and the Besov norm is a seminorm on it
  (a quasi-seminorm when `q < 1`).
* The scale is decreasing in `s` and increasing in `q`, `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for
  `s' ≤ s`, `q ≤ q'`, and a loss of smoothness pays for every change of `q`:
  `B^s_{p,q} ⊆ B^s_{p,∞} ⊆ B^{s'}_{p,q'}` for `s' < s` and arbitrary `q'`, with
  `‖u‖_{B^{s'}_{p,q'}} ≤ ‖(2^{j(s' - s)})_j‖_{ℓ^{q'}} ‖u‖_{B^s_{p,∞}}`.
* Since the blocks are bounded on `Lᵖ` uniformly in `j`, every `f ∈ Lᵖ` lies in `B^s_{p,∞}`
  for `s ≤ 0`, with `‖f‖_{B^s_{p,∞}} ≤ C ‖f‖_p`, and so in `B^s_{p,q}` for every `q` when `s < 0`.
* By almost orthogonality, a block `Δⱼ u` that is an `Lᵖ` function lies in every `B^s_{p,q}`:
  only finitely many blocks of `Δⱼ u` are nonzero.

The Besov spaces depend on `φ` only up to equivalent norms; that, and their completeness, are
not proved here.

## Main declarations

* `TemperedDistribution.besovENorm`: the Besov norm `‖u‖_{B^s_{p,q}}` in `ℝ≥0∞`.
* `TemperedDistribution.MemBesov`: membership in `B^s_{p,q}`.
* `TemperedDistribution.besov`: the Besov space `B^s_{p,q}` as a submodule of `𝓢'(E, F)`.
* `TemperedDistribution.besovENorm_add_le`, `TemperedDistribution.besovENorm_smul`: the seminorm
  laws.
* `TemperedDistribution.besovENorm_le_besovENorm_of_le`,
  `TemperedDistribution.besovENorm_le_besovENorm_of_exponent_le`: monotonicity in `s` and `q`.
* `TemperedDistribution.besovENorm_le_eLpNorm_mul_besovENorm_top`,
  `TemperedDistribution.MemBesov.of_lt`: trading smoothness for summability.
* `TemperedDistribution.exists_besovENorm_toTemperedDistribution_le`: `Lᵖ ⊆ B^s_{p,∞}` for
  `s ≤ 0`.
* `TemperedDistribution.memBesov_littlewoodPaleyBlock`: an `Lᵖ` block lies in every Besov space.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren 343, Springer, 2011, Definition 2.68 and Proposition 2.71.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory Measure
open scoped ENNReal NNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E))

/-- The **Besov norm** `‖u‖_{B^s_{p,q}} = ‖(2^{js} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}` of a tempered
distribution, with values in `ℝ≥0∞`. The blocks `Δⱼ u` are the inhomogeneous Littlewood–Paley
blocks built from `φ`, their size is the extended `Lᵖ` norm `TemperedDistribution.eLpNorm`
(`∞` for a block that is not an `Lᵖ` function), and the weighted sizes are summed with the `ℓ^q`
seminorm on `ℕ`. -/
def besovENorm (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm
    (fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p) q count

/-- A tempered distribution **lies in the Besov space** `B^s_{p,q}` if each of its
Littlewood–Paley blocks is an `Lᵖ` function and its Besov norm is finite. For `q ≠ 0` the first
condition follows from the second (`TemperedDistribution.memBesov_iff`). -/
def MemBesov (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E, F)) : Prop :=
  (∀ j, (littlewoodPaleyBlock F φ j u).eLpNorm p < ∞) ∧ besovENorm φ s p q u < ∞

variable {φ} {s s' : ℝ} {p q q' : ℝ≥0∞} [Fact (1 ≤ p)] {u v : 𝓢'(E, F)}

/-- Unfolding `TemperedDistribution.besovENorm`. -/
theorem besovENorm_def (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E, F)) :
    besovENorm φ s p q u = MeasureTheory.eLpNorm
      (fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p) q count :=
  (rfl)

/-- Unfolding `TemperedDistribution.MemBesov`. -/
theorem memBesov_def :
    MemBesov φ s p q u ↔
      (∀ j, (littlewoodPaleyBlock F φ j u).eLpNorm p < ∞) ∧ besovENorm φ s p q u < ∞ :=
  Iff.rfl

/-- `B^s_{p,∞}` carries the supremum norm `sup_j 2^{js} ‖Δⱼ u‖_p`. -/
theorem besovENorm_top (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E, F)) :
    besovENorm φ s p ∞ u =
      ⨆ j : ℕ, (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p := by
  simp only [besovENorm_def, eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count,
    enorm_eq_self]

/-- Each weighted block is bounded by the Besov norm. -/
theorem pow_mul_eLpNorm_le_besovENorm (hq : q ≠ 0) (j : ℕ) :
    (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p ≤ besovENorm φ s p q u :=
  enorm_le_eLpNorm_count (fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j *
    (littlewoodPaleyBlock F φ j u).eLpNorm p) j hq

/-- For `q ≠ 0`, a tempered distribution lies in `B^s_{p,q}` exactly when its Besov norm is
finite. -/
theorem memBesov_iff (hq : q ≠ 0) : MemBesov φ s p q u ↔ besovENorm φ s p q u < ∞ := by
  refine ⟨And.right, fun hu ↦ ⟨fun j ↦ ?_, hu⟩⟩
  have hj := (pow_mul_eLpNorm_le_besovENorm hq j).trans_lt hu
  have h2 : (2 ^ s : ℝ≥0∞) ^ j ≠ 0 :=
    pow_ne_zero _ (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  exact ENNReal.lt_top_of_mul_ne_top_right hj.ne h2

theorem MemBesov.besovENorm_lt_top (hu : MemBesov φ s p q u) : besovENorm φ s p q u < ∞ :=
  hu.2

/-- Each Littlewood–Paley block of a distribution in `B^s_{p,q}` is an `Lᵖ` function. -/
theorem MemBesov.exists_littlewoodPaleyBlock_eq (hu : MemBesov φ s p q u) (j : ℕ) :
    ∃ f : Lp F p (volume : Measure E), (f : 𝓢'(E, F)) = littlewoodPaleyBlock F φ j u :=
  eLpNorm_lt_top_iff.1 (hu.1 j)

/-! ### The seminorm laws -/

section Seminorm

variable (φ s p q) in
@[simp]
theorem besovENorm_zero : besovENorm φ s p q (0 : 𝓢'(E, F)) = 0 := by
  simp [besovENorm_def]

/-- The Besov norm is absolutely homogeneous. -/
theorem besovENorm_smul (c : ℂ) (u : 𝓢'(E, F)) :
    besovENorm φ s p q (c • u) = ‖c‖ₑ * besovENorm φ s p q u := by
  simp_rw [besovENorm_def, map_smul, eLpNorm_smul, mul_left_comm _ ‖c‖ₑ]
  exact eLpNorm_const_mul_ennreal .of_discrete

@[simp]
theorem besovENorm_neg (u : 𝓢'(E, F)) : besovENorm φ s p q (-u) = besovENorm φ s p q u := by
  simp [besovENorm_def]

/-- The weighted block sizes of `u + v` are bounded by the sums of those of `u` and `v`. -/
private theorem eLpNorm_besov_add_le_add :
    MeasureTheory.eLpNorm
        (fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j (u + v)).eLpNorm p) q count ≤
      MeasureTheory.eLpNorm
        ((fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p) +
          fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j v).eLpNorm p) q count := by
  refine eLpNorm_mono_enorm .of_discrete fun j ↦ ?_
  simp only [enorm_eq_self, Pi.add_apply, map_add, ← mul_add]
  gcongr
  exact eLpNorm_add_le _ _

/-- **Triangle inequality** for the Besov norm, `1 ≤ q ≤ ∞`. -/
theorem besovENorm_add_le (hq : 1 ≤ q) :
    besovENorm φ s p q (u + v) ≤ besovENorm φ s p q u + besovENorm φ s p q v :=
  eLpNorm_besov_add_le_add.trans (MeasureTheory.eLpNorm_add_le hq)

/-- The **quasi-triangle inequality** for the Besov norm, valid for every `q`. -/
theorem besovENorm_add_le' (q : ℝ≥0∞) :
    besovENorm φ s p q (u + v) ≤
      ENNReal.LpAddConst q * (besovENorm φ s p q u + besovENorm φ s p q v) :=
  eLpNorm_besov_add_le_add.trans (MeasureTheory.eLpNorm_add_le' q)

variable (φ s p q) in
theorem MemBesov.zero : MemBesov φ s p q (0 : 𝓢'(E, F)) :=
  ⟨fun j ↦ by simp, by simp⟩

theorem MemBesov.add (hu : MemBesov φ s p q u) (hv : MemBesov φ s p q v) :
    MemBesov φ s p q (u + v) := by
  refine ⟨fun j ↦ ?_, (besovENorm_add_le' q).trans_lt ?_⟩
  · rw [map_add]
    exact (eLpNorm_add_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hu.1 j, hv.1 j⟩)
  · exact ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top q) (ENNReal.add_lt_top.2 ⟨hu.2, hv.2⟩)

theorem MemBesov.smul (c : ℂ) (hu : MemBesov φ s p q u) : MemBesov φ s p q (c • u) := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · rw [map_smul, eLpNorm_smul]
    exact ENNReal.mul_lt_top enorm_lt_top (hu.1 j)
  · rw [besovENorm_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hu.2

theorem MemBesov.neg (hu : MemBesov φ s p q u) : MemBesov φ s p q (-u) := by
  simpa using hu.smul (-1)

theorem MemBesov.sub (hu : MemBesov φ s p q u) (hv : MemBesov φ s p q v) :
    MemBesov φ s p q (u - v) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

variable (φ s p q) in
/-- The **Besov space** `B^s_{p,q}` as a submodule of `𝓢'(E, F)`. -/
def besov : Submodule ℂ 𝓢'(E, F) where
  carrier := {u | MemBesov φ s p q u}
  zero_mem' := MemBesov.zero φ s p q
  add_mem' := MemBesov.add
  smul_mem' c _ hu := hu.smul c

@[simp]
theorem mem_besov : u ∈ besov φ s p q ↔ MemBesov φ s p q u :=
  Iff.rfl

end Seminorm

/-! ### Embeddings between Besov spaces -/

section Embedding

/-- **The Besov scale decreases in the smoothness index:** `‖u‖_{B^{s'}_{p,q}} ≤ ‖u‖_{B^s_{p,q}}`
for `s' ≤ s`. -/
theorem besovENorm_le_besovENorm_of_le (hs : s' ≤ s) :
    besovENorm φ s' p q u ≤ besovENorm φ s p q u := by
  simp only [besovENorm_def]
  refine eLpNorm_mono_enorm .of_discrete fun j ↦ ?_
  simp only [enorm_eq_self]
  gcongr
  exact one_le_two

/-- **The Besov scale increases in the summability index:** `‖u‖_{B^s_{p,q'}} ≤ ‖u‖_{B^s_{p,q}}`
for `0 < q ≤ q'`. -/
theorem besovENorm_le_besovENorm_of_exponent_le (hq : q ≠ 0) (hqq' : q ≤ q') :
    besovENorm φ s p q' u ≤ besovENorm φ s p q u :=
  eLpNorm_count_le_of_exponent_le hq hqq'

/-- **Trading smoothness for summability.** For all `s', s` and every `q`,
`‖u‖_{B^{s'}_{p,q}} ≤ ‖(2^{j(s' - s)})_j‖_{ℓ^q} ‖u‖_{B^s_{p,∞}}`. The first factor is finite when
`s' < s` (`MeasureTheory.eLpNorm_count_pow_lt_top`), which gives `B^s_{p,∞} ⊆ B^{s'}_{p,q}`. -/
theorem besovENorm_le_eLpNorm_mul_besovENorm_top (s' s : ℝ) (q : ℝ≥0∞) (u : 𝓢'(E, F)) :
    besovENorm φ s' p q u ≤
      MeasureTheory.eLpNorm (fun j : ℕ ↦ (2 ^ (s' - s) : ℝ≥0∞) ^ j) q count *
        besovENorm φ s p ∞ u := by
  rw [besovENorm_top, mul_comm, besovENorm_def, ← eLpNorm_const_mul_ennreal .of_discrete]
  refine eLpNorm_mono_enorm .of_discrete fun j ↦ ?_
  simp only [enorm_eq_self]
  -- `2^{js'} = 2^{j(s' - s)} 2^{js}`, and `2^{js} ‖Δⱼ u‖_p` is at most the supremum over `j`.
  rw [← sub_add_cancel s' s, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, mul_pow,
    sub_add_cancel, mul_assoc, mul_comm]
  gcongr
  exact le_iSup (fun j : ℕ ↦ (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j u).eLpNorm p) j

/-- `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for `s' ≤ s` and `0 < q ≤ q'`. -/
theorem MemBesov.mono (hu : MemBesov φ s p q u) (hs : s' ≤ s) (hq : q ≠ 0) (hqq' : q ≤ q') :
    MemBesov φ s' p q' u :=
  ⟨hu.1, (besovENorm_le_besovENorm_of_le hs).trans_lt <|
    (besovENorm_le_besovENorm_of_exponent_le hq hqq').trans_lt hu.2⟩

/-- **A loss of smoothness pays for any change of summability:** `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for
`s' < s`, `q ≠ 0` and every `q'`. -/
theorem MemBesov.of_lt (hu : MemBesov φ s p q u) (hs : s' < s) (hq : q ≠ 0) (q' : ℝ≥0∞) :
    MemBesov φ s' p q' u := by
  refine ⟨hu.1, (besovENorm_le_eLpNorm_mul_besovENorm_top s' s q' u).trans_lt <|
    ENNReal.mul_lt_top (eLpNorm_count_pow_lt_top ?_ q') (hu.mono le_rfl hq le_top).2⟩
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg ENNReal.one_lt_two (sub_neg.2 hs)

end Embedding

/-! ### Examples: `Lᵖ` functions and single blocks -/

section Examples

variable (φ) in
/-- **`Lᵖ ⊆ B^s_{p,∞}` for `s ≤ 0`.** Since the Littlewood–Paley blocks are bounded on `Lᵖ`
uniformly in `j`, there is `C`, depending only on `φ`, with `‖f‖_{B^s_{p,∞}} ≤ C ‖f‖_p` for every
`1 ≤ p ≤ ∞`, every `s ≤ 0` and every `f ∈ Lᵖ`. -/
theorem exists_besovENorm_toTemperedDistribution_le :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : ℝ}, s ≤ 0 →
      ∀ f : Lp F p (volume : Measure E), besovENorm φ s p ∞ (f : 𝓢'(E, F)) ≤ C * ‖f‖ₑ := by
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨C.toNNReal, fun {p} _ {s} hs f ↦ ?_⟩
  rw [besovENorm_top]
  refine iSup_le fun j ↦ ?_
  obtain ⟨g, hg, hgf⟩ := hC j f
  have h2 : (2 ^ s : ℝ≥0∞) ^ j ≤ 1 :=
    pow_le_one₀ zero_le <| (ENNReal.rpow_le_rpow_of_exponent_le one_le_two hs).trans_eq
      ENNReal.rpow_zero
  calc (2 ^ s : ℝ≥0∞) ^ j * (littlewoodPaleyBlock F φ j (f : 𝓢'(E, F))).eLpNorm p
      ≤ 1 * ‖g‖ₑ := mul_le_mul' h2 (eLpNorm_le_enorm g hg.symm)
    _ ≤ C.toNNReal * ‖f‖ₑ := by
      rw [one_mul, ← ofReal_norm, ← ofReal_norm, ENNReal.ofNNReal_toNNReal,
        ← ENNReal.ofReal_mul' (norm_nonneg f)]
      exact ENNReal.ofReal_le_ofReal hgf

/-- Every `f ∈ Lᵖ` lies in `B^s_{p,∞}` for `s ≤ 0`. -/
theorem memBesov_toTemperedDistribution (hs : s ≤ 0) (f : Lp F p (volume : Measure E)) :
    MemBesov φ s p ∞ (f : 𝓢'(E, F)) := by
  obtain ⟨C, hC⟩ := exists_besovENorm_toTemperedDistribution_le (F := F) φ
  exact (memBesov_iff (by simp)).2 <|
    (hC hs f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top enorm_lt_top)

/-- Every `f ∈ Lᵖ` lies in `B^s_{p,q}` for `s < 0` and every `q`. -/
theorem memBesov_toTemperedDistribution_of_neg (hs : s < 0) (q : ℝ≥0∞)
    (f : Lp F p (volume : Measure E)) : MemBesov φ s p q (f : 𝓢'(E, F)) :=
  (memBesov_toTemperedDistribution le_rfl f).of_lt hs (by simp) q

/-- **A single Littlewood–Paley block lies in every Besov space.** If the block `Δⱼ u` is an `Lᵖ`
function, then `Δⱼ u ∈ B^s_{p,q}` for every `s` and `q`: its own blocks `Δₖ Δⱼ u` are `Lᵖ`
functions, and they vanish for `k` beyond a fixed distance of `j`, by almost orthogonality. -/
theorem memBesov_littlewoodPaleyBlock {j : ℕ} (hu : (littlewoodPaleyBlock F φ j u).eLpNorm p < ∞)
    (s : ℝ) (q : ℝ≥0∞) : MemBesov φ s p q (littlewoodPaleyBlock F φ j u) := by
  obtain ⟨f, hf⟩ := eLpNorm_lt_top_iff.1 hu
  obtain ⟨C, hC⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ
  -- The blocks of `Δⱼ u` are the blocks of the `Lᵖ` function `f`, hence `Lᵖ` functions.
  have hblock (k : ℕ) :
      (littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u)).eLpNorm p < ∞ := by
    obtain ⟨g, hg, -⟩ := hC k f
    rw [← hf, hg]
    exact (eLpNorm_le_enorm g rfl).trans_lt enorm_lt_top
  -- Only the blocks with `k < j + L` survive.
  have hzero (k : ℕ) (hk : k ∉ Finset.range (j + L)) :
      littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) = 0 := by
    rw [Finset.mem_range, not_lt] at hk
    rw [← ContinuousLinearMap.comp_apply, (hL j k hk).2, zero_apply]
  set a : ℕ → ℝ≥0∞ := fun k ↦
    (2 ^ s : ℝ≥0∞) ^ k * (littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u)).eLpNorm p
  have ha (k : ℕ) : a k < ∞ :=
    ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero
      ENNReal.ofNat_ne_top).lt_top) (hblock k)
  refine ⟨hblock, ?_⟩
  -- The weighted block sizes are bounded by a constant on a finite set and vanish off it.
  set K := ∑ k ∈ Finset.range (j + L), a k
  have hle (k : ℕ) :
      ‖a k‖ₑ ≤ ‖(Finset.range (j + L) : Set ℕ).indicator (fun _ ↦ K) k‖ₑ := by
    simp only [enorm_eq_self]
    by_cases hk : k ∈ Finset.range (j + L)
    · rw [Set.indicator_of_mem (Finset.mem_coe.2 hk)]
      exact Finset.single_le_sum (fun i _ ↦ zero_le) hk
    · simp [a, hzero k hk]
  refine (eLpNorm_mono_enorm .of_discrete hle).trans_lt <|
    (eLpNorm_indicator_const_le K q (Finset.measurableSet _).nullMeasurableSet).trans_lt ?_
  refine ENNReal.mul_lt_top (enorm_eq_self K ▸ ENNReal.sum_lt_top.2 fun k _ ↦ ha k) ?_
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

end Examples

end TemperedDistribution
