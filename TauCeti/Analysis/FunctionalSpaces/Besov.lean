/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Inhomogeneous Besov spaces

Let `φ` be a smooth bump function on a finite-dimensional real inner product space `E`, and let
`Δⱼ`, `j ≥ 0`, be the Littlewood–Paley blocks of the inhomogeneous partition built from `φ`
(`TemperedDistribution.littlewoodPaleyBlock`). For `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`, the **Besov norm**
of a tempered distribution `u` is the extended real number

`‖u‖_{B^s_{p,q}} = ‖(2^{s j} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}`,

where `‖Δⱼ u‖_p` is the extended `Lᵖ` norm of a tempered distribution
(`TemperedDistribution.eLpNorm`, infinite unless `Δⱼ u ∈ Lᵖ`). The **inhomogeneous Besov space**
`B^s_{p,q}(E; F)` is the subspace of the tempered distributions of finite Besov norm.

The Besov norm is an extended norm on `𝓢'(E, F)` for `q ≥ 1`: it vanishes only at `0`, since
`u = ∑ⱼ Δⱼ u`, it is subadditive and it is homogeneous. It decreases when the smoothness index
`s` decreases, so `B^s_{p,q} ⊆ B^{s'}_{p,q}` for `s' ≤ s`. Each weighted block norm
`2^{s j} ‖Δⱼ u‖_p` is at most `‖u‖_{B^s_{p,q}}`, so the blocks of a distribution in `B^s_{p,q}` are
`Lᵖ` functions.

The space does not depend on the choice of the bump function, and the norms built from two bump
functions are equivalent. If `Δ'ⱼ` are the blocks built from a second bump function `φ'`, the
almost orthogonality of the two decompositions gives `L` with
`Δ'ⱼ u = ∑_{|j - k| < L} Δ'ⱼ Δₖ u`, and the blocks `Δ'ⱼ` are bounded on `Lᵖ` uniformly in `j`. Hence
`2^{s j} ‖Δ'ⱼ u‖_p ≤ C 2^{|s| L} ∑_{|j - k| < L} 2^{s k} ‖Δₖ u‖_p`, and the `ℓ^q` norm of the
right-hand side is at most `2 L` times that of `(2^{s k} ‖Δₖ u‖_p)_k`, since shifting a sequence
does not increase its `ℓ^q` norm. The constant depends only on `φ`, `φ'` and `s`, not on `p` or
`q`.

Every `Lᵖ` function lies in `B^0_{p,∞}`, with `‖f‖_{B^0_{p,∞}} ≤ C ‖f‖_p`, since the blocks are
bounded on `Lᵖ` uniformly in `j`.

## Main declarations

* `TemperedDistribution.besovNorm`: the Besov norm `‖u‖_{B^s_{p,q}}`.
* `TemperedDistribution.besov`: the inhomogeneous Besov space `B^s_{p,q}`, as a submodule of
  `𝓢'(E, F)`.
* `TemperedDistribution.eLpNorm_littlewoodPaleyBlock_lt_top`: the blocks of a distribution in
  `B^s_{p,q}` are `Lᵖ` functions.
* `TemperedDistribution.exists_besovNorm_le_mul_besovNorm`: the Besov norms built from two bump
  functions are comparable, with a constant independent of `p` and `q`.
* `TemperedDistribution.besov_eq`: the Besov space does not depend on the bump function.
* `TemperedDistribution.besov_anti`: `B^s_{p,q} ⊆ B^{s'}_{p,q}` for `s' ≤ s`.
* `TemperedDistribution.coe_mem_besov_zero_top`: `Lᵖ ⊆ B^0_{p,∞}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.68 and Lemma 2.69.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2 and
  Theorem 6.2.4.
-/

public section

noncomputable section

open MeasureTheory hiding eLpNorm
open scoped ENNReal NNReal SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The **Besov norm** `‖u‖_{B^s_{p,q}} = ‖(2^{s j} ‖Δⱼ u‖_p)_{j ≥ 0}‖_{ℓ^q}` of a tempered
distribution, for the Littlewood–Paley blocks `Δⱼ` built from the bump function `φ`. Here
`‖Δⱼ u‖_p` is the extended `Lᵖ` norm, which is infinite unless `Δⱼ u` is given by an `Lᵖ`
function. -/
def besovNorm (u : 𝓢'(E, F)) (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] :
    ℝ≥0∞ :=
  MeasureTheory.eLpNorm (fun j : ℕ ↦ 2 ^ (s * j) * (littlewoodPaleyBlock F φ j u).eLpNorm p) q
    .count

section Norm

variable (φ : ContDiffBump (0 : E)) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (q : ℝ≥0∞)

/-- Unfolding `TemperedDistribution.besovNorm`. -/
theorem besovNorm_def (u : 𝓢'(E, F)) :
    u.besovNorm φ s p q = MeasureTheory.eLpNorm
      (fun j : ℕ ↦ 2 ^ (s * j) * (littlewoodPaleyBlock F φ j u).eLpNorm p) q .count :=
  (rfl)

@[simp]
theorem besovNorm_zero : (0 : 𝓢'(E, F)).besovNorm φ s p q = 0 := by
  simp [besovNorm_def]

/-- The Besov norm is subadditive. -/
theorem besovNorm_add_le (hq : 1 ≤ q) (u v : 𝓢'(E, F)) :
    (u + v).besovNorm φ s p q ≤ u.besovNorm φ s p q + v.besovNorm φ s p q := by
  simp only [besovNorm_def]
  refine le_trans ?_ (MeasureTheory.eLpNorm_add_le hq)
  refine eLpNorm_count_le_of_injOn (e := id) (Set.injOn_id _) (fun j ↦ ?_) q
  rw [id, Pi.add_apply, ← mul_add, map_add]
  gcongr
  exact eLpNorm_add_le _ _

/-- The Besov norm is homogeneous. -/
theorem besovNorm_smul (c : ℂ) (u : 𝓢'(E, F)) :
    (c • u).besovNorm φ s p q = ‖c‖ₑ * u.besovNorm φ s p q := by
  simp only [besovNorm_def, map_smul, eLpNorm_smul, mul_left_comm _ ‖c‖ₑ]
  exact eLpNorm_const_mul_ennreal (measurable_of_countable _).aestronglyMeasurable

@[simp]
theorem besovNorm_neg (u : 𝓢'(E, F)) : (-u).besovNorm φ s p q = u.besovNorm φ s p q := by
  simp [besovNorm_def]

variable {q} in
/-- Each weighted block norm `2^{s j} ‖Δⱼ u‖_p` is at most the Besov norm `‖u‖_{B^s_{p,q}}`. -/
theorem two_rpow_mul_eLpNorm_littlewoodPaleyBlock_le_besovNorm (hq : q ≠ 0) (u : 𝓢'(E, F))
    (j : ℕ) : 2 ^ (s * j) * (littlewoodPaleyBlock F φ j u).eLpNorm p ≤ u.besovNorm φ s p q :=
  le_eLpNorm_count (fun j : ℕ ↦ 2 ^ (s * j) * (littlewoodPaleyBlock F φ j u).eLpNorm p) hq j

variable {q} in
/-- The Besov norm is definite: for `q ≠ 0`, it vanishes only at `0`. If all the blocks `Δⱼ u`
vanish, then so does `u = ∑ⱼ Δⱼ u`. -/
theorem besovNorm_eq_zero_iff (hq : q ≠ 0) {u : 𝓢'(E, F)} :
    u.besovNorm φ s p q = 0 ↔ u = 0 := by
  refine ⟨fun hu ↦ ?_, by rintro rfl; exact besovNorm_zero φ s q⟩
  have hblock (j : ℕ) : littlewoodPaleyBlock F φ j u = 0 := by
    have h := (two_rpow_mul_eLpNorm_littlewoodPaleyBlock_le_besovNorm φ s hq u j).trans_eq hu
    rcases mul_eq_zero.1 (nonpos_iff_eq_zero.1 h) with h | h
    · exact absurd h (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
    · exact eLpNorm_eq_zero_iff.1 h
  refine tendsto_nhds_unique (tendsto_sum_littlewoodPaleyBlock φ u) ?_
  simp only [hblock, Finset.sum_const_zero]
  exact tendsto_const_nhds

variable {s} in
/-- The Besov norm increases with the smoothness index. -/
theorem besovNorm_mono {s' : ℝ} (hs : s' ≤ s) (u : 𝓢'(E, F)) :
    u.besovNorm φ s' p q ≤ u.besovNorm φ s p q := by
  simp only [besovNorm_def]
  refine eLpNorm_count_le_of_injOn (e := id) (Set.injOn_id _) (fun j ↦ ?_) q
  rw [id]
  gcongr
  exact one_le_two

end Norm

/-! ### The Besov space -/

section Space

variable (F) in
/-- The **inhomogeneous Besov space** `B^s_{p,q}`, for `1 ≤ p, q ≤ ∞`: the tempered distributions
whose Besov norm `‖(2^{s j} ‖Δⱼ u‖_p)_j‖_{ℓ^q}`, for the Littlewood–Paley blocks `Δⱼ` built from
`φ`, is finite. By `TemperedDistribution.besov_eq` it does not depend on `φ`. -/
def besov (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Submodule ℂ 𝓢'(E, F) where
  carrier := {u | u.besovNorm φ s p q < ∞}
  add_mem' {u v} hu hv :=
    (besovNorm_add_le φ s q Fact.out u v).trans_lt (ENNReal.add_lt_top.2 ⟨hu, hv⟩)
  zero_mem' := by simp
  smul_mem' c u hu := by
    rw [Set.mem_ofPred_eq, besovNorm_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hu

variable (φ : ContDiffBump (0 : E)) (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem mem_besov_iff {u : 𝓢'(E, F)} : u ∈ besov F φ s p q ↔ u.besovNorm φ s p q < ∞ :=
  Iff.rfl

/-- The Littlewood–Paley blocks of a distribution in `B^s_{p,q}` are `Lᵖ` functions. -/
theorem eLpNorm_littlewoodPaleyBlock_lt_top {u : 𝓢'(E, F)} (hu : u ∈ besov F φ s p q) (j : ℕ) :
    (littlewoodPaleyBlock F φ j u).eLpNorm p < ∞ := by
  have h := (two_rpow_mul_eLpNorm_littlewoodPaleyBlock_le_besovNorm φ s
    (one_pos.trans_le (Fact.out : 1 ≤ q)).ne' u j).trans_lt hu
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'

variable {s} in
/-- **Monotonicity in the smoothness index.** `B^s_{p,q} ⊆ B^{s'}_{p,q}` for `s' ≤ s`. -/
theorem besov_anti {s' : ℝ} (hs : s' ≤ s) : besov F φ s p q ≤ besov F φ s' p q :=
  fun _ hu ↦ (besovNorm_mono φ q hs _).trans_lt hu

end Space

/-! ### Independence of the bump function -/

section Independence

/-- Every term `a k` with `|j - k| < L` appears, as `a (j + m - L)` for some `m < 2 L`, among the
`2 L` shifted sequences padded with zeros. -/
private theorem sum_Ico_le_sum_range (a : ℕ → ℝ≥0∞) (L j : ℕ) :
    ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), a k ≤
      ∑ m ∈ Finset.range (2 * L), if L ≤ j + m then a (j + m - L) else 0 := by
  set c : ℕ → ℝ≥0∞ := fun m ↦ if L ≤ j + m then a (j + m - L) else 0
  calc ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), a k
      = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c (k + L - j) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [Finset.mem_Ico] at hk
        simp only [c, show L ≤ j + (k + L - j) by omega, ↓reduceIte]
        congr 1
        omega
    _ = ∑ m ∈ (Finset.Ico (j + 1 - L) (j + L)).image (· + L - j), c m := by
        refine (Finset.sum_image fun k hk k' hk' h ↦ ?_).symm
        simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
        omega
    _ ≤ ∑ m ∈ Finset.range (2 * L), c m := by
        refine Finset.sum_le_sum_of_subset fun m hm ↦ ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hm
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_range]
        omega

/-- The sequence `a` shifted by `m - L` and padded with zeros has `ℓ^q` norm at most that of
`a`. -/
private theorem eLpNorm_shift_le (a : ℕ → ℝ≥0∞) (L m : ℕ) (q : ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun j ↦ if L ≤ j + m then a (j + m - L) else 0) q .count ≤
      MeasureTheory.eLpNorm a q .count := by
  refine eLpNorm_count_le_of_injOn (e := fun j ↦ j + m - L) (fun j hj k hk h ↦ ?_)
    (fun j ↦ ?_) q
  · have hj' : L ≤ j + m := by
      by_contra h'
      exact hj (by simp [h'])
    have hk' : L ≤ k + m := by
      by_contra h'
      exact hk (by simp [h'])
    simp only at h
    omega
  · split_ifs
    · exact le_rfl
    · exact bot_le

/-- For `|j - k| < L`, the weight `2^{s j}` is at most `2^{|s| L} 2^{s k}`. -/
private theorem two_rpow_le_mul_two_rpow (s : ℝ) {L j k : ℕ} (hjk : j < k + L) (hkj : k < j + L) :
    (2 : ℝ≥0∞) ^ (s * j) ≤ 2 ^ (|s| * L) * 2 ^ (s * k) := by
  rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h : |(j : ℝ) - k| ≤ L := by
    rw [abs_sub_le_iff]
    constructor
    · have : (j : ℝ) ≤ k + L := by exact_mod_cast hjk.le
      linarith
    · have : (k : ℝ) ≤ j + L := by exact_mod_cast hkj.le
      linarith
  have : s * ((j : ℝ) - k) ≤ |s| * L :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg s))
  linarith

/-- **Comparison of the blocks of two decompositions.** With `L` from
`TemperedDistribution.exists_littlewoodPaleyBlock_eq_sum_Ico` and `C` the uniform `Lᵖ` bound of the
blocks `Δ'ⱼ`, each weighted block norm of the decomposition built from `φ'` is bounded by
`C 2^{|s| L}` times the sum of the `2 L` shifted weighted block norms of the decomposition built
from `φ`. -/
private theorem weighted_eLpNorm_littlewoodPaleyBlock_le (φ φ' : ContDiffBump (0 : E)) (s : ℝ)
    {L : ℕ} (hL : ∀ (j : ℕ) (u : 𝓢'(E, F)), littlewoodPaleyBlock F φ' j u =
      ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
        littlewoodPaleyBlock F φ' j (littlewoodPaleyBlock F φ k u))
    {C : ℝ≥0} (hC : ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (u : 𝓢'(E, F)),
      (littlewoodPaleyBlock F φ' j u).eLpNorm p ≤ C * u.eLpNorm p)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢'(E, F)) (j : ℕ) :
    2 ^ (s * j) * (littlewoodPaleyBlock F φ' j u).eLpNorm p ≤
      C * 2 ^ (|s| * L) * ∑ m ∈ Finset.range (2 * L),
        if L ≤ j + m then
          2 ^ (s * (j + m - L : ℕ)) * (littlewoodPaleyBlock F φ (j + m - L) u).eLpNorm p
        else 0 := by
  set a : ℕ → ℝ≥0∞ := fun k ↦ 2 ^ (s * k) * (littlewoodPaleyBlock F φ k u).eLpNorm p
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_Ico_le_sum_range a L j) bot_le)
  rw [hL j u, Finset.mul_sum]
  calc 2 ^ (s * j) * (∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          littlewoodPaleyBlock F φ' j (littlewoodPaleyBlock F φ k u)).eLpNorm p
      ≤ 2 ^ (s * j) * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          C * (littlewoodPaleyBlock F φ k u).eLpNorm p := by
        gcongr
        exact (eLpNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ hC j _)
    _ = ∑ k ∈ Finset.Ico (j + 1 - L) (j + L),
          C * (2 ^ (s * j) * (littlewoodPaleyBlock F φ k u).eLpNorm p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ mul_left_comm _ _ _
    _ ≤ ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), C * 2 ^ (|s| * L) * a k := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [Finset.mem_Ico] at hk
        rw [mul_assoc, ← mul_assoc (2 ^ (|s| * L))]
        gcongr
        exact two_rpow_le_mul_two_rpow s (by omega) (by omega)

/-- **The Besov norms built from two bump functions are comparable.** For bump functions `φ` and
`φ'` and a smoothness index `s`, there is `C`, depending only on `φ`, `φ'` and `s`, such that
`‖u‖_{B^s_{p,q}} ≤ C ‖u‖_{B^s_{p,q}}` for the norms built from `φ'` and from `φ` respectively, for
every `1 ≤ p, q ≤ ∞` and every tempered distribution `u`. -/
theorem exists_besovNorm_le_mul_besovNorm (φ φ' : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞}, 1 ≤ q → ∀ u : 𝓢'(E, F),
      u.besovNorm φ' s p q ≤ C * u.besovNorm φ s p q := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ'
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_littlewoodPaleyBlock_le (F := F) φ'
  set K : ℝ≥0∞ := C₀ * 2 ^ (|s| * L)
  have hK : K * (2 * L) ≠ ∞ := by
    simp only [K]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofNat_ne_top))
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top L))
  refine ⟨(K * (2 * L)).toNNReal, fun {p} _ {q} hq u ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hK, besovNorm_def, besovNorm_def]
  set a : ℕ → ℝ≥0∞ := fun k ↦ 2 ^ (s * k) * (littlewoodPaleyBlock F φ k u).eLpNorm p
  set c : ℕ → ℕ → ℝ≥0∞ := fun m j ↦ if L ≤ j + m then a (j + m - L) else 0
  calc MeasureTheory.eLpNorm
        (fun j : ℕ ↦ 2 ^ (s * j) * (littlewoodPaleyBlock F φ' j u).eLpNorm p) q .count
      ≤ MeasureTheory.eLpNorm (fun j ↦ K * ∑ m ∈ Finset.range (2 * L), c m j) q .count :=
        eLpNorm_count_le_of_injOn (e := id) (Set.injOn_id _)
          (weighted_eLpNorm_littlewoodPaleyBlock_le φ φ' s hL hC₀ u) q
    _ = K * MeasureTheory.eLpNorm (∑ m ∈ Finset.range (2 * L), c m) q .count := by
        rw [← eLpNorm_const_mul_ennreal (measurable_of_countable _).aestronglyMeasurable]
        simp only [Finset.sum_apply]
    _ ≤ K * ∑ m ∈ Finset.range (2 * L), MeasureTheory.eLpNorm (c m) q .count := by
        gcongr
        exact MeasureTheory.eLpNorm_sum_le hq
    _ ≤ K * ∑ _m ∈ Finset.range (2 * L), MeasureTheory.eLpNorm a q .count := by
        gcongr with m
        exact eLpNorm_shift_le a L m q
    _ = K * (2 * L) * MeasureTheory.eLpNorm a q .count := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
        push_cast
        ring

/-- **The Besov space does not depend on the bump function.** -/
theorem besov_eq (φ φ' : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] : besov F φ s p q = besov F φ' s p q := by
  obtain ⟨C, hC⟩ := exists_besovNorm_le_mul_besovNorm (F := F) φ φ' s
  obtain ⟨C', hC'⟩ := exists_besovNorm_le_mul_besovNorm (F := F) φ' φ s
  ext u
  simp only [mem_besov_iff]
  exact ⟨fun hu ↦ (hC Fact.out u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu),
    fun hu ↦ (hC' Fact.out u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu)⟩

end Independence

/-! ### `Lᵖ` functions -/

/-- **`Lᵖ ⊆ B^0_{p,∞}`.** There is `C`, depending only on `φ`, such that
`‖u‖_{B^0_{p,∞}} = sup_j ‖Δⱼ u‖_p ≤ C ‖u‖_p` for every `1 ≤ p ≤ ∞` and every tempered
distribution `u`. -/
theorem exists_besovNorm_zero_top_le (φ : ContDiffBump (0 : E)) :
    ∃ C : ℝ≥0, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢'(E, F)),
      u.besovNorm φ 0 p ∞ ≤ C * u.eLpNorm p := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_littlewoodPaleyBlock_le (F := F) φ
  refine ⟨C, fun {p} _ u ↦ ?_⟩
  rw [besovNorm_def, eLpNorm_exponent_top (measurable_of_countable _).aestronglyMeasurable,
    eLpNormEssSup_count]
  simp only [zero_mul, ENNReal.rpow_zero, one_mul, enorm_eq_self]
  exact iSup_le fun j ↦ hC j u

/-- Every `Lᵖ` function lies in the Besov space `B^0_{p,∞}`. -/
theorem coe_mem_besov_zero_top (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp F p (volume : Measure E)) : (f : 𝓢'(E, F)) ∈ besov F φ 0 p ∞ := by
  obtain ⟨C, hC⟩ := exists_besovNorm_zero_top_le (F := F) φ
  rw [mem_besov_iff]
  refine (hC (f : 𝓢'(E, F))).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
  rw [eLpNorm_coe]
  exact enorm_lt_top

end TemperedDistribution
