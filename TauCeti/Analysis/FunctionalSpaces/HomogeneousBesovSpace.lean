/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.HomogeneousLittlewoodPaley
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Homogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`\dot Δⱼ` (`j ∈ ℤ`) be the homogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.homogeneousLittlewoodPaleyBlock`). For `s : ℝ` and `1 ≤ p ≤ ∞`, a tempered
distribution `u` lies in the **homogeneous Besov space** `\dot B^s_{p,q}` when its blocks
`\dot Δⱼ u` are `Lᵖ` functions with

`‖u‖_{\dot B^s_{p,q}} = ‖(2^{js} ‖\dot Δⱼ u‖_p)_{j ∈ ℤ}‖_{ℓ^q} < ∞`.

In contrast with the inhomogeneous space `B^s_{p,q}` (`TemperedDistribution.MemBesov`), every dyadic
frequency scale `2^j`, `j ∈ ℤ`, carries the weight `2^{js}`, so the quantity is homogeneous under
dyadic dilations. It is only a seminorm on tempered distributions: the blocks vanish on the
distributions whose Fourier transform is supported at the origin, the polynomials
(`TemperedDistribution.forall_homogeneousLittlewoodPaleyBlock_eq_zero_iff`). So `\dot B^s_{p,q}` is
a space of tempered distributions modulo polynomials.

We realise this quotient without forming it. The weighted block sequence `(2^{js} \dot Δⱼ u)ⱼ` of
`u` is an element of the normed space `ℓ^q(ℤ, Lᵖ)`, and the sequences arising this way form a
submodule `TauCeti.homogeneousBesovSubmodule`. This submodule, with the norm of `ℓ^q(ℤ, Lᵖ)`, is the
bundled space `TauCeti.HomogeneousBesovSpace`: two distributions have the same image exactly when
their difference has Fourier transform supported at the origin
(`TemperedDistribution.MemHomogeneousBesov.toHomogeneousBesovSpace_eq_iff`).

## Main declarations

* `TemperedDistribution.MemHomogeneousBesov φ s p q u`: the predicate `u ∈ \dot B^s_{p,q}`, and its
  characterisation `TemperedDistribution.memHomogeneousBesov_iff` by `Lᵖ` blocks with weighted
  `ℓ^q(ℤ)` norms.
* `TemperedDistribution.memHomogeneousBesov_of_isVanishingOn`: the distributions with Fourier
  transform supported at the origin, such as the constants, lie in every `\dot B^s_{p,q}`, with all
  blocks zero.
* `TemperedDistribution.MemHomogeneousBesov.of_bump`: the space does not depend on the bump
  function.
* `TemperedDistribution.MemBesov.memHomogeneousBesov`: for `s > 0`, `B^s_{p,q} ⊆ \dot B^s_{p,q}`.
* `TauCeti.HomogeneousBesovSpace F φ s p q`: the bundled space, the weighted block sequences in
  `ℓ^q(ℤ, Lᵖ)`, and `TemperedDistribution.MemHomogeneousBesov.toHomogeneousBesovSpace`, the image
  of a distribution in it, with its norm `norm_toHomogeneousBesovSpace_eq_tsum_rpow` (`q < ∞`)
  and `norm_toHomogeneousBesovSpace_eq_ciSup` (`q = ∞`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Definition 2.15 and Section 2.4.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.3.
* H. Triebel, *Theory of Function Spaces*, Chapter 5.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Distribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

section MemHomogeneousBesov

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **homogeneous Besov space** `\dot B^s_{p,q}` built from
the Littlewood–Paley cutoffs of `φ` if its weighted homogeneous blocks `2^{js} \dot Δⱼ u`, `j ∈ ℤ`,
are `Lᵖ` functions forming an `ℓ^q(ℤ)` sequence. See `TemperedDistribution.memHomogeneousBesov_iff`
for the formulation with the unweighted blocks. -/
def MemHomogeneousBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ v : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q,
    ∀ j : ℤ, (v j : 𝓢'(E, F)) =
      (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j u

variable {φ s p q}

/-- `u ∈ \dot B^s_{p,q}` exactly when every homogeneous block `\dot Δⱼ u` is an `Lᵖ` function `fⱼ`
and the sequence `2^{js} ‖fⱼ‖_p`, `j ∈ ℤ`, lies in `ℓ^q`. -/
theorem memHomogeneousBesov_iff {u : 𝓢'(E, F)} :
    u.MemHomogeneousBesov φ s p q ↔ ∃ f : ℤ → Lp F p (volume : Measure E),
      (∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) ∧
        Memℓp (fun j : ℤ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) q := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • v j, fun j ↦ ?_,
      (lp.memℓp v).norm.mono fun j ↦ le_of_eq ?_⟩
    · rw [Lp.toTemperedDistribution_smul, hv,
        inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]
    · rw [Real.norm_of_nonneg (by positivity), norm_smul, norm_inv,
        Complex.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ (by positivity)]
  · rintro ⟨f, hf, hmem⟩
    refine ⟨⟨fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f j, hmem.mono fun j ↦ le_of_eq ?_⟩,
      fun j ↦ ?_⟩
    · rw [norm_smul, Complex.norm_of_nonneg (by positivity)]
    · -- The `j`-th entry of the anonymous `lp` element is `2^{js} • f j` by definition: `lp`
      -- coerces through `Subtype.val` and has no lemma evaluating an anonymous constructor.
      rw [hf j]
      exact Lp.toTemperedDistribution_smul _ (f j)

theorem MemHomogeneousBesov.zero : (0 : 𝓢'(E, F)).MemHomogeneousBesov φ s p q :=
  ⟨0, fun j ↦ by simp⟩

theorem MemHomogeneousBesov.add {u v : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    (hv : v.MemHomogeneousBesov φ s p q) : (u + v).MemHomogeneousBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  refine ⟨a + b, fun j ↦ ?_⟩
  rw [lp.coeFn_add, Pi.add_apply, Lp.toTemperedDistribution_add, ha, hb, map_add, smul_add]

theorem MemHomogeneousBesov.smul {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) (c : ℂ) :
    (c • u).MemHomogeneousBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨c • a, fun j ↦ ?_⟩
  rw [lp.coeFn_smul, Pi.smul_apply, Lp.toTemperedDistribution_smul, ha, map_smul, smul_comm]

theorem MemHomogeneousBesov.neg {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) :
    (-u).MemHomogeneousBesov φ s p q := by
  simpa using hu.smul (-1)

theorem MemHomogeneousBesov.sub {u v : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    (hv : v.MemHomogeneousBesov φ s p q) : (u - v).MemHomogeneousBesov φ s p q := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- **Monotonicity in the fine index.** `\dot B^s_{p,q} ⊆ \dot B^s_{p,q'}` for `q ≤ q'`. Unlike the
inhomogeneous scale, the homogeneous scale is not monotone in `s`. -/
theorem MemHomogeneousBesov.mono {u : 𝓢'(E, F)} {q' : ℝ≥0∞}
    (hu : u.MemHomogeneousBesov φ s p q) (hq : q ≤ q') : u.MemHomogeneousBesov φ s p q' := by
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  exact memHomogeneousBesov_iff.2 ⟨f, hf, hmem.of_exponent_ge hq⟩

variable (φ s p q) in
/-- **Polynomials have homogeneous Besov seminorm zero.** A tempered distribution whose Fourier
transform vanishes away from the origin, such as a polynomial, lies in every homogeneous Besov
space: all its homogeneous blocks vanish. -/
theorem memHomogeneousBesov_of_isVanishingOn {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ) : u.MemHomogeneousBesov φ s p q :=
  ⟨0, fun j ↦ by simp [homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn φ hu j]⟩

/-- **The blocks of another bump function.** If the homogeneous blocks `\dot Δₖ u` built from `φ`
are `Lᵖ` functions `fₖ`, then the homogeneous blocks `\dot Δ'ⱼ u` built from `φ'` are `Lᵖ` functions
`f'ⱼ`, with `2^{js} ‖f'ⱼ‖_p ≤ K ∑_{j - L ≤ k < j + L} 2^{ks} ‖fₖ‖_p`. The constants `K` and `L`
depend only on `φ`, `φ'` and `s`. -/
private theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_le (φ φ' : ContDiffBump (0 : E))
    (s : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (f : ℤ → Lp F p (volume : Measure E)),
      (∀ k, homogeneousLittlewoodPaleyBlock F φ k u = f k) →
      ∃ f' : ℤ → Lp F p (volume : Measure E),
        (∀ j, homogeneousLittlewoodPaleyBlock F φ' j u = f' j) ∧
        ∀ j : ℤ, 2 ^ (s * j) * ‖f' j‖ ≤
          K * ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (s * k) * ‖f k‖ := by
  obtain ⟨L, hL⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ'
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ'
  refine ⟨max C 0 * 2 ^ (|s| * L), L, by positivity, fun {p} _ {u} f hf ↦ ?_⟩
  choose g hg hgC using fun j k ↦ hC (p := p) j (f k)
  refine ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), g j k, fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [hL j u]
    simp_rw [hf, hg]
    exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm
  · refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    calc 2 ^ (s * j) * ‖g j k‖ ≤ 2 ^ (|s| * L) * 2 ^ (s * k) * (max C 0 * ‖f k‖) := by
          gcongr
          · rw [Finset.mem_Ico] at hk
            refine Real.rpow_mul_le_rpow_abs_mul_mul_rpow_mul one_le_two s
              (abs_sub_le_iff.2 ⟨?_, ?_⟩)
            all_goals rw [sub_le_iff_le_add']; exact_mod_cast (by omega)
          · exact (hgC j k).trans (by gcongr; exact le_max_left C 0)
      _ = _ := by ring

/-- **Independence of the bump function.** A tempered distribution in the homogeneous Besov space
`\dot B^s_{p,q}` built from the Littlewood–Paley cutoffs of `φ` lies in the homogeneous Besov space
`\dot B^s_{p,q}` built from any other bump function `φ'`. -/
theorem MemHomogeneousBesov.of_bump {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    (φ' : ContDiffBump (0 : E)) : u.MemHomogeneousBesov φ' s p q := by
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  obtain ⟨K, L, hK, hKL⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_le (F := F) φ φ' s
  obtain ⟨f', hf', hle⟩ := hKL f hf
  refine memHomogeneousBesov_iff.2 ⟨f', hf', ((hmem.sum_Ico_sub_add_int L).const_mul K).mono
    fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hle j

/-- The low-frequency homogeneous blocks of `u ∈ B^s_{p,q}` are bounded in `Lᵖ`: there are `B` and
`Lᵖ` functions `G j` with `\dot Δⱼ u = G j` and `‖G j‖_p ≤ B` for every `j ≤ 0`. They are blocks of
the `Lᵖ` function `∑_{k ≤ N} Δₖ u`, for `N` with `φ.rOut ≤ 2^N φ.rIn`. -/
private theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos {u : 𝓢'(E, F)}
    {f : ℕ → Lp F p (volume : Measure E)} (hf : ∀ k, littlewoodPaleyBlock F φ k u = f k) :
    ∃ B : ℝ, ∃ G : ℤ → Lp F p (volume : Measure E), ∀ j ≤ 0,
      homogeneousLittlewoodPaleyBlock F φ j u = G j ∧ ‖G j‖ ≤ B := by
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
  set S : Lp F p (volume : Measure E) := ∑ k ∈ Finset.range (N + 1), f k
  choose G hG hGC using fun j : ℤ ↦ hC (p := p) j S
  refine ⟨C * ‖S‖, G, fun j hj ↦ ⟨?_, hGC j⟩⟩
  have hjN : (2 : ℝ) ^ j * φ.rOut ≤ 2 ^ N * φ.rIn :=
    calc (2 : ℝ) ^ j * φ.rOut ≤ 1 * φ.rOut :=
          mul_le_mul_of_nonneg_right (zpow_le_one_of_nonpos₀ (one_le_two (α := ℝ)) hj)
            φ.rOut_pos.le
      _ ≤ 2 ^ N * φ.rIn := by rw [one_mul]; exact ((div_lt_iff₀ φ.rIn_pos).1 hN).le
  rw [← homogeneousLittlewoodPaleyBlock_sum_littlewoodPaleyBlock_range φ hjN, ← hG j]
  congr 1
  rw [Finset.sum_congr rfl fun k _ ↦ hf k]
  exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm

/-- **Inhomogeneous Besov spaces of positive order are homogeneous Besov spaces.** For `s > 0` and
`q ≠ 0`, `B^s_{p,q} ⊆ \dot B^s_{p,q}`. The blocks `\dot Δⱼ`, `j ≥ 1`, are the inhomogeneous blocks
`Δⱼ`, and the blocks `\dot Δⱼ`, `j ≤ 0`, of `u` are blocks of the `Lᵖ` function `∑_{k ≤ N} Δₖ u`, so
they are bounded in `Lᵖ` and their weights `2^{js}` decay geometrically as `j → -∞`. -/
theorem MemBesov.memHomogeneousBesov {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (hs : 0 < s)
    (hq : q ≠ 0) : u.MemHomogeneousBesov φ s p q := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  obtain ⟨B, G, hG⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_nonpos hf
  -- The blocks of `u`: inhomogeneous blocks for `j ≥ 1`, the bounded `G j` for `j ≤ 0`.
  refine memHomogeneousBesov_iff.2 ⟨fun j ↦ if 1 ≤ j then f j.toNat else G j, fun j ↦ ?_, ?_⟩
  · dsimp only
    split_ifs with hj
    · rw [← hf, ← homogeneousLittlewoodPaleyBlock_natCast φ (by omega), Int.toNat_of_nonneg
        (by omega)]
    · exact (hG j (by omega)).1
  -- Dominate the weighted blocks by the reindexed inhomogeneous ones plus a geometric tail.
  have h₁ : Memℓp ({j : ℤ | 1 ≤ j}.indicator
      ((fun k : ℕ ↦ (2 : ℝ) ^ (s * k) * ‖f k‖) ∘ Int.toNat)) q :=
    hmem.indicator_comp fun a ha b hb h ↦ by
      simp only [Set.mem_ofPred_eq] at ha hb
      omega
  have hr : (0 : ℝ) ≤ 2 ^ (-s) := by positivity
  have hr1 : (2 : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hs)
  have h₂ : Memℓp ({j : ℤ | j ≤ 0}.indicator
      ((fun i : ℕ ↦ B * ((2 : ℝ) ^ (-s)) ^ i) ∘ fun j ↦ (-j).toNat)) q :=
    (Memℓp.of_norm_le_geometric hr hr1 (C := |B|) (fun i ↦ by
      rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_of_nonneg hr]) hq).indicator_comp
      fun a ha b hb h ↦ by
      simp only [Set.mem_ofPred_eq] at ha hb h
      omega
  refine (h₁.add h₂).mono fun j ↦ ?_
  simp only [Pi.add_apply, Set.indicator, Set.mem_ofPred_eq, Function.comp_apply]
  rw [Real.norm_of_nonneg (by positivity)]
  split_ifs with hj hj' hj'
  · omega
  · have hcast : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [hcast, add_zero]
  · rw [zero_add]
    -- For `j ≤ 0`, `2^{js} = (2^{-s})^{-j}`.
    have hpow : (2 : ℝ) ^ (s * j) = ((2 : ℝ) ^ (-s)) ^ (-j).toNat := by
      have hcast : (((-j).toNat : ℕ) : ℝ) = -j := by
        exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, hcast]
      ring_nf
    rw [hpow, mul_comm B]
    gcongr
    exact (hG j hj').2
  · omega

end MemHomogeneousBesov

end TemperedDistribution

namespace TauCeti

open TemperedDistribution

variable (F) in
/-- The weighted homogeneous block sequences `(2^{js} \dot Δⱼ u)_{j ∈ ℤ}` of tempered distributions
`u`, as a submodule of `ℓ^q(ℤ, Lᵖ)`. A sequence lies in it exactly when it is the weighted block
sequence of some `u ∈ \dot B^s_{p,q}`; the distribution `u` is determined only up to a
polynomial. -/
def homogeneousBesovSubmodule (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℂ (lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q) where
  carrier := {v | ∃ u : 𝓢'(E, F), ∀ j : ℤ, (v j : 𝓢'(E, F)) =
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j u}
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, fun j ↦ by
      rw [lp.coeFn_add, Pi.add_apply, Lp.toTemperedDistribution_add, hu, hv, map_add, smul_add]⟩
  zero_mem' := ⟨0, fun j ↦ by simp⟩
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    exact ⟨c • u, fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, Lp.toTemperedDistribution_smul, hu, map_smul, smul_comm]⟩

variable (F) in
/-- The **homogeneous Besov space** `\dot B^s_{p,q}` built from the Littlewood–Paley cutoffs of `φ`:
the tempered distributions in `\dot B^s_{p,q}` modulo those with Fourier transform supported at the
origin, realised as their weighted block sequences in `ℓ^q(ℤ, Lᵖ)`. For `1 ≤ q` it is a normed
space, whose norm is the homogeneous Besov norm. -/
abbrev HomogeneousBesovSpace (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] :=
  ↥(homogeneousBesovSubmodule F φ s p q)

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

theorem mem_homogeneousBesovSubmodule_iff {v : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q} :
    v ∈ homogeneousBesovSubmodule F φ s p q ↔ ∃ u : 𝓢'(E, F), ∀ j : ℤ, (v j : 𝓢'(E, F)) =
      (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j u :=
  Iff.rfl

end TauCeti

namespace TemperedDistribution.MemHomogeneousBesov

open TauCeti

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The image of a tempered distribution `u ∈ \dot B^s_{p,q}` in the bundled homogeneous Besov
space: its weighted block sequence `(2^{js} \dot Δⱼ u)_{j ∈ ℤ}`. -/
def toHomogeneousBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q) : HomogeneousBesovSpace F φ s p q :=
  ⟨hu.choose, u, hu.choose_spec⟩

/-- The entries of the image of `u` in `\dot B^s_{p,q}` are the weighted blocks
`2^{js} \dot Δⱼ u`. -/
@[simp]
theorem coe_toHomogeneousBesovSpace_apply
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) (j : ℤ) :
    (((hu.toHomogeneousBesovSpace : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q) j :
      Lp F p (volume : Measure E)) : 𝓢'(E, F)) =
      (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j u :=
  hu.choose_spec j

/-- **`\dot B^s_{p,q}` is a space modulo polynomials.** Two tempered distributions in
`\dot B^s_{p,q}` have the same image exactly when the Fourier transform of their difference
vanishes away from the origin. -/
theorem toHomogeneousBesovSpace_eq_iff
    {u v : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) (hv : v.MemHomogeneousBesov φ s p q) :
    hu.toHomogeneousBesovSpace = hv.toHomogeneousBesovSpace ↔
      IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  rw [← forall_homogeneousLittlewoodPaleyBlock_eq_zero_iff φ]
  simp_rw [map_sub, sub_eq_zero]
  refine ⟨fun h j ↦ smul_right_injective _
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos two_pos (s * j)).ne') ?_, fun h ↦ ?_⟩
  · dsimp only
    rw [← hu.coe_toHomogeneousBesovSpace_apply, ← hv.coe_toHomogeneousBesovSpace_apply, h]
  · refine Subtype.ext (lp.ext (funext fun j ↦ ?_))
    exact LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
        MemHomogeneousBesov.coe_toHomogeneousBesovSpace_apply, h]

/-- The image in `\dot B^s_{p,q}` of a distribution does not change when a polynomial is added. -/
theorem toHomogeneousBesovSpace_add_eq
    {u w : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    (hw : IsVanishingOn (𝓕 w : 𝓢'(E, F)) {0}ᶜ) :
    (hu.add (memHomogeneousBesov_of_isVanishingOn φ s p q hw)).toHomogeneousBesovSpace =
      hu.toHomogeneousBesovSpace := by
  rwa [MemHomogeneousBesov.toHomogeneousBesovSpace_eq_iff, add_sub_cancel_left]

theorem toHomogeneousBesovSpace_add
    {u v : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) (hv : v.MemHomogeneousBesov φ s p q) :
    (hu.add hv).toHomogeneousBesovSpace =
      hu.toHomogeneousBesovSpace + hv.toHomogeneousBesovSpace := by
  refine Subtype.ext (lp.ext (funext fun j ↦ ?_))
  refine LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
    MemHomogeneousBesov.coe_toHomogeneousBesovSpace_apply, Submodule.coe_add, lp.coeFn_add,
    Pi.add_apply, map_add, smul_add]

theorem toHomogeneousBesovSpace_smul
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) (c : ℂ) :
    (hu.smul c).toHomogeneousBesovSpace = c • hu.toHomogeneousBesovSpace := by
  refine Subtype.ext (lp.ext (funext fun j ↦ ?_))
  refine LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
    MemHomogeneousBesov.coe_toHomogeneousBesovSpace_apply, Submodule.coe_smul, lp.coeFn_smul,
    Pi.smul_apply, map_smul, smul_comm c]

/-- If the blocks `\dot Δⱼ u` are the `Lᵖ` functions `fⱼ`, the entries of the image of `u` in
`\dot B^s_{p,q}` are the weighted blocks `2^{js} fⱼ`. -/
theorem coe_toHomogeneousBesovSpace_apply_eq
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) (j : ℤ) :
    (hu.toHomogeneousBesovSpace : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q) j =
      (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • f j :=
  LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      MemHomogeneousBesov.coe_toHomogeneousBesovSpace_apply, hf, Lp.toTemperedDistribution_smul]

theorem norm_coe_toHomogeneousBesovSpace_apply
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) (j : ℤ) :
    ‖(hu.toHomogeneousBesovSpace : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q) j‖ =
      2 ^ (s * j) * ‖f j‖ := by
  rw [hu.coe_toHomogeneousBesovSpace_apply_eq hf, norm_smul, Complex.norm_of_nonneg (by positivity)]

section Normed

variable [Fact (1 ≤ q)]

/-- **The single-block bound.** If the block `\dot Δⱼ u` is the `Lᵖ` function `fⱼ`, then
`2^{js} ‖fⱼ‖_p` is at most the homogeneous Besov norm of `u`. -/
theorem rpow_mul_norm_le_norm_toHomogeneousBesovSpace
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) (j : ℤ) :
    2 ^ (s * j) * ‖f j‖ ≤ ‖hu.toHomogeneousBesovSpace‖ := by
  rw [← hu.norm_coe_toHomogeneousBesovSpace_apply hf, ← Submodule.norm_coe]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j

/-- For `q < ∞` the homogeneous Besov norm of `u` is `(∑_{j ∈ ℤ} (2^{js} ‖\dot Δⱼ u‖_p)^q)^{1/q}`,
where the blocks `\dot Δⱼ u` are the `Lᵖ` functions `fⱼ`. -/
theorem norm_toHomogeneousBesovSpace_eq_tsum_rpow
    (hq : q ≠ ∞) {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) :
    ‖hu.toHomogeneousBesovSpace‖ =
      (∑' j : ℤ, (2 ^ (s * j) * ‖f j‖) ^ q.toReal) ^ (1 / q.toReal) := by
  rw [← Submodule.norm_coe,
    lp.norm_eq_tsum_rpow (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)]
  congr 1
  refine tsum_congr fun j ↦ ?_
  rw [hu.norm_coe_toHomogeneousBesovSpace_apply hf]

/-- For `q = ∞` the homogeneous Besov norm of `u` is `sup_{j ∈ ℤ} 2^{js} ‖\dot Δⱼ u‖_p`, where the
blocks `\dot Δⱼ u` are the `Lᵖ` functions `fⱼ`. -/
theorem norm_toHomogeneousBesovSpace_eq_ciSup
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p ∞) {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) :
    ‖hu.toHomogeneousBesovSpace‖ = ⨆ j : ℤ, 2 ^ (s * j) * ‖f j‖ := by
  rw [← Submodule.norm_coe, lp.norm_eq_ciSup]
  simp_rw [hu.norm_coe_toHomogeneousBesovSpace_apply hf]

end Normed

end TemperedDistribution.MemHomogeneousBesov

namespace TauCeti

open TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every element of `\dot B^s_{p,q}` is the image of a tempered distribution. -/
theorem HomogeneousBesovSpace.exists_toHomogeneousBesovSpace_eq
    (v : HomogeneousBesovSpace F φ s p q) :
    ∃ (u : 𝓢'(E, F)) (hu : u.MemHomogeneousBesov φ s p q), hu.toHomogeneousBesovSpace = v := by
  obtain ⟨v, u, hu⟩ := v
  refine ⟨u, ⟨v, hu⟩, Subtype.ext (lp.ext (funext fun j ↦ ?_))⟩
  exact LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, hu]
    exact MemHomogeneousBesov.coe_toHomogeneousBesovSpace_apply _ j

end TauCeti
