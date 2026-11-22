/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.HomogeneousLittlewoodPaley
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Homogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space of
dimension `n` and let `Pⱼ`, `j ∈ ℤ`, be the homogeneous Littlewood–Paley blocks built from it
(`TemperedDistribution.homogeneousLittlewoodPaleyBlock`). For `s : ℝ` and `1 ≤ p ≤ ∞`, the
**homogeneous Besov space** `\dot B^s_{p,q}`, `0 ≤ q ≤ ∞`, consists of the tempered distributions
`u` whose blocks `Pⱼ u` are `Lᵖ` functions with

`‖u‖_{\dot B^s_{p,q}} = ‖(2^{js} ‖Pⱼ u‖_p)_{j ∈ ℤ}‖_{ℓ^q} < ∞`.

In contrast to the inhomogeneous space `B^s_{p,q}` of `TauCeti.BesovSpace`, every dyadic frequency
size `2^j`, down to `j → -∞`, carries its own weight, and no block collects the low frequencies.
The blocks do not see the frequency `0`: a tempered distribution whose Fourier transform vanishes
on `E \ {0}`, such as a polynomial, has no homogeneous blocks
(`TemperedDistribution.homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero`). So
for `1 ≤ q` the quantity `‖·‖_{\dot B^s_{p,q}}` is only a seminorm, and its null space is exactly
the space of distributions with spectrum at the origin
(`TauCeti.HomogeneousBesovSpace.norm_eq_zero_iff`). Two elements are inseparable, that is at
distance zero, exactly when their difference has spectrum at the origin
(`TauCeti.HomogeneousBesovSpace.inseparable_iff`), so the normed space `\dot B^s_{p,q}` of
distributions modulo those with spectrum at the origin is the separation quotient
`SeparationQuotient (TauCeti.HomogeneousBesovSpace F φ s p q)`.

The space is defined relative to the bump function `φ`, but membership is not: the homogeneous
blocks of two bump functions interact only at nearby indices
(`TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico`), so
`u ∈ \dot B^s_{p,q}` for one bump function implies the same for every other
(`TemperedDistribution.MemHomogeneousBesov.of_bump`).

The decomposition of `u ∈ \dot B^s_{p,q}` into its blocks converges up to the critical regularity
`n / p`. If `s < n / p`, or `s = n / p` and `q ≤ 1`, the two-sided partial sums
`∑_{a < j ≤ b} Pⱼ u` converge in the tempered distributions as `a → -∞` and `b → ∞`, to a
distribution `v` whose difference with `u` has spectrum at the origin
(`TemperedDistribution.MemHomogeneousBesov.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock`).
This is the reconstruction `u = ∑_{j ∈ ℤ} Pⱼ u` modulo distributions with spectrum at the origin.
The high-frequency partial sums `∑_{0 < j ≤ b} Pⱼ u` always converge, to `u` minus a low-pass
truncation of `u`. For the low frequencies Bernstein's inequality
(`TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le`) gives

`‖Pⱼ u‖_∞ ≤ C 2^{jn/p} ‖Pⱼ u‖_p = C 2^{j(n/p - s)} (2^{js} ‖Pⱼ u‖_p)`,

which is summable over `j ≤ 0`: geometrically when `s < n / p`, since the weighted block norms are
bounded, and by the summability of the weighted block norms when `s = n / p` and `q ≤ 1`. So the
low-frequency blocks sum in `L^∞`
(`TemperedDistribution.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock_of_summable`).

## Main declarations

* `TemperedDistribution.MemHomogeneousBesov φ s p q u`: the unbundled predicate
  `u ∈ \dot B^s_{p,q}`, and its characterisation `TemperedDistribution.memHomogeneousBesov_iff`
  by `Lᵖ` blocks with weighted `ℓ^q` norms.
* `TemperedDistribution.MemHomogeneousBesov.of_isVanishingOn_fourier_sub`: membership depends on
  `u` only modulo distributions with spectrum at the origin, and
  `TemperedDistribution.memHomogeneousBesov_of_isVanishingOn_fourier`: these lie in every
  `\dot B^s_{p,q}`.
* `TemperedDistribution.MemHomogeneousBesov.mono`: `\dot B^s_{p,q} ⊆ \dot B^s_{p,q'}` for `q ≤ q'`.
* `TemperedDistribution.MemHomogeneousBesov.of_bump`: membership does not depend on the bump
  function.
* `TemperedDistribution.MemHomogeneousBesov.mono_exponent`: the Bernstein embedding
  `\dot B^s_{p,q} ⊆ \dot B^{s - n (1/p - 1/r)}_{r,q}` for `p ≤ r`.
* `TemperedDistribution.MemHomogeneousBesov.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock`:
  the reconstruction modulo distributions with spectrum at the origin, for `s < n / p`, or
  `s = n / p` and `q ≤ 1`.
* `TauCeti.HomogeneousBesovSpace F φ s p q`: the bundled space, a complex seminormed space whose
  elements carry their tempered distribution `toDistr` and weighted blocks `weightedBlocks`. The
  weighted blocks form a linear isometry `TauCeti.HomogeneousBesovSpace.weightedBlocksₗᵢ` into
  `ℓ^q(ℤ, Lᵖ)`, and `TauCeti.HomogeneousBesovSpace.block` is the block `Pⱼ u` as an `Lᵖ` function.
* `TauCeti.HomogeneousBesovSpace.norm_eq_zero_iff` and
  `TauCeti.HomogeneousBesovSpace.inseparable_iff`: the seminorm vanishes exactly on the
  distributions with spectrum at the origin.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2
  (Definition 2.15 of `\dot B^s_{p,r}` and the convergence of the homogeneous decomposition below
  the critical regularity).
* H. Triebel, *Theory of Function Spaces*, Chapter 5 (homogeneous spaces as distributions modulo
  polynomials).
-/

public section

noncomputable section

open MeasureTheory FourierTransform Distribution Filter Topology
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

section MemHomogeneousBesov

variable (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A tempered distribution `u` lies in the **homogeneous Besov space** `\dot B^s_{p,q}` built from
the Littlewood–Paley partition of `φ` if its weighted homogeneous blocks `2^{js} Pⱼ u`, `j ∈ ℤ`,
are `Lᵖ` functions forming an `ℓ^q` sequence. See `TemperedDistribution.memHomogeneousBesov_iff` for
the formulation with the unweighted blocks. -/
def MemHomogeneousBesov (u : 𝓢'(E, F)) : Prop :=
  ∃ v : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q,
    ∀ j : ℤ, (v j : 𝓢'(E, F)) =
      (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j u

variable {φ s p q}

/-- `u ∈ \dot B^s_{p,q}` exactly when every homogeneous block `Pⱼ u` is an `Lᵖ` function `fⱼ` and
the sequence `2^{js} ‖fⱼ‖_p`, `j ∈ ℤ`, lies in `ℓ^q`. -/
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

/-- If the homogeneous blocks `Pⱼ u` are the `Lᵖ` functions `fⱼ`, then `u ∈ \dot B^s_{p,q}` exactly
when the sequence `2^{js} ‖fⱼ‖_p` lies in `ℓ^q`. -/
theorem memHomogeneousBesov_iff_memℓp {u : 𝓢'(E, F)} {f : ℤ → Lp F p (volume : Measure E)}
    (hf : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u = f j) :
    u.MemHomogeneousBesov φ s p q ↔ Memℓp (fun j : ℤ ↦ (2 : ℝ) ^ (s * j) * ‖f j‖) q := by
  refine ⟨fun hu ↦ ?_, fun h ↦ memHomogeneousBesov_iff.2 ⟨f, hf, h⟩⟩
  obtain ⟨g, hg, hmem⟩ := memHomogeneousBesov_iff.1 hu
  -- An `Lᵖ` function is determined by its tempered distribution, so `g = f`.
  have hgf : g = f := funext fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ← hg, hf]
  rwa [hgf] at hmem

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
inhomogeneous scale, the homogeneous scale is not monotone in `s`: lowering `s` increases the
weights of the low-frequency blocks. -/
theorem MemHomogeneousBesov.mono {u : 𝓢'(E, F)} {q' : ℝ≥0∞} (hu : u.MemHomogeneousBesov φ s p q)
    (hq : q ≤ q') : u.MemHomogeneousBesov φ s p q' := by
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  exact memHomogeneousBesov_iff.2 ⟨f, hf, hmem.of_exponent_ge hq⟩

/-- **Membership modulo spectrum at the origin.** If `u ∈ \dot B^s_{p,q}` and the Fourier transform
of `u - v` vanishes on `E \ {0}`, as when `u - v` is a polynomial, then `v ∈ \dot B^s_{p,q}`: the
two have the same homogeneous blocks. -/
theorem MemHomogeneousBesov.of_isVanishingOn_fourier_sub {u v : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q) (h : IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ) :
    v.MemHomogeneousBesov φ s p q := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨a, fun j ↦ ?_⟩
  rw [ha, homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub φ h]

/-- **Distributions with spectrum at the origin lie in every homogeneous Besov space.** If the
Fourier transform of `u` vanishes on `E \ {0}`, as for a polynomial, then `u ∈ \dot B^s_{p,q}` for
every `s`, `p` and `q`. -/
theorem memHomogeneousBesov_of_isVanishingOn_fourier {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ) : u.MemHomogeneousBesov φ s p q :=
  ⟨0, fun j ↦ by
    rw [homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero φ hu, smul_zero]
    simp⟩

/-- **The Bernstein embedding.** For `p ≤ r`, `\dot B^s_{p,q} ⊆ \dot B^{s - n (1/p - 1/r)}_{r,q}`,
where `n` is the dimension of `E` and `1/∞ = 0`: raising the integrability exponent of the blocks
from `p` to `r` costs exactly `n (1/p - 1/r)` orders of smoothness, at every frequency. -/
theorem MemHomogeneousBesov.mono_exponent {u : 𝓢'(E, F)} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hu : u.MemHomogeneousBesov φ s p q) (hpr : p ≤ r) :
    u.MemHomogeneousBesov φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r q := by
  obtain ⟨C, _, hB⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le (F := F) φ hpr
  set a : ℝ := Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  choose g hg hgf using fun j ↦ hB j u (f j) (hf j)
  refine memHomogeneousBesov_iff.2 ⟨g, hg, (hmem.const_mul C).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  calc (2 : ℝ) ^ ((s - a) * j) * ‖g j‖
      ≤ 2 ^ ((s - a) * j) * (C * 2 ^ (a * j) * ‖f j‖) := by gcongr; exact hgf j
    _ = C * (2 ^ (s * j) * ‖f j‖) := by
        have h2 : (2 : ℝ) ^ ((s - a) * j) * 2 ^ (a * j) = 2 ^ (s * j) := by
          rw [← Real.rpow_add two_pos, sub_mul, sub_add_cancel]
        rw [← h2]
        ring

/-- **The blocks of another bump function.** If the homogeneous blocks `Pₖ u` built from `φ` are
`Lᵖ` functions `fₖ`, then the homogeneous blocks `P'ⱼ u` built from `φ'` are `Lᵖ` functions `f'ⱼ`,
with `2^{js} ‖f'ⱼ‖_p ≤ K ∑_{-L ≤ i < L} 2^{(j + i)s} ‖f_{j + i}‖_p`. The constants `K` and `L`
depend only on `φ`, `φ'` and `s`. -/
private theorem exists_homogeneousLittlewoodPaleyBlock_eq_and_le (φ φ' : ContDiffBump (0 : E))
    (s : ℝ) :
    ∃ K : ℝ, ∃ L : ℕ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : 𝓢'(E, F)}
      (f : ℤ → Lp F p (volume : Measure E)), (∀ k, homogeneousLittlewoodPaleyBlock F φ k u = f k) →
      ∃ f' : ℤ → Lp F p (volume : Measure E),
        (∀ j, homogeneousLittlewoodPaleyBlock F φ' j u = f' j) ∧
        ∀ j : ℤ, 2 ^ (s * j) * ‖f' j‖ ≤
          K * ∑ i ∈ Finset.Ico (-(L : ℤ)) L, 2 ^ (s * (j + i : ℤ)) * ‖f (j + i)‖ := by
  obtain ⟨L, hL⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ'
  obtain ⟨C, hC⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le (F := F) φ'
  refine ⟨max C 0 * 2 ^ (|s| * L), L, by positivity, fun {p} _ {u} f hf ↦ ?_⟩
  choose g hg hgC using fun j k ↦ hC (p := p) j (f k)
  refine ⟨fun j ↦ ∑ i ∈ Finset.Ico (-(L : ℤ)) L, g j (j + i), fun j ↦ ?_, fun j ↦ ?_⟩
  · have hI : Finset.Ico (j - L) (j + L) = Finset.Ico (-(L : ℤ) + j) (L + j) := by
      congr 1 <;> ring
    rw [hL j u, hI, ← Finset.sum_Ico_add]
    simp_rw [hf, hg]
    exact (map_sum (Lp.toTemperedDistributionCLM F volume p) _ _).symm
  · -- Within the window the weights `2^{js}` and `2^{(j + i)s}` differ by at most `2^{|s| L}`.
    have hw (i : ℤ) (hi : i ∈ Finset.Ico (-(L : ℤ)) L) :
        (2 : ℝ) ^ (s * j) ≤ 2 ^ (|s| * L) * 2 ^ (s * (j + i : ℤ)) := by
      rw [Finset.mem_Ico] at hi
      rw [← Real.rpow_add two_pos]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      have hi' : |(i : ℝ)| ≤ L := abs_le.2 ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2.le⟩
      have := neg_abs_le (s * i)
      rw [abs_mul] at this
      push_cast
      nlinarith [abs_nonneg s]
    calc 2 ^ (s * j) * ‖∑ i ∈ Finset.Ico (-(L : ℤ)) L, g j (j + i)‖
        ≤ 2 ^ (s * j) * ∑ i ∈ Finset.Ico (-(L : ℤ)) L, max C 0 * ‖f (j + i)‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          exact (hgC j (j + i)).trans (by gcongr; exact le_max_left C 0)
      _ = ∑ i ∈ Finset.Ico (-(L : ℤ)) L, max C 0 * (2 ^ (s * j) * ‖f (j + i)‖) := by
          rw [Finset.mul_sum]
          ring_nf
      _ ≤ ∑ i ∈ Finset.Ico (-(L : ℤ)) L,
            max C 0 * (2 ^ (|s| * L) * 2 ^ (s * (j + i : ℤ)) * ‖f (j + i)‖) := by
          gcongr with i hi
          exact hw i hi
      _ = _ := by
          rw [Finset.mul_sum]
          ring_nf

/-- **Independence of the bump function.** A tempered distribution in the homogeneous Besov
space `\dot B^s_{p,q}` built from the Littlewood–Paley partition of `φ` lies in the homogeneous
Besov space `\dot B^s_{p,q}` built from any other bump function `φ'`. -/
theorem MemHomogeneousBesov.of_bump {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q)
    (φ' : ContDiffBump (0 : E)) : u.MemHomogeneousBesov φ' s p q := by
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  obtain ⟨K, L, _, hKL⟩ := exists_homogeneousLittlewoodPaleyBlock_eq_and_le (F := F) φ φ' s
  obtain ⟨f', hf', hle⟩ := hKL f hf
  -- The window sums of an `ℓ^q` sequence over `ℤ` are a finite sum of its shifts.
  have hwin : Memℓp (fun j : ℤ ↦ ∑ i ∈ Finset.Ico (-(L : ℤ)) L,
      (2 : ℝ) ^ (s * (j + i : ℤ)) * ‖f (j + i)‖) q := by
    have h := Memℓp.finsetSum (Finset.Ico (-(L : ℤ)) L) fun i _ ↦
      hmem.comp_injective (add_left_injective i)
    simpa only [Finset.sum_apply, Function.comp_def] using h
  refine memHomogeneousBesov_iff.2 ⟨f', hf', (hwin.const_mul K).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hle j

/-- **Summability of the low frequencies below the critical regularity.** Let `bⱼ ≥ 0`, `j ∈ ℤ`, be
an `ℓ^q` sequence. If `s < e`, or `s = e` and `q ≤ 1`, then `2^{(e - s) j} bⱼ` is summable over
the nonpositive indices `j = -k`. -/
private theorem summable_two_rpow_mul_neg {b : ℤ → ℝ} (hb0 : ∀ j, 0 ≤ b j) (hb : Memℓp b q)
    {e : ℝ} (hs : s < e ∨ (s = e ∧ q ≤ 1)) :
    Summable fun k : ℕ ↦ (2 : ℝ) ^ ((e - s) * ((-k : ℤ) : ℝ)) * b (-k) := by
  rcases hs with hs | ⟨rfl, hq⟩
  · -- The weights decay geometrically and the sequence is bounded.
    obtain ⟨M, hM⟩ := memℓp_infty_iff.1 (hb.of_exponent_ge le_top)
    have hr : (2 : ℝ) ^ (-(e - s)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (by positivity) (hb0 _)) (fun k ↦ ?_)
      ((summable_geometric_of_lt_one (by positivity) hr).mul_left M)
    have hbM : b (-k) ≤ M := (Real.le_norm_self _).trans (hM ⟨-k, rfl⟩)
    have hw : (2 : ℝ) ^ ((e - s) * ((-k : ℤ) : ℝ)) = (2 ^ (-(e - s))) ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
      push_cast
      ring_nf
    rw [hw, mul_comm]
    exact mul_le_mul_of_nonneg_right hbM (by positivity)
  · -- At the critical regularity the sequence itself is summable.
    have h1 := (memℓp_gen_iff (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).1
      (hb.of_exponent_ge hq)
    simp only [ENNReal.toReal_one, Real.rpow_one] at h1
    have hinj : Function.Injective fun k : ℕ ↦ -(k : ℤ) :=
      neg_injective.comp Nat.cast_injective
    refine ((h1.comp_injective hinj).of_norm).congr fun k ↦ ?_
    simp

/-- **Reconstruction modulo spectrum at the origin, below the critical regularity.** Let
`u ∈ \dot B^s_{p,q}` with `s < n / p`, or `s = n / p` and `q ≤ 1`, where `n` is the dimension of `E`
and `1/∞ = 0`. Then the two-sided partial sums `∑_{a < j ≤ b} Pⱼ u` of the homogeneous blocks
converge in the tempered distributions, as `a → -∞` and `b → ∞`, to a distribution `v` such that
the Fourier transform of `u - v` vanishes on `E \ {0}`: `u` is the sum of its blocks modulo a
distribution with spectrum at the origin. -/
theorem MemHomogeneousBesov.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock {u : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q)
    (hs : s < Module.finrank ℝ E * p.toReal⁻¹ ∨ (s = Module.finrank ℝ E * p.toReal⁻¹ ∧ q ≤ 1)) :
    ∃ v : 𝓢'(E, F), Tendsto (fun ab : ℤ × ℤ ↦
        ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
          (atBot ×ˢ atTop) (𝓝 v) ∧ IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  set e : ℝ := Module.finrank ℝ E * p.toReal⁻¹
  obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
  -- Bernstein's inequality: the blocks are bounded functions `gⱼ`,
  -- `‖gⱼ‖_∞ ≤ C 2^{je} ‖Pⱼ u‖_p = C 2^{j(e - s)} (2^{js} ‖Pⱼ u‖_p)`.
  obtain ⟨C, -, hB⟩ :=
    exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le (F := F) φ (le_top : p ≤ ∞)
  choose g hg hgf using fun j ↦ hB j u (f j) (hf j)
  simp only [ENNReal.toReal_top, inv_zero, sub_zero] at hgf
  -- The bounded blocks of nonpositive index are summable in `L^∞`.
  refine exists_tendsto_sum_homogeneousLittlewoodPaleyBlock_of_summable φ (fun k ↦ hg (-k)) ?_
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ (hgf _).trans_eq ?_)
    ((summable_two_rpow_mul_neg (fun j ↦ by positivity) hmem hs).mul_left C)
  have h2 : (2 : ℝ) ^ ((e - s) * ((-k : ℤ) : ℝ)) * 2 ^ (s * ((-k : ℤ) : ℝ)) =
      2 ^ (e * ((-k : ℤ) : ℝ)) := by
    rw [← Real.rpow_add two_pos, ← add_mul, sub_add_cancel]
  rw [← h2]
  ring

end MemHomogeneousBesov

end TemperedDistribution

namespace TauCeti

open TemperedDistribution

variable (F) in
/-- The **homogeneous Besov space** `\dot B^s_{p,q}` built from the Littlewood–Paley partition of
the bump function `φ`: the tempered distributions `u` whose weighted homogeneous blocks
`2^{js} Pⱼ u`, `j ∈ ℤ`, are `Lᵖ` functions forming an `ℓ^q` sequence. An element stores both `u`
and this sequence, which determine each other. For `1 ≤ q` it is a seminormed space with
`‖u‖ = ‖(2^{js} ‖Pⱼ u‖_p)ⱼ‖_{ℓ^q}`, whose null space is formed by the distributions with spectrum
at the origin (`TauCeti.HomogeneousBesovSpace.norm_eq_zero_iff`). -/
structure HomogeneousBesovSpace (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] where
  /-- The underlying tempered distribution. -/
  toDistr : 𝓢'(E, F)
  /-- The weighted homogeneous Littlewood–Paley blocks `(2^{js} Pⱼ u)_{j ∈ ℤ}`, an `ℓ^q` sequence
  of `Lᵖ` functions. -/
  weightedBlocks : lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q
  /-- The `j`-th weighted block is the `j`-th homogeneous block of `toDistr`, multiplied by
  `2^{js}`. -/
  coe_weightedBlocks_apply : ∀ j : ℤ, (weightedBlocks j : 𝓢'(E, F)) =
    (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j toDistr

namespace HomogeneousBesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tempered distribution of an element of `\dot B^s_{p,q}` lies in `\dot B^s_{p,q}`. -/
theorem memHomogeneousBesov_toDistr (u : HomogeneousBesovSpace F φ s p q) :
    u.toDistr.MemHomogeneousBesov φ s p q :=
  ⟨u.weightedBlocks, u.coe_weightedBlocks_apply⟩

/-- An element of a homogeneous Besov space is determined by its tempered distribution. -/
@[ext]
theorem ext {u v : HomogeneousBesovSpace F φ s p q} (h : u.toDistr = v.toDistr) : u = v := by
  obtain ⟨u, a, ha⟩ := u
  obtain ⟨v, b, hb⟩ := v
  obtain rfl : u = v := h
  obtain rfl : a = b := lp.ext <| funext fun j ↦
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, ha, hb]
  rfl

instance : Zero (HomogeneousBesovSpace F φ s p q) where
  zero := ⟨0, 0, fun j ↦ by simp⟩

instance : Add (HomogeneousBesovSpace F φ s p q) where
  add u v := ⟨u.toDistr + v.toDistr, u.weightedBlocks + v.weightedBlocks, fun j ↦ by
    simp [smul_add, ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : Neg (HomogeneousBesovSpace F φ s p q) where
  neg u := ⟨-u.toDistr, -u.weightedBlocks, fun j ↦ by
    simp [← u.coe_weightedBlocks_apply]⟩

instance : Sub (HomogeneousBesovSpace F φ s p q) where
  sub u v := ⟨u.toDistr - v.toDistr, u.weightedBlocks - v.weightedBlocks, fun j ↦ by
    simp [smul_sub, ← u.coe_weightedBlocks_apply, ← v.coe_weightedBlocks_apply]⟩

instance : SMul ℂ (HomogeneousBesovSpace F φ s p q) where
  smul c u := ⟨c • u.toDistr, c • u.weightedBlocks, fun j ↦ by
    rw [lp.coeFn_smul, Pi.smul_apply, Lp.toTemperedDistribution_smul, u.coe_weightedBlocks_apply,
      map_smul, smul_comm]⟩

instance : SMul ℕ (HomogeneousBesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

instance : SMul ℤ (HomogeneousBesovSpace F φ s p q) where
  smul n u := (n : ℂ) • u

@[simp]
theorem toDistr_zero : (0 : HomogeneousBesovSpace F φ s p q).toDistr = 0 := (rfl)

@[simp]
theorem weightedBlocks_zero : (0 : HomogeneousBesovSpace F φ s p q).weightedBlocks = 0 := (rfl)

@[simp]
theorem toDistr_add (u v : HomogeneousBesovSpace F φ s p q) :
    (u + v).toDistr = u.toDistr + v.toDistr := (rfl)

@[simp]
theorem weightedBlocks_add (u v : HomogeneousBesovSpace F φ s p q) :
    (u + v).weightedBlocks = u.weightedBlocks + v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_neg (u : HomogeneousBesovSpace F φ s p q) : (-u).toDistr = -u.toDistr := (rfl)

@[simp]
theorem weightedBlocks_neg (u : HomogeneousBesovSpace F φ s p q) :
    (-u).weightedBlocks = -u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_sub (u v : HomogeneousBesovSpace F φ s p q) :
    (u - v).toDistr = u.toDistr - v.toDistr := (rfl)

@[simp]
theorem weightedBlocks_sub (u v : HomogeneousBesovSpace F φ s p q) :
    (u - v).weightedBlocks = u.weightedBlocks - v.weightedBlocks := (rfl)

@[simp]
theorem toDistr_smul (c : ℂ) (u : HomogeneousBesovSpace F φ s p q) :
    (c • u).toDistr = c • u.toDistr := (rfl)

@[simp]
theorem weightedBlocks_smul (c : ℂ) (u : HomogeneousBesovSpace F φ s p q) :
    (c • u).weightedBlocks = c • u.weightedBlocks := (rfl)

@[simp]
theorem toDistr_nsmul (n : ℕ) (u : HomogeneousBesovSpace F φ s p q) :
    (n • u).toDistr = n • u.toDistr :=
  Nat.cast_smul_eq_nsmul ℂ n u.toDistr

@[simp]
theorem toDistr_zsmul (n : ℤ) (u : HomogeneousBesovSpace F φ s p q) :
    (n • u).toDistr = n • u.toDistr :=
  Int.cast_smul_eq_zsmul ℂ n u.toDistr

instance : AddCommGroup (HomogeneousBesovSpace F φ s p q) :=
  fast_instance% Function.Injective.addCommGroup toDistr (fun _ _ ↦ ext) toDistr_zero
    toDistr_add toDistr_neg toDistr_sub (fun u n ↦ toDistr_nsmul n u) fun u n ↦ toDistr_zsmul n u

instance : Module ℂ (HomogeneousBesovSpace F φ s p q) :=
  fast_instance% Function.Injective.module ℂ
    (⟨⟨toDistr, toDistr_zero⟩, toDistr_add⟩ : HomogeneousBesovSpace F φ s p q →+ 𝓢'(E, F))
    (fun _ _ ↦ ext) toDistr_smul

variable (F φ s p q) in
/-- The weighted homogeneous blocks `u ↦ (2^{js} Pⱼ u)_{j ∈ ℤ}`, as a linear map into
`ℓ^q(ℤ, Lᵖ)`. -/
def weightedBlocksₗ :
    HomogeneousBesovSpace F φ s p q →ₗ[ℂ] lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q where
  toFun := weightedBlocks
  map_add' := weightedBlocks_add
  map_smul' := weightedBlocks_smul

@[simp]
theorem weightedBlocksₗ_apply (u : HomogeneousBesovSpace F φ s p q) :
    weightedBlocksₗ F φ s p q u = u.weightedBlocks := (rfl)

/-- The homogeneous block `Pⱼ u` of an element of a homogeneous Besov space, as an `Lᵖ`
function. -/
def block (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) : Lp F p (volume : Measure E) :=
  (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)⁻¹ • u.weightedBlocks j

/-- The `Lᵖ` function `u.block j` is the homogeneous block `Pⱼ u`. -/
@[simp]
theorem coe_block (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    (u.block j : 𝓢'(E, F)) = homogeneousLittlewoodPaleyBlock F φ j u.toDistr := by
  rw [block, Lp.toTemperedDistribution_smul, coe_weightedBlocks_apply,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

theorem weightedBlocks_apply (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    u.weightedBlocks j = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • u.block j := by
  rw [block, smul_inv_smul₀ (Complex.ofReal_ne_zero.2 (by positivity))]

theorem norm_weightedBlocks_apply (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    ‖u.weightedBlocks j‖ = 2 ^ (s * j) * ‖u.block j‖ := by
  rw [weightedBlocks_apply, norm_smul, Complex.norm_of_nonneg (by positivity)]

@[simp]
theorem block_zero (j : ℤ) : (0 : HomogeneousBesovSpace F φ s p q).block j = 0 := by
  simp [block]

@[simp]
theorem block_add (u v : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    (u + v).block j = u.block j + v.block j := by
  simp [block, smul_add]

@[simp]
theorem block_neg (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) : (-u).block j = -u.block j := by
  simp [block]

@[simp]
theorem block_sub (u v : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    (u - v).block j = u.block j - v.block j := by
  simp [block, smul_sub]

@[simp]
theorem block_smul (c : ℂ) (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    (c • u).block j = c • u.block j := by
  rw [block, block, weightedBlocks_smul, lp.coeFn_smul, Pi.smul_apply, smul_comm]

/-- A tempered distribution in `\dot B^s_{p,q}`, as an element of the bundled homogeneous Besov
space. -/
def _root_.TemperedDistribution.MemHomogeneousBesov.toHomogeneousBesovSpace {u : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q) : HomogeneousBesovSpace F φ s p q :=
  ⟨u, hu.choose, hu.choose_spec⟩

@[simp]
theorem _root_.TemperedDistribution.MemHomogeneousBesov.toDistr_toHomogeneousBesovSpace
    {u : 𝓢'(E, F)} (hu : u.MemHomogeneousBesov φ s p q) :
    hu.toHomogeneousBesovSpace.toDistr = u := (rfl)

/-- The weighted blocks vanish exactly when the Fourier transform of the distribution vanishes on
`E \ {0}`. -/
theorem weightedBlocks_eq_zero_iff (u : HomogeneousBesovSpace F φ s p q) :
    u.weightedBlocks = 0 ↔ IsVanishingOn (𝓕 u.toDistr : 𝓢'(E, F)) {0}ᶜ := by
  constructor
  · intro h
    -- Every block of `u` vanishes, so the partial sums `∑_{a < j ≤ b} Pⱼ u` converge to `0`.
    have hblock : ∀ j, homogeneousLittlewoodPaleyBlock F φ j u.toDistr = 0 := fun j ↦ by
      rw [← coe_block, block, h]
      simp
    have hlim := isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock
      (u := u.toDistr) (v := 0) φ (by simp only [hblock, Finset.sum_const_zero]; exact
        tendsto_const_nhds)
    rwa [sub_zero] at hlim
  · intro h
    refine lp.ext <| funext fun j ↦
      LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      coe_weightedBlocks_apply,
      homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero φ h, smul_zero,
      lp.coeFn_zero, Pi.zero_apply, Lp.toTemperedDistribution_zero]

section Seminormed

variable [Fact (1 ≤ q)]

instance : SeminormedAddCommGroup (HomogeneousBesovSpace F φ s p q) :=
  fast_instance% SeminormedAddCommGroup.induced _ _ (weightedBlocksₗ F φ s p q)

/-- The homogeneous Besov seminorm of `u` is the `ℓ^q(ℤ, Lᵖ)` norm of its weighted blocks. -/
@[simp]
theorem norm_weightedBlocks (u : HomogeneousBesovSpace F φ s p q) :
    ‖u.weightedBlocks‖ = ‖u‖ := by rfl

instance : NormedSpace ℂ (HomogeneousBesovSpace F φ s p q) where
  norm_smul_le c u := by simp [← norm_weightedBlocks, norm_smul]

variable (F φ s p q) in
/-- The weighted homogeneous blocks `u ↦ (2^{js} Pⱼ u)_{j ∈ ℤ}`, as a linear isometry into
`ℓ^q(ℤ, Lᵖ)`: the homogeneous Besov seminorm is the seminorm induced by the weighted blocks. -/
def weightedBlocksₗᵢ :
    HomogeneousBesovSpace F φ s p q →ₗᵢ[ℂ] lp (fun _ : ℤ ↦ Lp F p (volume : Measure E)) q where
  toLinearMap := weightedBlocksₗ F φ s p q
  norm_map' := norm_weightedBlocks

@[simp]
theorem weightedBlocksₗᵢ_apply (u : HomogeneousBesovSpace F φ s p q) :
    weightedBlocksₗᵢ F φ s p q u = u.weightedBlocks := (rfl)

/-- **The single-block bound.** Each weighted block `2^{js} ‖Pⱼ u‖_p` is at most `‖u‖`. -/
theorem rpow_mul_norm_block_le (u : HomogeneousBesovSpace F φ s p q) (j : ℤ) :
    2 ^ (s * j) * ‖u.block j‖ ≤ ‖u‖ := by
  rw [← norm_weightedBlocks_apply, ← norm_weightedBlocks]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ j

/-- **The blocks depend continuously on the element:** `‖Pⱼ u‖_p ≤ 2^{-js} ‖u‖`. -/
theorem continuous_block (j : ℤ) :
    Continuous fun u : HomogeneousBesovSpace F φ s p q ↦ u.block j := by
  refine AddMonoidHomClass.continuous_of_bound
    (AddMonoidHom.mk' (fun u : HomogeneousBesovSpace F φ s p q ↦ u.block j)
      fun u v ↦ block_add u v j) ((2 : ℝ) ^ (s * j))⁻¹ fun u ↦ ?_
  rw [AddMonoidHom.mk'_apply, inv_mul_eq_div, le_div_iff₀' (by positivity)]
  exact rpow_mul_norm_block_le u j

/-- For `q < ∞`, the `q`-th power of the homogeneous Besov seminorm is the sum of the `q`-th powers
of the weighted block norms over `j ∈ ℤ`. -/
theorem norm_eq_tsum_rpow (hq : q ≠ ∞) (u : HomogeneousBesovSpace F φ s p q) :
    ‖u‖ = (∑' j : ℤ, (2 ^ (s * j) * ‖u.block j‖) ^ q.toReal) ^ (1 / q.toReal) := by
  rw [← norm_weightedBlocks, lp.norm_eq_tsum_rpow
    (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq)]
  simp_rw [norm_weightedBlocks_apply]

/-- For `q = ∞`, the homogeneous Besov seminorm is the supremum of the weighted block norms. -/
theorem norm_eq_ciSup (u : HomogeneousBesovSpace F φ s p ∞) :
    ‖u‖ = ⨆ j : ℤ, 2 ^ (s * j) * ‖u.block j‖ := by
  rw [← norm_weightedBlocks, lp.norm_eq_ciSup]
  simp_rw [norm_weightedBlocks_apply]

/-- **The null space of the homogeneous Besov seminorm.** `‖u‖ = 0` exactly when the Fourier
transform of `u` vanishes on `E \ {0}`, that is, when `u` has spectrum at the origin, as a
polynomial does. -/
theorem norm_eq_zero_iff (u : HomogeneousBesovSpace F φ s p q) :
    ‖u‖ = 0 ↔ IsVanishingOn (𝓕 u.toDistr : 𝓢'(E, F)) {0}ᶜ := by
  rw [← norm_weightedBlocks, norm_eq_zero, weightedBlocks_eq_zero_iff]

/-- **Inseparability in a homogeneous Besov space.** Two elements are at seminorm distance zero
exactly when their difference has spectrum at the origin. So the separation quotient of
`\dot B^s_{p,q}`, a normed space, is the space of these distributions modulo distributions with
spectrum at the origin. -/
theorem inseparable_iff (u v : HomogeneousBesovSpace F φ s p q) :
    Inseparable u v ↔ IsVanishingOn (𝓕 (u.toDistr - v.toDistr) : 𝓢'(E, F)) {0}ᶜ := by
  rw [Metric.inseparable_iff, dist_eq_norm, norm_eq_zero_iff, toDistr_sub]

end Seminormed

end HomogeneousBesovSpace

end TauCeti
