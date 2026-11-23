/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous

/-!
# Realisation of homogeneous Besov spaces in `𝓢'_h`

Let `φ : E → ℝ` be a smooth bump function and `Sₐ u = 𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` the low-pass
truncation at frequency `2^a`. The space `𝓢'_h` consists of the tempered distributions `u` with
`Sₐ u → 0` in `𝓢'` as `a → -∞` (`TemperedDistribution.vanishingAtLowFrequencies`). These are
exactly the distributions that are the sum `∑_{j ∈ ℤ} Pⱼ u` of their homogeneous Littlewood–Paley
blocks (`TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_iff`).

A distribution in `𝓢'_h` whose Fourier transform vanishes on `E \ {0}` is zero: all its blocks
vanish, so it is the sum of zero blocks. Hence `𝓢'_h` meets each class modulo distributions with
spectrum at the origin, such as polynomials, at most once
(`TemperedDistribution.eq_of_mem_vanishingAtLowFrequencies`). A constant function, whose
truncations are all equal to itself, does not lie in `𝓢'_h`.

The homogeneous Besov seminorm `‖·‖_{\dot B^s_{p,q}}` only sees `u` modulo spectrum at the origin.
Below the critical regularity, that is for `s < n / p`, or `s = n / p` and `q ≤ 1`, where `n` is the
dimension of `E`, the blocks of `u ∈ \dot B^s_{p,q}` sum in `𝓢'`
(`TemperedDistribution.MemHomogeneousBesov.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock`),
and their sum is the unique representative of the class of `u` in `𝓢'_h`
(`TemperedDistribution.MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies`). On the
bundled space this gives the **realisation**
`TauCeti.HomogeneousBesovSpace.realization : \dot B^s_{p,q} →ₗ[ℂ] 𝓢'(E, F)`, a linear map that
vanishes exactly on the null space of the seminorm and takes values in `𝓢'_h`.

## Main declarations

* `TemperedDistribution.vanishingAtLowFrequencies F φ`: the subspace `𝓢'_h`.
* `TemperedDistribution.eq_zero_of_mem_vanishingAtLowFrequencies`: an element of `𝓢'_h` with
  spectrum at the origin is zero.
* `TemperedDistribution.mem_vanishingAtLowFrequencies_of_tendsto_sum`: a limit of the partial sums
  of the homogeneous blocks of a distribution lies in `𝓢'_h`.
* `TemperedDistribution.MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies`: the
  unique representative in `𝓢'_h` below the critical regularity.
* `TauCeti.HomogeneousBesovSpace.realization`: the realisation as a linear map, with
  `realization_mem`, `isVanishingOn_fourier_toDistr_sub_realization`, `tendsto_sum_realization`
  and `realization_eq_zero_iff`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 1.5 (the
  space `𝓢'_h`) and Definition 2.15 and Theorem 2.25 of Section 2.3 (homogeneous Besov spaces as
  subspaces of `𝓢'_h`).
-/

public section

open Filter Topology MeasureTheory
open FourierTransform Distribution
open scoped SchwartzMap ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable (F) in
/-- The space `𝓢'_h` of tempered distributions **vanishing at low frequencies**: the `u` whose
low-pass truncations `𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` tend to `0` in `𝓢'` as `a → -∞`. -/
noncomputable def vanishingAtLowFrequencies (φ : ContDiffBump (0 : E)) :
    Submodule ℂ 𝓢'(E, F) where
  carrier := {u | Tendsto
    (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) u) atBot (𝓝 0)}
  add_mem' {u v} hu hv := by
    simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hu.add hv
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using tendsto_const_nhds
  smul_mem' c u hu := by
    simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hu.const_smul c

variable (φ : ContDiffBump (0 : E))

/-- Membership in `𝓢'_h`: the low-pass truncations tend to `0` as `a → -∞`. -/
theorem mem_vanishingAtLowFrequencies_iff {u : 𝓢'(E, F)} :
    u ∈ vanishingAtLowFrequencies F φ ↔ Tendsto
      (fun a : ℤ ↦ fourierMultiplierCLM F (fun ξ ↦ (φ (((2 : ℝ) ^ a)⁻¹ • ξ) : ℂ)) u) atBot
        (𝓝 0) :=
  Iff.rfl

/-- A tempered distribution lies in `𝓢'_h` exactly when it is the sum `∑_{j ∈ ℤ} Pⱼ u` of its
homogeneous blocks, as the limit of the two-sided partial sums. -/
theorem mem_vanishingAtLowFrequencies_iff_tendsto_sum {u : 𝓢'(E, F)} :
    u ∈ vanishingAtLowFrequencies F φ ↔ Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
        (atBot ×ˢ atTop) (𝓝 u) :=
  (tendsto_sum_homogeneousLittlewoodPaleyBlock_iff φ u).symm

/-- **No spectrum at the origin in `𝓢'_h`.** An element of `𝓢'_h` whose Fourier transform
vanishes on `E \ {0}`, such as a polynomial, is zero. -/
theorem eq_zero_of_mem_vanishingAtLowFrequencies {u : 𝓢'(E, F)}
    (hu : u ∈ vanishingAtLowFrequencies F φ) (h : IsVanishingOn (𝓕 u : 𝓢'(E, F)) {0}ᶜ) :
    u = 0 := by
  have hlim := (mem_vanishingAtLowFrequencies_iff_tendsto_sum φ).1 hu
  simp only [homogeneousLittlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_zero φ h,
    Finset.sum_const_zero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Uniqueness of representatives in `𝓢'_h`.** Two elements of `𝓢'_h` that differ by a
distribution with spectrum at the origin, such as a polynomial, are equal. -/
theorem eq_of_mem_vanishingAtLowFrequencies {u v : 𝓢'(E, F)}
    (hu : u ∈ vanishingAtLowFrequencies F φ) (hv : v ∈ vanishingAtLowFrequencies F φ)
    (h : IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ) : u = v :=
  sub_eq_zero.1 (eq_zero_of_mem_vanishingAtLowFrequencies φ (sub_mem hu hv) h)

/-- **Sums of blocks lie in `𝓢'_h`.** If the two-sided partial sums `∑_{a < j ≤ b} Pⱼ u` converge
to `v`, then `v ∈ 𝓢'_h`: `v` has the same blocks as `u`, so it is the sum of its own blocks. -/
theorem mem_vanishingAtLowFrequencies_of_tendsto_sum {u v : 𝓢'(E, F)}
    (h : Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u)
        (atBot ×ˢ atTop) (𝓝 v)) :
    v ∈ vanishingAtLowFrequencies F φ := by
  have hb := homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub φ
    (isVanishingOn_fourier_sub_of_tendsto_sum_homogeneousLittlewoodPaleyBlock φ h)
  rw [mem_vanishingAtLowFrequencies_iff_tendsto_sum]
  simpa only [hb] using h

section MemHomogeneousBesov

variable {φ} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [CompleteSpace F]

/-- **The realisation of a homogeneous Besov class.** Let `u ∈ \dot B^s_{p,q}` with `s < n / p`, or
`s = n / p` and `q ≤ 1`, where `n` is the dimension of `E` and `1/∞ = 0`. Then there is exactly one
`v ∈ 𝓢'_h` such that `u - v` has spectrum at the origin. It is the sum `∑_{j ∈ ℤ} Pⱼ u` of the
homogeneous blocks of `u`, and it lies in `\dot B^s_{p,q}`. -/
theorem MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies {u : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q)
    (hs : s < Module.finrank ℝ E * p.toReal⁻¹ ∨ (s = Module.finrank ℝ E * p.toReal⁻¹ ∧ q ≤ 1)) :
    ∃! v : 𝓢'(E, F), v ∈ vanishingAtLowFrequencies F φ ∧
      IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  obtain ⟨v, hlim, hv⟩ := hu.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock hs
  refine ⟨v, ⟨mem_vanishingAtLowFrequencies_of_tendsto_sum φ hlim, hv⟩, fun w ⟨hw, hw'⟩ ↦ ?_⟩
  refine eq_of_mem_vanishingAtLowFrequencies φ hw
    (mem_vanishingAtLowFrequencies_of_tendsto_sum φ hlim) fun ψ hψ ↦ ?_
  have h₁ := hv ψ hψ
  have h₂ := hw' ψ hψ
  simp only [fourier_sub, _root_.sub_apply, sub_eq_zero] at h₁ h₂ ⊢
  exact h₂.symm.trans h₁

end MemHomogeneousBesov

end TemperedDistribution

namespace TauCeti.HomogeneousBesovSpace

open TemperedDistribution

variable (E) in
/-- The critical-regularity condition `s < n / p`, or `s = n / p` and `q ≤ 1`, where `n` is the
dimension of `E` and `1/∞ = 0`, under which `\dot B^s_{p,q}` is realised in `𝓢'_h`. -/
abbrev RealizationCondition (s : ℝ) (p q : ℝ≥0∞) : Prop :=
  s < Module.finrank ℝ E * p.toReal⁻¹ ∨ (s = Module.finrank ℝ E * p.toReal⁻¹ ∧ q ≤ 1)

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [CompleteSpace F]

/-- The representative in `𝓢'_h` of an element of `\dot B^s_{p,q}`, for an exponent satisfying
the realisation condition; see `TauCeti.HomogeneousBesovSpace.realization`. -/
noncomputable def realizationFun (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) : 𝓢'(E, F) :=
  ((memHomogeneousBesov_toDistr u).existsUnique_mem_vanishingAtLowFrequencies hs).exists.choose

/-- The representative lies in `𝓢'_h` and differs from `u` by spectrum at the origin. -/
theorem realizationFun_spec (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) :
    realizationFun hs u ∈ vanishingAtLowFrequencies F φ ∧
      IsVanishingOn (𝓕 (u.toDistr - realizationFun hs u) : 𝓢'(E, F)) {0}ᶜ :=
  ((memHomogeneousBesov_toDistr u).existsUnique_mem_vanishingAtLowFrequencies hs).exists.choose_spec

/-- Characterisation of the representative: any `v ∈ 𝓢'_h` with `u - v` of spectrum at the origin
is the representative. -/
theorem realizationFun_eq (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) {v : 𝓢'(E, F)} (hv : v ∈ vanishingAtLowFrequencies F φ)
    (h : IsVanishingOn (𝓕 (u.toDistr - v) : 𝓢'(E, F)) {0}ᶜ) : realizationFun hs u = v :=
  ((memHomogeneousBesov_toDistr u).existsUnique_mem_vanishingAtLowFrequencies hs).unique
    (realizationFun_spec hs u) ⟨hv, h⟩

/-- **The realisation of `\dot B^s_{p,q}` in `𝓢'_h`.** For `s < n / p`, or `s = n / p` and `q ≤ 1`,
each element `u` has a unique representative in `𝓢'_h` modulo distributions with spectrum at the
origin, the sum `∑_{j ∈ ℤ} Pⱼ u` of its homogeneous blocks; this is a linear map. -/
noncomputable def realization (hs : RealizationCondition E s p q) :
    HomogeneousBesovSpace F φ s p q →ₗ[ℂ] 𝓢'(E, F) where
  toFun := realizationFun hs
  map_add' u v := by
    refine realizationFun_eq hs (u + v)
      (add_mem (realizationFun_spec hs u).1 (realizationFun_spec hs v).1) fun ψ hψ ↦ ?_
    have h₁ := (realizationFun_spec hs u).2 ψ hψ
    have h₂ := (realizationFun_spec hs v).2 ψ hψ
    simp only [toDistr_add, fourier_sub, FourierAdd.fourier_add, _root_.sub_apply,
      _root_.add_apply] at h₁ h₂ ⊢
    rw [add_sub_add_comm, h₁, h₂, add_zero]
  map_smul' c u := by
    refine realizationFun_eq hs (c • u)
      (Submodule.smul_mem _ c (realizationFun_spec hs u).1) fun ψ hψ ↦ ?_
    have h := (realizationFun_spec hs u).2 ψ hψ
    simp only [toDistr_smul, fourier_sub, fourier_smul, _root_.sub_apply, _root_.smul_apply,
      RingHom.id_apply] at h ⊢
    rw [← smul_sub, h, smul_zero]

variable (hs : RealizationCondition E s p q)

/-- Unfolding `TauCeti.HomogeneousBesovSpace.realization`. -/
theorem realization_apply (u : HomogeneousBesovSpace F φ s p q) :
    realization hs u = realizationFun hs u :=
  (rfl)

/-- The realisation lies in `𝓢'_h`. -/
theorem realization_mem (u : HomogeneousBesovSpace F φ s p q) :
    realization hs u ∈ vanishingAtLowFrequencies F φ :=
  (realizationFun_spec hs u).1

/-- The realisation differs from the distribution of `u` by a distribution with spectrum at the
origin. -/
theorem isVanishingOn_fourier_toDistr_sub_realization (u : HomogeneousBesovSpace F φ s p q) :
    IsVanishingOn (𝓕 (u.toDistr - realization hs u) : 𝓢'(E, F)) {0}ᶜ :=
  (realizationFun_spec hs u).2

/-- The realisation is characterised by the two properties `realization_mem` and
`isVanishingOn_fourier_toDistr_sub_realization`. -/
theorem realization_eq_iff (u : HomogeneousBesovSpace F φ s p q) (v : 𝓢'(E, F)) :
    realization hs u = v ↔ v ∈ vanishingAtLowFrequencies F φ ∧
      IsVanishingOn (𝓕 (u.toDistr - v) : 𝓢'(E, F)) {0}ᶜ :=
  ⟨fun h ↦ h ▸ ⟨realization_mem hs u, isVanishingOn_fourier_toDistr_sub_realization hs u⟩,
    fun h ↦ realizationFun_eq hs u h.1 h.2⟩

/-- The realisation of `u` is the sum `∑_{j ∈ ℤ} Pⱼ u` of the homogeneous blocks of `u`. -/
theorem tendsto_sum_realization (u : HomogeneousBesovSpace F φ s p q) :
    Tendsto (fun ab : ℤ × ℤ ↦
      ∑ j ∈ Finset.Ioc ab.1 ab.2, homogeneousLittlewoodPaleyBlock F φ j u.toDistr)
        (atBot ×ˢ atTop) (𝓝 (realization hs u)) := by
  have hb := homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub φ
    (isVanishingOn_fourier_toDistr_sub_realization hs u)
  simpa only [hb] using
    (mem_vanishingAtLowFrequencies_iff_tendsto_sum φ).1 (realization_mem hs u)

/-- The realisation of `u` lies in `\dot B^s_{p,q}`. -/
theorem memHomogeneousBesov_realization (u : HomogeneousBesovSpace F φ s p q) :
    (realization hs u).MemHomogeneousBesov φ s p q :=
  (memHomogeneousBesov_toDistr u).of_isVanishingOn_fourier_sub
    (isVanishingOn_fourier_toDistr_sub_realization hs u)

/-- The realisation of an element of `𝓢'_h` is its distribution. -/
theorem realization_eq_toDistr (u : HomogeneousBesovSpace F φ s p q)
    (hu : u.toDistr ∈ vanishingAtLowFrequencies F φ) : realization hs u = u.toDistr :=
  (realization_eq_iff hs u _).2 ⟨hu, fun ψ _ ↦ by simp⟩

/-- The realisation vanishes exactly on the null space of the homogeneous Besov seminorm: it is
injective on the normed space `\dot B^s_{p,q}`. -/
theorem realization_eq_zero_iff [Fact (1 ≤ q)] (u : HomogeneousBesovSpace F φ s p q) :
    realization hs u = 0 ↔ ‖u‖ = 0 := by
  rw [realization_eq_iff, norm_eq_zero_iff, sub_zero]
  exact and_iff_right (zero_mem _)

/-- Two elements have the same realisation exactly when they are inseparable, at seminorm
distance zero. -/
theorem realization_eq_realization_iff [Fact (1 ≤ q)] (u v : HomogeneousBesovSpace F φ s p q) :
    realization hs u = realization hs v ↔ Inseparable u v := by
  rw [← sub_eq_zero, ← map_sub, realization_eq_zero_iff, ← dist_eq_norm,
    Metric.inseparable_iff]

end TauCeti.HomogeneousBesovSpace
