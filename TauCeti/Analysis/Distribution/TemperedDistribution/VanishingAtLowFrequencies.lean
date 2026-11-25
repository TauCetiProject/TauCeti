/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.HomogeneousLittlewoodPaley

/-!
# Tempered distributions vanishing at low frequencies

Let `φ : E → ℝ` be a smooth bump function and `Sₐ u = 𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` the low-pass
truncation at frequency `2^a`. The space `𝓢'_h` consists of the tempered distributions `u` with
`Sₐ u → 0` in `𝓢'` as `a → -∞` (`TemperedDistribution.vanishingAtLowFrequencies`). These are
exactly the distributions that are the sum `∑_{j ∈ ℤ} Pⱼ u` of their homogeneous Littlewood–Paley
blocks (`TemperedDistribution.tendsto_sum_homogeneousLittlewoodPaleyBlock_iff`).

This is the variant of the space `𝓢'_h` of Bahouri–Chemin–Danchin defined by convergence in `𝓢'`.
Their Definition 1.26 asks for the stronger convergence `‖θ(λD) u‖_{L^∞} → 0` as `λ → ∞` for
every test function `θ`, so their space is contained in the one defined here.

A distribution in `𝓢'_h` whose Fourier transform vanishes on `E \ {0}` is zero: all its blocks
vanish, so it is the sum of zero blocks. Hence `𝓢'_h` meets each class modulo distributions with
spectrum at the origin, such as polynomials, at most once
(`TemperedDistribution.eq_of_mem_vanishingAtLowFrequencies`). A constant function, whose
truncations are all equal to itself, does not lie in `𝓢'_h`.

## Main declarations

* `TemperedDistribution.vanishingAtLowFrequencies F φ`: the subspace `𝓢'_h`.
* `TemperedDistribution.mem_vanishingAtLowFrequencies_iff_tendsto_sum`: the elements of `𝓢'_h`
  are the sums of their homogeneous blocks.
* `TemperedDistribution.eq_zero_of_mem_vanishingAtLowFrequencies`: an element of `𝓢'_h` with
  spectrum at the origin is zero.
* `TemperedDistribution.mem_vanishingAtLowFrequencies_of_tendsto_sum`: a limit of the partial sums
  of the homogeneous blocks of a distribution lies in `𝓢'_h`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Definition 1.26
  (the space `𝓢'_h` with convergence in `L^∞`, of which the space here is the weaker `𝓢'`
  variant).
-/

public section

open Filter Topology
open FourierTransform Distribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable (F) in
/-- The space `𝓢'_h` of tempered distributions **vanishing at low frequencies**: the `u` whose
low-pass truncations `𝓕⁻ (φ (2^{-a} ·) • 𝓕 u)` tend to `0` in `𝓢'` as `a → -∞`. This is the
`𝓢'`-convergence variant of the space of Bahouri–Chemin–Danchin (Definition 1.26), who ask for
convergence in `L^∞`; it contains their space. -/
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

end TemperedDistribution
