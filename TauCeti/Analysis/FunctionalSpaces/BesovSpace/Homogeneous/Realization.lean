/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.VanishingAtLowFrequencies
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
import TauCeti.Analysis.Distribution.Support

/-!
# Realisation of homogeneous Besov spaces in `𝓢'_h`

The homogeneous Besov seminorm `‖·‖_{\dot B^s_{p,q}}` only sees `u` modulo spectrum at the origin.
Below the critical regularity, that is for `s < n / p`, or `s = n / p` and `q ≤ 1`, where `n` is the
dimension of `E`, the blocks of `u ∈ \dot B^s_{p,q}` sum in `𝓢'`
(`TemperedDistribution.MemHomogeneousBesov.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock`),
and their sum is the unique representative of the class of `u` in the space `𝓢'_h` of tempered
distributions vanishing at low frequencies
(`TemperedDistribution.MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies`). On the
bundled space this gives the **realisation**
`TauCeti.HomogeneousBesovSpace.realization : \dot B^s_{p,q} →ₗ[ℂ] 𝓢'(E, F)`, a linear map that
takes values in `𝓢'_h` and, for `1 ≤ q`, vanishes exactly on the null space of the seminorm.

## Main declarations

* `TemperedDistribution.MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies`: the
  unique representative in `𝓢'_h` below the critical regularity.
* `TauCeti.HomogeneousBesovSpace.realization`: the realisation as a linear map, with
  `realization_mem`, `isVanishingOn_fourier_toDistr_sub_realization`, `tendsto_sum_realization`
  and `realization_eq_zero_iff`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Definition 2.15
  and Theorem 2.25 of Section 2.3 (homogeneous Besov spaces as subspaces of `𝓢'_h`; here `𝓢'_h`
  is the weaker `𝓢'`-convergence variant, see `TemperedDistribution.vanishingAtLowFrequencies`).
-/

public section

open Filter Topology
open FourierTransform Distribution
open scoped SchwartzMap ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [CompleteSpace F]

/-- **The realisation of a homogeneous Besov class.** Let `u ∈ \dot B^s_{p,q}` with `s < n / p`, or
`s = n / p` and `q ≤ 1`, where `n` is the dimension of `E` and `1/∞ = 0`. Then there is exactly one
`v ∈ 𝓢'_h` such that `u - v` has spectrum at the origin. On the bundled space,
`TauCeti.HomogeneousBesovSpace.tendsto_sum_realization` shows that `v` is the sum `∑_{j ∈ ℤ} Pⱼ u`
of the homogeneous blocks of `u`, and
`TauCeti.HomogeneousBesovSpace.memHomogeneousBesov_realization` that `v` lies in
`\dot B^s_{p,q}`. -/
theorem MemHomogeneousBesov.existsUnique_mem_vanishingAtLowFrequencies {u : 𝓢'(E, F)}
    (hu : u.MemHomogeneousBesov φ s p q)
    (hs : s < Module.finrank ℝ E * p.toReal⁻¹ ∨ (s = Module.finrank ℝ E * p.toReal⁻¹ ∧ q ≤ 1)) :
    ∃! v : 𝓢'(E, F), v ∈ vanishingAtLowFrequencies F φ ∧
      IsVanishingOn (𝓕 (u - v) : 𝓢'(E, F)) {0}ᶜ := by
  obtain ⟨v, hlim, hv⟩ := hu.exists_tendsto_sum_homogeneousLittlewoodPaleyBlock hs
  refine ⟨v, ⟨mem_vanishingAtLowFrequencies_of_tendsto_sum φ hlim, hv⟩, fun w ⟨hw, hw'⟩ ↦ ?_⟩
  refine eq_of_mem_vanishingAtLowFrequencies φ hw
    (mem_vanishingAtLowFrequencies_of_tendsto_sum φ hlim) ?_
  rw [← sub_sub_sub_cancel_left v w u, fourier_sub]
  exact hv.sub hw'

end TemperedDistribution

namespace TauCeti.HomogeneousBesovSpace

open TemperedDistribution

variable (E) in
/-- The critical-regularity condition `s < n / p`, or `s = n / p` and `q ≤ 1`, where `n` is the
dimension of `E` and `1/∞ = 0`, under which `\dot B^s_{p,q}` is realised in `𝓢'_h`. -/
abbrev RealizationCondition (s : ℝ) (p q : ℝ≥0∞) : Prop :=
  s < Module.finrank ℝ E * p.toReal⁻¹ ∨ (s = Module.finrank ℝ E * p.toReal⁻¹ ∧ q ≤ 1)

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [CompleteSpace F]

/-- The representative in `𝓢'_h` of an element of `\dot B^s_{p,q}`, used to build
`TauCeti.HomogeneousBesovSpace.realization`. -/
private noncomputable def realizationFun (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) : 𝓢'(E, F) :=
  ((memHomogeneousBesov_toDistr u).existsUnique_mem_vanishingAtLowFrequencies hs).exists.choose

private theorem realizationFun_spec (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) :
    realizationFun hs u ∈ vanishingAtLowFrequencies F φ ∧
      IsVanishingOn (𝓕 (u.toDistr - realizationFun hs u) : 𝓢'(E, F)) {0}ᶜ :=
  ((memHomogeneousBesov_toDistr u).existsUnique_mem_vanishingAtLowFrequencies hs).exists.choose_spec

private theorem realizationFun_eq (hs : RealizationCondition E s p q)
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
      (add_mem (realizationFun_spec hs u).1 (realizationFun_spec hs v).1) ?_
    rw [toDistr_add, add_sub_add_comm, FourierAdd.fourier_add]
    exact (realizationFun_spec hs u).2.add (realizationFun_spec hs v).2
  map_smul' c u := by
    refine realizationFun_eq hs (c • u)
      (Submodule.smul_mem _ c (realizationFun_spec hs u).1) ?_
    rw [toDistr_smul, RingHom.id_apply, ← smul_sub, fourier_smul]
    exact (realizationFun_spec hs u).2.smul c

variable (hs : RealizationCondition E s p q)

/-- The realisation lies in `𝓢'_h`. -/
@[simp]
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

/-- The realisation vanishes exactly on the null space of the homogeneous Besov seminorm, so it
descends to an injective map on `SeparationQuotient (HomogeneousBesovSpace F φ s p q)`. -/
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
