/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Topology.Maps.Proper.KernelSupport

/-!
# Properly supported amplitudes

An amplitude `a(x, y, ξ)` of order `m` on `ℝⁿ` has *proper input support*
(`TauCeti.Amplitude.HasProperInputSupport`, defined in
`TauCeti.Analysis.Pseudodifferential.Amplitude.Basic`) when `(x, y) ↦ x` is proper on the
closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`, so `y` stays in a compact set whenever `x` stays in a
compact set. This file bridges that notion to binary kernel support
(`TauCeti.HasProperOutputSupport` in `TauCeti.Topology.Maps.Proper.KernelSupport`) and defines the
symmetric notion of *proper output support* (`TauCeti.Amplitude.HasProperOutputSupport`), where
`(x, y) ↦ y` is proper (`TauCeti.HasProperInputSupport` for the underlying kernel) so `x` stays in
a compact set whenever `y` stays in a compact set. An amplitude has *proper support*
(`TauCeti.Amplitude.HasProperSupport`) when both hold.

Output-proper amplitudes preserve compact support under quantization
(`TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`), while
input-proper amplitudes map Schwartz functions to smooth functions
(`TauCeti.Amplitude.HasProperInputSupport.contDiff_quantizeAmplitudeValue`). Together, properly
supported amplitudes preserve compactly supported Schwartz functions unconditionally on the target
normed spaces (`TauCeti.Amplitude.HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue`).

## Main declarations

* `TauCeti.Amplitude.HasProperOutputSupport`, `TauCeti.Amplitude.HasProperSupport`.
* `TauCeti.Amplitude.hasProperInputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperOutputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperSupport_iff_kernel`.
* `TauCeti.Amplitude.hasProperOutputSupport_iff`.
* `TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`,
  `TauCeti.Amplitude.HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, pp. 68–72.
* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
-/

public section

noncomputable section

open Filter Function MeasureTheory Real FourierTransform Set
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

variable {n : ℕ}

namespace Amplitude

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- An amplitude `a(x, y, ξ)` has proper input support (meaning `y` stays compact over compact sets
of output positions `x`) if and only if the projection `(x, y) ↦ x` is proper on the closure of
`{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` (`TauCeti.HasProperOutputSupport`). -/
theorem hasProperInputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔
      TauCeti.HasProperOutputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  rw [Amplitude.hasProperInputSupport_iff, TauCeti.hasProperOutputSupport_iff]
  simp [funext_iff]

/-- An amplitude `a(x, y, ξ)` has **proper output support** if the second projection `(x, y) ↦ y`
is proper on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` (`TauCeti.HasProperInputSupport`).
Equivalently, for `y` in any compact set of input positions, `a(x, y, ξ)` vanishes for all `x`
outside a compact set and all `ξ` (`TauCeti.Amplitude.hasProperOutputSupport_iff`). -/
def HasProperOutputSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

/-- An amplitude `a(x, y, ξ)` is **properly supported** if it has both proper input support and
proper output support, i.e., both spatial projections from the closure of
`{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` to `ℝⁿ` are proper maps. -/
def HasProperSupport (a : Amplitude n V W m) : Prop :=
  a.HasProperInputSupport ∧ a.HasProperOutputSupport

theorem hasProperOutputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) :=
  Iff.rfl

theorem hasProperSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperSupport ↔
      TauCeti.HasProperSupport fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  rw [HasProperSupport, TauCeti.hasProperSupport_iff, hasProperInputSupport_iff_kernel,
    hasProperOutputSupport_iff_kernel, and_comm]

theorem HasProperSupport.inp {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperInputSupport := ha.1

theorem HasProperSupport.out {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperOutputSupport := ha.2

theorem hasProperSupport_iff {a : Amplitude n V W m} :
    a.HasProperSupport ↔ a.HasProperInputSupport ∧ a.HasProperOutputSupport :=
  Iff.rfl

/-- Characterization of proper output support for amplitudes: over every compact set `L` of input
positions, `a(x, y, ξ)` vanishes for `x` outside some compact set `K` and all frequencies `ξ`. -/
theorem hasProperOutputSupport_iff {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      ∀ L : Set (CoordinateSpace n), IsCompact L →
        ∃ K : Set (CoordinateSpace n), IsCompact K ∧
          ∀ x ∉ K, ∀ y ∈ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  simpa [HasProperOutputSupport, funext_iff] using
    (TauCeti.hasProperInputSupport_iff (K := fun x y ξ ↦ a.coefficient (x, y, ξ)))

private theorem slice_zero_eq :
    (fun x y ξ ↦ (0 : Amplitude n V W m).coefficient (x, y, ξ)) = 0 := by
  ext x y ξ; simp [coefficient_zero]

private theorem slice_add_eq (a b : Amplitude n V W m) :
    (fun x y ξ ↦ (a + b).coefficient (x, y, ξ)) =
      (fun x y ξ ↦ a.coefficient (x, y, ξ)) + fun x y ξ ↦ b.coefficient (x, y, ξ) := by
  ext x y ξ; simp [coefficient_add]

private theorem slice_neg_eq (a : Amplitude n V W m) :
    (fun x y ξ ↦ (-a).coefficient (x, y, ξ)) = -fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  ext x y ξ; simp [coefficient_neg]

private theorem slice_smul_eq (c : ℂ) (a : Amplitude n V W m) :
    (fun x y ξ ↦ (c • a).coefficient (x, y, ξ)) = fun x y ξ ↦ c • a.coefficient (x, y, ξ) := by
  ext x y ξ; simp [coefficient_smul]

private theorem slice_smulPositions_eq (a : Amplitude n V W m)
    (φ : CoordinateSpace n × CoordinateSpace n → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (fun x y ξ ↦ (a.smulPositions φ hφ).coefficient (x, y, ξ)) =
      fun x y ξ ↦ φ (x, y) • a.coefficient (x, y, ξ) := by
  ext x y ξ; simp [coefficient_smulPositions]

@[simp]
theorem hasProperInputSupport_zero : (0 : Amplitude n V W m).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <|
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperOutputSupport_zero

@[simp]
theorem hasProperOutputSupport_zero : (0 : Amplitude n V W m).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperInputSupport_zero

@[simp]
theorem hasProperSupport_zero : (0 : Amplitude n V W m).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨hasProperInputSupport_zero, hasProperOutputSupport_zero⟩

theorem HasProperInputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a + b).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperOutputSupport.add (hasProperInputSupport_iff_kernel.1 ha)
      (hasProperInputSupport_iff_kernel.1 hb)

theorem HasProperOutputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a + b).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperInputSupport.add (hasProperOutputSupport_iff_kernel.1 ha)
      (hasProperOutputSupport_iff_kernel.1 hb)

theorem HasProperSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a + b).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.add hb.inp, ha.out.add hb.out⟩

theorem HasProperInputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperInputSupport) :
    (-a).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperOutputSupport.neg (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperOutputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    (-a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperInputSupport.neg (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperSupport.neg {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    (-a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.neg, ha.out.neg⟩

theorem HasProperInputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a - b).HasProperInputSupport := ha.add hb.neg

theorem HasProperOutputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a - b).HasProperOutputSupport := ha.add hb.neg

theorem HasProperSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a - b).HasProperSupport := ha.add hb.neg

theorem HasProperInputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperInputSupport)
    (c : ℂ) : (c • a).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smul_eq c a).symm ▸
    TauCeti.HasProperOutputSupport.smul_left (fun _ _ ↦ c) (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperOutputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (c : ℂ) : (c • a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smul_eq c a).symm ▸
    TauCeti.HasProperInputSupport.smul_left (fun _ _ ↦ c) (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperSupport.smul {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (c : ℂ) : (c • a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.smul c, ha.out.smul c⟩

private theorem tsupport_deriv_slice_subset {m' : ℝ} {a : Amplitude n V W m}
    {da : Amplitude n V W m'} {d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n}
    (hda : da.coefficient = iteratedFDerivAlong ℝ [d] a.coefficient) :
    tsupport (uncurry fun x y ξ ↦ da.coefficient (x, y, ξ)) ⊆
      tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ)) := by
  rw [hda]
  refine closure_minimal (fun ⟨x, y⟩ hxy ↦ by_contra fun hnot ↦ mem_support.1 hxy ?_)
    (isClosed_tsupport _)
  funext ξ
  exact Amplitude.iteratedFDerivAlong_eq_zero_of_notMem (isClosed_tsupport _)
    (fun x' y' hp ↦ congrFun (image_eq_zero_of_notMem_tsupport hp)) [d] hnot

theorem HasProperOutputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperOutputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_spatialDerivFst_eq_iteratedFDerivAlong j a))

theorem HasProperOutputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperOutputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_spatialDerivSnd_eq_iteratedFDerivAlong j a))

theorem HasProperOutputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperOutputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_frequencyDeriv_eq_iteratedFDerivAlong j a))

theorem HasProperSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivFst j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.spatialDerivFst j, ha.out.spatialDerivFst j⟩

theorem HasProperSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.spatialDerivSnd j, ha.out.spatialDerivSnd j⟩

theorem HasProperSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (frequencyDeriv j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.frequencyDeriv j, ha.out.frequencyDeriv j⟩

/-- Multiplying any amplitude by a spatial cutoff `φ(x, y)` with `TauCeti.HasProperOutputSupport`
yields an amplitude with proper input support. -/
theorem hasProperInputSupport_smulPositions_of_cutoff (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_out : TauCeti.HasProperOutputSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    hφ_out.smul_right _

/-- Multiplying any amplitude by a spatial cutoff `φ(x, y)` with `TauCeti.HasProperInputSupport`
yields an amplitude with proper output support. -/
theorem hasProperOutputSupport_smulPositions_of_cutoff (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_in : TauCeti.HasProperInputSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    hφ_in.smul_right _

/-- Multiplying any amplitude by a properly supported spatial cutoff `φ(x, y)` yields a properly
supported amplitude. -/
theorem hasProperSupport_smulPositions_of_cutoff (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_prop : TauCeti.HasProperSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨a.hasProperInputSupport_smulPositions_of_cutoff hφ hφ_prop.out,
    a.hasProperOutputSupport_smulPositions_of_cutoff hφ hφ_prop.inp⟩

theorem HasProperOutputSupport.smulPositions {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (φ : CoordinateSpace n × CoordinateSpace n → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (a.smulPositions φ hφ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    TauCeti.HasProperInputSupport.smul_left (fun x y ↦ φ (x, y))
      (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperSupport.smulPositions {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (φ : CoordinateSpace n × CoordinateSpace n → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (a.smulPositions φ hφ).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.inp.smulPositions hφ, ha.out.smulPositions φ hφ⟩

/-- **Proper output support preserves compact support under amplitude quantization.** If `a` has
proper output support and `u : 𝓢(ℝⁿ, V)` has compact support, then `Op(a) u` has compact
support. -/
theorem HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    HasCompactSupport (quantizeAmplitudeValue a.coefficient u) := by
  obtain ⟨C, hC, hCa⟩ :=
    (hasProperOutputSupport_iff.mp ha) (tsupport (u : CoordinateSpace n → V)) hu
  refine HasCompactSupport.intro hC fun x hx ↦ ?_
  rw [quantizeAmplitudeValue_def]
  have hzero : ∀ ζ, (fun y ↦ a.coefficient (x, y, (2 * π) • ζ) (u y)) = 0 :=
    fun ζ ↦ funext fun y ↦ by
      by_cases hy : y ∈ tsupport (u : CoordinateSpace n → V)
      · simp [hCa x hx y hy ((2 * π) • ζ)]
      · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero, Real.fourier_eq]

/-- **Properly supported amplitudes preserve `C_c^∞` inside Schwartz space.** Unconditional on
completeness of `V` and `W`: if `a` is properly supported and `u : 𝓢(ℝⁿ, V)` has compact support,
then `Op(a) u` is the underlying function of a compactly supported Schwartz map `v : 𝓢(ℝⁿ, W)`, so
properly supported amplitude operators can be composed directly without spatial cutoffs. -/
theorem HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    ∃ v : 𝓢(CoordinateSpace n, W),
      (v : CoordinateSpace n → W) = quantizeAmplitudeValue a.coefficient u ∧
      HasCompactSupport (v : CoordinateSpace n → W) := by
  have hsupp := ha.out.hasCompactSupport_quantizeAmplitudeValue hu
  have hsmooth := ha.inp.contDiff_quantizeAmplitudeValue u
  have hv : ((hsupp.toSchwartzMap hsmooth : 𝓢(CoordinateSpace n, W)) : CoordinateSpace n → W) =
      quantizeAmplitudeValue a.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth)
  exact ⟨hsupp.toSchwartzMap hsmooth, hv, hv.symm ▸ hsupp⟩

end Amplitude

end TauCeti
