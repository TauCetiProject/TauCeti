/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Topology.Maps.Proper.KernelSupport

/-!
# Properly supported amplitudes

An amplitude `a(x, y, ξ)` of order `m` on `ℝⁿ` has *proper output support*
(`TauCeti.Amplitude.HasProperOutputSupport`) if `(x, y) ↦ x` is proper on the closure of
`{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`, *proper input support* (`TauCeti.Amplitude.HasProperInputSupport`)
if `(x, y) ↦ y` is proper, and *proper support* (`TauCeti.Amplitude.HasProperSupport`) if both
projections are proper.

These support conditions are stable under the amplitude module operations, differentiation in
`x`, `y`, and `ξ`, and spatial cutoff multiplication (`TauCeti.Amplitude.smulSpatial`). Cutting
off an output-proper amplitude by a compactly supported output cutoff `φ(x)` yields an amplitude
with global compact input support
(`TauCeti.Amplitude.HasProperOutputSupport.hasCompactInputSupport_smulSpatial_fst`), which is the
basis for the global left-symbol reduction (`TauCeti.Amplitude.leftSymbol` in
`TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol`) and asymptotic expansion
(`TauCeti.Analysis.Pseudodifferential.Amplitude.leftRemainder` in
`TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion`). Input-proper amplitudes preserve
compact support under quantization
(`TauCeti.Amplitude.HasProperInputSupport.hasCompactSupport_quantizeAmplitudeValue`).

## Main declarations

* `TauCeti.Amplitude.HasProperOutputSupport`, `TauCeti.Amplitude.HasProperInputSupport`,
  `TauCeti.Amplitude.HasProperSupport`.
* `TauCeti.Amplitude.hasProperOutputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperInputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperSupport_iff_kernel`.
* `TauCeti.Amplitude.hasProperOutputSupport_iff`,
  `TauCeti.Amplitude.hasProperInputSupport_iff`.
* `TauCeti.Amplitude.HasProperOutputSupport.hasCompactInputSupport_smulSpatial_fst`,
  `TauCeti.Amplitude.HasProperInputSupport.hasCompactSupport_quantizeAmplitudeValue`.

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

/-- An amplitude `a(x, y, ξ)` has **proper output support** if the first projection `(x, y) ↦ x`
is proper on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`. Equivalently, over every compact
set of output positions `x`, `a(x, y, ξ)` vanishes for all `y` outside a compact set and all `ξ`
(`TauCeti.Amplitude.hasProperOutputSupport_iff`). -/
def HasProperOutputSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperOutputSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

/-- An amplitude `a(x, y, ξ)` has **proper input support** if the second projection `(x, y) ↦ y`
is proper on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`. Equivalently, for `y` in any compact
set of input positions, `a(x, y, ξ)` vanishes for all `x` outside a compact set and all `ξ`
(`TauCeti.Amplitude.hasProperInputSupport_iff`). -/
def HasProperInputSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

/-- An amplitude `a(x, y, ξ)` is **properly supported** if both spatial projections from the
closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` to `ℝⁿ` are proper maps. -/
def HasProperSupport (a : Amplitude n V W m) : Prop :=
  TauCeti.HasProperSupport fun x y ξ ↦ a.coefficient (x, y, ξ)

theorem hasProperOutputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      TauCeti.HasProperOutputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) :=
  Iff.rfl

theorem hasProperInputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔
      TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) :=
  Iff.rfl

theorem hasProperSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperSupport ↔
      TauCeti.HasProperSupport fun x y ξ ↦ a.coefficient (x, y, ξ) :=
  Iff.rfl

theorem HasProperSupport.out {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperOutputSupport := TauCeti.HasProperSupport.out ha

theorem HasProperSupport.inp {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperInputSupport := TauCeti.HasProperSupport.inp ha

theorem hasProperSupport_iff {a : Amplitude n V W m} :
    a.HasProperSupport ↔ a.HasProperOutputSupport ∧ a.HasProperInputSupport :=
  TauCeti.hasProperSupport_iff

/-- Characterization of proper output support for amplitudes: over every compact set `K` of output
positions, `a(x, y, ξ)` vanishes for `y` outside some compact set `L` and all frequencies `ξ`. -/
theorem hasProperOutputSupport_iff {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      ∀ K : Set (CoordinateSpace n), IsCompact K →
        ∃ L : Set (CoordinateSpace n), IsCompact L ∧
          ∀ x ∈ K, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  simpa [HasProperOutputSupport, funext_iff] using
    (TauCeti.hasProperOutputSupport_iff (K := fun x y ξ ↦ a.coefficient (x, y, ξ)))

/-- Characterization of proper input support for amplitudes: over every compact set `L` of input
positions, `a(x, y, ξ)` vanishes for `x` outside some compact set `K` and all frequencies `ξ`. -/
theorem hasProperInputSupport_iff {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔
      ∀ L : Set (CoordinateSpace n), IsCompact L →
        ∃ K : Set (CoordinateSpace n), IsCompact K ∧
          ∀ x ∉ K, ∀ y ∈ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  simpa [HasProperInputSupport, funext_iff] using
    (TauCeti.hasProperInputSupport_iff (K := fun x y ξ ↦ a.coefficient (x, y, ξ)))

/-- Global compact input support implies proper output support. -/
theorem HasCompactInputSupport.hasProperOutputSupport {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) : a.HasProperOutputSupport := by
  obtain ⟨L, hL, hLa⟩ := hasCompactInputSupport_iff.mp ha
  exact hasProperOutputSupport_iff.2 fun _ _ ↦ ⟨L, hL, fun x _ y hy ξ ↦ hLa x y hy ξ⟩

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

private theorem slice_smulSpatial_eq (a : Amplitude n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (fun x y ξ ↦ (a.smulSpatial χ hχ).coefficient (x, y, ξ)) =
      fun x y ξ ↦ χ x y • a.coefficient (x, y, ξ) := by
  ext x y ξ; simp [coefficient_smulSpatial]

@[simp]
theorem hasProperOutputSupport_zero : (0 : Amplitude n V W m).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperOutputSupport_zero

@[simp]
theorem hasProperInputSupport_zero : (0 : Amplitude n V W m).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <|
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperInputSupport_zero

@[simp]
theorem hasProperSupport_zero : (0 : Amplitude n V W m).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨hasProperOutputSupport_zero, hasProperInputSupport_zero⟩

theorem HasProperOutputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a + b).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperOutputSupport.add (hasProperOutputSupport_iff_kernel.1 ha)
      (hasProperOutputSupport_iff_kernel.1 hb)

theorem HasProperInputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a + b).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperInputSupport.add (hasProperInputSupport_iff_kernel.1 ha)
      (hasProperInputSupport_iff_kernel.1 hb)

theorem HasProperSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a + b).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.add hb.out, ha.inp.add hb.inp⟩

theorem HasProperOutputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    (-a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperOutputSupport.neg (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperInputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperInputSupport) :
    (-a).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperInputSupport.neg (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperSupport.neg {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    (-a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.neg, ha.inp.neg⟩

theorem HasProperOutputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a - b).HasProperOutputSupport := ha.add hb.neg

theorem HasProperInputSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a - b).HasProperInputSupport := ha.add hb.neg

theorem HasProperSupport.sub {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a - b).HasProperSupport := ha.add hb.neg

theorem HasProperOutputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (c : ℂ) : (c • a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smul_eq c a).symm ▸
    TauCeti.HasProperOutputSupport.smul_left (fun _ _ ↦ c) (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperInputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperInputSupport)
    (c : ℂ) : (c • a).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smul_eq c a).symm ▸
    TauCeti.HasProperInputSupport.smul_left (fun _ _ ↦ c) (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperSupport.smul {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (c : ℂ) : (c • a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.smul c, ha.inp.smul c⟩

private theorem tsupport_deriv_slice_subset {m' : ℝ} {a : Amplitude n V W m}
    {da : Amplitude n V W m'} {d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n}
    (hda : da.coefficient = iteratedFDerivAlong ℝ [d] a.coefficient) :
    tsupport (uncurry fun x y ξ ↦ da.coefficient (x, y, ξ)) ⊆
      tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ)) := by
  rw [hda]
  set S := tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ))
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

theorem HasProperInputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperInputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_spatialDerivFst_eq_iteratedFDerivAlong j a))

theorem HasProperInputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperInputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_spatialDerivSnd_eq_iteratedFDerivAlong j a))

theorem HasProperInputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperInputSupport :=
  ha.of_tsupport_subset
    (tsupport_deriv_slice_subset (coefficient_frequencyDeriv_eq_iteratedFDerivAlong j a))

theorem HasProperSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivFst j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.spatialDerivFst j, ha.inp.spatialDerivFst j⟩

theorem HasProperSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.spatialDerivSnd j, ha.inp.spatialDerivSnd j⟩

theorem HasProperSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (frequencyDeriv j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.frequencyDeriv j, ha.inp.frequencyDeriv j⟩

/-- Multiplying any amplitude by a cutoff `χ` with proper output support yields an amplitude with
proper output support. -/
theorem hasProperOutputSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_out : TauCeti.HasProperOutputSupport χ) :
    (a.smulSpatial χ hχ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulSpatial_eq a χ hχ).symm ▸
    hχ_out.smul_right _

/-- Multiplying any amplitude by a cutoff `χ` with proper input support yields an amplitude with
proper input support. -/
theorem hasProperInputSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_in : TauCeti.HasProperInputSupport χ) :
    (a.smulSpatial χ hχ).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smulSpatial_eq a χ hχ).symm ▸
    hχ_in.smul_right _

/-- Multiplying any amplitude by a properly supported cutoff `χ` yields a properly supported
amplitude. -/
theorem hasProperSupport_smulSpatial_of_cutoff (a : Amplitude n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (uncurry χ))
    (hχ_prop : TauCeti.HasProperSupport χ) :
    (a.smulSpatial χ hχ).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨a.hasProperOutputSupport_smulSpatial_of_cutoff hχ hχ_prop.out,
    a.hasProperInputSupport_smulSpatial_of_cutoff hχ hχ_prop.inp⟩

theorem HasProperOutputSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulSpatial_eq a χ hχ).symm ▸
    TauCeti.HasProperOutputSupport.smul_left χ (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperInputSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperInputSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smulSpatial_eq a χ hχ).symm ▸
    TauCeti.HasProperInputSupport.smul_left χ (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperSupport.smulSpatial {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ (uncurry χ)) :
    (a.smulSpatial χ hχ).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.out.smulSpatial χ hχ, ha.inp.smulSpatial χ hχ⟩

/-- Cutting an amplitude with proper output support off in the output position by a compactly
supported smooth function `φ(x)` produces an amplitude with global compact input support. -/
theorem HasProperOutputSupport.hasCompactInputSupport_smulSpatial_fst
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ (uncurry fun x (_ : CoordinateSpace n) ↦ φ x))
    (hφ_supp : HasCompactSupport φ) :
    (a.smulSpatial (fun x _ ↦ φ x) hφ).HasCompactInputSupport := by
  obtain ⟨L, hL, hLa⟩ := (hasProperOutputSupport_iff.mp ha) (tsupport φ) hφ_supp
  refine hasCompactInputSupport_iff.mpr ⟨L, hL, fun x y hy ξ ↦ ?_⟩
  rw [coefficient_smulSpatial]
  by_cases hx : x ∈ tsupport φ
  · simp [hLa x hx y hy ξ]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **Proper input support preserves compact support under amplitude quantization.** If `a` has
proper input support and `u : 𝓢(ℝⁿ, V)` has compact support, then `Op(a) u` has compact support. -/
theorem HasProperInputSupport.hasCompactSupport_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperInputSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    HasCompactSupport (quantizeAmplitudeValue a.coefficient u) := by
  obtain ⟨C, hC, hCa⟩ := (hasProperInputSupport_iff.mp ha) (tsupport (u : CoordinateSpace n → V)) hu
  refine HasCompactSupport.intro hC fun x hx ↦ ?_
  rw [quantizeAmplitudeValue_def]
  have hzero : ∀ ζ, (fun y ↦ a.coefficient (x, y, (2 * π) • ζ) (u y)) = 0 :=
    fun ζ ↦ funext fun y ↦ by
      by_cases hy : y ∈ tsupport (u : CoordinateSpace n → V)
      · simp [hCa x hx y hy ((2 * π) • ζ)]
      · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero, Real.fourier_eq]

end Amplitude

end TauCeti
