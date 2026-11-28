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

An amplitude `a(x, y, ξ)` of order `m` on `ℝⁿ` has *proper input support*
(`TauCeti.Amplitude.HasProperInputSupport`, defined in
`TauCeti.Analysis.Pseudodifferential.Amplitude.Basic`) when for every compact set `K` of output
positions `x`, there is a compact set `L` of input positions `y` such that `a(x, y, ξ) = 0` for
all `x ∈ K`, `y ∉ L`, and `ξ`. Symmetrically, this file defines *proper output support*
(`TauCeti.Amplitude.HasProperOutputSupport`): for every compact set `L` of input positions `y`,
there is a compact set `K` of output positions `x` such that `a(x, y, ξ) = 0` for all `x ∉ K`,
`y ∈ L`, and `ξ`. An amplitude has *proper support* (`TauCeti.Amplitude.HasProperSupport`) when
both hold.

On `ℝⁿ`, these compact-vanishing conditions are equivalent to the kernel-level proper-map
conditions (`TauCeti.HasProperInputSupport`, `TauCeti.HasProperOutputSupport`,
`TauCeti.HasProperSupport` in `TauCeti.Topology.Maps.Proper.KernelSupport`) for the spatial slice
kernel `(x, y) ↦ fun ξ ↦ a.coefficient (x, y, ξ)`, as proved by
`TauCeti.Amplitude.hasProperInputSupport_iff_kernel`,
`TauCeti.Amplitude.hasProperOutputSupport_iff_kernel`, and
`TauCeti.Amplitude.hasProperSupport_iff_kernel`.

Output-proper amplitudes preserve compact support under quantization
(`TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`). Combining
this with `TauCeti.Amplitude.HasProperInputSupport.contDiff_quantizeAmplitudeValue` from
`TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol`, properly supported amplitudes preserve
compactly supported Schwartz functions unconditionally on the target normed spaces
(`TauCeti.Analysis.Pseudodifferential.Amplitude.SchwartzMapping`).

## Main declarations

* `TauCeti.Amplitude.HasProperOutputSupport`, `TauCeti.Amplitude.HasProperSupport`.
* `TauCeti.Amplitude.hasProperOutputSupport_iff`, `TauCeti.Amplitude.hasProperSupport_iff`.
* `TauCeti.Amplitude.hasProperInputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperOutputSupport_iff_kernel`,
  `TauCeti.Amplitude.hasProperSupport_iff_kernel`.
* `TauCeti.Amplitude.hasProperOutputSupport_of_lt_dist`,
  `TauCeti.Amplitude.hasProperSupport_of_lt_dist`.
* `TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`.

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

/-- An amplitude `a(x, y, ξ)` has proper input support (meaning that for every compact set `K` of
output positions, `a(x, y, ξ)` vanishes for `x ∈ K`, `y` outside some compact set `L`, and all
frequencies `ξ`) if and only if its spatial slice kernel `(x, y) ↦ fun ξ ↦ a.coefficient (x, y, ξ)`
has `TauCeti.HasProperInputSupport` (proper first projection on its closed support). -/
theorem hasProperInputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔
      TauCeti.HasProperInputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  rw [Amplitude.hasProperInputSupport_iff, TauCeti.hasProperInputSupport_iff]
  simp [funext_iff]

/-- An amplitude `a(x, y, ξ)` has **proper output support** if, for input positions in any compact
set, it vanishes at all output positions outside some compact set: equivalently, the second
projection `(x, y) ↦ y` on the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}` is proper
(`TauCeti.Amplitude.hasProperOutputSupport_iff_kernel`). -/
def HasProperOutputSupport (a : Amplitude n V W m) : Prop :=
  ∀ L : Set (CoordinateSpace n), IsCompact L → ∃ K : Set (CoordinateSpace n), IsCompact K ∧
    ∀ x ∉ K, ∀ y ∈ L, ∀ ξ, a.coefficient (x, y, ξ) = 0

/-- Characterization of proper output support for amplitudes: over every compact set `L` of input
positions, `a(x, y, ξ)` vanishes for `x` outside some compact set `K` and all frequencies `ξ`. -/
theorem hasProperOutputSupport_iff {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      ∀ L : Set (CoordinateSpace n), IsCompact L →
        ∃ K : Set (CoordinateSpace n), IsCompact K ∧
          ∀ x ∉ K, ∀ y ∈ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 :=
  Iff.rfl

/-- An amplitude `a(x, y, ξ)` has proper output support (the compact-set vanishing property) if and
only if its spatial slice kernel `(x, y) ↦ fun ξ ↦ a.coefficient (x, y, ξ)` has
`TauCeti.HasProperOutputSupport` (proper second projection on its closed support). -/
theorem hasProperOutputSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperOutputSupport ↔
      TauCeti.HasProperOutputSupport fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  rw [Amplitude.hasProperOutputSupport_iff, TauCeti.hasProperOutputSupport_iff]
  simp [funext_iff]

/-- An amplitude `a(x, y, ξ)` is **properly supported** if it has both proper input support and
proper output support. -/
def HasProperSupport (a : Amplitude n V W m) : Prop :=
  a.HasProperInputSupport ∧ a.HasProperOutputSupport

theorem HasProperSupport.hasProperInputSupport {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperInputSupport := ha.1

theorem HasProperSupport.hasProperOutputSupport {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    a.HasProperOutputSupport := ha.2

theorem hasProperSupport_iff {a : Amplitude n V W m} :
    a.HasProperSupport ↔ a.HasProperInputSupport ∧ a.HasProperOutputSupport :=
  Iff.rfl

/-- An amplitude `a(x, y, ξ)` is properly supported if and only if its spatial slice kernel has
`TauCeti.HasProperSupport` (both spatial projections `(x, y) ↦ x` and `(x, y) ↦ y` are proper on
the closure of `{(x, y) | ∃ ξ, a(x, y, ξ) ≠ 0}`). -/
theorem hasProperSupport_iff_kernel {a : Amplitude n V W m} :
    a.HasProperSupport ↔
      TauCeti.HasProperSupport fun x y ξ ↦ a.coefficient (x, y, ξ) := by
  rw [HasProperSupport, TauCeti.hasProperSupport_iff, hasProperInputSupport_iff_kernel,
    hasProperOutputSupport_iff_kernel]

@[simp]
theorem hasProperInputSupport_inclusion_iff {m' : ℝ} (h : m ≤ m') (a : Amplitude n V W m) :
    (inclusion h a).HasProperInputSupport ↔ a.HasProperInputSupport := by
  simp only [hasProperInputSupport_iff, coefficient_inclusion]

@[simp]
theorem hasProperOutputSupport_inclusion_iff {m' : ℝ} (h : m ≤ m') (a : Amplitude n V W m) :
    (inclusion h a).HasProperOutputSupport ↔ a.HasProperOutputSupport := by
  simp only [hasProperOutputSupport_iff, coefficient_inclusion]

@[simp]
theorem hasProperSupport_inclusion_iff {m' : ℝ} (h : m ≤ m') (a : Amplitude n V W m) :
    (inclusion h a).HasProperSupport ↔ a.HasProperSupport := by
  simp only [hasProperSupport_iff, hasProperInputSupport_inclusion_iff,
    hasProperOutputSupport_inclusion_iff]

/-- An amplitude vanishing at all pairs of positions at distance more than `R` has proper output
support. -/
theorem hasProperOutputSupport_of_lt_dist {a : Amplitude n V W m} {R : ℝ}
    (ha : ∀ x y ξ, R < dist x y → a.coefficient (x, y, ξ) = 0) : a.HasProperOutputSupport :=
  fun L hL ↦ ⟨Metric.cthickening R L, hL.cthickening, fun x hx y hy ξ ↦
    ha x y ξ (lt_of_not_ge fun h ↦ hx (Metric.mem_cthickening_of_dist_le x y R L hy h))⟩

/-- An amplitude vanishing at all pairs of positions at distance more than `R` is properly
supported. -/
theorem hasProperSupport_of_lt_dist {a : Amplitude n V W m} {R : ℝ}
    (ha : ∀ x y ξ, R < dist x y → a.coefficient (x, y, ξ) = 0) : a.HasProperSupport :=
  hasProperSupport_iff.mpr
    ⟨hasProperInputSupport_of_lt_dist ha, hasProperOutputSupport_of_lt_dist ha⟩

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
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperInputSupport_zero

@[simp]
theorem hasProperOutputSupport_zero : (0 : Amplitude n V W m).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (slice_zero_eq (n := n) (V := V) (W := W) (m := m)).symm ▸ TauCeti.hasProperOutputSupport_zero

@[simp]
theorem hasProperSupport_zero : (0 : Amplitude n V W m).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨hasProperInputSupport_zero, hasProperOutputSupport_zero⟩

theorem HasProperInputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (hb : b.HasProperInputSupport) :
    (a + b).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperInputSupport.add (hasProperInputSupport_iff_kernel.1 ha)
      (hasProperInputSupport_iff_kernel.1 hb)

theorem HasProperOutputSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (hb : b.HasProperOutputSupport) :
    (a + b).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_add_eq a b).symm ▸
    TauCeti.HasProperOutputSupport.add (hasProperOutputSupport_iff_kernel.1 ha)
      (hasProperOutputSupport_iff_kernel.1 hb)

theorem HasProperSupport.add {a b : Amplitude n V W m}
    (ha : a.HasProperSupport) (hb : b.HasProperSupport) :
    (a + b).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.add hb.hasProperInputSupport,
    ha.hasProperOutputSupport.add hb.hasProperOutputSupport⟩

theorem HasProperInputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperInputSupport) :
    (-a).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperInputSupport.neg (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperOutputSupport.neg {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) :
    (-a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_neg_eq a).symm ▸
    TauCeti.HasProperOutputSupport.neg (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperSupport.neg {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    (-a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.neg, ha.hasProperOutputSupport.neg⟩

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
    TauCeti.HasProperInputSupport.smul_left (fun _ _ ↦ c) (hasProperInputSupport_iff_kernel.1 ha)

theorem HasProperOutputSupport.smul {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    (c : ℂ) : (c • a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smul_eq c a).symm ▸
    TauCeti.HasProperOutputSupport.smul_left (fun _ _ ↦ c) (hasProperOutputSupport_iff_kernel.1 ha)

theorem HasProperSupport.smul {a : Amplitude n V W m} (ha : a.HasProperSupport)
    (c : ℂ) : (c • a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.smul c, ha.hasProperOutputSupport.smul c⟩

private theorem tsupport_deriv_slice_subset {m' : ℝ} {a : Amplitude n V W m}
    {da : Amplitude n V W m'} {d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n}
    (hda : ∀ p, da.coefficient p = fderiv ℝ a.coefficient p d) :
    tsupport (uncurry fun x y ξ ↦ da.coefficient (x, y, ξ)) ⊆
      tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ)) := by
  let S := tsupport (uncurry fun x y ξ ↦ a.coefficient (x, y, ξ))
  let C : Set (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :=
    {p | (p.1, p.2.1) ∈ S}
  have hC : IsClosed C :=
    (isClosed_tsupport _).preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hsub : tsupport a.coefficient ⊆ C := closure_minimal
    (fun p hp ↦ subset_closure fun h ↦ hp (congrFun h p.2.2)) hC
  refine closure_minimal (fun ⟨x, y⟩ hxy ↦ by_contra fun hnot ↦ hxy (funext fun ξ ↦ ?_))
    (isClosed_tsupport _)
  simp only [uncurry_apply_pair, Pi.zero_apply, hda]
  exact image_eq_zero_of_notMem_tsupport (f := fun p ↦ fderiv ℝ a.coefficient p d)
    fun hmem ↦ hnot (hsub (tsupport_fderiv_apply_subset ℝ d hmem))

theorem HasProperOutputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (hasProperOutputSupport_iff_kernel.1 ha).of_tsupport_subset
      (tsupport_deriv_slice_subset (coefficient_spatialDerivFst j a))

theorem HasProperOutputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (hasProperOutputSupport_iff_kernel.1 ha).of_tsupport_subset
      (tsupport_deriv_slice_subset (coefficient_spatialDerivSnd j a))

theorem HasProperOutputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperOutputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <|
    (hasProperOutputSupport_iff_kernel.1 ha).of_tsupport_subset
      (tsupport_deriv_slice_subset (coefficient_frequencyDeriv j a))

theorem HasProperSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivFst j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.spatialDerivFst j,
    ha.hasProperOutputSupport.spatialDerivFst j⟩

theorem HasProperSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.spatialDerivSnd j,
    ha.hasProperOutputSupport.spatialDerivSnd j⟩

theorem HasProperSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (j : Fin n) : (frequencyDeriv j a).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.frequencyDeriv j,
    ha.hasProperOutputSupport.frequencyDeriv j⟩

/-- Multiplying any amplitude by a spatial cutoff `φ(x, y)` with `TauCeti.HasProperInputSupport`
yields an amplitude with proper input support. -/
theorem hasProperInputSupport_smulPositions_of_hasProperInputSupport (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_in : TauCeti.HasProperInputSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperInputSupport :=
  hasProperInputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    hφ_in.smul_right _

/-- Multiplying any amplitude by a spatial cutoff `φ(x, y)` with `TauCeti.HasProperOutputSupport`
yields an amplitude with proper output support. -/
theorem hasProperOutputSupport_smulPositions_of_hasProperOutputSupport (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_out : TauCeti.HasProperOutputSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    hφ_out.smul_right _

/-- Multiplying any amplitude by a properly supported spatial cutoff `φ(x, y)` yields a properly
supported amplitude. -/
theorem hasProperSupport_smulPositions_of_hasProperSupport (a : Amplitude n V W m)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ_prop : TauCeti.HasProperSupport fun x y ↦ φ (x, y)) :
    (a.smulPositions φ hφ).HasProperSupport :=
  hasProperSupport_iff.mpr
    ⟨a.hasProperInputSupport_smulPositions_of_hasProperInputSupport hφ
        hφ_prop.hasProperInputSupport,
      a.hasProperOutputSupport_smulPositions_of_hasProperOutputSupport hφ
        hφ_prop.hasProperOutputSupport⟩

/-- Multiplying by a smooth function of the positions keeps proper output support. -/
theorem HasProperOutputSupport.smulPositions {a : Amplitude n V W m} (ha : a.HasProperOutputSupport)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    (a.smulPositions φ hφ).HasProperOutputSupport :=
  hasProperOutputSupport_iff_kernel.2 <| (slice_smulPositions_eq a φ hφ).symm ▸
    TauCeti.HasProperOutputSupport.smul_left (fun x y ↦ φ (x, y))
      (hasProperOutputSupport_iff_kernel.1 ha)

/-- Multiplying by a smooth function of the positions keeps proper support. -/
theorem HasProperSupport.smulPositions {a : Amplitude n V W m} (ha : a.HasProperSupport)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    (a.smulPositions φ hφ).HasProperSupport :=
  hasProperSupport_iff.mpr ⟨ha.hasProperInputSupport.smulPositions hφ,
    ha.hasProperOutputSupport.smulPositions hφ⟩

/-- Multiplying by a smooth function `φ(x, y)` of the positions vanishing at distance more than `R`
from the diagonal gives proper output support. -/
theorem hasProperOutputSupport_smulPositions_of_lt_dist
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hR : ∀ x y, R < dist x y → φ (x, y) = 0) (a : Amplitude n V W m) :
    (a.smulPositions φ hφ).HasProperOutputSupport :=
  hasProperOutputSupport_of_lt_dist fun x y ξ h ↦ by
    rw [coefficient_smulPositions, hR x y h, zero_smul]

/-- Multiplying by a smooth function `φ(x, y)` of the positions vanishing at distance more than `R`
from the diagonal gives proper support. -/
theorem hasProperSupport_smulPositions_of_lt_dist
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hR : ∀ x y, R < dist x y → φ (x, y) = 0) (a : Amplitude n V W m) :
    (a.smulPositions φ hφ).HasProperSupport :=
  hasProperSupport_iff.mpr
    ⟨hasProperInputSupport_smulPositions_of_lt_dist hφ hR a,
      hasProperOutputSupport_smulPositions_of_lt_dist hφ hR a⟩

/-- **Proper output support preserves compact support under amplitude quantization.** If `a` has
proper output support and `u : 𝓢(ℝⁿ, V)` has compact support, then `Op(a) u` has compact
support. -/
theorem HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperOutputSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    HasCompactSupport (quantizeAmplitudeValue a.coefficient u) := by
  obtain ⟨C, hC, -, hCa⟩ := (hasProperOutputSupport_iff_kernel.1
    ha).exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport hu
  refine HasCompactSupport.intro hC fun x hx ↦ ?_
  rw [quantizeAmplitudeValue_def]
  have hzero : ∀ ζ, (fun y ↦ a.coefficient (x, y, (2 * π) • ζ) (u y)) = 0 :=
    fun ζ ↦ funext fun y ↦ (hCa x hx y).elim
      (fun h ↦ by simp [congrFun h ((2 * π) • ζ)]) (fun h ↦ by simp [h])
  simp [hzero, Real.fourier_eq]

end Amplitude

end TauCeti
