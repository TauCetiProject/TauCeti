/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.NumberTheory.LocalField.Units.Decomposition

/-!
# The valuation shells of the units of a nonarchimedean local field

Let `K` be a nonarchimedean local field with normalized valuation `v_K`, residue field of
cardinality `q` and normalized absolute value `|x| = q ^ (-v_K(x))`. For `n ∈ ℤ`, the
**valuation shell** `{x ∈ Kˣ | v_K(x) = n}` is the fibre of `v_K : Kˣ → ℤ` over `n`. The shells
partition `Kˣ`; each is the translate `ϖ ^ n 𝒪[K]ˣ` of the units of the ring of integers by a
power of a uniformizer, hence compact and open, and every left-invariant measure on `Kˣ` gives
it the mass of `𝒪[K]ˣ`. This is the decomposition along which integrals over `Kˣ`, such as
Tate's local zeta integral, become Laurent series in `q ^ (-s)`.

## Main declarations

* `TauCeti.valuationShell K n`: the shell `{x ∈ Kˣ | v_K(x) = n}`.
* `TauCeti.valuationShell_eq_preimage_mul_left`: the shell of valuation `n` is `ϖ ^ n 𝒪[K]ˣ`.
* `TauCeti.isCompact_valuationShell`, `TauCeti.isOpen_valuationShell`,
  `TauCeti.pairwise_disjoint_valuationShell`, `TauCeti.iUnion_valuationShell`: the shells form a
  partition of `Kˣ` into compact open sets.
* `TauCeti.normalizedAbsoluteValue_of_mem_valuationShell`: `|x| = q ^ (-n)` on the shell `n`.
* `TauCeti.exists_forall_valuationShell_eq_zero_of_hasCompactSupport`: a compactly supported
  function on `K` vanishes on the shells of valuation `n < -N`, for some `N`.
* `TauCeti.measure_valuationShell`: a left-invariant measure on `Kˣ` gives every shell the mass of
  `𝒪[K]ˣ`.
-/

public section
noncomputable section

open MeasureTheory ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- The **valuation shell** `{x ∈ Kˣ | v_K(x) = n}` of the units of normalized valuation `n`. -/
def valuationShell (n : ℤ) : Set Kˣ := normalizedValuation K ⁻¹' {Multiplicative.ofAdd n}

theorem mem_valuationShell {n : ℤ} {x : Kˣ} :
    x ∈ valuationShell K n ↔ (normalizedValuation K x).toAdd = n := by
  simp only [valuationShell, Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦ by rw [← h, ofAdd_toAdd]⟩

theorem isOpen_valuationShell (n : ℤ) : IsOpen (valuationShell K n) :=
  (isOpen_discrete _).preimage (continuous_normalizedValuation K)

theorem pairwise_disjoint_valuationShell :
    Pairwise (Function.onFun Disjoint (valuationShell K)) :=
  fun _ _ h ↦ Set.disjoint_left.2 fun _ hm hn ↦
    h ((mem_valuationShell.1 hm).symm.trans (mem_valuationShell.1 hn))

theorem iUnion_valuationShell : ⋃ n, valuationShell K n = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ Set.mem_iUnion.2 ⟨_, mem_valuationShell.2 rfl⟩

/-- The shell of valuation `n` is the translate `ϖ ^ n 𝒪[K]ˣ` of the units of `𝒪[K]`, for a
uniformizer `ϖ`. -/
theorem valuationShell_eq_preimage_mul_left {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) (n : ℤ) :
    valuationShell K n = (fun x ↦ ϖ ^ (-n) * x) ⁻¹' (unitFiltration K 0 : Set Kˣ) := by
  ext x
  rw [Set.mem_preimage, SetLike.mem_coe, ← ker_normalizedValuation, MonoidHom.mem_ker, map_mul,
    normalizedValuation_zpow_of_eq_ofAdd_one ((isUniformizer_def ϖ).1 hϖ), mem_valuationShell]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← ofAdd_toAdd (normalizedValuation K x), h, ← ofAdd_add, neg_add_cancel, ofAdd_zero]
  · have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_ofAdd, toAdd_one] at h'
    omega

theorem isCompact_valuationShell (n : ℤ) : IsCompact (valuationShell K n) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  rw [valuationShell_eq_preimage_mul_left hϖ]
  exact (Homeomorph.mulLeft (ϖ ^ (-n))).isCompact_preimage.2 (isCompact_unitFiltration 0)

/-- `|x| = q ^ (-n)` on the shell of valuation `n`. -/
theorem normalizedAbsoluteValue_of_mem_valuationShell {n : ℤ} {x : Kˣ}
    (hx : x ∈ valuationShell K n) :
    (normalizedAbsoluteValue K (x : K) : ℝ) = (Nat.card 𝓀[K] : ℝ) ^ (-n) := by
  rw [coe_normalizedAbsoluteValue_eq_zpow, mem_valuationShell.1 hx]

/-- The units `𝒪[K]ˣ = TauCeti.unitFiltration K 0` have normalized absolute value one. -/
theorem normalizedAbsoluteValue_of_mem_unitFiltration_zero {u : Kˣ}
    (hu : u ∈ unitFiltration K 0) : normalizedAbsoluteValue K (u : K) = 1 := by
  rw [normalizedAbsoluteValue_coe,
    (normalizedValuation_eq_one_iff u).2 ((mem_unitFiltration_zero u).1 hu), toAdd_one,
    neg_zero, zpow_zero]

/-- A compactly supported function on `K` vanishes on the shells of valuation `n < -N`, for some
`N`. -/
theorem exists_forall_valuationShell_eq_zero_of_hasCompactSupport {M : Type*} [Zero M]
    {f : K → M} (hf : HasCompactSupport f) :
    ∃ N : ℤ, ∀ n < -N, ∀ x ∈ valuationShell K n, f x = 0 := by
  obtain ⟨M, hM⟩ := hf.isCompact.bddAbove_image continuous_normalizedAbsoluteValue.continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M (one_lt_natCard_residueField (K := K) (R := ℝ))
  refine ⟨N, fun n hn x hx ↦ by_contra fun h ↦ ?_⟩
  have hle : (normalizedAbsoluteValue K (x : K) : ℝ) ≤ M := hM ⟨x, subset_tsupport _ h, rfl⟩
  rw [normalizedAbsoluteValue_of_mem_valuationShell hx] at hle
  have hlt : (Nat.card 𝓀[K] : ℝ) ^ ((N : ℤ)) < (Nat.card 𝓀[K] : ℝ) ^ (-n) :=
    zpow_lt_zpow_right₀ (one_lt_natCard_residueField (K := K)) (by omega)
  rw [zpow_natCast] at hlt
  linarith

variable [MeasurableSpace K] [BorelSpace K]

theorem measurableSet_valuationShell (n : ℤ) : MeasurableSet (valuationShell K n) :=
  (isOpen_valuationShell n).measurableSet

/-- A left-invariant measure on `Kˣ` gives every valuation shell the mass of `𝒪[K]ˣ`. -/
theorem measure_valuationShell (ν : Measure Kˣ) [ν.IsMulLeftInvariant] (n : ℤ) :
    ν (valuationShell K n) = ν (unitFiltration K 0) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  rw [valuationShell_eq_preimage_mul_left hϖ, measure_preimage_mul]

/-- A left-invariant measure on `Kˣ` gives every valuation shell the real mass of `𝒪[K]ˣ`. -/
theorem measureReal_valuationShell (ν : Measure Kˣ) [ν.IsMulLeftInvariant] (n : ℤ) :
    ν.real (valuationShell K n) = ν.real (unitFiltration K 0) := by
  rw [measureReal_def, measureReal_def, measure_valuationShell]

end TauCeti
