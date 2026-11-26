/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.RingTheory.Valuation.Basic

/-!
# Uniformizers of a nonarchimedean local field

This file records the uniformizer predicate for a nonarchimedean local field.  It is formulated
on `Kˣ`, where the normalized valuation is defined.  The characterization below connects it with
the irreducible elements of the ring of integers, the convention used by the local-fields
infrastructure.

An element of `𝒪[K]` with the valuation of an irreducible element is itself irreducible
(`TauCeti.irreducible_of_valuation_eq`); this does not need `K` to be a local field.

The last result only needs `𝒪[K]` to be a discrete valuation ring. It recognises uniformizers
without choosing one: an element of `𝒪[K]` has valuation at least that of every element of
valuation below `1` exactly when it does not lie in `𝓂[K] ^ 2`
(`TauCeti.forall_valuation_le_iff_notMem_maximalIdeal_sq`); for an element of `𝓂[K]` this says it
has the valuation of a uniformizer.

Mathlib names that valuation without choosing an element: `ValuativeRel.uniformizer K` is the
largest value below `1`. An irreducible element of `𝒪[K]` has this valuation
(`TauCeti.valuation_eq_uniformizer_of_irreducible`), for any valued field with a discrete value
group. In a nonarchimedean local field the valuation of a unit `x` is therefore
`uniformizer K ^ v_K(x)` (`TauCeti.valuation_eq_uniformizer_zpow`), and the closed balls
`{x | valuation K x ≤ uniformizer K ^ m}`, the fractional ideals `𝓂[K] ^ m` for `m : ℤ`, form a
neighbourhood basis of `0` (`TauCeti.hasBasis_nhds_zero_valuation_le_uniformizer_zpow`). As
additive subgroups (`Valuation.leAddSubgroup`) these balls are compact
(`TauCeti.isCompact_leAddSubgroup`), and every compact subset of `K` lies in one of them
(`IsCompact.exists_subset_setOf_valuation_le_uniformizer_zpow`).
-/

public section
noncomputable section

open Set Filter
open scoped WithZero Pointwise Topology
open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

/-- An element of `𝒪[K]` with the valuation of an irreducible element is irreducible. -/
theorem irreducible_of_valuation_eq {ϖ c : 𝒪[K]} (hϖ : Irreducible ϖ)
    (h : valuation K (c : K) = valuation K (ϖ : K)) : Irreducible c :=
  have hv := Valuation.integer.integers (valuation K)
  (associated_of_dvd_dvd (hv.dvd_iff_le.2 h.le) (hv.dvd_iff_le.2 h.ge)).irreducible hϖ

/-- An irreducible element of `𝒪[K]` has valuation `ValuativeRel.uniformizer K`, the largest
value below `1`. -/
theorem valuation_eq_uniformizer_of_irreducible [IsDiscrete K] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) = uniformizer K := by
  have hv := Valuation.integer.integers (valuation K)
  refine le_antisymm (le_uniformizer_iff.2 (Valuation.integer.v_irreducible_lt_one hϖ)) ?_
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer K)
  have hy1 : valuation K y < 1 := hy ▸ uniformizer_lt_one
  let c : 𝒪[K] := ⟨y, (Valuation.mem_integer_iff _ _).2 hy1.le⟩
  rw [← hy]
  by_contra! hlt
  -- `c` divides `ϖ`, and neither factor of `ϖ = c * d` can be a unit.
  obtain ⟨d, hd⟩ := (hv.dvd_iff_le (x := c) (y := ϖ)).2 hlt.le
  rcases hϖ.isUnit_or_isUnit hd with hc | hd'
  · exact hy1.ne (hv.isUnit_iff_valuation_eq_one.1 hc)
  · have hd1 : valuation K (d : K) = 1 := hv.isUnit_iff_valuation_eq_one.1 hd'
    exact hlt.ne (by rw [hd, MulMemClass.coe_mul, map_mul, hd1, mul_one])

section LocalField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- A uniformizer is a nonzero field element whose normalized valuation is one. -/
def IsUniformizer (π : Kˣ) : Prop :=
  normalizedValuation K π = Multiplicative.ofAdd 1

@[simp]
theorem isUniformizer_def (π : Kˣ) :
    IsUniformizer (K := K) π ↔ normalizedValuation K π = Multiplicative.ofAdd 1 := by
  rfl

variable (K) in
/-- A field unit is a uniformizer iff its underlying element is the image of an irreducible
element of the ring of integers. -/
theorem isUniformizer_iff_exists_irreducible (π : Kˣ) :
    IsUniformizer (K := K) π ↔ ∃ ϖ : 𝒪[K], Irreducible ϖ ∧ (ϖ : K) = (π : K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  have hϖval : Ring.ordFrac 𝒪[K] (ϖ : K) = WithZero.exp 1 := by
    exact Ring.ordFrac_irreducible hϖ
  constructor
  · intro hπ
    have hπval : Ring.ordFrac 𝒪[K] (π : K) = WithZero.exp 1 := by
      rw [← normalizedValuationWithZero_eq_ordFrac, normalizedValuationWithZero_coe, hπ]
      simp only [WithZero.exp_eq_coe_ofAdd]
    obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := 𝒪[K]) (π : K) (ϖ : K)
      (hπval.trans hϖval.symm)
    let ϖ' : 𝒪[K] := (↑(u⁻¹) : 𝒪[K]) * ϖ
    have hϖ' : Irreducible ϖ' := by
      have huassoc : Associated ϖ ϖ' := ⟨u⁻¹, by simp [ϖ', mul_comm]⟩
      exact huassoc.irreducible hϖ
    refine ⟨ϖ', hϖ', ?_⟩
    have hu_cancel :
        ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : K) * (π : K)) = (π : K) := by
      rw [← mul_assoc]
      have hu_inv :
        ((↑(u⁻¹) : 𝒪[K]) : K) * ((u : 𝒪[K]) : K) = 1 := by
        have hu_inv' := congrArg (fun x : 𝒪[K] => (x : K)) (Units.inv_mul u)
        simpa only [Subring.coe_mul, Subring.coe_one] using hu_inv'
      rw [hu_inv, one_mul]
    dsimp only [ϖ']
    rw [Subring.coe_mul, ← hu, Units.smul_def]
    have hu_coe : algebraMap 𝒪[K] K (u : 𝒪[K]) = (u : K) := by rfl
    simpa only [Algebra.smul_def, hu_coe] using hu_cancel
  · rintro ⟨ϖ, hϖ, hϖπ⟩
    have hπϖ : π = Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)) := by
      apply Units.ext
      exact hϖπ.symm
    rw [isUniformizer_def, hπϖ, normalizedValuation_irreducible hϖ]

variable (K) in
/-- Uniformizers exist in every nonarchimedean local field. -/
theorem exists_isUniformizer : ∃ π : Kˣ, IsUniformizer (K := K) π := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  refine ⟨Units.mk0 (ϖ : K) (fun h => hϖ.ne_zero (Subtype.ext h)), ?_⟩
  exact (isUniformizer_iff_exists_irreducible K _).2 ⟨ϖ, hϖ, rfl⟩

/-- A uniformizer has valuation `ValuativeRel.uniformizer K`. -/
theorem IsUniformizer.valuation_eq {π : Kˣ} (hπ : IsUniformizer K π) :
    valuation K (π : K) = uniformizer K := by
  obtain ⟨ϖ, hϖ, h⟩ := (isUniformizer_iff_exists_irreducible K π).1 hπ
  rw [← h]
  exact valuation_eq_uniformizer_of_irreducible hϖ

/-- The valuation of a unit `x` is `uniformizer K ^ v_K(x)`, for the normalized valuation `v_K`. -/
theorem valuation_eq_uniformizer_zpow (x : Kˣ) :
    valuation K (x : K) = uniformizer K ^ (normalizedValuation K x).toAdd := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  rw [← hπ.valuation_eq]
  exact (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow hπ _ x).1 rfl

/-- A unit `x` lies in the fractional ideal `𝓂[K] ^ m`, the closed ball of radius
`uniformizer K ^ m`, exactly when `m ≤ v_K(x)`. -/
theorem valuation_le_uniformizer_zpow_iff (x : Kˣ) (m : ℤ) :
    valuation K (x : K) ≤ uniformizer K ^ m ↔ m ≤ (normalizedValuation K x).toAdd := by
  rw [valuation_eq_uniformizer_zpow, zpow_le_zpow_iff_right_of_lt_one₀ uniformizer_pos
    uniformizer_lt_one]

/-- Multiplication by a unit `b` maps the fractional ideal `𝓂[K] ^ m` onto
`𝓂[K] ^ (m + v_K(b))`. -/
theorem valuation_mul_le_uniformizer_zpow_iff (b : Kˣ) (x : K) (m : ℤ) :
    valuation K (b * x) ≤ uniformizer K ^ (m + (normalizedValuation K b).toAdd) ↔
      valuation K x ≤ uniformizer K ^ m := by
  rw [map_mul, valuation_eq_uniformizer_zpow, zpow_add₀ uniformizer_ne_zero,
    mul_comm (uniformizer K ^ m)]
  exact mul_le_mul_iff_right₀ (zpow_pos uniformizer_pos _)

variable (K) in
/-- The closed balls `{x | valuation K x ≤ uniformizer K ^ m}`, for `m : ℤ`, which are the
fractional ideals `𝓂[K] ^ m`, form a neighbourhood basis of `0`. -/
theorem hasBasis_nhds_zero_valuation_le_uniformizer_zpow :
    (𝓝 (0 : K)).HasBasis (fun _ : ℤ ↦ True)
      fun m ↦ {x | valuation K x ≤ uniformizer K ^ m} := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' K).to_hasBasis (fun γ hγ ↦ ?_) fun m _ ↦ ?_
  · -- Write `γ = valuation K y`; the ball of radius `uniformizer K ^ (v_K(y) + 1)` lies inside.
    obtain ⟨y, rfl⟩ := valuation_surjective γ
    have hy : y ≠ 0 := by simpa using hγ
    refine ⟨(normalizedValuation K (Units.mk0 y hy)).toAdd + 1, trivial,
      fun x (hx : valuation K x ≤ _) ↦ hx.trans_lt ?_⟩
    have hvy := valuation_eq_uniformizer_zpow (Units.mk0 y hy)
    rw [Units.val_mk0] at hvy
    rw [hvy]
    exact zpow_lt_zpow_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one (lt_add_one _)
  · exact ⟨uniformizer K ^ m, (zpow_pos uniformizer_pos m).ne',
      fun x (hx : valuation K x < _) ↦ hx.le⟩

variable (K) in
/-- The additive subgroup `(valuation K).leAddSubgroup γ`, the closed ball
`{x | valuation K x ≤ γ}`, is compact. -/
theorem isCompact_leAddSubgroup (γ : ValueGroupWithZero K) :
    IsCompact ((valuation K).leAddSubgroup γ : Set K) := by
  rw [Valuation.coe_leAddSubgroup]
  exact isCompact_closedBall K γ

/-- Every compact subset of `K` lies in some fractional ideal `𝓂[K] ^ n`, the closed ball
`{x | valuation K x ≤ uniformizer K ^ n}`: these balls are open, increase as `n` decreases, and
cover `K`. -/
theorem _root_.IsCompact.exists_subset_setOf_valuation_le_uniformizer_zpow {s : Set K}
    (hs : IsCompact s) : ∃ n : ℤ, s ⊆ {x | valuation K x ≤ uniformizer K ^ n} := by
  let U : ℤ → Set K := fun n ↦ (valuation K).leAddSubgroup (uniformizer K ^ n)
  have hU : Antitone U := fun i j hij ↦ SetLike.coe_subset_coe.2 <|
    (valuation K).leAddSubgroup_monotone <|
      zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hij
  have hcover : s ⊆ ⋃ n, U n := fun x _ ↦ by
    rcases eq_or_ne x 0 with rfl | hx
    · exact mem_iUnion.2 ⟨0, zero_mem ((valuation K).leAddSubgroup _)⟩
    · exact mem_iUnion.2 ⟨_, (valuation_le_uniformizer_zpow_iff (Units.mk0 x hx) _).2 le_rfl⟩
  simpa only [U, Valuation.coe_leAddSubgroup] using
    hs.elim_directed_cover U (fun n ↦ AddSubgroup.isOpen_of_mem_nhds _
      ((hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).mem_of_mem trivial)) hcover
      hU.directed_le

end LocalField

section DiscreteValuationRing

variable [IsDiscreteValuationRing 𝒪[K]]

/-- An element `c` of `𝒪[K]` has valuation at least that of every element of valuation below `1`
exactly when it does not lie in the square of the maximal ideal. For `c ∈ 𝓂[K]` this says that `c`
has the largest valuation below `1`, that of a uniformizer. -/
theorem forall_valuation_le_iff_notMem_maximalIdeal_sq {c : 𝒪[K]} :
    (∀ y : K, valuation K y < 1 → valuation K y ≤ valuation K c) ↔ c ∉ 𝓂[K] ^ 2 := by
  constructor
  · -- If `c = ϖ ^ 2 * d`, then `c` has valuation below that of the uniformizer `ϖ`.
    intro h hc2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc2
    obtain ⟨d, rfl⟩ := hc2
    have hϖ1 : valuation K ϖ < 1 := Valuation.integer.v_irreducible_lt_one hϖ
    have hϖ0 : 0 < valuation K ϖ := Valuation.integer.v_irreducible_pos hϖ
    have hd : valuation K d ≤ 1 := (Valuation.mem_integer_iff _ _).1 d.property
    have hle := h ϖ hϖ1
    rw [MulMemClass.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow] at hle
    exact (hle.trans (mul_le_of_le_one_right' hd)).not_gt (pow_lt_self_of_lt_one₀ hϖ0 hϖ1
      one_lt_two)
  · -- If `y ∈ 𝓂` had larger valuation than `c`, then `c = y * (c / y)` would lie in `𝓂 ^ 2`.
    intro hc2 y hy
    by_contra! hlt
    have hy0 : 0 < valuation K y := zero_le.trans_lt hlt
    have hz : valuation K (c / y) < 1 := by
      rwa [map_div₀, div_lt_one₀ hy0]
    refine hc2 ?_
    have hcy : c = ⟨y, (Valuation.mem_integer_iff _ _).2 hy.le⟩ *
        ⟨c / y, (Valuation.mem_integer_iff _ _).2 hz.le⟩ := by
      ext
      rw [MulMemClass.coe_mul, mul_div_cancel₀ _ ((_root_.map_ne_zero _).1 hy0.ne')]
    rw [hcy, pow_two]
    exact Ideal.mul_mem_mul ((valuation K).mem_maximalIdeal_iff.2 hy)
      ((valuation K).mem_maximalIdeal_iff.2 hz)

end DiscreteValuationRing

end TauCeti
