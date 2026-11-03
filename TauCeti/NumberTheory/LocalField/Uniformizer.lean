/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation
import TauCeti.RingTheory.Subring.SpanSingleton

/-!
# Uniformizers of a nonarchimedean local field

This file records the uniformizer predicate for a nonarchimedean local field.  It is formulated
on `Kˣ`, where the normalized valuation is defined.  The characterization below connects it with
the irreducible elements of the ring of integers, the convention used by the local-fields
infrastructure.

An element of `𝒪[K]` with the valuation of an irreducible element is itself irreducible
(`TauCeti.irreducible_of_valuation_eq`).

The last two results only need `𝒪[K]` to be a discrete valuation ring. They recognise
uniformizers without choosing one: an element of `𝒪[K]` has valuation at least that of every
element of valuation below `1` exactly when it does not lie in `𝓂[K] ^ 2`
(`TauCeti.forall_valuation_le_iff_notMem_maximalIdeal_sq`); for an element of `𝓂[K]` this says it
has the valuation of a uniformizer. For an irreducible `ϖ`, the image in `K` of `𝓂[K] ^ k` is the
scaled copy `ϖ ^ k • 𝒪[K]` (`TauCeti.image_maximalIdeal_pow_eq_smul`).
-/

public section
noncomputable section

open Set
open scoped WithZero Pointwise
open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

/-- An element of `𝒪[K]` with the valuation of an irreducible element is irreducible. -/
theorem irreducible_of_valuation_eq {ϖ c : 𝒪[K]} (hϖ : Irreducible ϖ)
    (h : valuation K (c : K) = valuation K (ϖ : K)) : Irreducible c :=
  have hv := Valuation.integer.integers (valuation K)
  (associated_of_dvd_dvd (hv.dvd_iff_le.2 h.le) (hv.dvd_iff_le.2 h.ge)).irreducible hϖ

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
    have hd : valuation K d ≤ 1 := (Valuation.mem_integer_iff _ _).1 d.2
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

/-- For a uniformizer `ϖ`, the image in `K` of the power `𝓂[K] ^ k` of the maximal ideal is the
scaled copy `ϖ ^ k • 𝒪[K]`. -/
theorem image_maximalIdeal_pow_eq_smul {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (k : ℕ) :
    ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) = (ϖ : K) ^ k • (𝒪[K] : Set K) := by
  rw [hϖ.maximalIdeal_eq, Subring.coe_span_singleton_pow _ ϖ.2, image_preimage_eq_inter_range,
    Subtype.range_coe, inter_eq_left]
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (pow_mem ϖ.2 k) hy

end DiscreteValuationRing

end TauCeti
