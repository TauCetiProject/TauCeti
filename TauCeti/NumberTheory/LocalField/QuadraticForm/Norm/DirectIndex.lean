/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.UnitQuotient
import TauCeti.NumberTheory.LocalField.UnitSquareClasses

/-!
# The direct norm-index calculation for odd-valuation radicands

For a uniformizer radicand, the unit norms meet exactly `q ^ v_K(2)` square classes,
whereas all units meet `2 * q ^ v_K(2)` square classes. Since every square is a norm,
this gives index two on units. The norm of the square-root generator has valuation one,
so the unit quotient is already the full norm quotient.

Rescaling the radicand by a square gives the same result for every odd-valuation
radicand, including negative valuations. This proof uses only arithmetic in the base
field: it does not use the norm-index theorem, Hilbert-symbol bimultiplicativity, or
the square-class count of a quadratic extension.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem unitNorm_index_of_isUniformizer (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : IsUniformizer K a) :
    ((quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0)).index = 2 := by
  obtain ⟨π, hπ, hπa⟩ := (isUniformizer_iff_exists_irreducible K a).mp ha
  let U := unitFiltration K 0
  let N := (quadraticNormSubgroup (a : K)).subgroupOf U
  let f : U →* MultiplicativeSquareClassGroup K := squareClassHom.comp U.subtype
  have hf : f.range = unitSquareClasses K := by
    rw [MonoidHom.range_comp, U.range_subtype]
    have hq : (squareClassHom : Kˣ →* MultiplicativeSquareClassGroup K) =
        QuotientGroup.mk' (Subgroup.square Kˣ) := by
      ext b
      exact squareClassHom_apply b
    rw [hq]
    exact map_unitFiltration_zero_eq_unitSquareClasses K
  have hker : f.ker ≤ N := by
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hu
    rw [Subgroup.mem_subgroupOf]
    apply square_le_quadraticNormSubgroup (a : K)
    exact (squareClassHom_eq_one_iff _).mp hu
  have hrange : (N.map f : Set (MultiplicativeSquareClassGroup K)) =
      Set.range (uniformizerNormSquareClass K hπ) := by
    ext c
    rw [mem_range_uniformizerNormSquareClass_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu
      exact ⟨u, (mem_unitFiltration_zero _).mp u.property, hπa ▸ hu, rfl⟩
    · rintro ⟨b, hb, hbn, rfl⟩
      refine ⟨⟨b, (mem_unitFiltration_zero b).mpr hb⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hπa.symm ▸ hbn
  have hcard : Nat.card (N.map f) = Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
    calc
      _ = (N.map f : Set (MultiplicativeSquareClassGroup K)).ncard :=
        Nat.card_coe_set_eq _
      _ = _ := by rw [hrange]; exact ncard_range_uniformizerNormSquareClass h2 hπ
  have hindex : (N.map f).relIndex f.range = N.index := by
    simpa only [Subgroup.map_top, sup_of_le_left hker, top_sup_eq,
      Subgroup.relIndex_top_right] using Subgroup.relIndex_map_map f N ⊤
  have hcount := (N.map f).relIndex_mul_card f.range
  rw [inf_of_le_left (N.map_le_range f), hcard, hindex, hf,
    card_unitSquareClasses K h2] at hcount
  have hq : 0 < Nat.card 𝓀[K] := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hcount

/-- For a radicand of odd normalized valuation, the quadratic norm subgroup has index two. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
  have hb : IsUniformizer K (a * c ^ 2) := by
    apply (isUniformizer_def _).mpr
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd]
    omega
  have hodd : Odd (normalizedValuation K (a * c ^ 2)).toAdd := by
    rw [(isUniformizer_def _).mp hb]
    exact odd_one
  have h := unitNorm_index_of_isUniformizer h2 hb
  rw [index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent
    (defectExponent_of_odd hodd) hodd] at h
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, quadraticNormSubgroup_mul_sq] using h

end TauCeti
