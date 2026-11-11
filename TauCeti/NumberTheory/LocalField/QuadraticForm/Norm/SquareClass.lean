/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Uniformizer
public import TauCeti.NumberTheory.LocalField.Squares
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Set.Card

/-!
# Square classes in the uniformizer norm family

Let `K` be a nonarchimedean local field of characteristic different from two.
For an irreducible `π` in the ring of integers, the unit norms from `K(√π)` have the
form `u² (1 - π t²)`. Two parameters `s, t` give the same square class precisely when
they are congruent modulo `(2)`, or equivalently modulo the `v_K(2)`-th power of the
maximal ideal. This separates the parameters in the finite residue quotient used to
count the unit norm classes, including in residue characteristic two.
`ncard_range_uniformizerNormSquareClass` computes their number as `q ^ v_K(2)`, and
`mem_range_uniformizerNormSquareClass_iff` identifies the counted range with unit norms.

The proof uses the sharp local square theorem and the obstruction to a square differing
from one to odd order below `2 v_K(2)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The values `1 - π t²` of the uniformizer norm family have valuation one. -/
theorem valuation_one_sub_uniformizer_mul_sq {π : 𝒪[K]} (hπ : Irreducible π)
    (t : 𝒪[K]) : valuation K (1 - (π : K) * (t : K) ^ 2) = 1 := by
  apply (valuation K).map_one_sub_of_lt
  rw [map_mul, map_pow]
  exact (mul_le_mul' le_rfl (pow_le_one₀ zero_le t.2)).trans_lt
    (by simpa using Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A value of the uniformizer norm family is nonzero. -/
theorem one_sub_uniformizer_mul_sq_ne_zero {π : 𝒪[K]} (hπ : Irreducible π) (t : 𝒪[K]) :
    1 - (π : K) * (t : K) ^ 2 ≠ 0 := by
  intro h
  have hv := valuation_one_sub_uniformizer_mul_sq hπ t
  rw [h, map_zero] at hv
  exact zero_ne_one hv

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem valuation_normFamily_div_sub_one {π : 𝒪[K]} (hπ : Irreducible π)
    (s t : 𝒪[K]) :
    valuation K ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2) - 1) =
      valuation K (π : K) * valuation K ((t : K) - s) * valuation K ((t : K) + s) := by
  have hid : (1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2) - 1 =
      -(π : K) * ((t : K) - s) * ((t : K) + s) /
        (1 - (π : K) * (s : K) ^ 2) := by
    rw [div_sub_one (one_sub_uniformizer_mul_sq_ne_zero hπ s)]
    congr 1
    ring
  rw [hid, map_div₀, map_mul, map_mul, Valuation.map_neg,
    valuation_one_sub_uniformizer_mul_sq hπ s, div_one]

/-- A square quotient in the uniformizer norm family forces the parameters to be congruent
modulo depth `v_K(2)`: below that depth the quotient differs from one to an odd order. -/
private theorem valuation_sub_le_two_of_isSquare_div (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) (s t : 𝒪[K])
    (hv2 : valuation K (2 : K) = valuation K (π : K) ^ natCastValuation K 2 h2)
    (htwo : valuation K (2 * (s : K)) ≤ valuation K (2 : K)) :
    IsSquare ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2)) →
      valuation K ((t : K) - s) ≤ valuation K (2 : K) := by
  have hπlt := Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  have hid : (t : K) + s = ((t : K) - s) + 2 * s := by ring
  intro hsq
  by_contra hle
  have hlt : valuation K (2 : K) < valuation K ((t : K) - s) := lt_of_not_ge hle
  have hdiff0 : (t : K) - s ≠ 0 := by
    intro h
    simp [h] at hlt
  -- The DVR factorization gives the nonnegative order of the parameter difference.
  obtain ⟨k, u, hu⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := t - s)
    (sub_ne_zero.mpr (fun h => hdiff0 (by rw [h, sub_self]))) hπ
  have hxv : valuation K ((t : K) - s) = valuation K (π : K) ^ k := by
    have hvu := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
    simp only [Algebra.algebraMap_ofSubsemiring_apply] at hvu
    rw [← AddSubgroupClass.coe_sub, hu, Subring.coe_mul, Subring.coe_pow, map_mul, hvu, one_mul,
      map_pow]
  have hk : k < natCastValuation K 2 h2 := by
    rw [hv2, hxv] at hlt
    exact (pow_lt_pow_iff_right_of_lt_one₀
      (Valuation.pos_iff _ |>.mpr (fun h => hπ.ne_zero (Subtype.ext h))) hπlt).mp hlt
  have hvsum : valuation K ((t : K) + s) = valuation K ((t : K) - s) := by
    rw [hid]
    exact (valuation K).map_add_eq_of_lt_left (htwo.trans_lt hlt)
  obtain ⟨ξ, hξ⟩ := hsq
  apply valuation_sq_sub_one_ne_pow_odd h2 hπ hk ξ
  have hξsq : ξ ^ 2 = (1 - (π : K) * (t : K) ^ 2) /
      (1 - (π : K) * (s : K) ^ 2) := by simpa only [sq] using hξ.symm
  rw [hξsq, valuation_normFamily_div_sub_one hπ, hvsum, hxv]
  rw [pow_succ, mul_comm 2 k, pow_mul, sq]
  ac_rfl

/-- Congruent parameters give a quotient in the square subgroup `U(K, 2 v_K(2) + 1)`. -/
private theorem isSquare_div_of_valuation_sub_le_two (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) (s t : 𝒪[K])
    (hv2 : valuation K (2 : K) = valuation K (π : K) ^ natCastValuation K 2 h2)
    (htwo : valuation K (2 * (s : K)) ≤ valuation K (2 : K)) :
    valuation K ((t : K) - s) ≤ valuation K (2 : K) →
      IsSquare ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2)) := by
  have hid : (t : K) + s = ((t : K) - s) + 2 * s := by ring
  intro hdiff
  have hsum : valuation K ((t : K) + s) ≤ valuation K (2 : K) := by
    rw [hid]
    exact ((valuation K).map_add _ _).trans (max_le hdiff htwo)
  let b : Kˣ := Units.mk0
    ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2))
    (div_ne_zero (one_sub_uniformizer_mul_sq_ne_zero hπ t)
      (one_sub_uniformizer_mul_sq_ne_zero hπ s))
  have hb : b ∈ unitFiltration K (2 * natCastValuation K 2 h2 + 1) := by
    apply (mem_unitFiltration_succ_valuation _ b π hπ).mpr
    rw [Units.val_mk0, valuation_normFamily_div_sub_one hπ, map_pow]
    calc
      valuation K (π : K) * valuation K ((t : K) - s) * valuation K ((t : K) + s) ≤
          valuation K (π : K) * valuation K (2 : K) * valuation K (2 : K) :=
        mul_le_mul' (mul_le_mul_right hdiff _) hsum
      _ = valuation K (π : K) ^ (2 * natCastValuation K 2 h2 + 1) := by
        rw [hv2, pow_succ, mul_comm 2 (natCastValuation K 2 h2), pow_mul, sq]
        ac_rfl
  obtain ⟨c, hc⟩ := unitFiltration_le_range_powMonoidHom_two h2 hb
  have hbsq : IsSquare b := ⟨c, by simpa only [powMonoidHom_apply, sq] using hc.symm⟩
  exact Units.isSquare_coe_iff.mpr hbsq

/-- Two members of the uniformizer norm family differ by a square exactly when their
parameters differ by an element of valuation at least `v_K(2)`. -/
theorem isSquare_div_one_sub_uniformizer_mul_sq_iff (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) (s t : 𝒪[K]) :
    IsSquare ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2)) ↔
      valuation K ((t : K) - s) ≤ valuation K (2 : K) := by
  have hv2 : valuation K (2 : K) = valuation K (π : K) ^ natCastValuation K 2 h2 := by
    simpa only [Nat.cast_ofNat] using valuation_natCast_eq_pow hπ 2 h2
  have htwo : valuation K (2 * (s : K)) ≤ valuation K (2 : K) := by
    simpa only [map_mul, mul_one] using
      mul_le_mul_right ((Valuation.mem_integer_iff _ _).mp s.2) (valuation K (2 : K))
  exact ⟨valuation_sub_le_two_of_isSquare_div h2 hπ s t hv2 htwo,
    isSquare_div_of_valuation_sub_le_two h2 hπ s t hv2 htwo⟩

/-- Equality of the square classes in the uniformizer norm family is congruence modulo
`𝓂[K] ^ v_K(2)`. This includes odd residue characteristic, when that quotient is trivial. -/
theorem isSquare_div_one_sub_uniformizer_mul_sq_iff_sub_mem (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) (s t : 𝒪[K]) :
    IsSquare ((1 - (π : K) * (t : K) ^ 2) / (1 - (π : K) * (s : K) ^ 2)) ↔
      t - s ∈ 𝓂[K] ^ natCastValuation K 2 h2 := by
  rw [isSquare_div_one_sub_uniformizer_mul_sq_iff h2 hπ]
  have hmem := Set.ext_iff.mp
    (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K)
      (natCastValuation K 2 h2)) (t - s)
  simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, ← valuation_natCast_eq_pow hπ 2 h2,
    Nat.cast_ofNat, AddSubgroupClass.coe_sub] using hmem.symm

/-- The square class of the unit norm `1 - π t²`, for a uniformizer `π`. -/
noncomputable def uniformizerNormSquareClass (K : Type*) [Field K] [ValuativeRel K]
    {π : 𝒪[K]} (hπ : Irreducible π) (t : 𝒪[K]) : MultiplicativeSquareClassGroup K :=
  squareClassHom (Units.mk0 (1 - (π : K) * (t : K) ^ 2)
    (one_sub_uniformizer_mul_sq_ne_zero hπ t))

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The uniformizer norm square class is computed by the native square-class quotient map. -/
theorem uniformizerNormSquareClass_def {π : 𝒪[K]} (hπ : Irreducible π) (t : 𝒪[K]) :
    uniformizerNormSquareClass K hπ t = squareClassHom
      (Units.mk0 (1 - (π : K) * (t : K) ^ 2)
        (one_sub_uniformizer_mul_sq_ne_zero hπ t)) := (rfl)

/-- The parameter of a uniformizer norm square class is determined modulo `𝓂[K] ^ v_K(2)`. -/
@[simp]
theorem uniformizerNormSquareClass_eq_iff (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) (s t : 𝒪[K]) :
    uniformizerNormSquareClass K hπ t = uniformizerNormSquareClass K hπ s ↔
      t - s ∈ 𝓂[K] ^ natCastValuation K 2 h2 := by
  rw [uniformizerNormSquareClass_def, uniformizerNormSquareClass_def,
    squareClassHom_apply, squareClassHom_apply, QuotientGroup.eq_iff_div_mem,
    Subgroup.mem_square, ← Units.isSquare_coe_iff]
  simpa only [Units.val_div_eq_div_val, Units.val_mk0] using
    isSquare_div_one_sub_uniformizer_mul_sq_iff_sub_mem h2 hπ s t

/-- The range of the uniformizer norm family consists exactly of the square classes of
unit norms. The norm condition uses the quadratic algebra with radicand `π`. -/
theorem mem_range_uniformizerNormSquareClass_iff {π : 𝒪[K]} (hπ : Irreducible π)
    (c : MultiplicativeSquareClassGroup K) :
    c ∈ Set.range (uniformizerNormSquareClass K hπ) ↔
      ∃ b : Kˣ, valuation K (b : K) = 1 ∧
        b ∈ quadraticNormSubgroup (π : K) ∧ squareClassHom b = c := by
  let a := Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))
  have ha : IsUniformizer K a :=
    (isUniformizer_def a).mpr (normalizedValuation_irreducible hπ)
  constructor
  · rintro ⟨t, rfl⟩
    let b := Units.mk0 (1 - (π : K) * (t : K) ^ 2)
      (one_sub_uniformizer_mul_sq_ne_zero hπ t)
    have hbv : valuation K (b : K) = 1 := valuation_one_sub_uniformizer_mul_sq hπ t
    refine ⟨b, hbv, ?_, (uniformizerNormSquareClass_def hπ t).symm⟩
    exact (mem_quadraticNormSubgroup_iff_of_isUniformizer ha hbv).mpr
      ⟨1, t, by simp only [b, a, Units.val_one, Subring.coe_one, one_pow, one_mul,
        Units.val_mk0]⟩
  · rintro ⟨b, hbv, hbn, rfl⟩
    obtain ⟨u, t, hbt⟩ := (mem_quadraticNormSubgroup_iff_of_isUniformizer ha hbv).mp hbn
    let v := Units.map (algebraMap 𝒪[K] K).toMonoidHom u
    let n := Units.mk0 (1 - (π : K) * (t : K) ^ 2)
      (one_sub_uniformizer_mul_sq_ne_zero hπ t)
    have hb : b = v ^ 2 * n := by
      apply Units.ext
      simpa only [v, n, a, RingHom.toMonoidHom_eq_coe, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.coe_map, MonoidHom.coe_ofClass, Algebra.algebraMap_ofSubsemiring_apply,
        Units.val_mk0] using hbt
    have hv : squareClassHom (v ^ 2) = 1 :=
      (squareClassHom_eq_one_iff _).mpr ⟨v, pow_two v⟩
    refine ⟨t, ?_⟩
    rw [uniformizerNormSquareClass_def, hb, map_mul, hv, one_mul]

/-- The uniformizer norm family meets exactly `q ^ v_K(2)` square classes, where `q` is
the residue-field cardinality. -/
theorem ncard_range_uniformizerNormSquareClass (h2 : (2 : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) :
    (Set.range (uniformizerNormSquareClass K hπ)).ncard =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  classical
  let I := 𝓂[K] ^ natCastValuation K 2 h2
  let q := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let r := Function.surjInv hq
  have hqr (x : 𝒪[K] ⧸ I) : q (r x) = x := Function.surjInv_eq hq x
  let f := uniformizerNormSquareClass K hπ
  have hf (s t : 𝒪[K]) : f t = f s ↔ q t = q s :=
    (uniformizerNormSquareClass_eq_iff h2 hπ s t).trans
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem t s).symm
  have hinj : Function.Injective (f ∘ r) := by
    intro x y h
    have heq := (hf (r y) (r x)).mp h
    simpa only [hqr] using heq
  have hrange : Set.range (f ∘ r) = Set.range f := by
    apply Set.Subset.antisymm (Set.range_comp_subset_range r f)
    rintro _ ⟨t, rfl⟩
    exact ⟨q t, (hf t (r (q t))).mpr (hqr (q t))⟩
  rw [← hrange, Set.ncard_range_of_injective hinj]
  exact IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow _

end TauCeti
