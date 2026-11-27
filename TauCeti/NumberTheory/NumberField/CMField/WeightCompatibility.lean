/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.WeightedNorm
public import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.NumberTheory.NumberField.CMField.IntegralNormOne

/-!
# Compatibility of weights and residue characters on integral norm-one points

Let `L` be a CM field over a base with one nonreal infinite place. If the torsion generator
has relative norm one, weights that are constant modulo its order give a product trivial on
integral norm-one points. The finite part is likewise trivial if the residue characters kill
roots of that order. Together these give the compatibility on global units needed to extend
the prescribed infinity type and tame part to a character of the norm-one torus.

This test is used for `New.Data.exists_char_hasWeight` in `New/Derivatives/Field/ChosenPlaces`
of lsernau/grh-lean (`72fead1`), in the classical construction of characters with prescribed
local data (Weil, *Basic Number Theory*, Chapter VII, §3).
-/

public section

namespace NumberField.IsCMField

open scoped NumberField
open NumberField.ComplexEmbedding NumberField.ComplexEmbedding.Extension

/-- For weights constant modulo the torsion order and a torsion generator of relative norm one,
the prescribed local factors are compatible on all integral norm-one units exactly when the
product of the residue factors is trivial on the generator. -/
theorem prod_infinite_place_zpow_mul_prod_residue_eq_one_iff
    {K L : Type*} [Field K] [Field L] [NumberField L] [IsCMField L] [Algebra K L]
    [Subsingleton (InfinitePlace K)] {σ : K →+* ℂ} (hσ : ¬ IsReal σ)
    {ζ : (𝓞 L)ˣ} (hζ : IsPrimitiveRoot (ζ : L) (Units.torsionOrder L))
    (hζN : Algebra.norm K (ζ : L) = 1) {weight : InfinitePlace L → ℤ} {a : ℤ}
    (hw : ∀ w, weight w ≡ a [ZMOD (Units.torsionOrder L : ℤ)])
    (S : Finset (Ideal (𝓞 L))) (ψ : ∀ I : S, (𝓞 L ⧸ (I : Ideal (𝓞 L))) →* ℂ) :
    (∀ u : (𝓞 L)ˣ, (u : L) * complexConj L (u : L) = 1 →
      (∏ w : InfinitePlace L, ((Extension.equivInfinitePlace hσ).symm w).val (u : L) ^ weight w) *
        (∏ I : S, ψ I (Ideal.Quotient.mk (I : Ideal (𝓞 L)) (u : 𝓞 L))) = 1) ↔
      (∏ I : S, ψ I (Ideal.Quotient.mk (I : Ideal (𝓞 L)) (ζ : 𝓞 L))) = 1 := by
  have : CharZero K := σ.charZero
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have harch (j : ℕ) :
      (∏ w : InfinitePlace L,
        ((Extension.equivInfinitePlace hσ).symm w).val ((ζ ^ j : (𝓞 L)ˣ) : L) ^ weight w) = 1 := by
    simp only [Units.coe_pow]
    have hp : ((ζ : L) ^ j) ^ Units.torsionOrder L = 1 := by
      rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    rw [← finprod_eq_prod_of_fintype, prod_equivInfinitePlace_symm_apply_zpow_eq_norm_zpow hσ hp hw,
      map_pow, hζN, one_pow, map_one, one_zpow]
  constructor
  · intro h
    have hζu : (ζ : L) * complexConj L (ζ : L) = 1 :=
      mul_complexConj_eq_one_of_pow_eq (Units.torsionOrder_ne_zero L) hζ.pow_eq_one (by simp)
    have ha := harch 1
    simp only [pow_one] at ha
    simpa only [ha, one_mul] using h ζ hζu
  · intro h u hu
    have hf := isOfFinOrder_iff_isIntegral_and_mul_complexConj_eq_one.mpr
      ⟨u.val.isIntegral_coe, hu⟩
    obtain ⟨k, hk, huk⟩ := hf.exists_pow_eq_one
    have ht : u ∈ Units.torsion L := by
      rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, hk, Units.coe_injective L (by simpa only [Units.coe_pow, Units.coe_one] using huk)⟩
    have hpow : (u : L) ^ Units.torsionOrder L = 1 := by
      rw [← Units.coe_pow, Units.pow_torsionOrder_eq_one L ht, Units.coe_one]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hpow
    have heq : ζ ^ j = u := Units.coe_injective L (by simpa only [Units.coe_pow] using hj)
    rw [← heq, harch, one_mul]
    simp only [_root_.Units.val_pow_eq_pow_val, map_pow, Finset.prod_pow, h, one_pow]

end NumberField.IsCMField
