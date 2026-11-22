/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Idempotent maximal ideals of valuation rings

The maximal ideal of a valuation ring is idempotent if it is not finitely generated.
Conversely, a nonzero idempotent maximal ideal cannot be finitely generated. This is the
algebraic input for almost mathematics over nondiscrete valuation rings; no rank or
completeness assumption is needed.

For a valuation ring whose fraction field is algebraically closed the maximal ideal is always
idempotent: every element of the maximal ideal is the square of an element of the maximal
ideal. A nonzero such maximal ideal is therefore not finitely generated.

All results are stated for a nontrivial commutative ring whose elements are totally ordered by
divisibility (a `PreValuationRing`); valuation domains are the main example, and no domain
assumption is needed.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.1, Example 2.1.2(i).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

open IsLocalRing

namespace TauCeti.ValuationRing

variable {V : Type*} [CommRing V] [Nontrivial V] [PreValuationRing V]

/-- The maximal ideal of a nontrivial ring whose elements are totally ordered by divisibility,
such as a valuation ring, is idempotent when it is not finitely generated. -/
theorem isIdempotentElem_maximalIdeal_of_not_fg (hfg : ¬ (maximalIdeal V).FG) :
    IsIdempotentElem (maximalIdeal V) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  -- Some `y ∈ m` is not a multiple of `x`, since otherwise `m = (x)` would be finitely generated.
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ maximalIdeal V, ¬ x ∣ y := by
    by_contra! h
    refine hfg ⟨{x}, ?_⟩
    rw [Finset.coe_singleton]
    exact le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr hx)
      fun y hy ↦ Ideal.mem_span_singleton.mpr (h y hy)
  obtain ⟨z, rfl⟩ := (_root_.ValuationRing.dvd_total x y).resolve_left hxy
  -- The cofactor `z` is not a unit, since otherwise `x = y * z` would divide `y`.
  have hz : z ∈ maximalIdeal V := by
    by_contra hz
    exact hxy ((notMem_maximalIdeal.mp hz).mul_right_dvd.mpr dvd_rfl)
  exact Ideal.mul_mem_mul hy hz

/-- A nonzero maximal ideal of a nontrivial ring whose elements are totally ordered by
divisibility, such as a valuation ring, is idempotent exactly when it is not finitely generated.
The nonzero assumption excludes the maximal ideal of a field. -/
theorem isIdempotentElem_maximalIdeal_iff (hne : maximalIdeal V ≠ ⊥) :
    IsIdempotentElem (maximalIdeal V) ↔ ¬ (maximalIdeal V).FG := by
  refine ⟨fun hi hfg ↦ hne ?_, isIdempotentElem_maximalIdeal_of_not_fg⟩
  -- Nakayama's lemma: a finitely generated `m` with `m = m • m` vanishes.
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ hfg (by rw [smul_eq_mul, hi.eq])
    (ringJacobson_eq_maximalIdeal V).ge

/-- The maximal ideal of a valuation ring whose fraction field `K` is algebraically closed is
idempotent, including when the valuation ring is the field itself. -/
theorem isIdempotentElem_maximalIdeal_of_isAlgClosed (K : Type*) [Field K] [Algebra V K]
    [IsFractionRing V K] [IsAlgClosed K] :
    IsIdempotentElem (maximalIdeal V) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  -- Write a square root of `x` in `K` as a quotient `a / b` of elements of `V`.
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap V K x) two_pos
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective V y
  have hb0 : algebraMap V K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := _root_.ValuationRing.dvd_total b a
  · -- If `b ∣ a`, then the square root `a / b = c` lies in `V`, and in `m` since `x` does.
    have hc : c ^ 2 = x := IsFractionRing.injective V K <| by
      rw [map_pow, ← hy, map_mul, mul_div_cancel_left₀ _ hb0]
    have hcm : c ∈ maximalIdeal V :=
      (maximalIdeal.isMaximal V).isPrime.mem_of_pow_mem 2 (hc ▸ hx)
    rw [← hc, pow_two]
    exact Ideal.mul_mem_mul hcm hcm
  · -- If `a ∣ b`, then `x * c ^ 2 = 1`, contradicting `x ∈ m`.
    rw [map_mul] at hb0 hy
    have hxc : x * c ^ 2 = 1 := IsFractionRing.injective V K <| by
      rw [map_mul, map_pow, map_one, ← hy]
      field_simp [left_ne_zero_of_mul hb0, right_ne_zero_of_mul hb0]
    exact (notMem_maximalIdeal.mpr (IsUnit.of_mul_eq_one _ hxc) hx).elim

end TauCeti.ValuationRing
