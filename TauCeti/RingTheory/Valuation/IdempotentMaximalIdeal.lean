/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Idempotent maximal ideals of valuation rings

The maximal ideal of a valuation domain is idempotent if it is not finitely generated.
Conversely, a nonzero idempotent maximal ideal cannot be finitely generated. This is the
algebraic input for almost mathematics over nondiscrete valuation rings; no rank or
completeness assumption is needed.

For a valuation on an algebraically closed field the maximal ideal is always idempotent:
every element has a square root in the maximal ideal. A nontrivial valuation therefore
provides a non-finitely-generated maximal ideal.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.1, Example 2.1.2(i).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

open IsLocalRing

namespace TauCeti.ValuationRing

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- The maximal ideal of a valuation domain is idempotent when it is not finitely generated. -/
theorem isIdempotentElem_maximalIdeal_of_not_fg (hfg : ¬ (maximalIdeal V).FG) :
    IsIdempotentElem (maximalIdeal V) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  have hex : ∃ y ∈ maximalIdeal V, ¬ x ∣ y := by
    by_contra! h
    apply hfg
    have heq : maximalIdeal V = Ideal.span {x} := by
      apply le_antisymm
      · exact fun y hy ↦ Ideal.mem_span_singleton.mpr (h y hy)
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    rw [heq]
    exact Submodule.fg_span_singleton x
  obtain ⟨y, hy, hxy⟩ := hex
  obtain ⟨z, rfl⟩ := (_root_.ValuationRing.dvd_total x y).resolve_left hxy
  have hz : z ∈ maximalIdeal V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hxy
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    exact ⟨w, by simp [mul_assoc, hw]⟩
  exact Ideal.mul_mem_mul hy hz

/-- A nonzero maximal ideal of a valuation domain is idempotent exactly when it is not
finitely generated. The nonzero assumption excludes the maximal ideal of a field. -/
theorem isIdempotentElem_maximalIdeal_iff (hne : maximalIdeal V ≠ ⊥) :
    IsIdempotentElem (maximalIdeal V) ↔ ¬ (maximalIdeal V).FG := by
  refine ⟨fun hi hfg ↦ ?_, isIdempotentElem_maximalIdeal_of_not_fg⟩
  exact ((maximalIdeal V).isIdempotentElem_iff_eq_bot_or_top hfg).mp hi |>.elim hne
    (maximalIdeal.isMaximal V).ne_top

end TauCeti.ValuationRing

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- The maximal ideal of a valuation ring of an algebraically closed field is idempotent,
including for the trivial valuation. -/
theorem isIdempotentElem_maximalIdeal_of_isAlgClosed (v : Valuation K Γ₀) [IsAlgClosed K] :
    IsIdempotentElem (maximalIdeal v.valuationSubring) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) (by decide : 0 < 2)
  have hyv : v y < 1 := by
    have hxv := (v.mem_maximalIdeal_iff).mp hx
    rw [← hy, map_pow] at hxv
    exact lt_of_not_ge fun h ↦ hxv.not_ge (one_le_pow₀ h)
  let z : v.valuationSubring := ⟨y, hyv.le⟩
  have hz : z ∈ maximalIdeal v.valuationSubring := v.mem_maximalIdeal_iff.mpr hyv
  have heq : x = z * z := Subtype.ext (by simpa [pow_two] using hy.symm)
  rw [heq]
  exact Ideal.mul_mem_mul hz hz

end Valuation
