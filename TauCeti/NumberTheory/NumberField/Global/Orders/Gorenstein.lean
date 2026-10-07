/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic
public import Mathlib.RingTheory.DedekindDomain.Different
import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice

/-!
# Gorenstein orders and the trace dual

The trace dual (or complementary module) of an order `O` in a number field `K` is

`O^∨ = {x ∈ K | Tr_{K/ℚ}(x O) ⊆ ℤ}`.

It is again a full fractional `O`-ideal. An order is Gorenstein when this fractional ideal is
invertible. This is the standard global definition for orders in number fields; equivalently, the
localizations of the order are one-dimensional Gorenstein rings.

This file constructs the trace dual as a fractional ideal, proves its elementwise trace
characterization and reflexivity, and shows that its multiplier ring is the original order. It
also records two fundamental families of examples: maximal orders and quadratic orders are
Gorenstein.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.traceDual`: the trace-dual fractional ideal of an
  order.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.IsGorenstein`: the trace dual is invertible.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.mem_traceDual_iff`: membership is integrality of
  the trace pairing against every element of the order.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.one_le_traceDual`: the order lies in its trace dual.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.multiplierRing_traceDual`: the trace dual is a
  proper fractional ideal.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_iff`: an order is Gorenstein exactly
  when its trace dual is invertible.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_of_isDedekindDomain`: an order that is
  a Dedekind domain is Gorenstein.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_maximalNumberFieldOrder`: the maximal
  order is Gorenstein.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_of_finrank_eq_two`: every quadratic
  order is Gorenstein.

## Implementation notes

The underlying submodule of `traceDual` is Mathlib's `Submodule.traceDual ℤ ℚ 1` (see
`coe_traceDual`), so Mathlib's general trace-dual API applies to it directly; reflexivity
(`traceDual_traceDual`) is stated at this submodule level.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

private abbrev FractionalOrderIdeal (O : NumberFieldOrder K) :=
  FractionalIdeal (nonZeroDivisors O.toSubalgebra) K

private noncomputable def integerBasis (O : NumberFieldOrder K) :=
  Module.Free.chooseBasis ℤ (1 : FractionalOrderIdeal O)

private noncomputable def rationalBasis (O : NumberFieldOrder K) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (1 : FractionalOrderIdeal O)) ℚ K := by
  let b := O.integerBasis
  refine Module.Basis.mk ?_ (O.span_rat_range_basis one_ne_zero b).ge
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (b.linearIndependent.map'
      ((((1 : FractionalOrderIdeal O) : Submodule O.toSubalgebra K).restrictScalars ℤ).subtype)
      (Submodule.ker_subtype _))

private theorem range_rationalBasis (O : NumberFieldOrder K) :
    Set.range O.rationalBasis = Set.range fun i ↦ (O.integerBasis i : K) := by
  rw [rationalBasis, Module.Basis.coe_mk]

private theorem restrictScalars_one_eq_span_integerBasis (O : NumberFieldOrder K) :
    ((1 : Submodule O.toSubalgebra K).restrictScalars ℤ) =
      Submodule.span ℤ (Set.range O.rationalBasis) := by
  apply SetLike.coe_injective
  rw [O.range_rationalBasis, O.span_int_range_basis, Submodule.coe_restrictScalars,
    ← FractionalIdeal.coe_one, FractionalIdeal.coeToSet_coeToSubmodule]

private theorem traceDual_restrictScalars_eq_span (O : NumberFieldOrder K) :
    (Submodule.traceDual ℤ ℚ (1 : Submodule O.toSubalgebra K)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range O.rationalBasis.traceDual) := by
  exact Submodule.traceDual_span_of_basis ℤ (1 : Submodule O.toSubalgebra K)
    O.rationalBasis (O.restrictScalars_one_eq_span_integerBasis)

private theorem traceDual_fg (O : NumberFieldOrder K) :
    (Submodule.traceDual ℤ ℚ (1 : Submodule O.toSubalgebra K)).FG := by
  rw [← Submodule.FG.restrictScalars_iff (R := ℤ), O.traceDual_restrictScalars_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

/-- The trace dual (or complementary module) of an order `O`:
the fractional ideal of `x : K` such that `Tr_{K/ℚ}(xy)` is an integer for every `y ∈ O`. -/
def traceDual (O : NumberFieldOrder K) :
    FractionalIdeal (nonZeroDivisors O.toSubalgebra) K :=
  ⟨Submodule.traceDual ℤ ℚ (1 : Submodule O.toSubalgebra K),
    FractionalIdeal.isFractional_of_fg O.traceDual_fg⟩

@[simp]
theorem coe_traceDual (O : NumberFieldOrder K) :
    (O.traceDual : Submodule O.toSubalgebra K) =
      Submodule.traceDual ℤ ℚ (1 : Submodule O.toSubalgebra K) :=
  (rfl)

/-- Membership in the trace dual means that the trace pairing against every element of the order
is integral. -/
@[simp]
theorem mem_traceDual_iff (O : NumberFieldOrder K) (x : K) :
    x ∈ O.traceDual ↔
      ∀ y : O.toSubalgebra,
        Algebra.trace ℚ K (x * y) ∈ (algebraMap ℤ ℚ).range := by
  rw [← FractionalIdeal.mem_coe, O.coe_traceDual, Submodule.mem_traceDual]
  constructor
  · intro h y
    simpa [Algebra.traceForm_apply] using h (y : K) (Submodule.mem_one.mpr ⟨y, rfl⟩)
  · intro h y hy
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hy
    simpa [Algebra.traceForm_apply] using h z

/-- The order, viewed as the unit fractional ideal, is contained in its trace dual. -/
theorem one_le_traceDual (O : NumberFieldOrder K) :
    (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) ≤ O.traceDual := by
  intro x hx
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
  rw [O.mem_traceDual_iff]
  intro y
  have htr : IsIntegral ℤ (Algebra.trace ℚ K ((a * y : O.toSubalgebra) : K)) :=
    Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := K) (O.isIntegral (a * y))
  simpa using IsIntegrallyClosed.isIntegral_iff.mp htr

/-- The unit element belongs to the trace dual of every number-field order. -/
theorem one_mem_traceDual (O : NumberFieldOrder K) : (1 : K) ∈ O.traceDual :=
  O.one_le_traceDual (FractionalIdeal.one_mem_one _)

/-- The trace dual of an order is nonzero. -/
theorem traceDual_ne_zero (O : NumberFieldOrder K) : O.traceDual ≠ 0 := by
  intro h
  have := O.one_mem_traceDual
  rw [h, FractionalIdeal.mem_zero_iff] at this
  exact one_ne_zero this

/-- Taking the trace dual twice recovers the original order. -/
theorem traceDual_traceDual (O : NumberFieldOrder K) :
    Submodule.traceDual ℤ ℚ (O.traceDual : Submodule O.toSubalgebra K) =
      (1 : Submodule O.toSubalgebra K) := by
  rw [O.coe_traceDual]
  apply Submodule.restrictScalars_injective ℤ
  rw [Submodule.traceDual_span_of_basis ℤ
      (Submodule.traceDual ℤ ℚ (1 : Submodule O.toSubalgebra K))
      O.rationalBasis.traceDual O.traceDual_restrictScalars_eq_span,
    Module.Basis.traceDual_traceDual, ← O.restrictScalars_one_eq_span_integerBasis]

/-- The multiplier ring of the trace dual is the order itself. Thus the trace dual is always a
proper fractional ideal, whether or not it is invertible. -/
@[simp]
theorem multiplierRing_traceDual (O : NumberFieldOrder K) :
    O.multiplierRing O.traceDual = O.toSubalgebra.toSubring := by
  apply le_antisymm ?_ (O.order_le_multiplierRing O.traceDual)
  intro x hx
  have hx' : x ∈ Submodule.traceDual ℤ ℚ
      (O.traceDual : Submodule O.toSubalgebra K) := by
    rw [Submodule.mem_traceDual]
    intro y hy
    have hxy : x * y ∈ O.traceDual := (O.mem_multiplierRing_iff O.traceDual x).mp hx y hy
    simpa [Algebra.traceForm_apply] using (O.mem_traceDual_iff (x * y)).mp hxy 1
  rw [O.traceDual_traceDual] at hx'
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hx'
  exact z.property

/-- The trace dual is a proper fractional ideal. -/
@[simp]
theorem isProperFractionalIdeal_traceDual (O : NumberFieldOrder K) :
    O.IsProperFractionalIdeal O.traceDual := by
  rw [O.isProperFractionalIdeal_def]
  exact O.multiplierRing_traceDual

/-- A number-field order is **Gorenstein** when its trace-dual fractional ideal is invertible. -/
@[mk_iff]
structure IsGorenstein (O : NumberFieldOrder K) : Prop where
  /-- The trace dual of a Gorenstein order is invertible. -/
  isUnit_traceDual : IsUnit O.traceDual

attribute [simp] isGorenstein_iff

/-- An order that is a Dedekind domain is Gorenstein, since every nonzero fractional ideal of a
Dedekind domain is invertible. -/
theorem isGorenstein_of_isDedekindDomain (O : NumberFieldOrder K)
    [IsDedekindDomain O.toSubalgebra] : O.IsGorenstein :=
  ⟨isUnit_iff_ne_zero.mpr O.traceDual_ne_zero⟩

/-- The maximal order of a number field is Gorenstein. -/
theorem isGorenstein_maximalNumberFieldOrder :
    (maximalNumberFieldOrder K).IsGorenstein := by
  let _ : IsDedekindDomain (maximalNumberFieldOrder K).toSubalgebra := by
    rw [maximalNumberFieldOrder_toSubalgebra]
    exact IsIntegralClosure.isDedekindDomain ℤ ℚ K _
  exact isGorenstein_of_isDedekindDomain _

/-- Every order in a quadratic number field is Gorenstein. -/
theorem isGorenstein_of_finrank_eq_two (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) : O.IsGorenstein :=
  ⟨IsProperFractionalIdeal.isUnit_of_finrank_eq_two hK O.isProperFractionalIdeal_traceDual⟩

end NumberFieldOrder

end TauCeti.GlobalNumberFields
