/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.Module

/-!
# Fractional ideals of an order as lattices

A fractional ideal `I` of an order `O` in a number field `K` is a finitely generated free
`ℤ`-module, and when `I ≠ 0` it spans `K` over `ℚ`, so its `ℤ`-rank is the degree `[K : ℚ]`.
Any `ℤ`-basis of `I` is therefore a `ℚ`-basis of `K`. These are the facts that let one compute
with a fractional ideal of an order through coordinates, as one does for the lattices `[α, β]` of
a quadratic order.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.span_rat_eq_top`: a nonzero fractional ideal of
  an order spans its number field over `ℚ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.span_int_range_basis`: the members of a `ℤ`-basis
  of a fractional ideal span it over `ℤ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.span_rat_range_basis`: the members of any
  `ℤ`-basis of a nonzero fractional ideal span the number field over `ℚ`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.finrank_int_eq_finrank_rat`: a nonzero
  fractional ideal has `ℤ`-rank `[K : ℚ]`.

## Implementation notes

This generalises Mathlib's treatment of fractional ideals of the maximal order `𝓞 K` in
`Mathlib/NumberTheory/NumberField/FractionalIdeal.lean`. The `Module.Finite ℤ` and
`Module.Free ℤ` instances follow its instances for `𝓞 K`, which transport the ideal to its
numerator (there along `FractionalIdeal.equivNum`, here along
`FractionalIdeal.equivNumOfIsLocalization`). The results `span_int_range_basis` and
`finrank_int_eq_finrank_rat` are the order analogues of
`NumberField.mem_span_basisOfFractionalIdeal` and `NumberField.fractionalIdeal_rank`, which
Mathlib states only for `𝓞 K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2 and §12.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- A fractional ideal of an order is a finitely generated `ℤ`-module: it is isomorphic to its
numerator, an ideal of the order, which lies in the finitely generated `ℤ`-module `O`. -/
instance (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Module.Finite ℤ I := by
  have : Module.Finite ℤ I.num :=
    .of_injective (I.num.subtype.restrictScalars ℤ) (Submodule.injective_subtype _)
  exact .of_surjective (I.equivNumOfIsLocalization.restrictScalars ℤ).symm.toLinearMap
    (LinearEquiv.surjective _)

/-- A fractional ideal of an order is a free `ℤ`-module. -/
instance (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Module.Free ℤ I :=
  Module.free_of_finite_type_torsion_free'

/-- **A nonzero fractional ideal of an order spans its number field over `ℚ`.** It contains
`x O` for each of its nonzero elements `x`, and `O` spans `K` over `ℚ`. -/
theorem span_rat_eq_top {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : I ≠ 0) :
    Submodule.span ℚ (I : Set K) = ⊤ := by
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  refine eq_top_iff.mpr fun y _ ↦ ?_
  have hy : y * x⁻¹ ∈ Submodule.span ℚ (O.toSubalgebra : Set K) := O.spans ▸ Submodule.mem_top
  have hle : ((LinearMap.mulLeft ℚ x) '' (O.toSubalgebra : Set K)) ⊆ I := by
    rintro _ ⟨o, ho, rfl⟩
    simpa [mul_comm x o, Algebra.smul_def] using
      (I : Submodule O.toSubalgebra K).smul_mem ⟨o, ho⟩ hxI
  refine Submodule.span_mono hle ?_
  rw [Submodule.span_image]
  exact ⟨y * x⁻¹, hy, by simp [mul_comm x, inv_mul_cancel_right₀ hx]⟩

/-- **The members of a `ℤ`-basis of a fractional ideal span it over `ℤ`.** -/
theorem span_int_range_basis {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    {ι : Type*} (b : Module.Basis ι ℤ I) :
    (Submodule.span ℤ (Set.range fun i ↦ (b i : K)) : Set K) = I := by
  let f := (I : Submodule O.toSubalgebra K).subtype.restrictScalars ℤ
  have hf : (Set.range fun i ↦ (b i : K)) = f '' Set.range b := by
    rw [← Set.range_comp]
    simp [f, Function.comp_def]
  rw [hf, Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.range_restrictScalars,
    Submodule.range_subtype, Submodule.coe_restrictScalars, FractionalIdeal.coeToSet_coeToSubmodule]

/-- **A `ℤ`-basis of a nonzero fractional ideal spans the number field over `ℚ`.** -/
theorem span_rat_range_basis {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (hI : I ≠ 0) {ι : Type*} (b : Module.Basis ι ℤ I) :
    Submodule.span ℚ (Set.range fun i ↦ (b i : K)) = ⊤ := by
  rw [← Submodule.span_span_of_tower ℤ, span_int_range_basis b]
  exact span_rat_eq_top hI

/-- **A nonzero fractional ideal of an order has `ℤ`-rank `[K : ℚ]`.** A `ℤ`-basis of the ideal is
linearly independent over `ℚ` and spans `K`, so it is a `ℚ`-basis of `K`. -/
theorem finrank_int_eq_finrank_rat {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K}
    (hI : I ≠ 0) :
    Module.finrank ℤ I = Module.finrank ℚ K := by
  let b := Module.Free.chooseBasis ℤ I
  have hli : LinearIndependent ℚ fun i ↦ (b i : K) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' (((I : Submodule O.toSubalgebra K).restrictScalars ℤ).subtype)
        (Submodule.ker_subtype _))
  rw [Module.finrank_eq_card_chooseBasisIndex,
    Module.finrank_eq_card_basis (Module.Basis.mk hli (span_rat_range_basis hI b).ge)]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
