/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Fractional ideals of an order as lattices

A nonzero fractional ideal `I` of an order `O` in a number field `K` is a lattice in `K`: it is
the `ℤ`-span of a `ℚ`-basis of `K`. Indeed `I` is isomorphic to its numerator, a submodule of the
finite free `ℤ`-module `O`, so it is finite free over `ℤ`; a `ℤ`-basis of `I` stays linearly
independent over `ℚ`, and it spans `K` over `ℚ` because `I` contains `x O` for any nonzero
`x ∈ I`.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_basis_restrictScalars_eq_span`: a nonzero
  fractional ideal of an order is the `ℤ`-span of a `ℚ`-basis of the number field.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open Module NumberField Submodule
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

universe u

variable {K : Type u} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- A nonzero fractional ideal of an order is the `ℤ`-span of a `ℚ`-basis of the number field. -/
theorem exists_basis_restrictScalars_eq_span
    {I : FractionalIdeal O.toSubalgebra⁰ K} (hI : I ≠ 0) :
    ∃ b : Basis (Fin (finrank ℚ K)) ℚ K,
      (I : Submodule O.toSubalgebra K).restrictScalars ℤ = span ℤ (Set.range b) := by
  -- `I` is isomorphic to its numerator, a submodule of the finite free `ℤ`-module `O`.
  have : Module.Finite ℤ I.num :=
    .of_injective (I.num.subtype.restrictScalars ℤ) (Submodule.injective_subtype _)
  have : Module.Finite ℤ I :=
    .of_surjective (I.equivNumOfIsLocalization.restrictScalars ℤ).symm.toLinearMap
      (LinearEquiv.surjective _)
  have : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let c := Module.Free.chooseBasis ℤ I
  let f := (I : Submodule O.toSubalgebra K).subtype.restrictScalars ℤ
  have hspan : span ℤ (Set.range (f ∘ c)) = (I : Submodule O.toSubalgebra K).restrictScalars ℤ := by
    rw [Set.range_comp, span_image, c.span_eq, Submodule.map_top, LinearMap.range_restrictScalars,
      range_subtype]
  have hli : LinearIndependent ℚ (f ∘ c) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (c.linearIndependent.map' f (by simp [f]))
  -- `I` contains `x O` for a nonzero `x ∈ I`, and `O` spans `K` over `ℚ`.
  have htop : span ℚ ((I : Submodule O.toSubalgebra K) : Set K) = ⊤ := by
    obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    refine eq_top_iff.mpr fun y _ ↦ ?_
    have hy : y * x⁻¹ ∈ span ℚ (O.toSubalgebra : Set K) := O.spans ▸ Submodule.mem_top
    have hle : (LinearMap.mulLeft ℚ x) '' (O.toSubalgebra : Set K) ⊆
        (I : Submodule O.toSubalgebra K) := by
      rintro _ ⟨o, ho, rfl⟩
      simpa [mul_comm x o, Algebra.smul_def] using
        (I : Submodule O.toSubalgebra K).smul_mem ⟨o, ho⟩ hxI
    refine span_mono hle ?_
    rw [span_image]
    exact ⟨y * x⁻¹, hy, by simp [mul_comm x, inv_mul_cancel_right₀ hx]⟩
  have hI' : ((I : Submodule O.toSubalgebra K) : Set K) =
      span ℤ (Set.range (f ∘ c)) := by
    rw [hspan, coe_restrictScalars]
  let b := Basis.mk hli (by rw [← htop, hI', span_span_of_tower])
  refine ⟨b.reindex (b.indexEquiv (finBasis ℚ K)), ?_⟩
  rw [Basis.range_reindex, Basis.coe_mk, hspan]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
