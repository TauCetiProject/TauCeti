/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# The conductor as an annihilator

For an order `O`, the normalization quotient `𝓞 K / O` is a finite module over `O`, not
in general a module over `𝓞 K`. We use `O.toRingOfIntegers` as the copy of the order in the
maximal order. The submodule `1` over this ring is precisely the image of the order, so
`𝓞 K ⧸ (1 : Submodule O.toRingOfIntegers (𝓞 K))` is the normalization quotient.

Its annihilator is the conductor contracted to the order. Extending that annihilator back
to the maximal order recovers the conductor itself. The cardinality of the quotient is
`O.index`, agreeing with the additive quotient used to define the index.

The annihilator calculation uses Mathlib's `Submodule.annihilator_quotient`, which identifies
the annihilator with a colon ideal.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- The annihilator of the normalization quotient is the conductor, viewed as an ideal of
the order rather than of the maximal order. -/
@[simp]
theorem annihilator_quotient_eq_conductor_comap :
    Module.annihilator O.toRingOfIntegers
        (𝓞 K ⧸ (1 : Submodule O.toRingOfIntegers (𝓞 K))) =
      O.conductor.comap O.toRingOfIntegers.val.toRingHom := by
  rw [Submodule.annihilator_quotient]
  ext x
  simp [Submodule.mem_colon, mem_conductor_iff, Algebra.smul_def,
    Subalgebra.algebraMap_eq]

/-- Extending the annihilator of `𝓞 K / O` to `𝓞 K` recovers the conductor. -/
theorem conductor_eq_map_annihilator_quotient :
    O.conductor =
      (Module.annihilator O.toRingOfIntegers
        (𝓞 K ⧸ (1 : Submodule O.toRingOfIntegers (𝓞 K)))).map
          O.toRingOfIntegers.val.toRingHom := by
  rw [O.annihilator_quotient_eq_conductor_comap]
  apply le_antisymm
  · intro x hx
    let y : O.toRingOfIntegers :=
      ⟨x, O.mem_toRingOfIntegers.mpr (O.conductor_le_order hx)⟩
    exact Ideal.mem_map_of_mem O.toRingOfIntegers.val.toRingHom
      (Ideal.mem_comap.mpr hx : y ∈ O.conductor.comap O.toRingOfIntegers.val.toRingHom)
  · exact Ideal.map_comap_le

/-- The normalization quotient has cardinality equal to the index of the order. -/
@[simp]
theorem natCard_quotient_eq_index :
    Nat.card (𝓞 K ⧸ (1 : Submodule O.toRingOfIntegers (𝓞 K))) = O.index := by
  rw [O.index_def]
  have h := Nat.card_congr
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (1 : Submodule O.toRingOfIntegers (𝓞 K))).toEquiv
  simpa only [Subalgebra.restrictScalars_one] using h.symm

/-- The normalization quotient of a number-field order is finite. -/
instance finite_quotient :
    Finite (𝓞 K ⧸ (1 : Submodule O.toRingOfIntegers (𝓞 K))) :=
  Nat.finite_of_card_ne_zero <| by
    rw [O.natCard_quotient_eq_index]
    exact O.index_ne_zero

end TauCeti.GlobalNumberFields.NumberFieldOrder
