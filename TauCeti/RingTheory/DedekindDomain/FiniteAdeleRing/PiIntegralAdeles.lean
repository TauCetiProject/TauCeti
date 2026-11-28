/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# The integral vectors `Ôⁱ` of the finite adeles

Let `R` be a Dedekind domain with fraction field `K` and `Ô = ∏_v 𝒪_v` the integral finite adeles
(`IsDedekindDomain.FiniteAdeleRing.integralAdeles`). For an index type `ι`, the vectors of
`𝔸_fⁱ` all of whose coordinates are integral form the additive subgroup `Ôⁱ`, the standard
lattice of `𝔸_fⁱ`. For finite `ι` it is open, as `Ô` is.

For the finite adeles of a CM field it carries the lattice vacuum of the Weil representation at
the finite places.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.piIntegralAdeles R K ι`: the additive subgroup `Ôⁱ` of
  `ι → FiniteAdeleRing R K`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.mem_piIntegralAdeles`,
  `IsDedekindDomain.FiniteAdeleRing.coe_piIntegralAdeles`: membership is integrality of every
  coordinate, and `Ôⁱ` is the box `Set.univ.pi fun _ ↦ Ô`.
* `IsDedekindDomain.FiniteAdeleRing.isOpen_piIntegralAdeles`: `Ôⁱ` is open for finite `ι`.
-/

public section

noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (ι : Type*)

/-- The **integral vectors** `Ôⁱ`: the additive subgroup of `ι → FiniteAdeleRing R K` of the
vectors all of whose coordinates are integral finite adeles. -/
def piIntegralAdeles : AddSubgroup (ι → FiniteAdeleRing R K) :=
  AddSubgroup.pi Set.univ fun _ ↦ (integralAdeles R K).toSubring.toAddSubgroup

variable {R K ι}

/-- A vector lies in `Ôⁱ` exactly when each of its coordinates is integral. -/
@[simp]
theorem mem_piIntegralAdeles {x : ι → FiniteAdeleRing R K} :
    x ∈ piIntegralAdeles R K ι ↔ ∀ i, x i ∈ integralAdeles R K := by
  simp [piIntegralAdeles, AddSubgroup.mem_pi]

variable (R K ι)

/-- `Ôⁱ` is the box with every factor `Ô`. -/
theorem coe_piIntegralAdeles :
    (piIntegralAdeles R K ι : Set (ι → FiniteAdeleRing R K)) =
      Set.univ.pi fun _ ↦ (integralAdeles R K : Set (FiniteAdeleRing R K)) := by
  ext x
  simp

/-- For finite `ι`, `Ôⁱ` is open in `ι → FiniteAdeleRing R K`. -/
theorem isOpen_piIntegralAdeles [Finite ι] :
    IsOpen (piIntegralAdeles R K ι : Set (ι → FiniteAdeleRing R K)) := by
  rw [coe_piIntegralAdeles]
  exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_integralAdeles R K

end IsDedekindDomain.FiniteAdeleRing
