/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Basic

/-!
# Kähler differentials over a formally unramified base

For a scalar tower `R → S → A`, formal unramifiedness of `S/R` identifies
`Ω[A⁄R]` with `Ω[A⁄S]`. Thus differentials, and their Fitting ideals, do not depend on
which of these two base rings is used. In particular this applies to changing affine
base charts along an open immersion.

## References

* The Stacks Project, Tag 00RS: the transitivity sequence for differentials.
-/

public section

noncomputable section

namespace KaehlerDifferential

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [Algebra.FormallyUnramified R S]

/-- Enlarging the base through a formally unramified algebra makes the canonical map
on Kähler differentials bijective. -/
theorem map_bijective_of_formallyUnramified_base :
    Function.Bijective (map R S A A) := by
  refine ⟨?_, map_surjective R S A⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R S A x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- The canonical identification `Ω[A⁄R] ≃ₗ[A] Ω[A⁄S]` when `S/R` is formally
unramified. -/
def equivOfFormallyUnramifiedBase : Ω[A⁄R] ≃ₗ[A] Ω[A⁄S] :=
  LinearEquiv.ofBijective (map R S A A)
    (map_bijective_of_formallyUnramified_base R S A)

/-- The base comparison is the canonical map on Kähler differentials. -/
@[simp]
theorem equivOfFormallyUnramifiedBase_apply (x : Ω[A⁄R]) :
    equivOfFormallyUnramifiedBase R S A x = map R S A A x :=
  (rfl)

/-- The inverse base comparison preserves the differential of a function. -/
@[simp]
theorem equivOfFormallyUnramifiedBase_symm_D (a : A) :
    (equivOfFormallyUnramifiedBase R S A).symm (D S A a) = D R A a := by
  rw [LinearEquiv.symm_apply_eq]
  simp

end KaehlerDifferential
