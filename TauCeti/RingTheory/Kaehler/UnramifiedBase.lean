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

Dually, if `A/S` is formally unramified, the first map of the transitivity sequence
`A ⊗[S] Ω[S⁄R] → Ω[A⁄R] → Ω[A⁄S] → 0` is surjective: the differentials of `A` over `R` are
spanned by those of `S`.

## References

* The Stacks Project, Tag 00RS: the transitivity sequence for differentials.
-/

public section

noncomputable section

namespace KaehlerDifferential

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

section UnramifiedBase

variable [Algebra.FormallyUnramified R S]

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

end UnramifiedBase

section UnramifiedTop

variable [Algebra.FormallyUnramified S A]

/-- If `A` is formally unramified over `S`, then `A ⊗[S] Ω[S⁄R] → Ω[A⁄R]` is surjective. This
generalizes `KaehlerDifferential.mapBaseChange_surjective`, for `S → A` surjective. -/
theorem mapBaseChange_surjective_of_formallyUnramified :
    Function.Surjective (mapBaseChange R S A) := by
  rw [← LinearMap.range_eq_top, range_mapBaseChange, ← top_le_iff]
  exact fun x _ ↦ Subsingleton.elim _ _

end UnramifiedTop

end KaehlerDifferential
