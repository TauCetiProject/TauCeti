/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The quotient by a maximal ideal of a local ring

A local ring `R` has exactly one maximal ideal, so the quotient `R ⧸ 𝔪` by any maximal ideal `𝔪`
is the residue field `κ`. This file records that identification as an `R`-linear equivalence, so
that a statement about the simple modules `R ⧸ 𝔪` of an arbitrary commutative ring can be
specialised to the residue field of a local ring.

## Main declarations

* `TauCeti.quotientEquivResidueField`: `R ⧸ 𝔪 ≃ₗ[R] κ` for a maximal ideal `𝔪`,
  sending the class of `r` to `residue R r`.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The quotient of a local ring by a maximal ideal is its residue field, as an `R`-linear
equivalence sending the class of `r` to `residue R r`. -/
def quotientEquivResidueField {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) :
    (R ⧸ 𝔪) ≃ₗ[R] ResidueField R :=
  -- `𝔪` is the maximal ideal, the kernel of `residue`.
  Submodule.quotEquivOfEq _ _ (by
      ext r
      simp [eq_maximalIdeal h𝔪, ResidueField.algebraMap_eq, residue_eq_zero_iff]) ≪≫ₗ
    (Algebra.linearMap R (ResidueField R)).quotKerEquivOfSurjective residue_surjective

/-- `quotientEquivResidueField` sends the class of `r` to its residue. -/
@[simp]
theorem quotientEquivResidueField_mk {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (r : R) :
    quotientEquivResidueField h𝔪 (Ideal.Quotient.mk 𝔪 r) = residue R r :=
  (rfl)

end TauCeti
