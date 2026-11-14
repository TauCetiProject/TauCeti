/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Ideal.AssociatedGraded

/-!
# The associated graded ring of a local ring over its residue field

For a commutative local ring `(R, 𝔪, κ)`, the associated graded ring `gr_𝔪 R = ⨁ ν, 𝔪ᵛ ⧸ 𝔪ᵛ⁺¹`
is an algebra over `R ⧸ 𝔪` through its degree-zero part. This file transports that structure to
the residue field `κ = IsLocalRing.ResidueField R`, so that `gr_𝔪 R` is a `κ`-algebra with `R`
acting through `κ`.
-/

public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The associated graded ring of the maximal ideal is an algebra over the residue field. -/
noncomputable instance : Algebra (ResidueField R) (maximalIdeal R).AssociatedGraded :=
  inferInstanceAs (Algebra (R ⧸ maximalIdeal R) (maximalIdeal R).AssociatedGraded)

/-- Scalars from the local ring act through its residue field on the associated graded ring. -/
instance : IsScalarTower R (ResidueField R) (maximalIdeal R).AssociatedGraded :=
  inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (maximalIdeal R).AssociatedGraded)

/-- The degree-zero class of a residue is the scalar class of its representative. -/
@[simp]
theorem algebraMap_associatedGraded_residue (r : R) :
    algebraMap (ResidueField R) (maximalIdeal R).AssociatedGraded (residue R r) =
      algebraMap R (maximalIdeal R).AssociatedGraded r :=
  Ideal.AssociatedGraded.algebraMap_quotient_mk r

end IsLocalRing
