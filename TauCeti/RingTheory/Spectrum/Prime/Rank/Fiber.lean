/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.LocallyConstant

/-!
# Coefficient rings of module rank fibres

For a finitely presented flat module, the rank is locally constant on the coefficient spectrum.
Its rank-`r` fibre defines a clopen factor ring over which scalar extension has constant rank `r`.
This construction does not require a presentation of the module as a quotient.

## References

* The Stacks Project, Tag 00EE, for clopen decompositions and idempotents.
-/

public section

open scoped TensorProduct

namespace Module

variable (A : Type*) [CommRing A] (Q : Type*) [AddCommGroup Q] [Module A Q]
  [FinitePresentation A Q] [Flat A Q]

/-- The coefficient ring of the clopen locus where `Q` has rank `r`. -/
noncomputable abbrev rankRing (r : ℕ) :=
  LocallyConstant.fiberRing ⟨_, isLocallyConstant_rankAtStalk (R := A) (M := Q)⟩ r

/-- Scalar extension of `Q` to its rank-`r` factor has constant stalk rank `r`. -/
@[simp]
theorem rankAtStalk_rankRing_tensor (r : ℕ) (p : PrimeSpectrum (rankRing A Q r)) :
    rankAtStalk (rankRing A Q r ⊗[A] Q) p = r := by
  rw [rankAtStalk_baseChange]
  exact (Set.ext_iff.mp (LocallyConstant.range_comap_fiberRing
    ⟨_, isLocallyConstant_rankAtStalk (R := A) (M := Q)⟩ r) _).mp ⟨p, rfl⟩

end Module
