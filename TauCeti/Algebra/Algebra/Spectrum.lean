/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Spectra under unit-reflecting algebra homomorphisms

Every algebra homomorphism `φ` satisfies `spectrum R (φ a) ⊆ spectrum R a`
(`AlgHom.spectrum_apply_subset`). When `φ` also reflects units, the inclusion is an equality.
This is the algebraic form of spectral permanence: it holds for the inclusion of an
inverse-closed subalgebra, and for the complexification of real operators.
-/

public section

namespace AlgHom

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [FunLike F A B] [AlgHomClass F R A B]

/-- An algebra homomorphism which reflects units preserves spectra. -/
@[simp]
theorem spectrum_apply_eq (φ : F) [IsLocalHom φ] (a : A) :
    spectrum R (φ a) = spectrum R a := by
  ext r
  simp only [spectrum.mem_iff, ← isUnit_map_iff φ (algebraMap R A r - a), map_sub,
    AlgHomClass.commutes]

end AlgHom
