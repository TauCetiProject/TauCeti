/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Fibres of quotient maps by two-sided ideals

For a two-sided ideal `I` of a ring `R` and an element `x ∈ R`, the fibre of the quotient map
`Ideal.Quotient.mk I : R →+* R ⧸ I` over `Ideal.Quotient.mk I x` is the coset `x + I`
(`Ideal.Quotient.preimage_mk_singleton`). This specializes `Ideal.Quotient.quotient_ring_saturate`
to a single residue class without assuming commutativity of multiplication.
-/

public section

namespace Ideal.Quotient

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- The fibre of the quotient map `R →+* R ⧸ I` over the class of `x` is the coset `x + I`. -/
theorem preimage_mk_singleton (x : R) :
    mk I ⁻¹' {mk I x} = (x + ·) '' (I : Set R) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Ideal.Quotient.eq, Set.mem_image,
    SetLike.mem_coe]
  refine ⟨fun h ↦ ⟨y - x, h, add_sub_cancel x y⟩, ?_⟩
  rintro ⟨z, hz, rfl⟩
  simpa using hz

end Ideal.Quotient
