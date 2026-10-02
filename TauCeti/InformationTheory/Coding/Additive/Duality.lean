/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Puncture.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower

/-!
# Puncturing, shortening, and duality for additive codes

An additive code over a finite bilinear alphabet has a dual given by the orthogonal complement
for the summed coordinate pairing. For a set `s` of retained coordinates,
`(puncture C s)ᗮ = shorten Cᗮ s`. If the alphabet pairing is nondegenerate, also
`(shorten C s)ᗮ = puncture Cᗮ s`.

These identities apply to arbitrary additive subgroups, including codes over discriminant
alphabets without a field structure. The first identity holds even for degenerate pairings;
the second uses nondegeneracy. The coordinate sets may be empty and the code may be zero.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §§1.4–1.5 and
  Chapter 9, for duality and coordinate deletion of linear and additive codes.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u v

variable (A : FiniteBilinearModule.{u}) {ι : Type v} [Fintype ι]
variable (C : AdditiveCode A ι) (s : Set ι) [Fintype s]

/-- The orthogonal complement of a punctured additive code is the shortened orthogonal
complement, retaining the same coordinates. No nondegeneracy assumption is needed. -/
@[simp]
theorem orthogonalComplement_puncture :
    (A.coordinatePower s).orthogonalComplement (AdditiveCode.puncture C s) =
      AdditiveCode.shorten ((A.coordinatePower ι).orthogonalComplement C) s := by
  ext y
  rw [AdditiveCode.mem_shorten_iff_extend_mem,
    mem_orthogonalComplement_iff, mem_orthogonalComplement_iff]
  simp_rw [A.coordinatePower_pairing_extend_zero_left
      (f := (Subtype.val : s → ι)) Subtype.val_injective]
  constructor
  · intro h x hx
    exact h _ (AdditiveCode.mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩)
  · intro h z hz
    obtain ⟨x, hx, hxz⟩ := AdditiveCode.mem_puncture.mp hz
    have heq : x ∘ (Subtype.val : s → ι) = z := funext hxz
    simpa only [heq] using h x hx

/-- For a nondegenerate finite bilinear alphabet, the orthogonal complement of a shortened
additive code is the punctured orthogonal complement, retaining the same coordinates. -/
@[simp]
theorem IsNondegenerate.orthogonalComplement_shorten (hA : A.IsNondegenerate) :
    (A.coordinatePower s).orthogonalComplement (AdditiveCode.shorten C s) =
      AdditiveCode.puncture ((A.coordinatePower ι).orthogonalComplement C) s := by
  have hι := hA.coordinatePower ι
  have hs := hA.coordinatePower s
  rw [← IsNondegenerate.orthogonalComplement_orthogonalComplement
    (A.coordinatePower s) hs
    (AdditiveCode.puncture ((A.coordinatePower ι).orthogonalComplement C) s),
    A.orthogonalComplement_puncture,
    IsNondegenerate.orthogonalComplement_orthogonalComplement (A.coordinatePower ι) hι]

end TauCeti.FiniteBilinearModule
