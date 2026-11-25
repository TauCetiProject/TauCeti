/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Absolute Galois automorphisms as algebra automorphisms

Mathlib defines `Field.absoluteGaloisGroup k` as the `k`-algebra automorphisms of
`AlgebraicClosure k`, through a definition that instance search and `simp` do not unfold. This
file names the identification of the two as a group isomorphism.

## Main definitions

* `Field.absoluteGaloisGroup.toAlgEquiv`: an absolute Galois automorphism viewed as a
  `k`-algebra automorphism of `AlgebraicClosure k`.
-/

public section

universe u

namespace Field.absoluteGaloisGroup

variable {k : Type u} [Field k]

/-- View an absolute Galois automorphism as an algebra automorphism of the algebraic closure. -/
noncomputable abbrev toAlgEquiv : Field.absoluteGaloisGroup k ≃*
    (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) := MulEquiv.refl _

end Field.absoluteGaloisGroup
