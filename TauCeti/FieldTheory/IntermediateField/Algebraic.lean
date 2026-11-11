/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Finite intermediate fields under inverse images

The inverse image of a finite intermediate field under an algebra map is finite-dimensional.
This lets finite subextensions be transported between ambient extensions, for example when
comparing their Krull topologies.
-/

public section

namespace IntermediateField

variable {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]

/-- The preimage of a finite intermediate field `M` of `E/F` under an `F`-algebra map `g` into `E`
is finite over `F`: restricting `g` embeds it `F`-linearly into `M`. -/
instance finiteDimensional_comap (M : IntermediateField F E) [FiniteDimensional F M]
    (g : L →ₐ[F] E) : FiniteDimensional F (M.comap g) :=
  .of_injective ((g.comp (val _)).codRestrict M.toSubalgebra fun x ↦ x.2).toLinearMap
    (RingHom.injective _)

end IntermediateField
