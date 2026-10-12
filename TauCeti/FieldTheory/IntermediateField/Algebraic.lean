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
is finite over `F`: it is `F`-isomorphic to its image under `g`, which is contained in `M`. -/
instance finiteDimensional_comap (M : IntermediateField F E) [FiniteDimensional F M]
    (g : L →ₐ[F] E) : FiniteDimensional F (M.comap g) :=
  have hle : (M.comap g).map g ≤ M := IntermediateField.map_le_iff_le_comap.mpr le_rfl
  Module.Finite.of_injective
    (((IntermediateField.inclusion hle).comp
      (IntermediateField.equivMap (M.comap g) g).toAlgHom).toLinearMap)
    ((IntermediateField.inclusion_injective hle).comp
      (IntermediateField.equivMap (M.comap g) g).injective)

end IntermediateField
