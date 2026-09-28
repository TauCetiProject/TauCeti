/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Fixing subgroups of conjugate embeddings

Two embeddings of a finite separable extension into a separable closure differ by an
automorphism of that closure. Their images are therefore conjugate intermediate fields, and
the Galois correspondence carries them to conjugate open subgroups of the absolute Galois
group. This is the subgroup comparison used when transporting restriction, corestriction,
and the Evens norm between different choices of embedding.

The automorphism carrying one embedding to the other comes from the transitive action on
embeddings in `TauCeti.FieldTheory.Normal.Embeddings`. Conjugacy of the fixing subgroups
follows from the corresponding stabilizer conjugacy theorem.
-/

public section

namespace TauCeti

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

/-- The open subgroups of `G_K` fixing two embedded copies of a finite extension `L/K`
are conjugate. The conjugating automorphism extends the natural `K`-algebra isomorphism
between the two copies of `L`. -/
theorem galoisSubgroup_conj [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) :
    ∃ g : AbsoluteGaloisGroup K,
      (galoisSubgroup K L τ).toSubgroup =
        (galoisSubgroup K L σ).toSubgroup.map (MulAut.conj g).toMonoidHom := by
  simpa only [galoisSubgroup_toSubgroup] using
    AlgHom.fixingSubgroup_fieldRange_conj σ τ

end TauCeti
