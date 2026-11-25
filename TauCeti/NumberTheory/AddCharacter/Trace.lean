/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.Trace.Defs
import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# Additive characters composed with traces along a tower

For a tower `F ⊆ K ⊆ L` and an additive character `ψ` of `F`, the character `ψ ∘ Tr_{L/F}` of `L`
is obtained in two steps, as `(ψ ∘ Tr_{K/F}) ∘ Tr_{L/K}`. Over finite fields, with `ψ` a character
of the prime field, this says that the characters `ψ_k = ψ ∘ Tr_{k/𝔽_p}` used by the finite
Fourier transform are compatible with extension of the base field: `ψ_{k'} = ψ_k ∘ Tr_{k'/k}`.

## Main results

* `AddChar.compAddMonoidHom_trace_compAddMonoidHom_trace`: for a tower of free extensions
  `F ⊆ K ⊆ L`, the character `ψ ∘ Tr_{L/F}` is `(ψ ∘ Tr_{K/F}) ∘ Tr_{L/K}`.
-/

public section

namespace AddChar

/-- **Transitivity of trace characters.** For a tower `F ⊆ K ⊆ L` of free extensions, the
character `ψ ∘ Tr_{L/F}` of `L` is `(ψ ∘ Tr_{K/F}) ∘ Tr_{L/K}`. -/
@[simp]
theorem compAddMonoidHom_trace_compAddMonoidHom_trace {F K L M : Type*} [CommRing F] [CommRing K]
    [CommRing L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [Module.Free F K] [Module.Free K L] [Monoid M] (ψ : AddChar F M) :
    (ψ.compAddMonoidHom (Algebra.trace F K).toAddMonoidHom).compAddMonoidHom
        (Algebra.trace K L).toAddMonoidHom =
      ψ.compAddMonoidHom (Algebra.trace F L).toAddMonoidHom := by
  ext x
  simp [TauCeti.Algebra.trace_trace_of_free]

end AddChar
