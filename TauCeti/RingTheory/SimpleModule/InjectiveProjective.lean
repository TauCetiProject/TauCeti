/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Modules over a semisimple ring satisfy Baer's criterion

Mathlib proves that every module over a semisimple ring is injective
(`Module.injective_of_isSemisimpleRing`). Converting that into Baer's criterion `Module.Baer R M`
through `Module.Baer.of_injective` costs a smallness hypothesis on the ring, which the criterion
does not need: an ideal of a semisimple ring is a direct summand of the ring, and a linear map on
the ideal extends to the ring by composing with the projection onto that summand. This file records
the criterion in that generality; it is what makes `Hom(-, M)` exact for every module `M` over a
field, such as `H²(G, 𝔽_p)` over `𝔽_p`.

## Main results

* `Module.Baer.of_isSemisimpleRing`: every module over a semisimple ring satisfies Baer's criterion.
-/

public section

namespace TauCeti

universe u v

/-- **Every module over a semisimple ring satisfies Baer's criterion.** An ideal `I` of a
semisimple ring `R` has a complement `J`, and a linear map `I → M` extends to `R` by composing with
the projection `R → I` along `J`. Unlike `Module.Baer.of_injective` applied to
`Module.injective_of_isSemisimpleRing`, this needs no smallness hypothesis on `R`. -/
theorem _root_.Module.Baer.of_isSemisimpleRing (R : Type u) (M : Type v) [Ring R]
    [IsSemisimpleRing R] [AddCommGroup M] [Module R M] : Module.Baer R M := fun I g ↦ by
  obtain ⟨J, hJ⟩ := exists_isCompl I
  exact ⟨g ∘ₗ Submodule.projectionOnto I J hJ, fun x hx ↦
    congrArg g (Submodule.projectionOnto_apply_left hJ ⟨x, hx⟩)⟩

end TauCeti
