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
does not need: the inclusion of an ideal into a semisimple ring has a complemented range, so
`IsSemisimpleModule.extension_property` extends every linear map on the ideal to the ring. This
file records the criterion in that generality; it is what makes `Hom(-, M)` exact for every module
`M` over a field, such as `H²(G, 𝔽_p)` over `𝔽_p`.

## Main results

* `Module.Baer.of_isSemisimpleRing`: every module over a semisimple ring satisfies Baer's criterion.
-/

public section

namespace Module.Baer

/-- **Every module over a semisimple ring satisfies Baer's criterion.** Unlike
`Module.Baer.of_injective` applied to `Module.injective_of_isSemisimpleRing`, this needs no
smallness hypothesis on `R`. -/
theorem of_isSemisimpleRing (R M : Type*) [Ring R] [IsSemisimpleRing R] [AddCommGroup M]
    [Module R M] : Module.Baer R M := fun I g ↦
  have ⟨g', hg'⟩ := IsSemisimpleModule.extension_property I.subtype I.injective_subtype g
  ⟨g', fun x hx ↦ LinearMap.congr_fun hg' ⟨x, hx⟩⟩

end Module.Baer
