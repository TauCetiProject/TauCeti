/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of modules under scalar pullback

For a surjective ring homomorphism `f : S →+* R`, an `R`-module `M` is finitely generated over `S`
under scalar pullback `Module.compHom M f` if and only if it is finitely generated over `R`.

## Main results

* `Module.Finite.compHom_iff_of_surjective`: scalar pullback along a surjective ring homomorphism
  preserves and reflects `Module.Finite`.
* `Module.Finite.compHom_of_surjective`: scalar pullback along a surjective ring homomorphism
  preserves `Module.Finite`.
-/

public section

namespace Module.Finite

/-- Scalar pullback along a surjective ring homomorphism `f : S →+* R` preserves and reflects
`Module.Finite`. -/
theorem compHom_iff_of_surjective {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] (f : S →+* R) (hf : Function.Surjective f) :
    (letI : Module S M := Module.compHom M f; Module.Finite S M) ↔ Module.Finite R M := by
  let : Module S M := Module.compHom M f
  have : RingHomSurjective f := ⟨hf⟩
  exact LinearMap.finite_iff_of_bijective
    ({ toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      M →ₛₗ[f] M)
    Function.bijective_id

/-- If `M` is a finite `R`-module and `f : S →+* R` is surjective, then `M` is a finite `S`-module
under scalar pullback `Module.compHom M f`. -/
theorem compHom_of_surjective {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] (f : S →+* R) (hf : Function.Surjective f) :
    letI : Module S M := Module.compHom M f
    Module.Finite S M :=
  (compHom_iff_of_surjective f hf).2 inferInstance

end Module.Finite
