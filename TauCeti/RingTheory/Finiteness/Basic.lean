/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of modules under scalar pullback and change of rings

For a surjective ring homomorphism `f : S →+* R`, an `R`-module `M` is finitely generated over `S`
under scalar pullback `Module.compHom M f` if and only if it is finitely generated over `R`.
Similarly, a surjective ring homomorphism `f : R →+* S` makes `S` a finitely generated `R`-module
via `f.toModule`, including the factor projections of a binary product ring `R × S` and their
opposites.

## Main results

* `Module.Finite.compHom_iff_of_surjective`: scalar pullback along a surjective ring homomorphism
  preserves and reflects `Module.Finite`.
* `Module.Finite.compHom_of_surjective`: scalar pullback along a surjective ring homomorphism
  preserves `Module.Finite`.
* `RingHom.finite_toModule_of_surjective`: a surjective ring homomorphism `f : R →+* S` makes `S`
  finitely generated over `R`.
* `RingHom.finite_fst`, `RingHom.finite_snd`, `RingHom.finite_op_fst`, `RingHom.finite_op_snd`:
  factor projections of `R × S` (and their opposites) make each factor finitely generated.
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

namespace RingHom

/-- If `f : R →+* S` is surjective, then `S` is finitely generated as an `R`-module through `f`. -/
theorem finite_toModule_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) :
    letI := f.toModule; Module.Finite R S :=
  letI := f.toModule
  Module.Finite.of_surjective ({ f with map_smul' := f.map_mul } : R →ₗ[R] S) hf

/-- `R` is finitely generated as an `(R × S)`-module via `RingHom.fst R S`. -/
theorem finite_fst (R S : Type*) [Ring R] [Ring S] :
    letI := (fst R S).toModule; Module.Finite (R × S) R :=
  finite_toModule_of_surjective _ Prod.fst_surjective

/-- `S` is finitely generated as an `(R × S)`-module via `RingHom.snd R S`. -/
theorem finite_snd (R S : Type*) [Ring R] [Ring S] :
    letI := (snd R S).toModule; Module.Finite (R × S) S :=
  finite_toModule_of_surjective _ Prod.snd_surjective

/-- `Rᵐᵒᵖ` is finitely generated as an `(R × S)ᵐᵒᵖ`-module via `RingHom.op (RingHom.fst R S)`. -/
theorem finite_op_fst (R S : Type*) [Ring R] [Ring S] :
    letI := (op (fst R S)).toModule; Module.Finite (R × S)ᵐᵒᵖ Rᵐᵒᵖ :=
  finite_toModule_of_surjective _ fun a ↦ ⟨MulOpposite.op (a.unop, 0), rfl⟩

/-- `Sᵐᵒᵖ` is finitely generated as an `(R × S)ᵐᵒᵖ`-module via `RingHom.op (RingHom.snd R S)`. -/
theorem finite_op_snd (R S : Type*) [Ring R] [Ring S] :
    letI := (op (snd R S)).toModule; Module.Finite (R × S)ᵐᵒᵖ Sᵐᵒᵖ :=
  finite_toModule_of_surjective _ fun b ↦ ⟨MulOpposite.op (0, b.unop), rfl⟩

end RingHom
