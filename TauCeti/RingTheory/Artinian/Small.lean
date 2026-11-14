/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Artin algebras over a small base ring

Let `R` be a commutative Artinian ring and `A` an Artin `R`-algebra, an `R`-algebra that is
finitely generated as an `R`-module. Then `A` is also an Artin algebra over the image
`R ⧸ ker (R → A)` of `R` in `A`, and this ring is small in the universe of `A`. So a construction
that needs the base ring to be small in the universe of `A`, such as the Matlis dual with values in
an injective hull of `R ⧸ J(R)` taken in that universe, can be carried out over this image.

## Main results

* `TauCeti.exists_small_isArtinianRing_algebra`: an Artin algebra is an Artin algebra over a
  commutative Artinian ring that is small in its universe.
-/

public section

namespace TauCeti

universe u v

/-- **Artin algebras over a small base ring.** An Artin `R`-algebra `A` is an Artin algebra over a
commutative Artinian ring `R'` in the universe of `R` that is small in the universe of `A`, namely
the image `R ⧸ ker (R → A)` of `R` in `A`. -/
theorem exists_small_isArtinianRing_algebra (R : Type u) [CommRing R] [IsArtinianRing R]
    (A : Type v) [Ring A] [Algebra R A] [Module.Finite R A] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsArtinianRing R') (_ : Algebra R' A)
      (_ : Module.Finite R' A), Small.{v} R' := by
  let g := RingHom.kerLift (algebraMap R A)
  let _ : Algebra (R ⧸ RingHom.ker (algebraMap R A)) A := g.toAlgebra' fun c x ↦ by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    simpa [g] using Algebra.commutes c x
  have : IsScalarTower R (R ⧸ RingHom.ker (algebraMap R A)) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by simp [g, RingHom.algebraMap_toAlgebra']
  exact ⟨R ⧸ RingHom.ker (algebraMap R A), inferInstance, inferInstance, inferInstance,
    Module.Finite.of_restrictScalars_finite R _ A, small_of_injective (RingHom.kerLift_injective _)⟩

end TauCeti
