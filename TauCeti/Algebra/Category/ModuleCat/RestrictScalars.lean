/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation and projectivity under restriction of scalars

Restriction of scalars along a ring homomorphism `f : R →+* S` keeps the underlying abelian
group of a module and only changes which ring acts on it. This file records when the two
finiteness properties defining `K₀(proj R)` and `G₀(mod R)` survive it.

* Along a **surjective** ring homomorphism, finite generation is preserved and reflected: every
  scalar of `S` is the image of a scalar of `R`, so the `S`-span and the `R`-span of a set
  coincide.
* Along a ring **isomorphism**, projectivity is preserved and reflected: the identity of the
  module is then a semilinear equivalence between the two module structures.

The API is dot notation on the ring homomorphism, respectively the ring isomorphism: use
`f.finite_restrictScalars_iff hf M` and `e.projective_restrictScalars_iff M`.

## Main definitions

* `RingHom.restrictScalarsSemilinearMap`: the identity of a module, as a semilinear map from its
  restriction of scalars.

## Main results

* `RingHom.finite_restrictScalars_iff` and `RingHom.isFG_restrictScalars_iff`: finite generation
  is invariant under restriction of scalars along a surjective ring homomorphism.
* `RingEquiv.projective_restrictScalars_iff`: projectivity is invariant under restriction of
  scalars along a ring isomorphism.
-/

public section

open CategoryTheory

universe v u₁ u₂

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

namespace RingHom

/-- The identity map of an `S`-module `M`, as an `f`-semilinear map from `M` with scalars
restricted along `f : R →+* S` to `M` itself. -/
def restrictScalarsSemilinearMap (f : R →+* S) (M : ModuleCat.{v} S) :
    (ModuleCat.restrictScalars f).obj M →ₛₗ[f] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' r m := ModuleCat.restrictScalars.smul_def f r m

@[simp]
theorem restrictScalarsSemilinearMap_apply (f : R →+* S) (M : ModuleCat.{v} S)
    (m : (ModuleCat.restrictScalars f).obj M) :
    f.restrictScalarsSemilinearMap M m = m :=
  (rfl)

/-- **Finite generation along a surjective ring homomorphism.** Restricting scalars along a
surjective ring homomorphism preserves and reflects finite generation: every scalar of `S` is the
image of a scalar of `R`, so the two spans of a set agree. -/
theorem finite_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) ↔ Module.Finite S M :=
  haveI : RingHomSurjective f := ⟨hf⟩
  LinearMap.finite_iff_of_bijective (f.restrictScalarsSemilinearMap M)
    Function.bijective_id

/-- Restricting scalars along a surjective ring homomorphism preserves and reflects the object
property of being finitely generated. -/
theorem isFG_restrictScalars_iff (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{v} S) :
    ModuleCat.isFG R ((ModuleCat.restrictScalars f).obj M) ↔ ModuleCat.isFG S M := by
  rw [ModuleCat.isFG_iff, ModuleCat.isFG_iff, f.finite_restrictScalars_iff hf]

end RingHom

namespace RingEquiv

/-- **Projectivity along a ring isomorphism.** Restricting scalars along a ring isomorphism
preserves and reflects projectivity: the identity is a semilinear equivalence between the two
module structures, and projectivity transports along semilinear equivalences. -/
theorem projective_restrictScalars_iff (e : R ≃+* S) (M : ModuleCat.{v} S) :
    Module.Projective R ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔
      Module.Projective S M := by
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let φ : (ModuleCat.restrictScalars e.toRingHom).obj M ≃ₛₗ[e.toRingHom] M :=
    { e.toRingHom.restrictScalarsSemilinearMap M with
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact ⟨fun _ ↦ Module.Projective.of_equiv φ, fun _ ↦ Module.Projective.of_equiv φ.symm⟩

end RingEquiv
