/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.RingHom
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

/-!
# Graded functoriality of symmetric algebras

A linear map induces a degree-preserving map of symmetric algebras. The bundled graded
map allows linear equivalences to act on the projective spectrum of the symmetric algebra.
The construction uses `SymmetricAlgebra.map` and the grading by powers of the generator range.
-/

public section

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

universe u v w x

variable (R : Type u) [CommSemiring R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- The degree-preserving ring map of symmetric algebras induced by a linear map. -/
noncomputable def gradedMap (f : M →ₗ[R] N) :
    homogeneousSubmodule R M →+*ᵍ homogeneousSubmodule R N where
  __ := (map R f).toRingHom
  map_mem := TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule f

/-- The underlying ring homomorphism is the ordinary symmetric-algebra map. -/
@[simp]
theorem gradedMap_toRingHom (f : M →ₗ[R] N) :
    (gradedMap R f).toRingHom = (map R f).toRingHom := (rfl)

/-- The graded map agrees with the symmetric-algebra map on every element. -/
@[simp]
theorem gradedMap_apply (f : M →ₗ[R] N) (a : SymmetricAlgebra R M) :
    gradedMap R f a = map R f a := (rfl)

/-- The identity linear map induces the identity graded map. -/
@[simp]
theorem gradedMap_id : gradedMap R (LinearMap.id (R := R) (M := M)) =
    GradedRingHom.id (homogeneousSubmodule R M) := by
  ext a
  simp

/-- Composition of linear maps induces composition of graded symmetric-algebra maps. -/
@[simp]
theorem gradedMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (gradedMap R g).comp (gradedMap R f) = gradedMap R (g.comp f) := by
  ext a
  exact AlgHom.congr_fun (map_comp_map R f g) a

/-- Every linear endomorphism fixes the degree-zero part of its symmetric algebra. -/
@[simp]
theorem gradedMap_gradedZeroRingHom (f : M →ₗ[R] M) :
    (gradedMap R f).gradedZeroRingHom = RingHom.id _ := by
  ext a
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp
    (by simpa [homogeneousSubmodule] using a.property)
  simp only [GradedRingHom.gradedZeroRingHom_apply_coe, gradedMap_apply, RingHom.id_apply]
  rw [← hr, AlgHom.commutes]

end SymmetricAlgebra
