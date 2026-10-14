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

More generally, a linear map from `M` into the degree-one part of a graded algebra `A` lifts to a
degree-preserving map `Sym M → A`, which is surjective when the image generates `A`. This presents
a graded algebra generated in degree one as a graded quotient of a symmetric algebra, the algebraic
form of an embedding of its projective spectrum into a projective space.
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

section GradedLift

variable {A : Type*} [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [SetLike.GradedMonoid 𝒜]

/-- The degree-preserving ring map out of a symmetric algebra induced by a linear map into the
degree-one part of a graded algebra: the lift of `f`, which sends a product of `n` generators to a
product of `n` elements of degree one. -/
noncomputable def gradedLift (f : M →ₗ[R] 𝒜 1) : homogeneousSubmodule R M →+*ᵍ 𝒜 where
  __ := (lift ((𝒜 1).subtype ∘ₗ f)).toRingHom
  map_mem {_ _} hx := by
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r => simpa using SetLike.algebraMap_mem_graded 𝒜 r
    | add x y _ _ _ hx hy => simpa using add_mem hx hy
    | mem_mul m hm i x _ ih =>
      obtain ⟨y, rfl⟩ := hm
      simpa [add_comm 1 i] using SetLike.mul_mem_graded (f y).2 ih

/-- The graded lift agrees with the symmetric-algebra lift on every element. -/
@[simp]
theorem gradedLift_apply (f : M →ₗ[R] 𝒜 1) (a : SymmetricAlgebra R M) :
    gradedLift R 𝒜 f a = lift ((𝒜 1).subtype ∘ₗ f) a := (rfl)

/-- The graded lift sends a generator `m` to `f m`. -/
theorem gradedLift_ι (f : M →ₗ[R] 𝒜 1) (m : M) : gradedLift R 𝒜 f (ι R M m) = f m := by
  simp

/-- The graded lift is surjective when the degree-one elements `f m` generate the target as an
`R`-algebra. -/
theorem gradedLift_surjective {f : M →ₗ[R] 𝒜 1}
    (hf : Algebra.adjoin R (Set.range fun m ↦ (f m : A)) = ⊤) :
    Function.Surjective (gradedLift R 𝒜 f) := by
  -- the range of the lift is a subalgebra containing every generator `f m`
  refine (AlgHom.range_eq_top (lift ((𝒜 1).subtype ∘ₗ f))).mp (top_le_iff.mp ?_)
  rw [← hf, Algebra.adjoin_le_iff]
  rintro _ ⟨m, rfl⟩
  exact ⟨ι R M m, by simp⟩

end GradedLift

end SymmetricAlgebra
