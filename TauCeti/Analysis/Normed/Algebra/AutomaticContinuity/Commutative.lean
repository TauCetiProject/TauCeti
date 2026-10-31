/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character
public import TauCeti.Analysis.Normed.Operator.SeparatingSpace

/-!
# Automatic continuity into commutative semisimple Banach algebras

**Šilov's theorem**: every homomorphism `θ : A → B` from a complex Banach algebra into a
commutative semisimple complex Banach algebra is continuous. Neither algebra needs a unit, and
`θ` is assumed neither continuous nor unital.

More precisely, for an arbitrary commutative complex Banach algebra `B` the separating space of
`θ` lies in the Jacobson radical of `B`. Indeed every character `φ` of `B` is continuous, and so
is the character `φ ∘ θ` of `A`, so `φ` kills the separating space of `θ`. In a commutative
complex Banach algebra the elements killed by every character form the radical. When `B` is
semisimple the separating space therefore vanishes, and `θ` is continuous by the closed graph
theorem.

Commutativity of `B` cannot simply be dropped: for noncommutative semisimple targets the
analogous theorem needs `θ` to be surjective.

## Main results

* `NonUnitalAlgHom.separatingSpace_le_nonUnitalJacobsonSubmodule`: the separating space of a
  homomorphism into a commutative complex Banach algebra lies in its radical.
* `NonUnitalAlgHom.continuous_of_nonUnitalJacobson_eq_bot`: Šilov's theorem for a semisimple
  commutative target, possibly without unit.
* `NonUnitalAlgHom.continuous_of_jacobson_eq_bot`: Šilov's theorem for a semisimple commutative
  unital target, with the radical `Ring.jacobson`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*: Šilov's theorem on homomorphisms into
  commutative semisimple Banach algebras,, and the separating space of a homomorphism.
-/

public section

namespace NonUnitalAlgHom

open TauCeti

variable {A B : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

section NonUnital

variable [NonUnitalNormedCommRing B] [NormedSpace ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] [CompleteSpace B]

/-- The separating space of a homomorphism `θ : A → B` of complex Banach algebras, not assumed
continuous, lies in the Jacobson radical of `B` when `B` is commutative. -/
theorem separatingSpace_le_nonUnitalJacobsonSubmodule (θ : A →ₙₐ[ℂ] B) :
    (θ : A →ₗ[ℂ] B).separatingSpace ≤ nonUnitalJacobsonSubmodule ℂ B := by
  intro y hy
  rw [mem_nonUnitalJacobsonSubmodule,
    mem_nonUnitalJacobson_iff_forall_nonUnitalAlgHom_apply_eq_zero]
  intro φ
  -- The characters `φ` of `B` and `φ ∘ θ` of `A` are continuous, so `φ` kills the separating
  -- space of `θ`.
  have h := (θ : A →ₗ[ℂ] B).separatingSpace_le_ker_of_continuous_comp
    ⟨(φ : B →ₗ[ℂ] ℂ), map_continuous φ⟩ (map_continuous (φ.comp θ)) hy
  simpa using h

/-- **Šilov's theorem.** Every homomorphism from a complex Banach algebra into a commutative
semisimple complex Banach algebra is continuous. Neither algebra needs a unit. -/
theorem continuous_of_nonUnitalJacobson_eq_bot (θ : A →ₙₐ[ℂ] B)
    (hB : nonUnitalJacobson ℂ B = ⊥) : Continuous θ := by
  refine ((θ : A →ₗ[ℂ] B).continuous_iff_separatingSpace_eq_bot).mpr <|
    eq_bot_iff.mpr fun y hy => ?_
  have hy := θ.separatingSpace_le_nonUnitalJacobsonSubmodule hy
  rw [mem_nonUnitalJacobsonSubmodule, hB, TwoSidedIdeal.mem_bot] at hy
  exact (Submodule.mem_bot ℂ).mpr hy

end NonUnital

/-- **Šilov's theorem** for a unital target. Every homomorphism, not necessarily unital, from a
complex Banach algebra into a commutative unital complex Banach algebra with zero Jacobson radical
is continuous. -/
theorem continuous_of_jacobson_eq_bot [NormedCommRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (θ : A →ₙₐ[ℂ] B) (hB : Ring.jacobson B = ⊥) : Continuous θ :=
  θ.continuous_of_nonUnitalJacobson_eq_bot <| by
    ext y
    simp [hB]

end NonUnitalAlgHom
