/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.Lie.OfAssociative

/-!
# Finite associative targets for Lie representations

An injective Lie map from `L` to a finite-dimensional associative algebra `A` gives a faithful
finite-dimensional representation: let `L` act on `A` by left multiplication. Conversely, a
faithful finite-dimensional representation extends uniquely to an algebra homomorphism from the
universal enveloping algebra whose restriction to `L` remains injective.

Thus existence of a faithful finite-dimensional representation is equivalent to existence of a
finite-dimensional associative target of the universal enveloping algebra that separates the
canonical copy of `L`. This interface lets constructions of finite quotients of `U(L)` produce
representations without repeating the left-regular argument.

## Main results

* `TauCeti.ado_of_finiteAssociativeEmbedding`: an associative embedding gives a faithful
  finite-dimensional representation.
* `TauCeti.ado_of_finiteEnvelopingTarget`: a finite target of the enveloping algebra gives such a
  representation.
* `TauCeti.faithfulRepresentation_iff_finiteEnvelopingTarget`: the finite-target equivalence.
-/

public section

universe u

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) [Field K]
variable (L : Type u) [LieRing L] [LieAlgebra K L]

/-- An injective Lie map into a finite-dimensional associative algebra yields a faithful
finite-dimensional representation, obtained by letting the Lie algebra act by left
multiplication. -/
theorem ado_of_finiteAssociativeEmbedding {A : Type u} [Ring A] [Algebra K A]
    [FiniteDimensional K A] (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  exact ⟨A, inferInstance, inferInstance, inferInstance, f.leftRegularRep,
    (LieHom.leftRegularRep_injective_iff f).2 hf⟩

/-- A finite-dimensional associative target of the universal enveloping algebra which separates
the canonical copy of `L` yields a faithful finite-dimensional representation. -/
theorem ado_of_finiteEnvelopingTarget {A : Type u} [Ring A] [Algebra K A]
    [FiniteDimensional K A] (q : UniversalEnvelopingAlgebra K L →ₐ[K] A)
    (hq : Function.Injective
      (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι K x))) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  exact ado_of_finiteAssociativeEmbedding K L
    ((q : UniversalEnvelopingAlgebra K L →ₗ⁅K⁆ A).comp
      (UniversalEnvelopingAlgebra.ι K)) hq

/-- A Lie algebra has a faithful finite-dimensional representation if and only if its universal
enveloping algebra has a finite-dimensional associative target whose restriction to the canonical
copy of the Lie algebra is injective. -/
theorem faithfulRepresentation_iff_finiteEnvelopingTarget :
    (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ) ↔
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (_ : FiniteDimensional K A)
        (q : UniversalEnvelopingAlgebra K L →ₐ[K] A),
        Function.Injective
          (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι K x)) := by
  constructor
  · rintro ⟨V, _, _, _, ρ, hρ⟩
    refine ⟨Module.End K V, inferInstance, inferInstance, inferInstance,
      UniversalEnvelopingAlgebra.lift K ρ, ?_⟩
    intro x y hxy
    apply hρ
    simpa only [UniversalEnvelopingAlgebra.lift_ι_apply] using hxy
  · rintro ⟨A, _, _, _, q, hq⟩
    exact ado_of_finiteEnvelopingTarget K L q hq

end TauCeti
