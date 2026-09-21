/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.FormallySmooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Surjectivity of the Lie differential of a formally smooth morphism

A formally smooth morphism of affine monoid schemes induces a surjective Lie algebra
morphism on tangent spaces at the identity, with values in any commutative coefficient
algebra. For affine groups, this gives the surjectivity needed for the Lie-dimension
formula for a scheme-theoretic kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

namespace TauCeti

variable {R A A' B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R A'] [CommRing B] [Algebra R B]

/-- The Lie differential of a formally smooth affine monoid morphism is surjective. -/
theorem derivationCompLieHom_surjective_of_formallySmooth (φ : A' →ₐc[R] A)
    (hφ : φ.toAlgHom.toRingHom.FormallySmooth) :
    Function.Surjective (derivationCompLieHom (B := B) φ) := by
  intro d
  obtain ⟨e, he⟩ := derivationComp_surjective_of_formallySmooth (B := B) φ hφ d
  exact ⟨e, (derivationCompLieHom_apply φ e).trans he⟩

end TauCeti
