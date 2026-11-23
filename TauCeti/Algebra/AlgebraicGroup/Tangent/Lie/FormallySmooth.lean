/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.FormallySmooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# The Lie differential of a formally smooth or formally étale morphism

A formally smooth morphism of affine monoid schemes induces a surjective Lie algebra
morphism on tangent spaces at the identity, with values in any commutative coefficient
algebra. For affine groups, this gives the surjectivity needed for the Lie-dimension
formula for a scheme-theoretic kernel. A formally étale morphism induces a bijective one.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.e, Proposition 1.63, for the relation between
  smoothness, differential surjectivity, and kernel dimensions for group varieties;
  §10.b, 10.6, and Appendix A.51 for the dual-number description of Lie and tangent spaces.
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

/-- The Lie differential of a formally étale affine monoid morphism is bijective. -/
theorem _root_.BialgHom.derivationCompLieHom_bijective_of_formallyEtale (φ : A' →ₐc[R] A)
    (hφ : φ.toAlgHom.toRingHom.FormallyEtale) :
    Function.Bijective (derivationCompLieHom (B := B) φ) := by
  let _ := φ.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FormallyEtale A' A := hφ
  rw [funext (derivationCompLieHom_apply (B := B) φ)]
  exact ⟨φ.derivationComp_injective_of_formallyUnramified
      (inferInstance : Algebra.FormallyUnramified A' A),
    derivationComp_surjective_of_formallySmooth φ (inferInstance : Algebra.FormallySmooth A' A)⟩

end TauCeti
