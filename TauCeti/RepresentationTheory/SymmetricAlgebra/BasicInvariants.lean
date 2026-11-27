/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# Basic invariants

`Representation.IsBasicInvariants` says that a family of homogeneous invariants freely generates
the invariant algebra, using Mathlib's `MvPolynomial.aeval`.
`Representation.IsBasicInvariants.aevalEquiv` gives the resulting polynomial presentation, and
`Representation.IsBasicInvariants.algebraicIndependent` gives algebraic independence over a ring.

For a representation on `V`, the contragredient gives formal invariants in `Sym(V*)`. Pointwise
evaluation on `V` can identify distinct formal invariants, for instance over finite fields.

See L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2.
-/

public section

open MvPolynomial TauCeti.SymmetricAlgebra

namespace Representation

variable {R G M ι : Type*}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The family `f` is a system of basic invariants of degrees `d` if each `f i` is homogeneous of
degree `d i` and evaluation at `f` identifies the polynomial algebra with `Sym(M)^G`. -/
structure IsBasicInvariants (ρ : Representation R G M)
    (f : ι → ρ.symmetricAlgebraInvariants) (d : ι → ℕ) : Prop where
  /-- Each generator belongs to the specified homogeneous piece. -/
  homogeneous (i : ι) : (f i : SymmetricAlgebra R M) ∈ homogeneousSubmodule R M (d i)
  /-- Polynomial evaluation at the generators is bijective. -/
  bijective_aeval : Function.Bijective (aeval (R := R) f)

variable {ρ : Representation R G M} {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}

/-- A system of basic invariants gives a polynomial presentation of the invariant algebra. -/
noncomputable def IsBasicInvariants.aevalEquiv (h : ρ.IsBasicInvariants f d) :
    MvPolynomial ι R ≃ₐ[R] ρ.symmetricAlgebraInvariants :=
  AlgEquiv.ofBijective (aeval f) h.bijective_aeval

/-- The polynomial presentation evaluates at the given system of basic invariants. -/
@[simp]
theorem IsBasicInvariants.aevalEquiv_toAlgHom (h : ρ.IsBasicInvariants f d) :
    h.aevalEquiv.toAlgHom = aeval f :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- On a polynomial, the presentation is evaluation at the given basic invariants. -/
@[simp]
theorem IsBasicInvariants.aevalEquiv_apply (h : ρ.IsBasicInvariants f d) (p : MvPolynomial ι R) :
    h.aevalEquiv p = aeval f p :=
  AlgEquiv.ofBijective_apply _ _ _

/-- The polynomial presentation sends each variable to the corresponding basic invariant. -/
theorem IsBasicInvariants.aevalEquiv_X (h : ρ.IsBasicInvariants f d) (i : ι) :
    h.aevalEquiv (X i) = f i := by
  rw [h.aevalEquiv_apply, aeval_X]

end CommSemiring

/-- A system of basic invariants over a commutative ring is algebraically independent. -/
theorem IsBasicInvariants.algebraicIndependent [CommRing R] [Monoid G] [AddCommMonoid M]
    [Module R M] {ρ : Representation R G M} {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}
    (h : ρ.IsBasicInvariants f d) : AlgebraicIndependent R f :=
  algebraicIndependent_iff_injective_aeval.mpr h.bijective_aeval.injective

end Representation
