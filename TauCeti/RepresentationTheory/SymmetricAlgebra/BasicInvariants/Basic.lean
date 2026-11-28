/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.Algebra.MvPolynomial.Eval

/-!
# Basic invariants

`Representation.IsBasicInvariants` says that a family of homogeneous invariants freely generates
the invariant algebra, using Mathlib's `MvPolynomial.aeval`.
`Representation.IsBasicInvariants.aevalEquiv` gives the resulting polynomial presentation, and
`Representation.IsBasicInvariants.algebraicIndependent` gives algebraic independence over a ring.
`Representation.isBasicInvariants_iff` characterizes a system over a ring in terms of homogeneity,
algebraic independence and generation by `Algebra.adjoin`.

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

/-- The inverse presentation recovers a polynomial from its value at the basic invariants. -/
@[simp]
theorem IsBasicInvariants.aevalEquiv_symm_aeval (h : ρ.IsBasicInvariants f d)
    (p : MvPolynomial ι R) : h.aevalEquiv.symm (aeval f p) = p := by
  rw [← h.aevalEquiv_apply, AlgEquiv.symm_apply_apply]

/-- Evaluating the inverse polynomial presentation recovers the invariant. -/
@[simp]
theorem IsBasicInvariants.aeval_aevalEquiv_symm (h : ρ.IsBasicInvariants f d)
    (y : ρ.symmetricAlgebraInvariants) : aeval f (h.aevalEquiv.symm y) = y := by
  rw [← h.aevalEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The inverse presentation sends a basic invariant to its corresponding variable. -/
@[simp]
theorem IsBasicInvariants.aevalEquiv_symm_apply_generator (h : ρ.IsBasicInvariants f d) (i : ι) :
    h.aevalEquiv.symm (f i) = X i := by
  rw [← aeval_X (R := R) f i, h.aevalEquiv_symm_aeval]

end CommSemiring

/-- A system of basic invariants over a commutative ring is algebraically independent. -/
theorem IsBasicInvariants.algebraicIndependent [CommRing R] [Monoid G] [AddCommMonoid M]
    [Module R M] {ρ : Representation R G M} {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}
    (h : ρ.IsBasicInvariants f d) : AlgebraicIndependent R f :=
  algebraicIndependent_iff_injective_aeval.mpr h.bijective_aeval.injective

/-- Over a commutative ring, basic invariants are precisely homogeneous, algebraically independent
generators of the invariant algebra, with the specified degrees. -/
theorem isBasicInvariants_iff [CommRing R] [Monoid G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ} :
    ρ.IsBasicInvariants f d ↔
      (∀ i, (f i : SymmetricAlgebra R M) ∈ homogeneousSubmodule R M (d i)) ∧
        AlgebraicIndependent R f ∧ Algebra.adjoin R (Set.range f) = ⊤ := by
  rw [algebraicIndependent_iff_injective_aeval, ← aeval_surjective_iff_adjoin_range_eq_top]
  exact ⟨fun h ↦ ⟨h.homogeneous, h.bijective_aeval⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end Representation
