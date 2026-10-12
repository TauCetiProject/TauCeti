/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Decomposition

/-!
# Tensor multiplicities of irreducible modules

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system.
The **tensor multiplicity** `TauCeti.tensorMultiplicity b lam mu nu` is the dimension of the space
of morphisms `L(nu) →ₗ⁅K,L⁆ L(lam) ⊗ L(mu)`. For dominant integral `lam` and `mu` the tensor
product is a finite-dimensional `L`-module, so Weyl's theorem decomposes it into irreducibles, and
at a `nu` with `L(nu)` nonzero, hence irreducible, that dimension is the number of copies of
`L(nu)` in the decomposition, the structure constant `c^nu_{lam mu}`. The definition itself, and
the lemmas reading irreducibility off a nonzero multiplicity, ask only for a triangularizable
Cartan subalgebra; algebraic closure enters with the character identity, which calls on Weyl's
complete reducibility theorem.

The theorem about it is the character identity

`ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)`,

which combines two facts already in place: formal characters are multiplicative on tensor products
(`TauCeti.formalCharacter_tensor`), and the character of a finite-dimensional module is the
multiplicity-weighted sum of the irreducible characters
(`TauCeti.formalCharacter_eq_finsum_isotypicMultiplicity_smul`). It is what makes the tensor
multiplicities computable from characters, and the identity a Pieri or Littlewood-Richardson rule
evaluates.

Every `L(nu)` is irreducible, the Verma module `M(nu)` being nonzero
(`TauCeti.vermaGenerator_ne_zero`), so the identity is a statement about honest irreducibles, and
it never degenerates to `0 = 0`: some `c^nu_{lam mu}` is nonzero
(`TauCeti.exists_tensorMultiplicity_ne_zero`), because `L(lam) ⊗ L(mu)` is a nonzero
finite-dimensional module.

## Main definitions

* `TauCeti.tensorMultiplicity`: the multiplicity `c^nu_{lam mu}` of `L(nu)` in `L(lam) ⊗ L(mu)`.

## Main results

* `TauCeti.irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul`: **the character
  identity** `ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)`.
* `TauCeti.exists_tensorMultiplicity_ne_zero`: **some tensor multiplicity is nonzero**, so the
  character identity is not a statement about zero modules.

## References

This is the tensor-multiplicity item of the milestone "tensor multiplicities and the minuscule
Pieri rule" in the Layer 6 decomposition toolkit of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which asks for `c^ν_{λμ}` "with
the character identity `ch L(λ) · ch L(μ) = Σ_ν c^ν_{λμ} ch L(ν)` through `formalCharacter_tensor`".
The minuscule Pieri rule itself, which evaluates these multiplicities, awaits the Weyl character
formula.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra Module

universe u v

-- Algebraic closure is not assumed here: the highest weight theory of
-- `TauCeti/Algebra/Lie/HighestWeight/Verma.lean` that the definition rests on asks only for a
-- triangularizable Cartan subalgebra. It is assumed in the character-identity section below.
variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [_root_.LieModule.IsTriangularizable K H L]

variable (b : (IsKilling.rootSystem H).Base)

/-- **The tensor multiplicity** `c^nu_{lam mu}`: the multiplicity of `L(nu)` in
`L(lam) ⊗ L(mu)` in the sense of `LieModule.isotypicMultiplicity`, that is the dimension of the
space of morphisms `L(nu) →ₗ⁅K,L⁆ L(lam) ⊗ L(mu)`.

It is the number of copies of `L(nu)` in a decomposition of the tensor product into irreducibles
when that reading is available: `lam` and `mu` dominant integral, so that the tensor product is
finite-dimensional and completely reducible, `L(nu)` being irreducible. -/
noncomputable def tensorMultiplicity (lam mu nu : Dual K H) : ℕ :=
  LieModule.isotypicMultiplicity K L
    (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu)

-- This private reduction is required by Lean's module system: an exported theorem cannot unfold
-- the opaque exported definition directly while checking its public signature.
private theorem tensorMultiplicity_def_aux (lam mu nu : Dual K H) :
    tensorMultiplicity b lam mu nu = LieModule.isotypicMultiplicity K L
      (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu) :=
  (rfl)

/-- The tensor multiplicity is the multiplicity of `L(nu)` in the tensor product. -/
@[simp]
theorem tensorMultiplicity_def (lam mu nu : Dual K H) :
    tensorMultiplicity b lam mu nu = LieModule.isotypicMultiplicity K L
      (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) (irreducibleQuotient b nu) :=
  tensorMultiplicity_def_aux b lam mu nu

/-! ### The character identity

The character of `L(lam)` is the character of a decomposition into irreducibles, so from here on
the field is algebraically closed: that is what Weyl's complete reducibility theorem is available
over in `TauCeti/Algebra/Lie/HighestWeight/Decomposition.lean`.
-/

section CharacterIdentity

variable [IsAlgClosed K]

/-- **The character identity for a tensor product of highest weight modules**: the product of the
characters of `L(lam)` and `L(mu)` is the sum of the characters of the `L(nu)`, weighted by the
tensor multiplicities.

Formal characters are multiplicative on tensor products, so the left-hand side is the character of
`L(lam) ⊗ L(mu)`; that module is finite-dimensional, so its character is the
multiplicity-weighted sum of the irreducible characters. -/
theorem irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul
    (lam mu : {l : Dual K H // IsDominantIntegral b l}) :
    irreducibleFormalCharacter b lam * irreducibleFormalCharacter b mu
      = ∑ᶠ nu : {l : Dual K H // IsDominantIntegral b l},
          (tensorMultiplicity b lam.1 mu.1 nu.1 : ℤ) • irreducibleFormalCharacter b nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral mu.2
  simp only [tensorMultiplicity_def]
  rw [irreducibleFormalCharacter_def, irreducibleFormalCharacter_def,
    ← formalCharacter_tensor]
  exact formalCharacter_eq_finsum_isotypicMultiplicity_smul b

/-- **The character identity is never a statement about zero modules.** `L(lam) ⊗ L(mu)` is a
nonzero finite-dimensional module, so at least one tensor multiplicity is nonzero, and the sum
`ch L(lam) · ch L(mu) = ∑_nu c^nu_{lam mu} · ch L(nu)` has a term that survives. -/
theorem exists_tensorMultiplicity_ne_zero (lam mu : {l : Dual K H // IsDominantIntegral b l}) :
    ∃ nu : {l : Dual K H // IsDominantIntegral b l}, tensorMultiplicity b lam.1 mu.1 nu.1 ≠ 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral mu.2
  by_contra hall
  push Not at hall
  -- every term of the sum vanishes, so the product of the two characters does
  have hzero : ∀ nu : {l : Dual K H // IsDominantIntegral b l},
      (tensorMultiplicity b lam.1 mu.1 nu.1 : ℤ) • irreducibleFormalCharacter b nu = 0 := by
    intro nu
    rw [hall nu]
    simp
  have hprod : irreducibleFormalCharacter b lam * irreducibleFormalCharacter b mu = 0 := by
    rw [irreducibleFormalCharacter_mul_eq_finsum_tensorMultiplicity_smul b lam mu,
      finsum_congr hzero, finsum_zero]
  -- characters are multiplicative on tensor products, so this is the character of `L(lam) ⊗ L(mu)`
  -- vanishing, which says that the tensor product is zero-dimensional
  rw [irreducibleFormalCharacter_def, irreducibleFormalCharacter_def, ← formalCharacter_tensor,
    formalCharacter_eq_zero_iff, Module.finrank_tensorProduct] at hprod
  -- so one of the two factors is zero-dimensional, but both are irreducible, hence nonzero
  have _ := LieModule.nontrivial_of_isIrreducible (R := K) (L := L)
    (M := irreducibleQuotient b lam.1)
  have _ := LieModule.nontrivial_of_isIrreducible (R := K) (L := L)
    (M := irreducibleQuotient b mu.1)
  rcases Nat.mul_eq_zero.mp hprod with h | h
  · exact not_subsingleton _ (Module.finrank_zero_iff.mp h)
  · exact not_subsingleton _ (Module.finrank_zero_iff.mp h)

end CharacterIdentity

end TauCeti
