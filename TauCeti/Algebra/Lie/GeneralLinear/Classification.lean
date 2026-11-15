/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
public import TauCeti.Algebra.Lie.GeneralLinear.Existence

/-!
# The classification of the finite-dimensional irreducible `gl N`-modules

Over a field of characteristic zero, the irreducible finite-dimensional modules of `gl N K` on
which the diagonal Cartan subalgebra acts triangularizably are exactly the named modules
`TauCeti.glIrreducible N mu`, one for each dominant integral weight `mu`. Triangularizability is
automatic over an algebraically closed field; over a smaller field it cannot be dropped, since the
identity matrix can act on an irreducible module by a scalar outside `K`.

The three ingredients are already available: a nonzero such module has a dominant highest weight
vector (`TauCeti.exists_isGlHighestWeightVector_and_isGlDominantIntegral`), such a vector identifies
the module with `L(mu)` (`TauCeti.nonempty_lieModuleEquiv_glIrreducible`), and all highest weight
vectors of an irreducible module have one weight
(`TauCeti.IsGlHighestWeightVector.weight_eq_of_isIrreducible`).

## Main results

* `TauCeti.existsUnique_isGlDominantIntegral_and_nonempty_lieModuleEquiv_glIrreducible`: **the
  classification**: such a module is equivalent to `L(mu)` for exactly one dominant `mu`.

## References

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}
variable (M : Type*) [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]

/-- **The classification of the finite-dimensional irreducible `gl N`-modules.** Over a field of
characteristic zero, a finite-dimensional irreducible `gl N K`-module on which the diagonal Cartan
subalgebra acts triangularizably is equivalent to `L(mu)` for exactly one dominant integral `mu`. -/
theorem existsUnique_isGlDominantIntegral_and_nonempty_lieModuleEquiv_glIrreducible
    [FiniteDimensional K M] [LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) M]
    [LieModule.IsTriangularizable K (diagonalCartan K (Fin N)) M] :
    ∃! mu : Fin N → K, IsGlDominantIntegral mu ∧
      Nonempty (M ≃ₗ⁅K, Matrix (Fin N) (Fin N) K⁆ glIrreducible N mu) := by
  have : Nontrivial M := LieModule.nontrivial_of_isIrreducible K (Matrix (Fin N) (Fin N) K) M
  obtain ⟨mu, v, hv, hmu⟩ :=
    exists_isGlHighestWeightVector_and_isGlDominantIntegral (K := K) (N := N) (M := M)
  refine ⟨mu, ⟨hmu, nonempty_lieModuleEquiv_glIrreducible hmu hv⟩, fun nu ⟨hnu, ⟨e⟩⟩ => ?_⟩
  exact hv.weight_eq_of_isIrreducible
    ((isGlHighestWeightVector_glIrreducibleGenerator hnu).congr e.symm)

end TauCeti
