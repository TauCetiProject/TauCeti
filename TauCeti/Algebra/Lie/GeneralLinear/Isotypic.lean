/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
public import TauCeti.Algebra.Lie.Isotypic
-- Non-public: these declarations appear only inside proofs.
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.Algebra.Lie.GeneralLinear.Uniqueness
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# The single-weight isotypy criterion for `gl_n`

This file packages highest-weight existence and uniqueness into an isotypy criterion for modules
over the general linear Lie algebra. If every irreducible submodule has the same highest weight,
then every pair of irreducible submodules is equivalent.

The resulting `LieModule.IsIsotypic` assertion is deliberately pairwise: a direct-sum
decomposition into irreducibles additionally requires complete reducibility, which is not automatic
for representations of a reductive Lie algebra unless its centre acts semisimply.

## Main results

* `gl_isotypic_of_forall_irreducible_exists_isGlHighestWeightVector`: a criterion using a supplied
  highest-weight vector in every irreducible submodule.
* `gl_isotypic_of_forall_isGlHighestWeightVector`: the finite-dimensional criterion over an
  algebraically closed field.

## Roadmap

This is the single-weight criterion in Layer 9 of the Lie highest-weight roadmap. It supplies the
isotypy step for the CAR module in Layer 9 of the spin-representation roadmap.

## References

The formal precedent is `TauCeti.isIsotypicOfType_of_forall_isHighestWeightVector` in
`TauCeti/Algebra/Lie/HighestWeight/Isotypic.lean`.
-/

public section

namespace TauCeti

open LieModule Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {K : Type u} [Field K] [CharZero K]
variable {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M]
  [LieModule K (Matrix (Fin N) (Fin N) K) M]
variable {mu : Fin N → K}

/-- If every irreducible submodule of a `gl_N`-module carries a highest-weight vector of weight
`mu`, then the module is isotypic.

This form does not require finite-dimensionality or an algebraically closed field: those
hypotheses are only needed to produce the highest-weight vectors, which are supplied here. -/
theorem gl_isotypic_of_forall_irreducible_exists_isGlHighestWeightVector
    (h : ∀ (P : LieSubmodule K (Matrix (Fin N) (Fin N) K) M)
      [LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) P],
      ∃ v : P, IsGlHighestWeightVector mu v) :
    LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M := by
  rw [LieModule.isIsotypic_iff]
  intro P _
  rw [LieModule.isIsotypicOfType_iff]
  intro Q _
  obtain ⟨v, hv⟩ := h P
  obtain ⟨w, hw⟩ := h Q
  exact nonempty_lieModuleEquiv_of_isGlHighestWeightVector hw hv

/-- **The single-weight isotypy criterion for `gl_N`.** If every highest-weight vector in a
finite-dimensional `gl_N`-module over an algebraically closed field has weight `mu`, then every
pair of irreducible submodules is equivalent. -/
theorem gl_isotypic_of_forall_isGlHighestWeightVector [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M := by
  apply gl_isotypic_of_forall_irreducible_exists_isGlHighestWeightVector (mu := mu)
  intro P _
  let _ : Nontrivial P :=
    LieModule.nontrivial_of_isIrreducible
      (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P)
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := P)
  have hnu : nu = mu := h nu (v : M) (isGlHighestWeightVector_coe_iff.mpr hv)
  subst nu
  exact ⟨v, hv⟩

end TauCeti
