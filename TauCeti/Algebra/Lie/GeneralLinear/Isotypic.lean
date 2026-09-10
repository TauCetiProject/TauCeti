/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity
-- Non-public: these declarations appear only inside proofs.
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.Algebra.Lie.GeneralLinear.Uniqueness
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# The single-weight isotypy criterion for `gl_n`

This file packages highest-weight existence and uniqueness into isotypy criteria for modules over
the general linear Lie algebra. If every irreducible submodule has the same highest weight, then
every pair of irreducible submodules is equivalent. Under complete reducibility, the module is the
direct sum of copies of the named irreducible with that weight.

The foundational `LieModule.IsIsotypic` assertion is pairwise. The counted direct-sum theorem adds
complete reducibility explicitly, since it is not automatic for representations of a reductive Lie
algebra unless its centre acts semisimply.

## Main results

* `gl_isotypic_of_forall_irreducible_exists_isGlHighestWeightVector`: a criterion using a supplied
  highest-weight vector in every irreducible submodule.
* `gl_isotypic_of_forall_isGlHighestWeightVector`: the finite-dimensional criterion over an
  algebraically closed field.
* `nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_isGlHighestWeightVector`: the counted
  direct-sum criterion for a completely reducible nonzero module.

## Roadmap

This is the single-weight criterion in Layer 9 of the Lie highest-weight roadmap. It supplies the
isotypy step for the CAR module in Layer 9 of the spin-representation roadmap.

## References

The formal precedent is `TauCeti.isIsotypicOfType_of_forall_isHighestWeightVector` in
`TauCeti/Algebra/Lie/HighestWeight/Isotypic.lean`.
-/

public section

namespace TauCeti

open _root_.LieModule Matrix
open scoped DirectSum

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
      [_root_.LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) P],
      ∃ v : P, IsGlHighestWeightVector mu v) :
    _root_.LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M := by
  rw [_root_.LieModule.isIsotypic_iff]
  intro P _
  rw [_root_.LieModule.isIsotypicOfType_iff]
  intro Q _
  obtain ⟨v, hv⟩ := h P
  obtain ⟨w, hw⟩ := h Q
  exact nonempty_lieModuleEquiv_of_isGlHighestWeightVector hw hv

/-- **The single-weight isotypy criterion for `gl_N`.** If every highest-weight vector in a
finite-dimensional `gl_N`-module over an algebraically closed field has weight `mu`, then every
pair of irreducible submodules is equivalent. -/
theorem gl_isotypic_of_forall_isGlHighestWeightVector [IsAlgClosed K] [FiniteDimensional K M]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    _root_.LieModule.IsIsotypic K (Matrix (Fin N) (Fin N) K) M := by
  apply gl_isotypic_of_forall_irreducible_exists_isGlHighestWeightVector (mu := mu)
  intro P _
  let _ : Nontrivial P :=
    _root_.LieModule.nontrivial_of_isIrreducible
      (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P)
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := P)
  have hnu : nu = mu := h nu (v : M) (isGlHighestWeightVector_coe_iff.mpr hv)
  subst nu
  exact ⟨v, hv⟩

/-- **The single-weight direct-sum criterion for `gl_N`.** A nonzero finite-dimensional completely
reducible `gl_N`-module whose highest-weight vectors all have weight `mu` is the direct sum of
`LieModule.isotypicMultiplicity` copies of the named irreducible `glIrreducible N mu`.

Complete reducibility is an explicit hypothesis: it is not automatic for a reductive Lie algebra,
whose centre may act non-semisimply. -/
theorem nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_isGlHighestWeightVector
    [IsAlgClosed K] [FiniteDimensional K M] [Nontrivial M]
    [ComplementedLattice (LieSubmodule K (Matrix (Fin N) (Fin N) K) M)]
    (h : ∀ (nu : Fin N → K) (v : M), IsGlHighestWeightVector nu v → nu = mu) :
    Nonempty (M ≃ₗ⁅K,Matrix (Fin N) (Fin N) K⁆
      (⨁ (_ : Fin (_root_.LieModule.isotypicMultiplicity K (Matrix (Fin N) (Fin N) K) M
        (glIrreducible N mu))), glIrreducible N mu)) := by
  obtain ⟨nu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := M)
  have hnu : nu = mu := h nu v hv
  subst nu
  have hmu := hv.isGlDominantIntegral
  let _ := isIrreducible_glIrreducible (K := K) hmu
  apply _root_.LieModule.nonempty_lieModuleEquiv_of_isIsotypicOfType
  rw [_root_.LieModule.isIsotypicOfType_iff]
  intro P _
  let _ : Nontrivial P :=
    _root_.LieModule.nontrivial_of_isIrreducible
      (R := K) (L := Matrix (Fin N) (Fin N) K) (M := P)
  obtain ⟨nu, w, hw⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := P)
  have hnu : nu = mu := h nu (w : M) (isGlHighestWeightVector_coe_iff.mpr hw)
  subst nu
  exact nonempty_lieModuleEquiv_glIrreducible hmu hw

end TauCeti
