/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The short exact sequence of cubical chains of a pair

For any subspace `A ⊆ X`, the sequence of normalized cubical chains
`0 → C^□_n(A; R) → C^□_n(X; R) → C^□_n(X, A; R) → 0` is short exact.
The inclusion is injective even after normalization: an injective continuous map reflects
coordinate independence, so no nondegenerate cube becomes degenerate in the ambient space.

`TauCeti.NormalizedCubicalChain.pairShortComplex` packages this sequence in `ModuleCat` in each
degree. This supplies the degreewise exactness needed to construct the homology sequence of a
pair. No openness, closedness, or separation assumption on the subspace is required.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.NormalizedCubicalChain

variable {X : Type*} [TopologicalSpace X] (R : Type*) [Ring R] (A : Set X)

/-- The degreewise chain sequence of a pair: subspace chains, ambient chains, and relative
chains. The first arrow is induced by the inclusion and the second is the quotient map. -/
abbrev pairShortComplex (n : ℕ) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (map R (ContinuousMap.subtypeVal A) n)
    (supportedIn R A n).mkQ
    (by
      rw [supportedIn_def]
      exact (map R (ContinuousMap.subtypeVal A) n).exact_map_mkQ_range.linearMap_comp_eq_zero)

@[simp]
theorem pairShortComplex_f (n : ℕ) :
    (pairShortComplex R A n).f = ModuleCat.ofHom (map R (ContinuousMap.subtypeVal A) n) :=
  (rfl)

@[simp]
theorem pairShortComplex_g (n : ℕ) :
    (pairShortComplex R A n).g = ModuleCat.ofHom (supportedIn R A n).mkQ :=
  (rfl)

/-- The cubical chain sequence of every subspace is short exact, in every degree and over any
coefficient ring. -/
theorem shortExact_pairShortComplex (n : ℕ) : (pairShortComplex R A n).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (LinearMap.exact_iff.mpr (by
      simp only [ModuleCat.hom_ofHom, Submodule.ker_mkQ, supportedIn_def]))
    (map_injective R (ContinuousMap.subtypeVal A) Subtype.val_injective n)
    (Submodule.mkQ_surjective _)

end TauCeti.NormalizedCubicalChain
