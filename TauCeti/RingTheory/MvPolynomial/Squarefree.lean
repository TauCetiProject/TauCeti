/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree products of distinct polynomial variables

A finite product of distinct variables over a unique factorization domain is squarefree.
This supplies the reduced coordinate boundaries in algebraic normal crossings charts.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {R ι σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- A finite product of variables indexed by an injective map is squarefree. -/
theorem squarefree_prod_X_of_injective {f : ι → σ} (hf : Function.Injective f)
    (s : Finset ι) : Squarefree (∏ i ∈ s, X (R := R) (f i)) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply prime_X.irreducible.isRelPrime_iff_not_dvd.mpr
    simpa only [X_dvd_X] using fun h ↦ hij (hf h)
  · intro i _
    exact prime_X.squarefree

end TauCeti.MvPolynomial
