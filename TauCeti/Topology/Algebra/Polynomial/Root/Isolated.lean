/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Separation.Basic

/-!
# Roots of a polynomial are isolated

A nonzero polynomial over `R` has finitely many roots in an integral domain `A` that is a faithful
`R`-algebra. When `A` carries a T₁ topology, finite sets are closed, so every point `x` of `A` has
a neighbourhood containing no root of the polynomial other than (possibly) `x` itself.
-/

public section

open Filter Topology

namespace Polynomial

/-- The roots of a nonzero polynomial are isolated: near any point `x` of a T₁ faithful algebra
that is an integral domain, every root of the polynomial is `x`. -/
theorem eventually_aeval_eq_zero_imp_eq {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [FaithfulSMul R A] [TopologicalSpace A] [T1Space A] {f : R[X]} (hf : f ≠ 0)
    (x : A) : ∀ᶠ w in 𝓝 x, aeval w f = 0 → w = x := by
  have hfin : {w : A | aeval w f = 0}.Finite := by
    simpa [IsRoot, eval_map_algebraMap] using finite_setOfPred_isRoot
      ((Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R A)).2 hf)
  filter_upwards [(hfin.sdiff (t := {x})).isClosed.compl_mem_nhds (by simp)] with w hw h0
  by_contra hne
  exact hw ⟨h0, hne⟩

end Polynomial
