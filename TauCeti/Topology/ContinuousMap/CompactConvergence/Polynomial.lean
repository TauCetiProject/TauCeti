/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.CompactConvergence.Dense
public import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Polynomial approximation on compact subsets of the real line

The real polynomial functions approximate every continuous restriction to a compact subset
of the real line. The coordinate polynomial separates points of the compact set, so we can
apply Mathlib's real Stone–Weierstrass theorem on that set.
-/

public section

open scoped Polynomial

namespace TauCeti

/-- Real polynomial functions are dense on compact sets of the real line. -/
theorem denseOnCompacts_polynomial_eval :
    DenseOnCompacts (Set.range (fun p : ℝ[X] => fun x => p.eval x)) := by
  refine denseOnCompacts_iff.mpr fun K hK f hf ε hε => ?_
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (polynomialFunctions K) (polynomialFunctions_separatesPoints K) (K.domRestrict f)
    (continuousOn_iff_continuous_domRestrict.mp hf) ε hε
  have hgmem : (g : C(K, ℝ)) ∈ (polynomialFunctions K : Set C(K, ℝ)) := g.property
  rw [polynomialFunctions_coe] at hgmem
  obtain ⟨p, hp⟩ := hgmem
  refine ⟨fun x => p.eval x, ⟨p, rfl⟩, fun x hx => ?_⟩
  have hpx := congrFun (congrArg DFunLike.coe hp) ⟨x, hx⟩
  have hnear := hg ⟨x, hx⟩
  rw [Real.dist_eq, abs_sub_comm]
  simpa only [Real.norm_eq_abs, Set.domRestrict_apply, ← hpx,
    Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply] using hnear

end TauCeti
