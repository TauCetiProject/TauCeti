/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations

/-!
# Orbit-quotient descent for alternating-map domain pullbacks

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with
`ContinuousAlternatingMap.compContinuousLinearMap`
(`TauCeti.compContinuousLinearMap_orbitRelQuotientRec`).
-/

public section

namespace TauCeti

/-- Fibrewise domain pullback `ContinuousAlternatingMap.compContinuousLinearMap` of alternating
maps commutes with `MulAction.orbitRelQuotientRec`. -/
theorem compContinuousLinearMap_orbitRelQuotientRec {G M 𝕜 ι : Type*} [Group G] [MulAction G M]
    [CommRing 𝕜] {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*} [∀ q, AddCommGroup (V₁ q)]
    [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)] [∀ q, AddCommGroup (V₂ q)]
    [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)] [∀ q, AddCommGroup (V₃ q)]
    [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    {α : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    {A : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) A hA q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q)
        (fun x ↦ (α x).compContinuousLinearMap (A x)) (MulAction.apply₂_smul_heq
          (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA) q :=
  MulAction.apply₂_orbitRelQuotientRec
    (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA q

end TauCeti
