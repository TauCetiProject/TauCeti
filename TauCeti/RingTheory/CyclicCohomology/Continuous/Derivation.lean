/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Derivation
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuity of trace-derivation cochains

The degree-one and degree-two trace-derivation cochains are jointly continuous whenever
the linear map and derivations defining them are continuous. No trace, invariance, or
commutation identity is needed for continuity; those identities ensure cyclicity in
`TauCeti.RingTheory.CyclicCohomology.Derivation`.
-/

public section

namespace TauCeti

variable {k A M : Type*} [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] [AddCommGroup M] [Module k M]
  [TopologicalSpace A] [ContinuousMul A] [TopologicalSpace M]
  {τ : A →ₗ[k] M} {δ δ₁ δ₂ : derivationLieAlgebra k A}

/-- The degree-one trace-derivation cochain is jointly continuous when its factors are. -/
@[fun_prop]
theorem continuous_traceDerivationCochain (hτ : Continuous τ)
    (hδ : Continuous (δ : Module.End k A)) : Continuous (traceDerivationCochain τ δ) := by
  apply (continuous_congr fun a ↦ traceDerivationCochain_apply a).2
  fun_prop

/-- The degree-two trace-derivation cochain is jointly continuous when its factors are. -/
@[fun_prop]
theorem continuous_traceDerivationPairCochain [ContinuousSub A] (hτ : Continuous τ)
    (h₁ : Continuous (δ₁ : Module.End k A)) (h₂ : Continuous (δ₂ : Module.End k A)) :
    Continuous (traceDerivationPairCochain τ δ₁ δ₂) := by
  apply (continuous_congr fun a ↦ traceDerivationPairCochain_apply a).2
  fun_prop

end TauCeti
