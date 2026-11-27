/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations

/-!
# Orbit-quotient descent for continuous linear endomorphism determinants

Pointwise compatibility of `MulAction.orbitRelQuotientRec` with fibrewise endomorphism
determinants (`TauCeti.det_orbitRelQuotientRec`).
-/

public section

namespace TauCeti

/-- Fibrewise determinant `ContinuousLinearMap.det` commutes with quotient descent: the determinant
of `MulAction.orbitRelQuotientRec φ hφ` at `q` equals the scalar descent of `x ↦ (φ x).det`. -/
theorem det_orbitRelQuotientRec {G M 𝕜 : Type*} [Group G] [MulAction G M] [CommRing 𝕜]
    {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q).det =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_smul_eq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q :=
  MulAction.apply_orbitRelQuotientRec_eq_orbitRelQuotientLift (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ q

end TauCeti
