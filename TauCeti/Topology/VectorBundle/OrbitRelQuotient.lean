/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Orbit-quotient descent for topological vector-bundle operations

Pointwise algebraic and topological compatibility of `MulAction.orbitRelQuotientRec` with
endomorphism determinants (`TauCeti.det_orbitRelQuotientRec`), alternating-map domain pullbacks
(`TauCeti.compContinuousLinearMap_orbitRelQuotientRec`,
`TauCeti.bundleTopForm_compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul`), dual pairing
(`TauCeti.orbitRelQuotientRec_dual_apply`), and fibrewise precomposition and dual maps
(`TauCeti.precomp_orbitRelQuotientRec`, `TauCeti.dualMap_orbitRelQuotientRec`), without manifold
structure on the base.
-/

public section

noncomputable section

open Bundle

namespace TauCeti

variable {G M : Type*} [Group G] [MulAction G M]

/-- Fibrewise determinant `ContinuousLinearMap.det` commutes with quotient descent: the determinant
of `MulAction.orbitRelQuotientRec φ hφ` at `q` equals the scalar descent of `x ↦ (φ x).det`. -/
theorem det_orbitRelQuotientRec {𝕜 : Type*} [CommRing 𝕜]
    {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q).det =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_smul_eq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q :=
  MulAction.apply_orbitRelQuotientRec_eq_orbitRelQuotientLift (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ q

/-- Fibrewise domain pullback `ContinuousAlternatingMap.compContinuousLinearMap` of alternating
maps commutes with `MulAction.orbitRelQuotientRec`. -/
theorem compContinuousLinearMap_orbitRelQuotientRec {𝕜 ι : Type*} [CommRing 𝕜]
    {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    {α : ∀ x : M, V₂ (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜]
      V₃ (Quotient.mk (MulAction.orbitRel G M) x)}
    {A : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x)
    (hA : ∀ (g : G) (x : M), A (g • x) ≍ A x) (q : MulAction.orbitRel.Quotient G M) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₂ q [⋀^ι]→L[𝕜] V₃ q) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) A hA q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q [⋀^ι]→L[𝕜] V₃ q)
        (fun x ↦ (α x).compContinuousLinearMap (A x)) (MulAction.apply₂_smul_heq
          (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA) q :=
  MulAction.apply₂_orbitRelQuotientRec
    (fun _ (f : _ [⋀^ι]→L[𝕜] _) (T : _ →L[𝕜] _) ↦ f.compContinuousLinearMap T) hα hA q

/-- On the top-degree scalar alternating line bundle (`Fintype.card ι = Module.finrank 𝕜 F`) over
`M ⧸ G`, pulling back a descended top form along a descended endomorphism multiplies the form by
the descended scalar determinant `MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det) ...`. -/
theorem bundleTopForm_compContinuousLinearMap_orbitRelQuotientRec_eq_det_smul
    {𝕜 ι F : Type*} [TopologicalSpace M] [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    (hrank : Fintype.card ι = Module.finrank 𝕜 F)
    {α : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) [⋀^ι]→L[𝕜] 𝕜}
    {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x) (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)
    (q : MulAction.orbitRel.Quotient G M) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] V q) φ hφ q) =
      MulAction.orbitRelQuotientLift (fun x ↦ (φ x).det)
        (MulAction.apply_smul_eq (fun _ (A : _ →L[𝕜] _) ↦ A.det) hφ) q •
        MulAction.orbitRelQuotientRec (V := fun q ↦ V q [⋀^ι]→L[𝕜] 𝕜) α hα q := by
  rw [bundleTopForm_compContinuousLinearMap_eq_det_smul hrank, det_orbitRelQuotientRec]

section Dual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Pairing a descended dual-bundle section with a descended vector-bundle section over `M ⧸ G`
agrees with the scalar descent `MulAction.orbitRelQuotientLift` of their upstairs pairing. -/
theorem orbitRelQuotientRec_dual_apply {V : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
    {α : ∀ x : M, StrongDual 𝕜 (V (Quotient.mk (MulAction.orbitRel G M) x))}
    {t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x)}
    (hα : ∀ (g : G) (x : M), α (g • x) ≍ α x)
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x) (q : MulAction.orbitRel.Quotient G M) :
    MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V q)) α hα q
        (MulAction.orbitRelQuotientRec t ht q) =
      MulAction.orbitRelQuotientLift (fun x ↦ α x (t x))
        (MulAction.apply₂_smul_eq (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht) q :=
  MulAction.apply₂_orbitRelQuotientRec_eq_orbitRelQuotientLift
    (fun _ (f : StrongDual 𝕜 _) v ↦ f v) hα ht q

/-- Fibrewise precomposition into any third bundle `V₃` over `M ⧸ G` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem precomp_orbitRelQuotientRec {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    (V₃ : MulAction.orbitRel.Quotient G M → Type*)
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    [∀ q, AddCommGroup (V₃ q)] [∀ q, Module 𝕜 (V₃ q)] [∀ q, TopologicalSpace (V₃ q)]
    [∀ q, IsTopologicalAddGroup (V₃ q)] [∀ q, ContinuousSMul 𝕜 (V₃ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp (V₃ q)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) φ hφ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ (V₂ q →L[𝕜] V₃ q) →L[𝕜] V₁ q →L[𝕜] V₃ q)
        (fun x ↦ ContinuousLinearMap.precomp (V₃ (Quotient.mk (MulAction.orbitRel G M) x)) (φ x))
        (MulAction.apply_smul_heq (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun q A ↦ ContinuousLinearMap.precomp (V₃ q) A) hφ q

/-- Fibrewise dual (transpose) `ContinuousLinearMap.precomp 𝕜` commutes with
`MulAction.orbitRelQuotientRec`. -/
theorem dualMap_orbitRelQuotientRec {V₁ V₂ : MulAction.orbitRel.Quotient G M → Type*}
    [∀ q, AddCommGroup (V₁ q)] [∀ q, Module 𝕜 (V₁ q)] [∀ q, TopologicalSpace (V₁ q)]
    [∀ q, AddCommGroup (V₂ q)] [∀ q, Module 𝕜 (V₂ q)] [∀ q, TopologicalSpace (V₂ q)]
    {φ : ∀ x : M, V₁ (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
      V₂ (Quotient.mk (MulAction.orbitRel G M) x)}
    (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x) (q : MulAction.orbitRel.Quotient G M) :
    ContinuousLinearMap.precomp 𝕜
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V₁ q →L[𝕜] V₂ q) φ hφ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ StrongDual 𝕜 (V₂ q) →L[𝕜] StrongDual 𝕜 (V₁ q))
        (fun x ↦ ContinuousLinearMap.precomp 𝕜 (φ x))
        (MulAction.apply_smul_heq (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ) q :=
  MulAction.apply_orbitRelQuotientRec (fun _ A ↦ ContinuousLinearMap.precomp 𝕜 A) hφ q

end Dual

end TauCeti
