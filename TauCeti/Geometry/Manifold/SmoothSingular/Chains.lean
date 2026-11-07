/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Integral
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Integration over smooth singular chains

`TauCeti.chainIntegral c φ` integrates a differential form over a finite real linear combination
of smooth simplices. It uses `SmoothSimplex.integral` and Mathlib's
`Finsupp.linearCombination`; coefficients of repeated simplices are combined before integration.
It is linear in the chain, additive on continuous forms, and commutes with pullback along smooth
maps. No compactness or finite-dimensionality assumption on the manifold is needed.

`TauCeti.integrationCochain φ` is the same functional on the degree term of Mathlib's simplicial
chain complex of `smoothSingularSubcomplex`. The comparison uses the existing
`SSet.chainsLinearEquivFinsupp`, so integration uses the canonical chain complex, including its
induced maps. Its value on a simplex with coefficient `a` is `a • σ.integral φ`.
This is the chain pairing used to construct the de Rham comparison. Stokes supplies the remaining
compatibility with differentials needed for a cochain map. The categorical statements use small
spaces, as does the real singular cohomology comparison.

As with simplex integration, these are total Bochner integrals. Completeness of the coefficient
space makes them meaningful for continuous forms; additivity in the form requires continuity,
whereas linearity in a finite chain holds even for the total integral.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, integration over smooth
  chains.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold Simplicial ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- Integration of a form over a finite real linear combination of smooth singular simplices.
The integral on each simplex is the total Bochner integral `SmoothSimplex.integral`. -/
def chainIntegral (c : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p) : F :=
  Finsupp.linearCombination ℝ (fun σ ↦ σ.integral φ) c

/-- The chain integral is the finite sum of coefficient times simplex integral. -/
theorem chainIntegral_eq_sum (c : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p) :
    chainIntegral c φ = c.sum fun σ a ↦ a • σ.integral φ :=
  Finsupp.linearCombination_apply ℝ _

/-- Integration of a chain consisting of one simplex. -/
@[simp]
theorem chainIntegral_single (σ : SmoothSimplex I M p) (a : ℝ) (φ : RoughForm I M F p) :
    chainIntegral (Finsupp.single σ a) φ = a • σ.integral φ :=
  Finsupp.linearCombination_single ℝ _ _

/-- The integral over the zero chain vanishes. -/
@[simp]
theorem chainIntegral_zero (φ : RoughForm I M F p) : chainIntegral 0 φ = 0 :=
  map_zero (Finsupp.linearCombination ℝ _)

/-- Integration is additive in the chain, with no regularity assumption on the form. -/
@[simp]
theorem chainIntegral_add (c d : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p) :
    chainIntegral (c + d) φ = chainIntegral c φ + chainIntegral d φ :=
  map_add (Finsupp.linearCombination ℝ _) c d

/-- Reversing all coefficients negates the integral. -/
@[simp]
theorem chainIntegral_neg (c : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p) :
    chainIntegral (-c) φ = -chainIntegral c φ :=
  map_neg (Finsupp.linearCombination ℝ _) c

/-- Integration takes the difference of two chains to the difference of their integrals. -/
@[simp]
theorem chainIntegral_sub (c d : SmoothSimplex I M p →₀ ℝ) (φ : RoughForm I M F p) :
    chainIntegral (c - d) φ = chainIntegral c φ - chainIntegral d φ :=
  map_sub (Finsupp.linearCombination ℝ _) c d

/-- Integration is homogeneous in the real chain coefficients. -/
@[simp]
theorem chainIntegral_smul (a : ℝ) (c : SmoothSimplex I M p →₀ ℝ)
    (φ : RoughForm I M F p) : chainIntegral (a • c) φ = a • chainIntegral c φ :=
  map_smul (Finsupp.linearCombination ℝ _) a c

/-- The zero form integrates to zero over every smooth chain. -/
@[simp]
theorem chainIntegral_zero_form (c : SmoothSimplex I M p →₀ ℝ) :
    chainIntegral c (0 : RoughForm I M F p) = 0 := by
  simp [chainIntegral_eq_sum]

/-- Scalar multiplication of a form commutes with chain integration, also for complex-valued
forms and complex scalars. -/
@[simp]
theorem chainIntegral_smul_form {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [SMulCommClass ℝ 𝕜 F] (c : SmoothSimplex I M p →₀ ℝ)
    (a : 𝕜) (φ : RoughForm I M F p) :
    chainIntegral c (a • φ) = a • chainIntegral c φ := by
  simp only [chainIntegral_eq_sum, SmoothSimplex.integral_smul, Finsupp.sum,
    Finset.smul_sum, smul_comm]

/-- Chain integration is additive on continuous forms. -/
theorem chainIntegral_add_form [IsManifold I 1 M] (c : SmoothSimplex I M p →₀ ℝ)
    {φ ψ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    chainIntegral c (φ + ψ) = chainIntegral c φ + chainIntegral c ψ := by
  simp [chainIntegral_eq_sum, SmoothSimplex.integral_add _ hφ hψ, smul_add,
    Finsupp.sum, Finset.sum_add_distrib]

/-- In degree zero the chain integral is the coefficient-weighted sum of function values.
This includes the normalization that a unit point chain integrates the constant function one
to one. -/
theorem chainIntegral_ofFunction [CompleteSpace F] (c : SmoothSimplex I M 0 →₀ ℝ) (a : M → F) :
    chainIntegral c (RoughForm.ofFunction I a) =
      c.sum fun σ r ↦ r • a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 0⟩) := by
  simp [chainIntegral_eq_sum]

section Naturality

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- Integrating over the pushforward of a smooth chain is integrating the pulled-back form.
`mapDomain` adds coefficients when different simplices have the same image. -/
theorem chainIntegral_mapDomain {f : M → N} (hf : ContMDiff I J ∞ f)
    (c : SmoothSimplex I M p →₀ ℝ) (ψ : RoughForm J N F p) :
    chainIntegral
        (Finsupp.mapDomain ((smoothSingularSubcomplexMap f hf).app (Opposite.op ⦋p⦌)) c) ψ =
      chainIntegral c (mpullback I J f ψ) := by
  simp only [chainIntegral, Finsupp.linearCombination_mapDomain, Function.comp_def,
    SmoothSimplex.integral_smoothSingularSubcomplexMap_app hf]

end Naturality

section Cochain

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The linear functional on Mathlib's smooth singular chains given by integrating a form.
It is a cochain in degree `p`; being a cocycle additionally requires a closed form and Stokes. -/
def integrationCochain (φ : RoughForm I M F p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X p ⟶
      ModuleCat.of ℝ F :=
  ModuleCat.ofHom ((Finsupp.linearCombination ℝ (fun σ : SmoothSimplex I M p ↦ σ.integral φ)).comp
    (SSet.chainsLinearEquivFinsupp _ ℝ p).toLinearMap)

/-- On canonical simplicial chains, integration is the finite coefficient sum. -/
theorem integrationCochain_apply (φ : RoughForm I M F p)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X p) :
    (integrationCochain φ).hom c =
      chainIntegral ((smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp ℝ p c) φ :=
  (rfl)

/-- The integration cochain takes a simplex with coefficient `a` to `a` times its integral. -/
@[simp]
theorem integrationCochain_ιChainComplex (φ : RoughForm I M F p) (σ : SmoothSimplex I M p)
    (a : ℝ) :
    (integrationCochain φ).hom (((smoothSingularSubcomplex I M : SSet).ιChainComplex
      (R := ModuleCat.of ℝ ℝ) σ).hom a) = a • σ.integral φ := by
  rw [integrationCochain_apply (I := I),
    _root_.SSet.chainsLinearEquivFinsupp_ιChainComplex
      (smoothSingularSubcomplex I M : SSet) σ a]
  exact chainIntegral_single σ a φ

/-- Integrating the zero form gives the zero cochain. -/
@[simp]
theorem integrationCochain_zero : integrationCochain (0 : RoughForm I M F p) = 0 := by
  apply ModuleCat.hom_ext
  ext c
  simp [integrationCochain_apply (I := I)]

/-- The integration cochain is homogeneous in the form. -/
@[simp]
theorem integrationCochain_smul (a : ℝ) (φ : RoughForm I M F p) :
    integrationCochain (a • φ) = a • integrationCochain φ := by
  apply ModuleCat.hom_ext
  ext c
  simp [integrationCochain_apply (I := I)]

/-- Integration takes addition of continuous forms to addition of cochains. -/
theorem integrationCochain_add [IsManifold I 1 M] {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    integrationCochain (φ + ψ) = integrationCochain φ + integrationCochain ψ := by
  apply ModuleCat.hom_ext
  ext c
  simp [integrationCochain_apply (I := I), chainIntegral_add_form _ hφ hψ]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- The integration cochain is natural for the actual chain map induced by a smooth map. -/
@[reassoc]
theorem integrationCochain_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    (ψ : RoughForm J N F p) :
    (SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℝ ℝ)).f p ≫
      integrationCochain ψ = integrationCochain (mpullback I J f ψ) := by
  apply ModuleCat.hom_ext
  ext c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, integrationCochain_apply (I := I),
    integrationCochain_apply (I := J),
    SSet.chainsLinearEquivFinsupp_chainComplexMap_f, chainIntegral_mapDomain hf]

end Cochain

end TauCeti
