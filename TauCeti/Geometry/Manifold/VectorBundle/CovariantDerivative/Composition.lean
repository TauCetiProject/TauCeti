/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant differentiation and composition of bundle maps

The induced Hom connections respect contraction of a target slot with a source slot:
`∇(B ∘ A) = (∇B) ∘ A + B ∘ ∇A`. In particular, the induced connection on
endomorphisms differentiates their commutator by the ordinary Leibniz rule. This is the
coefficient-level rule used for products and brackets of endomorphism-valued forms.

The formulas hold for sections differentiable at the evaluated point, with no regularity
assumption on the connections. The first two bundles have finite rank, as required by the
native induced Hom connections; the final target can have arbitrary rank. No metric or
torsion hypothesis is needed.

The proof uses `CovariantDerivative.hom_apply` and local section extensions, without
choosing connection matrices or introducing new bundle carriers.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (induced connections and tensor contractions).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [ContMDiffVectorBundle 1 G W I]
  {K : Type*} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  {U : M → Type*} [TopologicalSpace (TotalSpace K U)]
  [∀ x, AddCommGroup (U x)] [∀ x, Module 𝕜 (U x)]
  [∀ x, TopologicalSpace (U x)] [∀ x, IsTopologicalAddGroup (U x)]
  [∀ x, ContinuousSMul 𝕜 (U x)] [FiberBundle K U] [VectorBundle 𝕜 K U]

/-- Induced Hom connections obey the product rule for composition of differentiable bundle
maps. The derivative is taken in a single tangent direction, and the equality is of fibre maps. -/
theorem hom_comp (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
    (covU : CovariantDerivative I K U)
    {A : Π x : M, V x →L[𝕜] W x} {B : Π x : M, W x →L[𝕜] U x} {x : M}
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] G)
      (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (G →L[𝕜] K)
      (E := fun z ↦ W z →L[𝕜] U z) y (B y)) x) (v : TangentSpace I x) :
    covV.hom covU (fun y ↦ (B y).comp (A y)) x v =
      (covW.hom covU B x v).comp (A x) + (B x).comp (covV.hom covW A x v) := by
  ext u
  let s := extend F u
  have hs : MDiffAt (T% s) x := mdifferentiableAt_extend ..
  have hAs := hA.clm_bundle_apply hs
  have heq : s x = u := extend_apply_self ..
  rw [← heq, hom_apply covV covU (hB.clm_bundle_comp hA) hs]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [hom_apply covW covU hB hAs, hom_apply covV covW hA hs]
  simp only [map_sub]
  abel

/-- The induced endomorphism connection differentiates the commutator by the Leibniz rule.
Both endomorphism sections need only be differentiable at the evaluated point. -/
theorem hom_commutator (cov : CovariantDerivative I F V)
    {A B : Π x : M, V x →L[𝕜] V x} {x : M}
    (hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z ↦ V z →L[𝕜] V z) y (A y)) x)
    (hB : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z ↦ V z →L[𝕜] V z) y (B y)) x) (v : TangentSpace I x) :
    cov.hom cov (fun y ↦ (A y).comp (B y) - (B y).comp (A y)) x v =
      (cov.hom cov A x v).comp (B x) - (B x).comp (cov.hom cov A x v) +
        ((A x).comp (cov.hom cov B x v) - (cov.hom cov B x v).comp (A x)) := by
  have hsub := (cov.hom cov).isCovariantDerivativeOnUniv.sub
    (hA.clm_bundle_comp hB) (hB.clm_bundle_comp hA)
  have hfun : (fun y ↦ (A y).comp (B y) - (B y).comp (A y)) =
      (fun y ↦ (A y).comp (B y)) - (fun y ↦ (B y).comp (A y)) := by
    funext y
    exact (Pi.sub_apply (fun z ↦ (A z).comp (B z))
      (fun z ↦ (B z).comp (A z)) y).symm
  rw [hfun, hsub, sub_apply, hom_comp cov cov cov hB hA,
    hom_comp cov cov cov hA hB]
  abel

end CovariantDerivative
