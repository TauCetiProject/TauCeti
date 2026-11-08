/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Smoothness of Hessian pairings along maps

On a smoothness domain for a scalar function, pairing its Riemannian Hessian with two
smooth tangent fields along an arbitrary smooth base map gives a smooth scalar function. The
parameter manifold needs no dimension or regularity assumption beyond its charts.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- Hessian pairings with smooth tangent fields along a smooth map are smooth. -/
theorem contMDiffAt_hessian_pair {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) {γ : N → M} {P Q : ∀ y, TangentSpace I (γ y)}
    {x : N} (hx : γ x ∈ U) (hγ : ContMDiffAt J I ∞ γ x)
    (hP : ContMDiffAt J I.tangent ∞ (fun y ↦ TotalSpace.mk' E (γ y) (P y)) x)
    (hQ : ContMDiffAt J I.tangent ∞ (fun y ↦ TotalSpace.mk' E (γ y) (Q y)) x) :
    ContMDiffAt J 𝓘(ℝ) ∞ (fun y ↦ hessian I f (γ y) (P y) (Q y)) x := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff[U] ∞ (T% (mgradient I f)) := by
    intro y hy
    exact (contMDiffAt_mgradient (n := ∞)
      (by simpa using hf.contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  have hA := contMDiffOn_leviCivitaConnection (I := I) (n := ∞) (m := ∞) (k := ∞)
    hU (by simp) (by simp) (by simpa using hG)
  have hAP := ((hA.contMDiffAt (hU.mem_nhds hx)).comp x hγ).clm_bundle_apply hP
  have heq : (fun y ↦ hessian I f (γ y) (P y) (Q y)) =
      (fun y ↦ inner ℝ (leviCivitaConnection I M (mgradient I f) (γ y) (P y)) (Q y)) := by
    funext y
    exact hessian_def I f (γ y) (P y) (Q y)
  rw [heq]
  exact ContMDiffAt.inner_bundle (IB := I) (F := E)
    (E := fun y : M ↦ TangentSpace I y) (b := γ) hAP hQ

end TauCeti.Manifold
