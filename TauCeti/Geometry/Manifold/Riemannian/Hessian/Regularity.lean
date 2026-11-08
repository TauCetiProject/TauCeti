/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Smoothness of Hessian pairings along maps

On an open set where a scalar function is `C^(n+2)`, pairing its Riemannian Hessian with two
`C^n` tangent fields along a `C^n` base map gives a `C^n` scalar function, on a `C^(n+2)`
manifold with a `C^(n+1)` metric. The parameter manifold needs no dimension or regularity
assumption beyond its charts.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {n m k : ℕ∞ω} [IsManifold I m M]
  [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- Hessian pairings of a `C^(n+2)` function with `C^n` tangent fields along a `C^n` map are
`C^n`, on a `C^(n+2)` manifold with a `C^(n+1)` metric. -/
theorem contMDiffAt_hessian_pair (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ) (n + 2) f U) {γ : N → M}
    {P Q : ∀ y, TangentSpace I (γ y)} {x : N} (hx : γ x ∈ U)
    (hP : ContMDiffAt J I.tangent n (fun y ↦ TotalSpace.mk' E (γ y) (P y)) x)
    (hQ : ContMDiffAt J I.tangent n (fun y ↦ TotalSpace.mk' E (γ y) (Q y)) x) :
    ContMDiffAt J 𝓘(ℝ) n (fun y ↦ hessian I f (γ y) (P y) (Q y)) x := by
  have hγ : ContMDiffAt J I n γ x := (contMDiffAt_totalSpace.mp hP).1
  have h2 : n + 1 + 1 = n + 2 := by rw [add_assoc, one_add_one_eq_two]
  have : IsManifold I (n + 1 + 1) M := IsManifold.of_le (n := m) (h2 ▸ hm)
  have : IsContMDiffRiemannianBundle I (n + 1) E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hk
  have : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (le_self_add.trans hk)
  have hG : CMDiff[U] (n + 1) (T% (mgradient I f)) := by
    intro y hy
    exact (contMDiffAt_mgradient (n := n + 1)
      (by simpa [h2] using hf.contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt
  have hA := contMDiffOn_leviCivitaConnection (I := I) hU hm hk hG
  have hAP := ((hA.contMDiffAt (hU.mem_nhds hx)).comp x hγ).clm_bundle_apply hP
  have heq : (fun y ↦ hessian I f (γ y) (P y) (Q y)) =
      (fun y ↦ inner ℝ (leviCivitaConnection I M (mgradient I f) (γ y) (P y)) (Q y)) := by
    funext y
    exact hessian_def I f (γ y) (P y) (Q y)
  rw [heq]
  exact ContMDiffAt.inner_bundle (IB := I) (F := E)
    (E := fun y : M ↦ TangentSpace I y) (b := γ) hAP hQ

end TauCeti.Manifold
