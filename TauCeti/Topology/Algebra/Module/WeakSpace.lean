/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Convergence in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations.

Weak convergence in an indexed product implies coordinatewise weak convergence
(`TauCeti.tendsto_toWeakSpace_pi_apply`), and for a finite index type the converse holds as well
(`TauCeti.tendsto_toWeakSpace_pi_iff`).

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A family converges weakly exactly when its values under every continuous linear functional
converge. -/
theorem tendsto_toWeakSpace_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {u : α → E}
    {x : E} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x)) ↔
      ∀ f : StrongDual 𝕜 E, Tendsto (fun n ↦ f (u n)) l (𝓝 (f x)) :=
  (IsInducing.induced _).tendsto_nhds_iff.trans tendsto_pi_nhds

/-- Weak convergence in a product of topological modules implies coordinatewise weak convergence. -/
theorem tendsto_toWeakSpace_pi_apply {ι α : Type*} {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    {l : Filter α} {u : α → ∀ i, F i} {x : ∀ i, F i}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 (∀ i, F i) (u n)) l (𝓝 (toWeakSpace 𝕜 (∀ i, F i) x)))
    (i : ι) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (F i) (u n i)) l (𝓝 (toWeakSpace 𝕜 (F i) (x i))) := by
  rw [tendsto_toWeakSpace_iff_forall_eval_tendsto] at h ⊢
  intro f
  exact h (f.comp (ContinuousLinearMap.proj (R := 𝕜) (φ := F) i))

/-- Weak convergence in a finite product of topological modules is equivalent to coordinatewise
weak convergence. -/
theorem tendsto_toWeakSpace_pi_iff {ι α : Type*} [Finite ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    {l : Filter α} {u : α → ∀ i, F i} {x : ∀ i, F i} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (∀ i, F i) (u n)) l (𝓝 (toWeakSpace 𝕜 (∀ i, F i) x)) ↔
      ∀ i : ι, Tendsto (fun n ↦ toWeakSpace 𝕜 (F i) (u n i)) l (𝓝 (toWeakSpace 𝕜 (F i) (x i))) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨tendsto_toWeakSpace_pi_apply, fun h ↦ ?_⟩
  rw [tendsto_toWeakSpace_iff_forall_eval_tendsto]
  intro Λ
  have hcoord : ∀ i : ι,
      Tendsto (fun n ↦ (Λ.comp (ContinuousLinearMap.single 𝕜 F i)) (u n i)) l
        (𝓝 ((Λ.comp (ContinuousLinearMap.single 𝕜 F i)) (x i))) := fun i ↦
    (tendsto_toWeakSpace_iff_forall_eval_tendsto.mp (h i))
      (Λ.comp (ContinuousLinearMap.single 𝕜 F i))
  simpa only [ContinuousLinearMap.sum_comp_single] using
    tendsto_finsetSum Finset.univ fun i _ ↦ hcoord i

/-- If the weak topology is Hausdorff, a family that eventually stays in a compact set and
converges weakly to `a` converges to `a` in the original topology. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isCompact [T2Space (WeakSpace 𝕜 E)] {α : Type*}
    {l : Filter α} {K : Set E} (hK : IsCompact K) {u : α → E} (hu : ∀ᶠ n in l, u n ∈ K) {a : E}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E a))) :
    Tendsto u l (𝓝 a) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt hu fun y _ hy ↦ (toWeakSpace 𝕜 E).injective ?_
  -- A cluster point in the original topology is a weak cluster point, and the weak topology is
  -- Hausdorff.
  have hy' : MapClusterPt (toWeakSpace 𝕜 E y) l (fun n ↦ toWeakSpace 𝕜 E (u n)) :=
    hy.tendsto_comp ((toWeakSpaceCLM 𝕜 E).continuous.tendsto y)
  exact eq_of_nhds_neBot (hy'.neBot.mono (inf_le_inf_left _ h))

end TauCeti
