/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Defs.Sequences

/-!
# Convergence and separation quotients in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`), and sequential
closedness of `toWeakSpace 𝕜 E '' S` reduces to closure of `S` under weak sequential limits in `E`
(`TauCeti.isSeqClosed_image_toWeakSpace_iff`). This lets weak convergence and sequential weak
closedness be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space. No
injectivity of the duality pairing is needed, since the weak topology is induced by the evaluations.

When the scalar ring is `T₀`, every continuous linear functional vanishes on elements inseparable
from zero and therefore factors through `SeparationQuotient E`. Consequently the weak map induced
by `SeparationQuotient.mkCLM 𝕜 E` is a topological inducing map (`WeakSpace.isInducing_map_mkCLM`),
transferring weak topological properties from separated quotients back to unseparated modules.

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.
-/

public section

open Filter Set Topology

namespace WeakSpace

/-- When the scalar ring is `T₀`, the weak map induced by `SeparationQuotient.mkCLM 𝕜 E` is a
topological inducing map: every continuous linear functional on `E` factors through
`SeparationQuotient E`. -/
theorem isInducing_map_mkCLM (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [T0Space 𝕜]
    [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] :
    IsInducing (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)) := by
  let g : WeakSpace 𝕜 (SeparationQuotient E) → StrongDual 𝕜 E → 𝕜 := fun y f ↦
    ((topDualPairing 𝕜 (SeparationQuotient E)).flip y)
      (SeparationQuotient.liftCLM f fun a b hab ↦ (hab.map f.continuous).eq)
  have hg : Continuous g := continuous_pi fun f ↦
    WeakBilin.eval_continuous (topDualPairing 𝕜 (SeparationQuotient E)).flip
      (SeparationQuotient.liftCLM f fun a b hab ↦ (hab.map f.continuous).eq)
  exact .of_comp (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)).continuous hg (.induced _)

end WeakSpace

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

/-- The weak image of `S` is sequentially closed in `WeakSpace 𝕜 E` if and only if every sequence
in `S` converging weakly to a point of `E` has that limit in `S`. -/
theorem isSeqClosed_image_toWeakSpace_iff {S : Set E} :
    IsSeqClosed (toWeakSpace 𝕜 E '' S) ↔
      ∀ ⦃u : ℕ → E⦄ ⦃x : E⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) → x ∈ S := by
  constructor
  · intro hS u x hu hlim
    obtain ⟨y, hy, hyx⟩ := hS (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 E) (hu n)) hlim
    exact (toWeakSpace 𝕜 E).injective hyx ▸ hy
  · intro hS w z hw hlim
    choose u huS huw using hw
    refine ⟨(toWeakSpace 𝕜 E).symm z, hS huS ?_, (toWeakSpace 𝕜 E).apply_symm_apply z⟩
    simpa only [huw, LinearEquiv.apply_symm_apply] using hlim

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
