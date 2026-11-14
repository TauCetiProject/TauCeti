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
# Convergence and quotient induction in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations. Sequential closedness of `toWeakSpace 𝕜 E '' S` unfolds directly to a statement on
sequences in `E` (`TauCeti.isSeqClosed_toWeakSpace_iff`).

When the scalar ring `𝕜` is `T₀`, every continuous linear functional on `E` factors through
`SeparationQuotient E`, so `WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)` induces the weak topology
from that of the separated quotient (`WeakSpace.isInducing_map_mkCLM`).

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.
-/

public section

open Filter Set Topology

namespace WeakSpace

variable {𝕜 E F : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- `WeakSpace.map` intertwines `toWeakSpace` with the underlying continuous linear map. -/
@[simp]
theorem map_toWeakSpace [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    (f : E →L[𝕜] F) (x : E) :
    WeakSpace.map f (toWeakSpace 𝕜 E x) = toWeakSpace 𝕜 F (f x) :=
  (rfl)

/-- `WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)` is surjective. -/
theorem surjective_map_mkCLM [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] :
    Function.Surjective (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)) := fun y ↦ by
  obtain ⟨x, hx⟩ := SeparationQuotient.surjective_mk ((toWeakSpace 𝕜 (SeparationQuotient E)).symm y)
  exact ⟨toWeakSpace 𝕜 E x, by simp [hx]⟩

/-- Pushing `toWeakSpace 𝕜 E '' s` along `WeakSpace.map f` gives the weak image of `f '' s`. -/
theorem image_map_toWeakSpace [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    (f : E →L[𝕜] F) (s : Set E) :
    WeakSpace.map f '' (toWeakSpace 𝕜 E '' s) = toWeakSpace 𝕜 F '' (f '' s) := by
  simp_rw [← image_comp, Function.comp_def, map_toWeakSpace]

/-- When `𝕜` is `T₀`, pushing forward to `SeparationQuotient E` induces the weak topology on
`WeakSpace 𝕜 E`, because every continuous `𝕜`-linear functional factors through the separation
quotient. -/
theorem isInducing_map_mkCLM [T0Space 𝕜] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] :
    IsInducing (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)) := by
  let q := WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)
  let lift (f : StrongDual 𝕜 E) : StrongDual 𝕜 (SeparationQuotient E) :=
    SeparationQuotient.liftCLM f fun _ _ h ↦ (h.map f.continuous).eq
  let g : WeakSpace 𝕜 (SeparationQuotient E) → StrongDual 𝕜 E → 𝕜 := fun z f ↦
    lift f ((toWeakSpace 𝕜 (SeparationQuotient E)).symm z)
  have hg : Continuous g :=
    continuous_pi fun f ↦
      WeakBilin.eval_continuous (topDualPairing 𝕜 (SeparationQuotient E)).flip (lift f)
  exact .of_comp q.continuous hg (IsInducing.induced _)

/-- When `𝕜` is `T₀`, `WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)` commutes with topological
closure. -/
theorem image_map_mkCLM_closure [T0Space 𝕜] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    (s : Set (WeakSpace 𝕜 E)) :
    WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E) '' closure s =
      closure (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E) '' s) := by
  rw [(isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).closure_eq_preimage_closure_image,
    surjective_map_mkCLM.image_preimage]

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

/-- The weak image of `S` is sequentially closed if and only if weak limits of sequences in `S`
belong to `S`. -/
theorem isSeqClosed_toWeakSpace_iff {S : Set E} :
    IsSeqClosed (toWeakSpace 𝕜 E '' S) ↔
      ∀ ⦃u : ℕ → E⦄ ⦃v : E⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E v)) → v ∈ S := by
  refine ⟨fun h u v hu hlim ↦ ?_, fun h u w hu hlim ↦ ?_⟩
  · obtain ⟨v', hv', heq⟩ :=
      h (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 E) (hu n)) hlim
    exact (toWeakSpace 𝕜 E).injective heq ▸ hv'
  · choose x hx hux using hu
    refine mem_image_of_mem (toWeakSpace 𝕜 E) (h hx (u := x) (v := (toWeakSpace 𝕜 E).symm w) ?_)
    simpa only [hux, LinearEquiv.apply_symm_apply] using hlim

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
