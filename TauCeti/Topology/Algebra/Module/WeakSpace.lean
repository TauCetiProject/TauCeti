/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Sequences
import TauCeti.Topology.Sequences.Basic

/-!
# Convergence and neighbourhoods in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations. Sequential closedness of an image `toWeakSpace 𝕜 E '' s` likewise translates directly
to closure of `s` under limits of weakly convergent sequences
(`TauCeti.isSeqClosed_toWeakSpace_image_iff`).

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.

Every weak neighbourhood of a point `x` in a topological vector space over a field contains an
entire affine subspace `x + K` of finite codimension
(`TauCeti.exists_submodule_finiteDimensional_quotient_forall_toWeakSpace_add_mem_of_mem_nhds`).
Consequently, for any linear map `L` of infinite-dimensional range it contains an affine line
`x + c • v` with `L v ≠ 0`
(`LinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds`), and in an
infinite-dimensional space it contains an affine line in a nonzero direction
(`TauCeti.exists_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds`, and
`TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero` at `0`).
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

/-- Sequential closedness of `toWeakSpace 𝕜 E '' s` in `WeakSpace 𝕜 E` is equivalent to closure of
`s` under limits of weakly convergent sequences in `E`. -/
theorem isSeqClosed_toWeakSpace_image_iff {s : Set E} :
    IsSeqClosed (toWeakSpace 𝕜 E '' s) ↔
      ∀ ⦃u : ℕ → E⦄ ⦃x : E⦄, (∀ n, u n ∈ s) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) → x ∈ s :=
  (toWeakSpace 𝕜 E).toEquiv.isSeqClosed_image_iff

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

/-- **Finite-codimensional affine subspaces in weak neighbourhoods.** Every neighbourhood of
`toWeakSpace 𝕜 E x` in a topological vector space over a field contains an affine subspace
`{toWeakSpace 𝕜 E (x + v) | v ∈ K}` for a submodule `K` of finite codimension. -/
theorem exists_submodule_finiteDimensional_quotient_forall_toWeakSpace_add_mem_of_mem_nhds
    {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {x : E} {U : Set (WeakSpace 𝕜 E)}
    (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ K : Submodule 𝕜 E, FiniteDimensional 𝕜 (E ⧸ K) ∧
      ∀ v ∈ K, toWeakSpace 𝕜 E (x + v) ∈ U := by
  let eval : E → StrongDual 𝕜 E → 𝕜 := fun y f ↦ f y
  have htend : Tendsto (toWeakSpace 𝕜 E) (comap eval (𝓝 (eval x))) (𝓝 (toWeakSpace 𝕜 E x)) :=
    tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun f ↦
      ((continuous_apply f).tendsto (eval x)).comp tendsto_comap
  obtain ⟨W, hW, hWU⟩ := mem_comap.1 (htend hU)
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hIW⟩ := hW
  let Φ : E →ₗ[𝕜] (I → 𝕜) := LinearMap.pi fun i : I ↦ (i.val : StrongDual 𝕜 E).toLinearMap
  refine ⟨LinearMap.ker Φ,
    FiniteDimensional.of_injective ((LinearMap.ker Φ).liftQ Φ le_rfl)
      (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl)),
    fun v hv ↦ ?_⟩
  have hmem : eval (x + v) ∈ W := hIW fun f hf ↦ by
    have hfv : f v = 0 := congrFun (LinearMap.mem_ker.1 hv) ⟨f, hf⟩
    simpa only [eval, map_add, hfv, add_zero] using mem_of_mem_nhds (ht f)
  exact hWU hmem

/-- **Affine lines in weak neighbourhoods for linear maps of infinite rank.** If a linear map
`L : E →ₗ[𝕜] F` has infinite-dimensional range, then every weak neighbourhood of
`toWeakSpace 𝕜 E x` contains an entire affine line `{toWeakSpace 𝕜 E (x + c • v) | c : 𝕜}` along a
direction `v` with `L v ≠ 0`. -/
theorem _root_.LinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds
    {𝕜 E F : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]
    (L : E →ₗ[𝕜] F) (hL : ¬ FiniteDimensional 𝕜 (LinearMap.range L)) {x : E}
    {U : Set (WeakSpace 𝕜 E)} (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, L v ≠ 0 ∧ ∀ c : 𝕜, toWeakSpace 𝕜 E (x + c • v) ∈ U := by
  obtain ⟨K, _, hKU⟩ :=
    exists_submodule_finiteDimensional_quotient_forall_toWeakSpace_add_mem_of_mem_nhds hU
  have hnotle : ¬ K ≤ LinearMap.ker L := fun hle ↦ by
    have : FiniteDimensional 𝕜 (LinearMap.range (K.liftQ L hle)) := Module.Finite.range _
    exact hL (Submodule.range_liftQ K L hle ▸ this)
  obtain ⟨v, hvK, hv_not_ker⟩ := IsConcreteLE.not_le_iff_exists.1 hnotle
  exact ⟨v, LinearMap.mem_ker.not.1 hv_not_ker, fun c ↦ hKU (c • v) (K.smul_mem c hvK)⟩

/-- **Affine lines in weak neighbourhoods.** Every neighbourhood of `toWeakSpace 𝕜 E x` in an
infinite-dimensional topological vector space over a field contains the entire affine line
`{toWeakSpace 𝕜 E (x + c • v) | c : 𝕜}` in some nonzero direction `v`. -/
theorem exists_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds {𝕜 E : Type*} [Field 𝕜]
    [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (hE : ¬ FiniteDimensional 𝕜 E) {x : E}
    {U : Set (WeakSpace 𝕜 E)} (hU : U ∈ 𝓝 (toWeakSpace 𝕜 E x)) :
    ∃ v : E, v ≠ 0 ∧ ∀ c : 𝕜, toWeakSpace 𝕜 E (x + c • v) ∈ U := by
  have hid : ¬ FiniteDimensional 𝕜 (LinearMap.range (LinearMap.id (R := 𝕜) (M := E))) := by
    rw [LinearMap.range_id]
    exact fun h ↦ hE (Module.Finite.equiv Submodule.topEquiv)
  simpa only [LinearMap.id_apply] using
    LinearMap.exists_apply_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds
      (LinearMap.id (R := 𝕜) (M := E)) hid hU

section Field

variable {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- In an infinite-dimensional space, every weak neighbourhood of `0` contains the line through
some nonzero vector. -/
theorem exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero
    (hE : ¬ FiniteDimensional 𝕜 E) {U : Set (WeakSpace 𝕜 E)} (hU : U ∈ 𝓝 0) :
    ∃ x : E, x ≠ 0 ∧ ∀ c : 𝕜, toWeakSpace 𝕜 E (c • x) ∈ U := by
  simpa only [zero_add] using
    exists_ne_zero_forall_toWeakSpace_add_smul_mem_of_mem_nhds hE (x := 0) (by simpa using hU)

end Field

end TauCeti
