/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compact restriction operators between spaces of bounded continuous functions

Let `S` be a subspace of the bounded continuous functions `α →ᵇ F` with values in a proper
normed space, and `S'` a closed subspace of `β →ᵇ F`. An operator `T : S → S'` that reads
functions along a continuous map `j : β → α` with values in a compact set `K` is compact as soon
as the unit ball of `S` is equicontinuous on `K`
(`TauCeti.isCompactOperator_of_equicontinuousOn`). This is the Arzelà–Ascoli
theorem in the form used for restriction maps: for spaces of bounded holomorphic functions,
Cauchy estimates give the equicontinuity, and the result is Montel's theorem.
-/

public section

open BoundedContinuousFunction Metric Set

namespace TauCeti

variable {𝕜 α β F : Type*} [NormedField 𝕜] [TopologicalSpace α] [TopologicalSpace β]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [ProperSpace F]

/-- **Arzelà–Ascoli for restriction operators.** Let `T` send `f ∈ S ≤ (α →ᵇ F)` to the
function `f ∘ j` in a closed subspace `S'` of `β →ᵇ F`, where `j` takes values in a compact set
`K`. If `F` is proper and the unit ball of `S` is equicontinuous on `K`, then `T` is a compact
operator. -/
theorem isCompactOperator_of_equicontinuousOn {S : Submodule 𝕜 (α →ᵇ F)}
    {S' : Submodule 𝕜 (β →ᵇ F)} (hS' : IsClosed (S' : Set (β →ᵇ F))) {K : Set α}
    (hK : IsCompact K) (j : C(β, α)) (hjK : ∀ z, j z ∈ K) {T : S → S'}
    (hT : ∀ f z, (T f : β →ᵇ F) z = (f : α →ᵇ F) (j z))
    (hS : EquicontinuousOn (fun f : closedBall (0 : S) 1 => ((f : S) : α → F)) K) :
    IsCompactOperator T := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ρ : C(K, α) := ⟨Subtype.val, continuous_subtype_val⟩
  let σ : C(β, K) := ⟨fun z => ⟨j z, hjK z⟩, j.continuous.subtype_mk _⟩
  -- The unit ball of `S`, restricted to `K`.
  let g : closedBall (0 : S) 1 → K →ᵇ F := fun f => ((f : S) : α →ᵇ F).compContinuous ρ
  have hA : IsCompact (closure (range g)) := by
    refine arzela_ascoli (closedBall 0 1) (isCompact_closedBall 0 1) _ ?_ fun x => ?_
    · rintro _ z ⟨f, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (norm_coe_le_norm ((f : S) : α →ᵇ F) z).trans (mem_closedBall_zero_iff.mp f.2)
    · -- Reindex the restricted unit ball by a choice of preimages in the unit ball.
      have hx := ((equicontinuousAt_restrict_iff _ x).mpr (hS x x.2)).comp
        fun a : range g => a.2.choose
      convert hx using 1
      funext a z
      rw [← a.2.choose_spec]
      simp [g, ρ]
  have hcomp : IsCompact (((↑) : S' → β →ᵇ F) ⁻¹' ((·.compContinuous σ) '' closure (range g))) :=
    hS'.isClosedEmbedding_subtypeVal.isCompact_preimage (hA.image (continuous_compContinuous σ))
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    ⟨closedBall 0 1, closedBall_mem_nhds _ one_pos, _, hcomp, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨g ⟨f, hf⟩, subset_closure (mem_range_self _), ext fun z => (hT f z).symm⟩

end TauCeti
