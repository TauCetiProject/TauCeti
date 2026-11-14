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
# Compact operators into spaces of bounded continuous functions

Let `F` be a proper normed group. An operator `T : E → α →ᵇ F` on a seminormed group, with `α`
compact, is compact as soon as the image of the unit ball of `E` is pointwise bounded and
equicontinuous (`TauCeti.isCompactOperator_of_equicontinuous`). This is the Arzelà–Ascoli
theorem in operator form.

In the form used for restriction maps, an operator from a subgroup `s` of `α →ᵇ F` to `β →ᵇ F`
that reads functions along a continuous map `j : β → α` with values in a compact set `K` is
compact as soon as the unit ball of `s` is equicontinuous on `K`
(`TauCeti.isCompactOperator_of_equicontinuousOn`). For spaces of bounded holomorphic functions,
Cauchy estimates give the equicontinuity, and the result is Montel's theorem.
-/

public section

open BoundedContinuousFunction Metric Set

namespace TauCeti

variable {E α β F : Type*} [SeminormedAddCommGroup E] [TopologicalSpace α] [TopologicalSpace β]
  [NormedAddCommGroup F] [ProperSpace F]

/-- **Arzelà–Ascoli for operators.** Let `α` be compact and `F` proper. If an operator
`T : E → α →ᵇ F` maps the unit ball of `E` to a pointwise bounded, equicontinuous family, then
`T` is a compact operator. -/
theorem isCompactOperator_of_equicontinuous [CompactSpace α] {T : E → α →ᵇ F} {C : ℝ}
    (hC : ∀ f ∈ closedBall (0 : E) 1, ∀ x, ‖T f x‖ ≤ C)
    (hT : Equicontinuous fun f : closedBall (0 : E) 1 => (T f : α → F)) :
    IsCompactOperator T := by
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image T).mpr
    ⟨closedBall 0 1, closedBall_mem_nhds _ one_pos,
      arzela_ascoli (closedBall 0 C) (isCompact_closedBall 0 C) _ ?_ ?_⟩
  · rintro _ x ⟨f, hf, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hC f hf x)
  · rw [image_eq_range]
    simpa only [Equicontinuous, EquicontinuousAt, forall_subtype_range_iff] using hT

/-- **Arzelà–Ascoli for restriction operators.** Let `T` send `f ∈ s ≤ (α →ᵇ F)` to the
function `f ∘ j` in `β →ᵇ F`, where `j` takes values in a compact set `K`. If `F` is proper and
the unit ball of `s` is equicontinuous on `K`, then `T` is a compact operator. -/
theorem isCompactOperator_of_equicontinuousOn {S : Type*} [SetLike S (α →ᵇ F)]
    [AddSubgroupClass S (α →ᵇ F)] {s : S} {K : Set α} (hK : IsCompact K) (j : C(β, α))
    (hjK : ∀ z, j z ∈ K) {T : s → β →ᵇ F} (hT : ∀ f z, T f z = (f : α →ᵇ F) (j z))
    (hs : EquicontinuousOn (fun f : closedBall (0 : s) 1 => ((f : s) : α → F)) K) :
    IsCompactOperator T := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ : C(β, K) := ⟨fun z => ⟨j z, hjK z⟩, j.continuous.subtype_mk _⟩
  have hR : IsCompactOperator fun f : s => (f : α →ᵇ F).domRestrict K :=
    isCompactOperator_of_equicontinuous (C := 1)
      (fun f hf x => (norm_coe_le_norm (f : α →ᵇ F) x).trans (mem_closedBall_zero_iff.mp hf))
      ((equicontinuous_restrict_iff _).mpr hs)
  convert hR.continuous_comp (continuous_compContinuous σ) using 1
  exact funext fun f => ext fun z => hT f z

end TauCeti
