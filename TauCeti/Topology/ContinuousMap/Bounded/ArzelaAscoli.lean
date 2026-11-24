/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.UniformSpace.Equicontinuity
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Compact operators into spaces of bounded continuous functions

Let `F` be a pseudometric space and `α` a compact space. An operator `T : E → α →ᵇ F` is
compact as soon as it maps a neighborhood of `0` to an equicontinuous family whose values at
each point lie in a compact set (`TauCeti.isCompactOperator_of_equicontinuous`). This is the
Arzelà–Ascoli theorem in operator form.

In the form used for restriction maps, an operator `E → β →ᵇ F` that reads the functions
`Φ f : α → F` along a continuous map `j : β → α` with values in a compact set `K` is compact as
soon as a neighborhood of `0` gives a family that is equicontinuous on `K` with pointwise
relatively compact values there (`IsCompact.isCompactOperator_of_equicontinuousOn`). For spaces
of bounded holomorphic functions, Cauchy estimates give the equicontinuity, and the result is
Montel's theorem.
-/

public section

open BoundedContinuousFunction Set
open scoped Topology

variable {E α β F : Type*} [TopologicalSpace E] [Zero E] [TopologicalSpace α]
  [TopologicalSpace β] [PseudoMetricSpace F]

namespace TauCeti

/-- **Arzelà–Ascoli for operators.** Let `α` be compact. If an operator `T : E → α →ᵇ F` maps
a neighborhood `V` of `0` to an equicontinuous family whose values at each point lie in a
compact set, then `T` is a compact operator. -/
theorem isCompactOperator_of_equicontinuous [CompactSpace α] {T : E → α →ᵇ F} {V : Set E}
    (hV : V ∈ 𝓝 0) (hTV : ∀ x, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, T f x ∈ Q)
    (hT : Equicontinuous fun f : V => (T f : α → F)) :
    IsCompactOperator T := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact α F
  have h := ArzelaAscoli.isCompact_closure_range_of_equicontinuous (f := fun f : V => e.symm (T f))
    hT fun x => let ⟨Q, hQ, hTQ⟩ := hTV x; ⟨Q, hQ, fun f => hTQ f f.property⟩
  refine ⟨_, h.image e.continuous, Filter.mem_of_superset hV fun f hf => ?_⟩
  exact ⟨_, subset_closure ⟨⟨f, hf⟩, rfl⟩, e.apply_symm_apply _⟩

end TauCeti

/-- **Arzelà–Ascoli for restriction operators.** Let `T` send `f : E` to the function
`Φ f ∘ j` in `β →ᵇ F`, where `j` takes values in a compact set `K`. If `Φ` maps a neighborhood
`V` of `0` to a family that is equicontinuous on `K` and whose values at each point of `K` lie in
a compact set, then `T` is a compact operator. -/
theorem IsCompact.isCompactOperator_of_equicontinuousOn {K : Set α} (hK : IsCompact K)
    (j : C(β, α)) (hjK : ∀ z, j z ∈ K) {Φ : E → α → F} {T : E → β →ᵇ F}
    (hT : ∀ f z, T f z = Φ f (j z)) {V : Set E} (hV : V ∈ 𝓝 0)
    (hΦV : ∀ x ∈ K, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, Φ f x ∈ Q)
    (hs : EquicontinuousOn (fun f : V => Φ f) K) :
    IsCompactOperator T := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ : C(β, K) := ⟨fun z => ⟨j z, hjK z⟩, j.continuous.subtype_mk _⟩
  -- Only the functions indexed by `V` matter; `p` projects every `f` to one of them, and
  -- equicontinuity makes each `Φ (p f)` continuous on `K`.
  classical
  let p : E → V := fun f => if h : f ∈ V then ⟨f, h⟩ else ⟨0, mem_of_mem_nhds hV⟩
  obtain ⟨Q, hQ, hRQ⟩ := TauCeti.isCompactOperator_of_equicontinuous
    (T := fun f => mkOfCompact ⟨K.domRestrict (Φ (p f)), (hs.continuousOn (p f)).domRestrict⟩)
    hV (fun x => let ⟨Q, hQ, hΦQ⟩ := hΦV x x.property; ⟨Q, hQ, fun f _ => hΦQ _ (p f).property⟩)
    (((equicontinuous_restrict_iff _).mpr hs).comp fun f : V => p f)
  refine ⟨_, hQ.image (continuous_compContinuous σ),
    Filter.mem_of_superset (Filter.inter_mem hV hRQ) fun f hf => ⟨_, hf.right, ext fun z => ?_⟩⟩
  simp [p, hf.left, hT, σ]
