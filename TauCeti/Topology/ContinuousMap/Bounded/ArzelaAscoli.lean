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

In the form used for restriction maps, an operator `E → β →ᵇ F` that, on a neighborhood of `0`,
reads the functions `Φ f : α → F` along a continuous map `j : β → α` with values in a compact set
`K` is compact as soon as the family indexed by that neighborhood is equicontinuous on `K` with
pointwise relatively compact values there (`IsCompact.isCompactOperator_of_equicontinuousOn`).
For the restriction of bounded holomorphic functions to a set lying in a compact subset `K` of
their domain, Cauchy estimates give the equicontinuity on `K` and properness of the target gives
the pointwise relatively compact values, and the result is Montel's theorem.
-/

public section

open BoundedContinuousFunction Set
open scoped Topology

variable {E α β F : Type*} [TopologicalSpace E] [Zero E] [TopologicalSpace α]
  [TopologicalSpace β] [PseudoMetricSpace F]

/-- **Arzelà–Ascoli for restriction operators.** Let `j : β → α` be a continuous map with
values in a compact set `K`, and let `T` send each `f` in a neighborhood `V` of `0` in `E` to the
function `Φ f ∘ j` in `β →ᵇ F`. If the family `Φ f` for `f ∈ V` is equicontinuous on `K` and its
values at each point of `K` lie in a compact set, then `T` is a compact operator. -/
theorem IsCompact.isCompactOperator_of_equicontinuousOn {K : Set α} (hK : IsCompact K)
    (j : C(β, α)) (hjK : ∀ z, j z ∈ K) {Φ : E → α → F} {T : E → β →ᵇ F} {V : Set E}
    (hV : V ∈ 𝓝 0) (hT : ∀ f ∈ V, ∀ z, T f z = Φ f (j z))
    (hΦV : ∀ x ∈ K, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, Φ f x ∈ Q)
    (hs : EquicontinuousOn (fun f : V => Φ f) K) :
    IsCompactOperator T := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ : C(β, K) := ⟨fun z => ⟨j z, hjK z⟩, j.continuous.subtype_mk _⟩
  -- The restrictions to `K` of the functions indexed by `V`, continuous by equicontinuity.
  let R : V → C(K, F) := fun f => ⟨K.domRestrict (Φ f), (hs.continuousOn f).domRestrict⟩
  have hR (f : V) : ⇑(R f) = K.domRestrict (Φ f) := ContinuousMap.coe_mk _ _
  have h := ArzelaAscoli.isCompact_closure_range_of_equicontinuous (f := R)
    (by simpa only [hR, Function.comp_def] using (equicontinuous_restrict_iff _).mpr hs) fun x => by
      obtain ⟨Q, hQ, hΦQ⟩ := hΦV x x.property
      exact ⟨Q, hQ, fun f => by simpa only [hR, Set.domRestrict_apply] using hΦQ f f.property⟩
  -- Read the restrictions along `σ` as bounded functions on `β`.
  let e := ContinuousMap.isometryEquivBoundedOfCompact K F
  let G : C(K, F) → β →ᵇ F := fun g => (e g).compContinuous σ
  have hG : Continuous G := (continuous_compContinuous σ).comp e.continuous
  refine ⟨_, h.image hG,
    Filter.mem_of_superset hV fun f hf => ⟨R ⟨f, hf⟩, subset_closure (mem_range_self _), ?_⟩⟩
  ext z
  simp only [G, e, compContinuous_apply, ContinuousMap.isometryEquivBoundedOfCompact_apply,
    mkOfCompact_apply, hR, Set.domRestrict_apply, σ, ContinuousMap.coe_mk, hT f hf z]

namespace TauCeti

/-- **Arzelà–Ascoli for operators.** Let `α` be compact. If an operator `T : E → α →ᵇ F` maps
a neighborhood `V` of `0` to an equicontinuous family whose values at each point lie in a
compact set, then `T` is a compact operator. -/
theorem isCompactOperator_of_equicontinuous [CompactSpace α] {T : E → α →ᵇ F} {V : Set E}
    (hV : V ∈ 𝓝 0) (hTV : ∀ x, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, T f x ∈ Q)
    (hT : Equicontinuous fun f : V => (T f : α → F)) :
    IsCompactOperator T :=
  isCompact_univ.isCompactOperator_of_equicontinuousOn (ContinuousMap.id α)
    (fun _ => mem_univ _) (Φ := fun f => T f) hV (fun _ _ _ => rfl) (fun x _ => hTV x)
    (hT.equicontinuousOn _)

end TauCeti
