/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Product
public import TauCeti.Topology.Homotopy.HurewiczFibration

/-!
# Restriction fibrations of mapping spaces

Let `A` be a closed subspace of a locally compact space `K`.  If `A ⊆ K` has the homotopy
extension property, then restriction along the inclusion is a Hurewicz fibration

`C(K, X) → C(A, X)`.

A lifting problem with parameter space `P` uncurries to a homotopy-extension problem on
`P × A ⊆ P × K`.  The product stability of the homotopy extension property supplies the
extension, and the compact-open exponential law curries it back to the required lift.  In
particular this applies to every closed cofibration of compact Hausdorff spaces.

## Main results

* `TauCeti.HasHomotopyExtensionProperty.isHurewiczFibration_restrict`: restriction along a closed
  subspace with the homotopy extension property is a Hurewicz fibration when the ambient source
  is locally compact.
* `TauCeti.HasHomotopyExtensionProperty.isHurewiczFibration_restrict_of_compact_t2`: the compact
  Hausdorff specialization, where closedness follows from the homotopy extension property.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
* The currying step uses Mathlib's compact-open exponential law and restriction API in
  `Mathlib.Topology.CompactOpen`: `ContinuousMap.curry`, `ContinuousMap.uncurry`, and
  `ContinuousMap.continuous_restrict`.
-/

public section

noncomputable section

open Set unitInterval

universe u v w

namespace TauCeti

variable {K : Type u} [TopologicalSpace K] {A : Set K}
  {X : Type v} [TopologicalSpace X]

/-- **Restriction along a closed cofibration is a Hurewicz fibration.**  If `K` is locally
compact and the closed subset `A ⊆ K` has the homotopy extension property, then
`C(K, X) → C(A, X)` is a Hurewicz fibration for the compact-open topologies. -/
theorem HasHomotopyExtensionProperty.isHurewiczFibration_restrict
    [LocallyCompactSpace K] (h : HasHomotopyExtensionProperty A) (hA : IsClosed A) :
    IsHurewiczFibration.{w} (ContinuousMap.restrict A : C(K, X) → C(A, X)) := by
  let _ : LocallyCompactSpace A := hA.locallyCompactSpace
  apply isHurewiczFibration_iff.2
  refine ⟨ContinuousMap.continuous_restrict A, fun P _ f H hH ↦ ?_⟩
  let B : Set (P × K) := {q | q.2 ∈ A}
  have hB : IsClosed B := hA.preimage continuous_snd
  have hBhep : HasHomotopyExtensionProperty B := h.prod_left hA
  let f₀ : C(P × K, X) := ContinuousMap.uncurry f
  let H₀ : C(I × B, X) :=
    ⟨fun q ↦ H (q.1, q.2.1.1) ⟨q.2.1.2, q.2.2⟩, by fun_prop⟩
  have hH₀ : ∀ b : B, H₀ (0, b) = f₀ b := by
    rintro ⟨⟨p, k⟩, hk⟩
    -- Both sides are evaluations of `H (0, p)` and `f p` at the point `k ∈ A`.
    simpa only [H₀, f₀, ContinuousMap.coe_mk, ContinuousMap.uncurry_apply,
      Function.uncurry_apply_pair, ContinuousMap.restrict_apply] using
      congrArg (fun g : C(A, X) ↦ g ⟨k, hk⟩) (hH p)
  obtain ⟨G₀, hG₀, hG₀B⟩ := hBhep.exists_extension_of_isClosed hB f₀ H₀ hH₀
  let α : C((I × P) × K, I × (P × K)) :=
    ⟨fun q ↦ (q.1.1, q.1.2, q.2), by fun_prop⟩
  let G : C(I × P, C(K, X)) :=
    ContinuousMap.curry (G₀.comp α)
  refine ⟨G, funext fun q ↦ ContinuousMap.ext fun a ↦ ?_, fun p ↦ ContinuousMap.ext fun k ↦ ?_⟩
  -- Unfold the curried lift pointwise: `G q a = G₀ (q.1, q.2, a)`, compared with `H` on `A`
  -- and with `f` at time `0`.
  · simpa only [G, α, H₀, Function.comp_apply, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.restrict_apply] using hG₀B q.1 ⟨(q.2, a), a.2⟩
  · simpa only [G, α, f₀, Function.comp_apply, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using
      hG₀ (p, k)

/-- **Restriction along a cofibration of compact Hausdorff spaces is a Hurewicz fibration.**
Here closedness is automatic: a subspace with the homotopy extension property in a Hausdorff
space is closed. -/
theorem HasHomotopyExtensionProperty.isHurewiczFibration_restrict_of_compact_t2
    [CompactSpace K] [T2Space K] (h : HasHomotopyExtensionProperty A) :
    IsHurewiczFibration.{w} (ContinuousMap.restrict A : C(K, X) → C(A, X)) :=
  h.isHurewiczFibration_restrict h.isClosed

end TauCeti

end

end
