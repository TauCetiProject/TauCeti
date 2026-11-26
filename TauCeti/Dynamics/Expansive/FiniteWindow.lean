/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Expansive
import Mathlib.Topology.UniformSpace.Separation
import TauCeti.Topology.Homeomorph.Semiconj
import TauCeti.Topology.UniformSpace.Compact

/-!
# Finite-window forms of expansiveness

On a compact space, the separation of orbits in an expansive system is uniform in a finite window
of times. Each statement applies the compactness lemma
`TauCeti.exists_finset_forall_mem_of_isClosed` (in `TauCeti.Topology.UniformSpace.Compact`) to
the maps `x ↦ m • x` or `x ↦ T ^ n x`.

* For a continuous monoid action on a compact uniform space, expansiveness is equivalent, on a
  `T0` space, to the existence of an entourage `V` such that for every entourage `W` a finite set
  of times suffices (`TauCeti.isExpansiveAction_iff_finite_window`).
* For a homeomorphism `T` of a compact metric space, expansive with constant `δ`, every `ε > 0`
  has a window `N` with: if `dist (T ^ n x) (T ^ n y) ≤ δ` for `|n| ≤ N`, then `dist x y < ε`
  (`TauCeti.IsExpansive.exists_window`); the positive version for a continuous map is
  `TauCeti.IsPositivelyExpansive.exists_window`.
-/

public section

namespace TauCeti

open Set Filter
open scoped Uniformity Topology

variable {X : Type*} [UniformSpace X] [CompactSpace X] {M : Type*} [SMul M X]

/-- **Finite windows for expansive actions.** A continuous expansive action on a compact uniform
space has a closed entourage `V` such that for every entourage `W` finitely many times suffice:
`(m • x, m • y) ∈ V` for `m` in a finite set implies `(x, y) ∈ W`. -/
theorem IsExpansiveAction.exists_finite_window (h : IsExpansiveAction M X)
    (hcont : ∀ m : M, Continuous (m • · : X → X)) :
    ∃ V ∈ 𝓤 X, IsClosed V ∧
      ∀ W ∈ 𝓤 X, ∃ F : Finset M, ∀ x y, (∀ m ∈ F, (m • x, m • y) ∈ V) → (x, y) ∈ W := by
  obtain ⟨U, hU, hsep⟩ := isExpansiveAction_iff.1 h
  obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ := uniformity_hasBasis_closed.mem_iff.1 hU
  exact ⟨V, hV, hVc, fun W hW ↦ exists_finset_forall_mem_of_isClosed hcont hVc
    (fun x y hxy ↦ hsep x y fun m ↦ hVU (hxy m)) hW⟩

/-- **Expansiveness through finite windows.** A continuous action on a compact `T0` uniform space
is expansive exactly when some entourage `V` has the finite-window property: for every entourage
`W` there is a finite set `F` of times such that `(m • x, m • y) ∈ V` for all `m ∈ F` implies
`(x, y) ∈ W`. -/
theorem isExpansiveAction_iff_finite_window [T0Space X]
    (hcont : ∀ m : M, Continuous (m • · : X → X)) :
    IsExpansiveAction M X ↔ ∃ V ∈ 𝓤 X,
      ∀ W ∈ 𝓤 X, ∃ F : Finset M, ∀ x y, (∀ m ∈ F, (m • x, m • y) ∈ V) → (x, y) ∈ W := by
  refine ⟨fun h ↦ ?_, fun ⟨V, hV, hwin⟩ ↦ isExpansiveAction_iff.2 ⟨V, hV, fun x y hxy ↦ ?_⟩⟩
  · obtain ⟨V, hV, -, hwin⟩ := h.exists_finite_window hcont
    exact ⟨V, hV, hwin⟩
  · refine eq_of_uniformity fun hW ↦ ?_
    obtain ⟨F, hF⟩ := hwin _ hW
    exact hF x y fun m _ ↦ hxy m

end TauCeti

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

/-- **Finite windows for expansive homeomorphisms.** On a compact metric space, if `T` is expansive
with constant `δ` and continuous with continuous inverse, then for every `ε > 0` there is `N` such
that points staying `δ`-close for all times `|n| ≤ N` are `ε`-close. -/
theorem IsExpansive.exists_window {T : Equiv.Perm X} {δ : ℝ} (h : IsExpansive T δ)
    (hT : Continuous T) (hT' : Continuous T.symm) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x y, (∀ n : ℤ, |n| ≤ N → dist ((T ^ n) x) ((T ^ n) y) ≤ δ) → dist x y < ε := by
  obtain ⟨F, hF⟩ := exists_finset_forall_mem_of_isClosed
    (fun n ↦ by simpa only [Homeomorph.coe_zpow] using ((⟨T, hT, hT'⟩ : X ≃ₜ X) ^ n).continuous)
    (V := {p | dist p.1 p.2 ≤ δ}) (isClosed_le continuous_dist continuous_const)
    (fun _ _ ↦ h.eq_of_forall_dist_le) (Metric.dist_mem_uniformity hε)
  refine ⟨F.sup Int.natAbs, fun x y hxy ↦ hF x y fun n hn ↦ hxy n ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.le_sup (f := Int.natAbs) hn

/-- **Finite windows for positively expansive maps.** On a compact metric space, if a continuous
`T` is positively expansive with constant `δ`, then for every `ε > 0` there is `N` such that
points staying `δ`-close for all times `n ≤ N` are `ε`-close. -/
theorem IsPositivelyExpansive.exists_window {T : X → X} {δ : ℝ} (h : IsPositivelyExpansive T δ)
    (hT : Continuous T) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x y, (∀ n ≤ N, dist (T^[n] x) (T^[n] y) ≤ δ) → dist x y < ε := by
  obtain ⟨F, hF⟩ := exists_finset_forall_mem_of_isClosed (fun n ↦ hT.iterate n)
    (V := {p | dist p.1 p.2 ≤ δ}) (isClosed_le continuous_dist continuous_const)
    (fun _ _ ↦ h.eq_of_forall_dist_le) (Metric.dist_mem_uniformity hε)
  exact ⟨F.sup id, fun x y hxy ↦ hF x y fun n hn ↦ hxy n (Finset.le_sup (f := id) hn)⟩

end TauCeti
