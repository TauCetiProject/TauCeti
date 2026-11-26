/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Topology.UniformSpace.Equiv
public import TauCeti.Topology.MetricSpace.Isometry.Group
public import TauCeti.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Separation.Connected
import TauCeti.Algebra.AddCircle
import TauCeti.Topology.Homeomorph.Semiconj

/-!
# Expansive maps and actions

An action of a monoid `M` on a uniform space `X` is *expansive* (`TauCeti.IsExpansiveAction M X`)
if there is an entourage `U` such that two points whose orbits stay `U`-close,
`∀ m, (m • x, m • y) ∈ U`, are equal. Expansiveness pulls back along injective uniformly continuous
equivariant maps (`TauCeti.IsExpansiveAction.of_injective`), so it passes to invariant subsets
(`TauCeti.IsExpansiveAction.subMulAction`) and is invariant under uniform conjugacy
(`TauCeti.IsExpansiveAction.congr`).

On a metric space the entourage can be replaced by a constant. A permutation `T` is *expansive
with constant `δ`* (`TauCeti.IsExpansive T δ`) if distinct points are separated by more than `δ`
at some time `n : ℤ`, and a map `T` is *positively expansive with constant `δ`*
(`TauCeti.IsPositivelyExpansive T δ`) if this happens at some time `n : ℕ`. A map is positively
expansive for some `δ > 0` exactly when the `ℕ`-action of its iterates, `IterateMulAct T`, is
expansive (`TauCeti.isExpansiveAction_iterateMulAct_iff`), and a permutation is expansive for some
`δ > 0` exactly when the action of the cyclic group `Subgroup.zpowers T` is
(`TauCeti.isExpansiveAction_zpowers_iff`). Only constants `δ > 0` are meaningful: on a metric
space every permutation is expansive with any constant `δ ≤ 0`. For a homeomorphism `T`,
`Homeomorph.isExpansive_toEquiv_iff` states expansiveness of `T.toEquiv` through the powers of `T`
in the group `X ≃ₜ X`.

An isometry moves no pair of points apart, so an isometric permutation of a space with a
non-isolated point is not expansive with any constant `δ > 0` (`Isometry.not_isExpansive`); in
particular no rotation of the circle is (`AddCircle.not_isExpansive_addRight`).

## Main definitions

* `TauCeti.IsExpansiveAction M X`: expansiveness of a monoid action on a uniform space.
* `TauCeti.IsExpansive T δ`: expansiveness of a permutation of a metric space with constant `δ`.
* `TauCeti.IsPositivelyExpansive T δ`: positive expansiveness of a map with constant `δ`.

## Main results

* `TauCeti.isExpansiveAction_iff`, `TauCeti.isExpansive_iff`, `TauCeti.isPositivelyExpansive_iff`:
  the defining properties, with the eliminators `TauCeti.IsExpansive.exists_lt_dist` and
  `TauCeti.IsPositivelyExpansive.exists_lt_dist`.
* `Isometry.isExpansive_iff`: an isometric permutation is expansive with constant `δ` exactly when
  distinct points are more than `δ` apart.
-/

public section

namespace TauCeti

open Set Filter
open scoped Uniformity Topology

section Action

variable (M X : Type*) [SMul M X] [UniformSpace X]

/-- An action of `M` on a uniform space `X` is *expansive* if some entourage `U` separates orbits:
two points with `(m • x, m • y) ∈ U` for every `m` are equal. -/
def IsExpansiveAction : Prop :=
  ∃ U ∈ 𝓤 X, ∀ x y : X, (∀ m : M, (m • x, m • y) ∈ U) → x = y

variable {M X}

/-- The defining property of an expansive action, for use outside this file. -/
theorem isExpansiveAction_iff :
    IsExpansiveAction M X ↔ ∃ U ∈ 𝓤 X, ∀ x y : X, (∀ m : M, (m • x, m • y) ∈ U) → x = y :=
  .rfl

/-- Expansiveness pulls back along an injective uniformly continuous equivariant map. -/
theorem IsExpansiveAction.of_injective {Y : Type*} [SMul M Y] [UniformSpace Y]
    (hY : IsExpansiveAction M Y) {φ : X → Y} (hφ : UniformContinuous φ)
    (hinj : Function.Injective φ) (heq : ∀ (m : M) (x : X), φ (m • x) = m • φ x) :
    IsExpansiveAction M X := by
  obtain ⟨U, hU, hsep⟩ := isExpansiveAction_iff.1 hY
  rw [isExpansiveAction_iff]
  refine ⟨{p | (φ p.1, φ p.2) ∈ U}, hφ hU, fun x y h ↦ hinj (hsep _ _ fun m ↦ ?_)⟩
  simpa [heq] using h m

/-- Expansiveness is invariant under equivariant uniform isomorphisms. -/
theorem IsExpansiveAction.congr {Y : Type*} [SMul M Y] [UniformSpace Y] (e : X ≃ᵤ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    IsExpansiveAction M X ↔ IsExpansiveAction M Y := by
  refine ⟨fun h ↦ h.of_injective e.symm.uniformContinuous e.symm.injective fun m y ↦ ?_,
    fun h ↦ h.of_injective e.uniformContinuous e.injective he⟩
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply]

/-- An expansive action restricts to an expansive action on every invariant subset. -/
theorem IsExpansiveAction.subMulAction (h : IsExpansiveAction M X) (S : SubMulAction M X) :
    IsExpansiveAction M S :=
  h.of_injective uniformContinuous_subtypeVal Subtype.val_injective fun m x ↦
    (SubMulAction.val_smul m x).symm

/-- An expansive `M`-action stays expansive for any `N`-action through a map `f : M → N` with
`f m • x = m • x`: every `M`-orbit lies in an `N`-orbit. -/
theorem IsExpansiveAction.of_smul_eq {N : Type*} [SMul N X] (h : IsExpansiveAction M X)
    (f : M → N) (hf : ∀ (m : M) (x : X), f m • x = m • x) : IsExpansiveAction N X := by
  obtain ⟨U, hU, hsep⟩ := isExpansiveAction_iff.1 h
  exact isExpansiveAction_iff.2
    ⟨U, hU, fun x y hxy ↦ hsep x y fun m ↦ by simpa [hf] using hxy (f m)⟩

end Action

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A permutation `T` of a metric space is *expansive with constant `δ`* if any two distinct points
are more than `δ` apart at some time `n : ℤ`. Only `δ > 0` is meaningful: on a metric space every
permutation is expansive with any constant `δ ≤ 0`, taking `n = 0`. -/
def IsExpansive (T : Equiv.Perm X) (δ : ℝ) : Prop :=
  ∀ x y : X, x ≠ y → ∃ n : ℤ, δ < dist ((T ^ n) x) ((T ^ n) y)

/-- A map `T` of a metric space is *positively expansive with constant `δ`* if any two distinct
points are more than `δ` apart at some time `n : ℕ`. Only `δ > 0` is meaningful: on a metric space
every map is positively expansive with any constant `δ ≤ 0`, taking `n = 0`. -/
def IsPositivelyExpansive (T : X → X) (δ : ℝ) : Prop :=
  ∀ x y : X, x ≠ y → ∃ n : ℕ, δ < dist (T^[n] x) (T^[n] y)

/-- The defining property of expansiveness with constant `δ`. -/
theorem isExpansive_iff {T : Equiv.Perm X} {δ : ℝ} :
    IsExpansive T δ ↔ ∀ x y : X, x ≠ y → ∃ n : ℤ, δ < dist ((T ^ n) x) ((T ^ n) y) :=
  .rfl

/-- The defining property of positive expansiveness with constant `δ`. -/
theorem isPositivelyExpansive_iff {T : X → X} {δ : ℝ} :
    IsPositivelyExpansive T δ ↔ ∀ x y : X, x ≠ y → ∃ n : ℕ, δ < dist (T^[n] x) (T^[n] y) :=
  .rfl

/-- Two distinct points are separated by more than `δ` at some time under a permutation that is
expansive with constant `δ`. -/
theorem IsExpansive.exists_lt_dist {T : Equiv.Perm X} {δ : ℝ} (h : IsExpansive T δ) {x y : X}
    (hxy : x ≠ y) : ∃ n : ℤ, δ < dist ((T ^ n) x) ((T ^ n) y) :=
  isExpansive_iff.1 h x y hxy

/-- Two distinct points are separated by more than `δ` at some time `n : ℕ` under a map that is
positively expansive with constant `δ`. -/
theorem IsPositivelyExpansive.exists_lt_dist {T : X → X} {δ : ℝ} (h : IsPositivelyExpansive T δ)
    {x y : X} (hxy : x ≠ y) : ∃ n : ℕ, δ < dist (T^[n] x) (T^[n] y) :=
  isPositivelyExpansive_iff.1 h x y hxy

/-- Expansiveness with constant `δ` implies expansiveness with every smaller constant. -/
theorem IsExpansive.mono {T : Equiv.Perm X} {δ δ' : ℝ} (h : IsExpansive T δ) (hδ : δ' ≤ δ) :
    IsExpansive T δ' := isExpansive_iff.2 fun _ _ hxy ↦
  (h.exists_lt_dist hxy).imp fun _ hn ↦ hδ.trans_lt hn

/-- Positive expansiveness with constant `δ` implies it with every smaller constant. -/
theorem IsPositivelyExpansive.mono {T : X → X} {δ δ' : ℝ} (h : IsPositivelyExpansive T δ)
    (hδ : δ' ≤ δ) : IsPositivelyExpansive T δ' := isPositivelyExpansive_iff.2 fun _ _ hxy ↦
  (h.exists_lt_dist hxy).imp fun _ hn ↦ hδ.trans_lt hn

/-- A positively expansive permutation is expansive with the same constant. -/
theorem IsPositivelyExpansive.isExpansive {T : Equiv.Perm X} {δ : ℝ}
    (h : IsPositivelyExpansive T δ) : IsExpansive T δ := isExpansive_iff.2 fun _ _ hxy ↦ by
  obtain ⟨n, hn⟩ := h.exists_lt_dist hxy
  exact ⟨n, by simpa [zpow_natCast, ← Equiv.Perm.iterate_eq_pow] using hn⟩

/-- A map is positively expansive for some constant `δ > 0` exactly when the `ℕ`-action of its
iterates is expansive. -/
theorem isExpansiveAction_iterateMulAct_iff (T : X → X) :
    IsExpansiveAction (IterateMulAct T) X ↔ ∃ δ > 0, IsPositivelyExpansive T δ := by
  rw [isExpansiveAction_iff,
    exists_separating_entourage_iff_exists_pos_dist (fun m : IterateMulAct T ↦ (m • ·))]
  simp_rw [isPositivelyExpansive_iff]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ forall₃_congr fun x y _ ↦ ?_
  constructor
  · rintro ⟨⟨n⟩, hn⟩
    exact ⟨n, by simpa only [IterateMulAct.mk_smul] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨n⟩, by simpa only [IterateMulAct.mk_smul] using hn⟩

/-- A permutation is expansive for some constant `δ > 0` exactly when the action of the cyclic
group it generates is expansive. -/
theorem isExpansiveAction_zpowers_iff (T : Equiv.Perm X) :
    IsExpansiveAction (Subgroup.zpowers T) X ↔ ∃ δ > 0, IsExpansive T δ := by
  rw [isExpansiveAction_iff,
    exists_separating_entourage_iff_exists_pos_dist (fun m : Subgroup.zpowers T ↦ (m • ·))]
  simp_rw [isExpansive_iff]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ forall₃_congr fun x y _ ↦ ?_
  constructor
  · rintro ⟨⟨_, hg⟩, hn⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ⟨n, by simpa only [Subgroup.mk_smul, Equiv.Perm.smul_def] using hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨T ^ n, Subgroup.zpow_mem_zpowers T n⟩, ?_⟩
    simpa only [Subgroup.mk_smul, Equiv.Perm.smul_def] using hn

end Metric

end TauCeti

namespace Homeomorph

open TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- A homeomorphism `T` is expansive with constant `δ`, as a permutation, exactly when any two
distinct points are more than `δ` apart under some power of `T` in the group `X ≃ₜ X`. -/
theorem isExpansive_toEquiv_iff {T : X ≃ₜ X} {δ : ℝ} :
    IsExpansive T.toEquiv δ ↔ ∀ x y : X, x ≠ y → ∃ n : ℤ, δ < dist ((T ^ n) x) ((T ^ n) y) := by
  simp only [TauCeti.isExpansive_iff, Homeomorph.coe_zpow]

end Homeomorph

namespace Isometry

open TauCeti Set Filter
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- An isometric permutation `T` is expansive with constant `δ` exactly when distinct points are
already more than `δ` apart. -/
theorem isExpansive_iff {T : Equiv.Perm X} (hT : Isometry T) {δ : ℝ} :
    IsExpansive T δ ↔ ∀ x y : X, x ≠ y → δ < dist x y := by
  simp [TauCeti.isExpansive_iff, (hT.zpow _).dist_eq]

/-- An isometric permutation of a space with a non-isolated point is not expansive with any
constant `δ > 0`. -/
theorem not_isExpansive {T : Equiv.Perm X} (hT : Isometry T) {x : X}
    (hx : (𝓝[≠] x).NeBot) {δ : ℝ} (hδ : 0 < δ) : ¬ IsExpansive T δ := by
  rw [hT.isExpansive_iff]
  intro h
  obtain ⟨y, hyx, hy⟩ := (hx.nonempty_of_mem (inter_mem_nhdsWithin _
    (Metric.ball_mem_nhds x hδ)))
  exact (h y x hyx).not_gt (Metric.mem_ball.1 hy)

end Isometry

namespace AddCircle

open TauCeti

/-- No rotation of the circle `AddCircle p` is expansive with any constant `δ > 0`. -/
theorem not_isExpansive_addRight {p : ℝ} (a : AddCircle p) {δ : ℝ} (hδ : 0 < δ) :
    ¬ IsExpansive (Equiv.addRight a) δ := by
  have hT : Isometry (Equiv.addRight a) := by
    rw [← IsometryEquiv.addRight_toEquiv, IsometryEquiv.coe_toEquiv]
    exact (IsometryEquiv.addRight a).isometry
  -- `AddCircle p` is connected, T1 and infinite (`AddCircle.infinite`), hence nontrivial, so no
  -- point is isolated.
  exact hT.not_isExpansive (x := 0) inferInstance hδ

end AddCircle
