/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Expansive maps and actions

An action of a monoid `M` on a uniform space `X` is *expansive* (`TauCeti.IsExpansiveAction M X`)
if there is an entourage `U` such that two points whose orbits stay `U`-close,
`∀ m, (m • x, m • y) ∈ U`, are equal. Expansiveness pulls back along injective uniformly continuous
equivariant maps (`TauCeti.IsExpansiveAction.of_injective`), so it passes to invariant subsets and
is invariant under uniform conjugacy (`TauCeti.IsExpansiveAction.congr`).

On a metric space the entourage can be replaced by a constant. A permutation `T` is *expansive
with constant `δ`* (`TauCeti.IsExpansive T δ`) if distinct points are separated by more than `δ`
at some time `n : ℤ`, and a map `T` is *positively expansive with constant `δ`*
(`TauCeti.IsPositivelyExpansive T δ`) if this happens at some time `n : ℕ`. A map is positively
expansive for some `δ > 0` exactly when the `ℕ`-action of its iterates, `IterateMulAct T`, is
expansive (`TauCeti.isExpansiveAction_iterateMulAct_iff`), and a permutation is expansive for some
`δ > 0` exactly when the action of the cyclic group `Subgroup.zpowers T` is
(`TauCeti.isExpansiveAction_zpowers_iff`).

An isometry moves no pair of points apart, so an isometric permutation of a space with a
non-isolated point is not expansive (`TauCeti.not_isExpansive_of_isometry`); in particular no
rotation of the circle is expansive (`TauCeti.not_isExpansive_addCircle_addRight`).

## Main definitions

* `TauCeti.IsExpansiveAction M X`: expansiveness of a monoid action on a uniform space.
* `TauCeti.IsExpansive T δ`: expansiveness of a permutation of a metric space with constant `δ`.
* `TauCeti.IsPositivelyExpansive T δ`: positive expansiveness of a map with constant `δ`.
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

/-- Expansiveness pulls back along an injective uniformly continuous equivariant map. -/
theorem IsExpansiveAction.of_injective {Y : Type*} [SMul M Y] [UniformSpace Y]
    (hY : IsExpansiveAction M Y) {φ : X → Y} (hφ : UniformContinuous φ)
    (hinj : Function.Injective φ) (heq : ∀ (m : M) (x : X), φ (m • x) = m • φ x) :
    IsExpansiveAction M X := by
  obtain ⟨U, hU, hsep⟩ := hY
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

/-- An expansive action of a monoid stays expansive when acting by a larger monoid through a
homomorphism: every orbit of the smaller monoid is part of an orbit of the larger one. -/
theorem IsExpansiveAction.of_compHom {N : Type*} [SMul N X] (h : IsExpansiveAction M X)
    (f : M → N) (hf : ∀ (m : M) (x : X), f m • x = m • x) : IsExpansiveAction N X := by
  obtain ⟨U, hU, hsep⟩ := h
  exact ⟨U, hU, fun x y hxy ↦ hsep x y fun m ↦ by simpa [hf] using hxy (f m)⟩

end Action

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A permutation `T` of a metric space is *expansive with constant `δ`* if any two distinct points
are more than `δ` apart at some time `n : ℤ`. -/
def IsExpansive (T : Equiv.Perm X) (δ : ℝ) : Prop :=
  ∀ x y : X, x ≠ y → ∃ n : ℤ, δ < dist ((T ^ n) x) ((T ^ n) y)

/-- A map `T` of a metric space is *positively expansive with constant `δ`* if any two distinct
points are more than `δ` apart at some time `n : ℕ`. -/
def IsPositivelyExpansive (T : X → X) (δ : ℝ) : Prop :=
  ∀ x y : X, x ≠ y → ∃ n : ℕ, δ < dist (T^[n] x) (T^[n] y)

/-- Expansiveness with constant `δ` implies expansiveness with every smaller constant. -/
theorem IsExpansive.mono {T : Equiv.Perm X} {δ δ' : ℝ} (h : IsExpansive T δ) (hδ : δ' ≤ δ) :
    IsExpansive T δ' := fun x y hxy ↦
  (h x y hxy).imp fun _ hn ↦ hδ.trans_lt hn

/-- Positive expansiveness with constant `δ` implies it with every smaller constant. -/
theorem IsPositivelyExpansive.mono {T : X → X} {δ δ' : ℝ} (h : IsPositivelyExpansive T δ)
    (hδ : δ' ≤ δ) : IsPositivelyExpansive T δ' := fun x y hxy ↦
  (h x y hxy).imp fun _ hn ↦ hδ.trans_lt hn

/-- A positively expansive permutation is expansive with the same constant. -/
theorem IsPositivelyExpansive.isExpansive {T : Equiv.Perm X} {δ : ℝ}
    (h : IsPositivelyExpansive T δ) : IsExpansive T δ := fun x y hxy ↦ by
  obtain ⟨n, hn⟩ := h x y hxy
  exact ⟨n, by simpa [zpow_natCast, ← Equiv.Perm.iterate_eq_pow] using hn⟩

/-- Expansiveness of a family of maps indexed by `ι` in terms of a separating constant. -/
private lemma exists_entourage_iff_exists_pos {ι : Type*} (f : ι → X → X) :
    (∃ U ∈ 𝓤 X, ∀ x y : X, (∀ i, (f i x, f i y) ∈ U) → x = y) ↔
      ∃ δ > 0, ∀ x y : X, x ≠ y → ∃ i, δ < dist (f i x) (f i y) := by
  constructor
  · rintro ⟨U, hU, hsep⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
    refine ⟨ε / 2, half_pos hε, fun x y hxy ↦ ?_⟩
    by_contra! h
    exact hxy (hsep x y fun i ↦ hεU ((h i).trans_lt (half_lt_self hε)))
  · rintro ⟨δ, hδ, hsep⟩
    refine ⟨{p | dist p.1 p.2 ≤ δ}, Metric.mem_uniformity_dist.2 ⟨δ, hδ, fun _ _ h ↦ h.le⟩,
      fun x y h ↦ ?_⟩
    by_contra hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact (h i).not_gt hi

/-- A map is positively expansive for some constant `δ > 0` exactly when the `ℕ`-action of its
iterates is expansive. -/
theorem isExpansiveAction_iterateMulAct_iff (T : X → X) :
    IsExpansiveAction (IterateMulAct T) X ↔ ∃ δ > 0, IsPositivelyExpansive T δ := by
  rw [IsExpansiveAction, exists_entourage_iff_exists_pos (fun m : IterateMulAct T ↦ (m • ·))]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ forall₃_congr fun x y _ ↦ ?_
  exact ⟨fun ⟨m, hm⟩ ↦ ⟨m.val, hm⟩, fun ⟨n, hn⟩ ↦ ⟨⟨n⟩, hn⟩⟩

/-- A permutation is expansive for some constant `δ > 0` exactly when the action of the cyclic
group it generates is expansive. -/
theorem isExpansiveAction_zpowers_iff (T : Equiv.Perm X) :
    IsExpansiveAction (Subgroup.zpowers T) X ↔ ∃ δ > 0, IsExpansive T δ := by
  rw [IsExpansiveAction, exists_entourage_iff_exists_pos (fun m : Subgroup.zpowers T ↦ (m • ·))]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ forall₃_congr fun x y _ ↦ ?_
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨T ^ n, n, rfl⟩, hn⟩

/-- The integer powers of an isometric permutation are isometries. -/
theorem dist_zpow_apply_of_isometry {T : Equiv.Perm X} (hT : Isometry T) (n : ℤ) (x y : X) :
    dist ((T ^ n) x) ((T ^ n) y) = dist x y := by
  induction n using Int.induction_on generalizing x y with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hT.dist_eq]
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, ← hT.dist_eq]
    simp

/-- An isometric permutation `T` is expansive with constant `δ` exactly when distinct points are
already more than `δ` apart. -/
theorem isExpansive_iff_of_isometry {T : Equiv.Perm X} (hT : Isometry T) {δ : ℝ} :
    IsExpansive T δ ↔ ∀ x y : X, x ≠ y → δ < dist x y := by
  simp [IsExpansive, dist_zpow_apply_of_isometry hT]

/-- An isometric permutation of a space with a non-isolated point is not expansive. -/
theorem not_isExpansive_of_isometry {T : Equiv.Perm X} (hT : Isometry T) {x : X}
    (hx : (𝓝[≠] x).NeBot) {δ : ℝ} (hδ : 0 < δ) : ¬ IsExpansive T δ := by
  rw [isExpansive_iff_of_isometry hT]
  intro h
  obtain ⟨y, hyx, hy⟩ := (hx.nonempty_of_mem (inter_mem_nhdsWithin _
    (Metric.ball_mem_nhds x hδ)))
  exact (h y x hyx).not_gt (Metric.mem_ball.1 hy)

/-- No rotation of the circle `AddCircle p`, `p > 0`, is expansive. -/
theorem not_isExpansive_addCircle_addRight {p : ℝ} (hp : 0 < p) (a : AddCircle p) {δ : ℝ}
    (hδ : 0 < δ) : ¬ IsExpansive (Equiv.addRight a) δ := by
  rw [isExpansive_iff_of_isometry
    (show Isometry (Equiv.addRight a) from (IsometryEquiv.addRight a).isometry)]
  intro h
  set t := min (δ / 2) (p / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos hp)
  have hnorm : ‖(t : AddCircle p)‖ = t := by
    rw [(AddCircle.norm_coe_eq_abs_iff p hp.ne').2, abs_of_pos ht]
    rw [abs_of_pos ht, abs_of_pos hp]
    exact min_le_right _ _
  have hne : (t : AddCircle p) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact ht.ne hnorm
  have := h (t : AddCircle p) 0 hne
  rw [dist_zero_right, hnorm] at this
  linarith [min_le_left (δ / 2) (p / 2)]

end Metric

end TauCeti
