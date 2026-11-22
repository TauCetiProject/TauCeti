/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.Homotopy.Extension.Basic
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Topology.Homotopy.Extension.NDRPair
import TauCeti.Topology.Homotopy.Extension.Segment

/-!
# Finite sets of points are closed cofibrations

Two disjoint closed subsets `A` and `B` with the homotopy extension property, separated by a
continuous function `φ` with `φ = 0` on `A` and `φ = 1` on `B`, have a union with the homotopy
extension property (`TauCeti.HasHomotopyExtensionProperty.union_of_eqOn`): NDR data for `A` and
for `B` are cut off before `φ` reaches `1 / 3`, respectively after it drops below `2 / 3`, and
glued along the level `φ = 1 / 2`. By Urysohn's lemma such a function exists when `A` is compact,
in a locally compact Hausdorff space. So a finite set of points, each of which has the homotopy
extension property, has it as well (`Set.Finite.hasHomotopyExtensionProperty`).

In a Hausdorff space charted on a proper real normed space, for instance a finite-dimensional
manifold without boundary, every point has the homotopy extension property, being a degenerate
segment in a chart (`OpenPartialHomeomorph.hasHomotopyExtensionProperty_symm_image_segment`). So
every finite set has it (`Set.Finite.hasHomotopyExtensionProperty_of_chartedSpace`), in every
dimension.

The homotopy extension property of a discrete subset `A` lets its points be moved along arbitrary
prescribed paths by a deformation of the whole space
(`TauCeti.HasHomotopyExtensionProperty.exists_homotopy_apply_eq`). In a path-connected manifold
this moves any finite set of points to one point: there is a map homotopic to the identity which
is constant on the finite set (`Set.Finite.exists_homotopic_id_forall_apply_eq`). This is how, in
Morse homology with differential graded coefficients, the critical points are joined to a
basepoint, so that the paths of broken trajectories between critical points become loops at the
basepoint (Barraud–Cornea, who collapse an embedded tree through the critical points; the time-one
map of a deformation collapsing the tree is such a map).

## Main results

* `TauCeti.HasHomotopyExtensionProperty.union_of_eqOn`: the union of two closed subsets with the
  homotopy extension property separated by a continuous function has the property.
* `Set.Finite.hasHomotopyExtensionProperty`: in a locally compact Hausdorff space, a finite set of
  points with the homotopy extension property has the property.
* `TauCeti.hasHomotopyExtensionProperty_singleton_of_chartedSpace` and
  `Set.Finite.hasHomotopyExtensionProperty_of_chartedSpace`: points and finite sets of a Hausdorff
  space charted on a proper real normed space have the homotopy extension property.
* `TauCeti.HasHomotopyExtensionProperty.exists_homotopy_apply_eq`: the points of a discrete
  subset with the homotopy extension property can be moved along prescribed paths by a
  deformation of the whole space.
* `Set.Finite.exists_homotopic_id_forall_apply_eq`: in a path-connected Hausdorff space charted on
  a proper real normed space, a finite set is sent to any given point by a map homotopic to the
  identity.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the section "The Homotopy Extension Property".
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152, Section 6, for NDR pairs.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
-/

public section

open Set unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

/-! ### Unions of separated closed cofibrations -/

/-- NDR data for the union of two subsets with NDR data, separated by a continuous function `φ`
with `φ = 0` on `A` and `φ = 1` on `B`. The deformation of `A` runs at full speed where
`φ ≤ 1 / 6` and is cut off before `φ` reaches `1 / 3`; the deformation of `B` runs at full speed
where `5 / 6 ≤ φ` and is cut off before `φ` drops to `2 / 3`. The two cut-off deformations are
glued along the level `φ = 1 / 2`, where neither moves any point. -/
private noncomputable def ndrPairUnion (N : NDRPair A) (M : NDRPair B) (φ : C(X, ℝ))
    (hφA : EqOn φ 0 A) (hφB : EqOn φ 1 B) : NDRPair (A ∪ B) where
  control := ⟨fun x ↦ min (max (N.control x) (projIcc 0 1 zero_le_one (6 * φ x)))
    (max (M.control x) (projIcc 0 1 zero_le_one (6 - 6 * φ x))), by fun_prop⟩
  control_eq_zero_iff x := by
    simp only [ContinuousMap.coe_mk, mem_union]
    constructor
    · intro h
      rcases min_eq_bot.1 h with h | h
      · exact Or.inl ((N.control_eq_zero_iff x).1 (max_eq_bot.1 h).1)
      · exact Or.inr ((M.control_eq_zero_iff x).1 (max_eq_bot.1 h).1)
    · rintro (hx | hx)
      · refine min_eq_bot.2 (Or.inl (max_eq_bot.2 ⟨(N.control_eq_zero_iff x).2 hx, ?_⟩))
        exact projIcc_eq_zero.2 (by simp [hφA hx])
      · refine min_eq_bot.2 (Or.inr (max_eq_bot.2 ⟨(M.control_eq_zero_iff x).2 hx, ?_⟩))
        exact projIcc_eq_zero.2 (by simp [hφB hx])
  deformation :=
    ⟨fun p ↦ if φ p.2 ≤ 1 / 2
      then N.deformation (p.1 * projIcc 0 1 zero_le_one (2 - 6 * φ p.2), p.2)
      else M.deformation (p.1 * projIcc 0 1 zero_le_one (6 * φ p.2 - 4), p.2),
    Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const fun p hp ↦ by
      rw [hp, projIcc_eq_zero.2 (by norm_num), projIcc_eq_zero.2 (by norm_num), mul_zero,
        N.deformation_zero, M.deformation_zero]⟩
  deformation_zero x := by
    simp only [ContinuousMap.coe_mk, zero_mul, N.deformation_zero, M.deformation_zero, ite_self]
  deformation_of_mem t x hx := by
    rcases hx with hx | hx
    · simp [hφA hx, N.deformation_of_mem _ hx]
    · simp [hφB hx, M.deformation_of_mem _ hx, (by norm_num : ¬(1 : ℝ) ≤ 2⁻¹)]
  deformation_one_mem {x} hx := by
    simp only [ContinuousMap.coe_mk, one_mul] at hx ⊢
    rcases min_lt_iff.1 hx with h | h
    · -- Here `φ x < 1 / 6`, so the deformation of `A` runs at full speed.
      have hφ : φ x < 1 / 6 := by
        by_contra hge
        exact (max_lt_iff.1 h).2.ne (projIcc_eq_one.2 (by linarith [not_lt.1 hge]))
      simp only [show φ x ≤ 1 / 2 by linarith, ↓reduceIte, projIcc_eq_one.2 (by linarith :
        (1 : ℝ) ≤ 2 - 6 * φ x)]
      exact Or.inl (N.deformation_one_mem (max_lt_iff.1 h).1)
    · -- Here `5 / 6 < φ x`, so the deformation of `B` runs at full speed.
      have hφ : 5 / 6 < φ x := by
        by_contra hge
        exact (max_lt_iff.1 h).2.ne (projIcc_eq_one.2 (by linarith [not_lt.1 hge]))
      simp only [show ¬φ x ≤ 1 / 2 by linarith, ↓reduceIte, projIcc_eq_one.2 (by linarith :
        (1 : ℝ) ≤ 6 * φ x - 4)]
      exact Or.inr (M.deformation_one_mem (max_lt_iff.1 h).1)

/-- **The union of two closed cofibrations separated by a function is a closed cofibration.** If
closed subsets `A` and `B` have the homotopy extension property, and a continuous function `φ`
vanishes on `A` and is equal to `1` on `B`, then `A ∪ B` has the homotopy extension property. -/
theorem HasHomotopyExtensionProperty.union_of_eqOn (hA : HasHomotopyExtensionProperty A)
    (hAc : IsClosed A) (hB : HasHomotopyExtensionProperty B) (hBc : IsClosed B) {φ : C(X, ℝ)}
    (hφA : EqOn φ 0 A) (hφB : EqOn φ 1 B) : HasHomotopyExtensionProperty (A ∪ B) := by
  obtain ⟨N⟩ := nonempty_ndrPair_iff.2 ⟨hAc, hA⟩
  obtain ⟨M⟩ := nonempty_ndrPair_iff.2 ⟨hBc, hB⟩
  exact (ndrPairUnion N M φ hφA hφB).hasHomotopyExtensionProperty

end TauCeti

/-- **Finite sets of points with the homotopy extension property have it.** In a locally compact
Hausdorff space, a finite set each of whose points has the homotopy extension property has the
homotopy extension property. -/
theorem Set.Finite.hasHomotopyExtensionProperty {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] {S : Set X} (hS : S.Finite)
    (h : ∀ x ∈ S, TauCeti.HasHomotopyExtensionProperty ({x} : Set X)) :
    TauCeti.HasHomotopyExtensionProperty S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact TauCeti.hasHomotopyExtensionProperty_empty
  | @insert a S ha hS ih =>
    -- Separate the new point from the others by an Urysohn function.
    obtain ⟨φ, hφa, hφS, -⟩ := exists_continuous_zero_one_of_isCompact isCompact_singleton
      hS.isClosed (disjoint_singleton_left.2 ha)
    rw [insert_eq]
    exact (h a (mem_insert a S)).union_of_eqOn isClosed_singleton
      (ih fun x hx ↦ h x (mem_insert_of_mem a hx)) hS.isClosed hφa hφS

namespace TauCeti

/-! ### Points and finite sets of manifolds -/

section ChartedSpace

variable (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

include E in
/-- **Points of a manifold are closed cofibrations.** In a Hausdorff space charted on a proper real
normed space, every point has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_singleton_of_chartedSpace (x : M) :
    HasHomotopyExtensionProperty ({x} : Set M) := by
  have h := (chartAt E x).hasHomotopyExtensionProperty_symm_image_segment
    (x := chartAt E x x) (y := chartAt E x x) (by simp [segment_same])
  rwa [segment_same, image_singleton, (chartAt E x).left_inv (mem_chart_source E x)] at h

end ChartedSpace

/-! ### Moving points along prescribed paths -/

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- **Moving the points of a discrete closed cofibration along prescribed paths.** If a discrete
subset `A` has the homotopy extension property and `γ a` is a path starting at each `a ∈ A`, there
is a deformation `F` of the whole space, starting at the identity, which moves each `a ∈ A` along
`γ a`. -/
theorem HasHomotopyExtensionProperty.exists_homotopy_apply_eq [DiscreteTopology A]
    (hA : HasHomotopyExtensionProperty A) (γ : A → C(I, X)) (hγ : ∀ a, γ a 0 = a) :
    ∃ F : C(I × X, X), (∀ x, F (0, x) = x) ∧ ∀ (t : I) (a : A), F (t, a) = γ a t :=
  hA.exists_extension (ContinuousMap.id X)
    ⟨fun p ↦ γ p.2 p.1, continuous_prod_of_discrete_right.2 fun a ↦ (γ a).continuous⟩ hγ

end TauCeti

section ChartedSpace

variable (E : Type*) {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S : Set M}

include E in
/-- **Finite sets of points of a manifold are closed cofibrations.** In a Hausdorff space charted
on a proper real normed space, every finite set has the homotopy extension property. -/
theorem Set.Finite.hasHomotopyExtensionProperty_of_chartedSpace (hS : S.Finite) :
    TauCeti.HasHomotopyExtensionProperty S :=
  have := ChartedSpace.locallyCompactSpace E M
  hS.hasHomotopyExtensionProperty fun x _ ↦
    TauCeti.hasHomotopyExtensionProperty_singleton_of_chartedSpace E x

include E in
/-- **Collapsing finitely many points of a manifold to one point, up to homotopy.** In a
path-connected Hausdorff space charted on a proper real normed space, for every finite set `S` and
every point `y₀` there is a map homotopic to the identity which sends all of `S` to `y₀`. -/
theorem Set.Finite.exists_homotopic_id_forall_apply_eq [PathConnectedSpace M] (hS : S.Finite)
    (y₀ : M) :
    ∃ θ : C(M, M), (ContinuousMap.id M).Homotopic θ ∧ ∀ x ∈ S, θ x = y₀ := by
  have : Finite S := hS.to_subtype
  -- Move each point of `S` to `y₀` along a path, by a deformation of `M`.
  obtain ⟨F, hF₀, hFS⟩ :=
    (hS.hasHomotopyExtensionProperty_of_chartedSpace E).exists_homotopy_apply_eq
      (fun a ↦ (PathConnectedSpace.somePath (a : M) y₀ : C(I, M))) fun a ↦ by simp
  refine ⟨⟨fun x ↦ F (1, x), by fun_prop⟩,
    ⟨{ toContinuousMap := F, map_zero_left := hF₀, map_one_left := fun _ ↦ rfl }⟩,
    fun x hx ↦ ?_⟩
  simpa using hFS 1 ⟨x, hx⟩

end ChartedSpace
