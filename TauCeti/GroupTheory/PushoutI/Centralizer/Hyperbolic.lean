/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TrivialIntersection
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Elliptic
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Malnormal
import TauCeti.GroupTheory.GTree.Centralizer
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of hyperbolic elements of an amalgamated product

Let `E = A ∗_C B` be an amalgamated product of two groups, Mathlib's `Monoid.PushoutI` indexed by
`Bool`, with injective maps of `C` into the factors. In the action of `E` on its Bass–Serre tree,
whose vertex stabilizers are the conjugates of `A` and `B`, an element either fixes a vertex, and
is then conjugate into one of the factors, or is hyperbolic: it translates a line, its axis.

Suppose that `C` is malnormal in one factor, and let `x ∈ E` be conjugate into neither factor.
Then `x` is hyperbolic, and an element commuting with `x` translates the axis of `x`
(`TauCeti.GTree.exists_smul_eq_add_of_commute`). At a vertex of the malnormal factor the axis
leaves along two distinct edges, and the intersection of the stabilizers of these two edges is
conjugate to `C ∩ a C a⁻¹` for some `a ∉ C`, so it is trivial. Hence only the identity fixes the
axis pointwise (`TauCeti.GraphOfGroups.bassSerreTree_segment_fixingSubgroup_range_eq_bot`), and the
centralizer of `x` acts faithfully on the axis by translations: it embeds in `ℤ` and is cyclic
(`TauCeti.GTree.IsHyperbolic.isCyclic_centralizer`).

The centralizers of elements of a factor are described by `Monoid.PushoutI.centralizer_of_eq_map`
and `Monoid.PushoutI.centralizer_of_eq_map_of_isTISubgroup`.

## Main results

* `Monoid.PushoutI.isCyclic_centralizer`: in `A ∗_C B` with `C` malnormal in one factor, the
  centralizer of an element conjugate into neither factor is cyclic.

## Implementation notes

`A ∗_C B` is identified with the fundamental group of the segment graph of groups of `C → A` and
`C → B` (`TauCeti.GraphOfGroups.π₁.equivPushoutIBool`), which acts on its Bass–Serre tree
`TauCeti.GraphOfGroups.bassSerreTree`.

## References

* J.-P. Serre, *Trees*, Chapter I, §4 (the tree of an amalgam) and §6 (hyperbolic automorphisms
  and their axes).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, Lemma 19.
-/

public section

namespace Monoid.PushoutI

open Function Subgroup TauCeti GraphOfGroups

variable {H : Type*} [Group H] {G : Bool → Type*} [∀ b, Group (G b)] {φ : ∀ b, H →* G b}

/-- In an amalgamated product `A ∗_C B` in which `C` is malnormal in one of the factors, the
centralizer of an element conjugate into neither factor is cyclic. -/
theorem isCyclic_centralizer (hφ : ∀ b, Injective (φ b)) {b : Bool}
    (hT : IsTISubgroup (φ b).range) {x : PushoutI φ}
    (hx : ∀ (i : Bool) (y : PushoutI φ), y * x * y⁻¹ ∉ (of i).range) :
    IsCyclic (centralizer {x}) := by
  set e := (π₁.equivPushoutIBool φ hφ (SerreGraph.segment.src false)).symm
  -- The vertex stabilizers of the Bass–Serre tree are the conjugates of the factors.
  have hhyp : (bassSerreTree _ _).IsHyperbolic (e x) := by
    by_contra hell
    obtain ⟨i, p, y, hy⟩ := bassSerreTree_isElliptic_iff.1 (GTree.not_isHyperbolic_iff.1 hell)
    obtain ⟨w, hw⟩ : ∃ w, x = w * of (φ := φ) (id i) (segmentVertexEquiv φ hφ i y) * w⁻¹ :=
      ⟨_, ((MulEquiv.apply_symm_apply _ x).symm.trans (congrArg _ hy.symm)).trans
        (π₁.equivPushoutIBool_vertexHom φ hφ p y)⟩
    exact hx (id i) w⁻¹ ⟨segmentVertexEquiv φ hφ i y, by simp [hw, mul_assoc]⟩
  obtain ⟨c, -, hc, -, hrange⟩ := hhyp.exists_range_eq_axis (GTree.axis_nonempty _ _).some_mem
  have hfix := bassSerreTree_segment_fixingSubgroup_range_eq_bot (b := b)
    (by cases b
        · rw [segmentMaps_false]
          exact hT
        · rw [segmentMaps_true]
          exact hT) hc
  rw [hrange] at hfix
  exact (MulEquiv.centralizerMap e Set.image_singleton).isCyclic.2 (hhyp.isCyclic_centralizer hfix)

end Monoid.PushoutI
