/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PushoutI.Reduced
public import TauCeti.GroupTheory.TrivialIntersection
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Elliptic
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Malnormal
import TauCeti.GroupTheory.GTree.Centralizer
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers in an amalgamated product

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`. This file proves two results on centralizers in it, each under its own
hypotheses.

If an element `g` of a factor `G i` is not conjugate in `G i` into the amalgamated subgroup
`φ i H`, then every element of the amalgamated product commuting with `g` lies in `G i`: the
centralizer of `g` in the amalgamated product is its centralizer in `G i`.

Let now `E = A ∗_C B` be an amalgamated product of two groups, indexed by `Bool`. In the action of
`E` on its Bass–Serre tree, whose vertex stabilizers are the conjugates of `A` and `B`, an element
either fixes a vertex, and is then conjugate into one of the factors, or is hyperbolic: it
translates a line, its axis. Suppose that `C` is malnormal in one factor, and let `x ∈ E` be
conjugate into neither factor. Then `x` is hyperbolic, and an element commuting with `x`
translates the axis of `x` (`TauCeti.GTree.IsHyperbolic.isCyclic_centralizer`). At a vertex of
the malnormal factor, the stabilizer of the two edges of the axis is `C ∩ a C a⁻¹ = 1` for an
`a ∉ C` (`TauCeti.GraphOfGroups.bassSerreTree_segment_fixingSubgroup_range_eq_bot`), so the
centralizer of `x` acts faithfully on the axis by translations: it embeds in `ℤ` and is cyclic.

## Main results

* `Monoid.PushoutI.centralizer_of_eq_map`: the centralizer of an element of a factor that is not
  conjugate in that factor into the amalgamated subgroup.
* `Monoid.PushoutI.isCyclic_centralizer`: in `A ∗_C B` with `C` malnormal in one factor, the
  centralizer of an element conjugate into neither factor is cyclic.

## Implementation notes

The first result is proved with normal forms rather than the Bass–Serre tree: write an element
`x` commuting with `g` as `a * w` with `a ∈ G i` and `w` a reduced word not starting in `G i`
(`Monoid.PushoutI.exists_eq_of_mul_list_prod`). If `w` is nonempty, then
`x⁻¹ * g * x = w⁻¹ * (a⁻¹ * g * a) * w` lies in no factor
(`Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_of`), but it equals `g`.

For the second, `A ∗_C B` is identified with the fundamental group of the segment graph of groups
of `C → A` and `C → B` (`TauCeti.GraphOfGroups.π₁Equiv`,
`TauCeti.GraphOfGroups.π₁Tree.equivPushoutI` and `TauCeti.GraphOfGroups.segmentPushoutIEquiv`),
which acts on its Bass–Serre tree `TauCeti.GraphOfGroups.bassSerreTree`.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem), §4 (the tree of an
  amalgam) and §6 (hyperbolic automorphisms and their axes).
* W. Magnus, A. Karrass, D. Solitar, *Combinatorial group theory*, Theorem 4.5 (commuting
  elements of an amalgamated product), as used in G. Baumslag, A. Myasnikov, V. Remeslennikov,
  *Algebraic geometry over groups I: Algebraic sets and ideal theory*, J. Algebra 219 (1999),
  proof of Theorem A2.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, Lemma 19.
-/

public section

namespace Monoid.PushoutI

open Function Subgroup

section General

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Centralizers of factor elements away from the amalgamated subgroup.** If an element `g` of
a factor `G i` of an amalgamated product of groups is not conjugate in `G i` into the amalgamated
subgroup, then its centralizer in the amalgamated product is its centralizer in `G i`. -/
theorem centralizer_of_eq_map (hφ : ∀ i, Injective (φ i)) {i : ι} {g : G i}
    (hg : ∀ k : G i, k * g * k⁻¹ ∉ (φ i).range) :
    centralizer {of (φ := φ) i g} = (centralizer {g}).map (of i) := by
  refine le_antisymm (fun x hx => ?_) (map_le_iff_le_comap.2 fun k hk => ?_)
  · obtain ⟨a, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod i x
    have hx' : (of (φ := φ) i a * (L.map fun l => of l.1 l.2).prod)⁻¹ * of i g *
        (of i a * (L.map fun l => of l.1 l.2).prod) = of i g := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hx, inv_mul_cancel_left]
    rcases eq_or_ne L [] with rfl | hL
    · refine ⟨a, mem_centralizer_singleton_iff.2 (of_injective hφ i ?_), by simp⟩
      simpa using (mem_centralizer_singleton_iff.1 hx).eq
    · -- Otherwise `x⁻¹ * g * x` is a reduced word of length at least three.
      refine (list_prod_inv_mul_of_mul_list_prod_notMem_range_of hφ hL hc hred (hg a⁻¹) hhead
        ⟨g, ?_⟩).elim
      rw [← hx']
      simp [mul_assoc]
  · rw [mem_comap, mem_centralizer_singleton_iff, commute_iff_eq, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.1 hk).eq]

end General

/-! ### Centralizers of hyperbolic elements -/

section Bool

open TauCeti GraphOfGroups

variable {H : Type*} [Group H] {G : Bool → Type*} [∀ b, Group (G b)] {φ : ∀ b, H →* G b}

/-- The fundamental group at a vertex `v₀` of the segment graph of groups of `A ∗_C B` is
`A ∗_C B`. -/
private noncomputable def segmentEquiv (hφ : ∀ b, Injective (φ b)) (v₀ : SerreGraph.segment.V) :
    π₁ (segment (φ false) (φ true) (hφ false) (hφ true)) v₀ ≃* PushoutI φ :=
  (π₁Equiv _ v₀ SerreGraph.segment_isTree.spanningTree).trans
    ((π₁Tree.equivPushoutI _ _ _ _ (SerreGraph.segment_spanningTree_darts_nonempty _)).trans
      (segmentPushoutIEquiv φ hφ))

/-- The vertex stabilizers `p A_b p⁻¹` of the Bass–Serre tree of `A ∗_C B` are conjugates of the
factors. -/
private theorem exists_mul_segmentEquiv_vertexHom_mul_inv_mem (hφ : ∀ b, Injective (φ b))
    {v₀ b : SerreGraph.segment.V}
    (p : (segment (φ false) (φ true) (hφ false) (hφ true)).Path ⟨v₀⟩ ⟨b⟩)
    (y : (segment (φ false) (φ true) (hφ false) (hφ true)).vertexGroup b) :
    ∃ w, w * segmentEquiv hφ v₀ (π₁.vertexHom p y) * w⁻¹ ∈ (of (φ := φ) (id b)).range := by
  -- Along the tree path `q` from `v₀` to `b`, the conjugate `q A_b q⁻¹` is the factor at `b`.
  set q := SerreGraph.segment_isTree.spanningTree.path v₀ b
  rw [π₁.vertexHom_eq_conj_comp_apply ((dartPrefunctor _).mapPath q) p]
  refine ⟨(segmentEquiv hφ v₀ (π₁.mk (p.comp ((dartPrefunctor _).mapPath q).reverse)))⁻¹, ?_⟩
  simp only [map_mul, map_inv, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have h : segmentEquiv hφ v₀ (π₁.vertexHom ((dartPrefunctor _).mapPath q) y) =
      segmentPushoutIEquiv φ hφ (of b y) :=
    congrArg _ ((congrArg _ (π₁Equiv_segment_vertexHom_mapPath q y)).trans
      (π₁Tree.equivPushoutI_of ..))
  cases b
  · exact ⟨y, (h.trans (segmentPushoutIEquiv_of_false φ hφ y)).symm⟩
  · exact ⟨y, (h.trans (segmentPushoutIEquiv_of_true φ hφ y)).symm⟩

/-- In an amalgamated product `A ∗_C B` in which `C` is malnormal in one of the factors, the
centralizer of an element conjugate into neither factor is cyclic. -/
theorem isCyclic_centralizer (hφ : ∀ b, Injective (φ b)) {b : Bool}
    (hT : IsTISubgroup (φ b).range) {x : PushoutI φ}
    (hx : ∀ (i : Bool) (y : PushoutI φ), y * x * y⁻¹ ∉ (of i).range) :
    IsCyclic (centralizer {x}) := by
  set e := (segmentEquiv hφ (SerreGraph.segment.src false)).symm
  -- The vertex stabilizers of the Bass–Serre tree are the conjugates of the factors.
  have hhyp : (bassSerreTree _ _).IsHyperbolic (e x) := by
    by_contra hell
    obtain ⟨i, p, y, hy⟩ := bassSerreTree_isElliptic_iff.1 (GTree.not_isHyperbolic_iff.1 hell)
    obtain ⟨w, hw⟩ := exists_mul_segmentEquiv_vertexHom_mul_inv_mem hφ p y
    rw [hy, MulEquiv.apply_symm_apply] at hw
    exact hx (id i) w hw
  obtain ⟨c, -, hc, -, hrange⟩ := hhyp.exists_range_eq_axis (GTree.axis_nonempty _ _).some_mem
  have hfix := bassSerreTree_segment_fixingSubgroup_range_eq_bot (b := b)
    (by cases b
        · rw [segmentMaps_false]
          exact hT
        · rw [segmentMaps_true]
          exact hT) hc
  rw [hrange] at hfix
  exact (MulEquiv.centralizerMap e Set.image_singleton).isCyclic.2 (hhyp.isCyclic_centralizer hfix)

end Bool

end Monoid.PushoutI
