/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
import TauCeti.GroupTheory.GraphOfGroups.OneEdge
import TauCeti.GroupTheory.GTree.Axis

/-!
# Finite subgroups of the fundamental group of a graph of groups

A finite group acting on a tree without inversions fixes a vertex
(`TauCeti.GTree.isEllipticSubgroup_of_finite`). Applied to the action of the fundamental group
`π₁(𝔸, a)` of a graph of groups on its Bass–Serre tree, whose vertex stabilizers are the
conjugates `p A_b p⁻¹` of the vertex groups, this shows that every finite subgroup of `π₁(𝔸, a)`,
and every element of finite order, lies in a conjugate of a vertex group. Consequently the
fundamental group of a graph of torsion-free groups is torsion-free, and so is an HNN extension of
a torsion-free group, the fundamental group of a loop of groups.

## Main results

* `TauCeti.GraphOfGroups.π₁.exists_le_range_vertexHom_of_finite`: a finite subgroup of
  `π₁(𝔸, a)` lies in a conjugate `p A_b p⁻¹` of a vertex group.
* `TauCeti.GraphOfGroups.π₁.exists_vertexHom_eq_of_isOfFinOrder`: an element of finite order of
  `π₁(𝔸, a)` is the conjugate `p y p⁻¹` of an element `y` of finite order of a vertex group.
* `TauCeti.GraphOfGroups.π₁.instIsMulTorsionFree`,
  `TauCeti.GraphOfGroups.π₁Tree.isMulTorsionFree`: the fundamental group of a graph of
  torsion-free groups is torsion-free.
* `HNNExtension.instIsMulTorsionFree`: an HNN extension of a torsion-free group is torsion-free.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12 (the Bass–Serre tree and its vertex
  stabilizers) and §6.5, Proposition 26 and its corollaries (Serre's lemma).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2, p. 16 (a
  subgroup is elliptic in the Bass–Serre tree exactly when it lies in a conjugate of a vertex
  group; finite groups have Serre's property (FA)).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Chapter IV, Theorem 2.4 (elements of
  finite order of an HNN extension are conjugate into the base group).
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

namespace π₁

/-- A finite subgroup of `π₁(𝔸, a)` lies in a conjugate `p A_b p⁻¹` of a vertex group: it fixes a
vertex of the Bass–Serre tree. -/
theorem exists_le_range_vertexHom_of_finite (H : Subgroup (π₁ 𝔸 a)) [Finite H] :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), H ≤ (vertexHom p).range := by
  obtain ⟨y, hy⟩ := GTree.isEllipticSubgroup_iff.mp
    (GTree.isEllipticSubgroup_of_finite (T := bassSerreTree 𝔸 a) H)
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  exact ⟨b, p, stabilizer_bassSerreVertex p ▸ hy⟩

/-- An element of finite order of `π₁(𝔸, a)` is the conjugate `p y p⁻¹` of an element `y` of finite
order of a vertex group `A_b`. -/
theorem exists_vertexHom_eq_of_isOfFinOrder {g : π₁ 𝔸 a} (hg : IsOfFinOrder g) :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (y : 𝔸.vertexGroup b),
      IsOfFinOrder y ∧ vertexHom p y = g := by
  obtain ⟨y, hy⟩ := GTree.isElliptic_iff.mp
    (GTree.isElliptic_of_isOfFinOrder (T := bassSerreTree 𝔸 a) hg)
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  obtain ⟨z, rfl⟩ : g ∈ (vertexHom p).range := stabilizer_bassSerreVertex p ▸ hy
  exact ⟨b, p, z, (vertexHom_injective p).isOfFinOrder_iff.mp hg, rfl⟩

/-- The fundamental group of a graph of torsion-free groups is torsion-free. -/
instance instIsMulTorsionFree [∀ b, IsMulTorsionFree (𝔸.vertexGroup b)] :
    IsMulTorsionFree (π₁ 𝔸 a) :=
  isMulTorsionFree_iff_not_isOfFinOrder.mpr fun g hg1 hg ↦ by
    obtain ⟨b, p, y, hy, rfl⟩ := exists_vertexHom_eq_of_isOfFinOrder hg
    exact hg1 (by rw [hy.eq_one', map_one])

end π₁

/-- The fundamental group `π₁(𝔸, T)` of a graph of torsion-free groups, relative to a spanning
tree `T`, is torsion-free. -/
theorem π₁Tree.isMulTorsionFree [∀ b, IsMulTorsionFree (𝔸.vertexGroup b)] (T : Γ.SpanningTree) :
    IsMulTorsionFree (π₁Tree 𝔸 T.darts) := by
  obtain ⟨v⟩ := ((SerreGraph.connected_iff _).mp T.isTree.connected).1
  exact (π₁Equiv 𝔸 v T).symm.injective.isMulTorsionFree (π₁Equiv 𝔸 v T).symm.toMonoidHom

end GraphOfGroups

end TauCeti

namespace HNNExtension

open TauCeti GraphOfGroups

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The second edge map `A →* G`, `a ↦ φ a`, of the loop of groups of `HNNExtension G A B φ`. -/
private abbrev loopSnd (φ : A ≃* B) : A →* G :=
  B.subtype.comp φ.toMonoidHom

private theorem loopSnd_injective : Function.Injective (loopSnd φ) :=
  B.subtype_injective.comp φ.injective

/-- The HNN extension along the identification `loopEquiv` of the loop of groups with edge maps
`A.subtype` and `loopSnd φ`, which is how `π₁Tree.equivHNNExtension` presents it. -/
private abbrev LoopHNN (φ : A ≃* B) : Type _ :=
  HNNExtension G A.subtype.range (loopSnd φ).range
    (loopEquiv _ _ A.subtype_injective loopSnd_injective)

/-- `HNNExtension G A B φ →* LoopHNN φ`, the identity on `G` and on the stable letter. -/
private noncomputable def toLoopHNN : HNNExtension G A B φ →* LoopHNN φ :=
  lift of t fun a ↦ by
    simpa [MonoidHom.ofInjective_apply] using
      t_mul_of (φ := loopEquiv _ _ A.subtype_injective (loopSnd_injective (φ := φ)))
      (MonoidHom.ofInjective A.subtype_injective a)

/-- `LoopHNN φ →* HNNExtension G A B φ`, the identity on `G` and on the stable letter. -/
private noncomputable def ofLoopHNN : LoopHNN φ →* HNNExtension G A B φ :=
  lift of t fun a ↦ by
    obtain ⟨a, rfl⟩ := (MonoidHom.ofInjective A.subtype_injective).surjective a
    simpa [MonoidHom.ofInjective_apply] using t_mul_of (φ := φ) a

private theorem ofLoopHNN_comp_toLoopHNN :
    (ofLoopHNN (φ := φ)).comp toLoopHNN = MonoidHom.id _ :=
  hom_ext (MonoidHom.ext fun _ ↦ by simp [toLoopHNN, ofLoopHNN]) (by simp [toLoopHNN, ofLoopHNN])

private theorem toLoopHNN_injective : Function.Injective (toLoopHNN (φ := φ)) :=
  Function.LeftInverse.injective (DFunLike.congr_fun ofLoopHNN_comp_toLoopHNN)

/-- **HNN extensions of torsion-free groups are torsion-free.** The HNN extension
`⟨G, t | t a t⁻¹ = φ a⟩` of a torsion-free group `G` along an isomorphism `φ : A ≃* B` of two
subgroups is torsion-free. -/
instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree (HNNExtension G A B φ) := by
  let 𝔸 := loop A.subtype (loopSnd φ) A.subtype_injective loopSnd_injective
  have : ∀ b, IsMulTorsionFree (𝔸.vertexGroup b) := fun _ ↦ inferInstanceAs (IsMulTorsionFree G)
  have h := π₁Tree.isMulTorsionFree (𝔸 := 𝔸) (SerreGraph.roseTree Unit)
  rw [SerreGraph.roseTree_darts] at h
  exact Function.Injective.isMulTorsionFree
    ((π₁Tree.equivHNNExtension _ _ _ _).symm.toMonoidHom.comp toLoopHNN)
    ((π₁Tree.equivHNNExtension _ _ _ _).symm.injective.comp toLoopHNN_injective)

end HNNExtension
