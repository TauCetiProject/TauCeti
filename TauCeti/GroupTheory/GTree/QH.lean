/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.SurfaceGroup.Signed
import Mathlib.Tactic.Group

/-!
# Quadratically hanging vertices

A vertex `v` of a `G`-tree `T` is *quadratically hanging* (QH), relative to a family `ℋ` of
subgroups of `G`, when its stabilizer `Q` is identified with the fundamental group `S±(g, m)` of
a compact surface of negative Euler characteristic in such a way that every incident edge
stabilizer, and every intersection `Q ∩ g H g⁻¹` with `H ∈ ℋ`, is trivial or contained in a
conjugate of a boundary subgroup `⟨pⱼ⟩`. This is the case of trivial fiber and of a surface,
rather than a 2-orbifold, of the definition of Guirardel and Levitt; the surface and the
isomorphism are part of the structure.

The incident subgroups at `v` (`TauCeti.GTree.incidentSubgroups`) are the incident edge
stabilizers and the intersections `Q ∩ g H g⁻¹`, as subgroups of `Q`.

## Main definitions

* `TauCeti.GTree.QH T ℋ v`: a QH structure at `v`, with `QH.boundarySubgroup` and `QH.IsUsed`.
* `TauCeti.GTree.IsQH T ℋ v`: the vertex `v` carries a QH structure.
* `TauCeti.GTree.QH.point`: the QH structure at the vertex of the one-vertex tree of a surface
  group, relative to a family of peripheral subgroups.

## Main results

* `TauCeti.GTree.QH.ne_top_of_mem_incidentSubgroups`: incident subgroups are proper subgroups of
  the stabilizer of a QH vertex; hence a QH vertex is the only vertex fixed by its stabilizer
  (`TauCeti.GTree.QH.eq_of_stabilizer_le`).
* `TauCeti.GTree.not_isQH_of_isMulCommutative`: a vertex with abelian stabilizer is not QH.
* `TauCeti.GTree.isQH_point`: the vertex of the one-vertex tree of `S±(g, m)`, relative to a
  family of peripheral subgroups such as the boundary subgroups, is QH; a boundary component is
  used exactly when the family contains a nontrivial subgroup of a conjugate of its boundary
  subgroup (`TauCeti.GTree.QH.isUsed_point_iff`).

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.2,
  Definitions 5.13 and 5.15.
-/

public section

universe u v w

open MulAction Subgroup

namespace TauCeti

namespace GTree

open SurfaceGroup

variable {G : Type w} [Group G] (T : GTree.{u, v} G)

/-- A quadratically hanging structure at a vertex `v` of a `G`-tree, relative to a family `ℋ` of
subgroups: an isomorphism of the stabilizer of `v` with the fundamental group `S±(g, m)` of a
compact surface of negative Euler characteristic, carrying every incident subgroup to a
peripheral subgroup. -/
structure QH (ℋ : Set (Subgroup G)) (v : T.V) where
  /-- Whether the surface is orientable; in genus `0` both values give the planar surface. -/
  orientable : Bool
  /-- The genus of the surface. -/
  genus : ℕ
  /-- The number of boundary components of the surface. -/
  boundary : ℕ
  /-- The surface has negative Euler characteristic. -/
  eulerChar_neg : Signed.eulerChar orientable genus boundary < 0
  /-- The isomorphism of the vertex stabilizer with the surface group. -/
  surfaceEquiv : stabilizer G v ≃* Signed orientable genus boundary
  /-- Incident subgroups are carried to peripheral subgroups. -/
  isPeripheral_map : ∀ K ∈ T.incidentSubgroups ℋ v,
    Signed.IsPeripheral (K.map surfaceEquiv.toMonoidHom)

/-- A vertex is quadratically hanging, relative to `ℋ`, when it carries a QH structure. -/
def IsQH (ℋ : Set (Subgroup G)) (v : T.V) : Prop :=
  Nonempty (T.QH ℋ v)

theorem isQH_iff {ℋ : Set (Subgroup G)} {v : T.V} : T.IsQH ℋ v ↔ Nonempty (T.QH ℋ v) := Iff.rfl

namespace QH

variable {T} {ℋ : Set (Subgroup G)} {v : T.V} (q : T.QH ℋ v)

/-- The boundary subgroup of `G` corresponding to the boundary element `pⱼ` of the surface. -/
def boundarySubgroup (j : Fin q.boundary) : Subgroup G :=
  ((zpowers (Signed.peripheral q.orientable q.genus q.boundary j)).comap
    q.surfaceEquiv.toMonoidHom).map (stabilizer G v).subtype

theorem mem_boundarySubgroup_iff {j : Fin q.boundary} {g : G} :
    g ∈ q.boundarySubgroup j ↔ ∃ hg : g ∈ stabilizer G v,
      q.surfaceEquiv ⟨g, hg⟩ ∈
        zpowers (Signed.peripheral q.orientable q.genus q.boundary j) := by
  simp [boundarySubgroup]

theorem boundarySubgroup_le_stabilizer (j : Fin q.boundary) :
    q.boundarySubgroup j ≤ stabilizer G v := map_subtype_le _

/-- A boundary component is used when some nontrivial incident subgroup is carried into a
conjugate of its boundary subgroup. The incident subgroups are the incident edge stabilizers and
the intersections of the vertex stabilizer with the conjugates of the members of `ℋ`; Guirardel
and Levitt use the conjugates of members of `ℋ` contained in the vertex stabilizer instead of
these intersections. Nontriviality stands for their condition of finite index in the boundary
subgroup, which is infinite cyclic. -/
def IsUsed (j : Fin q.boundary) : Prop :=
  ∃ K ∈ T.incidentSubgroups ℋ v, K ≠ ⊥ ∧ ∃ s : Signed q.orientable q.genus q.boundary,
    K.map q.surfaceEquiv.toMonoidHom ≤
      (zpowers (Signed.peripheral q.orientable q.genus q.boundary j)).map
        (MulAut.conj s).toMonoidHom

theorem isUsed_iff {j : Fin q.boundary} :
    q.IsUsed j ↔ ∃ K ∈ T.incidentSubgroups ℋ v, K ≠ ⊥ ∧
      ∃ s : Signed q.orientable q.genus q.boundary, K.map q.surfaceEquiv.toMonoidHom ≤
        (zpowers (Signed.peripheral q.orientable q.genus q.boundary j)).map
          (MulAut.conj s).toMonoidHom := Iff.rfl

include q in
/-- Incident subgroups are proper subgroups of the stabilizer of a QH vertex. -/
theorem ne_top_of_mem_incidentSubgroups {K : Subgroup (stabilizer G v)}
    (hK : K ∈ T.incidentSubgroups ℋ v) : K ≠ ⊤ := by
  rintro rfl
  have := q.isPeripheral_map ⊤ hK
  rw [map_top_of_surjective _ q.surfaceEquiv.surjective] at this
  exact Signed.not_isPeripheral_top q.eulerChar_neg this

include q in
/-- A QH vertex is the only vertex fixed by its stabilizer. -/
theorem eq_of_stabilizer_le {w : T.V} (h : stabilizer G v ≤ stabilizer G w) : w = v := by
  by_contra hwv
  -- The stabilizer of `v` fixes the reduced path from `v` to `w`, hence its first dart.
  obtain ⟨p, hp, -⟩ := T.isTree.existsUnique_isReduced v w
  obtain ⟨e, he⟩ : ∃ e, e ∈ (SerreGraph.Path.darts T.toSerreGraph p).head? := by
    cases hd : SerreGraph.Path.darts T.toSerreGraph p with
    | nil => exact absurd (p.eq_of_darts_eq_nil _ hd).symm hwv
    | cons e _ => exact ⟨e, rfl⟩
  have hQ : stabilizer G v ≤ stabilizer G e := fun g hg =>
    SerreGraph.Aut.smul_eq_of_mem_darts T.isTree.isAcyclic (T.action g) hg (h hg) hp
      (List.mem_of_mem_head? he)
  exact q.ne_top_of_mem_incidentSubgroups (mem_incidentSubgroups_iff.mpr
    (.inl ⟨e, SerreGraph.Path.src_eq_of_mem_head?_darts _ p he, rfl⟩)) (subgroupOf_eq_top.mpr hQ)

end QH

/-- A vertex with abelian stabilizer is not quadratically hanging. -/
theorem not_isQH_of_isMulCommutative {ℋ : Set (Subgroup G)} {v : T.V}
    [IsMulCommutative (stabilizer G v)] : ¬T.IsQH ℋ v := fun ⟨q⟩ =>
  Signed.not_isMulCommutative_of_eulerChar_neg q.eulerChar_neg
    q.surfaceEquiv.surjective.isMulCommutative

/-- A vertex whose stabilizer is contained in a conjugate of a member of `ℋ` is not quadratically
hanging. -/
theorem not_isQH_of_stabilizer_le {ℋ : Set (Subgroup G)} {v : T.V} {H : Subgroup G} (hH : H ∈ ℋ)
    (g : G) (h : stabilizer G v ≤ H.map (MulAut.conj g).toMonoidHom) : ¬T.IsQH ℋ v := fun ⟨q⟩ =>
  q.ne_top_of_mem_incidentSubgroups (mem_incidentSubgroups_iff.mpr (.inr ⟨H, hH, g, rfl⟩))
    (subgroupOf_eq_top.mpr h)

/-! ### The one-vertex tree of a surface group -/

namespace QH

variable {o : Bool} {g m : ℕ} {ℋ : Set (Subgroup (Signed o g m))}

/-- The quadratically hanging structure at the vertex of the one-vertex tree of the fundamental
group `S±(g, m)` of a compact surface of negative Euler characteristic, relative to a family of
peripheral subgroups: the surface group itself, with the identity of the stabilizer. It is
reducible, so that the surface data of this structure are `o`, `g` and `m` themselves: its
boundary components are indexed by `Fin m` and its surface group is `Signed o g m`. -/
abbrev point (h : Signed.eulerChar o g m < 0) (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H)
    (x : (point.{u, v} (Signed o g m)).V) : (point.{u, v} (Signed o g m)).QH ℋ x where
  orientable := o
  genus := g
  boundary := m
  eulerChar_neg := h
  surfaceEquiv :=
    (MulEquiv.subgroupCongr (stabilizer_eq_top_of_subsingleton x)).trans Subgroup.topEquiv
  isPeripheral_map := by
    rw [incidentSubgroups_of_subsingleton]
    rintro K ⟨H, hH, s, rfl⟩
    convert (hℋ H hH).map_conj s using 1
    exact map_subgroupOf_eq_of_le (le_top.trans_eq (stabilizer_eq_top_of_subsingleton x).symm)

variable (h : Signed.eulerChar o g m < 0) (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H)
  (x : (GTree.point.{u, v} (Signed o g m)).V)

/-- The boundary subgroups of the one-vertex tree of a surface group are the cyclic subgroups
generated by the peripheral elements. -/
@[simp]
theorem boundarySubgroup_point (j : Fin m) :
    (QH.point h hℋ x).boundarySubgroup j = zpowers (Signed.peripheral o g m j) := by
  ext y
  simp [mem_boundarySubgroup_iff]

/-- On the one-vertex tree, the surface isomorphism carries `L ∩ Q` back to `L`. -/
private theorem map_subgroupOf_point (L : Subgroup (Signed o g m)) :
    (L.subgroupOf (stabilizer (Signed o g m) x)).map (QH.point h hℋ x).surfaceEquiv.toMonoidHom =
      L :=
  map_subgroupOf_eq_of_le (le_top.trans_eq (stabilizer_eq_top_of_subsingleton x).symm)

/-- At the vertex of the one-vertex tree of a surface group, a boundary component is used
exactly when the family `ℋ` contains a nontrivial subgroup of a conjugate of its boundary
subgroup. -/
theorem isUsed_point_iff {j : Fin m} :
    (QH.point h hℋ x).IsUsed j ↔ ∃ H ∈ ℋ, H ≠ ⊥ ∧ ∃ s : Signed o g m,
      H ≤ (zpowers (Signed.peripheral o g m j)).map (MulAut.conj s).toMonoidHom := by
  have h1 : (MulAut.conj (1 : Signed o g m)).toMonoidHom = MonoidHom.id _ := by ext; simp
  rw [isUsed_iff, incidentSubgroups_of_subsingleton]
  constructor
  · rintro ⟨K, ⟨H, hH, t, rfl⟩, hK, s, hs⟩
    rw [map_subgroupOf_point] at hs
    refine ⟨H, hH, fun hH0 => hK (by simp [hH0]), t⁻¹ * s, fun y hy => ?_⟩
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hs (mem_map_of_mem _ hy))
    refine mem_map.mpr ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom] at hzy ⊢
    rw [map_mul, MulAut.mul_apply, hzy, map_inv, MulAut.inv_apply_self]
  · rintro ⟨H, hH, hH0, s, hs⟩
    refine ⟨(H.map (MulAut.conj 1).toMonoidHom).subgroupOf _, ⟨H, hH, 1, rfl⟩,
      fun hK => hH0 ?_, s, ?_⟩
    · have := congrArg (map (QH.point h hℋ x).surfaceEquiv.toMonoidHom) hK
      rwa [map_subgroupOf_point, h1, map_id, Subgroup.map_bot] at this
    · rwa [map_subgroupOf_point, h1, map_id]

/-- At the vertex of the one-vertex tree of a surface group, relative to a family containing the
boundary subgroup `⟨pⱼ⟩`, the boundary component `j` is used. -/
theorem isUsed_point_of_mem {j : Fin m} (hj : zpowers (Signed.peripheral o g m j) ∈ ℋ) :
    (QH.point h hℋ x).IsUsed j :=
  (isUsed_point_iff h hℋ x).mpr ⟨_, hj, by
    simpa using Signed.peripheral_ne_one (by cases o <;> simp at h <;> lia) j,
    1, by simp⟩

end QH

/-- The vertex of the one-vertex tree of the fundamental group of a compact surface of negative
Euler characteristic is quadratically hanging relative to every family of peripheral
subgroups, in particular relative to the boundary subgroups. -/
theorem isQH_point {o : Bool} {g m : ℕ} (h : Signed.eulerChar o g m < 0)
    {ℋ : Set (Subgroup (Signed o g m))} (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H)
    (x : (point.{u, v} (Signed o g m)).V) : (point.{u, v} (Signed o g m)).IsQH ℋ x :=
  ⟨QH.point h hℋ x⟩

/-! ### Checks -/

/- A vertex with stabilizer `ℤ²` is not quadratically hanging, whatever the family `ℋ`. -/
example (ℋ : Set (Subgroup (Multiplicative (Fin 2 → ℤ))))
    (x : (point.{0, 0} (Multiplicative (Fin 2 → ℤ))).V) :
    ¬(point.{0, 0} (Multiplicative (Fin 2 → ℤ))).IsQH ℋ x :=
  not_isQH_of_isMulCommutative _

/- The pair of pants `S⁺(0, 3)`, relative to its three boundary subgroups, is a QH vertex of its
one-vertex tree, and each of its boundary components is used. -/
example (x : (point.{0, 0} (Signed true 0 3)).V) :
    (point.{0, 0} (Signed true 0 3)).IsQH
      (Set.range fun j => zpowers (Signed.peripheral true 0 3 j)) x :=
  isQH_point (by simp) (by rintro _ ⟨j, rfl⟩; exact Signed.isPeripheral_zpowers_peripheral j) x

example (x : (point.{0, 0} (Signed true 0 3)).V) (j : Fin 3) :
    (QH.point (ℋ := Set.range fun j => zpowers (Signed.peripheral true 0 3 j)) (by simp)
      (by rintro _ ⟨j, rfl⟩; exact Signed.isPeripheral_zpowers_peripheral j) x).IsUsed j :=
  QH.isUsed_point_of_mem _ _ _ ⟨j, rfl⟩

/- Relative to the empty family, no boundary component of the pair of pants is used. -/
example (x : (point.{0, 0} (Signed true 0 3)).V) (j : Fin 3) :
    ¬(QH.point (ℋ := ∅) (by simp) (by simp) x).IsUsed j := by
  simp [QH.isUsed_point_iff]

end GTree

end TauCeti
