/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.SurfaceGroup.Signed
import TauCeti.Algebra.Group.Subgroup.Map

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
* `TauCeti.GTree.QH.smul` and `TauCeti.GTree.QH.ofSubset`: the QH structure at a translate of `v`,
  and relative to a smaller family.
* `TauCeti.GTree.QH.ofSubsingleton`: the QH structure at the vertex of a one-vertex tree of a
  surface group, relative to a family of peripheral subgroups.

## Main results

* `TauCeti.GTree.IsQH.ne_top_of_mem_incidentSubgroups`: incident subgroups are proper subgroups of
  the stabilizer of a QH vertex; hence a QH vertex is the only vertex fixed by its stabilizer
  (`TauCeti.GTree.IsQH.eq_of_stabilizer_le`).
* `TauCeti.GTree.isQH_smul_iff`: being QH is invariant under the action of `G`.
* `TauCeti.GTree.not_isQH_of_isMulCommutative`: a vertex with abelian stabilizer is not QH.
* `TauCeti.GTree.QH.eq_bot_or_exists_le_map_conj_boundarySubgroup` and
  `TauCeti.GTree.QH.isUsed_iff_exists_le_map_conj_boundarySubgroup`: the peripheral condition and
  the used boundary components, read in `G`; a boundary component whose boundary subgroup
  belongs to `ℋ` is used (`TauCeti.GTree.QH.isUsed_of_boundarySubgroup_mem`).
* `TauCeti.GTree.isQH_of_subsingleton`: the vertex of a one-vertex tree of `S±(g, m)`, relative
  to a family of peripheral subgroups such as the boundary subgroups, is QH; a boundary component
  is used exactly when the family contains a nontrivial subgroup of a conjugate of its boundary
  subgroup (`TauCeti.GTree.QH.isUsed_ofSubsingleton_iff`).

## Implementation notes

The surface is recorded by its orientability, its genus and its number of boundary components,
a nonorientable surface having positive genus. By the classification of compact surfaces these
determine the surface, and `S±(g, m)`, with the conjugates of the cyclic subgroups `⟨pⱼ⟩`, is its
fundamental group with its boundary subgroups.

## TODO

Record a polygonal model of the surface (`TauCeti.SurfaceModel`) together with an isomorphism of
its fundamental group with `S±(g, m)` carrying its boundary components to the conjugacy classes
of the `pⱼ`: curves on the surface, and the splittings dual to them, are defined on the model.

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
  /-- Whether the surface is orientable. -/
  orientable : Bool
  /-- The genus of the surface: its number of handles, or of cross-caps when it is
  nonorientable. -/
  genus : ℕ
  /-- The number of boundary components of the surface. -/
  boundary : ℕ
  /-- A nonorientable surface has at least one cross-cap. -/
  orientable_or_genus_pos : orientable = true ∨ 0 < genus
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

variable {T} in
theorem isQH_iff {ℋ : Set (Subgroup G)} {v : T.V} : T.IsQH ℋ v ↔ Nonempty (T.QH ℋ v) := Iff.rfl

namespace QH

variable {T} {ℋ : Set (Subgroup G)} {v : T.V} (q : T.QH ℋ v)

include q in
/-- A vertex carrying a QH structure is QH. -/
theorem isQH : T.IsQH ℋ v := isQH_iff.mpr ⟨q⟩

/-! ### Boundary subgroups and used boundary components -/

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

/-- The boundary subgroup `⟨pⱼ⟩`, in `G`, is generated by the element corresponding to `pⱼ`. -/
theorem boundarySubgroup_eq_zpowers (j : Fin q.boundary) :
    q.boundarySubgroup j =
      zpowers (q.surfaceEquiv.symm (Signed.peripheral q.orientable q.genus q.boundary j) : G) := by
  simp [boundarySubgroup, comap_equiv_eq_map_symm, MonoidHom.map_zpowers]

/-- The surface isomorphism carries the boundary subgroup to `⟨pⱼ⟩`. -/
@[simp]
theorem map_surfaceEquiv_boundarySubgroup (j : Fin q.boundary) :
    ((q.boundarySubgroup j).subgroupOf (stabilizer G v)).map
        (q.surfaceEquiv : stabilizer G v →* Signed q.orientable q.genus q.boundary) =
      zpowers (Signed.peripheral q.orientable q.genus q.boundary j) := by
  rw [boundarySubgroup, MulEquiv.toMonoidHom_eq_coe, subgroupOf,
    comap_map_eq_self_of_injective (subtype_injective _),
    map_comap_eq_self_of_surjective q.surfaceEquiv.surjective]

/-- The boundary subgroups of a QH vertex are nontrivial. -/
theorem boundarySubgroup_ne_bot (j : Fin q.boundary) : q.boundarySubgroup j ≠ ⊥ := by
  rw [boundarySubgroup_eq_zpowers, Ne, zpowers_eq_bot]
  simpa using Signed.peripheral_ne_one_of_eulerChar_neg q.eulerChar_neg j

/-- Containment in a conjugate of `⟨pⱼ⟩`, read in `G`: an incident subgroup is carried into the
conjugate of `⟨pⱼ⟩` by `s` exactly when it lies in the conjugate of the boundary subgroup by the
element corresponding to `s`. -/
theorem map_surfaceEquiv_le_map_conj_iff {K : Subgroup (stabilizer G v)} {j : Fin q.boundary}
    {s : Signed q.orientable q.genus q.boundary} :
    K.map q.surfaceEquiv.toMonoidHom ≤
        (zpowers (Signed.peripheral q.orientable q.genus q.boundary j)).map
          (MulAut.conj s).toMonoidHom ↔
      K.map (stabilizer G v).subtype ≤
        (q.boundarySubgroup j).map (MulAut.conj (q.surfaceEquiv.symm s : G)).toMonoidHom := by
  have h := map_map_conj ((zpowers (Signed.peripheral q.orientable q.genus q.boundary j)).comap
    q.surfaceEquiv.toMonoidHom) q.surfaceEquiv.toMonoidHom (q.surfaceEquiv.symm s)
  rw [map_comap_eq_self_of_surjective q.surfaceEquiv.surjective, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] at h
  rw [← h, map_le_map_iff_of_injective q.surfaceEquiv.injective, boundarySubgroup,
    ← map_le_map_iff_of_injective (subtype_injective (stabilizer G v)), map_map_conj, coe_subtype]

/-- Every incident subgroup is trivial or lies, in `G`, in a conjugate of a boundary subgroup by
an element of the vertex stabilizer. -/
theorem eq_bot_or_exists_le_map_conj_boundarySubgroup {K : Subgroup (stabilizer G v)}
    (hK : K ∈ T.incidentSubgroups ℋ v) :
    K = ⊥ ∨ ∃ j, ∃ s ∈ stabilizer G v,
      K.map (stabilizer G v).subtype ≤ (q.boundarySubgroup j).map (MulAut.conj s).toMonoidHom := by
  rcases Signed.isPeripheral_iff.mp (q.isPeripheral_map K hK) with h | ⟨j, s, h⟩
  · exact .inl ((map_eq_bot_iff_of_injective _ q.surfaceEquiv.injective).mp h)
  · exact .inr ⟨j, _, (q.surfaceEquiv.symm s).2, q.map_surfaceEquiv_le_map_conj_iff.mp h⟩

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

/-- A boundary component is used exactly when some nontrivial incident subgroup lies, in `G`, in a
conjugate of its boundary subgroup by an element of the vertex stabilizer. -/
theorem isUsed_iff_exists_le_map_conj_boundarySubgroup {j : Fin q.boundary} :
    q.IsUsed j ↔ ∃ K ∈ T.incidentSubgroups ℋ v, K ≠ ⊥ ∧ ∃ s ∈ stabilizer G v,
      K.map (stabilizer G v).subtype ≤ (q.boundarySubgroup j).map (MulAut.conj s).toMonoidHom := by
  rw [isUsed_iff]
  refine exists_congr fun K => and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact ⟨_, (q.surfaceEquiv.symm s).2, q.map_surfaceEquiv_le_map_conj_iff.mp hs⟩
  · rintro ⟨s, hs, hle⟩
    refine ⟨q.surfaceEquiv ⟨s, hs⟩, q.map_surfaceEquiv_le_map_conj_iff.mpr ?_⟩
    rwa [MulEquiv.symm_apply_apply]

/-- A boundary component whose boundary subgroup belongs to `ℋ` is used. -/
theorem isUsed_of_boundarySubgroup_mem {j : Fin q.boundary} (hj : q.boundarySubgroup j ∈ ℋ) :
    q.IsUsed j := by
  refine ⟨_, T.subgroupOf_mem_incidentSubgroups hj v, fun h => q.boundarySubgroup_ne_bot j ?_, 1,
    by simp⟩
  rwa [subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot (q.boundarySubgroup_le_stabilizer j)] at h

/-! ### Translates and smaller families -/

/-- The QH structure at `g • v` obtained by translating a QH structure at `v` by `g`. -/
@[expose, simps]
def smul (g : G) : T.QH ℋ (g • v) where
  orientable := q.orientable
  genus := q.genus
  boundary := q.boundary
  orientable_or_genus_pos := q.orientable_or_genus_pos
  eulerChar_neg := q.eulerChar_neg
  surfaceEquiv := (stabilizerEquivStabilizer (rfl : g • v = g • v)).symm.trans q.surfaceEquiv
  isPeripheral_map := by
    rw [incidentSubgroups_smul]
    rintro _ ⟨K, hK, rfl⟩
    rw [map_map]
    convert q.isPeripheral_map K hK using 3
    ext
    simp

/-- The boundary subgroups at `g • v` are the conjugates by `g` of those at `v`. -/
@[simp]
theorem boundarySubgroup_smul (g : G) (j : Fin q.boundary) :
    (q.smul g).boundarySubgroup j = (q.boundarySubgroup j).map (MulAut.conj g).toMonoidHom := by
  rw [boundarySubgroup_eq_zpowers (q.smul g) j, boundarySubgroup_eq_zpowers, MonoidHom.map_zpowers]
  -- The surface isomorphism at `g • v` is conjugation by `g⁻¹` followed by that at `v`.
  exact congrArg zpowers (stabilizerEquivStabilizer_apply rfl _)

/-- A QH structure relative to `ℋ` is a QH structure relative to every smaller family. -/
@[expose, simps]
def ofSubset {ℋ' : Set (Subgroup G)} (h : ℋ' ⊆ ℋ) : T.QH ℋ' v where
  __ := q
  isPeripheral_map K hK := q.isPeripheral_map K (T.incidentSubgroups_mono h v hK)

end QH

/-! ### Consequences for the vertex stabilizer -/

namespace IsQH

variable {T} {ℋ : Set (Subgroup G)} {v : T.V}

/-- Incident subgroups are proper subgroups of the stabilizer of a QH vertex. -/
theorem ne_top_of_mem_incidentSubgroups (hv : T.IsQH ℋ v) {K : Subgroup (stabilizer G v)}
    (hK : K ∈ T.incidentSubgroups ℋ v) : K ≠ ⊤ := by
  obtain ⟨q⟩ := isQH_iff.mp hv
  rintro rfl
  have := q.isPeripheral_map ⊤ hK
  rw [map_top_of_surjective _ q.surfaceEquiv.surjective] at this
  exact Signed.not_isPeripheral_top q.eulerChar_neg this

/-- Incident subgroups at a QH vertex are abelian. -/
theorem isMulCommutative_of_mem_incidentSubgroups (hv : T.IsQH ℋ v)
    {K : Subgroup (stabilizer G v)} (hK : K ∈ T.incidentSubgroups ℋ v) : IsMulCommutative K := by
  obtain ⟨q⟩ := isQH_iff.mp hv
  have := (q.isPeripheral_map K hK).isMulCommutative
  exact (K.equivMapOfInjective q.surfaceEquiv.toMonoidHom
    q.surfaceEquiv.injective).symm.surjective.isMulCommutative

/-- A QH vertex is the only vertex fixed by its stabilizer. -/
theorem eq_of_stabilizer_le (hv : T.IsQH ℋ v) {w : T.V} (h : stabilizer G v ≤ stabilizer G w) :
    w = v := by
  by_contra hwv
  obtain ⟨e, he, hle⟩ := exists_src_eq_and_stabilizer_inf_le (Ne.symm hwv)
  exact hv.ne_top_of_mem_incidentSubgroups (T.stabilizer_subgroupOf_mem_incidentSubgroups ℋ he)
    (subgroupOf_eq_top.mpr ((le_inf le_rfl h).trans hle))

/-- A QH vertex relative to `ℋ` is QH relative to every smaller family. -/
theorem mono (hv : T.IsQH ℋ v) {ℋ' : Set (Subgroup G)} (h : ℋ' ⊆ ℋ) : T.IsQH ℋ' v :=
  ((isQH_iff.mp hv).some.ofSubset h).isQH

end IsQH

/-- Being quadratically hanging is invariant under the action of `G`. -/
@[simp]
theorem isQH_smul_iff {ℋ : Set (Subgroup G)} {g : G} {v : T.V} :
    T.IsQH ℋ (g • v) ↔ T.IsQH ℋ v := by
  refine ⟨fun hv => ?_, fun hv => ((isQH_iff.mp hv).some.smul g).isQH⟩
  simpa using ((isQH_iff.mp hv).some.smul g⁻¹).isQH

/-- A vertex with abelian stabilizer is not quadratically hanging. -/
theorem not_isQH_of_isMulCommutative {ℋ : Set (Subgroup G)} {v : T.V}
    [IsMulCommutative (stabilizer G v)] : ¬T.IsQH ℋ v := fun hv =>
  let ⟨q⟩ := isQH_iff.mp hv
  Signed.not_isMulCommutative_of_eulerChar_neg q.eulerChar_neg
    q.surfaceEquiv.surjective.isMulCommutative

/-- A vertex whose stabilizer is contained in a conjugate of a member of `ℋ` is not quadratically
hanging. -/
theorem not_isQH_of_stabilizer_le {ℋ : Set (Subgroup G)} {v : T.V} {H : Subgroup G} (hH : H ∈ ℋ)
    (g : G) (h : stabilizer G v ≤ H.map (MulAut.conj g).toMonoidHom) : ¬T.IsQH ℋ v := fun hv =>
  hv.ne_top_of_mem_incidentSubgroups (T.map_subgroupOf_mem_incidentSubgroups hH g v)
    (subgroupOf_eq_top.mpr h)

/-! ### One-vertex trees of surface groups -/

section Subsingleton

variable {o : Bool} {g m : ℕ} {T : GTree.{u, v} (Signed o g m)} [Subsingleton T.V]
  {ℋ : Set (Subgroup (Signed o g m))}

namespace QH

/-- The quadratically hanging structure at the vertex of a one-vertex tree of the fundamental
group `S±(g, m)` of a compact surface of negative Euler characteristic, relative to a family of
peripheral subgroups: the stabilizer is the whole group, identified with `S±(g, m)` by the
inclusion. -/
@[expose]
def ofSubsingleton (ho : o = true ∨ 0 < g) (h : Signed.eulerChar o g m < 0)
    (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H) (x : T.V) : T.QH ℋ x where
  orientable := o
  genus := g
  boundary := m
  orientable_or_genus_pos := ho
  eulerChar_neg := h
  surfaceEquiv :=
    (MulEquiv.subgroupCongr (stabilizer_eq_top_of_subsingleton x)).trans Subgroup.topEquiv
  isPeripheral_map := by
    -- The surface isomorphism is the inclusion of the stabilizer, which is the whole group.
    have hφ : ((MulEquiv.subgroupCongr (stabilizer_eq_top_of_subsingleton x)).trans
        Subgroup.topEquiv).toMonoidHom = (stabilizer _ x).subtype := by
      ext
      simp
    rw [incidentSubgroups_of_subsingleton]
    rintro K ⟨H, hH, s, rfl⟩
    rw [hφ, subgroupOf_map_subtype, stabilizer_eq_top_of_subsingleton, inf_top_eq]
    exact (hℋ H hH).map_conj s

variable (ho : o = true ∨ 0 < g) (h : Signed.eulerChar o g m < 0)
  (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H) (x : T.V)

@[simp] theorem ofSubsingleton_orientable : (ofSubsingleton ho h hℋ x).orientable = o := (rfl)

@[simp] theorem ofSubsingleton_genus : (ofSubsingleton ho h hℋ x).genus = g := (rfl)

@[simp] theorem ofSubsingleton_boundary : (ofSubsingleton ho h hℋ x).boundary = m := (rfl)

/-- The surface isomorphism at the vertex of a one-vertex tree is the inclusion of the
stabilizer. -/
@[simp]
theorem ofSubsingleton_surfaceEquiv_apply (y : stabilizer (Signed o g m) x) :
    ((ofSubsingleton ho h hℋ x).surfaceEquiv y : Signed o g m) = (y : Signed o g m) := (rfl)

@[simp]
theorem ofSubsingleton_surfaceEquiv_symm_apply (y : Signed o g m) :
    (((ofSubsingleton ho h hℋ x).surfaceEquiv.symm y : stabilizer (Signed o g m) x) :
      Signed o g m) = y := (rfl)

theorem ofSubsingleton_surfaceEquiv_toMonoidHom :
    (ofSubsingleton ho h hℋ x).surfaceEquiv.toMonoidHom = (stabilizer _ x).subtype :=
  MonoidHom.ext (ofSubsingleton_surfaceEquiv_apply ho h hℋ x)

/-- The boundary subgroups of a one-vertex tree of a surface group are the cyclic subgroups
generated by the peripheral elements. -/
@[simp]
theorem boundarySubgroup_ofSubsingleton (j : Fin m) :
    (ofSubsingleton ho h hℋ x).boundarySubgroup j = zpowers (Signed.peripheral o g m j) :=
  (boundarySubgroup_eq_zpowers (ofSubsingleton ho h hℋ x) j).trans
    (congrArg zpowers
      (ofSubsingleton_surfaceEquiv_symm_apply ho h hℋ x (Signed.peripheral o g m j)))

/-- At the vertex of a one-vertex tree of a surface group, a boundary component is used exactly
when the family `ℋ` contains a nontrivial subgroup of a conjugate of its boundary subgroup. -/
theorem isUsed_ofSubsingleton_iff {j : Fin m} :
    (ofSubsingleton ho h hℋ x).IsUsed j ↔ ∃ H ∈ ℋ, H ≠ ⊥ ∧ ∃ s : Signed o g m,
      H ≤ (zpowers (Signed.peripheral o g m j)).map (MulAut.conj s).toMonoidHom := by
  -- The stabilizer is the whole group, so `L ∩ Q = L` for every subgroup `L`.
  have hQ (L : Subgroup (Signed o g m)) : (L.subgroupOf (stabilizer _ x)).map
      (stabilizer _ x).subtype = L := by
    rw [subgroupOf_map_subtype, stabilizer_eq_top_of_subsingleton, inf_top_eq]
  have h1 (L : Subgroup (Signed o g m)) :
      L.map (MulAut.conj (1 : Signed o g m)).toMonoidHom = L := by
    simp [MulAut.one_def]
  refine (isUsed_iff_exists_le_map_conj_boundarySubgroup _).trans ?_
  rw [boundarySubgroup_ofSubsingleton ho h hℋ x j, incidentSubgroups_of_subsingleton]
  constructor
  · rintro ⟨K, ⟨H, hH, t, rfl⟩, hK, s, -, hs⟩
    rw [hQ] at hs
    refine ⟨H, hH, fun hH0 => hK (by simp [hH0]), t⁻¹ * s, ?_⟩
    have := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hs
    rwa [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, h1] at this
  · rintro ⟨H, hH, hH0, s, hs⟩
    refine ⟨_, ⟨H, hH, 1, rfl⟩, fun hK => hH0 ?_, s, by simp, by rwa [hQ, h1]⟩
    rw [← h1 H, ← hQ (H.map _), hK, Subgroup.map_bot]

end QH

/-- The vertex of a one-vertex tree of the fundamental group of a compact surface of negative
Euler characteristic is quadratically hanging relative to every family of peripheral subgroups,
in particular relative to the boundary subgroups. -/
theorem isQH_of_subsingleton (ho : o = true ∨ 0 < g) (h : Signed.eulerChar o g m < 0)
    (hℋ : ∀ H ∈ ℋ, Signed.IsPeripheral H) (x : T.V) : T.IsQH ℋ x :=
  (QH.ofSubsingleton ho h hℋ x).isQH

end Subsingleton

/-! ### Checks -/

/- A vertex with stabilizer `ℤ²` is not quadratically hanging, whatever the family `ℋ`. -/
example (ℋ : Set (Subgroup (Multiplicative (Fin 2 → ℤ))))
    (x : (point.{0, 0} (Multiplicative (Fin 2 → ℤ))).V) :
    ¬(point.{0, 0} (Multiplicative (Fin 2 → ℤ))).IsQH ℋ x :=
  not_isQH_of_isMulCommutative _

/- No QH structure records a nonorientable surface of genus `0`: the tuple `(false, 0, 3)` that
would describe a pair of pants as nonorientable is rejected. -/
example {T : GTree.{u, v} G} {ℋ : Set (Subgroup G)} {v : T.V} (q : T.QH ℋ v) :
    ¬(q.orientable = false ∧ q.genus = 0) := by
  rintro ⟨ho, hg⟩
  simpa [ho, hg] using q.orientable_or_genus_pos

/- The pair of pants `S⁺(0, 3)`, relative to its three boundary subgroups, is a QH vertex of its
one-vertex tree, and each of its boundary components is used. -/
example (x : (point.{0, 0} (Signed true 0 3)).V) :
    (point.{0, 0} (Signed true 0 3)).IsQH
      (Set.range fun j => zpowers (Signed.peripheral true 0 3 j)) x :=
  isQH_of_subsingleton (.inl rfl) (by simp [Orientable.eulerChar_def])
    (by rintro _ ⟨j, rfl⟩; exact Signed.isPeripheral_zpowers_peripheral j) x

example (x : (point.{0, 0} (Signed true 0 3)).V) (j : Fin 3) :
    (QH.ofSubsingleton (ℋ := Set.range fun j => zpowers (Signed.peripheral true 0 3 j)) (.inl rfl)
      (by simp [Orientable.eulerChar_def])
      (by rintro _ ⟨j, rfl⟩; exact Signed.isPeripheral_zpowers_peripheral j) x).IsUsed j :=
  QH.isUsed_of_boundarySubgroup_mem _ (by simp)

/- Relative to the empty family, no boundary component of the pair of pants is used. -/
example (x : (point.{0, 0} (Signed true 0 3)).V) (j : Fin 3) :
    ¬(QH.ofSubsingleton (ℋ := ∅) (.inl rfl) (by simp [Orientable.eulerChar_def]) (by simp)
      x).IsUsed j := by
  simp [QH.isUsed_ofSubsingleton_iff]

end GTree

end TauCeti
