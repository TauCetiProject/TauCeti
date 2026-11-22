/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.DoubleCoset
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.FreeProduct
import TauCeti.GroupTheory.GTree.QuotientGraphOfGroups
import TauCeti.GroupTheory.GTree.Restrict

/-!
# The Kurosh subgroup theorem

Let `U` be a subgroup of a free product `G = ∗ᵢ Gᵢ` of groups. **Kurosh's subgroup theorem** says
that `U` is the free product of a free group and of subgroups `U ∩ g Gᵢ g⁻¹`, one for each double
coset `U g Gᵢ` for which this intersection is nontrivial.

The proof restricts the action of `G` on the Bass–Serre tree of the free product
(`GraphOfGroups.exists_gTree_coprodI`) to `U`. Dart stabilizers stay trivial, so `U` is the free
product of a free group and of the stabilizers in `U` of one vertex from each `U`-orbit of
vertices with nontrivial stabilizer (`GTree.exists_bijective_coprod_lift_stabilizer`). A vertex
with nontrivial stabilizer in `G` is a translate `g • t i` of the vertex `t i` fixed by `Gᵢ`, with
stabilizer `g Gᵢ g⁻¹`, and two such translates `g • t i` and `g' • t i'` lie in one `U`-orbit
exactly when `i = i'` and `g'` lies in the double coset `U g Gᵢ`.

## Main results

* `Subgroup.exists_bijective_coprod_lift_subgroupOf_conj`: the Kurosh subgroup theorem.

## References

* A. G. Kurosch, *Die Untergruppen der freien Produkte von beliebigen Gruppen*, Math. Ann. 109
  (1934), 647–660.
* J.-P. Serre, *Trees*, Chapter I, §5.5, Theorem 14.
-/

public section

open Monoid _root_.MulAction TauCeti

universe u w

namespace Subgroup

variable {ι : Type u} {M : ι → Type w} [∀ i, Group (M i)]

/-- Two families of subgroups that agree pointwise give the same homomorphism out of the free
product of their members. -/
private theorem bijective_lift_subtype_of_eq {H : Type*} [Group H] {J : Type*}
    {S S' : J → Subgroup H} (h : ∀ j, S j = S' j) {X : Type*} {f : FreeGroup X →* H}
    (hb : Function.Bijective (Coprod.lift (CoprodI.lift fun j => (S j).subtype) f)) :
    Function.Bijective (Coprod.lift (CoprodI.lift fun j => (S' j).subtype) f) := by
  obtain rfl := funext h
  exact hb

/-- **The Kurosh subgroup theorem.** Every subgroup `U` of a free product `∗ᵢ Mᵢ` is the internal
free product of a free subgroup, the image of an injective `f : FreeGroup X →* U`, and of the
subgroups `U ∩ gⱼ M_{iⱼ} gⱼ⁻¹`, where `M_{iⱼ}` is the range of `Monoid.CoprodI.of`. These
intersections are nontrivial, and `j ↦ (iⱼ, U gⱼ M_{iⱼ})` is a bijection onto the pairs of an index
`i` and a double coset `U g Mᵢ` for which `U ∩ g Mᵢ g⁻¹` is nontrivial. -/
theorem exists_bijective_coprod_lift_subgroupOf_conj (U : Subgroup (CoprodI M)) :
    ∃ (J : Type (max u w)) (i : J → ι) (g : J → CoprodI M) (X : Type (max u w))
      (f : FreeGroup X →* U),
      Function.Bijective (Coprod.lift (CoprodI.lift fun j =>
        (((CoprodI.of (M := M) (i := i j)).range.map
          (MulAut.conj (g j)).toMonoidHom).subgroupOf U).subtype) f) ∧
      (∀ j, ((CoprodI.of (M := M) (i := i j)).range.map
          (MulAut.conj (g j)).toMonoidHom).subgroupOf U ≠ ⊥) ∧
      (∀ j j', i j = i j' →
        g j' ∈ DoubleCoset.doubleCoset (g j) U (CoprodI.of (M := M) (i := i j)).range → j = j') ∧
      (∀ (i' : ι) (g' : CoprodI M), ((CoprodI.of (M := M) (i := i')).range.map
          (MulAut.conj g').toMonoidHom).subgroupOf U ≠ ⊥ →
        ∃ j, i j = i' ∧
          g' ∈ DoubleCoset.doubleCoset (g j) U (CoprodI.of (M := M) (i := i')).range) := by
  obtain ⟨T, t, hE, ht, hV, hinj⟩ := GraphOfGroups.exists_gTree_coprodI M
  -- Restrict the action on the tree of the free product to `U`.
  let T' := T.comap U.subtype
  have hstab (y : T.V) : stabilizer U (y : T'.V) = (stabilizer (CoprodI M) y).subgroupOf U :=
    (GTree.stabilizer_comap_vertex T U.subtype y).trans (comap_subtype _ _)
  have hE' (e : T'.E) : stabilizer U e = ⊥ := by
    rw [GTree.stabilizer_comap_dart, hE, MonoidHom.comap_bot, U.ker_subtype]
  obtain ⟨J, x, X, f, hbij, hne, hdist, hcov⟩ := T'.exists_bijective_coprod_lift_stabilizer hE'
  have hconj (i : ι) (g : CoprodI M) : stabilizer (CoprodI M) (g • t i) =
      (CoprodI.of (M := M) (i := i)).range.map (MulAut.conj g).toMonoidHom := by
    rw [stabilizer_smul_eq_stabilizer_map_conj, ht]
  -- Each representative vertex has nontrivial stabilizer, so it is a translate of some `t i`.
  have hx (j : J) : ∃ (i : ι) (g : CoprodI M), g • t i = x j :=
    (hV (x j)).resolve_left fun h => hne j ((hstab (x j)).trans (by rw [h, bot_subgroupOf]))
  choose i g hg using hx
  have hK (j : J) : stabilizer U (x j) = ((CoprodI.of (M := M) (i := i j)).range.map
      (MulAut.conj (g j)).toMonoidHom).subgroupOf U :=
    (hstab (x j)).trans (by rw [← hg j, hconj])
  refine ⟨J, i, g, X, f, bijective_lift_subtype_of_eq hK hbij,
    fun j => ne_of_eq_of_ne (hK j).symm (hne j), ?_, ?_⟩
  · -- Translates of `t i` by elements of one double coset `U g Mᵢ` lie in one `U`-orbit.
    intro j j' hii hmem
    obtain ⟨u, hu, h, hh, hgj⟩ := DoubleCoset.mem_doubleCoset.1 hmem
    have hh' : h • t (i j) = t (i j) := by
      rw [← mem_stabilizer_iff, ht]
      exact hh
    refine hdist j j' ⟨u, hu⟩ ((GTree.comap_smul_vertex T U.subtype _ _).trans ?_)
    rw [← hg j', ← hii, hgj, coe_subtype, ← hg j, mul_smul, mul_smul, hh']
  · -- A vertex `g' • t i'` with nontrivial stabilizer in `U` is in the `U`-orbit of some `x j`.
    intro i' g' hne'
    obtain ⟨j, ⟨u, hu⟩, huj⟩ :=
      hcov _ (ne_of_eq_of_ne ((hstab (g' • t i')).trans (by rw [hconj])) hne')
    have huj' : (u * g j) • t (i j) = g' • t i' := by
      rw [mul_smul, hg j]
      exact (GTree.comap_smul_vertex T U.subtype _ _).symm.trans huj
    obtain rfl : i j = i' :=
      hinj (i j) i' (g'⁻¹ * (u * g j)) (by rw [mul_smul, huj', inv_smul_smul])
    refine ⟨j, rfl, DoubleCoset.mem_doubleCoset.2 ⟨u, hu, (u * g j)⁻¹ * g', ?_, by group⟩⟩
    rw [← ht, SetLike.mem_coe, mem_stabilizer_iff, mul_smul, ← huj', inv_smul_smul]

end Subgroup
