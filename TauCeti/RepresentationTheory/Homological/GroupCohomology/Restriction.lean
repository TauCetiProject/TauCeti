/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# Transitivity of restriction in group cohomology

Restriction along a tower of subgroups `K ≤ H ≤ G` is transitive: restriction of `Hⁿ⁺¹(G, M)` to
`H` and then to `K.subgroupOf H` is restriction to `K`, once `K.subgroupOf H` is identified with `K`
by the change-of-group map along `Subgroup.subgroupOfEquivOfLe hKH`. This lets the cohomology of a
small subgroup be computed in stages through an intermediate subgroup; it is what makes Tate
restriction in positive degrees (`TauCeti.TateCohomology.posRes`) functorial along a tower of
layers of a class formation.

The change-of-group map is unavoidable, because `Rep.res` does not compose: for `K ≤ H ≤ G` the
composite `Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M)` and the single restriction
`Rep.res K.subtype M` are representations of groups with different carrier types
(`↥(K.subgroupOf H)` and `↥K`), so the two cannot even be compared as representations. The
comparison morphism between them is built from
`Subgroup.subtype_comp_subgroupOfEquivOfLe` and `Rep.isIntertwiningMap_res_res`.

## Main results

* `TauCeti.groupCohomology.map_subgroupOf_trans`: restriction along a tower of subgroups is
  transitive, in every degree `n` for `n : ℕ`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §5 for the composition law of the maps induced on cohomology by homomorphisms, and
  Chapter III, §9 for the dual transitivity of the transfer in group homology
  (`TauCeti.groupHomology.transfer_trans`).
* Formally: Mathlib's `groupCohomology.map` and its composition law `groupCohomology.map_comp`, of
  `Mathlib/RepresentationTheory/Homological/GroupCohomology/Functoriality.lean`, of which this is
  the case of two inclusions composed with a change of group; and Tau Ceti's
  `Rep.isIntertwiningMap_res_res`, of
  `TauCeti/RepresentationTheory/Rep/ChangeOfGroup.lean`, which is what makes the two restrictions
  of `M` agree along `Subgroup.subgroupOfEquivOfLe`.
-/

public noncomputable section

universe u

open CategoryTheory Rep Representation

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {R G : Type u} [CommRing R] [Group G] (M : Rep.{u} R G)

/-- **Restriction along a tower of subgroups is transitive**: for `K ≤ H ≤ G` and `n : ℕ`, the map
`Hⁿ(G, M) ⟶ Hⁿ(H, Res_H M)` along `H.subtype` followed by the map along
`(K.subgroupOf H).subtype` and then the change-of-group map along
`Subgroup.subgroupOfEquivOfLe hKH` is restriction `Hⁿ(G, M) ⟶ Hⁿ(K, Res_K M)` along
`K.subtype`. Here `K.subgroupOf H`, which is `K` viewed as a subgroup of `H`, is identified with
`K` by `Subgroup.subgroupOfEquivOfLe hKH`, under which the two restrictions of `M` agree
(`Rep.isIntertwiningMap_res_res`). -/
@[reassoc]
theorem map_subgroupOf_trans {K H : Subgroup G} (hKH : K ≤ H) (n : ℕ) :
    map H.subtype (𝟙 (Rep.res H.subtype M)) n ≫
      map (K.subgroupOf H).subtype
        (𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) n ≫
      map (A := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
        (B := Rep.res K.subtype M) ((Subgroup.subgroupOfEquivOfLe hKH).symm)
        (Rep.isIntertwiningMap_res_res M
          (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes n =
    map K.subtype (𝟙 (Rep.res K.subtype M)) n := by
  have h₁ := map_comp (A := M) (B := Rep.res H.subtype M)
      (C := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
      (f := H.subtype) (g := (K.subgroupOf H).subtype)
      (φ := 𝟙 (Rep.res H.subtype M))
      (ψ := 𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) n
  have h₃ := map_comp (A := M)
      (B := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M)) (C := Rep.res K.subtype M)
      (f := H.subtype.comp (K.subgroupOf H).subtype)
      (g := (Subgroup.subgroupOfEquivOfLe hKH).symm)
      (φ := (Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M)))
      (ψ := (Rep.isIntertwiningMap_res_res M
        (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes) n
  rw [← Category.assoc, h₁.symm]
  have h₁' :
      map (H.subtype.comp (K.subgroupOf H).subtype)
          ((Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M))) n =
        map (H.subtype.comp (K.subgroupOf H).subtype)
          ((Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M)) ≫
            𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) n :=
    map_congr rfl (by ext x; simp) n
  rw [h₁'.symm, h₃.symm]
  have hg : (H.subtype.comp (K.subgroupOf H).subtype).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm = K.subtype := by
    rw [← Subgroup.subtype_comp_subgroupOfEquivOfLe hKH]
    ext x
    simp
  exact map_congr hg (by ext x; simp) n

end TauCeti.groupCohomology
