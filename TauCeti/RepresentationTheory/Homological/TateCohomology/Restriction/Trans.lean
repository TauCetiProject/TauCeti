/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic
import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Naturality
import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Trans

/-!
# Tate restriction below degree `-1` along towers and isomorphisms

Below degree `-1`, restriction in Tate cohomology is the transfer in group homology, read through
Mathlib's comparison `TateCohomology.isoGroupHomology` (`TauCeti.TateCohomology.negSuccRes`). This
file transports the transitivity of the transfer and its compatibility with group isomorphisms
(`TauCeti.groupHomology.transfer_trans`, `TauCeti.groupHomology.map_comp_transfer_congrOfMapEq`)
to Tate cohomology.

## Main results

* `TauCeti.TateCohomology.negSuccRes_trans`: restriction is transitive along a tower of subgroups.
* `TauCeti.TateCohomology.map_comp_negSuccRes`: restriction commutes with the Tate map of a
  compatible pair along a group isomorphism.
-/

public section

universe u

open CategoryTheory Rep Representation

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep.{u} R G)

attribute [local instance] Subgroup.fintypeOfFinite

/-- **Tate restriction below degree `-1` is transitive along a tower of subgroups** `K ≤ H ≤ G`:
restricting from `G` to `H` and then from `H` to `K` is restriction from `G` to `K`, once
`K.subgroupOf H` is identified with `K` by the Tate map along `Subgroup.subgroupOfEquivOfLe hKH`. -/
@[reassoc]
theorem negSuccRes_trans {K H : Subgroup G} (hKH : K ≤ H) (n : ℕ) [NeZero n] :
    negSuccRes M H n ≫ negSuccRes (Rep.res H.subtype M) (K.subgroupOf H) n ≫
      map (e := Subgroup.subgroupOfEquivOfLe hKH) (φ := LinearMap.id)
        (Rep.isIntertwiningMap_res_res M (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH))
        (Int.negSucc n) = negSuccRes M K n := by
  -- Compare both sides in group homology, where restriction is the transfer.
  rw [← cancel_mono (negSuccIso (Rep.res K.subtype M) n).hom]
  simp only [Category.assoc, map_comp_negSuccIso_hom, negSuccRes_comp_negSuccIso_hom_assoc,
    negSuccRes_comp_negSuccIso_hom, TauCeti.groupHomology.transfer_trans]

/-- **Tate restriction below degree `-1` is compatible with a group isomorphism** `e : G ≃* G'`
carrying `S` onto `S'`: for a compatible pair `(e, φ)`, restricting to `S'` after transporting
along `(e, φ)` is transporting along the restricted pair after restricting to `S`. This is
`TauCeti.groupHomology.map_comp_transfer_congrOfMapEq` in Tate cohomology. -/
@[reassoc]
theorem map_comp_negSuccRes {G' : Type u} [Group G'] [Fintype G'] (e : G ≃* G') {N : Rep.{u} R G'}
    {φ : M.V →ₗ[R] N.V} (hφ : M.ρ.IsIntertwiningMap (N.ρ.comp (e : G →* G')) φ) {S : Subgroup G}
    {S' : Subgroup G'} (he : S.map (e : G →* G') = S') (n : ℕ) [NeZero n] :
    map hφ (Int.negSucc n) ≫ negSuccRes N S' n =
      negSuccRes M S n ≫ map (e := TauCeti.Subgroup.congrOfMapEq e he) (φ := φ)
        ⟨fun s v ↦ by simpa using hφ.isIntertwining (s : G) v⟩ (Int.negSucc n) := by
  -- Compare both sides in group homology, where restriction is the transfer.
  rw [← cancel_mono (negSuccIso (Rep.res S'.subtype N) n).hom]
  simp only [Category.assoc, map_comp_negSuccIso_hom, negSuccRes_comp_negSuccIso_hom_assoc,
    negSuccRes_comp_negSuccIso_hom, map_comp_negSuccIso_hom_assoc]
  -- What is left is the compatibility of the transfer with `(e, φ)`, up to the two presentations
  -- of the restricted coefficient map over `S`.
  exact _ ≫= (TauCeti.groupHomology.map_comp_transfer_congrOfMapEq e he hφ.toRes n).trans
    (_ ≫= groupHomology.map_congr rfl (by simp) n)

end TauCeti.TateCohomology
