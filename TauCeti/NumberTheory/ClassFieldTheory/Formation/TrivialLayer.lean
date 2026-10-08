/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap

/-!
# Trivial layers and class formations

For a finite normal layer `V ◁ U` with equal top and ground subgroups, the relative subgroup is
all of `U`, so its Galois group `U / V` is trivial and its degree is one. The norm is therefore the
identity after identifying the two levels. In particular, its image is the whole ground level and
the norm quotient is trivial.

For a class formation, Artin reciprocity identifies this norm quotient with the additive
abelianization of the Galois group. Consequently the Artin map of the layer is the unique additive
homomorphism into a trivial group. This gives the trivial-layer direction check without comparing
cardinalities.

If the ambient profinite group itself is a subsingleton, every layer is trivial. In that case every
positive-degree cohomology group of a layer vanishes, so every formation has a canonical class
formation whose invariant maps are zero. This is the class formation used at a complex place.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.subsingleton_gal_of_top_eq_ground`: the Galois group of a
  trivial layer is a subsingleton.
* `TauCeti.ClassFieldTheory.NormalLayer.top_eq_ground_of_subsingleton`: every layer over a
  subsingleton group is trivial.
* `TauCeti.ClassFieldTheory.ClassFormation.ofSubsingleton`: the canonical class formation over a
  subsingleton profinite group.
* `TauCeti.ClassFieldTheory.NormalLayer.normSubgroup_eq_top_of_top_eq_ground`: the norm subgroup
  of a trivial layer is the whole ground level.
* `TauCeti.ClassFieldTheory.NormalLayer.subsingleton_normQuotient_of_top_eq_ground`: the norm
  quotient of a trivial layer is a subsingleton.
* `TauCeti.ClassFieldTheory.ClassFormation.artinMap_trivialLayer`: the Artin map of a trivial
  layer is zero.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§5–6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

variable (L : NormalLayer G)

/-- Every layer over a subsingleton group is trivial. -/
theorem top_eq_ground_of_subsingleton [Subsingleton G] : L.top = L.ground := by
  apply le_antisymm L.top_le_ground
  intro g _
  rw [Subsingleton.elim g 1]
  exact one_mem L.top

/-- The Galois group of a layer whose top and ground subgroups agree is trivial. -/
theorem subsingleton_gal_of_top_eq_ground (hL : L.top = L.ground) : Subsingleton L.Gal := by
  rw [QuotientGroup.subsingleton_iff]
  ext x
  simp only [relativeTop, Subgroup.mem_top, iff_true]
  simp [hL]

/-- A layer whose top and ground subgroups agree has degree one. -/
theorem degree_eq_one_of_top_eq_ground (hL : L.top = L.ground) : L.degree = 1 := by
  rw [degree_eq_relIndex, Subgroup.relIndex_eq_one]
  simp [hL]

variable (F : Formation G)

/-- The norm of a trivial layer is the identity after reading both levels in the ambient
representation. -/
theorem norm_apply_coe_of_top_eq_ground (hL : L.top = L.ground) (x : F.level L.top) :
    (L.norm F x : F.toRep.V) = x := by
  rw [L.norm_apply_coe_of_mem_level_ground F x, L.degree_eq_one_of_top_eq_ground hL]
  · simp
  · simpa [hL] using x.2

/-- The norm of a layer whose top and ground subgroups agree is surjective. -/
theorem norm_surjective_of_top_eq_ground (hL : L.top = L.ground) :
    Function.Surjective (L.norm F) := by
  intro y
  let x : F.level L.top := ⟨y, by simp [hL]⟩
  refine ⟨x, Subtype.ext ?_⟩
  exact L.norm_apply_coe_of_top_eq_ground F hL x

/-- The norm subgroup of a trivial layer is the whole ground level. -/
@[simp]
theorem normSubgroup_eq_top_of_top_eq_ground (hL : L.top = L.ground) :
    L.normSubgroup F = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro y
  rw [L.mem_normSubgroup]
  exact L.norm_surjective_of_top_eq_ground F hL y

/-- The norm quotient of a trivial layer is a subsingleton. -/
theorem subsingleton_normQuotient_of_top_eq_ground (hL : L.top = L.ground) :
    Subsingleton (L.NormQuotient F) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact L.normSubgroup_eq_top_of_top_eq_ground F hL

end NormalLayer

namespace ClassFormation

variable {F : Formation G}

/-- The canonical class formation on a formation over a subsingleton profinite group. Every layer
is trivial, its positive-degree cohomology vanishes, and its invariant map is consequently zero. -/
def ofSubsingleton (F : Formation G) [Subsingleton G] : ClassFormation F where
  subsingleton_h1 L := by
    let _ : Subsingleton L.Gal :=
      L.subsingleton_gal_of_top_eq_ground L.top_eq_ground_of_subsingleton
    exact ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (L.rep F) 0)
  inv _ := 0
  inv_injective L := by
    let _ : Subsingleton L.Gal :=
      L.subsingleton_gal_of_top_eq_ground L.top_eq_ground_of_subsingleton
    let _ : Subsingleton (L.H F 2) := ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (L.rep F) 1)
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  range_inv L := by
    rw [L.degree_eq_one_of_top_eq_ground L.top_eq_ground_of_subsingleton]
    ext x
    simp [AddSubgroup.torsionBy, eq_comm]
  inv_restrict _ _ := by simp
  inv_infl _ _ := by simp
  inv_conj _ _ _ := by simp

/-- The invariant maps of the canonical class formation over a subsingleton group are zero. -/
@[simp]
theorem ofSubsingleton_inv_apply [Subsingleton G] (F : Formation G) (L : NormalLayer G)
    (x : L.H F 2) : (ofSubsingleton F).inv L x = 0 := by
  simp [ofSubsingleton]

/-- The Artin map of a layer whose top and ground subgroups agree is the zero homomorphism. -/
@[simp]
theorem artinMap_trivialLayer (cf : ClassFormation F) (L : NormalLayer G)
    (hL : L.top = L.ground) : cf.artinMap L = 0 := by
  apply AddMonoidHom.ext
  intro a
  rw [AddMonoidHom.zero_apply, cf.artinMap_eq_zero_iff L,
    L.normSubgroup_eq_top_of_top_eq_ground F hL]
  exact Submodule.mem_top

end ClassFormation

end TauCeti.ClassFieldTheory
