/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap

/-!
# The Artin map of a trivial layer

For a finite normal layer `V ◁ U` with equal top and ground subgroups, the relative subgroup is
all of `U`, so its Galois group `U / V` is trivial and its degree is one. The norm is therefore the
identity after identifying the two levels. In particular, its image is the whole ground level and
the norm quotient is trivial.

For a class formation, Artin reciprocity identifies this norm quotient with the additive
abelianization of the Galois group. Consequently the Artin map of the layer is the unique additive
homomorphism into a trivial group. This gives the trivial-layer direction check without comparing
cardinalities.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.subsingleton_gal_of_top_eq_ground`: the Galois group of a
  trivial layer is a subsingleton.
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
theorem normSubgroup_eq_top_of_top_eq_ground (hL : L.top = L.ground) :
    L.normSubgroup F = ⊤ := by
  ext y
  rw [L.mem_normSubgroup]
  exact iff_true_intro (L.norm_surjective_of_top_eq_ground F hL y)

/-- The norm quotient of a trivial layer is a subsingleton. -/
theorem subsingleton_normQuotient_of_top_eq_ground (hL : L.top = L.ground) :
    Subsingleton (L.NormQuotient F) := by
  rw [Submodule.Quotient.subsingleton_iff]
  exact L.normSubgroup_eq_top_of_top_eq_ground F hL

end NormalLayer

namespace ClassFormation

variable {F : Formation G}

/-- The Artin map of a layer whose top and ground subgroups agree is the zero homomorphism. -/
theorem artinMap_trivialLayer (cf : ClassFormation F) (L : NormalLayer G)
    (hL : L.top = L.ground) : cf.artinMap L = 0 := by
  have hsource := L.subsingleton_normQuotient_of_top_eq_ground F hL
  have htarget : Subsingleton (Additive (Abelianization L.Gal)) :=
    @Function.Surjective.subsingleton _ _ (cf.artinEquiv L) hsource
      (cf.artinEquiv L).surjective
  ext a
  exact @Subsingleton.elim _ htarget _ _

end ClassFormation

end TauCeti.ClassFieldTheory
