/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce
import TauCeti.GroupTheory.FreeGroup.Rank
import TauCeti.GroupTheory.FreeGroup.ResiduallyP
import TauCeti.GroupTheory.ResiduallyFinite

/-!
# Two noncommuting elements of a free group generate a free group of rank two

Let `a` and `b` be elements of a free group `F`. If they do not commute, the homomorphism
`FreeGroup (Fin 2) →* F` sending the two generators to `a` and `b` is injective, so `a` and `b`
freely generate the subgroup they generate. Together with the description of commuting pairs as
powers of a common element (`IsFreeGroup.commute_iff_exists_common_zpow`), this shows that a
two-generated subgroup of a free group is trivial, infinite cyclic, or free of rank two.

The proof is the classical one. The subgroup `H = ⟨a, b⟩` is free by the Nielsen–Schreier theorem,
say on a basis `ι`. As `H` is the image of `FreeGroup (Fin 2)`, the basis `ι` has at most two
elements (`FreeGroupBasis.card_le_of_surjective`). It has at least two since `H` is not
commutative. Hence `H ≃* FreeGroup (Fin 2)`, and the surjection `FreeGroup (Fin 2) →* H` becomes a
surjective endomorphism of `FreeGroup (Fin 2)`, which is injective because finitely generated
residually finite groups are Hopfian.

## Main results

* `FreeGroup.not_commute_of_injective_lift`: two elements of any group that freely generate a free
  group of rank two do not commute.
* `IsFreeGroup.injective_lift_iff_not_commute`: the homomorphism `FreeGroup (Fin 2) →* F` sending
  the generators to `a` and `b` is injective if and only if `a` and `b` do not commute.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter I.
* A. I. Malcev, *On isomorphic matrix representations of infinite groups*, Mat. Sb. 8 (50)
  (1940), 405–422.
-/

public section

/-- Two elements of a group that freely generate a free group of rank two do not commute, since
the two generators of `FreeGroup (Fin 2)` do not. -/
theorem FreeGroup.not_commute_of_injective_lift {G : Type*} [Group G] {a b : G}
    (h : Function.Injective (FreeGroup.lift ![a, b])) : ¬Commute a b := fun hab => by
  have : Commute (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) := h (by simpa using hab.eq)
  exact absurd (FreeGroup.eq_of_commute_of_of this) (by decide)

namespace IsFreeGroup

variable {F : Type*} [Group F] [IsFreeGroup F]

/-- If two elements of a subgroup `H` of a free group do not commute, the basis of `H` has at
least two elements. -/
private theorem not_subsingleton_generators_of_not_commute {H : Subgroup F} {a b : F} (ha : a ∈ H)
    (hb : b ∈ H) (h : ¬Commute a b) : ¬Subsingleton (Generators H) := by
  intro hι
  have : IsMulCommutative (FreeGroup (Generators H)) :=
    FreeGroup.isMulCommutative_iff_subsingleton.mpr hι
  have : IsMulCommutative H := (basis H).repr.symm.surjective.isMulCommutative
  exact h (congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩))

/-- **Two noncommuting elements of a free group freely generate a free group of rank two.** -/
theorem injective_lift_of_not_commute {a b : F} (h : ¬Commute a b) :
    Function.Injective (FreeGroup.lift ![a, b]) := by
  set φ := FreeGroup.lift ![a, b]
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  -- The range of `φ` is free by the Nielsen–Schreier theorem, on a basis of exactly two elements.
  have := (basis φ.range).finite_of_surjective hsurj
  have hle := (basis φ.range).card_le_of_surjective hsurj
  rw [Nat.card_fin] at hle
  have hge : ¬Nat.card (Generators φ.range) ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    exact not_subsingleton_generators_of_not_commute ⟨FreeGroup.of 0, by simp [φ]⟩
      ⟨FreeGroup.of 1, by simp [φ]⟩ h
  let e : Generators φ.range ≃ Fin 2 := Finite.equivFinOfCardEq (by omega)
  -- Identifying the range with `FreeGroup (Fin 2)`, `φ` becomes a surjective endomorphism.
  let ψ : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
    ((basis φ.range).repr.trans (FreeGroup.freeGroupCongr e)).toMonoidHom.comp φ.rangeRestrict
  have hψ : Function.Injective ψ :=
    Group.ResiduallyFinite.injective_of_surjective
      (((basis φ.range).repr.trans (FreeGroup.freeGroupCongr e)).surjective.comp hsurj)
  rw [MonoidHom.coe_comp] at hψ
  exact MonoidHom.rangeRestrict_injective_iff.mp hψ.of_comp

/-- Elements `a` and `b` of a free group freely generate a free group of rank two if and only if
they do not commute. -/
theorem injective_lift_iff_not_commute {a b : F} :
    Function.Injective (FreeGroup.lift ![a, b]) ↔ ¬Commute a b :=
  ⟨FreeGroup.not_commute_of_injective_lift, injective_lift_of_not_commute⟩

end IsFreeGroup
