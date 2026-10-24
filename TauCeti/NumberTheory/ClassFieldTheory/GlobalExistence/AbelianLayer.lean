/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup

import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Global norm subgroups of abelian layers

Let `K` be a number field and `V` an open normal subgroup of its absolute Galois group `G_K`
containing the closed commutator subgroup, so that `V` cuts out a finite abelian extension `L/K`
with Galois group `G_K ⧸ V`. Global reciprocity for the global class formation then reads as an
isomorphism onto the Galois group of the layer itself,

`C_K / N_{L/K}(C_L) ≃ Gal(L/K)`,

with no abelianization left in the target (`globalAbelianGaloisEquiv`). In particular the global
norm subgroup has index `[L : K]` (`index_globalNormSubgroup`).

This is reciprocity for the abelian layers of a class formation
(`ClassFormation.abelianArtinMap`), applied to the global class formation and read on the idele
class group `C_K` through `globalGroundEquiv`. The lattice laws of global norm subgroups are
likewise those of the norm subgroups of a class formation
(`ClassFormation.normSubgroup_inf_of_isAbelian`, `ClassFormation.normSubgroup_sup`), read on `C_K`
through `globalGroundOrderIso`: the compositum of two finite abelian extensions has the
intersection of their norm subgroups as its norm subgroup (`globalNormSubgroup_inf_of_isAbelian`),
and the intersection of two finite Galois extensions has the product of their norm subgroups
(`globalNormSubgroup_sup`; by norm limitation this needs no abelianity).

## Main definitions

* `TauCeti.ClassFieldTheory.globalAbelianArtinHom`: the Artin map `C_K →* Gal(L/K)` of an abelian
  layer.
* `TauCeti.ClassFieldTheory.globalAbelianGaloisEquiv`: global reciprocity for an abelian layer,
  `C_K / N_{L/K}(C_L) ≃* Gal(L/K)`.

## Main results

* `TauCeti.ClassFieldTheory.globalAbelianGaloisEquiv_artinMap`: `globalAbelianGaloisEquiv` is the
  Artin map of the global class formation.
* `TauCeti.ClassFieldTheory.index_globalNormSubgroup`: `[C_K : N_{L/K}(C_L)] = [L : K]` for an
  abelian layer.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_inf_of_isAbelian`: the norm subgroup of a
  compositum of finite abelian extensions is the intersection of their norm subgroups.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_sup`: the norm subgroup of an intersection of
  finite Galois extensions is the product of their norm subgroups.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable (K : Type) [Field K] [NumberField K]

/-! ### Reciprocity onto the Galois group of an abelian layer -/

section Reciprocity

variable {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- The **Artin map of an abelian layer** of a number field, as a homomorphism from the idele
class group `C_K`: the Artin map `ClassFormation.abelianArtinMap` of the abelian layer for the
global class formation, read on `C_K` through `globalGroundEquiv`. For an abelian layer it takes
values in the Galois group itself rather than in its abelianization. -/
def globalAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    IdeleClassGroup (𝓞 K) K →* (ofOpenNormal V).Gal :=
  (AddMonoidHom.toMultiplicativeLeft ((globalClassFormation K).abelianArtinMap hV)).comp <|
    AddMonoidHom.toMultiplicativeRight (globalGroundEquiv K).toAddMonoidHom

variable {K}

/-- `globalAbelianArtinHom` is the Artin map of the abelian layer evaluated on `c ∈ C_K`, read in
the ground level of the idele-class formation. -/
theorem globalAbelianArtinHom_apply (hV : V.IsAbelianClassFieldLayer)
    (c : IdeleClassGroup (𝓞 K) K) :
    globalAbelianArtinHom K hV c =
      ((globalClassFormation K).abelianArtinMap hV (globalGroundEquiv K (.ofMul c))).toMul :=
  (rfl)

/-- The abelianization class of `globalAbelianArtinHom` is the Artin map of the global class
formation. -/
@[simp]
theorem of_globalAbelianArtinHom (hV : V.IsAbelianClassFieldLayer)
    (c : IdeleClassGroup (𝓞 K) K) :
    Additive.ofMul (Abelianization.of (globalAbelianArtinHom K hV c)) =
      (globalClassFormation K).artinMap (ofOpenNormal V)
        (groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K (.ofMul c))) := by
  rw [globalAbelianArtinHom_apply, ClassFormation.ofMul_of_abelianArtinMap]

/-- **The kernel of `globalAbelianArtinHom` is the global norm subgroup.** -/
theorem ker_globalAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    (globalAbelianArtinHom K hV).ker = globalNormSubgroup K V := by
  ext c
  rw [MonoidHom.mem_ker, globalAbelianArtinHom_apply, toMul_eq_one,
    ClassFormation.abelianArtinMap_eq_zero_iff, ← globalGroundOrderIso_globalNormSubgroup,
    mem_globalGroundOrderIso, AddEquiv.symm_apply_apply, toMul_ofMul]

/-- **`globalAbelianArtinHom` is surjective.** -/
theorem surjective_globalAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Function.Surjective (globalAbelianArtinHom K hV) := by
  intro γ
  obtain ⟨a, ha⟩ := (globalClassFormation K).surjective_abelianArtinMap hV (Additive.ofMul γ)
  obtain ⟨c, rfl⟩ := (globalGroundEquiv K).surjective a
  refine ⟨c.toMul, ?_⟩
  rw [globalAbelianArtinHom_apply, ofMul_toMul, ha, toMul_ofMul]

variable (K) in
/-- **Global reciprocity for an abelian layer**, `C_K / N_{L/K}(C_L) ≃* Gal(L/K)`. Its target is
the Galois group `G_K ⧸ V` of the layer itself: since the layer is abelian,
`abelianizationGalEquiv` removes the abelianization from the target of the Artin equivalence of
the global class formation (`globalAbelianGaloisEquiv_artinMap`). -/
def globalAbelianGaloisEquiv (hV : V.IsAbelianClassFieldLayer) :
    IdeleClassGroup (𝓞 K) K ⧸ globalNormSubgroup K V ≃* (ofOpenNormal V).Gal :=
  (QuotientGroup.quotientMulEquivOfEq (ker_globalAbelianArtinHom hV).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_globalAbelianArtinHom hV))

/-- `globalAbelianGaloisEquiv` sends the class of `c` to its Artin symbol
`globalAbelianArtinHom K hV c`. -/
@[simp]
theorem globalAbelianGaloisEquiv_mk (hV : V.IsAbelianClassFieldLayer)
    (c : IdeleClassGroup (𝓞 K) K) :
    globalAbelianGaloisEquiv K hV (QuotientGroup.mk c) = globalAbelianArtinHom K hV c := by
  rw [globalAbelianGaloisEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **`globalAbelianGaloisEquiv` is the Artin map of the global class formation**: composed with
`Abelianization.of`, which is injective because the layer is abelian, it is
`ClassFormation.artinMap`. So it is reciprocity, not an arbitrary isomorphism between two finite
groups of the same order. -/
theorem globalAbelianGaloisEquiv_artinMap (hV : V.IsAbelianClassFieldLayer)
    (c : IdeleClassGroup (𝓞 K) K) :
    Additive.ofMul (Abelianization.of (globalAbelianGaloisEquiv K hV (QuotientGroup.mk c))) =
      (globalClassFormation K).artinMap (ofOpenNormal V)
        (groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K (.ofMul c))) := by
  rw [globalAbelianGaloisEquiv_mk, of_globalAbelianArtinHom]

/-- **The norm index of an abelian layer**: `[C_K : N_{L/K}(C_L)] = [L : K]`, the degree of the
layer being the order of its Galois group `G_K ⧸ V`. -/
theorem index_globalNormSubgroup (hV : V.IsAbelianClassFieldLayer) :
    (globalNormSubgroup K V).index = (ofOpenNormal V).degree := by
  rw [Subgroup.index_eq_card, degree_eq_natCard_gal,
    Nat.card_congr (globalAbelianGaloisEquiv K hV).toEquiv]

end Reciprocity

/-! ### Composita and intersections -/

section Lattice

variable {K} {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- **Composita.** For finite abelian extensions of a number field cut out by `V` and `W`, the
idele-class norm subgroup of their compositum, cut out by `V ⊓ W`, is the intersection of the two
norm subgroups. Abelianity is needed: by norm limitation the left side only sees the maximal
abelian subextension of the compositum, which can be larger than the compositum of the maximal
abelian subextensions. -/
theorem globalNormSubgroup_inf_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    globalNormSubgroup K (V ⊓ W) = globalNormSubgroup K V ⊓ globalNormSubgroup K W := by
  apply (globalGroundOrderIso K).injective
  rw [map_inf, globalGroundOrderIso_globalNormSubgroup, globalGroundOrderIso_globalNormSubgroup,
    globalGroundOrderIso_globalNormSubgroup,
    (globalClassFormation K).normSubgroup_inf_of_isAbelian hV hW]

/-- **Intersections.** The idele-class norm subgroup of the intersection of the finite Galois
extensions cut out by `V` and `W`, which is cut out by `V ⊔ W`, is the product of the two norm
subgroups. No abelianity is needed: by norm limitation every norm subgroup is that of its maximal
abelian sublayer, and the maximal abelian sublayer of `V ⊔ W` is the join of those of `V` and
`W`. -/
@[simp]
theorem globalNormSubgroup_sup (V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    globalNormSubgroup K (V ⊔ W) = globalNormSubgroup K V ⊔ globalNormSubgroup K W := by
  apply (globalGroundOrderIso K).injective
  rw [map_sup, globalGroundOrderIso_globalNormSubgroup, globalGroundOrderIso_globalNormSubgroup,
    globalGroundOrderIso_globalNormSubgroup, (globalClassFormation K).normSubgroup_sup]

end Lattice

end TauCeti.ClassFieldTheory
