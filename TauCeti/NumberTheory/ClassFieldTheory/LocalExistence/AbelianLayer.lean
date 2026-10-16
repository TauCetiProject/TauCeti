/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup

import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Norm subgroups of abelian local layers

Let `K` be a nonarchimedean local field and `V` an open normal subgroup of its absolute Galois
group `G_K` containing the closed commutator subgroup, so that `V` cuts out a finite abelian
extension `L/K` with Galois group `G_K ⧸ V`. Local reciprocity for the local class formation then
reads as an isomorphism onto the Galois group of the layer itself,

`Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)`,

with no abelianization left in the target (`localAbelianGaloisEquiv`). In particular the norm
subgroup has index `[L : K]` (`index_localNormSubgroup`).

This is reciprocity for the abelian layers of a class formation
(`ClassFormation.abelianArtinMap`), applied to the local class formation and read on `Kˣ`. The
lattice laws of local norm subgroups are likewise those of the norm subgroups of a class formation
(`ClassFormation.normSubgroup_inf_of_isAbelian`, `ClassFormation.normSubgroup_sup`), read on `Kˣ`
through `localGroundOrderIso`: the compositum of two finite abelian extensions has the intersection
of their norm subgroups as its norm subgroup (`localNormSubgroup_inf_of_isAbelian`), and the
intersection of two finite Galois extensions has the product of their norm subgroups
(`localNormSubgroup_sup`; by norm limitation this needs no abelianity).

## Main definitions

* `TauCeti.ClassFieldTheory.localAbelianGaloisEquiv`: local reciprocity for an abelian layer,
  `Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)`.

## Main results

* `TauCeti.ClassFieldTheory.localAbelianGaloisEquiv_artinMap`: `localAbelianGaloisEquiv` is the
  Artin map of the local class formation.
* `TauCeti.ClassFieldTheory.index_localNormSubgroup`: `[Kˣ : N_{L/K}(Lˣ)] = [L : K]` for an
  abelian layer.
* `TauCeti.ClassFieldTheory.localNormSubgroup_inf_of_isAbelian`: the norm subgroup of a compositum
  of finite abelian extensions is the intersection of their norm subgroups.
* `TauCeti.ClassFieldTheory.localNormSubgroup_sup`: the norm subgroup of an intersection of finite
  Galois extensions is the product of their norm subgroups.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Reciprocity onto the Galois group of an abelian layer -/

section Reciprocity

variable {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- The Artin map of the local class formation on the layer `V ◁ G_K`, as a homomorphism from
`Kˣ`: the Artin map `ClassFormation.abelianArtinMap` of the abelian layer, read on `Kˣ` through the
identification of `Kˣ` with the ground level. For an abelian layer it is read in the Galois group
itself rather than in its abelianization. -/
def localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Kˣ →* (ofOpenNormal V).Gal :=
  (AddMonoidHom.toMultiplicativeLeft ((localClassFormation K).abelianArtinMap hV)).comp <|
    AddMonoidHom.toMultiplicativeRight
      (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_toSubgroup_top_eq_fieldRange K)).toAddMonoidHom

variable {K}

/-- `localAbelianArtinHom` is the Artin map of the abelian layer evaluated on `x ∈ Kˣ`, read in
the ground level `((Kˢ)ˣ)^{G_K}`. -/
theorem localAbelianArtinHom_apply (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    localAbelianArtinHom K hV x =
      ((localClassFormation K).abelianArtinMap hV
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_toSubgroup_top_eq_fieldRange K) (Additive.ofMul x))).toMul :=
  (rfl)

/-- The abelianization class of `localAbelianArtinHom` is the Artin map of the local class
formation. -/
@[simp]
theorem of_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    Additive.ofMul (Abelianization.of (localAbelianArtinHom K hV x)) =
      (localClassFormation K).artinMap (ofOpenNormal V)
        (localGroundEquiv K V (Additive.ofMul x)) := by
  rw [localAbelianArtinHom_apply, ClassFormation.ofMul_of_abelianArtinMap,
    groundEquivOfOpenNormal_unitsLevelEquiv]

/-- The kernel of `localAbelianArtinHom` is the local norm subgroup. -/
theorem ker_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    (localAbelianArtinHom K hV).ker = localNormSubgroup K V := by
  ext x
  rw [MonoidHom.mem_ker, localAbelianArtinHom_apply, toMul_eq_one,
    ClassFormation.abelianArtinMap_eq_zero_iff, Formation.mem_normSubgroup,
    groundEquivOfOpenNormal_unitsLevelEquiv, localGroundEquiv_mem_normSubgroup_iff]

/-- `localAbelianArtinHom` is surjective. -/
theorem surjective_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Function.Surjective (localAbelianArtinHom K hV) := by
  intro γ
  obtain ⟨a, ha⟩ := (localClassFormation K).surjective_abelianArtinMap hV (Additive.ofMul γ)
  obtain ⟨x, rfl⟩ := (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
    (fixedField_toSubgroup_top_eq_fieldRange K)).surjective a
  refine ⟨x.toMul, ?_⟩
  rw [localAbelianArtinHom_apply, ofMul_toMul, ha, toMul_ofMul]

variable (K) in
/-- **Local reciprocity for an abelian layer**, `Kˣ / N_{L/K}(Lˣ) ≃* Gal(L/K)`. Its target is the
Galois group `G_K ⧸ V` of the layer itself: since the layer is abelian, `abelianizationGalEquiv`
removes the abelianization from the target of the Artin equivalence of the local class formation
(`localAbelianGaloisEquiv_artinMap`). -/
def localAbelianGaloisEquiv (hV : V.IsAbelianClassFieldLayer) :
    Kˣ ⧸ localNormSubgroup K V ≃* (ofOpenNormal V).Gal :=
  (QuotientGroup.quotientMulEquivOfEq (ker_localAbelianArtinHom hV).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_localAbelianArtinHom hV))

/-- `localAbelianGaloisEquiv` sends the class of `x` to its Artin symbol
`localAbelianArtinHom K hV x`. -/
@[simp]
theorem localAbelianGaloisEquiv_mk (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    localAbelianGaloisEquiv K hV (QuotientGroup.mk x) = localAbelianArtinHom K hV x := by
  rw [localAbelianGaloisEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- **`localAbelianGaloisEquiv` is the Artin map of the local class formation**: composed with
`Abelianization.of`, which is injective because the layer is abelian, it is
`ClassFormation.artinMap`. -/
theorem localAbelianGaloisEquiv_artinMap (hV : V.IsAbelianClassFieldLayer) (x : Kˣ) :
    Additive.ofMul (Abelianization.of (localAbelianGaloisEquiv K hV (QuotientGroup.mk x))) =
      (localClassFormation K).artinMap (ofOpenNormal V)
        (localGroundEquiv K V (Additive.ofMul x)) := by
  rw [localAbelianGaloisEquiv_mk, of_localAbelianArtinHom]

/-- **The norm index of an abelian layer**: `[Kˣ : N_{L/K}(Lˣ)] = [L : K]`, the degree of the
layer being the order of its Galois group `G_K ⧸ V`. -/
theorem index_localNormSubgroup (hV : V.IsAbelianClassFieldLayer) :
    (localNormSubgroup K V).index = (ofOpenNormal V).degree := by
  rw [Subgroup.index_eq_card, degree_eq_natCard_gal,
    Nat.card_congr (localAbelianGaloisEquiv K hV).toEquiv]

end Reciprocity

/-! ### Composita and intersections -/

section Lattice

variable {K} {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- **Composita.** For finite abelian extensions cut out by `V` and `W`, the norm subgroup of their
compositum, cut out by `V ⊓ W`, is the intersection of the two norm subgroups. Abelianity is
needed: by norm limitation the left side only sees the maximal abelian subextension of the
compositum, which can be larger than the compositum of the maximal abelian subextensions. -/
theorem localNormSubgroup_inf_of_isAbelian (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer) :
    localNormSubgroup K (V ⊓ W) = localNormSubgroup K V ⊓ localNormSubgroup K W := by
  apply (localGroundOrderIso K).injective
  rw [map_inf, localGroundOrderIso_localNormSubgroup, localGroundOrderIso_localNormSubgroup,
    localGroundOrderIso_localNormSubgroup,
    (localClassFormation K).normSubgroup_inf_of_isAbelian hV hW]

/-- **Intersections.** The norm subgroup of the intersection of the finite Galois extensions cut
out by `V` and `W`, which is cut out by `V ⊔ W`, is the product of the two norm subgroups. No
abelianity is needed: by norm limitation every norm subgroup is that of its maximal abelian
sublayer, and the maximal abelian sublayer of `V ⊔ W` is the join of those of `V` and `W`. -/
@[simp]
theorem localNormSubgroup_sup (V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    localNormSubgroup K (V ⊔ W) = localNormSubgroup K V ⊔ localNormSubgroup K W := by
  apply (localGroundOrderIso K).injective
  rw [map_sup, localGroundOrderIso_localNormSubgroup, localGroundOrderIso_localNormSubgroup,
    localGroundOrderIso_localNormSubgroup, (localClassFormation K).normSubgroup_sup]

end Lattice

end TauCeti.ClassFieldTheory
