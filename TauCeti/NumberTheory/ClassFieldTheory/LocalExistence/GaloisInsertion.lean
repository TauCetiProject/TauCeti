/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Correspondence

/-!
# The norm-subgroup Galois insertion

The local class-field correspondence `localClassFieldCorrespondence` identifies open finite-index
subgroups of `Kˣ` with the abelian layers of the absolute Galois group. This file extends it to
every open normal subgroup `V` of `G_K`, abelian or not: the norm subgroup of `V` lies in `N`
exactly when `V` lies in the class field of `N`. On fields, a finite Galois extension `L/K`
contains the class field of `N` exactly when `N_{L/K}(Lˣ) ≤ N`.

Together with `localClassField_normSubgroup`, the norm subgroup and the class field form a Galois
insertion. Its closure operator on layers is the maximal abelian sublayer: by norm limitation and
uniqueness, the class field of the norm subgroup of `V` is `V.maximalAbelianLayer`. The insertion
is not an order isomorphism, since a nonabelian layer is strictly below its maximal abelian
sublayer.

Both statements are proved in characteristic zero, and in every characteristic in the
prime-to-residue-characteristic range, where the layers are restricted to those of degree prime
to `p`.

## Main definitions

* `TauCeti.ClassFieldTheory.localClassFieldGaloisInsertion`: the norm-subgroup Galois insertion
  in characteristic zero.
* `TauCeti.ClassFieldTheory.OpenNormalLayerPrimeTo`: open normal subgroups of `G_K` whose layer
  has degree prime to `p`.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristicGaloisInsertion`: the
  norm-subgroup Galois insertion in the prime-to-residue-characteristic range.

## Main results

* `TauCeti.ClassFieldTheory.localClassField_galoisConnection`: the norm subgroup of `V` lies in
  `N` exactly when `V` lies in the class field of `N`.
* `TauCeti.ClassFieldTheory.localClassField_localNormOpenSubgroup`: the class field of the norm
  subgroup of `V` is the maximal abelian sublayer of `V`.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristic_galoisConnection` and
  `TauCeti.ClassFieldTheory.localClassFieldPrimeToLayer_localNormOpenSubgroupPrimeTo`:
  the same statements in the prime-to-residue-characteristic range.

## References

* J. S. Milne, *Class Field Theory*, I Corollaries 1.2(b) and 1.5, and III Theorem 3.5.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer
open _root_.ValuativeRel

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For any layer `V` and any abelian layer `W`, the bundled norm subgroup of `V` lies in that of
`W` exactly when `V ≤ W`. -/
private theorem localNormOpenSubgroup_le_iff_of_isAbelian
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)} (hW : W.IsAbelianClassFieldLayer) :
    localNormOpenSubgroup K V ≤ localNormOpenSubgroup K W ↔ V ≤ W := by
  rw [← Subtype.coe_le_coe, ← OpenSubgroup.toSubgroup_le, localNormOpenSubgroup_toSubgroup,
    localNormOpenSubgroup_toSubgroup]
  exact localNormSubgroup_le_iff_of_isAbelian hW

/-! ### Characteristic zero -/

section CharZero

variable [CharZero K]

/-- The bundled norm subgroup of the local class field attached to `N` is `N`. -/
private theorem localNormOpenSubgroup_localClassField (N : LocalNormSubgroups K) :
    localNormOpenSubgroup K (localClassField N).val = N := by
  simpa using localClassFieldCorrespondence.symm_apply_apply N

variable (K) in
/-- **The norm-subgroup Galois connection.** In characteristic zero, for every open normal
subgroup `V` of `G_K` (abelian or not) and every open finite-index `N ≤ Kˣ`, the norm subgroup of
`V` lies in `N` exactly when `V` lies in the class field of `N`. On fields: a finite Galois
extension contains the class field of `N` exactly when its norm group lies in `N`. -/
theorem localClassField_galoisConnection :
    GaloisConnection (localNormOpenSubgroup K)
      (fun N : LocalNormSubgroups K ↦ (localClassField N).val) := fun V N ↦ by
  conv_lhs => rw [← localNormOpenSubgroup_localClassField N]
  exact localNormOpenSubgroup_le_iff_of_isAbelian (localClassField N).property

variable (K) in
/-- **The norm-subgroup Galois insertion** in characteristic zero: the Galois connection
`localClassField_galoisConnection`, with `localClassField_normSubgroup` as the insertion
equation. -/
def localClassFieldGaloisInsertion :
    GaloisInsertion (localNormOpenSubgroup K)
      (fun N : LocalNormSubgroups K ↦ (localClassField N).val) :=
  (localClassField_galoisConnection K).toGaloisInsertion fun N ↦
    (localNormOpenSubgroup_localClassField N).ge

variable (K) in
/-- **The closure operator of the insertion.** The class field of the norm subgroup of a layer is
its maximal abelian sublayer; this is norm limitation, `localNormSubgroup_maximalAbelianLayer`,
read through uniqueness. The insertion is not an order isomorphism: a nonabelian layer lies
strictly below its maximal abelian sublayer. -/
theorem localClassField_localNormOpenSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localClassField (localNormOpenSubgroup K V)).val = V.maximalAbelianLayer :=
  localClassField_unique (localClassField _).property
    V.isAbelianClassFieldLayer_maximalAbelianLayer <| by
      rw [localClassField_normSubgroup, localNormSubgroup_maximalAbelianLayer,
        localNormOpenSubgroup_toSubgroup]

end CharZero

/-! ### The prime-to-residue-characteristic range -/

/-- Open normal subgroups of `G_K` whose layer has degree prime to `p`: the source of the
prime-to-residue-characteristic norm-subgroup Galois insertion. -/
abbrev OpenNormalLayerPrimeTo (K : Type) [Field K] (p : ℕ) : Type :=
  {V : OpenNormalSubgroup (AbsoluteGaloisGroup K) // (ofOpenNormal V).degree.Coprime p}

/-- The norm subgroup of a layer of degree prime to `p` has index prime to `p`. -/
private theorem index_localNormSubgroup_coprime {p : ℕ} (V : OpenNormalLayerPrimeTo K p) :
    (localNormOpenSubgroup K V.val).val.toSubgroup.index.Coprime p := by
  rw [localNormOpenSubgroup_toSubgroup, ← localNormSubgroup_maximalAbelianLayer,
    index_localNormSubgroup (K := K) V.val.isAbelianClassFieldLayer_maximalAbelianLayer]
  exact Nat.Coprime.coprime_dvd_left (V.val.degree_ofOpenNormal_maximalAbelianLayer_dvd) V.property

/-- The norm subgroup of a layer of degree prime to `p`, as a norm subgroup of index prime
to `p`. -/
def localNormOpenSubgroupPrimeTo {p : ℕ} (V : OpenNormalLayerPrimeTo K p) :
    LocalNormSubgroupsPrimeTo K p :=
  ⟨localNormOpenSubgroup K V.val, index_localNormSubgroup_coprime V⟩

/-- The open finite-index subgroup underlying `localNormOpenSubgroupPrimeTo` is the norm subgroup
of the layer. -/
@[simp]
theorem localNormOpenSubgroupPrimeTo_val {p : ℕ} (V : OpenNormalLayerPrimeTo K p) :
    (localNormOpenSubgroupPrimeTo V).val = localNormOpenSubgroup K V.val :=
  (rfl)

variable (p : ℕ) [CharP 𝓀[K] p]

/-- The prime-to-`p` local class field of `N`, as a layer of degree prime to `p`. -/
def localClassFieldPrimeToLayer (N : LocalNormSubgroupsPrimeTo K p) : OpenNormalLayerPrimeTo K p :=
  ⟨(localClassFieldPrimeToResidueCharacteristic p N).val.val,
    (localClassFieldPrimeToResidueCharacteristic p N).property⟩

/-- The layer underlying `localClassFieldPrimeToLayer` is the prime-to-`p` local class field. -/
@[simp]
theorem localClassFieldPrimeToLayer_val (N : LocalNormSubgroupsPrimeTo K p) :
    (localClassFieldPrimeToLayer p N).val =
      (localClassFieldPrimeToResidueCharacteristic p N).val.val :=
  (rfl)

/-- The prime-to-`p` norm subgroup of the prime-to-`p` local class field attached to `N` is `N`. -/
private theorem localNormOpenSubgroupPrimeTo_localClassFieldPrimeToLayer
    (N : LocalNormSubgroupsPrimeTo K p) :
    localNormOpenSubgroupPrimeTo (localClassFieldPrimeToLayer p N) = N :=
  Subtype.ext <| by
    simpa using congrArg Subtype.val
      ((localClassFieldCorrespondencePrimeToResidueCharacteristic (K := K) p).symm_apply_apply N)

variable (K) in
/-- **The prime-to-residue-characteristic norm-subgroup Galois connection.** For a layer `V` of
degree prime to `p` and a norm subgroup `N` of index prime to `p`, the norm subgroup of `V` lies
in `N` exactly when `V` lies in the class field of `N`. -/
theorem localClassFieldPrimeToResidueCharacteristic_galoisConnection :
    GaloisConnection (localNormOpenSubgroupPrimeTo (K := K) (p := p))
      (localClassFieldPrimeToLayer p) := fun V N ↦ by
  conv_lhs => rw [← localNormOpenSubgroupPrimeTo_localClassFieldPrimeToLayer p N]
  exact localNormOpenSubgroup_le_iff_of_isAbelian
    (localClassFieldPrimeToResidueCharacteristic p N).val.property

variable (K) in
/-- **The prime-to-residue-characteristic norm-subgroup Galois insertion**, with
`localClassFieldPrimeToResidueCharacteristic_normSubgroup` as the insertion equation. -/
def localClassFieldPrimeToResidueCharacteristicGaloisInsertion :
    GaloisInsertion (localNormOpenSubgroupPrimeTo (K := K) (p := p))
      (localClassFieldPrimeToLayer p) :=
  (localClassFieldPrimeToResidueCharacteristic_galoisConnection K p).toGaloisInsertion fun N ↦
    (localNormOpenSubgroupPrimeTo_localClassFieldPrimeToLayer p N).ge

/-- **The closure operator of the prime-to-`p` insertion** is the maximal abelian sublayer: the
prime-to-`p` class field of the norm subgroup of a layer of degree prime to `p` is its maximal
abelian sublayer. -/
theorem localClassFieldPrimeToLayer_localNormOpenSubgroupPrimeTo
    (V : OpenNormalLayerPrimeTo K p) :
    (localClassFieldPrimeToLayer p (localNormOpenSubgroupPrimeTo V)).val =
      V.val.maximalAbelianLayer :=
  localClassField_unique (localClassFieldPrimeToResidueCharacteristic p _).val.property
    V.val.isAbelianClassFieldLayer_maximalAbelianLayer <| by
      rw [localClassFieldPrimeToLayer_val,
        localClassFieldPrimeToResidueCharacteristic_normSubgroup,
        localNormSubgroup_maximalAbelianLayer, localNormOpenSubgroupPrimeTo_val,
        localNormOpenSubgroup_toSubgroup]

end TauCeti.ClassFieldTheory
