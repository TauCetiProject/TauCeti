/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Correspondence

/-!
# The norm-subgroup Galois insertion

The local class-field correspondence (`localClassFieldCorrespondence`) matches open finite-index
subgroups `N` of `Kˣ` with finite *abelian* extensions of a nonarchimedean local field `K`. This
file extends it to every finite Galois extension, abelian or not. For an open normal subgroup `V`
of `G_K`, cutting out a finite Galois extension `L/K`, and an open finite-index `N ≤ Kˣ`,

`N_{L/K}(Lˣ) ≤ N  ↔  V ≤ V_N`,

where `V_N` is the layer of the class field of `N` (`localNormOpenSubgroup_le_iff`). On fields:
`L` contains the class field of `N` exactly when `N_{L/K}(Lˣ) ≤ N`
(`classField_localClassField_le_iff`). So taking norm subgroups is the lower adjoint of a Galois
connection whose upper adjoint is the class field (`localClassField_galoisConnection`). Since the
norm subgroup of the class field of `N` is `N`, this is a Galois insertion
(`localClassFieldGaloisInsertion`).

By norm limitation a layer and its maximal abelian sublayer have the same norm subgroup, so the
induced closure operator on layers is the maximal abelian sublayer
(`OpenNormalSubgroup.localClassField_localNormOpenSubgroup`,
`localClassField_galoisConnection_closureOperator`). On fields, the class field of
`N_{L/K}(Lˣ)` is the maximal abelian subextension of `L/K`. Hence the insertion is not an order
isomorphism as soon as its domain contains a nonabelian layer: such a layer differs from its
closure.

All of this holds in characteristic zero. In arbitrary characteristic, with residue
characteristic `p`, the existing correspondence
`localClassFieldCorrespondencePrimeToResidueCharacteristic` covers the abelian layers of degree
prime to `p`. The insertion here has the larger domain `LayerPrimeTo K p` of all layers, abelian
or not, of degree prime to `p`: the norm subgroup of such a layer has index dividing its degree
(`OpenNormalSubgroup.index_localNormSubgroup_dvd_degree`), hence prime to `p`. Its closure
operator is described pointwise: it sends a layer to its maximal abelian sublayer
`LayerPrimeTo.maximalAbelianLayer`
(`localClassFieldPrimeToResidueCharacteristicLayer_localNormOpenSubgroupPrimeTo`).

## Main definitions

* `TauCeti.ClassFieldTheory.localClassFieldGaloisInsertion`: the Galois insertion of open
  finite-index subgroups of `Kˣ` into open normal subgroups of `G_K`, in characteristic zero.
* `TauCeti.ClassFieldTheory.LayerPrimeTo.maximalAbelianLayer`: the maximal abelian sublayer of a
  layer of degree prime to `p`, as a layer of degree prime to `p`.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristicGaloisInsertion`: the
  Galois insertion on layers of degree prime to the residue characteristic.

## Main results

* `TauCeti.ClassFieldTheory.localClassField_galoisConnection`: `N_{L/K}(Lˣ) ≤ N` exactly when
  the layer of `L` lies in the layer of the class field of `N`.
* `TauCeti.ClassFieldTheory.classField_localClassField_le_iff`: the same statement on fields.
* `OpenNormalSubgroup.localClassField_localNormOpenSubgroup`: the class field of the norm
  subgroup of a layer is its maximal abelian sublayer.
* `TauCeti.ClassFieldTheory.eq_maximalAbelianLayer_of_localNormSubgroup_eq`: an abelian layer with
  the norm subgroup of `V` is the maximal abelian sublayer of `V`, in any characteristic.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristic_galoisConnection`,
  `TauCeti.ClassFieldTheory.classField_localClassFieldPrimeToResidueCharacteristic_le_iff` and
  `localClassFieldPrimeToResidueCharacteristicLayer_localNormOpenSubgroupPrimeTo`:
  the same statements in the prime-to-residue-characteristic range.

## References

* J. S. Milne, *Class Field Theory*, I Corollaries 1.2(b) and 1.5, and III Theorem 3.5.
* J.-P. Serre, *Local Fields*, Chapter XIV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer
open _root_.ValuativeRel

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **An abelian layer with the norm subgroup of `V` is its maximal abelian sublayer.** By norm
limitation `V` and `V.maximalAbelianLayer` have the same norm subgroup, and abelian layers are
determined by their norm subgroups. No assumption on the characteristic is needed. -/
theorem eq_maximalAbelianLayer_of_localNormSubgroup_eq
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)} (hW : W.IsAbelianClassFieldLayer)
    (h : localNormSubgroup K W = localNormSubgroup K V) :
    W = V.maximalAbelianLayer :=
  localClassField_unique hW V.isAbelianClassFieldLayer_maximalAbelianLayer
    (h.trans (localNormSubgroup_maximalAbelianLayer K V).symm)

/-! ### Characteristic zero -/

section CharZero

variable [CharZero K]

/-- **Norm subgroups below `N` are the layers below its class field.** In characteristic zero, the
norm subgroup of a finite Galois extension cut out by `V` lies in `N` exactly when `V` lies in the
layer of the class field of `N`. The layer `V` need not be abelian. -/
theorem localNormOpenSubgroup_le_iff
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : LocalNormSubgroups K} :
    localNormOpenSubgroup K V ≤ N ↔ V ≤ (localClassField N).val := by
  rw [localNormOpenSubgroup_le_iff_localNormSubgroup_le, ← localClassField_normSubgroup N]
  exact localNormSubgroup_le_iff_of_isAbelian (localClassField N).property

/-- **The norm-subgroup Galois connection.** In characteristic zero, taking norm subgroups of
finite layers is the lower adjoint of a Galois connection whose upper adjoint sends an open
finite-index subgroup of `Kˣ` to the layer of its class field. -/
theorem localClassField_galoisConnection :
    GaloisConnection (localNormOpenSubgroup K)
      (fun N : LocalNormSubgroups K ↦ (localClassField N).val) :=
  fun _ _ ↦ localNormOpenSubgroup_le_iff

/-- **The norm-subgroup Galois connection on fields.** In characteristic zero, a finite Galois
extension `L/K` contains the class field of `N` exactly when `N_{L/K}(Lˣ) ≤ N`. -/
theorem classField_localClassField_le_iff
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : LocalNormSubgroups K} :
    classField K (localClassField N).val ≤ classField K V ↔
      localNormSubgroup K V ≤ N.val.toSubgroup := by
  rw [classField_le_classField_iff, ← localNormOpenSubgroup_le_iff,
    localNormOpenSubgroup_le_iff_localNormSubgroup_le]

/-- **The norm-subgroup Galois insertion.** In characteristic zero, the norm-subgroup Galois
connection is a Galois insertion: the norm subgroup of the class field of `N` is `N`. -/
def localClassFieldGaloisInsertion :
    GaloisInsertion (localNormOpenSubgroup K)
      (fun N : LocalNormSubgroups K ↦ (localClassField N).val) :=
  localClassField_galoisConnection.toGaloisInsertion fun N ↦
    (localNormOpenSubgroup_localClassField N).ge

/-- **The class field of a norm subgroup is the maximal abelian sublayer.** In characteristic zero,
the layer of the class field of `N_{L/K}(Lˣ)` is the maximal abelian sublayer of the layer of `L`:
on fields, it cuts out the maximal abelian subextension of `L/K`. -/
@[simp]
theorem _root_.OpenNormalSubgroup.localClassField_localNormOpenSubgroup
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localClassField (localNormOpenSubgroup K V)).val = V.maximalAbelianLayer :=
  eq_maximalAbelianLayer_of_localNormSubgroup_eq (localClassField _).property
    (by rw [localClassField_normSubgroup, localNormOpenSubgroup_toSubgroup])

/-- **The closure operator of the norm-subgroup Galois connection** is the maximal abelian
sublayer `OpenNormalSubgroup.abelianLayerClosure`. -/
@[simp]
theorem localClassField_galoisConnection_closureOperator :
    (localClassField_galoisConnection (K := K)).closureOperator =
      OpenNormalSubgroup.abelianLayerClosure :=
  ClosureOperator.ext _ _ fun V ↦ by
    rw [GaloisConnection.closureOperator_apply, OpenNormalSubgroup.abelianLayerClosure_apply,
      V.localClassField_localNormOpenSubgroup]

end CharZero

/-! ### The prime-to-residue-characteristic range -/

section PrimeTo

variable {p : ℕ}

/-- The maximal abelian sublayer of a layer of degree prime to `p`, as a layer of degree prime to
`p`: its degree divides the degree of the layer. -/
def LayerPrimeTo.maximalAbelianLayer (V : LayerPrimeTo K p) : LayerPrimeTo K p :=
  ⟨V.val.maximalAbelianLayer, V.property.coprime_dvd_left <| by
    simp only [degree_eq_relIndex, top_ofOpenNormal, ground_ofOpenNormal]
    exact Subgroup.relIndex_dvd_of_le_left _ V.val.le_maximalAbelianLayer⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The open normal subgroup underlying `V.maximalAbelianLayer` is the maximal abelian sublayer of
the open normal subgroup underlying `V`. -/
@[simp]
theorem LayerPrimeTo.maximalAbelianLayer_coe (V : LayerPrimeTo K p) :
    V.maximalAbelianLayer.val = V.val.maximalAbelianLayer :=
  (rfl)

variable (p) [CharP 𝓀[K] p]

/-- **Norm subgroups below `N` are the layers below its class field**, in the
prime-to-residue-characteristic range. For a layer `V` of degree prime to the residue
characteristic `p` and an open subgroup `N` of index prime to `p`, the norm subgroup of `V` lies in
`N` exactly when `V` lies in the layer of the class field of `N`. -/
theorem localNormOpenSubgroupPrimeTo_le_iff {V : LayerPrimeTo K p}
    {N : LocalNormSubgroupsPrimeTo K p} :
    localNormOpenSubgroupPrimeTo p V ≤ N ↔
      V ≤ localClassFieldPrimeToResidueCharacteristicLayer p N := by
  rw [← Subtype.coe_le_coe (x := localNormOpenSubgroupPrimeTo p V),
    localNormOpenSubgroupPrimeTo_coe, localNormOpenSubgroup_le_iff_localNormSubgroup_le,
    ← Subtype.coe_le_coe (x := V), localClassFieldPrimeToResidueCharacteristicLayer_coe,
    ← localClassFieldPrimeToResidueCharacteristic_normSubgroup p N]
  exact localNormSubgroup_le_iff_of_isAbelian
    (localClassFieldPrimeToResidueCharacteristic p N).val.property

/-- **The prime-to-residue-characteristic norm-subgroup Galois connection.** On layers of degree
prime to the residue characteristic `p`, taking norm subgroups is the lower adjoint of a Galois
connection whose upper adjoint sends an open subgroup of `Kˣ` of index prime to `p` to the layer of
its class field. -/
theorem localClassFieldPrimeToResidueCharacteristic_galoisConnection :
    GaloisConnection (localNormOpenSubgroupPrimeTo (K := K) p)
      (localClassFieldPrimeToResidueCharacteristicLayer p) :=
  fun _ _ ↦ localNormOpenSubgroupPrimeTo_le_iff p

/-- **The prime-to-residue-characteristic norm-subgroup Galois connection on fields.** A finite
Galois extension `L/K` contains the class field of an open subgroup `N` of index prime to the
residue characteristic `p` exactly when `N_{L/K}(Lˣ) ≤ N`. The degree of `L/K` is arbitrary. -/
theorem classField_localClassFieldPrimeToResidueCharacteristic_le_iff
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : LocalNormSubgroupsPrimeTo K p} :
    classField K (localClassFieldPrimeToResidueCharacteristic p N).val.val ≤ classField K V ↔
      localNormSubgroup K V ≤ N.val.val.toSubgroup := by
  rw [classField_le_classField_iff, ← localClassFieldPrimeToResidueCharacteristic_normSubgroup p N]
  exact (localNormSubgroup_le_iff_of_isAbelian
    (localClassFieldPrimeToResidueCharacteristic p N).val.property).symm

/-- **The prime-to-residue-characteristic norm-subgroup Galois insertion.** On layers of degree
prime to the residue characteristic `p`, the norm-subgroup Galois connection is a Galois
insertion: the norm subgroup of the class field of `N` is `N`. -/
def localClassFieldPrimeToResidueCharacteristicGaloisInsertion :
    GaloisInsertion (localNormOpenSubgroupPrimeTo (K := K) p)
      (localClassFieldPrimeToResidueCharacteristicLayer p) :=
  (localClassFieldPrimeToResidueCharacteristic_galoisConnection p).toGaloisInsertion fun N ↦
    (localNormOpenSubgroupPrimeTo_localClassFieldPrimeToResidueCharacteristicLayer p N).ge

/-- **The class field of a norm subgroup is the maximal abelian sublayer**, in the
prime-to-residue-characteristic range: for a layer `V` of degree prime to the residue
characteristic, the layer of the class field of `N_{L/K}(Lˣ)` is the maximal abelian sublayer of
`V`. -/
@[simp]
theorem localClassFieldPrimeToResidueCharacteristic_localNormOpenSubgroupPrimeTo
    (V : LayerPrimeTo K p) :
    (localClassFieldPrimeToResidueCharacteristic p (localNormOpenSubgroupPrimeTo p V)).val.val =
      V.val.maximalAbelianLayer :=
  eq_maximalAbelianLayer_of_localNormSubgroup_eq
    (localClassFieldPrimeToResidueCharacteristic p _).val.property
    (by rw [localClassFieldPrimeToResidueCharacteristic_normSubgroup,
      localNormOpenSubgroupPrimeTo_coe, localNormOpenSubgroup_toSubgroup])

/-- **The closure operator of the prime-to-residue-characteristic norm-subgroup Galois
connection**, pointwise and bundled: the layer of the class field of the norm subgroup of a layer
`V` of degree prime to `p` is `V.maximalAbelianLayer`, as a layer of degree prime to `p`. The
closure operator itself is rewritten to this form by `GaloisConnection.closureOperator_apply`. -/
@[simp]
theorem localClassFieldPrimeToResidueCharacteristicLayer_localNormOpenSubgroupPrimeTo
    (V : LayerPrimeTo K p) :
    localClassFieldPrimeToResidueCharacteristicLayer p (localNormOpenSubgroupPrimeTo p V) =
      V.maximalAbelianLayer :=
  Subtype.ext <| by
    rw [localClassFieldPrimeToResidueCharacteristicLayer_coe, LayerPrimeTo.maximalAbelianLayer_coe,
      localClassFieldPrimeToResidueCharacteristic_localNormOpenSubgroupPrimeTo]

end PrimeTo

end TauCeti.ClassFieldTheory
