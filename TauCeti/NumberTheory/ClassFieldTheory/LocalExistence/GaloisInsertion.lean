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

The connection is not an order isomorphism: norm limitation identifies the norm subgroup of a
layer with that of its maximal abelian sublayer, and the induced closure operator on layers is the
maximal abelian sublayer (`localClassField_localNormOpenSubgroup`,
`localClassField_galoisConnection_closureOperator`). On fields, the class field of
`N_{L/K}(Lˣ)` is the maximal abelian subextension of `L/K`.

All of this holds in characteristic zero. In arbitrary characteristic it holds for layers of
degree prime to the residue characteristic `p`, the range of
`localClassFieldCorrespondencePrimeToResidueCharacteristic`: the norm subgroup of such a layer has
index dividing its degree (`index_localNormSubgroup_dvd_degree`), hence prime to `p`.

## Main definitions

* `TauCeti.ClassFieldTheory.localClassFieldGaloisInsertion`: the Galois insertion of open
  finite-index subgroups of `Kˣ` into open normal subgroups of `G_K`, in characteristic zero.
* `TauCeti.ClassFieldTheory.LayerPrimeTo`: finite layers of degree prime to `p`.
* `TauCeti.ClassFieldTheory.localNormOpenSubgroupPrimeTo`: the norm subgroup of such a layer, as a
  subgroup of index prime to `p`.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristicGaloisInsertion`: the
  Galois insertion in the prime-to-residue-characteristic range.

## Main results

* `TauCeti.ClassFieldTheory.localClassField_galoisConnection`: `N_{L/K}(Lˣ) ≤ N` exactly when
  the layer of `L` lies in the layer of the class field of `N`.
* `TauCeti.ClassFieldTheory.classField_localClassField_le_iff`: the same statement on fields.
* `TauCeti.ClassFieldTheory.localClassField_localNormOpenSubgroup`: the class field of the norm
  subgroup of a layer is its maximal abelian sublayer.
* `TauCeti.ClassFieldTheory.localClassFieldPrimeToResidueCharacteristic_galoisConnection`,
  `TauCeti.ClassFieldTheory.classField_localClassFieldPrimeToResidueCharacteristic_le_iff` and
  `localClassFieldPrimeToResidueCharacteristic_localNormOpenSubgroupPrimeTo`: the same statements
  for layers of degree prime to the residue characteristic.

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

/-- Inclusion of an open finite-index subgroup in the norm subgroup of a finite layer is inclusion
of the underlying subgroups. -/
theorem localNormOpenSubgroup_le_iff_localNormSubgroup_le
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : LocalNormSubgroups K} :
    localNormOpenSubgroup K V ≤ N ↔ localNormSubgroup K V ≤ N.val.toSubgroup := by
  rw [← localNormOpenSubgroup_toSubgroup, Subtype.coe_le_coe.symm, OpenSubgroup.toSubgroup_le]

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

/-- The norm subgroup of the class field of `N` is `N`, as an open finite-index subgroup. -/
@[simp]
theorem localNormOpenSubgroup_localClassField (N : LocalNormSubgroups K) :
    localNormOpenSubgroup K (localClassField N).val = N :=
  Subtype.ext <| OpenSubgroup.toSubgroup_injective <|
    (localNormOpenSubgroup_toSubgroup K _).trans (localClassField_normSubgroup N)

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
theorem localClassField_localNormOpenSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localClassField (localNormOpenSubgroup K V)).val = V.maximalAbelianLayer :=
  localClassField_unique (localClassField _).property V.isAbelianClassFieldLayer_maximalAbelianLayer
    (by rw [localClassField_normSubgroup, localNormOpenSubgroup_toSubgroup,
      localNormSubgroup_maximalAbelianLayer])

/-- **The closure operator of the norm-subgroup Galois connection** is the maximal abelian
sublayer `OpenNormalSubgroup.abelianLayerClosure`. -/
theorem localClassField_galoisConnection_closureOperator :
    (localClassField_galoisConnection (K := K)).closureOperator =
      OpenNormalSubgroup.abelianLayerClosure :=
  ClosureOperator.ext _ _ fun V ↦ by
    rw [OpenNormalSubgroup.abelianLayerClosure_apply]
    -- `gc.closureOperator V` is `u (l V)` by definition; Mathlib states no `_apply` lemma for it.
    exact localClassField_localNormOpenSubgroup V

end CharZero

/-! ### The prime-to-residue-characteristic range -/

section PrimeTo

/-- Finite layers whose degree is prime to `p`. -/
abbrev LayerPrimeTo (K : Type) [Field K] (p : ℕ) : Type :=
  {V : OpenNormalSubgroup (AbsoluteGaloisGroup K) // (ofOpenNormal V).degree.Coprime p}

variable (p : ℕ)

/-- The norm subgroup of a finite layer of degree prime to `p`, as an open subgroup of `Kˣ` of
index prime to `p`; the index divides the degree (`index_localNormSubgroup_dvd_degree`). -/
def localNormOpenSubgroupPrimeTo (V : LayerPrimeTo K p) : LocalNormSubgroupsPrimeTo K p :=
  ⟨localNormOpenSubgroup K V.val,
    V.property.coprime_dvd_left <| by
      rw [localNormOpenSubgroup_toSubgroup]
      exact index_localNormSubgroup_dvd_degree V.val⟩

/-- The norm subgroup of a layer of degree prime to `p` is its norm subgroup as a layer. -/
@[simp]
theorem localNormOpenSubgroupPrimeTo_coe (V : LayerPrimeTo K p) :
    (localNormOpenSubgroupPrimeTo p V).val = localNormOpenSubgroup K V.val :=
  (rfl)

variable [CharP 𝓀[K] p]

/-- The layer of the local class field of a norm subgroup of index prime to `p`, as a layer of
degree prime to `p`. -/
abbrev localClassFieldPrimeToResidueCharacteristicLayer (N : LocalNormSubgroupsPrimeTo K p) :
    LayerPrimeTo K p :=
  ⟨(localClassFieldPrimeToResidueCharacteristic p N).val.val,
    (localClassFieldPrimeToResidueCharacteristic p N).property⟩

/-- **Norm subgroups below `N` are the layers below its class field**, in the
prime-to-residue-characteristic range. For a layer `V` of degree prime to the residue
characteristic `p` and an open subgroup `N` of index prime to `p`, the norm subgroup of `V` lies in
`N` exactly when `V` lies in the layer of the class field of `N`. -/
theorem localNormOpenSubgroupPrimeTo_le_iff {V : LayerPrimeTo K p}
    {N : LocalNormSubgroupsPrimeTo K p} :
    localNormOpenSubgroupPrimeTo p V ≤ N ↔
      V ≤ localClassFieldPrimeToResidueCharacteristicLayer p N := by
  rw [← Subtype.coe_le_coe, localNormOpenSubgroupPrimeTo_coe,
    localNormOpenSubgroup_le_iff_localNormSubgroup_le,
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
Galois extension `L/K` of degree prime to the residue characteristic `p` contains the class field
of an open subgroup `N` of index prime to `p` exactly when `N_{L/K}(Lˣ) ≤ N`. -/
theorem classField_localClassFieldPrimeToResidueCharacteristic_le_iff {V : LayerPrimeTo K p}
    {N : LocalNormSubgroupsPrimeTo K p} :
    classField K (localClassFieldPrimeToResidueCharacteristic p N).val.val ≤
        classField K V.val ↔
      localNormSubgroup K V.val ≤ N.val.val.toSubgroup := by
  rw [classField_le_classField_iff, ← localNormOpenSubgroup_le_iff_localNormSubgroup_le,
    ← localNormOpenSubgroupPrimeTo_coe, Subtype.coe_le_coe]
  exact (localNormOpenSubgroupPrimeTo_le_iff p).symm

/-- The norm subgroup of the class field of a subgroup `N` of index prime to `p` is `N`. -/
@[simp]
theorem localNormOpenSubgroupPrimeTo_localClassFieldPrimeToResidueCharacteristicLayer
    (N : LocalNormSubgroupsPrimeTo K p) :
    localNormOpenSubgroupPrimeTo p (localClassFieldPrimeToResidueCharacteristicLayer p N) = N :=
  Subtype.ext <| Subtype.ext <| OpenSubgroup.toSubgroup_injective <|
    (localNormOpenSubgroup_toSubgroup K _).trans
      (localClassFieldPrimeToResidueCharacteristic_normSubgroup p N)

/-- **The prime-to-residue-characteristic norm-subgroup Galois insertion.** -/
def localClassFieldPrimeToResidueCharacteristicGaloisInsertion :
    GaloisInsertion (localNormOpenSubgroupPrimeTo (K := K) p)
      (localClassFieldPrimeToResidueCharacteristicLayer p) :=
  (localClassFieldPrimeToResidueCharacteristic_galoisConnection p).toGaloisInsertion fun N ↦
    (localNormOpenSubgroupPrimeTo_localClassFieldPrimeToResidueCharacteristicLayer p N).ge

/-- **The class field of a norm subgroup is the maximal abelian sublayer**, in the
prime-to-residue-characteristic range: for a layer `V` of degree prime to the residue
characteristic, the layer of the class field of `N_{L/K}(Lˣ)` is the maximal abelian sublayer of
`V`. -/
theorem localClassFieldPrimeToResidueCharacteristic_localNormOpenSubgroupPrimeTo
    (V : LayerPrimeTo K p) :
    (localClassFieldPrimeToResidueCharacteristic p (localNormOpenSubgroupPrimeTo p V)).val.val =
      V.val.maximalAbelianLayer :=
  localClassField_unique (localClassFieldPrimeToResidueCharacteristic p _).val.property
    V.val.isAbelianClassFieldLayer_maximalAbelianLayer
    (by rw [localClassFieldPrimeToResidueCharacteristic_normSubgroup,
      localNormOpenSubgroupPrimeTo_coe, localNormOpenSubgroup_toSubgroup,
      localNormSubgroup_maximalAbelianLayer])

end PrimeTo

end TauCeti.ClassFieldTheory
