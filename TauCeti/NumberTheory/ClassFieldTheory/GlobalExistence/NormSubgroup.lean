/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Open

/-!
# Global norm subgroups

Let `K` be a number field. An open normal subgroup `V` of the absolute Galois group `G_K` cuts out
the finite Galois extension `classField K V` of `K`. This file attaches to `V` its norm subgroup in
the idele class group `C_K`: the norm subgroup of the layer `V ◁ G_K` of the idele-class formation
`globalFormation K`, read on `C_K` through the identification `globalGroundEquiv` of `C_K` with the
ground level. It is the idele-class norm group `N_{E/K}(C_E)` of the class field `E`
(`globalNormSubgroup_eq_range_classField`, `globalNormSubgroup_eq_range`), and of any finite Galois
extension `L/K` whose layer is `V` (`globalNormSubgroup_fixingOpenNormalSubgroup`).

The idele-class norm group is open and of finite index
(`TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap`,
`TauCeti.GlobalNumberFields.finiteIndex_range_ideleClassNormMap`), so global norm subgroups are open
subgroups of finite index of `C_K`, the objects on which the global class-field correspondence is
stated. Transitivity of the formation norm makes the construction monotone in `V`, so it reverses
inclusion of class fields, and the layer `G_K` itself, which cuts out `K`, has norm subgroup `C_K`.

## Main definitions

* `TauCeti.ClassFieldTheory.globalNormSubgroup`: the norm subgroup of `C_K` cut out by an open
  normal subgroup of `G_K`.
* `TauCeti.ClassFieldTheory.globalGroundOrderIso`: subgroups of `C_K` are the subgroups of the
  ground level of the idele-class formation; it carries `globalNormSubgroup K V` to the norm
  subgroup of the layer `V` (`globalGroundOrderIso_globalNormSubgroup`).

## Main results

* `TauCeti.ClassFieldTheory.globalNormSubgroup_eq_range_classField`: it is `N_{E/K}(C_E)` for the
  class field `E = classField K V`.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_eq_range`: the same for any finite Galois
  subextension `E` of `Kˢ/K` given as the fixed field of `V`.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_fixingOpenNormalSubgroup`: the layer of a finite
  Galois extension `L/K` has norm subgroup `N_{L/K}(C_L)`.
* `TauCeti.ClassFieldTheory.isOpen_globalNormSubgroup`: global norm subgroups are open.
* `TauCeti.ClassFieldTheory.finiteIndex_globalNormSubgroup`: global norm subgroups have finite
  index.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_mono`: inclusion of layer subgroups gives inclusion
  of norm subgroups.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_top`: the ground field has norm subgroup `C_K`.
* `TauCeti.ClassFieldTheory.index_globalGroundOrderIso`: the ground-level identification preserves
  the index of an idele-class subgroup.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§2 and 6.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
-/

public noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- **The idele-class norm subgroup cut out by an open normal subgroup** `V` of `G_K`: the norm
subgroup of the layer `V ◁ G_K` of the idele-class formation, read on `C_K` through
`globalGroundEquiv`. It is the idele-class norm group of the class field of `V`
(`globalNormSubgroup_eq_range`). -/
def globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  AddSubgroup.toSubgroup'
    (((NormalLayer.ofOpenNormal V).normSubgroup (globalFormation K)).toAddSubgroup.comap
      ((globalGroundEquiv K).trans
        (NormalLayer.groundEquivOfOpenNormal (globalFormation K) V).toAddEquiv).toAddMonoidHom)

variable {K}

/-- An idele class lies in the global norm subgroup of `V` exactly when, read in the ground level
of the layer `V ◁ G_K`, it lies in the norm subgroup of that layer. -/
theorem mem_globalNormSubgroup_iff {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    {c : IdeleClassGroup (𝓞 K) K} :
    c ∈ globalNormSubgroup K V ↔
      NormalLayer.groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K (.ofMul c)) ∈
        (NormalLayer.ofOpenNormal V).normSubgroup (globalFormation K) :=
  Iff.rfl

/-- **The global norm subgroup of `V` is `N_{E/K}(C_E)`** for any finite Galois subextension `E`
of `Kˢ/K` that is the fixed field of `V`. -/
theorem globalNormSubgroup_eq_range (E : Ω) {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E) :
    globalNormSubgroup K V =
      (GlobalNumberFields.ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →*
        IdeleClassGroup (𝓞 K) K).range := by
  ext c
  rw [mem_globalNormSubgroup_iff, globalGroundEquiv_mem_normSubgroup_iff E hV]

/-- **The global norm subgroup of the layer of `L` is `N_{L/K}(C_L)`** for a finite Galois
extension `L/K`. -/
theorem globalNormSubgroup_fixingOpenNormalSubgroup (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    globalNormSubgroup K (fixingOpenNormalSubgroup K L) =
      (GlobalNumberFields.ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →*
        IdeleClassGroup (𝓞 K) K).range := by
  ext c
  rw [mem_globalNormSubgroup_iff, globalGroundEquiv_mem_layerNormSubgroup_iff]

variable (K) in
/-- **The global norm subgroup of `V` is `N_{E/K}(C_E)` for the class field `E` of `V`.** -/
theorem globalNormSubgroup_eq_range_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    globalNormSubgroup K V =
      (GlobalNumberFields.ideleClassNormMap K (classField K V) :
        IdeleClassGroup (𝓞 (classField K V)) (classField K V) →*
          IdeleClassGroup (𝓞 K) K).range := by
  conv_lhs => rw [← fixingOpenNormalSubgroup_classField V]
  exact globalNormSubgroup_fixingOpenNormalSubgroup (classField K V)

variable (K) in
/-- The global norm subgroup of `V` is normal in the commutative group `C_K`, so the norm quotient
`C_K / N_{E/K}(C_E)` is a group. -/
instance normal_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (globalNormSubgroup K V).Normal := by
  rw [globalNormSubgroup_eq_range_classField]
  infer_instance

/-- An idele class lies in the global norm subgroup of `V` exactly when it is the norm of an idele
class of the class field of `V`. -/
@[simp]
theorem mem_globalNormSubgroup_iff_exists {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    {c : IdeleClassGroup (𝓞 K) K} :
    c ∈ globalNormSubgroup K V ↔
      ∃ d : IdeleClassGroup (𝓞 (classField K V)) (classField K V),
        GlobalNumberFields.ideleClassNormMap K (classField K V) d = c := by
  rw [globalNormSubgroup_eq_range_classField, MonoidHom.mem_range]
  rfl

variable (K) in
/-- **Subgroups of `C_K` are the subgroups of the ground level of the idele-class formation.** The
level of the whole group `G_K` is `C_K`, written additively (`globalGroundEquiv`), so taking
preimages along that identification is an order isomorphism. It carries the global norm subgroups
to the norm subgroups of the idele-class formation (`globalGroundOrderIso_globalNormSubgroup`),
which transports the laws of the norm subgroups of a class formation to `C_K`. -/
def globalGroundOrderIso :
    Subgroup (IdeleClassGroup (𝓞 K) K) ≃o Submodule ℤ ((globalFormation K).level ⊤) :=
  Subgroup.toAddSubgroup.trans <|
    (globalGroundEquiv K).symm.comapAddSubgroup.trans AddSubgroup.toIntSubmodule

/-- An element of the ground level lies in the image of a subgroup `H ≤ C_K` under
`globalGroundOrderIso` exactly when the corresponding idele class lies in `H`. -/
@[simp]
theorem mem_globalGroundOrderIso {H : Subgroup (IdeleClassGroup (𝓞 K) K)}
    {a : (globalFormation K).level ⊤} :
    a ∈ globalGroundOrderIso K H ↔ ((globalGroundEquiv K).symm a).toMul ∈ H :=
  Iff.rfl

variable (K) in
/-- The ground-level order isomorphism preserves the index of every idele-class subgroup. -/
theorem index_globalGroundOrderIso (N : Subgroup (IdeleClassGroup (𝓞 K) K)) :
    (globalGroundOrderIso K N).toAddSubgroup.index = N.index := by
  have : (globalGroundOrderIso K N).toAddSubgroup =
      N.toAddSubgroup.comap (globalGroundEquiv K).symm.toAddMonoidHom := by
    ext a
    exact mem_globalGroundOrderIso
  rw [this, ← Subgroup.index_toAddSubgroup]
  exact AddSubgroup.index_comap_of_surjective _ (globalGroundEquiv K).symm.surjective

variable (K) in
/-- `globalGroundOrderIso` carries the global norm subgroup of `V` to the norm subgroup of the
layer `V ◁ G_K` of the idele-class formation. -/
@[simp]
theorem globalGroundOrderIso_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    globalGroundOrderIso K (globalNormSubgroup K V) = (globalFormation K).normSubgroup V := by
  ext a
  obtain ⟨c, rfl⟩ : ∃ c, globalGroundEquiv K c = a := (globalGroundEquiv K).surjective a
  rw [mem_globalGroundOrderIso, AddEquiv.symm_apply_apply, mem_globalNormSubgroup_iff, ofMul_toMul,
    Formation.mem_normSubgroup]

variable (K) in
/-- **Global norm subgroups are open.** -/
theorem isOpen_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    IsOpen ((globalNormSubgroup K V : Subgroup (IdeleClassGroup (𝓞 K) K)) :
      Set (IdeleClassGroup (𝓞 K) K)) := by
  rw [globalNormSubgroup_eq_range_classField]
  exact GlobalNumberFields.isOpen_range_ideleClassNormMap K (classField K V)

variable (K) in
/-- **Global norm subgroups have finite index.** -/
theorem finiteIndex_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (globalNormSubgroup K V).FiniteIndex := by
  rw [globalNormSubgroup_eq_range_classField]
  exact GlobalNumberFields.finiteIndex_range_ideleClassNormMap K (classField K V)

/-! ### Order properties

Shrinking the layer subgroup `V` enlarges its class field, and a norm from a larger field is a norm
from every intermediate field, so `globalNormSubgroup K` is monotone in `V`. The top layer `G_K`
cuts out `K` itself, whose norm subgroup is all of `C_K`.
-/

variable (K) in
/-- **Global norm subgroups are monotone in the layer subgroup.** If `V ≤ W`, then the class field
of `W` is contained in that of `V`, and every norm from the larger field is a norm from the smaller
field. -/
theorem globalNormSubgroup_mono : Monotone (globalNormSubgroup K) := by
  intro V W h c hc
  apply mem_globalNormSubgroup_iff.2
  exact Formation.mem_normSubgroup.1 ((globalFormation K).normSubgroup_mono h
    (Formation.mem_normSubgroup.2 (mem_globalNormSubgroup_iff.1 hc)))

variable (K) in
/-- **The top layer has the whole idele class group as its norm subgroup.** It cuts out the ground
field itself, whose norm to itself is the identity. This pins the direction of the global
class-field correspondence. -/
@[simp]
theorem globalNormSubgroup_top :
    globalNormSubgroup K (openNormalSubgroupTop (AbsoluteGaloisGroup K)) = ⊤ := by
  apply top_unique
  intro c _
  apply mem_globalNormSubgroup_iff.2
  apply Formation.mem_normSubgroup.1
  rw [Formation.normSubgroup_top]
  exact Submodule.mem_top

end TauCeti.ClassFieldTheory
