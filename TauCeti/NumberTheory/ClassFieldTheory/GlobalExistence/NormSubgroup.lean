/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Open

import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
import TauCeti.NumberTheory.ClassFieldTheory.Formation.TrivialLayer

/-!
# Global norm subgroups

Let `K` be a number field. An open normal subgroup `V` of the absolute Galois group `G_K` cuts out
the finite Galois extension `classField K V` of `K`. This file attaches to `V` its norm subgroup in
the idele class group `C_K`: the norm subgroup of the layer `V ◁ G_K` of the idele-class formation
`globalFormation K`, read on `C_K` through the identification `globalGroundEquiv` of `C_K` with the
ground level. It is the idele-class norm group `N_{E/K}(C_E)` of the class field `E`
(`globalNormSubgroup_eq_range`), and of any finite Galois extension `L/K` whose layer is `V`
(`globalNormSubgroup_fixingOpenNormalSubgroup`).

The idele-class norm group is open and of finite index
(`TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap`,
`TauCeti.GlobalNumberFields.finiteIndex_range_ideleClassNormMap`), so global norm subgroups are open
subgroups of finite index of `C_K`, the objects on which the global class-field correspondence is
stated. Transitivity of the formation norm makes the construction monotone in `V`, so it reverses
inclusion of class fields, and the layer `G_K` itself, which cuts out `K`, has norm subgroup `C_K`.

## Main definitions

* `TauCeti.ClassFieldTheory.globalNormSubgroup`: the norm subgroup of `C_K` cut out by an open
  normal subgroup of `G_K`.

## Main results

* `TauCeti.ClassFieldTheory.globalNormSubgroup_eq_range`: it is `N_{E/K}(C_E)` for the class field
  `E` of `V`.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_fixingOpenNormalSubgroup`: the layer of a finite
  Galois extension `L/K` has norm subgroup `N_{L/K}(C_L)`.
* `TauCeti.ClassFieldTheory.isOpen_globalNormSubgroup`: global norm subgroups are open.
* `TauCeti.ClassFieldTheory.finiteIndex_globalNormSubgroup`: global norm subgroups have finite
  index.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_mono`: inclusion of layer subgroups gives inclusion
  of norm subgroups.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_top`: the ground field has norm subgroup `C_K`.

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

/-- Every open normal subgroup `V` of `G_K` is the top subgroup of a layer whose fixed field is a
finite Galois subextension of `Kˢ/K`, namely the class field of `V`. -/
private theorem exists_fixedField_top_ofOpenNormal_eq
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    ∃ E : Ω, fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E :=
  ⟨⟨classField K V⟩, IntermediateField.ext fun x ↦ by
    rw [NormalLayer.top_ofOpenNormal, mem_fixedField_iff]
    exact mem_classField.symm⟩

variable (K) in
/-- **Global norm subgroups are open.** -/
theorem isOpen_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    IsOpen ((globalNormSubgroup K V : Subgroup (IdeleClassGroup (𝓞 K) K)) :
      Set (IdeleClassGroup (𝓞 K) K)) := by
  obtain ⟨E, hE⟩ := exists_fixedField_top_ofOpenNormal_eq V
  rw [globalNormSubgroup_eq_range E hE]
  exact GlobalNumberFields.isOpen_range_ideleClassNormMap K E

variable (K) in
/-- **Global norm subgroups have finite index.** -/
theorem finiteIndex_globalNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (globalNormSubgroup K V).FiniteIndex := by
  obtain ⟨E, hE⟩ := exists_fixedField_top_ofOpenNormal_eq V
  rw [globalNormSubgroup_eq_range E hE]
  exact GlobalNumberFields.finiteIndex_range_ideleClassNormMap K E

/-! ### Order properties -/

/-- The ground-level identification of the refinement `V ≤ W` is compatible with the two
identifications of `C_K` with the ground levels of the layers of `W` and `V`. -/
private theorem groundEquiv_groundEquivOfOpenNormal
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)} (h : V ≤ W)
    (c : Additive (IdeleClassGroup (𝓞 K) K)) :
    (LayerRefinement.ofOpenNormal h).groundEquiv (globalFormation K)
        (NormalLayer.groundEquivOfOpenNormal (globalFormation K) W (globalGroundEquiv K c)) =
      NormalLayer.groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K c) := by
  apply Subtype.ext
  rw [LayerRefinement.groundEquiv_apply_coe, NormalLayer.groundEquivOfOpenNormal_apply_coe,
    NormalLayer.groundEquivOfOpenNormal_apply_coe]

variable (K) in
/-- **Global norm subgroups are monotone in the layer subgroup.** If `V ≤ W`, then the class field
of `W` is contained in that of `V`, and every norm from the larger field is a norm from the smaller
field. -/
theorem globalNormSubgroup_mono : Monotone (globalNormSubgroup K) := by
  intro V W h c hc
  let T := LayerRefinement.ofOpenNormal h
  obtain ⟨y, hy, hyc⟩ := T.normSubgroup_le_map (globalFormation K) (mem_globalNormSubgroup_iff.1 hc)
  have hy' : y = NormalLayer.groundEquivOfOpenNormal (globalFormation K) W
      (globalGroundEquiv K (.ofMul c)) :=
    (T.groundEquiv (globalFormation K)).injective <|
      hyc.trans (groundEquiv_groundEquivOfOpenNormal h (.ofMul c)).symm
  exact mem_globalNormSubgroup_iff.2 (hy' ▸ hy)

variable (K) in
/-- **The top layer has the whole idele class group as its norm subgroup.** It cuts out the ground
field itself, whose norm to itself is the identity. This pins the direction of the global
class-field correspondence. -/
@[simp]
theorem globalNormSubgroup_top :
    globalNormSubgroup K (openNormalSubgroupTop (AbsoluteGaloisGroup K)) = ⊤ := by
  let V := openNormalSubgroupTop (AbsoluteGaloisGroup K)
  have hV : (NormalLayer.ofOpenNormal V).top = (NormalLayer.ofOpenNormal V).ground := by
    rw [NormalLayer.top_ofOpenNormal, NormalLayer.ground_ofOpenNormal]
    apply OpenSubgroup.toSubgroup_injective
    exact openNormalSubgroupTop_toSubgroup _
  apply top_unique
  intro c _
  rw [mem_globalNormSubgroup_iff,
    (NormalLayer.ofOpenNormal V).normSubgroup_eq_top_of_top_eq_ground (globalFormation K) hV]
  exact Submodule.mem_top

end TauCeti.ClassFieldTheory
