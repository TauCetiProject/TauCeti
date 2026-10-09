/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.NumberTheory.LocalField.Norm.Open

import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
import TauCeti.NumberTheory.ClassFieldTheory.Formation.TrivialLayer
import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation
import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# Local norm subgroups

An open normal subgroup `V` of the absolute Galois group of a nonarchimedean local field cuts out
the finite Galois extension `classField K V`. This file attaches to `V` the concrete norm subgroup
`N_{classField K V/K}(classField K V)ˣ` of `Kˣ`, identifies it with the norm subgroup of the local
class formation, and proves its order-theoretic properties.

The topology statement is inherited from the local inverse-function theorem for the field norm;
finite index follows from the valuation--unit decomposition of `Kˣ`. Transitivity of the abstract
formation norm makes the construction monotone in `V`, while norm limitation shows that replacing
`V` by its maximal abelian sublayer does not change the subgroup.

## Main definitions

* `TauCeti.ClassFieldTheory.localNormSubgroup`: the norm subgroup of the class field cut out by an
  open normal subgroup of the absolute Galois group.
* `TauCeti.ClassFieldTheory.localGroundEquiv`: the identification of `Kˣ`, written additively,
  with the ground level of a finite layer of the units formation.

## Main results

* `TauCeti.ClassFieldTheory.isOpen_localNormSubgroup`: local norm subgroups are open.
* `TauCeti.ClassFieldTheory.finiteIndex_localNormSubgroup`: local norm subgroups have finite index.
* `TauCeti.ClassFieldTheory.localNormSubgroup_mono`: inclusion of layer subgroups gives inclusion
  of norm subgroups.
* `TauCeti.ClassFieldTheory.localNormSubgroup_maximalAbelianLayer`: a layer and its maximal
  abelian sublayer have the same norm subgroup.
* `TauCeti.ClassFieldTheory.localNormSubgroup_top`: the ground field has norm subgroup `Kˣ`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.ValuativeRel

section Basic

variable (K : Type*) [Field K]

/-- **The local norm subgroup cut out by an open normal subgroup.** It is the image in `Kˣ` of
the field norm from the finite Galois extension `classField K V`. -/
def localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) : Subgroup Kˣ :=
  normGroup K (classField K V)

/-- The local norm subgroup of `V` is the norm group of the class field `classField K V`. -/
theorem localNormSubgroup_def (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    localNormSubgroup K V = normGroup K (classField K V) :=
  (rfl)

/-- Membership in a local norm subgroup means being the norm of a nonzero element of the
corresponding class field. -/
@[simp]
theorem mem_localNormSubgroup_iff {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {x : Kˣ} :
    x ∈ localNormSubgroup K V ↔
      ∃ y : (classField K V)ˣ, Algebra.norm K (y : classField K V) = x := by
  rw [localNormSubgroup_def, mem_normGroup_iff]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Local norm subgroups are open.** -/
theorem isOpen_localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    IsOpen ((localNormSubgroup K V : Subgroup Kˣ) : Set Kˣ) := by
  rw [localNormSubgroup_def]
  exact isOpen_normGroup

/-- **Local norm subgroups have finite index.** -/
theorem finiteIndex_localNormSubgroup (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (localNormSubgroup K V).FiniteIndex := by
  rw [localNormSubgroup_def]
  exact finiteIndex_normGroup

end Basic

/-! ### Comparison with the units formation -/

section Formation

variable (K : Type) [Field K]

/-- The ground level of the layer `V ◁ G_K` of the units formation is `Kˣ`, written additively.
This identification moves no element of the separable closure. -/
def localGroundEquiv (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    Additive Kˣ ≃+ (unitsFormation K).level (NormalLayer.ofOpenNormal V).ground :=
  unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) (fixedField_ground_ofOpenNormal K V)

/-- `localGroundEquiv` sends a unit of `K` to the same unit in the coefficient module of the
units formation. -/
@[simp]
theorem localGroundEquiv_apply_coe (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (x : Additive Kˣ) :
    (dsimp% only
      ((localGroundEquiv K V x : (unitsFormation K).level (NormalLayer.ofOpenNormal V).ground) :
        (unitsFormation K).toRep.V)) =
      unitsCoeffEquivUnitsFormation K
        (Additive.ofMul (Units.map (Algebra.ofId K (SeparableClosure K) :
          K →* SeparableClosure K) x.toMul)) :=
  unitsLevelEquiv_apply_coe (Algebra.ofId K (SeparableClosure K))
    (fixedField_ground_ofOpenNormal K V) x

/-- Under `localGroundEquiv`, the concrete local norm subgroup is the norm subgroup of the
corresponding layer of the units formation. -/
theorem localGroundEquiv_mem_normSubgroup_iff
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (x : Kˣ) :
    localGroundEquiv K V (Additive.ofMul x) ∈
        (NormalLayer.ofOpenNormal V).normSubgroup (unitsFormation K) ↔
      x ∈ localNormSubgroup K V := by
  rw [localNormSubgroup_def, ← unitsLevelEquiv_mem_normSubgroup_iff K (classField K V),
    fixingOpenNormalSubgroup_classField]
  rfl

/-- The ground-level identification of the refinement `V ≤ W` is compatible with the two
identifications of `Kˣ` with the ground levels of the layers of `W` and `V`. -/
@[simp]
theorem groundEquiv_localGroundEquiv {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (h : V ≤ W) (x : Additive Kˣ) :
    (LayerRefinement.ofOpenNormal h).groundEquiv (unitsFormation K) (localGroundEquiv K W x) =
      localGroundEquiv K V x := by
  apply Subtype.ext
  rw [LayerRefinement.groundEquiv_apply_coe, localGroundEquiv_apply_coe,
    localGroundEquiv_apply_coe]

/-! ### Order properties -/

/-- **Local norm subgroups are monotone in the layer subgroup.** If `V ≤ W`, then the class field
of `W` is contained in that of `V`, and every norm from the larger field is a norm from the
smaller field. -/
theorem localNormSubgroup_mono : Monotone (localNormSubgroup K) := by
  intro V W h x hx
  let T := LayerRefinement.ofOpenNormal h
  have hx' : localGroundEquiv K V (Additive.ofMul x) ∈
      (NormalLayer.ofOpenNormal V).normSubgroup (unitsFormation K) :=
    (localGroundEquiv_mem_normSubgroup_iff K V x).2 hx
  obtain ⟨y, hy, hyx⟩ := T.normSubgroup_le_map (unitsFormation K) hx'
  have hy' : y = localGroundEquiv K W (Additive.ofMul x) :=
    (T.groundEquiv (unitsFormation K)).injective <|
      hyx.trans (groundEquiv_localGroundEquiv K h (Additive.ofMul x)).symm
  exact (localGroundEquiv_mem_normSubgroup_iff K W x).1 (hy' ▸ hy)

/-- **The top layer has the whole unit group as its norm subgroup.** It cuts out the ground field
itself, whose norm to itself is the identity. This pins the direction of the local class-field
correspondence. -/
@[simp]
theorem localNormSubgroup_top :
    localNormSubgroup K (openNormalSubgroupTop (AbsoluteGaloisGroup K)) = ⊤ := by
  let V := openNormalSubgroupTop (AbsoluteGaloisGroup K)
  have hV : (NormalLayer.ofOpenNormal V).top = (NormalLayer.ofOpenNormal V).ground := by
    rw [NormalLayer.top_ofOpenNormal, NormalLayer.ground_ofOpenNormal]
    apply OpenSubgroup.toSubgroup_injective
    exact openNormalSubgroupTop_toSubgroup _
  apply top_unique
  intro x _
  rw [← localGroundEquiv_mem_normSubgroup_iff K V x,
    (NormalLayer.ofOpenNormal V).normSubgroup_eq_top_of_top_eq_ground (unitsFormation K) hV]
  exact Submodule.mem_top

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Concrete norm limitation.** A finite Galois extension of a nonarchimedean local field and
its maximal abelian subextension have the same norm subgroup. -/
theorem localNormSubgroup_maximalAbelianLayer
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    localNormSubgroup K V.maximalAbelianLayer = localNormSubgroup K V := by
  ext x
  rw [← localGroundEquiv_mem_normSubgroup_iff K V.maximalAbelianLayer x,
    ← localGroundEquiv_mem_normSubgroup_iff K V x]
  let T := LayerRefinement.ofOpenNormal V.le_maximalAbelianLayer
  have hground := groundEquiv_localGroundEquiv K V.le_maximalAbelianLayer (Additive.ofMul x)
  have hlim := (localClassFormation K).normSubgroup_maximalAbelianLayer V
  constructor
  · intro hx
    rw [← hlim]
    exact ⟨_, hx, hground⟩
  · intro hx
    rw [← hlim] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = localGroundEquiv K V.maximalAbelianLayer (Additive.ofMul x) :=
      (T.groundEquiv (unitsFormation K)).injective (hyx.trans hground.symm)
    exact this ▸ hy

end Formation

end TauCeti.ClassFieldTheory
