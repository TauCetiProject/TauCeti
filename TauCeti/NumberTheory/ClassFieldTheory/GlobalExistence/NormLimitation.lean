/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup

import TauCeti.NumberTheory.ClassFieldTheory.Formation.Reciprocity

/-!
# Norm limitation and uniqueness for global norm subgroups

Let `K` be a number field. Global reciprocity, in the form of the global class formation
`globalClassFormation K`, controls which open normal subgroups of `G_K` a global norm subgroup
`N_{L/K}(C_L) ≤ C_K` can see:

* **norm limitation** (`globalNormSubgroup_maximalAbelianLayer`): a finite Galois extension `L/K`
  and its maximal abelian subextension have the same idele-class norm group;
* for an abelian layer `W`, inclusion of norm subgroups is equivalent to inclusion of the layer
  subgroups (`globalNormSubgroup_le_iff_of_isAbelian`);
* **uniqueness** (`globalClassField_unique`): two finite abelian extensions of `K` with the same
  idele-class norm group are equal.

These are the norm-subgroup laws of an arbitrary class formation
(`ClassFormation.normSubgroup_maximalAbelianLayer`,
`ClassFormation.normSubgroup_le_iff_of_isAbelian`) applied to the global class formation and read
on `C_K` through `globalGroundOrderIso`.

## Main results

* `TauCeti.ClassFieldTheory.globalNormSubgroup_maximalAbelianLayer`: norm limitation.
* `TauCeti.ClassFieldTheory.globalNormSubgroup_le_iff_of_isAbelian`: norm subgroups detect the
  order on abelian layers.
* `TauCeti.ClassFieldTheory.globalClassField_unique`: a finite abelian extension is determined by
  its idele-class norm group.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- **Global norm limitation.** A finite Galois extension of a number field and its maximal
abelian subextension have the same idele-class norm group. -/
@[simp]
theorem globalNormSubgroup_maximalAbelianLayer
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    globalNormSubgroup K V.maximalAbelianLayer = globalNormSubgroup K V := by
  apply (globalGroundOrderIso K).injective
  rw [globalGroundOrderIso_globalNormSubgroup, globalGroundOrderIso_globalNormSubgroup,
    (globalClassFormation K).normSubgroup_maximalAbelianLayer]

/-- For a finite abelian layer `W` and any finite layer `V` of a number field, inclusion of global
norm subgroups is equivalent to inclusion of the layer subgroups. On class fields the latter
inclusion is reversed. -/
theorem globalNormSubgroup_le_iff_of_isAbelian
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)} (hW : W.IsAbelianClassFieldLayer) :
    globalNormSubgroup K V ≤ globalNormSubgroup K W ↔ V ≤ W := by
  rw [← (globalGroundOrderIso K).le_iff_le, globalGroundOrderIso_globalNormSubgroup,
    globalGroundOrderIso_globalNormSubgroup]
  exact (globalClassFormation K).normSubgroup_le_iff_of_isAbelian hW

/-- **Uniqueness of finite abelian global class fields.** Two abelian layers of a number field
with the same idele-class norm group are equal. The abelianity hypotheses are essential: by norm
limitation, every layer has the norm group of its maximal abelian sublayer. -/
theorem globalClassField_unique
    {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : V.IsAbelianClassFieldLayer) (hW : W.IsAbelianClassFieldLayer)
    (h : globalNormSubgroup K V = globalNormSubgroup K W) :
    V = W :=
  le_antisymm ((globalNormSubgroup_le_iff_of_isAbelian hW).1 h.le)
    ((globalNormSubgroup_le_iff_of_isAbelian hV).1 h.ge)

end TauCeti.ClassFieldTheory
