/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.AbelianLayer

/-!
# Local norm subgroups determine abelian extensions

For a nonarchimedean local field, inclusion of norm subgroups of finite abelian extensions is
reverse inclusion of the extensions. In particular, two finite abelian extensions inside the
separable closure with the same norm subgroup are equal. These statements require reciprocity,
not the existence theorem for class fields, and hold in both mixed and equal characteristic.

The comparison uses the surjective Artin map of a common abelian refinement, as supplied by
`localAbelianArtinHom` and `localNormSubgroup_eq_comap_ker`. Norm limitation extends the result
to arbitrary finite Galois extensions: their norm subgroups distinguish exactly their maximal
abelian subextensions.

## Main results

* `TauCeti.ClassFieldTheory.localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian`: order
  reflection when the right-hand layer is abelian.
* `TauCeti.ClassFieldTheory.localClassField_unique`: uniqueness of an abelian layer with a given
  norm subgroup.
* `TauCeti.ClassFieldTheory.localNormSubgroup_eq_iff_maximalAbelianLayer_eq`: two finite Galois
  layers have the same norm subgroup exactly when their maximal abelian sublayers agree.

## References

* J.-P. Serre, *Local Fields*, Chapter XI, §3.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {V W : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

/-- Inclusion of local norm subgroups reflects inclusion of layer subgroups when the
right-hand layer is abelian. In terms of fields, the inclusions run in opposite directions. -/
theorem localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian (hW : W.IsAbelianClassFieldLayer) :
    localNormSubgroup K V ≤ localNormSubgroup K W ↔ V ≤ W := by
  rw [← localNormSubgroup_maximalAbelianLayer K V]
  refine ⟨fun h ↦ V.le_maximalAbelianLayer.trans ?_,
    fun h ↦ localNormSubgroup_mono K (OpenNormalSubgroup.maximalAbelianLayer_le h hW)⟩
  have hU := V.isAbelianClassFieldLayer_maximalAbelianLayer.inf hW
  rw [localNormSubgroup_eq_comap_ker hU inf_le_left,
    localNormSubgroup_eq_comap_ker hU inf_le_right,
    Subgroup.comap_le_comap_of_surjective (surjective_localAbelianArtinHom hU)] at h
  exact (LayerRefinement.ker_galHom_ofOpenNormal_le_ker_galHom_ofOpenNormal_iff
    inf_le_left inf_le_right).1 h

/-- Distinct finite abelian extensions of a local field have distinct norm subgroups.
Abelianity is essential: norm limitation identifies every finite Galois extension's norm
subgroup with that of its maximal abelian subextension. -/
theorem localClassField_unique (hV : V.IsAbelianClassFieldLayer)
    (hW : W.IsAbelianClassFieldLayer)
    (h : localNormSubgroup K V = localNormSubgroup K W) : V = W :=
  le_antisymm ((localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian hW).1 h.le)
    ((localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian hV).1 h.ge)

/-- For arbitrary finite Galois layers, inclusion of norm subgroups is equivalent to inclusion
of their maximal abelian layer subgroups. -/
theorem localNormSubgroup_le_iff_maximalAbelianLayer_le :
    localNormSubgroup K V ≤ localNormSubgroup K W ↔
      V.maximalAbelianLayer ≤ W.maximalAbelianLayer := by
  rw [← localNormSubgroup_maximalAbelianLayer K V,
    ← localNormSubgroup_maximalAbelianLayer K W]
  exact localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian
    W.isAbelianClassFieldLayer_maximalAbelianLayer

/-- Two finite Galois layers have the same local norm subgroup exactly when their maximal
abelian sublayers coincide. -/
theorem localNormSubgroup_eq_iff_maximalAbelianLayer_eq :
    localNormSubgroup K V = localNormSubgroup K W ↔
      V.maximalAbelianLayer = W.maximalAbelianLayer := by
  simp only [le_antisymm_iff, localNormSubgroup_le_iff_maximalAbelianLayer_le]

/-- Inclusion of a finite abelian class field in a finite Galois class field is reverse
inclusion of their local norm subgroups. The fields are fixed fields in the separable closure. -/
theorem classField_le_classField_iff_localNormSubgroup_ge_of_isAbelian
    (hW : W.IsAbelianClassFieldLayer) :
    classField K W ≤ classField K V ↔ localNormSubgroup K V ≤ localNormSubgroup K W :=
  (classField_le_classField_iff K V W).trans
    (localNormSubgroup_le_localNormSubgroup_iff_of_isAbelian hW).symm

/-- Two finite abelian class fields inside the separable closure are equal exactly when their
local norm subgroups are equal. -/
theorem classField_eq_classField_iff_localNormSubgroup_eq_of_isAbelian
    (hV : V.IsAbelianClassFieldLayer) (hW : W.IsAbelianClassFieldLayer) :
    classField K V = classField K W ↔ localNormSubgroup K V = localNormSubgroup K W :=
  ⟨fun h ↦ congrArg (localNormSubgroup K) (classField_injective K h),
    fun h ↦ congrArg (classField K) (localClassField_unique hV hW h)⟩

end TauCeti.ClassFieldTheory
