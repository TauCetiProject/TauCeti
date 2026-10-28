/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation

import TauCeti.NumberTheory.ClassFieldTheory.Formation.Reciprocity

/-!
# Upward closure and descent of global norm subgroups

Let `K` be a number field. This file proves the two inputs of global existence that come from
global reciprocity alone, as opposed to the Kummer theory of `S`-units:

* **upward closure** (`exists_abelianLayer_globalNormSubgroup_eq_of_le`): a subgroup of `C_K`
  containing the norm subgroup of a finite Galois extension is the norm subgroup of a finite
  **abelian** extension. More generally, a subgroup containing the idele-class norm group
  `N_{M/K}(C_M)` of any finite extension `M/K` is such a norm subgroup
  (`exists_abelianLayer_globalNormSubgroup_eq_of_range_ideleClassNormMap_le`);
* **descent along a finite extension**
  (`exists_abelianLayer_globalNormSubgroup_eq_of_comap_ideleClassNorm`): if `L/K` is a finite
  extension and the preimage of `N ≤ C_K` under the idele-class norm `N_{L/K} : C_L → C_K`
  contains a norm subgroup over `L`, then `N` is the norm subgroup of a finite abelian extension
  of `K`.

Upward closure is the upward closure of the norm subgroups of any class formation
(`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_le`), applied to the global class
formation and read on `C_K` through `globalGroundOrderIso`. Descent follows by composing norms in
the tower `M/L/K`: `N_{M/K}(C_M) = N_{L/K}(N_{M/L}(C_M)) ≤ N`.

In the proof of global existence by induction on the index, descent is applied to `L = K(ζ_p)` to
reduce to fields containing the `p`-th roots of unity, where the Kummer case applies.

## Main results

All in the namespace `TauCeti.ClassFieldTheory`:

* `exists_abelianLayer_globalNormSubgroup_eq_of_le`: upward closure of global norm subgroups.
* `exists_abelianLayer_globalNormSubgroup_eq_of_range_ideleClassNormMap_le`: upward closure from
  the idele-class norm group of any finite extension.
* `exists_abelianLayer_globalNormSubgroup_eq_of_comap_ideleClassNorm`: descent of norm subgroups
  along a finite extension.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §9 (Lemmas 9.1 and 9.4).
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

open NormalLayer GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- **Upward closure of global norm subgroups.** For a number field `K`, a subgroup of `C_K`
containing the norm subgroup of the finite Galois extension cut out by `V` is the norm subgroup of
a finite abelian extension. -/
theorem exists_abelianLayer_globalNormSubgroup_eq_of_le
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    (h : globalNormSubgroup K V ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ globalNormSubgroup K W = N := by
  rw [← (globalGroundOrderIso K).le_iff_le, globalGroundOrderIso_globalNormSubgroup] at h
  obtain ⟨W, hW, -, hWN⟩ := (globalClassFormation K).exists_abelianLayer_normSubgroup_eq_of_le h
  refine ⟨W, hW, (globalGroundOrderIso K).injective ?_⟩
  rw [globalGroundOrderIso_globalNormSubgroup, hWN]

/-- **Upward closure from a finite extension.** For a number field `K`, a subgroup of `C_K`
containing the idele-class norm group `N_{M/K}(C_M)` of a finite extension `M/K` is the norm
subgroup of a finite abelian extension. The extension `M` need not be Galois, nor lie in the
separable closure: the normal closure of an embedding of `M` into `Kˢ` is a finite Galois extension
with a smaller norm group. -/
theorem exists_abelianLayer_globalNormSubgroup_eq_of_range_ideleClassNormMap_le
    {M : Type*} [Field M] [NumberField M] [Algebra K M] {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    (h : (ideleClassNormMap K M : IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 K) K).range ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ globalNormSubgroup K W = N := by
  -- the normal closure of `M` in `Kˢ` is the class field of some `V`
  let E := IntermediateField.normalClosure K M (SeparableClosure K)
  obtain ⟨V, hV⟩ := (exists_classField_eq_iff E).2 ⟨inferInstance, inferInstance⟩
  refine exists_abelianLayer_globalNormSubgroup_eq_of_le (V := V) (le_trans ?_ h)
  rw [globalNormSubgroup_eq_range_classField]
  exact range_ideleClassNormMap_le_of_algHom ((IntermediateField.equivOfEq hV.symm).toAlgHom.comp
    ((normalClosure.algHomEquiv K M (SeparableClosure K)).symm IsSepClosed.lift))

/-- **Descent of norm subgroups along a finite extension.** Let `L/K` be an extension of number
fields and `N ≤ C_K`. If the preimage of `N` under the idele-class norm `N_{L/K} : C_L → C_K`
contains the norm subgroup of the layer `W` of `G_L` (in particular, if it is that norm subgroup),
then `N` is the norm subgroup of a finite abelian extension of `K`. -/
theorem exists_abelianLayer_globalNormSubgroup_eq_of_comap_ideleClassNorm
    {L : Type} [Field L] [NumberField L] [Algebra K L] {N : Subgroup (IdeleClassGroup (𝓞 K) K)}
    {W : OpenNormalSubgroup (AbsoluteGaloisGroup L)}
    (h : globalNormSubgroup L W ≤
      N.comap (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K)) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      V.IsAbelianClassFieldLayer ∧ globalNormSubgroup K V = N := by
  -- the class field `M` of `W` is a finite extension of `K` through `L`
  let M := classField L W
  let _ : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine exists_abelianLayer_globalNormSubgroup_eq_of_range_ideleClassNormMap_le (M := M) ?_
  rintro _ ⟨y, rfl⟩
  have hy : ideleClassNormMap L M y ∈ globalNormSubgroup L W :=
    mem_globalNormSubgroup_iff_exists.2 ⟨y, rfl⟩
  have hcomp : ideleClassNormMap K L (ideleClassNormMap L M y) = ideleClassNormMap K M y :=
    DFunLike.congr_fun (ideleClassNormMap_comp K L M) y
  simpa only [Subgroup.mem_comap, MonoidHom.coe_ofClass, hcomp] using h hy

end TauCeti.ClassFieldTheory
