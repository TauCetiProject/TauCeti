/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.AbelianLayer

/-!
# Upward closure of local norm subgroups

Let `K` be a nonarchimedean local field. A subgroup `N ≤ Kˣ` containing the norm subgroup of a
finite Galois extension is itself the norm subgroup of a finite **abelian** extension
(`exists_abelianLayer_localNormSubgroup_eq_of_le`). This is the reciprocity half of local
existence: once every open subgroup of finite index is known to contain some norm subgroup, it is
a norm subgroup.

The proof is by local reciprocity alone: it is the upward closure of the norm subgroups of any
class formation (`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_le`), applied to the local
class formation and read on `Kˣ` through `localGroundOrderIso`.

## Main results

* `TauCeti.ClassFieldTheory.exists_abelianLayer_localNormSubgroup_eq_of_le`: a subgroup of `Kˣ`
  containing a local norm subgroup is the norm subgroup of an abelian layer.
* `TauCeti.ClassFieldTheory.exists_abelianLayer_localNormSubgroup_eq_of_normGroup_le`: the same
  for a subgroup containing the norm group of any finite separable extension.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Upward closure of local norm subgroups.** For a nonarchimedean local field `K`, a subgroup
of `Kˣ` containing the norm subgroup of the finite Galois extension cut out by `V` is the norm
subgroup of a finite abelian extension. -/
theorem exists_abelianLayer_localNormSubgroup_eq_of_le
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)} {N : Subgroup Kˣ}
    (h : localNormSubgroup K V ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ localNormSubgroup K W = N := by
  rw [← (localGroundOrderIso K).le_iff_le, localGroundOrderIso_localNormSubgroup] at h
  obtain ⟨W, hW, -, hWN⟩ := (localClassFormation K).exists_abelianLayer_normSubgroup_eq_of_le h
  refine ⟨W, hW, (localGroundOrderIso K).injective ?_⟩
  rw [localGroundOrderIso_localNormSubgroup, hWN]

/-- **Upward closure from a finite separable extension.** For a nonarchimedean local field `K`, a
subgroup of `Kˣ` containing the norm group `N_{M/K}(Mˣ)` of a finite separable extension `M/K`
is the norm subgroup of a finite abelian extension. The extension `M` need not be Galois, nor lie
in the separable closure: the normal closure of an embedding of `M` into `Kˢ` is a finite Galois
extension with a smaller norm group. -/
theorem exists_abelianLayer_localNormSubgroup_eq_of_normGroup_le {M : Type*} [Field M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] {N : Subgroup Kˣ}
    (h : normGroup K M ≤ N) :
    ∃ W : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      W.IsAbelianClassFieldLayer ∧ localNormSubgroup K W = N := by
  -- the normal closure of `M` in `Kˢ` is the class field of some `V`
  let E := IntermediateField.normalClosure K M (SeparableClosure K)
  obtain ⟨V, hV⟩ := (exists_classField_eq_iff E).2 ⟨inferInstance, inferInstance⟩
  refine exists_abelianLayer_localNormSubgroup_eq_of_le (V := V) (le_trans ?_ h)
  rw [localNormSubgroup_def]
  exact AlgHom.normGroup_le_normGroup ((IntermediateField.equivOfEq hV.symm).toAlgHom.comp
    ((normalClosure.algHomEquiv K M (SeparableClosure K)).symm IsSepClosed.lift))

end TauCeti.ClassFieldTheory
