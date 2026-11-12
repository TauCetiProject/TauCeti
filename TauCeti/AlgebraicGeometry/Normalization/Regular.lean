/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Normalization in a field, and resolution of curves

Let `K` be a field and `f : Spec K ⟶ Y` a quasi-compact quasi-separated morphism. Over an affine
open `U ⊆ Y` the relative normalization `f.normalization` of `Y` in `Spec K` is the spectrum of
the integral closure of `Γ(Y, U)` in `Γ(Spec K, f ⁻¹ U)`, which is either `K` or zero. An
integral closure in a field is an integrally closed domain, so `f.normalization` is a normal
scheme.

The main case is the normalization of an integral scheme `Y` in its function field, along
`Spec k(Y) ⟶ Y`. When `Y` is locally Noetherian of dimension at most one and this normalization is
finite over `Y`, it is again locally Noetherian of dimension at most one, so its local rings are
fields or discrete valuation rings and it is a regular scheme. This is the regularity half of the
resolution of curves by normalization. The finiteness hypothesis carries the Japanese/Nagata
input; for one-dimensional `Y` it is equivalent to the existence of a resolution of
singularities (Stacks, Lemma 54.15.1 (0BI4)).

## Main results

* `TauCeti.AlgebraicGeometry.isNormalScheme_normalization_of_field`: the normalization of a
  scheme in the spectrum of a field is normal.
* `TauCeti.AlgebraicGeometry.isRegular_normalization_of_field`: the normalization of a locally
  Noetherian scheme of dimension at most one in the spectrum of a field is regular when it is
  finite over the scheme.
* `TauCeti.AlgebraicGeometry.isRegular_normalization_fromSpecStalk_genericPoint`: resolution of
  curves, regularity half. The normalization of an integral locally Noetherian scheme of
  dimension at most one in its function field is regular when it is finite over the scheme.

## References

* [Stacks Project, Lemma 33.41.1](https://stacks.math.columbia.edu/tag/0C45).
* [Stacks Project, Lemma 54.15.1](https://stacks.math.columbia.edu/tag/0BI4).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {Y : Scheme.{u}}

/-- The normalization of a scheme `Y` in the spectrum of a field `K`, along a quasi-compact
quasi-separated morphism `f : Spec K ⟶ Y`, is a normal scheme: its sections over the preimage of
an affine open of `Y` are an integral closure in `K`, or zero. -/
instance isNormalScheme_normalization_of_field {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsNormalScheme f.normalization := by
  refine isNormalScheme_iff_forall_exists_affineOpens.mpr fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.fromNormalization x))
      isOpen_univ
  refine ⟨⟨_, hU.preimage f.fromNormalization⟩, hxU, ?_⟩
  let := (f.app U).hom.toAlgebra
  let e := (f.normalizationObjIso hU).commRingCatIsoToRingEquiv
  by_cases htop : f ⁻¹ᵁ U = ⊤
  · -- The sections of `Spec K` over everything are `K`, so the sections of the normalization
    -- over the preimage of `U` are an integral closure in a field.
    let eK : Γ(Spec (.of K), f ⁻¹ᵁ U) ≃+* K :=
      ((Spec (.of K)).presheaf.mapIso (eqToIso htop.symm).op ≪≫
        Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
    have : IsDomain Γ(Spec (.of K), f ⁻¹ᵁ U) := eK.toMulEquiv.isDomain _
    have : IsIntegrallyClosed Γ(Spec (.of K), f ⁻¹ᵁ U) := .of_equiv eK.symm
    have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(Spec (.of K), f ⁻¹ᵁ U)) :=
      .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ Γ(Spec (.of K), f ⁻¹ᵁ U)
    have : IsDomain Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) := e.toMulEquiv.isDomain _
    have : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) := .of_equiv e.symm
    exact (isNormalScheme_Spec_iff _).mpr this
  · -- Otherwise the preimage of `U` is empty, the sections vanish and there is nothing to check.
    have hbot : f ⁻¹ᵁ U = ⊥ :=
      eq_bot_iff.mpr fun z hz ↦ htop (top_le_iff.mp fun w _ ↦ Subsingleton.elim z w ▸ hz)
    have : Subsingleton Γ(Spec (.of K), f ⁻¹ᵁ U) := by
      rw [hbot]
      infer_instance
    have : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
      e.injective.subsingleton
    exact (isNormalScheme_Spec_iff_forall_localization _).mpr fun p hp ↦
      absurd (Subsingleton.elim p ⊤) hp.ne_top

/-- The normalization of a locally Noetherian scheme `Y` of dimension at most one in the spectrum
of a field, along `f : Spec K ⟶ Y`, is a regular scheme provided it is finite over `Y`: it is
normal, locally Noetherian and of dimension at most one, so its local rings are fields or discrete
valuation rings. -/
theorem isRegular_normalization_of_field [IsLocallyNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1) {K : Type u} [Field K] (f : Spec (.of K) ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsFinite f.fromNormalization] :
    IsRegular f.normalization :=
  have := LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  .of_isNormalScheme_of_topologicalKrullDim_le_one
    (f.fromNormalization.topologicalKrullDim_le.trans hY)

/-- **Resolution of curves: regularity of the normalization.** Let `Y` be an integral locally
Noetherian scheme of dimension at most one, and suppose that the normalization of `Y` in its
function field, along `Spec k(Y) ⟶ Y`, is finite over `Y`. Then this normalization is a regular
scheme. -/
theorem isRegular_normalization_fromSpecStalk_genericPoint [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : topologicalKrullDim Y ≤ 1)
    [IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization] :
    IsRegular (Y.fromSpecStalk (genericPoint Y)).normalization :=
  isRegular_normalization_of_field hY (Y.fromSpecStalk (genericPoint Y))

end TauCeti.AlgebraicGeometry
