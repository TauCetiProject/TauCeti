/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete

/-!
# Open immersions are locally of finite type

An open immersion with adic source is locally of finite type. In particular, the identity
of every adic space is locally of finite type.

This gives the open-subspace morphisms used in refining local finite-type charts.
The target may be any pre-adic space.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

open Huber ValuationSpectrum

universe u

variable {X Y : PreAdicSpace.{u}}

/-- The identity of every adic space is locally of finite type. -/
theorem locallyOfFiniteType_id (hX : isAdic X) : LocallyOfFiniteType (𝟙 X) := by
  refine LocallyOfFiniteType.of_iSup_eq_top (fun U : X.affinoidOpens ↦ U.1) ?_ ?_
  · simpa only [sSup_eq_iSup'] using
      (isLocallyAffinoid_iff_sSup_eq_top X).mp hX.isLocallyAffinoid
  intro U
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ :=
    (isAffinoid_iff_exists_complete _).mp U.2
  have hs : isSheafy (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ObjectProperty.prop_of_iso isSheafy e (isSheafy_restrict U.1.isOpenEmbedding hX.isSheafy)
  have hs' := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp hs
  have hid := locallyOfFiniteType_id_presentationLimitPreAdicSpace (T := S) P hP hs'
  have hpre := MorphismProperty.RespectsIso.precomp (@LocallyOfFiniteType) e.hom _ hid
  have hpost := MorphismProperty.RespectsIso.postcomp (@LocallyOfFiniteType) e.inv _ hpre
  have hU : LocallyOfFiniteType (𝟙 (X.restrict U.1.isOpenEmbedding)) := by
    simpa using hpost
  simpa using hU.comp_of_isOpenImmersion (X.ofRestrict U.1.isOpenEmbedding)

/-- An open immersion with adic source is locally of finite type, with arbitrary pre-adic
target. -/
theorem locallyOfFiniteType_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (hX : isAdic X) : LocallyOfFiniteType f := by
  simpa using (locallyOfFiniteType_id hX).comp_of_isOpenImmersion f

end TauCeti.PreAdicSpace
