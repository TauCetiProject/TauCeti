/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Noetherian
import TauCeti.Topology.Algebra.Ring.Subring
import Mathlib.RingTheory.Localization.Submodule

/-!
# Noetherian type for Tate rings

A Tate ring with a noetherian ring of definition is strongly noetherian. Indeed, a sufficiently
large positive power of a pseudouniformiser belongs to any open subring, and inverting it
recovers the ambient ring. Thus a Tate ring with a noetherian open subring is noetherian.
Apply this to the completed rings of definition of the restricted power-series algebras.

Consequently, on Tate rings the two alternatives defining noetherian type reduce to strong
noetherianness. Neither completeness nor Hausdorffness of the original ring is needed: the
power-series algebras in the definition of strong noetherianness are separated completions.

## References

* T. Wedhorn, *Adic Spaces*, §6.7, Remark 6.37(3).
-/

public section

open Topology

namespace Subring

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [TauCeti.Huber.IsTateRing A]

/-- A Tate ring with a noetherian open subring is noetherian: it is a localization of that
subring at a positive power of a pseudouniformiser. No boundedness or completeness is needed. -/
theorem isNoetherianRing_of_isOpen (S : Subring A) [IsNoetherianRing S]
    (hS : IsOpen (S : Set A)) : IsNoetherianRing A := by
  obtain ⟨ϖ, hϖ⟩ := TauCeti.Huber.IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (hϖ.isTopologicallyNilpotent.eventually_mem (hS.mem_nhds S.zero_mem))
  let s : S := ⟨ϖ ^ (n + 1), hn (n + 1) (by omega)⟩
  have : IsLocalization.Away s A := S.isLocalizationAway_of_isOpen hS s
    (hϖ.isTopologicallyNilpotent.pow (Nat.succ_ne_zero n)) (hϖ.isUnit.pow (n + 1))
  exact IsLocalization.isNoetherianRing (Submonoid.powers s) A inferInstance

end Subring

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- A Tate ring with a noetherian ring of definition is strongly noetherian, without any
completeness assumption on the original ring. -/
theorem PairOfDefinition.isStronglyNoetherian (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] : IsStronglyNoetherian A := by
  refine ⟨fun k ↦ ?_⟩
  have := P.isNoetherianRing_weighted_completion_ringOfDefinition
    (isWeightFamily_one_weight (k := k)) (fun _ ↦ Set.finite_singleton 1)
  exact Subring.isNoetherianRing_of_isOpen _
    (P.weighted (isWeightFamily_one_weight (k := k))).completion.isOpen_ringOfDefinition

/-- For a Tate ring, noetherian type implies strong noetherianness. -/
theorem IsNoetherianType.isStronglyNoetherian [hA : IsNoetherianType A] :
    IsStronglyNoetherian A :=
  hA.elim (fun P _ ↦ P.isStronglyNoetherian) (fun _ h ↦ h)

/-- On Tate rings, noetherian type is equivalent to strong noetherianness. -/
@[simp]
theorem isNoetherianType_iff_isStronglyNoetherian :
    IsNoetherianType A ↔ IsStronglyNoetherian A :=
  ⟨fun _ ↦ IsNoetherianType.isStronglyNoetherian, fun _ ↦ inferInstance⟩

end TauCeti.Huber
