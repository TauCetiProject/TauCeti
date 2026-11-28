/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.AdicCompletion.Flat.Basic
import TauCeti.RingTheory.AdicCompletion.LocalRing

/-!
# Flatness of the completion of a local algebra along an extended maximal ideal

Let `R` be a Noetherian local ring and let `S` be a flat local `R`-algebra satisfying
`(maximalIdeal R).map (algebraMap R S) = maximalIdeal S`, without assuming that `S` itself is
Noetherian. Since `S ⧸ maximalIdeal S` is a field, hence Noetherian,
`TauCeti.AdicCompletion.flat_of_map_eq` (in `TauCeti/RingTheory/AdicCompletion/Flat/Basic.lean`)
shows that `AdicCompletion (maximalIdeal S) S` is flat over `R`, and combining this with
`TauCeti.AdicCompletion.isLocalHom_algebraMap_base_of_map_maximalIdeal_eq` (in
`TauCeti/RingTheory/AdicCompletion/LocalRing.lean`) shows that it is faithfully flat over `R`.

This applies both to the completed pointed étale colimit in
`TauCeti/RingTheory/StrictHenselization/Noetherian.lean`
(`TauCeti.StrictHenselization.isNoetherianRing_algebra_iff`) and to local extensions with
arbitrary residue field extensions (*ÉGA III*, Chap. 0, 10.3.1), where `S` may have infinite
transcendence or inseparable residue degree.

## Main results

* `TauCeti.AdicCompletion.flat_of_map_maximalIdeal_eq`: `AdicCompletion (maximalIdeal S) S` is flat
  over `R`.
* `TauCeti.AdicCompletion.faithfullyFlat_of_map_maximalIdeal_eq`:
  `AdicCompletion (maximalIdeal S) S` is faithfully flat over `R`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.3 (the local criterion for flatness).
* [Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK).
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique III*, Chapitre 0,
  Proposition 10.3.1.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]

/-- If `R` is a Noetherian local ring and `S` is a flat local `R`-algebra with
`(maximalIdeal R).map (algebraMap R S) = maximalIdeal S`, then the completion
`AdicCompletion (maximalIdeal S) S` is flat over `R`, without assuming `S` is Noetherian. -/
theorem flat_of_map_maximalIdeal_eq [IsNoetherianRing R] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Module.Flat R (_root_.AdicCompletion (maximalIdeal S) S) := by
  let _ := Ideal.Quotient.field (maximalIdeal S)
  exact flat_of_map_eq h

/-- Under the hypotheses of `TauCeti.AdicCompletion.flat_of_map_maximalIdeal_eq`, the completion
`AdicCompletion (maximalIdeal S) S` is faithfully flat over `R`. -/
theorem faithfullyFlat_of_map_maximalIdeal_eq [IsNoetherianRing R] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Module.FaithfullyFlat R (_root_.AdicCompletion (maximalIdeal S) S) := by
  have hR : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  have := _root_.AdicCompletion.isLocalRing_of_fg (h ▸ hR.map (algebraMap R S))
  have := isLocalHom_algebraMap_base_of_map_maximalIdeal_eq hR h
  have := flat_of_map_maximalIdeal_eq h
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end TauCeti.AdicCompletion
