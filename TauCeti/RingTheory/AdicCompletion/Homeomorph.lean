/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# When the canonical map to an adic completion is a homeomorphism

The canonical map from a topological ring `R` to `AdicCompletion I R`, equipped with the
adic topology of the extended ideal, is a homeomorphism exactly when `R` is `I`-adic and
`I`-adically separated and complete. No finite generation hypothesis is needed for this
characterisation. It permits a canonical completion comparison to recover both the topology
and algebraic completeness of the original ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R)

/-- The canonical map to the adic completion, with the adic topology of the extended ideal,
is a homeomorphism precisely when the source has the adic topology and is adically complete.
The topology of the completion is specified explicitly, without choosing a uniformity on `R`.
-/
theorem isHomeomorph_algebraMap_iff :
    @IsHomeomorph R (AdicCompletion I R) _
      (I.map (algebraMap R (AdicCompletion I R))).adicTopology
      (algebraMap R (AdicCompletion I R)) ↔ IsAdic I ∧ IsAdicComplete I R := by
  let : TopologicalSpace (AdicCompletion I R) :=
    (I.map (algebraMap R (AdicCompletion I R))).adicTopology
  constructor
  · intro h
    let e := RingEquiv.ofBijective (algebraMap R (AdicCompletion I R)) h.bijective
    have ht := IsAdic.comap (I := I.map (algebraMap R (AdicCompletion I R))) rfl
      e h.isInducing
    have he : (I.map (algebraMap R (AdicCompletion I R))).comap e = I :=
      I.comap_map_of_bijective _ h.bijective
    rw [he] at ht
    exact ⟨ht, of_bijective_iff.mp h.bijective⟩
  · rintro ⟨hI, hc⟩
    let : IsAdicComplete I R := hc
    -- Transport the two adic topologies along the canonical algebra equivalence.
    rw [hI]
    let : WithIdeal R := ⟨I⟩
    let : TopologicalSpace R := I.adicTopology
    let : WithIdeal (AdicCompletion I R) :=
      ⟨I.map (algebraMap R (AdicCompletion I R))⟩
    exact (WithIdeal.uniformEquiv (ofAlgEquiv I).toRingEquiv rfl).toHomeomorph.isHomeomorph

end AdicCompletion
