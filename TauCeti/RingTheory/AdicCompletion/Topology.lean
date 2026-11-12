/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Independence of adic completeness from the ideal of definition

Two ideals defining the same topology on a ring give the same notion of separated completeness,
for the ring itself and for every module over it. Each of the two ideals has a power inside the
other, so their adic filtrations are cofinal in each other and adic completeness transfers by
`IsAdicComplete.of_pow_le_of_pow_le`. Callers need only specify the ring topology: no uniform
structure on the ring and no topology on the module is involved.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.1.9.
-/

public section

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I J : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Separated adic completeness of a module depends only on the topology defined by the ideal on
the ring. There is no finite generation hypothesis on either ideal. -/
theorem isAdicComplete_iff_of_isAdic (hI : IsAdic I) (hJ : IsAdic J) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  obtain ⟨-, k, hJI⟩ := hI.isAdic_iff_isOpen_and_exists_pow_le.mp hJ
  obtain ⟨-, l, hIJ⟩ := hJ.isAdic_iff_isOpen_and_exists_pow_le.mp hI
  exact ⟨fun _ ↦ .of_pow_le_of_pow_le hJI hIJ, fun _ ↦ .of_pow_le_of_pow_le hIJ hJI⟩

end IsAdic
