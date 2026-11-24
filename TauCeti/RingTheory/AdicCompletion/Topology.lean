/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Pow
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic
public import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Adic topology and adic completeness

Two ideals defining the same topology on a ring give the same notion of separated completeness,
for the ring itself and for every module over it (`IsAdic.isAdicComplete_iff_of_isAdic`). Each of
the two ideals has a power inside the other, so their adic filtrations are cofinal in each other
and adic completeness transfers by `IsAdicComplete.of_pow_le_of_pow_le`. Callers need only specify
the ring topology: no uniform structure on the ring and no topology on the module is involved.

In an `I`-adically complete ring carrying the `I`-adic topology, `I` is open and contained in the
Jacobson radical, so the topological nilradical also lies in the Jacobson radical
(`IsAdic.topologicalNilradical_le_jacobson`).

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

/-- In an `I`-adically complete ring whose topology is `I`-adic, the topological nilradical lies in
the Jacobson radical. -/
theorem topologicalNilradical_le_jacobson [IsLinearTopology R R] (hI : IsAdic I)
    [IsAdicComplete I R] : topologicalNilradical R ≤ Ring.jacobson R := by
  rw [← Ideal.jacobson_bot]
  refine topologicalNilradical_le_jacobson_bot (by simpa using hI.isOpen_pow 1) ?_
  rw [Ideal.jacobson_bot]
  exact IsAdicComplete.le_jacobson I

end IsAdic
