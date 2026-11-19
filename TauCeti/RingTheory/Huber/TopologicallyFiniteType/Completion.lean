/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Homeomorph
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

import TauCeti.RingTheory.AdicCompletion.Topology

/-!
# A completion criterion for topologically finite type adic algebras

Over a noetherian `I`-adic ring `A`, a topological `A`-algebra `B` is strictly topologically
of finite type if and only if its canonical map to its adic completion is a homeomorphism
and its first infinitesimal quotient `B / I²B` is of finite type over `A / I²`.
This is the completion formulation of EGA I, Ch. 0, 7.5.5, (b) ⇔ (c).

The completion is Mathlib's compatible-family carrier `AdicCompletion (I B) B`, equipped
here with the adic topology of the extended ideal. The comparison is the canonical algebra
map, so it preserves the given `A`-algebra structures. The source ring `A` need not be
complete, and no choice of uniformity on either ring is required. Comparison of this
topology with the initial topology of the quotient projections is a separate result.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.5.5.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsNoetherianRing A] {I : Ideal A}
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]

/-- **The completion criterion for strictly topologically finite type algebras.** The
canonical map to the adic completion is a homeomorphism, and the first infinitesimal quotient
is of finite type. The completion has the adic topology of the extended ideal. -/
theorem isStrictlyTopologicallyFiniteType_algebraMap_iff_isHomeomorph_adicCompletion
    (hI : IsAdic I) :
    IsStrictlyTopologicallyFiniteType (algebraMap A B) ↔
      (@IsHomeomorph B (AdicCompletion (I.map (algebraMap A B)) B) _
        ((I.map (algebraMap A B)).map
          (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B))).adicTopology
        (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B))) ∧
      Algebra.FiniteType (A ⧸ I ^ 2) (B ⧸ (I ^ 2).map (algebraMap A B)) := by
  rw [AdicCompletion.isHomeomorph_algebraMap_iff]
  have hI₂ : IsAdic (I ^ 2) := is_ideal_adic_pow hI (by decide)
  constructor
  · intro h
    exact ⟨⟨h.isAdic hI (IsNoetherian.noetherian I), h.isAdicComplete hI⟩,
      h.finiteType_quotient hI₂ (IsNoetherian.noetherian _)⟩
  · rintro ⟨⟨hB, hc⟩, hft⟩
    have hB₂ : IsAdic ((I ^ 2).map (algebraMap A B)) := by
      rw [Ideal.map_pow]
      exact is_ideal_adic_pow hB (by decide)
    have : IsAdicComplete ((I ^ 2).map (algebraMap A B)) B :=
      (hB.isAdicComplete_iff_of_isAdic hB₂).mp hc
    have := hft
    exact isStrictlyTopologicallyFiniteType_of_isAdic hI₂
      (IsNoetherian.noetherian _) hB₂

end TauCeti.Huber
