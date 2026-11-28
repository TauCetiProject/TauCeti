/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import Mathlib.Topology.Algebra.Module.Compact
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Range
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.ProcyclicSubgroups
import TauCeti.Topology.Algebra.Ring.UnitPowers

/-!
# Topological generators of cyclotomic images

At an odd prime, the image of the cyclotomic character is procyclic by reduction modulo
prime powers. At `2`, the closed-subgroup criterion for the dyadic units applies. In particular,
a field containing a primitive fourth root of unity has a topologically cyclic image at every
prime. A generator in the image lifts to the absolute Galois group. For each exponent, its
power difference divides the corresponding differences at all Galois elements.

The cyclotomic generator is the input used in `New.Selmer.exists_cyclotomicChar_pow_sub_one_dvd`
in `grh/src/New/Congruences/FirstOrder/DenominatorBound.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti

/-- The image of a cyclotomic character has a topological generator at any odd prime.
At `2` the same holds if the image omits `-1` or contains no nonidentity unit congruent
to `1` modulo `4`. The generator is the image of a Galois element, and for every exponent
its power difference divides the corresponding power difference of every other image. -/
theorem exists_topologicalClosure_zpowers_eq_range_cyclotomicCharacter (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K]
    (h₂ : p = 2 → (-1 : ℤ_[p]ˣ) ∉ (localCyclotomicCharacter p K).range ∨
      (localCyclotomicCharacter p K).range ⊓ unitsPrincipal p 2 = ⊥) :
    ∃ g : Field.absoluteGaloisGroup K,
      (Subgroup.zpowers (localCyclotomicCharacter p K g)).topologicalClosure =
          (localCyclotomicCharacter p K).range ∧
        ∀ (a : ℕ) (g' : Field.absoluteGaloisGroup K),
          (localCyclotomicCharacter p K g : ℤ_[p]) ^ a - 1 ∣
            (localCyclotomicCharacter p K g' : ℤ_[p]) ^ a - 1 := by
  have hclosed := isClosed_range_localCyclotomicCharacter p K
  have hgen : ∃ u : ℤ_[p]ˣ,
      (Subgroup.zpowers u).topologicalClosure = (localCyclotomicCharacter p K).range := by
    by_cases hp : p = 2
    · subst p
      exact (exists_topologicalClosure_zpowers_eq_iff_of_isClosed hclosed).2 (h₂ rfl)
    · exact exists_topologicalClosure_zpowers_eq_of_isClosed_of_ne_two hp hclosed
  obtain ⟨u, hu⟩ := hgen
  obtain ⟨g, rfl⟩ : u ∈ (localCyclotomicCharacter p K).range :=
    hu ▸ Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers u)
  refine ⟨g, hu, fun a g' ↦ pow_sub_one_dvd_of_mem_topologicalClosure_zpowers ?_ a ?_⟩
  · rw [hu]
    exact ⟨g', rfl⟩
  · exact (Ideal.isCompact_of_fg (Submodule.fg_span_singleton _)).isClosed

end TauCeti
