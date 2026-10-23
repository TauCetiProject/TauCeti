/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.RingTheory.CompositionSeries.Additivity

/-!
# Simple modules occur in the regular module

Every simple left module over an Artinian ring is a quotient of the regular module.
Consequently it occurs among the factors of any composition series of that module.
Thus one finite composition series supplies representatives of all simple modules,
even when the ring is not semisimple.

## References

* Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter I, Section 4.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) [Ring R]
variable (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S]

/-- Every simple module over an Artinian ring occurs with positive multiplicity in the
left regular module. -/
theorem jordanHolderMultiplicity_regular_pos [IsArtinianRing R] :
    0 < jordanHolderMultiplicity R R S := by
  have := IsSimpleModule.nontrivial R S
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  have hle := jordanHolderMultiplicity_le_of_surjective (S := S)
    (LinearMap.toSpanSingleton R S x) (IsSimpleModule.toSpanSingleton_surjective R hx)
  rw [jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S
    (LinearEquiv.refl R S)] at hle
  exact hle

/-- The factors of any exhaustive composition series of a ring's left regular module
include a copy of every simple left module. -/
theorem exists_isCompositionFactorAt_regular (s : CompositionSeries (Submodule R R))
    (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    ∃ i, IsCompositionFactorAt s i S := by
  have ⟨instNoetherian, instArtinian⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_of_exists_compositionSeries ⟨s, hbot, htop⟩)
  exact (jordanHolderMultiplicity_ne_zero_iff s hbot htop S).mp
    (jordanHolderMultiplicity_regular_pos R S).ne'

end TauCeti
