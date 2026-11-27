/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Quotient
public import TauCeti.RingTheory.Ideal.Annihilator

/-!
# Noetherian self-injective commutative rings are artinian

Over a self-injective commutative ring, a finitely generated ideal is its double
annihilator. Consequently, when the ring is noetherian, annihilation reverses and reflects
the order on all ideals. The ascending chain condition therefore gives the descending
chain condition.

For a local ring with finite residue field this also proves that the ring is finite.
Thus finite coefficient duality applies to noetherian self-injective local rings without
an additional finiteness assumption on the ring.

The double-annihilator argument uses the reflexivity of finitely presented modules from
`TauCeti.Algebra.Module.Injective.Bidual`, applied to the quotient by the ideal.
-/

public section

namespace TauCeti

/-- A noetherian self-injective commutative ring is artinian: annihilation converts
ascending chains of ideals into descending chains and conversely. -/
theorem isArtinianRing_of_injective (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Module.Injective R R] : IsArtinianRing R := by
  have hanti : Antitone (fun I : Ideal R ↦ I.annihilator) :=
    fun _ _ h ↦ Submodule.annihilator_mono h
  have hinj : Function.Injective (fun I : Ideal R ↦ I.annihilator) :=
    Function.LeftInverse.injective fun I ↦
      I.annihilator_annihilator_of_fg (IsNoetherian.noetherian _)
  exact (wellFounded_gt.onFun (f := fun I : Ideal R ↦ I.annihilator)).mono
    fun _ _ h ↦ hanti.strictAnti_of_injective hinj h

/-- A noetherian self-injective commutative local ring with finite residue field is
finite. In particular, its finitely generated modules are finite sets. -/
theorem finite_of_injective_of_finite_residueField (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Module.Injective R R]
    [Finite (IsLocalRing.ResidueField R)] : Finite R := by
  have := isArtinianRing_of_injective R
  have : Finite (R ⧸ (⊥ : Ideal R)) :=
    IsLocalRing.finite_quotient_iff.mpr
      (IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient ⊥)
  exact Finite.of_equiv _ (RingEquiv.quotientBot R).toEquiv

end TauCeti
