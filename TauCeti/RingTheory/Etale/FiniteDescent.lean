/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.RingHom.Finite

/-!
# Finite étale algebras under faithfully flat base change

For a pushout square of commutative rings `S' = R' ⊗[R] S` in which `R'` is faithfully flat over
`R`, the algebra `S` is finite étale over `R` if and only if `S'` is finite étale over `R'`. One
direction is stability of finite and étale ring maps under base change; the other is their
descent along faithfully flat ring maps, `RingHom.Finite.codescendsAlong_faithfullyFlat` and
`RingHom.Etale.codescendsAlong_faithfullyFlat`. Thus finite étaleness of an algebra may be checked
after a faithfully flat extension of the base, for instance after completing a Noetherian local
ring.

## Main results

* `Algebra.IsPushout.finite_and_etale_iff_of_faithfullyFlat`: across a pushout square whose base
  extension is faithfully flat, finite étaleness holds on one side if and only if it holds on the
  other.
-/

public section

universe u

namespace Algebra.IsPushout

variable {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
  [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S']

/-- For a pushout square `S' = R' ⊗[R] S` with `R'` faithfully flat over `R`, the algebra `S` is
finite étale over `R` if and only if `S'` is finite étale over `R'`. -/
theorem finite_and_etale_iff_of_faithfullyFlat [Module.FaithfullyFlat R R'] :
    (Module.Finite R S ∧ Algebra.Etale R S) ↔ (Module.Finite R' S' ∧ Algebra.Etale R' S') := by
  have hR' : (algebraMap R R').FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›
  simp only [← RingHom.finite_algebraMap, ← RingHom.etale_algebraMap]
  exact ⟨fun h ↦ ⟨RingHom.finite_isStableUnderBaseChange R S R' S' h.1,
      RingHom.Etale.isStableUnderBaseChange R S R' S' h.2⟩,
    fun h ↦ ⟨RingHom.Finite.codescendsAlong_faithfullyFlat hR' h.1,
      RingHom.Etale.codescendsAlong_faithfullyFlat hR' h.2⟩⟩

end Algebra.IsPushout
