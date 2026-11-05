/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Completion
public import TauCeti.RingTheory.Dagger.FaithfullyFlat
import TauCeti.RingTheory.RingHom.FaithfullyFlat
import TauCeti.RingTheory.RingHom.Quotient

/-!
# Faithful flatness of dagger completion

The completion map `A → Â` of a dagger algebra is faithfully flat, and hence injective.
For a presentation `A ≃ Wₙ/I`, its completion is `Tₙ/ITₙ`: the map between these quotients
is the base change of the faithfully flat inclusion `Wₙ → Tₙ`. This allows descent from
completed affinoid algebras to dagger algebras, without assuming reducedness of either ring.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), Theorem 1.7 (1).
-/

public section

namespace TauCeti.Dagger

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The completion map of a dagger algebra is faithfully flat. -/
theorem faithfullyFlat_toCompletion : (toCompletion K A).toRingHom.FaithfullyFlat := by
  have h := RingHom.FaithfullyFlat.isStableUnderBaseChange.quotientMap
    RingHom.FaithfullyFlat.respectsIso
    (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K).toRingHom
    (RingHom.ker (presentation K A)) washnitzerAlgebra.faithfullyFlat_toTate
  let e := (Ideal.quotientKerAlgEquivOfSurjective (presentation_surjective K A)).symm
  let q := Ideal.quotientMap
    ((RingHom.ker (presentation K A)).map
      (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K))
    (washnitzerAlgebra.toTate (Fin (presentationDim K A)) K).toRingHom Ideal.le_comap_map
  have he : e.toRingHom.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.bijective
  -- `Ideal.map` uses the same underlying function for an algebra hom and its ring hom;
  -- the coercion equalities are `AlgHom.toRingHom_eq_coe` and `Ideal.map_coe`.
  have hq : q.FaithfullyFlat := h
  have hmap : (toCompletion K A).toRingHom = q.comp e.toRingHom := by
    ext a
    obtain ⟨f, rfl⟩ := presentation_surjective K A a
    simp [q, e]
  rw [hmap]
  exact he.comp hq

/-- A dagger algebra embeds in its affinoid completion, including when it has nilpotents. -/
theorem toCompletion_injective : Function.Injective (toCompletion K A) :=
  faithfullyFlat_toCompletion.injective

end TauCeti.Dagger
