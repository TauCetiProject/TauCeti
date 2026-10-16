/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Maximal ideals over an ideal with Artinian quotient

An Artinian commutative ring has only finitely many maximal ideals
(`IsArtinianRing.setOfPred_isMaximal_finite`). Pulling this back along the quotient map, an ideal
`𝔞` of a commutative ring `R` with Artinian quotient `R ⧸ 𝔞`, for instance with finite quotient,
lies in only finitely many maximal ideals of `R`.

## Main results

* `Ideal.finite_setOfPred_isMaximal_and_le`: an ideal with Artinian quotient ring lies in only
  finitely many maximal ideals.
-/

public section

namespace Ideal

/-- An ideal with Artinian quotient ring, for instance with finite quotient ring, lies in only
finitely many maximal ideals. -/
theorem finite_setOfPred_isMaximal_and_le {R : Type*} [CommRing R] (𝔞 : Ideal R)
    [IsArtinianRing (R ⧸ 𝔞)] : {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite := by
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (R ⧸ 𝔞)).image (comap (Quotient.mk 𝔞))).subset
    fun P ⟨hP, h𝔞P⟩ => ⟨P.map (Quotient.mk 𝔞), ?_, ?_⟩
  · have := hP
    exact IsMaximal.map_of_surjective_of_ker_le Quotient.mk_surjective (by rwa [mk_ker])
  · rw [comap_map_of_surjective _ Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
      sup_eq_left.mpr h𝔞P]

end Ideal
