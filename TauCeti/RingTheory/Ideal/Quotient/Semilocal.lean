/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Maximal ideals over an ideal with semilocal quotient

The maximal ideals of a commutative ring `R` containing an ideal `𝔞` are the pullbacks of the
maximal ideals of `R ⧸ 𝔞`. So if the quotient `R ⧸ 𝔞` is semilocal (has only finitely many maximal
ideals), then `𝔞` lies in only finitely many maximal ideals of `R`. This applies for instance
when `R ⧸ 𝔞` is Artinian (`IsArtinianRing.setOfPred_isMaximal_finite`), in particular when it is
finite.

## Main results

* `Ideal.finite_setOfPred_isMaximal_and_le`: an ideal with semilocal quotient ring lies in only
  finitely many maximal ideals.
-/

public section

namespace Ideal

/-- An ideal with semilocal quotient ring, for instance with Artinian or finite quotient ring, lies
in only finitely many maximal ideals. -/
theorem finite_setOfPred_isMaximal_and_le {R : Type*} [CommRing R] (𝔞 : Ideal R)
    [Finite (MaximalSpectrum (R ⧸ 𝔞))] : {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite :=
  (Set.finite_range fun Q : MaximalSpectrum (R ⧸ 𝔞) => Q.asIdeal.comap (Quotient.mk 𝔞)).subset
    fun P ⟨_, h𝔞P⟩ => ⟨⟨P.map (Quotient.mk 𝔞), IsMaximal.map_of_surjective_of_ker_le
      Quotient.mk_surjective (mk_ker.trans_le h𝔞P)⟩, comap_map_mk h𝔞P⟩

end Ideal
