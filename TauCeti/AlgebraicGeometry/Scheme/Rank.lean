/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.LocallyConstant
public import TauCeti.RingTheory.Spectrum.Prime.Rank.Fiber

/-!
# Affine covers by module rank fibres

The rank fibres of a finitely presented flat module give a finite affine clopen cover of the
coefficient spectrum. Any bound on the stalk ranks makes the coproduct of the rank-factor spectra
isomorphic to the coefficient spectrum, including zero rings for unused ranks.

## References

* The Stacks Project, Tag 00EE, for clopen decompositions and idempotents.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Module

variable (A : Type*) [CommRing A] (Q : Type*) [AddCommGroup Q] [Module A Q]
  [FinitePresentation A Q] [Flat A Q] (d : ℕ)

/-- The canonical morphism from the disjoint union of rank factors to `Spec A`.
It is an isomorphism when `d` bounds the stalk ranks of `Q`. -/
noncomputable def rankSpecCover :
    (∐ fun r : Fin (d + 1) ↦ Spec (.of (rankRing A Q r))) ⟶ Spec (.of A) :=
  LocallyConstant.specCover
    ⟨_, isLocallyConstant_rankAtStalk (R := A) (M := Q)⟩
    ⟨Fin.val, Fin.val_injective⟩

/-- Restriction of the rank-factor cover to a summand is the canonical coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_rankSpecCover (r : Fin (d + 1)) :
    Sigma.ι _ r ≫ rankSpecCover A Q d =
      Spec.map (CommRingCat.ofHom (algebraMap A (rankRing A Q r))) :=
  LocallyConstant.ι_specCover
    ⟨_, isLocallyConstant_rankAtStalk (R := A) (M := Q)⟩
    ⟨Fin.val, Fin.val_injective⟩ r

/-- The canonical rank-factor cover is an isomorphism onto `Spec A`. -/
theorem isIso_rankSpecCover
    (hd : ∀ p : PrimeSpectrum A, rankAtStalk Q p ≤ d) : IsIso (rankSpecCover A Q d) := by
  apply LocallyConstant.isIso_specCover
    ⟨_, isLocallyConstant_rankAtStalk (R := A) (M := Q)⟩
    ⟨Fin.val, Fin.val_injective⟩
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨_, Nat.lt_succ_of_le (hd p)⟩, rfl⟩

end Module
