/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Semiperfect
public import TauCeti.RingTheory.Henselian.Semiperfect

/-!
# Krull-Schmidt categories over a Henselian local ring

Let `R` be a Henselian local ring, such as a complete Noetherian local ring. In an
idempotent-complete `R`-linear category whose endomorphism modules are finitely generated over
`R`, every endomorphism ring is a module-finite `R`-algebra, hence semiperfect
(`TauCeti.IsSemiperfectRing.of_henselianRing`). By Krause's criterion the category is
Krull-Schmidt. This is the analogue, over a Henselian local base, of
`TauCeti.isKrullSchmidt_of_module_finite` over a commutative Artinian base. No Noetherian
hypothesis is needed.

## Main results

* `TauCeti.exists_completeOrthogonalIdempotents_isLocalRing_corner_end_of_henselianRing`: if
  `X ⟶ X` is finite over a Henselian local ring, `𝟙 X` is a sum of orthogonal idempotents with
  local corners.
* `TauCeti.isKrullSchmidt_of_module_finite_of_henselianRing`: an idempotent-complete category with
  finite biproducts that is Hom-finite over a Henselian local ring is Krull-Schmidt.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Corollary 4.4.
-/

public section

open CategoryTheory IsLocalRing

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C] (R : Type*) [CommRing R] [IsLocalRing R]
  [HenselianRing R (maximalIdeal R)] [Linear R C]

/-- **Summand decomposition over a Henselian local ring**: if `X ⟶ X` is finite over a Henselian
local ring `R`, then `𝟙 X` is a sum of orthogonal idempotents whose corners are local rings, as
the module-finite `R`-algebra `End X` is semiperfect. -/
theorem exists_completeOrthogonalIdempotents_isLocalRing_corner_end_of_henselianRing (X : C)
    [Module.Finite R (X ⟶ X)] :
    ∃ (n : ℕ) (f : Fin n → End X) (hf : CompleteOrthogonalIdempotents f),
      ∀ i, IsLocalRing (hf.idem i).Corner :=
  have : Module.Finite R (End X) := Module.Finite.equiv End.linearEquiv.symm
  have := IsSemiperfectRing.of_henselianRing R (End X)
  IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner

/-- **Recognition of Krull-Schmidt categories over a Henselian local ring**: an
idempotent-complete category with finite biproducts whose endomorphisms are finite over a
Henselian local ring is Krull-Schmidt. -/
theorem isKrullSchmidt_of_module_finite_of_henselianRing [Limits.HasFiniteBiproducts C]
    [IsIdempotentComplete C] [∀ X : C, Module.Finite R (X ⟶ X)] : IsKrullSchmidt C :=
  isKrullSchmidt_of_isSemiperfectRing_end fun X ↦
    have : Module.Finite R (End X) := Module.Finite.equiv End.linearEquiv.symm
    IsSemiperfectRing.of_henselianRing R (End X)

end TauCeti
