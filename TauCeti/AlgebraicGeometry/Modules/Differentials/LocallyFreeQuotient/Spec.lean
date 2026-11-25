/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Spec
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# Locally free quotients of the differentials of an affine scheme

Let `A` be an algebra over a commutative ring `R`. A surjective `A`-linear map `g : Ω[A⁄R] → A^d`
induces an epimorphism `Ω_{Spec A/R} ⟶ (A^d)~` (`differentialsSpecToTilde`), and `(A^d)~` is the
free sheaf of rank `d`, so `Ω_{Spec A/R}` admits a locally free quotient of rank `d`. This is the
affine global case of the stalk criterion for `HasLocallyFreeQuotientOfDifferentials`.

## Main declarations

* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective`: a
  surjective `A`-linear map `Ω[A⁄R] → A^d` gives a locally free quotient of rank `d` of
  `Ω_{Spec A/R}`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]

/-- **A surjection of the Kähler differentials onto a free module gives a locally free quotient.**
For an `R`-algebra `A`, a surjective `A`-linear map `Ω[A⁄R] → A^d` induces an epimorphism
`Ω_{Spec A/R} ⟶ (A^d)~` onto the free sheaf of rank `d`. -/
theorem hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective {d : ℕ}
    (g : Ω[A⁄R] →ₗ[A] (Fin d → A)) (hg : Function.Surjective g) :
    HasLocallyFreeQuotientOfDifferentials R (Spec A) d := by
  refine (hasLocallyFreeQuotientOfDifferentials_iff R _ d).mpr
    ⟨FiniteLocallyFreeSheaf.FixedRank.free _ d, ?_⟩
  rw [FiniteLocallyFreeSheaf.FixedRank.free_obj]
  exact ⟨differentialsSpecToTilde R A g ≫ (FiniteLocallyFreeSheaf.tildePiIsoFree A d).hom,
    epi_comp' (epi_differentialsSpecToTilde R A hg) inferInstance⟩

end

end TauCeti.AlgebraicGeometry
