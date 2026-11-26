/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Spec
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Locally free quotients of the differentials of an affine scheme

Let `A` be an algebra over a commutative ring `R`. A surjective `A`-linear map `g : Ω[A⁄R] → A^d`
induces an epimorphism `Ω_{Spec A/R} ⟶ (A^d)~` (`differentialsSpecToTilde`), and `(A^d)~` is the
free sheaf of rank `d`, so `Ω_{Spec A/R}` admits a locally free quotient of rank `d`. This is the
affine global case of the stalk criterion for `HasLocallyFreeQuotientOfDifferentials`. Through
`Spec Γ(X, V) ≅ V`, the same holds on an affine open `V` of a scheme `X` over `Spec R`.

## Main declarations

* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective`: a
  surjective `A`-linear map `Ω[A⁄R] → A^d` gives a locally free quotient of rank `d` of
  `Ω_{Spec A/R}`.
* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective`: a
  surjection `Ω[Γ(X, V)⁄R] → Γ(X, V)^d` on an affine open `V` gives a locally free quotient of
  rank `d` of `Ω_{V/R}`.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

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

/-- **A surjection of the Kähler differentials of an affine open onto a free module gives a
locally free quotient.** For an affine open `V` of a scheme `X` over `Spec R`, with `Γ(X, V)` an
`R`-algebra through the base-ring map, a surjective `Γ(X, V)`-linear map
`Ω[Γ(X, V)⁄R] → Γ(X, V)^d` gives a locally free quotient of rank `d` of `Ω_{V/R}`. -/
theorem hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective {X : Scheme.{u}}
    [X.Over (Spec (.of R))] (V : X.affineOpens) {d : ℕ}
    (g : letI : Algebra R Γ(X, V) :=
        ((X.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
      Ω[Γ(X, V)⁄R] →ₗ[Γ(X, V)] (Fin d → Γ(X, V)))
    (hg : Function.Surjective g) :
    HasLocallyFreeQuotientOfDifferentials R V.val d := by
  let : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  have hSpec := hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective R Γ(X, V) g hg
  have hV : IsAffineOpen V.val := V.property
  have : hV.isoSpec.hom.IsOver (Spec (.of R)) := by
    have h := isOver_fromSpec R X V
    rw [Scheme.Hom.isOver_iff] at h ⊢
    rw [← h, ← Category.assoc, hV.isoSpec_hom_fromSpec, Scheme.Opens.ι_comp_over]
  exact hSpec.of_isOpenImmersion hV.isoSpec.hom

end

end TauCeti.AlgebraicGeometry
