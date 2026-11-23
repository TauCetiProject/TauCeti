/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.DegreeZero
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Flasque
import TauCeti.Topology.Sheaves.SupportedCohomology.Resolution

/-!
# Algebraic local cohomology and sheaf cohomology with closed supports

Let `R` be a Noetherian commutative ring, `I` an ideal of `R`, and `M` an `R`-module with
associated quasi-coherent sheaf `M~` on `Spec R`. Write `V(I)`
(`AlgebraicGeometry.Spec.zeroLocusClosed I`) for the closed vanishing locus of `I` in `Spec R`.

The functor `tildeSheafFunctor R : M ↦ M~` is exact and sends injective `R`-modules over a
Noetherian ring to flasque sheaves (`isFlasque_tilde_of_injective`), while flasque sheaves are
adapted to `supportedSubmoduleSectionsFunctor`
(`shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque`). Right deriving the degree-zero
comparison `tildeCompSupportedSubmoduleSectionsTopIso`
(`TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.DegreeZero`) via
`Functor.compRightDerivedIsoOfResolution` identifies
`tildeSheafFunctor R ⋙
  (supportedSubmoduleSectionsFunctor (Spec.zeroLocusClosed I) ⊤).rightDerived q`
with `I.primaryComponentFunctor.rightDerived q` (`tildeCompRightDerivedSupportedSectionsIso`,
Stacks 0955), and combining with `rightDerivedSupportedSubmoduleSectionsIso` and
`localCohomology.isoRightDerivedPrimaryComponent` gives the natural isomorphism with algebraic local
cohomology (`tildeCompSupportedModuleHTopIsoLocalCohomology`,
`supportedModuleHTopTildeLinearEquivLocalCohomology`, Stacks 0A6T):
`H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)`.

## Main definitions

* `TauCeti.AlgebraicGeometry.tildeCompRightDerivedSupportedSectionsIso` (Stacks 0955): the natural
  isomorphism `(R^q Γ_{V(I)}(Spec R, -)) ∘ (~) ≅ R^q Γ_I` over a Noetherian ring `R`.
* `TauCeti.AlgebraicGeometry.tildeCompSupportedModuleHTopIsoLocalCohomology` and
  `TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology` (Stacks 0A6T):
  the comparison `H^q_{V(I)}(Spec R, M~) ≃ₗ[R] H^q_I(M)` over a Noetherian ring `R`.

## Main results

* `TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology_naturality`:
  naturality of the module-level comparison with respect to `R`-module morphisms.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [The Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, §3.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open CategoryTheory.Sheaf

section Comparison

variable {R : CommRingCat.{u}}

/-- **Derived supported global sections agree with derived `I`-power torsion (Stacks 0955).**
Over a Noetherian ring `R`, composing `M ↦ M~` with the `q`-th right derived functor of
`Γ_{V(I)}(Spec R, -)` is naturally isomorphic to `(R^q Γ_I)`. -/
@[stacks 0955]
def tildeCompRightDerivedSupportedSectionsIso [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        (supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).rightDerived q ≅
      I.primaryComponentFunctor.{u}.rightDerived q :=
  Functor.compRightDerivedIsoOfResolution
    (supportedSubmoduleSectionsFunctor (R := R)
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤)
    (isFlasque (Spec R) (ModuleCat.{u} R))
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _))
    (fun _ hT h₁ h₂ ↦ by
      have := isFlasque_iff.mp h₁
      have := isFlasque_iff.mp h₂
      exact isFlasque_iff.mpr hT.isFlasque_X₃_of_isFlasque)
    (fun _ hT h₁ _ ↦ by
      have := isFlasque_iff.mp h₁
      exact shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque _ ⊤ hT)
    (tildeSheafFunctor R)
    I.primaryComponentFunctor.{u}
    (tildeCompSupportedSubmoduleSectionsTopIso (IsNoetherian.noetherian I))
    (fun M _ ↦ isFlasque_iff.mpr (isFlasque_modulesSpecToSheaf_tilde_of_injective M))
    q

/-- **Algebraic local cohomology agrees with sheaf cohomology with supports (Stacks 0A6T).**
Over a Noetherian ring `R`, the functor `M ↦ H^q_{V(I)}(Spec R, M~)` is naturally isomorphic to
`localCohomology I q`. -/
@[stacks 0A6T]
def tildeCompSupportedModuleHTopIsoLocalCohomology [IsNoetherianRing R] (I : Ideal R) (q : ℕ) :
    tildeSheafFunctor R ⋙
        supportedModuleHPresheafFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) q ⋙
        (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat.{u} R)).obj (op ⊤) ≅
      localCohomology I q :=
  (Functor.isoWhiskerLeft (tildeSheafFunctor R)
    (rightDerivedSupportedSubmoduleSectionsIso
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q)).symm ≪≫
    tildeCompRightDerivedSupportedSectionsIso I q ≪≫
    (localCohomology.isoRightDerivedPrimaryComponent I q).symm

/-- **Module-level local cohomology comparison (Stacks 0A6T).** Over a Noetherian ring `R`,
`H^q_{V(I)}(Spec R, M~)` is `R`-linearly equivalent to `H^q_I(M)`. -/
@[stacks 0A6T]
def supportedModuleHTopTildeLinearEquivLocalCohomology [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (q : ℕ) :
    (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q ≃ₗ[R]
      (localCohomology I q).obj M :=
  ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).app M).toLinearEquiv

/-- `supportedModuleHTopTildeLinearEquivLocalCohomology` commutes with morphisms `f : M ⟶ N` of
`R`-modules. -/
lemma supportedModuleHTopTildeLinearEquivLocalCohomology_naturality [IsNoetherianRing R]
    (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) (q : ℕ)
    (x : (modulesSpecToSheaf.obj (tilde M)).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ q) :
    (localCohomology I q).map f
        (supportedModuleHTopTildeLinearEquivLocalCohomology I M q x) =
      supportedModuleHTopTildeLinearEquivLocalCohomology I N q
        (((supportedModuleHPresheafFunctor
          (Spec.zeroLocusClosed (R := R) (I : Set R)) q).map
            ((tildeSheafFunctor R).map f)).app (op ⊤) x) :=
  (ConcreteCategory.congr_hom
    ((tildeCompSupportedModuleHTopIsoLocalCohomology I q).hom.naturality f) x).symm

end Comparison

end TauCeti.AlgebraicGeometry
