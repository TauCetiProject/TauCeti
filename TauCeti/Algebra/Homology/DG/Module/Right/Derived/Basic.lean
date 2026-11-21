/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso

/-!
# The derived category of right DG modules

The derived category of a differential graded algebra is the category of right DG modules
localized at quasi-isomorphisms. We use Mathlib's localization, so its universal property applies
to functors and natural transformations without any choice of resolutions or representatives.
The category is large; no essential smallness or smallness of its morphism types is asserted.

Total cohomology descends to this category, with values in right modules over the cohomology
algebra. Consequently a map of DG modules becomes invertible precisely when it is a
quasi-isomorphism: localization introduces no additional weak equivalences among the original
maps. This file constructs the category and its cohomology functor; a triangulated structure
and computations of derived tensor products require further constructions.

## References

* B. Keller, *Deriving DG categories*, Sections 2--3.
-/

public section

open CategoryTheory

namespace TauCeti.DGRightModuleCat

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

variable (h : IsDGAlgebra 𝒜 d) in
/-- The derived category of right modules over a DG algebra, obtained by inverting
quasi-isomorphisms. Its localization universal property is provided by Mathlib. -/
abbrev DerivedCategory := (quasiIsos.{uR, uA, uM} h).Localization

namespace DerivedCategory

variable (h : IsDGAlgebra 𝒜 d)

/-- The canonical functor from right DG modules to their derived category. -/
abbrev Q : DGRightModuleCat.{uR, uA, uM} h ⥤ DerivedCategory h :=
  (quasiIsos h).Q

/-- Total cohomology on the derived category, retaining the right action of the cohomology
algebra. -/
noncomputable def cohomologyFunctor :
    DerivedCategory.{uR, uA, uM} h ⥤ ModuleCat.{uM} h.Cohomologyᵐᵒᵖ :=
  Localization.Construction.lift DGRightModuleCat.cohomologyFunctor (W := quasiIsos h)
    (fun _ _ f hf ↦ (isQuasiIso_iff_isIso_cohomologyFunctor_map f).mp ((quasiIsos_iff f).mp hf))

/-- Computing derived cohomology on DG modules recovers ordinary total cohomology. -/
@[simp]
theorem Q_comp_cohomologyFunctor :
    Q.{uR, uA, uM} h ⋙ cohomologyFunctor h = DGRightModuleCat.cohomologyFunctor := by
  unfold cohomologyFunctor
  exact Localization.Construction.fac _ _

/-- Derived cohomology lifts ordinary total cohomology along localization. -/
noncomputable instance :
    Localization.Lifting (Q.{uR, uA, uM} h) (quasiIsos h) DGRightModuleCat.cohomologyFunctor
      (cohomologyFunctor h) :=
  ⟨eqToIso (Q_comp_cohomologyFunctor h)⟩

/-- Derived cohomology agrees with ordinary cohomology on DG modules, naturally in the module. -/
noncomputable def cohomologyFunctorFactors :
    Q.{uR, uA, uM} h ⋙ cohomologyFunctor h ≅ DGRightModuleCat.cohomologyFunctor :=
  Localization.Lifting.iso (Q h) (quasiIsos h) _ _

/-- The lifting isomorphism of derived cohomology is `cohomologyFunctorFactors`. -/
@[simp]
theorem liftingIso_cohomologyFunctor :
    Localization.Lifting.iso (Q.{uR, uA, uM} h) (quasiIsos h) DGRightModuleCat.cohomologyFunctor
      (cohomologyFunctor h) = cohomologyFunctorFactors h := (rfl)

/-- The comparison of derived and ordinary cohomology is natural in maps of DG modules. -/
@[reassoc (attr := simp)]
theorem cohomologyFunctorFactors_hom_naturality {M N : DGRightModuleCat.{uR, uA, uM} h}
    (f : M ⟶ N) :
    (cohomologyFunctor h).map ((Q h).map f) ≫ (cohomologyFunctorFactors h).hom.app N =
      (cohomologyFunctorFactors h).hom.app M ≫ DGRightModuleCat.cohomologyFunctor.map f :=
  (cohomologyFunctorFactors h).hom.naturality f

/-- A map of DG right modules becomes an isomorphism in the derived category exactly when
it is a quasi-isomorphism. -/
@[simp]
theorem isIso_Q_map_iff_isQuasiIso {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) :
    IsIso ((Q h).map f) ↔ IsQuasiIso f := by
  constructor
  · intro hf
    have hc : IsIso ((Q h ⋙ cohomologyFunctor h).map f) :=
      Functor.map_isIso (cohomologyFunctor h) ((Q h).map f)
    rw [Q_comp_cohomologyFunctor] at hc
    exact (isQuasiIso_iff_isIso_cohomologyFunctor_map f).mpr hc
  · intro hf
    exact Localization.inverts (Q h) (quasiIsos h) f ((quasiIsos_iff f).mpr hf)

end DerivedCategory

end TauCeti.DGRightModuleCat
