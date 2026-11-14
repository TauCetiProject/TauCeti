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
noncomputable def cohomology : DerivedCategory.{uR, uA, uM} h ⥤ ModuleCat.{uM} h.Cohomologyᵐᵒᵖ :=
  Localization.Construction.lift cohomologyFunctor (W := quasiIsos h) (by
    intro M N f hf
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (DGRightModuleHom.isQuasiIso_iff f).mp ((quasiIsos_iff f).mp hf))

/-- Computing derived cohomology on DG modules recovers ordinary total cohomology. -/
@[simp]
theorem Q_comp_cohomology : Q.{uR, uA, uM} h ⋙ cohomology h = cohomologyFunctor := by
  unfold cohomology
  exact Localization.Construction.fac _ _

/-- A map of DG right modules becomes an isomorphism in the derived category exactly when
it is a quasi-isomorphism. -/
@[simp]
theorem isIso_map_Q_iff {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) :
    IsIso ((Q h).map f) ↔ IsQuasiIso f := by
  constructor
  · intro hf
    have := hf
    have hc : IsIso (((Q h) ⋙ cohomology h).map f) := by
      dsimp only [Functor.comp_map]
      infer_instance
    rw [Q_comp_cohomology] at hc
    exact (DGRightModuleHom.isQuasiIso_iff f).mpr
      ((ConcreteCategory.isIso_iff_bijective _).mp hc)
  · intro hf
    exact Localization.inverts (Q h) (quasiIsos h) f ((quasiIsos_iff f).mpr hf)

end DerivedCategory

end TauCeti.DGRightModuleCat
