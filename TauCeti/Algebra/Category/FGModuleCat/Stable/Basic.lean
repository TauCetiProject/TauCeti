/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Stable categories of finitely generated modules

For a right Noetherian ring `A`, this file defines the stable category of finitely generated
right `A`-modules as the additive quotient by maps factoring through projective modules. When `A` is
a finite-dimensional algebra over a field and is self-injective on both sides, the canonical
exact structure on `FGModuleCat Aᵐᵒᵖ` is Frobenius. In that case this is the usual stable module
category: projective and injective modules coincide, and precisely they become zero in the
quotient.

The construction is stated first for a right Noetherian ring because the quotient itself does not
use self-injectivity. The finite-dimensional self-injective hypotheses enter only in the results
identifying the killed objects with injectives.  This is the `stmod-A` carrier used by stable
module and hypersurface comparison theorems.

## Main definitions

* `FGModuleCat.stableModuleCategory A` is the stable category of finitely generated
  right `A`-modules.
* `FGModuleCat.stableModuleFunctor A` is the quotient functor.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Ragnar-Olaf Buchweitz, *Maximal Cohen--Macaulay Modules and Tate Cohomology*, Section 4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w u

namespace FGModuleCat

variable (A : Type u) [Ring A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The **stable module category** of finitely generated right `A`-modules: maps factoring through a
projective module are killed.  For a finite-dimensional self-injective algebra, this is the
usual category `stmod-A`. -/
noncomputable abbrev stableModuleCategory : Type (u + 1) :=
  (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).ProjectiveStableCategory

/-- The quotient functor from finitely generated right `A`-modules to their stable category. -/
noncomputable abbrev stableModuleFunctor : FGModuleCat.{u} Aᵐᵒᵖ ⥤ stableModuleCategory A :=
  (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).projectiveStableFunctor

variable {A}

/-- A finitely generated module is zero in the stable module category exactly when it is
projective. -/
theorem _root_.FGModuleCat.isZero_stableModuleFunctor_obj_iff (X : FGModuleCat.{u} Aᵐᵒᵖ) :
    IsZero ((stableModuleFunctor A).obj X) ↔ Projective X := by
  rw [ExactStructure.isZero_projectiveStableFunctor_obj_iff,
    ExactStructure.abelian_isProjective_iff]

/-- A map of finitely generated modules vanishes in the stable module category exactly when it
factors through a projective module. -/
theorem stableModuleFunctor_map_eq_zero_iff {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) :
    (stableModuleFunctor A).map f = 0 ↔
      ∃ (P : FGModuleCat.{u} Aᵐᵒᵖ), Projective P ∧ ∃ (i : X ⟶ P) (p : P ⟶ Y), f = i ≫ p := by
  rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff]
  constructor
  · intro hf
    obtain ⟨P, hP, i, p, rfl⟩ :=
      (ObjectProperty.factorsThrough_iff
        (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).isProjective f).mp hf
    exact ⟨P, (ExactStructure.abelian_isProjective_iff P).mp hP, i, p, rfl⟩
  · rintro ⟨P, hP, i, p, rfl⟩
    exact (ObjectProperty.factorsThrough_iff
      (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).isProjective _).mpr
      ⟨P, (ExactStructure.abelian_isProjective_iff P).mpr hP, i, p, rfl⟩

/-- Two maps of finitely generated modules are equal in the stable module category exactly when
their difference factors through a projective module. -/
theorem stableModuleFunctor_map_eq_iff {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f g : X ⟶ Y) :
    (stableModuleFunctor A).map f = (stableModuleFunctor A).map g ↔
      ∃ (P : FGModuleCat.{u} Aᵐᵒᵖ), Projective P ∧ ∃ (i : X ⟶ P) (p : P ⟶ Y), f - g = i ≫ p := by
  rw [← sub_eq_zero, ← Functor.map_sub]
  exact stableModuleFunctor_map_eq_zero_iff (f - g)

variable (k : Type w) [Field k] [Algebra k A] [FiniteDimensional k A]

include k in
/-- For a finite-dimensional algebra self-injective on both sides, an object is zero in `stmod-A`
exactly when it is injective. -/
theorem _root_.FGModuleCat.isZero_stableModuleFunctor_obj_iff_injective
    (hr : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ)
    (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ) (X : FGModuleCat.{u} Aᵐᵒᵖ) :
    IsZero ((stableModuleFunctor A).obj X) ↔ Injective X := by
  rw [FGModuleCat.isZero_stableModuleFunctor_obj_iff,
    FGModuleCat.projective_iff_injective_of_moduleInjective_self k hr hl]

include k in
/-- Under the self-injectivity hypotheses, a map is zero in `stmod-A` exactly when it factors
through an injective module. -/
theorem stableModuleFunctor_map_eq_zero_iff_injective
    (hr : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ)
    (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)
    {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) :
    (stableModuleFunctor A).map f = 0 ↔
      ∃ (I : FGModuleCat.{u} Aᵐᵒᵖ), Injective I ∧ ∃ (i : X ⟶ I) (p : I ⟶ Y), f = i ≫ p := by
  rw [stableModuleFunctor_map_eq_zero_iff]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩
    exact ⟨P, (FGModuleCat.projective_iff_injective_of_moduleInjective_self k hr hl P).mp hP,
      i, p, rfl⟩
  · rintro ⟨I, hI, i, p, rfl⟩
    exact ⟨I, (FGModuleCat.projective_iff_injective_of_moduleInjective_self k hr hl I).mpr hI,
      i, p, rfl⟩

end FGModuleCat

end TauCeti
