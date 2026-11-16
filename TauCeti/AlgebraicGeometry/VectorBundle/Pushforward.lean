/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Finite flat pushforward of vector bundles

A finite flat morphism locally of finite presentation sends finite locally free sheaves to
finite locally free sheaves, over arbitrary base schemes. On affine opens, this is restriction
of scalars through a finite projective algebra. The source and target need not be Noetherian,
and the ranks need not be constant.

The resulting functor on finite locally free sheaves gives the vector bundles whose determinants
enter norm constructions for line bundles along finite locally free families of divisors.

## References

* The Stacks Project, Tags 00NX (finite projective modules) and 02K9 (finite locally free maps).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Finite flat morphisms locally of finite presentation preserve finite local freeness of
module sheaves, without any Noetherian hypothesis or constant-rank assumption. -/
theorem isFiniteLocallyFree_pushforward (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) := by
  have : M.IsLocallyFree := hM.1
  have : M.IsFinitePresentation := hM.2
  have : M.IsQuasicoherent := inferInstance
  have : ((pushforward f).obj M).IsQuasicoherent := isQuasicoherent_pushforward M f
  refine isFiniteLocallyFree_of_finite_projective_sections _ fun U hU ↦ ?_
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hproj := (M.finite_projective_sections hM hV).2
  let := (f.app U).hom.toAlgebra
  let : Module Γ(X, f ⁻¹ᵁ U) Γ((pushforward f).obj M, U) :=
    inferInstanceAs (Module Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U))
  have : Module.Projective Γ(X, f ⁻¹ᵁ U) Γ((pushforward f).obj M, U) := hproj
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ((pushforward f).obj M, U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    rw [← RingHom.finitePresentation_algebraMap]
    simpa only [RingHom.algebraMap_toAlgebra, ← Hom.app_eq_appLE] using
      f.finitePresentation_appLE hU hV le_rfl
  have : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    rw [← RingHom.flat_algebraMap_iff]
    simpa only [RingHom.algebraMap_toAlgebra, ← Hom.app_eq_appLE] using
      f.flat_appLE hU hV le_rfl
  have : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    .of_finite_of_finitePresentation _ _
  have : Module.Projective Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.Flat.projective_of_finitePresentation
  exact ⟨M.finite_sections_pushforward f U hU, Module.Projective.trans Γ(X, f ⁻¹ᵁ U) _⟩

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Pushforward of finite locally free sheaves along a finite flat morphism locally of finite
presentation, with the usual pushforward on morphisms of module sheaves. -/
noncomputable def pushforward (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  ObjectProperty.lift _ ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f M.obj M.property)

/-- The underlying module sheaf of finite-flat pushforward is the usual pushforward. -/
@[simp]
lemma pushforward_obj_obj (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- On morphisms, finite-flat pushforward agrees with pushforward of module sheaves. -/
@[simp]
lemma pushforward_map_hom (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
