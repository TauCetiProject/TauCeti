/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Scalar endomorphisms on the homology of module presheaves

A chain endomorphism acting by a scalar on a term of a complex of module presheaves
acts by the same scalar on its homology in that degree, object by object. This lets
one identify scalar actions on derived functors computed using such complexes.
The result is `HomologicalComplex.homologyMap_app_eq_smul`.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe v w w' u

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {ι : Type*} {c : ComplexShape ι}

/-- A chain endomorphism acting by a scalar on the degree-`n` term at `U` acts by
that scalar on the degree-`n` homology at `U`. No condition in other degrees is needed. -/
lemma homologyMap_app_eq_smul (K : HomologicalComplex (PresheafOfModules.{w'} R) c)
    (φ : K ⟶ K) (n : ι) (U : Cᵒᵖ) (r : R.obj U)
    (hφ : ∀ x, (φ.f n).app U x = r • x) (x : (K.homology n).obj U) :
    (homologyMap φ n).app U x = r • x := by
  let E := PresheafOfModules.evaluation R U
  have hπ : Function.Surjective ((K.homologyπ n).app U) :=
    (ModuleCat.epi_iff_surjective (E.map (K.homologyπ n))).mp inferInstance
  have hi : Function.Injective ((K.iCycles n).app U) :=
    (ModuleCat.mono_iff_injective (E.map (K.iCycles n))).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ x
  have hc : (cyclesMap φ n).app U z = r • z := hi (by
    have h : (cyclesMap φ n).app U ≫ (K.iCycles n).app U =
        (K.iCycles n).app U ≫ (φ.f n).app U :=
      congrArg (fun g ↦ g.app U) (cyclesMap_i φ n)
    have hz := congrArg (fun g ↦ g z) h
    simpa only [ModuleCat.comp_apply, hφ, map_smul] using hz)
  have h : (K.homologyπ n).app U ≫ (homologyMap φ n).app U =
      (cyclesMap φ n).app U ≫ (K.homologyπ n).app U :=
    congrArg (fun g ↦ g.app U) (homologyπ_naturality φ n)
  have hz := congrArg (fun g ↦ g z) h
  simpa only [ModuleCat.comp_apply, hc, map_smul] using hz

end HomologicalComplex
