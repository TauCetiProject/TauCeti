/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Algebra.Category.FGModuleCat.Basic

/-!
# Homology and the forgetful functor from `FGModuleCat`

This file records the comparison between taking homology in `FGModuleCat` and taking homology
after forgetting to `ModuleCat`.  It lets invariants of homology objects, such as finrank, be
transported between the two categories for Euler-characteristic computations.

Conversely, a homological complex of modules whose terms are finitely generated lifts to a complex
in `FGModuleCat` (`FGModuleCat.liftHomologicalComplex`), which recovers the original complex after
forgetting (`FGModuleCat.liftHomologicalComplexIso`).
-/

public section

open CategoryTheory

universe u v

namespace HomologicalComplex

variable {k : Type u} [DivisionRing k]

/-- The comparison between homology after forgetting an `FGModuleCat` cochain complex and the
underlying module of its homology. -/
noncomputable def homologyForgetIso (K : CochainComplex (FGModuleCat.{v} k) ℤ) (n : ℤ) :
    (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K).homology n ≅
      (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).obj (K.homology n) := by
  let i := n - 1
  let j := n
  let l := n + 1
  have hij : i + 1 = j := by dsimp [i, j]; omega
  have hjl : j + 1 = l := by dsimp [j, l]
  exact HomologicalComplex.homologyIsoSc'
      (((forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapHomologicalComplex _).obj K) i j l
      ((ComplexShape.up ℤ).prev_eq' hij) ((ComplexShape.up ℤ).next_eq' hjl) ≪≫
    (K.sc' i j l).mapHomologyIso
      (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)) ≪≫
    (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).mapIso
      (K.homologyIsoSc' i j l
        ((ComplexShape.up ℤ).prev_eq' hij) ((ComplexShape.up ℤ).next_eq' hjl)).symm

end HomologicalComplex

namespace FGModuleCat

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (hK : ∀ i, Module.Finite R (K.X i))

/-- A homological complex of modules with finitely generated terms, as a complex in
`FGModuleCat R`. Its body is exposed, like Mathlib's constructor `CochainComplex.of`, so that its
terms and differentials are definitionally those of `K`. -/
@[expose] def liftHomologicalComplex : HomologicalComplex (FGModuleCat.{v} R) c where
  X i := ⟨K.X i, hK i⟩
  d i j := ObjectProperty.homMk (K.d i j)
  shape i j hij := ObjectProperty.hom_ext _ (K.shape i j hij)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (K.d_comp_d i j k)

/-- The underlying module of a term of `liftHomologicalComplex K hK` is the term of `K`. -/
@[simp]
lemma liftHomologicalComplex_X_obj (i : ι) : ((liftHomologicalComplex K hK).X i).obj = K.X i :=
  rfl

/-- The underlying morphism of a differential of `liftHomologicalComplex K hK` is the differential
of `K`. -/
@[simp]
lemma liftHomologicalComplex_d_hom (i j : ι) :
    ((liftHomologicalComplex K hK).d i j).hom = K.d i j :=
  rfl

/-- Forgetting the finite generation of the terms of `liftHomologicalComplex K hK` recovers `K`. -/
noncomputable def liftHomologicalComplexIso :
    ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj
      (liftHomologicalComplex K hK) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp)

end FGModuleCat
