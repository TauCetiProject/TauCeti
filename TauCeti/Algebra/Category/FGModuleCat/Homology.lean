/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.FullSubcategory

/-!
# Lifting complexes of modules to `FGModuleCat`

A homological complex of modules whose terms are finitely generated lifts to a complex in
`FGModuleCat` by Mathlib's `HomologicalComplex.liftObjectProperty`. This file records that the
lift recovers the original complex after forgetting finite generation
(`HomologicalComplex.liftFGModuleCatIso`).
-/

public section

open CategoryTheory

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (hK : ∀ i, Module.Finite R (K.X i))

/-- A homological complex of modules with finitely generated terms, lifted to `FGModuleCat R`
by Mathlib's `HomologicalComplex.liftObjectProperty`, recovers the original complex after
forgetting finite generation. -/
noncomputable def liftFGModuleCatIso :
    ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex c).obj
      (K.liftObjectProperty (ModuleCat.isFG R) fun i ↦ (ModuleCat.isFG_iff _).2 (hK i)) ≅ K :=
  -- `forget₂` is the inclusion of the full subcategory, so it sends `homMk f` to `f`.
  Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun _ _ _ ↦
    (Category.id_comp _).trans (Category.comp_id _).symm

end HomologicalComplex
