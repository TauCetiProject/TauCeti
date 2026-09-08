/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective finite-dimensional modules

Over a division ring, every finite-dimensional module is free and hence projective. Consequently,
every short exact sequence of finite-dimensional modules splits.

## Main results

* `FGModuleCat.projective`: every finite-dimensional module over a division ring is projective.
* `FGModuleCat.projective_of_free`: every finite free module is projective.
* `FGModuleCat.nonempty_splitting_of_shortExact`: every short exact sequence of finite-dimensional
  modules over a division ring splits.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable (R : Type u) [Ring R]

/-- Every finite free module is a projective object. -/
theorem _root_.FGModuleCat.projective_of_free (X : FGModuleCat.{v} R) [Module.Free R X] :
    Projective X := by
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).projective_of_map_projective
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis R X)

variable (k : Type u) [DivisionRing k]

/-- Every finite-dimensional vector space over a division ring is a projective object. -/
theorem _root_.FGModuleCat.projective (X : FGModuleCat.{v} k) : Projective X :=
  FGModuleCat.projective_of_free k X

/-- Every short exact sequence of finite-dimensional vector spaces over a division ring splits. -/
theorem _root_.FGModuleCat.nonempty_splitting_of_shortExact
    {S : ShortComplex (FGModuleCat.{v} k)}
    (hS : S.ShortExact) : Nonempty S.Splitting := by
  have h₃ : (ExactStructure.abelian (FGModuleCat.{v} k)).isProjective S.X₃ :=
    (ExactStructure.abelian_isProjective_iff S.X₃).mpr (FGModuleCat.projective k S.X₃)
  exact ⟨(ExactStructure.abelian (FGModuleCat.{v} k)).splittingOfProjective
    ((ExactStructure.abelian_conflation S).mpr hS) h₃⟩

end TauCeti
