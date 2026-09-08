/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective finite-dimensional modules

Over a division ring, every finite-dimensional module is free and hence projective. Consequently,
every short exact sequence of finite-dimensional modules splits.

## Main results

* `FGModuleCat.projective`: every finite-dimensional module over a division ring is projective.
* `FGModuleCat.nonempty_splitting_of_shortExact`: every short exact sequence of finite-dimensional
  modules over a division ring splits.
* `FGModuleCat.finrank_biprod`: dimension is additive on biproducts of finite-dimensional modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable (k : Type u) [DivisionRing k]

/-- The dimension of a biproduct of finite-dimensional modules is the sum of their dimensions. -/
theorem _root_.FGModuleCat.finrank_biprod (X Y : FGModuleCat.{v} k) :
    Module.finrank k ((X ⊞ Y : FGModuleCat.{v} k) : Type v) =
      Module.finrank k X + Module.finrank k Y := by
  let F := forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)
  let _ : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  let e : F.obj (X ⊞ Y) ≅ ModuleCat.of k (X × Y) :=
    F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd X.obj Y.obj
  let e' : (X ⊞ Y : FGModuleCat.{v} k) ≅ FGModuleCat.of k (X × Y) := F.preimageIso e
  exact (FGModuleCat.isoToLinearEquiv e').finrank_eq.trans Module.finrank_prod

/-- Every finite-dimensional vector space over a division ring is a projective object. -/
theorem _root_.FGModuleCat.projective (X : FGModuleCat.{v} k) : Projective X := by
  apply (forget₂ (FGModuleCat.{v} k) (ModuleCat.{v} k)).projective_of_map_projective
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis k X)

/-- Every short exact sequence of finite-dimensional vector spaces over a division ring splits. -/
theorem _root_.FGModuleCat.nonempty_splitting_of_shortExact
    {S : ShortComplex (FGModuleCat.{v} k)}
    (hS : S.ShortExact) : Nonempty S.Splitting := by
  have h₃ : (ExactStructure.abelian (FGModuleCat.{v} k)).isProjective S.X₃ :=
    (ExactStructure.abelian_isProjective_iff S.X₃).mpr (FGModuleCat.projective k S.X₃)
  exact ⟨(ExactStructure.abelian (FGModuleCat.{v} k)).splittingOfProjective
    ((ExactStructure.abelian_conflation S).mpr hS) h₃⟩

end TauCeti
