/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

/-!
# Naturality of smooth singular chain maps

Passing `TauCeti.smoothSingularSubcomplexMap_ι` through `SSet.chainComplexFunctor` shows that
pushing smooth singular chains forward along a smooth map and then including into continuous
singular chains agrees with including first and then pushing forward
(`TauCeti.chainComplexMap_smoothSingularSubcomplexMap_ι`).
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {J₁ : ModelWithCorners ℝ E₁ H₁} {N₁ : Type u} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- Pushing smooth singular chains forward along a smooth map `f : M → N₁` and then including
them into continuous singular chains is the same as including first and then pushing forward
along `f`. -/
@[reassoc]
theorem chainComplexMap_smoothSingularSubcomplexMap_ι {f : M → N₁} (hf : ContMDiff I J₁ ∞ f)
    (R : C) :
    SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex J₁ N₁).ι R =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R := by
  rw [← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι hf]

end TauCeti
