/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected

/-!
# Base change of a diagram and its limit cone along a morphism to a stage

Given a diagram `D : I ⥤ C` in a category with pullbacks and a morphism `p : Y ⟶ D.obj i₀` to a
stage `i₀ : I`, pulling `p` back along `D.map j.hom` for `j : Over i₀` defines an `Over i₀`-indexed
diagram `TauCeti.pullbackDiagram D i₀ p` together with its projections `pullbackDiagramSnd` and
`pullbackDiagramToBase`, pullback transition squares (`isPullback_pullbackDiagram_map`), and an
induced cone `pullbackDiagramCone D c i₀ p` over any cone `c` on `D`. When
`(Over.forget i₀).Initial` and `c` is a limit cone, `isLimitPullbackDiagramCone` shows that
`pullback p (c.π.app i₀)` is the limit of `pullbackDiagram D i₀ p`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

variable {I C : Type*} [Category* I] [Category* C] [HasPullbacks C] (D : I ⥤ C) (c : Cone D)

/-- Base-changing `D : I ⥤ C` along `p : Y ⟶ D.obj i₀` gives an `Over i₀`-indexed diagram. -/
@[expose, simps, implicit_reducible]
noncomputable def pullbackDiagram (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) : Over i₀ ⥤ C where
  obj j := pullback p (D.map j.hom)
  map f := pullback.map p _ p _ (𝟙 _) (D.map f.left) (𝟙 _) (by simp) (by simp [← D.map_comp])
  map_id _ := by apply pullback.hom_ext <;> simp
  map_comp _ _ := by apply pullback.hom_ext <;> simp

/-- Second projection from `pullbackDiagram D i₀ p` to `Over.forget i₀ ⋙ D`. -/
@[expose, simps] noncomputable def pullbackDiagramSnd (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    pullbackDiagram D i₀ p ⟶ Over.forget i₀ ⋙ D where
  app j := pullback.snd p (D.map j.hom)

/-- Natural transformation from `pullbackDiagram D i₀ p` to the constant diagram on `D.obj i₀`. -/
@[expose, simps] noncomputable def pullbackDiagramToBase (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    pullbackDiagram D i₀ p ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) where
  app j := pullback.snd p (D.map j.hom) ≫ D.map j.hom
  naturality _ _ _ := by simp [← D.map_comp]

/-- Cone over `pullbackDiagram D i₀ p` with vertex `pullback p (c.π.app i₀)` induced by `c`. -/
@[expose, simps, implicit_reducible]
noncomputable def pullbackDiagramCone (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    Cone (pullbackDiagram D i₀ p) where
  pt := pullback p (c.π.app i₀)
  π := { app j := pullback.map p _ p _ (𝟙 _) (c.π.app j.left) (𝟙 _) (by simp) (by simp [c.w])
         naturality _ _ _ := by apply pullback.hom_ext <;> simp [c.w] }

/-- Transition morphisms of `pullbackDiagram D i₀ p` form pullback squares with `D.map f.left`. -/
theorem isPullback_pullbackDiagram_map {i₀ : I} {Y : C} (p : Y ⟶ D.obj i₀) {j k : Over i₀}
    (f : j ⟶ k) : IsPullback ((pullbackDiagram D i₀ p).map f) (pullback.snd p (D.map j.hom))
      (pullback.snd p (D.map k.hom)) (D.map f.left) :=
  .of_right (by simpa [← D.map_comp, Over.w f] using IsPullback.of_hasPullback p (D.map j.hom))
    (by simp) (IsPullback.of_hasPullback p (D.map k.hom))

/-- When `(Over.forget i₀).Initial` and `c` is a limit cone over `D`, `pullbackDiagramCone D c i₀ p`
exhibits `pullback p (c.π.app i₀)` as the limit of `pullbackDiagram D i₀ p`. -/
noncomputable def isLimitPullbackDiagramCone (hc : IsLimit c) (i₀ : I) [(Over.forget i₀).Initial]
    {Y : C} (p : Y ⟶ D.obj i₀) : IsLimit (pullbackDiagramCone D c i₀ p) :=
  letI : IsConnected (Over i₀) := isConnected_of_isTerminal (Over i₀) Over.mkIdTerminal
  isLimitOfIsPullbackOfIsConnected (pullbackDiagramSnd D i₀ p) (pullbackDiagramCone D c i₀ p)
    (c.whisker (Over.forget i₀)) { hom := pullback.snd p (c.π.app i₀), w := fun _ ↦ by simp }
    (fun j ↦ .of_right (by simpa [c.w j.hom] using IsPullback.of_hasPullback p (c.π.app i₀))
      (by simp) (IsPullback.of_hasPullback p (D.map j.hom)))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)

end TauCeti
