/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Pullback along a flat morphism of ringed spaces is exact

Let `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` be a morphism of ringed spaces whose stalk maps
`𝒪_{X,f(y)} → 𝒪_{Y,y}` are flat. Then pullback of sheaves of modules `f^*` preserves
monomorphisms (`TauCeti.SheafOfModules.preservesMonomorphisms_pullback_of_flat`). Being a left
adjoint, it also preserves finite colimits, so it preserves homology
(`TauCeti.SheafOfModules.preservesHomology_pullback_of_flat`) and finite limits
(`TauCeti.SheafOfModules.preservesFiniteLimits_pullback_of_flat`): `f^*` is exact. No hypothesis
is made on the sheaves of modules; in particular they need not be quasi-coherent, which matters for
injective resolutions.

Injectivity of a morphism of sheaves of modules can be checked on stalks
(`SheafOfModules.mono_iff_forall_injective_stalkMapCommRing`), and the stalk of `f^* G` at `y` is
`𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} G_{f(y)}`, naturally in `G`
(`TauCeti.SheafOfModules.pullbackStalkEquiv_naturality`). So the stalk map of `f^* g` at `y` is the
base change of the stalk map of `g` at `f y` along a flat ring map, which is injective when that of
`g` is.

## References

* The Stacks Project, *Sheaves of Modules*, the section on flat morphisms of ringed spaces.
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- **Flat pullback preserves monomorphisms.** If every stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of a
morphism of ringed spaces `(f, φ)` is flat, then pullback of sheaves of modules along `(f, φ)`
preserves monomorphisms. -/
theorem preservesMonomorphisms_pullback_of_flat (hφ : ∀ y, (ringStalkMap φ y).hom.Flat) :
    (_root_.SheafOfModules.pullback φ).PreservesMonomorphisms where
  preserves {G G'} g hg := by
    rw [_root_.SheafOfModules.mono_iff_forall_injective_stalkMapCommRing] at hg ⊢
    intro y
    let := stalkAlgebra φ y
    -- Flatness of a ring map is flatness of the algebra it defines.
    have : Module.Flat _ _ := hφ y
    have hbc : Function.Injective (LinearMap.baseChange ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
        (PresheafOfModules.stalkMapCommRing (S := 𝒪X.obj) (f y) g.val)) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ (hg (f y))
    -- Under the identifications of stalks of pullbacks with base changes of stalks, the stalk
    -- map of `f^* g` at `y` is the base change of the stalk map of `g` at `f y`.
    have h : ⇑(PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
        ((_root_.SheafOfModules.pullback φ).map g).val) =
        ⇑(pullbackStalkEquiv φ G' y) ∘ ⇑(LinearMap.baseChange ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
          (PresheafOfModules.stalkMapCommRing (S := 𝒪X.obj) (f y) g.val)) ∘
            ⇑(pullbackStalkEquiv φ G y).symm := by
      funext t
      simpa using congr($(pullbackStalkEquiv_naturality φ G y g)
        ((pullbackStalkEquiv φ G y).symm t)).symm
    rw [h]
    exact (LinearEquiv.injective _).comp (hbc.comp (LinearEquiv.injective _))

/-- **Flat pullback is exact.** If every stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of a morphism of
ringed spaces `(f, φ)` is flat, then pullback of sheaves of modules along `(f, φ)` preserves
homology. -/
theorem preservesHomology_pullback_of_flat (hφ : ∀ y, (ringStalkMap φ y).hom.Flat) :
    (_root_.SheafOfModules.pullback φ).PreservesHomology :=
  have := preservesMonomorphisms_pullback_of_flat φ hφ
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- If every stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` of a morphism of ringed spaces `(f, φ)` is flat,
then pullback of sheaves of modules along `(f, φ)` preserves finite limits. -/
theorem preservesFiniteLimits_pullback_of_flat (hφ : ∀ y, (ringStalkMap φ y).hom.Flat) :
    PreservesFiniteLimits (_root_.SheafOfModules.pullback φ) :=
  have := preservesHomology_pullback_of_flat φ hφ
  Functor.preservesFiniteLimits_of_preservesHomology _

end SheafOfModules

end

end TauCeti
