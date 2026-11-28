/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.CategoryTheory.Preadditive.Projectivization
public import TauCeti.RingTheory.GlobalDimension
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Additive generators from global dimension at most two

Let `M` be an object of an abelian category `C` and `Γ = End M`. The functor `Hom(M, -)`, with
values in right `Γ`-modules, is left exact and identifies `add M` with the finitely generated
projective right `Γ`-modules (projectivization, `TauCeti.finiteProjectiveModules_le_essImage`).
When the right global dimension of `Γ` is at most two, this forces `add M` to be closed under
kernels: for a morphism `d : Q₀ ⟶ Q₁` in `add M`, the module `Hom(M, ker d)` is the kernel of a
morphism between projective modules whose cokernel has projective dimension at most two, so it is
projective. If moreover `Γ` is right Noetherian and `M` is a separator, then `Hom(M, ker d)` is
`Hom(M, Q')` for some `Q'` in `add M`, the isomorphism is composition with a morphism
`Q' ⟶ ker d`, and this morphism is an isomorphism since `Hom(M, -)` is faithful and `C` is
balanced.

So if every object embeds into an object of `add M`, every object `X` is the kernel of a morphism
`Q₀ ⟶ Q₁` in `add M`, and `M` is an additive generator. This is the key step of the converse of
the Auslander correspondence, with `M` a generator-cogenerator of `mod B` for an Artin algebra `B`.

## Main results

* `TauCeti.projective_preadditiveCoyonedaObj_obj_kernel`: if `End M` has right global dimension
  at most two, `Hom(M, ker d)` is projective for every morphism `d` in `add M`.
* `CategoryTheory.IsSeparator.additiveClosure_kernel`: for a separator `M` with `End M` right
  Noetherian of right global dimension at most two, `ker d` lies in `add M` for every morphism `d`
  in `add M`.
* `CategoryTheory.IsSeparator.isAdditiveGenerator_of_globalDimension_le_two`: such a separator is
  an additive generator if every object embeds into an object of `add M`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Proposition VI.5.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {M : C}

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti

/-- Let `M` be an object of an abelian category whose endomorphism ring has right global dimension
at most two, and let `d : Q₀ ⟶ Q₁` be a morphism in `add M`. Then `Hom(M, ker d)` is a projective
right `End M`-module. -/
theorem projective_preadditiveCoyonedaObj_obj_kernel
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2) {Q₀ Q₁ : C} (h₀ : additiveClosure M Q₀)
    (h₁ : additiveClosure M Q₁) (d : Q₀ ⟶ Q₁) :
    Projective ((preadditiveCoyonedaObj M).obj (kernel d)) := by
  -- `Hom(M, -)` is left exact, so `Hom(M, ker d)` is the kernel of `Hom(M, d)` between the
  -- projectives `Hom(M, Q₀)` and `Hom(M, Q₁)`: a second syzygy of a module of projective dimension
  -- at most two.
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₀)).2
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₁)).2
  have hC := (Abelian.globalDimension_le_iff_hasProjectiveDimensionLE _ 2).1 hgl
    (cokernel ((preadditiveCoyonedaObj M).map d))
  have := (hasProjectiveDimensionLT_cokernel_iff_kernel ((preadditiveCoyonedaObj M).map d) 0).1 hC
  exact Projective.of_iso (PreservesKernel.iso (preadditiveCoyonedaObj M) d).symm
    (projective_iff_hasProjectiveDimensionLT_one.2 this)

end TauCeti

namespace CategoryTheory

open TauCeti

/-- Let `M` be a separator of an abelian category whose endomorphism ring is right Noetherian of
right global dimension at most two. Then the kernel of every morphism `d : Q₀ ⟶ Q₁` in `add M` lies
in `add M`. -/
theorem IsSeparator.additiveClosure_kernel [IsNoetherianRing (End M)ᵐᵒᵖ] (hM : IsSeparator M)
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2) {Q₀ Q₁ : C} (h₀ : additiveClosure M Q₀)
    (h₁ : additiveClosure M Q₁) (d : Q₀ ⟶ Q₁) : additiveClosure M (kernel d) := by
  -- By projectivization `Hom(M, ker d) ≅ Hom(M, Q')` with `Q' ∈ add M`, induced by some
  -- `h : Q' ⟶ ker d`; `Hom(M, -)` is faithful and `C` is balanced, so `h` is an isomorphism.
  let F := preadditiveCoyonedaObj M
  have hP := projective_preadditiveCoyonedaObj_obj_kernel hgl h₀ h₁ d
  -- `Hom(M, ker d)` is a submodule of the finitely generated module `Hom(M, Q₀)`.
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₀)).1
  have : Module.Finite (End M)ᵐᵒᵖ (F.obj (kernel d)) := Module.Finite.of_injective
    (F.map (kernel.ι d)).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  obtain ⟨Q', ⟨e⟩⟩ := finiteProjectiveModules_le_essImage (M := M) (F.obj (kernel d))
    (finiteProjectiveModules_iff.2 ⟨this, inferInstance⟩)
  obtain ⟨h, hh⟩ := (preadditiveCoyonedaObj_map_bijective Q'.property (kernel d)).2 e.hom
  have : F.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj M).1 hM
  have : IsIso (F.map h) := hh ▸ inferInstance
  have : IsIso h := isIso_of_reflects_iso h F
  exact (additiveClosure M).prop_of_iso (asIso h) Q'.property

/-- **Additive generators from global dimension at most two.** Let `M` be a separator of an abelian
category whose endomorphism ring is right Noetherian of right global dimension at most two. If every
object embeds into an object of `add M`, then `M` is an additive generator. -/
theorem IsSeparator.isAdditiveGenerator_of_globalDimension_le_two
    [IsNoetherianRing (End M)ᵐᵒᵖ] (hM : IsSeparator M)
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2)
    (hmono : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), additiveClosure M Y ∧ Mono i) :
    IsAdditiveGenerator M := by
  -- Every `X` has a copresentation `0 ⟶ X ⟶ Q₀ ⟶ Q₁` in `add M`, so it is a kernel in `add M`.
  refine isAdditiveGenerator_def.2 fun X ↦ ?_
  obtain ⟨Q₀, i, h₀, _⟩ := hmono X
  obtain ⟨Q₁, j, h₁, _⟩ := hmono (cokernel i)
  -- `X` is the kernel of `cokernel.π i`, hence of `cokernel.π i ≫ j` as `j` is a monomorphism.
  let e : X ≅ kernel (cokernel.π i ≫ j) :=
    (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫ (kernelCompMono _ _).symm
  exact (additiveClosure M).prop_of_iso e.symm (hM.additiveClosure_kernel hgl h₀ h₁ _)

end CategoryTheory
