/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Finite locally free morphisms and pushforward of the structure sheaf

A quasi-coherent `𝒪_X`-module `M` is finite locally free if and only if, over every affine open
`U` of `X`, its module of sections `Γ(M, U)` is a finitely generated projective `Γ(X, U)`-module.
For a commutative `Γ(X, U)`-algebra `S`, being finitely generated and projective as a
`Γ(X, U)`-module is equivalent to `S` being module-finite, flat, and finitely presented as an
algebra: a finitely generated projective module is flat and finitely presented, and conversely a
module-finite, finitely presented algebra is finitely presented as a module, hence projective once
it is flat.

Applied to a quasi-coherent commutative `𝒪_X`-algebra `A`, this shows that the underlying
`𝒪_X`-module `A.X` is finite locally free if and only if the relative spectrum
`Spec_X(A) ⟶ X` is finite, flat, and locally of finite presentation (Stacks, Lemma 29.48.2
(02KB)). Via the recovery isomorphism `Spec_X(f_* 𝒪_Y) ≅ Y` of an affine morphism `f : Y ⟶ X`,
the pushforward `f_* 𝒪_Y` of the structure sheaf is finite locally free if and only if `f` is
finite, flat, and locally of finite presentation; in particular this holds for every finite étale
morphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback_fromSpec_iff`: the pullback of a
  quasi-coherent module `M` along an affine chart `Spec Γ(X, U) ⟶ X` is finite locally free if
  and only if `Γ(M, U)` is finitely generated and projective over `Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen`: a quasi-coherent
  module on `X` is finite locally free if and only if its sections on every affine open are
  finitely generated and projective.
* `CategoryTheory.CommMon.relativeSpec_isFiniteLocallyFree_iff`: for a quasi-coherent commutative
  `𝒪_X`-algebra `A`, the module `A.X` is finite locally free if and only if `Spec_X(A) ⟶ X` is
  finite, flat, and locally of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra_iff` and
  `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit_iff`: for an affine
  morphism `f : Y ⟶ X`, the pushforward `f_* 𝒪_Y` is finite locally free if and only if `f` is
  finite, flat, and locally of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra` and
  `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit`: `f_* 𝒪_Y` is finite
  locally free when `f` is finite, flat, and locally of finite presentation.

## References

* [The Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- For a quasi-coherent `𝒪_X`-module `M` and an affine open `U` of `X`, the pullback of `M`
along the affine chart `Spec Γ(X, U) ⟶ X` is finite locally free if and only if `Γ(M, U)` is a
finitely generated projective `Γ(X, U)`-module. -/
theorem isFiniteLocallyFree_pullback_fromSpec_iff (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    isFiniteLocallyFree (Spec Γ(X, U)) ((pullback hU.fromSpec).obj M) ↔
      Module.Finite Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let K : (Spec Γ(X, U)).Modules := M.restrict hU.fromSpec
  let e : tilde (moduleSpecΓFunctor.obj K) ≅ (pullback hU.fromSpec).obj M :=
    @asIso _ _ _ _ K.fromTildeΓ (isIso_fromTildeΓ_of_isQuasicoherent K) ≪≫
      (restrictFunctorIsoPullback hU.fromSpec).app M
  have he : isFiniteLocallyFree (Spec Γ(X, U)) ((pullback hU.fromSpec).obj M) ↔
      Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj K) ∧
        Module.Projective Γ(X, U) (moduleSpecΓFunctor.obj K) :=
    ⟨fun h ↦ (TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff
      (moduleSpecΓFunctor.obj K)).mp ((isFiniteLocallyFree _).prop_of_iso e.symm h),
     fun h ↦ (isFiniteLocallyFree _).prop_of_iso e
      ((TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff
        (moduleSpecΓFunctor.obj K)).mpr h)⟩
  let eΓ : Γ(M, U) ≃ₗ[Γ(X, U)] moduleSpecΓFunctor.obj K := M.fromSpecSectionsEquiv hU
  exact he.trans ⟨fun ⟨h₁, h₂⟩ ↦ ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv eΓ.symm⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨Module.Finite.equiv eΓ, Module.Projective.of_equiv eΓ⟩⟩

/-- A quasi-coherent `𝒪_X`-module is finite locally free if and only if, on every affine open `U`
of `X`, its sections `Γ(M, U)` form a finitely generated projective `Γ(X, U)`-module. -/
theorem isFiniteLocallyFree_iff_forall_isAffineOpen (M : X.Modules) [M.IsQuasicoherent] :
    isFiniteLocallyFree X M ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        Module.Finite Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  refine ⟨fun ⟨_, _⟩ U hU ↦ (isFiniteLocallyFree_pullback_fromSpec_iff M hU).mp
    ⟨isLocallyFree_pullback hU.fromSpec M, isFinitePresentation_pullback hU.fromSpec M⟩, fun h ↦ ?_⟩
  let hAff (U : X.affineOpens) : IsAffineOpen U.1 := U.2
  let 𝒰 : X.OpenCover := Cover.mkOfCovers X.affineOpens (fun U ↦ Spec Γ(X, U.1))
    (fun U ↦ (hAff U).fromSpec) (fun x ↦ by
      have hx : x ∈ ⨆ U : X.affineOpens, U.1 := by
        rw [iSup_affineOpens_eq_top]
        trivial
      obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
      have hxRange : x ∈ Set.range (hAff U).fromSpec := by
        rw [← Scheme.Hom.coe_opensRange, (hAff U).opensRange_fromSpec]
        exact hxU
      obtain ⟨y, hy⟩ := hxRange
      exact ⟨U, y, hy⟩) (fun U ↦ (hAff U).isOpenImmersion_fromSpec)
  exact (isFiniteLocallyFree_iff_forall_pullback 𝒰 M).mpr fun U ↦
    (isFiniteLocallyFree_pullback_fromSpec_iff M (hAff U)).mpr (h U.1 (hAff U))

end

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.CommMon

open AlgebraicGeometry Opposite

private lemma finite_and_projective_iff_of_algebra {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] :
    Module.Finite R S ∧ Module.Projective R S ↔
      Module.Finite R S ∧ Module.Flat R S ∧ Algebra.FinitePresentation R S := by
  refine ⟨fun ⟨_, _⟩ ↦ ⟨‹_›, Module.Flat.of_projective, ?_⟩,
    fun ⟨_, _, _⟩ ↦ ⟨‹_›, ?_⟩⟩
  · have : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
    exact Algebra.FinitePresentation.of_finitePresentation R S
  · have : Module.FinitePresentation R S :=
      Module.FinitePresentation.of_finite_of_finitePresentation R S
    exact Module.Flat.projective_of_finitePresentation

/-- For a quasi-coherent commutative `𝒪_X`-algebra `A`, the underlying `𝒪_X`-module `A.X` is
finite locally free if and only if the relative spectrum `Spec_X(A) ⟶ X` is finite, flat, and
locally of finite presentation. Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem relativeSpec_isFiniteLocallyFree_iff {X : Scheme.{u}} (A : CommMon X.Modules)
    [A.X.IsQuasicoherent] :
    Scheme.Modules.isFiniteLocallyFree X A.X ↔
      IsFinite A.relativeSpecToBase ∧ Flat A.relativeSpecToBase ∧
        LocallyOfFinitePresentation A.relativeSpecToBase := by
  rw [Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen, A.relativeSpec_finite_iff,
    A.relativeSpec_flat_iff, A.relativeSpec_finitePresentation_iff]
  exact ⟨fun h ↦ ⟨fun U hU ↦ ((finite_and_projective_iff_of_algebra.mp (h U hU)).1),
      fun U hU ↦ (finite_and_projective_iff_of_algebra.mp (h U hU)).2.1,
      fun U hU ↦ (finite_and_projective_iff_of_algebra.mp (h U hU)).2.2⟩,
    fun ⟨hfin, hflat, hfp⟩ U hU ↦
      finite_and_projective_iff_of_algebra.mpr ⟨hfin U hU, hflat U hU, hfp U hU⟩⟩

end CategoryTheory.CommMon

namespace AlgebraicGeometry.Scheme.Hom

/-- For an affine morphism `f : Y ⟶ X`, the pushforward algebra `f_* 𝒪_Y` has finite locally free
underlying `𝒪_X`-module if and only if `f` is finite, flat, and locally of finite presentation.
Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforwardStructureAlgebra_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] :
    Modules.isFiniteLocallyFree X f.pushforwardStructureAlgebra.X ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  rw [f.pushforwardStructureAlgebra.relativeSpec_isFiniteLocallyFree_iff,
    ← f.relativeSpecFunctionsToScheme_comp]
  refine ⟨fun ⟨_, _, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ⟨inferInstance, inferInstance, inferInstance⟩⟩
  -- `f` is isomorphic on the source to `f.relativeSpecFunctionsToScheme ≫ f`.
  have hf : f = inv f.relativeSpecFunctionsToScheme ≫ (f.relativeSpecFunctionsToScheme ≫ f) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [hf]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- If `f : Y ⟶ X` is finite, flat, and locally of finite presentation, then the pushforward
algebra `f_* 𝒪_Y` has finite locally free underlying `𝒪_X`-module. In particular this applies when
`f` is finite and étale. Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforwardStructureAlgebra {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    Modules.isFiniteLocallyFree X f.pushforwardStructureAlgebra.X :=
  (f.isFiniteLocallyFree_pushforwardStructureAlgebra_iff).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- For an affine morphism `f : Y ⟶ X`, the pushforward `f_* 𝒪_Y` of the structure sheaf is
finite locally free if and only if `f` is finite, flat, and locally of finite presentation.
Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit_iff {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] :
    Modules.isFiniteLocallyFree X ((Modules.pushforward f).obj (𝟙_ Y.Modules)) ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  f.isFiniteLocallyFree_pushforwardStructureAlgebra_iff

/-- If `f : Y ⟶ X` is finite, flat, and locally of finite presentation, then `f_* 𝒪_Y` is a
finite locally free `𝒪_X`-module. Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    Modules.isFiniteLocallyFree X ((Modules.pushforward f).obj (𝟙_ Y.Modules)) :=
  f.isFiniteLocallyFree_pushforwardStructureAlgebra

end AlgebraicGeometry.Scheme.Hom
