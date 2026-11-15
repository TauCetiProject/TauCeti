/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Finite local freeness is local on the scheme

An `𝒪_X`-module `M` on a scheme `X` is finite locally free exactly when it is trivialized by an
open cover of `X`: for some open cover `fᵢ : Uᵢ ⟶ X`, each pullback `fᵢ^* M` is isomorphic to the
free `𝒪_{Uᵢ}`-module on a finite type
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_exists_openCover`). Consequently
finite local freeness can be checked on any open cover
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`): `M` is finite locally
free if and only if every `fᵢ^* M` is.

Finite local freeness of `𝒪_X`-modules is defined on the site of opens of `X`, through finite
local bases over the slices at a cover of `X` by opens
(`SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType`). The
characterization by open covers states it instead through the modules on the open subschemes
`Uᵢ`. The slice at an open `U` and the open subscheme `U` carry equivalent categories of modules
(`AlgebraicGeometry.Scheme.Modules.overEquiv`), restriction along `U.ι` corresponds to restriction
to the slice (`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`), and these identifications, as
well as pullback along an isomorphism of schemes, preserve free modules. An arbitrary open
immersion `f` is identified with the inclusion of its open image `f.opensRange` through the
isomorphism `f.isoOpensRange`.

Checking on an open cover is how statements about modules on affine schemes, where they are
modules over a ring, extend to modules on arbitrary schemes, along an affine open cover.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_exists_openCover`: a module is finite
  locally free if and only if some open cover trivializes it with finite free modules;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback`: a module is finite
  locally free if and only if its pullback to each member of a given open cover is.

## References

* [The Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is finite locally free if and only if it is trivialized by an open cover:
for some open cover `fᵢ : Uᵢ ⟶ X`, each pullback `fᵢ^* M` is isomorphic to the free
`𝒪_{Uᵢ}`-module on a finite type. -/
theorem isFiniteLocallyFree_iff_exists_openCover (M : X.Modules) :
    isFiniteLocallyFree X M ↔ ∃ 𝒰 : X.OpenCover.{u}, ∀ i, ∃ I : Type u, Finite I ∧
      Nonempty ((pullback (𝒰.f i)).obj M ≅ SheafOfModules.free I) := by
  refine (SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType M).trans ?_
  constructor
  · rintro ⟨q, hq, hq'⟩
    -- The opens of a cover with finite local bases form an open cover of `X`, and each local
    -- basis is a trivialization over the corresponding open subscheme.
    refine ⟨X.openCoverOfIsOpenCover q.X ((Opens.coversTop_iff _ q.X).mp q.coversTop),
      fun i ↦ ⟨(q.generators i).I, (hq'.isFiniteType i).finite, ⟨?_⟩⟩⟩
    let U : X.Opens := q.X i
    have := hq.isIso i
    exact ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
      restrictIsoFreeOfOverIsoFree M U (asIso (q.generators i).π).symm
  · rintro ⟨𝒰, h⟩
    choose I hI e using h
    -- The open images of the members of the cover carry local bases of `M`.
    let e' (i : 𝒰.I₀) : M.over (𝒰.f i).opensRange ≅ SheafOfModules.free (I i) :=
      overIsoFreeOfRestrictIsoFree M _ (restrictOpensRangeIsoFree M (𝒰.f i) (e i).some)
    let q : SheafOfModules.LocalGeneratorsData.{u} (R := X.ringCatSheaf) M :=
      { I := 𝒰.I₀
        X i := (𝒰.f i).opensRange
        coversTop := (Opens.coversTop_iff _ _).mpr 𝒰.isOpenCover_opensRange
        generators i := (SheafOfModules.free.generatingSections (I i)).ofEpi (e' i).inv }
    refine ⟨q, ?_, ?_⟩
    · constructor
      intro i
      exact (SheafOfModules.free.generatingSections (I i)).isIso_ofEpi_π (e' i).inv inferInstance
    · constructor
      intro i
      exact ⟨hI i⟩

/-- Finite local freeness of `𝒪_X`-modules can be checked on an open cover: an `𝒪_X`-module `M`
is finite locally free if and only if its pullback `fᵢ^* M` to each member `fᵢ : Uᵢ ⟶ X` of an
open cover is. -/
theorem isFiniteLocallyFree_iff_forall_pullback (𝒰 : X.OpenCover) (M : X.Modules) :
    isFiniteLocallyFree X M ↔ ∀ i, isFiniteLocallyFree (𝒰.X i) ((pullback (𝒰.f i)).obj M) := by
  refine ⟨fun ⟨_, _⟩ i ↦ ⟨isLocallyFree_pullback _ M, isFinitePresentation_pullback _ M⟩,
    fun h ↦ ?_⟩
  choose 𝒱 h𝒱 using fun i ↦ (isFiniteLocallyFree_iff_exists_openCover _).mp (h i)
  -- Every point `x` lies in the image of some `𝒰.f i`, say of `y`, and `y` lies in the image of
  -- a member of `𝒱 i`; the composites of these members with `𝒰.f i` cover `X` and trivialize `M`.
  choose y hy using fun x ↦ 𝒰.covers x
  let k (x : X) : (𝒱 (𝒰.idx x)).I₀ := (𝒱 (𝒰.idx x)).idx (y x)
  rw [isFiniteLocallyFree_iff_exists_openCover]
  refine ⟨Cover.mkOfCovers X (fun x ↦ (𝒱 (𝒰.idx x)).X (k x))
    (fun x ↦ (𝒱 (𝒰.idx x)).f (k x) ≫ 𝒰.f (𝒰.idx x)) (fun x ↦ ?_) (fun _ ↦ inferInstance),
    fun x ↦ ?_⟩
  · obtain ⟨z, hz⟩ := (𝒱 (𝒰.idx x)).covers (y x)
    exact ⟨x, z, by rw [Scheme.Hom.comp_apply, hz, hy x]⟩
  · obtain ⟨I, hI, ⟨e⟩⟩ := h𝒱 (𝒰.idx x) (k x)
    exact ⟨I, hI, ⟨((pullbackComp _ _).app M).symm ≪≫ e⟩⟩

end

end AlgebraicGeometry.Scheme.Modules
