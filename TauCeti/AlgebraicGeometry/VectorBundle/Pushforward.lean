/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Pushforward of finite locally free sheaves along finite locally free morphisms

For a finite, flat, locally finitely presented morphism of schemes `f : Y ⟶ X`, the direct image
`f_* M` of any finite locally free `𝒪_Y`-module `M` is finite locally free on `X`
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`). In particular, the
pushforward of the structure sheaf `f_* 𝒪_Y` is finite locally free
(`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit`).

Over an affine open `U` of `X`, the preimage `V = f⁻¹ U` is affine because `f` is finite. The
sections `Γ(M, V)` form a finite projective `Γ(Y, V)`-module because `M` is finite locally free,
and `Γ(Y, V)` is a finite projective `Γ(X, U)`-module because `f` is finite, flat, and locally of
finite presentation (`AlgebraicGeometry.Scheme.Hom.projective_app`). Restriction of scalars
preserves both finiteness and projectivity, so the quasi-coherent sheaf `f_* M` restricts to a
finite locally free sheaf on `Spec Γ(X, U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: pushforward along a finite,
  flat, locally finitely presented morphism preserves finite locally free sheaves.
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit`: the pushforward `f_* 𝒪_Y`
  of the structure sheaf along a finite, flat, locally finitely presented morphism `f : Y ⟶ X` is
  finite locally free on `X`.

## References

* [The Stacks Project, Lemma 29.48.2](https://stacks.math.columbia.edu/tag/02KB), finite locally
  free morphisms.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- On an affine open `U` of `Y`, the sections `Γ(M, U)` of a finite locally free `𝒪_Y`-module `M`
form a finite projective `Γ(Y, U)`-module. -/
private theorem finite_and_projective_sections_of_isFiniteLocallyFree (M : Y.Modules)
    (hM : isFiniteLocallyFree Y M) (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ(M, U.1) ∧ Module.Projective Γ(Y, U.1) Γ(M, U.1) := by
  have : M.IsLocallyFree := hM.1
  have : M.IsFinitePresentation := hM.2
  have := U.2.isOpenImmersion_fromSpec
  let N : (Spec Γ(Y, U.1)).Modules := M.restrict U.2.fromSpec
  have hN : isFiniteLocallyFree (Spec Γ(Y, U.1)) N :=
    (isFiniteLocallyFree (Spec Γ(Y, U.1))).prop_of_iso
      ((restrictFunctorIsoPullback U.2.fromSpec).app M).symm
      ⟨isLocallyFree_pullback U.2.fromSpec M, isFinitePresentation_pullback U.2.fromSpec M⟩
  have ⟨hfin, hproj⟩ :=
    TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_projective_moduleSpecΓ ⟨N, hN⟩
  let e : moduleSpecΓFunctor.obj N ≃ₗ[Γ(Y, U.1)] Γ(M, U.1) := (M.fromSpecSectionsEquiv U.2).symm
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩

/-- Pushforward along a finite, flat, locally finitely presented morphism `f : Y ⟶ X` preserves
finite locally free sheaves. -/
theorem isFiniteLocallyFree_pushforward (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (M : Y.Modules) (hM : isFiniteLocallyFree Y M) :
    isFiniteLocallyFree X ((pushforward f).obj M) := by
  have : M.IsQuasicoherent :=
    ((TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.toQuasicoherent Y).obj ⟨M, hM⟩).property
  let P : X.Modules := (pushforward f).obj M
  have : P.IsQuasicoherent := isQuasicoherent_pushforward M f
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X.affineOpens
    (fun U : X.affineOpens ↦ Spec Γ(X, U))
    (fun U ↦ U.property.fromSpec)
    (fun x ↦ by
      obtain ⟨U, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).symm ▸ TopologicalSpace.Opens.mem_top x)
      rw [← U.property.opensRange_fromSpec] at hx
      obtain ⟨p, hp⟩ := hx
      exact ⟨U, p, hp⟩)
    (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.property)
  refine (isFiniteLocallyFree_iff_forall_pullback 𝒰 P).mpr fun U ↦ ?_
  have := U.2.isOpenImmersion_fromSpec
  let N : (Spec Γ(X, U.1)).Modules := P.restrict U.2.fromSpec
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor U.2.fromSpec P
  have hN : isFiniteLocallyFree (Spec Γ(X, U.1)) N := by
    have : IsIso (fromTildeΓ N) := isIso_fromTildeΓ_of_isQuasicoherent N
    refine (isFiniteLocallyFree (Spec Γ(X, U.1))).prop_of_iso (asIso (fromTildeΓ N)) ?_
    rw [TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff]
    let V : Y.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
    have ⟨hMfin, hMproj⟩ := finite_and_projective_sections_of_isFiniteLocallyFree M hM V
    let := (f.app U.1).hom.toAlgebra
    have : Module.Finite Γ(X, U.1) Γ(Y, V.1) := RingHom.finite_algebraMap.mp (f.finite_app U.1 U.2)
    have : Module.Projective Γ(X, U.1) Γ(Y, V.1) := f.projective_app U
    let : Module Γ(X, U.1) Γ(M, V.1) := Module.compHom Γ(M, V.1) (f.app U.1).hom
    have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(M, V.1) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have hPfin : Module.Finite Γ(X, U.1) Γ(M, V.1) := Module.Finite.trans Γ(Y, V.1) Γ(M, V.1)
    have hPproj : Module.Projective Γ(X, U.1) Γ(M, V.1) := by
      classical
      obtain ⟨s, hs⟩ := hMproj
      have : Module.Projective Γ(X, U.1) (Γ(M, V.1) →₀ Γ(Y, V.1)) :=
        Module.Projective.of_equiv' (finsuppLequivDFinsupp Γ(X, U.1)).symm
      exact Module.Projective.of_split (s.restrictScalars Γ(X, U.1))
        ((Finsupp.linearCombination Γ(Y, V.1) id).restrictScalars Γ(X, U.1)) (LinearMap.ext hs)
    -- Pushforward sections over `U` are `Γ(M, f⁻¹ U)` with scalars restricted along `f.app U`.
    let eSec : Γ(M, V.1) ≃ₗ[Γ(X, U.1)] Γ(P, U.1) :=
      { toFun := id
        invFun := id
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    let e : Γ(M, V.1) ≃ₗ[Γ(X, U.1)] moduleSpecΓFunctor.obj N :=
      eSec.trans (P.fromSpecSectionsEquiv U.2)
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  exact (isFiniteLocallyFree (Spec Γ(X, U.1))).prop_of_iso
    ((restrictFunctorIsoPullback U.2.fromSpec).app P) hN

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- For a finite, flat, locally finitely presented morphism `f : Y ⟶ X`, the pushforward of the
structure sheaf `f_* 𝒪_Y` is finite locally free on `X`. -/
theorem isFiniteLocallyFree_pushforward_unit (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    Scheme.Modules.isFiniteLocallyFree X ((Scheme.Modules.pushforward f).obj (𝟙_ Y.Modules)) :=
  Scheme.Modules.isFiniteLocallyFree_pushforward f (𝟙_ Y.Modules)
    (Scheme.Modules.isMonoidal_isFiniteLocallyFree Y).prop_unit

end AlgebraicGeometry.Scheme.Hom
