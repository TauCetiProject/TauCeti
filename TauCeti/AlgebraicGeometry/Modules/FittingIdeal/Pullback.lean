/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Basic
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
public import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Pullback of Fitting ideal sheaves

Fitting ideal sheaves of quasicoherent modules of finite type commute with pullback.
Their affine computation is the algebraic identity `Fitt_k(S ⊗_R M) = Fitt_k(M) S`.
This compatibility is an ingredient for base change of relative singular subschemes.
That application also requires a pullback comparison for relative differentials,
which is not established here.

## References

* The Stacks Project, Tag 0C3C (Fitting ideals of quasicoherent modules).
* The Stacks Project, Tag 07ZA (base change of Fitting ideals).

-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

/-- The affine calculation used to glue the pullback identity. -/
private theorem fittingIdeal_pullback_SpecMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (k : ℕ) :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k =
      (M.fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k).comap
          (Spec.map φ) := by
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ M
  have : N.IsFiniteType := Scheme.Modules.isFiniteType_pullback _ M
  have : Module.Finite R Γ(M, ⊤) := M.finite_moduleSpecΓ
  have : Module.Finite S Γ(N, ⊤) := N.finite_moduleSpecΓ
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := M.finite_moduleSpecΓ
  have : Module.Finite S (moduleSpecΓFunctor.obj N) := N.finite_moduleSpecΓ
  let eM : tilde (moduleSpecΓFunctor.obj M) ≅ M :=
    @asIso (Spec R).Modules _ _ _ M.fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)
  let := φ.hom.toAlgebra
  -- `tildeFunctorCompPullbackIso` is the canonical comparison between pullback
  -- of an associated sheaf and extension of scalars.
  let e : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj N :=
    (tilde.toTildeΓNatIso (R := S)).app _ ≪≫
      (moduleSpecΓFunctor (R := S)).mapIso
        (((AlgebraicGeometry.tildeFunctorCompPullbackIso φ).app _).symm ≪≫
          (Scheme.Modules.pullback (Spec.map φ)).mapIso eM)
  have : Module.Finite S ((ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj M)) := Module.Finite.equiv e.toLinearEquiv.symm
  have hfit : TauCeti.fittingIdeal S Γ(N, ⊤) k =
      (TauCeti.fittingIdeal R Γ(M, ⊤) k).map φ.hom := by
    -- `moduleSpecΓFunctor` and `Γ(-, ⊤)` use different category wrappers for the
    -- same sections and scalar action; the explicit isomorphism `e` supplies the comparison.
    convert! (TauCeti.fittingIdeal_congr e.toLinearEquiv k).symm.trans
      (fittingIdeal_baseChange (S := S) (M := moduleSpecΓFunctor.obj M) k)
  rw [Scheme.Modules.fittingIdeal_Spec, Scheme.Modules.fittingIdeal_Spec,
    Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_map, hfit, Ideal.map_map]
  congr 2
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality φ)

/-- The pullback identity on an affine chart of the source. -/
private theorem fittingIdeal_pullback_fromSpec
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {U : X.Opens} (hU : IsAffineOpen U) (k : ℕ) :
    ((Scheme.Modules.pullback hU.fromSpec).obj M).fittingIdeal
        (fun V ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ V.1 V.2) k =
      (M.fittingIdeal
        (fun V ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ V.1 V.2) k).comap
          hU.fromSpec := by
  let P := (Scheme.Modules.pullback hU.fromSpec).obj M
  have : P.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ M
  have : P.IsFiniteType := Scheme.Modules.isFiniteType_pullback _ M
  have : Module.Finite Γ(X, U) Γ(M, U) := M.finite_sections_of_isAffineOpen U hU
  have : Module.Finite Γ(X, U) Γ(P, ⊤) := P.finite_moduleSpecΓ
  let eQ : Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(P, ⊤) := by
    -- The spectrum global-sections functor uses ModuleCat rather than Ab wrappers.
    convert! ((moduleSpecΓFunctor (R := Γ(X, U))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M)).toLinearEquiv
  let e := (M.fromSpecSectionsEquiv hU).trans eQ
  rw [Scheme.Modules.fittingIdeal_Spec,
    Scheme.IdealSheafData.comap_fromSpec_eq_ofIdealTop, Scheme.Modules.fittingIdeal_ideal]
  congr 2
  exact (TauCeti.fittingIdeal_congr e k).symm

/-- Fitting ideal sheaves of quasicoherent modules of finite type commute with
pullback along arbitrary morphisms of schemes, without a flatness hypothesis. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (k : ℕ) :
    ((Scheme.Modules.pullback f).obj M).fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k =
      (M.fittingIdeal
        (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.1 U.2) k).comap f := by
  have charts (x : X) : ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧
      x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
    obtain ⟨V, hV, hxV, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (U := ⊤) (x := f x) (by simp)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (U := f ⁻¹ᵁ V) (x := x) hxV
    exact ⟨U, V, hU, hV, hxU, hUV⟩
  choose U V hU hV hx hUV using charts
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x ↦ Spec Γ(X, U x))
    (fun x ↦ (hU x).fromSpec) (fun x ↦ ⟨x, by
      have hmem : x ∈ Set.range (hU x).fromSpec := (hU x).range_fromSpec.symm ▸ hx x
      simpa only [Set.mem_range] using hmem⟩)
  apply Scheme.IdealSheafData.ext_of_comap_openCover 𝒰
  intro x
  let N := (Scheme.Modules.pullback f).obj M
  let P := (Scheme.Modules.pullback (hV x).fromSpec).obj M
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ M
  have : N.IsFiniteType := Scheme.Modules.isFiniteType_pullback _ M
  have : P.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pullback _ M
  have : P.IsFiniteType := Scheme.Modules.isFiniteType_pullback _ M
  let ψ := Spec.map (f.appLE (V x) (U x) (hUV x))
  have hcomm : ψ ≫ (hV x).fromSpec = (hU x).fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f (hV x) (hU x) (hUV x)
  let e : (Scheme.Modules.pullback (hU x).fromSpec).obj N ≅
      (Scheme.Modules.pullback ψ).obj P :=
    (Scheme.Modules.pullbackComp (hU x).fromSpec f).app M ≪≫
      (Scheme.Modules.pullbackCongr hcomm.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp ψ (hV x).fromSpec).app M).symm
  have he := Scheme.Modules.fittingIdeal_congr
    (fun W ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ W.1 W.2)
    e k
  -- The cover maps are the chosen affine charts. The pullback-composition isomorphism
  -- compares the two actual sheaves, rather than identifying chosen pullbacks by equality.
  -- `rw` cannot reduce the cover's dependent index and object projections together.
  -- Restate the goal using its specified chart maps before applying the comparisons.
  change (N.fittingIdeal
      (fun W ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ W.1 W.2) k).comap
        (hU x).fromSpec =
    ((M.fittingIdeal
      (fun W ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ W.1 W.2) k).comap f).comap
        (hU x).fromSpec
  rw [← fittingIdeal_pullback_fromSpec N (hU x), he,
    fittingIdeal_pullback_SpecMap, fittingIdeal_pullback_fromSpec,
    ← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp]

end TauCeti
