/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Module.Torsion.Localization
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Flat base change in singular homology

Let `S` be a flat `R`-algebra. Extension of scalars `M ↦ S ⊗[R] M` is then an exact functor
from `R`-modules to `S`-modules which preserves coproducts, so it commutes with singular homology:

`S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`

(`TauCeti.singularHomologyTensorIso`). This is the universal coefficient theorem for flat
coefficients, where the `Tor` term vanishes. It is the simplicial comparison
`SSet.homologyExtendScalarsIso` applied to the singular simplicial set. The exactness of
`S ⊗[R] -` is the instance `ModuleCat.preservesFiniteLimits_extendScalars_algebraMap`.

The main example is a localization `S = M⁻¹R` of `R` at a submonoid `M`, for instance
`ℚ = (ℤ ∖ 0)⁻¹ℤ` or `ℤ[1/d]`. Since `M⁻¹R ⊗[R] N` vanishes exactly when every element of `N` is
killed by an element of `M`, the homology with coefficients in `M⁻¹R` vanishes in a degree exactly
when the homology with coefficients in `R` is `M`-torsion there
(`TauCeti.isTorsion'_singularChains_homology_iff`). For `R = ℤ` and `S = ℚ`: the rational homology
of a space vanishes in a degree exactly when its integral homology is a torsion group there
(`TauCeti.isAddTorsion_singularChains_homology_iff`).

## Main declarations

* `TauCeti.singularHomologyTensorIso`: `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` for a flat `R`-algebra `S`,
  natural in `X` (`TauCeti.singularHomologyTensorIso_hom_naturality`), with components given by
  `TauCeti.singularHomologyTensorIso_hom`.
* `TauCeti.isTorsion'_singularChains_homology_iff`: `Hₙ(X; R)` is `M`-torsion exactly when
  `Hₙ(X; M⁻¹R)` vanishes; `TauCeti.isTorsion'_singularChains_int_homology_iff` is the case
  `R = ℤ`.
* `TauCeti.isAddTorsion_singularChains_homology_iff`: `Hₙ(X; ℤ)` is a torsion group exactly when
  `Hₙ(X; ℚ)` vanishes.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.A.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TensorProduct

universe u

namespace TauCeti

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- **Flat base change in singular homology.** For a flat `R`-algebra `S`, singular homology with
coefficients in `S` is the extension of scalars of singular homology with coefficients in `R`:
`S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)`, as `S`-modules. It is the simplicial comparison
`SSet.homologyExtendScalarsIso` for the singular simplicial set of `X`. -/
def singularHomologyTensorIso [Module.Flat R S] (X : TopCat.{u}) (n : ℕ) :
    ModuleCat.of S (S ⊗[R] ((singularChains R).obj X).homology n) ≅
      ((singularChains S).obj X).homology n :=
  (ModuleCat.extendScalarsAlgebraMapIso _).symm ≪≫
    -- The simplicial comparison takes its `R`-coefficients in `ULift R`.
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapIso
      (HomologicalComplex.homologyMapIso (((SSet.chainComplexFunctor (ModuleCat.{u} R)).flip.obj
        (TopCat.toSSet.obj X)).mapIso ULift.moduleEquiv.toModuleIso) n).symm ≪≫
    (TopCat.toSSet.obj X).homologyExtendScalarsIso (algebraMap R S) n

/-- The identification `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` identifies `S ⊗[R] Hₙ(X; R)` with the
extension of scalars of `Hₙ(X; R)`, changes the coefficients `R` into `ULift R`, and then applies
the simplicial comparison `SSet.homologyExtendScalarsIso`. -/
theorem singularHomologyTensorIso_hom [Module.Flat R S] (X : TopCat.{u}) (n : ℕ) :
    (singularHomologyTensorIso R S X n).hom =
      (ModuleCat.extendScalarsAlgebraMapIso _).inv ≫
        (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).map
          (HomologicalComplex.homologyMap (((SSet.chainComplexFunctor (ModuleCat.{u} R)).flip.obj
            (TopCat.toSSet.obj X)).map ULift.moduleEquiv.toModuleIso.inv) n) ≫
        ((TopCat.toSSet.obj X).homologyExtendScalarsIso (algebraMap R S) n).hom :=
  (rfl)

/-- The identification `S ⊗[R] Hₙ(X; R) ≅ Hₙ(X; S)` is natural in the space `X`. -/
@[reassoc]
theorem singularHomologyTensorIso_hom_naturality [Module.Flat R S] {X Y : TopCat.{u}} (f : X ⟶ Y)
    (n : ℕ) :
    ModuleCat.ofHom ((HomologicalComplex.homologyMap ((singularChains R).map f) n).hom.baseChange
        S) ≫ (singularHomologyTensorIso R S Y n).hom =
      (singularHomologyTensorIso R S X n).hom ≫
        HomologicalComplex.homologyMap ((singularChains S).map f) n := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  -- Changing the coefficients `R` into `ULift R` is natural in the space.
  let e : ModuleCat.of R (ULift.{u} R) ≅ ModuleCat.of R R := ULift.moduleEquiv.toModuleIso
  have h := congrArg (fun g ↦ F.map (HomologicalComplex.homologyMap g n))
    (((SSet.chainComplexFunctor (ModuleCat.{u} R)).map e.inv).naturality (TopCat.toSSet.map f))
  simp only [HomologicalComplex.homologyMap_comp, F.map_comp] at h
  rw [singularHomologyTensorIso_hom, singularHomologyTensorIso_hom]
  -- The three squares name the same objects in different unfolded forms, so `rw` cannot match
  -- them in the goal, and they are chained explicitly.
  exact (ModuleCat.extendScalarsAlgebraMapIso_inv_naturality_assoc _ _).trans <|
    congrArg (_ ≫ ·) <| ((reassoc_of% h) _).trans <|
      congrArg (_ ≫ ·) (SSet.homologyExtendScalarsIso_hom_naturality _ (algebraMap R S) n)

/-- For a flat `R`-algebra `S`, the homology with coefficients in `S` vanishes exactly when the
extension of scalars of the homology with coefficients in `R` does. -/
theorem subsingleton_singularChains_homology_iff_tensorProduct [Module.Flat R S]
    (X : TopCat.{u}) (n : ℕ) :
    Subsingleton (((singularChains S).obj X).homology n) ↔
      Subsingleton (S ⊗[R] ((singularChains R).obj X).homology n) :=
  (singularHomologyTensorIso R S X n).toLinearEquiv.toEquiv.subsingleton_congr.symm

/-- **Homology with localized coefficients detects torsion.** For a localization `S` of `R` at a
submonoid `M`, the singular homology `Hₙ(X; R)` is `M`-torsion, every class being killed by an
element of `M`, exactly when `Hₙ(X; S)` vanishes. -/
theorem isTorsion'_singularChains_homology_iff (M : Submonoid R) [IsLocalization M S]
    (X : TopCat.{u}) (n : ℕ) :
    Module.IsTorsion' (((singularChains R).obj X).homology n) M ↔
      Subsingleton (((singularChains S).obj X).homology n) := by
  have := IsLocalization.flat S M
  rw [subsingleton_singularChains_homology_iff_tensorProduct R S]
  exact M.isTorsion'_iff_subsingleton_tensorProduct S

/-- The case `R = ℤ` of `TauCeti.isTorsion'_singularChains_homology_iff`, for the canonical action
of `ℤ` on the abelian group `Hₙ(X; ℤ)`: for a localization `k` of `ℤ` at a submonoid `S`, every
class of `Hₙ(X; ℤ)` is killed by an element of `S` exactly when `Hₙ(X; k)` vanishes. -/
theorem isTorsion'_singularChains_int_homology_iff (S : Submonoid ℤ) (k : Type) [CommRing k]
    [Algebra ℤ k] [IsLocalization S k] (X : TopCat.{0}) (n : ℕ) :
    Module.IsTorsion' (((singularChains ℤ).obj X).homology n) S ↔
      Subsingleton (((singularChains k).obj X).homology n) := by
  rw [← isTorsion'_singularChains_homology_iff ℤ k S X n]
  -- An element of `S` acts through its value in `ℤ`, and the scalar action of `ℤ` from
  -- `ModuleCat ℤ` is the canonical action of the abelian group.
  refine ⟨fun h x ↦ (@h x).imp fun _ ha ↦ ?_, fun h x ↦ (@h x).imp fun _ ha ↦ ?_⟩
  · simp only [Submonoid.smul_def] at ha ⊢
    exact (int_smul_eq_zsmul _ _ _).trans ha
  · simp only [Submonoid.smul_def] at ha ⊢
    exact (int_smul_eq_zsmul _ _ _).symm.trans ha

/-- **Rational homology detects torsion in integral homology.** The integral singular homology
`Hₙ(X; ℤ)` of a space in the lowest universe is a torsion group exactly when its rational homology
`Hₙ(X; ℚ)` vanishes. -/
theorem isAddTorsion_singularChains_homology_iff (X : TopCat.{0}) (n : ℕ) :
    IsAddTorsion (((singularChains ℤ).obj X).homology n) ↔
      Subsingleton (((singularChains ℚ).obj X).homology n) :=
  isAddTorsion_iff_isTorsion_int.trans
    (isTorsion'_singularChains_int_homology_iff (nonZeroDivisors ℤ) ℚ X n)

end TauCeti
