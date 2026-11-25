/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.FiniteDimensional
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.FiniteDimensional
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.PointTwist
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence
public import TauCeti.Topology.Sheaves.Cech.Skyscraper
import TauCeti.LinearAlgebra.Exact

/-!
# The cohomology sequence of a point twist

For a divisor `D` on a compact Hausdorff complex curve and a point `x`, the point-twist
sequence gives the six-term exact sequence

`0 → O(D)(X) → O(D+x)(X) → ℂ → H¹(O(D)) → H¹(O(D+x)) → 0`.

Here cohomology is cover-colimit Čech cohomology with complex-vector-space coefficients.
The scalar map is the actual newly permitted coordinate coefficient, not an abstract quotient
map. The sequence ends because a skyscraper has no positive Čech cohomology, not because of
any assumption on the cohomological dimension of the curve. No finiteness of `H¹` is assumed
in the exactness statements. Consequently finiteness of the first cohomology is unchanged by
adding a point; when it is finite, adding a point raises `h⁰ - h¹` by one. These are the
point-twist steps in the Euler-characteristic calculation for divisor sheaves.

The cohomology of `O(0)` is that of the holomorphic structure sheaf
(`TauCeti.RiemannSurface.divisorCechCohomologyZeroIso`). Since every divisor is reached from `0`
by point twists, finiteness of `H¹(O(D))` does not depend on `D`
(`TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_one_iff`). On a compact Hausdorff
Riemann surface `H¹(X, 𝒪)` is finite-dimensional
(`TauCeti.RiemannSurface.finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules`),
so `H¹(O(D))` is finite-dimensional for every divisor
(`TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_one`).

On a compact connected curve the degree-zero cohomology of `𝒪(D)` has the dimension of its global
sections (`TauCeti.RiemannSurface.finrank_divisorCechCohomology_zero`).

Where `D + [x]` vanishes at `x`, the new coefficient of a global section is its value at `x`
(`TauCeti.RiemannSurface.pointTwistGlobalCoefficient_eq_apply`). On a compact connected curve
`h⁰(𝒪) = 1`, so the coefficient map of the sequence for `𝒪(-[x]) → 𝒪` is bijective.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Cover-colimit Čech cohomology of the divisor sheaf, with its complex vector space
structure. In degree zero it identifies with the divisor's global sections. -/
abbrev divisorCechCohomology (D : WeilDivisor X) (n : ℕ) : ModuleCat.{0} ℂ :=
  (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj (divisorSheaf D).obj

/-- Degree-zero divisor cohomology has the dimension of the divisor's global sections. -/
@[simp]
theorem finrank_divisorCechCohomology_zero (D : WeilDivisor X) :
    Module.finrank ℂ (divisorCechCohomology D 0) =
      Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) :=
  (cechCohomologyZeroIso (divisorSheaf D)).toLinearEquiv.finrank_eq.symm

/-- On a compact connected complex curve, degree-zero divisor cohomology is
finite-dimensional. -/
instance finiteDimensional_divisorCechCohomology_zero [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
    [CompactSpace X] (D : WeilDivisor X) :
    FiniteDimensional ℂ (divisorCechCohomology D 0) :=
  (cechCohomologyZeroIso (divisorSheaf D)).toLinearEquiv.finiteDimensional

variable (D : WeilDivisor X) (x : X)

/-- The new coordinate coefficient of a global section of `O(D+x)`. -/
def pointTwistGlobalCoefficient :
    (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤) →ₗ[ℂ] ℂ :=
  (divisorSections.pointTwistCoefficient D ⊤ ⟨x, trivial⟩).comp
    (divisorSheafSectionsEquiv _ ⊤).toLinearMap

/-- The global coefficient is computed by the native divisor-section coefficient map. -/
@[simp]
theorem pointTwistGlobalCoefficient_apply
    (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) :
    pointTwistGlobalCoefficient D x f = divisorSections.pointTwistCoefficient D ⊤
      ⟨x, trivial⟩ (divisorSheafSectionsEquiv _ ⊤ f) := (rfl)

open Classical in
private def skyscraperSectionsIso :
    (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj.obj (op ⊤) ≅
      ModuleCat.of ℂ ℂ :=
  skyscraperSheafGlobalSectionsIso (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ)) ≪≫
    (ULift.moduleEquiv : ULift ℂ ≃ₗ[ℂ] ℂ).toModuleIso

open Classical in
private theorem coefficient_comp_skyscraperSectionsIso :
    ModuleCat.ofHom (pointTwistGlobalCoefficient D x) ≫ (skyscraperSectionsIso x).inv =
      (pointTwistMap D x).hom.app (op ⊤) := by
  apply (cancel_mono (skyscraperSectionsIso x).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [skyscraperSectionsIso, Iso.trans_hom, skyscraperSheafGlobalSectionsIso_hom]
  ext f
  simpa [pointTwistGlobalCoefficient] using
    congrArg ULift.down (pointTwistMap_app_apply_of_mem D x (U := ⊤) trivial f).symm

/-- The map on Čech cohomology induced by the inclusion `O(D) → O(D+x)`. -/
def pointTwistCohomologyMap (n : ℕ) :
    divisorCechCohomology D n →ₗ[ℂ] divisorCechCohomology (D + WeilDivisor.ofPoint x) n :=
  ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
    (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom).hom

/-- The map on cohomology is induced by the native divisor inclusion. -/
theorem pointTwistCohomologyMap_def (n : ℕ) :
    pointTwistCohomologyMap D x n =
      ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom).hom := (rfl)

variable {D x} in
/-- Where `D + [x]` vanishes at `x`, the newly permitted coefficient at `x` of a global section of
`𝒪(D + [x])` is its value at `x`. -/
theorem pointTwistGlobalCoefficient_eq_apply (hD : D x = -1)
    (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) :
    pointTwistGlobalCoefficient D x f = (divisorSheafSectionsEquiv _ ⊤ f).val ⟨x, trivial⟩ :=
  divisorSections.pointTwistCoefficient_eq_apply (x := ⟨x, trivial⟩) hD _

variable [IsManifold 𝓘(ℂ) 1 X]

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- At a twist of `-[x]`, every scalar is the newly permitted coefficient of a global section of
`𝒪(-[x] + [x])`. -/
theorem pointTwistGlobalCoefficient_neg_ofPoint_surjective :
    Function.Surjective (pointTwistGlobalCoefficient (-WeilDivisor.ofPoint x) x) := fun c ↦
  ⟨(divisorSheafSectionsEquiv _ ⊤).symm ⟨(fun _ : X ↦ c) ∘ Subtype.val,
      comp_val_mem_divisorSections fun _ _ ↦
        (isDivisorSectionAt_iff_of_eq_zero (by simp)).2 contMDiffAt_const⟩, by
    have h₁ : (WeilDivisor.ofPoint x) x = 1 := WeilDivisor.coeff_ofPoint_self x
    rw [pointTwistGlobalCoefficient_eq_apply (by simp [h₁]), LinearEquiv.apply_symm_apply]
    rfl⟩

variable (X) in
/-- The Čech cohomology of the divisor sheaf `𝒪(0)` is that of the structure sheaf, through the
identification `𝒪(0) ≅ 𝒪` of sheaves. -/
def divisorCechCohomologyZeroIso (n : ℕ) :
    divisorCechCohomology (0 : WeilDivisor X) n ≅
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj :=
  (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapIso
    ((sheafToPresheaf _ _).mapIso (divisorSheafZeroIso X))

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The isomorphism `Hⁿ(X, 𝒪(0)) ≅ Hⁿ(X, 𝒪)` is the map on cohomology induced by `𝒪(0) ≅ 𝒪`. -/
@[simp]
theorem divisorCechCohomologyZeroIso_hom (n : ℕ) :
    (divisorCechCohomologyZeroIso X n).hom =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map (divisorSheafZeroIso X).hom.hom :=
  (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The inverse of `Hⁿ(X, 𝒪(0)) ≅ Hⁿ(X, 𝒪)` is the map on cohomology induced by `𝒪 ≅ 𝒪(0)`. -/
@[simp]
theorem divisorCechCohomologyZeroIso_inv (n : ℕ) :
    (divisorCechCohomologyZeroIso X n).inv =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map (divisorSheafZeroIso X).inv.hom :=
  (rfl)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- `Hⁿ(X, 𝒪(0))` is finite-dimensional exactly when `Hⁿ(X, 𝒪)` is. -/
theorem finiteDimensional_divisorCechCohomology_zero_iff (n : ℕ) :
    FiniteDimensional ℂ (divisorCechCohomology (0 : WeilDivisor X) n) ↔
      FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) :=
  ⟨fun _ ↦ (divisorCechCohomologyZeroIso X n).toLinearEquiv.finiteDimensional,
    fun _ ↦ (divisorCechCohomologyZeroIso X n).toLinearEquiv.symm.finiteDimensional⟩

open Classical in
private theorem displayedPointTwist_shortExact :
    (ShortComplex.mk (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x))
      (pointTwistMap D x) (divisorSheafMapOfLE_comp_pointTwistMap D x)).ShortExact :=
  ShortComplex.shortExact_of_iso (pointTwistSequenceIso D x) (pointTwistSequence_shortExact D x)

/-- A global section of `O(D+x)` comes from `O(D)` exactly when its new coefficient vanishes. -/
theorem exact_pointTwist_globalSections_coefficient :
    Function.Exact ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app (op ⊤))
      (pointTwistGlobalCoefficient D x) := by
  classical
  have hS := displayedPointTwist_shortExact D x
  have := hS.mono_f
  have h := hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ (ModuleCat ℂ)).obj (op ⊤))
    inferInstance inferInstance
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
  -- Expose the evaluated short-complex maps so the coefficient comparison can rewrite them.
  change Function.Exact
    ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app (op ⊤)).hom
    ((pointTwistMap D x).hom.app (op ⊤)).hom at he
  rw [← coefficient_comp_skyscraperSectionsIso] at he
  exact ((ModuleCat.mono_iff_injective (skyscraperSectionsIso x).inv).mp
    inferInstance).comp_exact_iff_exact.mp he

section Compact

variable [CompactSpace X] [ConnectedSpace X]

/-- On a compact connected complex curve, in the six-term sequence of `𝒪(-[x]) → 𝒪`, the
coefficient map `H⁰(𝒪(-[x] + [x])) → ℂ` is bijective. -/
theorem pointTwistGlobalCoefficient_neg_ofPoint_bijective :
    Function.Bijective (pointTwistGlobalCoefficient (-WeilDivisor.ofPoint x) x) := by
  have hs := pointTwistGlobalCoefficient_neg_ofPoint_surjective x
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hs, hs⟩
  rw [neg_add_cancel, finrank_divisorSheaf_zero, Module.finrank_self]

end Compact

open Classical in
/-- Scalar coefficients identify with the degree-zero cohomology of the point skyscraper. -/
def pointTwistCoefficientCechIso : ModuleCat.of ℂ ℂ ≅
    (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj :=
  (ULift.moduleEquiv : ULift ℂ ≃ₗ[ℂ] ℂ).toModuleIso.symm ≪≫
    (cechCohomologyZeroSkyscraperPresheafIso (X := TopCat.of X)
      (A := ModuleCat.{0} ℂ) x (ModuleCat.of ℂ (ULift ℂ))).symm

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] in
open Classical in
/-- The coefficient identification is the inverse skyscraper cohomology identification,
after lifting the scalar to the coefficient universe. -/
theorem pointTwistCoefficientCechIso_def :
    pointTwistCoefficientCechIso x =
      (ULift.moduleEquiv : ULift ℂ ≃ₗ[ℂ] ℂ).toModuleIso.symm ≪≫
        (cechCohomologyZeroSkyscraperPresheafIso (X := TopCat.of X)
          (A := ModuleCat.{0} ℂ) x (ModuleCat.of ℂ (ULift ℂ))).symm := by rfl

variable [CompactSpace X] [T2Space X]

/-- The point-twist connecting map sends a prescribed new coefficient to its obstruction to
being realized by a global section of `O(D+x)`. -/
def pointTwistConnecting : ℂ →ₗ[ℂ] divisorCechCohomology D 1 :=
  ((pointTwistCoefficientCechIso x).hom ≫
    (displayedPointTwist_shortExact D x).cechCohomologyδ 0).hom

open Classical in
/-- The point-twist obstruction is the Čech boundary of the scalar coefficient, using the
public skyscraper identification and the point-twist short exact sequence. -/
theorem pointTwistConnecting_def :
    pointTwistConnecting D x =
      ((pointTwistCoefficientCechIso x).hom ≫
        (ShortComplex.shortExact_of_iso (pointTwistSequenceIso D x)
          (pointTwistSequence_shortExact D x)).cechCohomologyδ 0).hom := by rfl

omit [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X] in
open Classical in
private theorem coefficient_augmentation :
    ModuleCat.ofHom (pointTwistGlobalCoefficient D x) ≫ (pointTwistCoefficientCechIso x).hom =
      (cechCohomologyZeroIso (divisorSheaf (D + WeilDivisor.ofPoint x))).hom ≫
        (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).map (pointTwistMap D x).hom := by
  rw [pointTwistCoefficientCechIso, cechCohomologyZeroSkyscraperPresheafIso_eq]
  -- Reassociate the isomorphisms to use the global-section coefficient comparison.
  change ModuleCat.ofHom (pointTwistGlobalCoefficient D x) ≫
    ((skyscraperSectionsIso x).symm ≪≫ cechCohomologyZeroIso _).hom = _
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    coefficient_comp_skyscraperSectionsIso, cechCohomologyZeroIso_hom_naturality]

/-- A scalar is realized as the new coefficient of a global section if and only if its
point-twist obstruction vanishes. -/
theorem exact_pointTwist_coefficient_connecting :
    Function.Exact (pointTwistGlobalCoefficient D x) (pointTwistConnecting D x) := by
  classical
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((displayedPointTwist_shortExact D x).cechCohomology_exact₃ 0)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := (cechCohomologyZeroIso
      (divisorSheaf (D + WeilDivisor.ofPoint x))).toLinearEquiv)
    (e₂ := (pointTwistCoefficientCechIso x).toLinearEquiv)
    (e₃ := LinearEquiv.refl ℂ _)
    (congrArg ModuleCat.Hom.hom (coefficient_augmentation D x)).symm
    (by rfl)).mp he

/-- The kernel of `H¹(O(D)) → H¹(O(D+x))` consists exactly of the coefficient obstructions. -/
theorem exact_pointTwist_connecting_cohomologyMap :
    Function.Exact (pointTwistConnecting D x) (pointTwistCohomologyMap D x 1) := by
  classical
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((displayedPointTwist_shortExact D x).cechCohomology_exact₁ 0)
  exact (LinearEquiv.precomp_exact_iff_exact
    (e := (pointTwistCoefficientCechIso x).toLinearEquiv)).mpr he

/-- The point-twist sequence ends at `H¹(O(D+x))`: the coefficient skyscraper has vanishing
positive Čech cohomology. -/
theorem pointTwistCohomologyMap_one_surjective :
    Function.Surjective (pointTwistCohomologyMap D x 1) := by
  classical
  have hz := isZero_cechCohomology_skyscraperPresheaf (X := TopCat.of X)
    x (ModuleCat.of ℂ (ULift ℂ)) 0
  have he := (displayedPointTwist_shortExact D x).cechCohomology_exact₂ 1
  have hep := (ShortComplex.exact_iff_epi _ (hz.eq_zero_of_tgt _)).mp he
  exact (ModuleCat.epi_iff_surjective _).mp hep

/-- Finiteness of the first divisor cohomology is unchanged by adding a point. This does not
assert finiteness for any initial divisor. -/
theorem finiteDimensional_divisorCechCohomology_one_add_point_iff :
    FiniteDimensional ℂ (divisorCechCohomology (D + WeilDivisor.ofPoint x) 1) ↔
      FiniteDimensional ℂ (divisorCechCohomology D 1) := by
  constructor
  · intro h
    exact (exact_pointTwist_connecting_cohomologyMap D x).moduleFinite
  · intro h
    exact FiniteDimensional.of_surjective (pointTwistCohomologyMap D x 1)
      (pointTwistCohomologyMap_one_surjective D x)

/-- **Finiteness of `H¹(X, 𝒪(D))` does not depend on `D`.** No finiteness is asserted for any
divisor. -/
theorem finiteDimensional_divisorCechCohomology_one_iff (D E : WeilDivisor X) :
    FiniteDimensional ℂ (divisorCechCohomology D 1) ↔
      FiniteDimensional ℂ (divisorCechCohomology E 1) := by
  suffices h : ∀ D : WeilDivisor X, FiniteDimensional ℂ (divisorCechCohomology D 1) ↔
      FiniteDimensional ℂ (divisorCechCohomology (0 : WeilDivisor X) 1) from (h D).trans (h E).symm
  exact WeilDivisor.induction_add_ofPoint Iff.rfl fun D x ↦ by
    rw [finiteDimensional_divisorCechCohomology_one_add_point_iff]

/-- On a compact Hausdorff Riemann surface, `H¹(X, 𝒪(D))` is finite-dimensional for every
divisor `D`, since `H¹(X, 𝒪)` is. -/
instance finiteDimensional_divisorCechCohomology_one (D : WeilDivisor X) :
    FiniteDimensional ℂ (divisorCechCohomology D 1) :=
  (finiteDimensional_divisorCechCohomology_one_iff D 0).mpr
    ((finiteDimensional_divisorCechCohomology_zero_iff 1).mpr inferInstance)

/-- The point-twist step of the Euler characteristic calculation: on a compact connected
Riemann surface, adding a point raises `h⁰ - h¹` by one. -/
theorem finrank_pointTwist_euler_characteristic [ConnectedSpace X] :
    (Module.finrank ℂ ((divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology (D + WeilDivisor.ofPoint x) 1) =
      (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology D 1) + 1 := by
  let f := ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app (op ⊤)).hom
  have hf : Function.Injective f := (ModuleCat.mono_iff_injective _).mp inferInstance
  have h₀ := f.finrank_eq_finrank_range_add_finrank_range_of_exact
    (pointTwistGlobalCoefficient D x) (exact_pointTwist_globalSections_coefficient D x)
  rw [LinearMap.finrank_range_of_inj hf] at h₀
  have h₁ := (pointTwistGlobalCoefficient D x).finrank_eq_finrank_range_add_finrank_range_of_exact
    (pointTwistConnecting D x) (exact_pointTwist_coefficient_connecting D x)
  rw [Module.finrank_self] at h₁
  have h₂ := (pointTwistConnecting D x).finrank_eq_finrank_range_add_finrank_range_of_exact
    (pointTwistCohomologyMap D x 1) (exact_pointTwist_connecting_cohomologyMap D x)
  rw [LinearMap.range_eq_top.mpr (pointTwistCohomologyMap_one_surjective D x),
    finrank_top] at h₂
  omega

end TauCeti.RiemannSurface
