/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.PointTwist
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence
public import TauCeti.Topology.Sheaves.Cech.Skyscraper
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.FiniteDimensional
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
  eqToIso ((skyscraperSheaf_obj_obj (X := TopCat.of X) x
    (ModuleCat.of ℂ (ULift ℂ)) (op ⊤)).trans
    (ite_eq_left (show x ∈ (⊤ : Opens X) from trivial))) ≪≫
      (ULift.moduleEquiv : ULift ℂ ≃ₗ[ℂ] ℂ).toModuleIso

open Classical in
private theorem coefficient_comp_skyscraperSectionsIso :
    ModuleCat.ofHom (pointTwistGlobalCoefficient D x) ≫ (skyscraperSectionsIso x).inv =
      (pointTwistMap D x).hom.app (op ⊤) := by
  apply (cancel_mono (skyscraperSectionsIso x).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [skyscraperSectionsIso, Iso.trans_hom, eqToIso.hom]
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

variable [IsManifold 𝓘(ℂ) 1 X]

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
  intro f
  have hz : (pointTwistMap D x).hom.app (op ⊤) f = 0 ↔ pointTwistGlobalCoefficient D x f = 0 := by
    rw [← coefficient_comp_skyscraperSectionsIso, ConcreteCategory.comp_apply]
    have hi := (ModuleCat.mono_iff_injective (skyscraperSectionsIso x).inv).mp inferInstance
    simpa using hi.eq_iff (a := pointTwistGlobalCoefficient D x f) (b := 0)
  exact hz.symm.trans (he f)

variable [CompactSpace X] [T2Space X]

open Classical in
private def coefficientCechIso : ModuleCat.of ℂ ℂ ≅
    (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).obj
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ))).obj :=
  (skyscraperSectionsIso x).symm ≪≫ cechCohomologyZeroIso
    (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift ℂ)))

/-- The point-twist connecting map sends a prescribed new coefficient to its obstruction to
being realized by a global section of `O(D+x)`. -/
def pointTwistConnecting : ℂ →ₗ[ℂ] divisorCechCohomology D 1 :=
  ((coefficientCechIso x).hom ≫ (displayedPointTwist_shortExact D x).cechCohomologyδ 0).hom

omit [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X] in
open Classical in
private theorem coefficient_augmentation :
    ModuleCat.ofHom (pointTwistGlobalCoefficient D x) ≫ (coefficientCechIso x).hom =
      (cechCohomologyZeroIso (divisorSheaf (D + WeilDivisor.ofPoint x))).hom ≫
        (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 0).map (pointTwistMap D x).hom := by
  rw [coefficientCechIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    coefficient_comp_skyscraperSectionsIso, cechCohomologyZeroIso_hom_naturality]

/-- A scalar is realized as the new coefficient of a global section if and only if its
point-twist obstruction vanishes. -/
theorem exact_pointTwist_coefficient_connecting :
    Function.Exact (pointTwistGlobalCoefficient D x) (pointTwistConnecting D x) := by
  classical
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((displayedPointTwist_shortExact D x).cechCohomology_exact₃ 0)
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (he ((coefficientCechIso x).hom a)).mp ha
    refine ⟨(cechCohomologyZeroIso (divisorSheaf (D + WeilDivisor.ofPoint x))).inv b, ?_⟩
    apply (ModuleCat.mono_iff_injective (coefficientCechIso x).hom).mp inferInstance
    have hc := ConcreteCategory.congr_hom (coefficient_augmentation D x)
      ((cechCohomologyZeroIso (divisorSheaf (D + WeilDivisor.ofPoint x))).inv b)
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hc
    exact hc.trans hb
  · rintro ⟨b, rfl⟩
    apply (he _).mpr
    refine ⟨(cechCohomologyZeroIso (divisorSheaf (D + WeilDivisor.ofPoint x))).hom b, ?_⟩
    exact (ConcreteCategory.congr_hom (coefficient_augmentation D x) b).symm

/-- The kernel of `H¹(O(D)) → H¹(O(D+x))` consists exactly of the coefficient obstructions. -/
theorem exact_pointTwist_connecting_cohomologyMap :
    Function.Exact (pointTwistConnecting D x) (pointTwistCohomologyMap D x 1) := by
  classical
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((displayedPointTwist_shortExact D x).cechCohomology_exact₁ 0)
  intro c
  exact (he c).trans ⟨fun ⟨a, ha⟩ ↦ ⟨(coefficientCechIso x).inv a, by
    simpa only [pointTwistConnecting, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.Hom.hom, Iso.inv_hom_id_apply] using ha⟩,
    fun ⟨a, ha⟩ ↦ ⟨(coefficientCechIso x).hom a, ha⟩⟩

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
    exact finiteDimensional_of_exact (exact_pointTwist_connecting_cohomologyMap D x)
  · intro h
    exact FiniteDimensional.of_surjective (pointTwistCohomologyMap D x 1)
      (pointTwistCohomologyMap_one_surjective D x)

/-- The point-twist step of the Euler characteristic calculation: once the first cohomology
is finite-dimensional, adding a point raises `h⁰ - h¹` by one. The analytic finiteness theorem
is not assumed implicitly or asserted here. -/
theorem finrank_pointTwist_euler_characteristic [ConnectedSpace X]
    [FiniteDimensional ℂ (divisorCechCohomology D 1)] :
    (Module.finrank ℂ ((divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology (D + WeilDivisor.ofPoint x) 1) =
      (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) -
        Module.finrank ℂ (divisorCechCohomology D 1) + 1 := by
  have := (finiteDimensional_divisorCechCohomology_one_add_point_iff D x).mpr inferInstance
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
