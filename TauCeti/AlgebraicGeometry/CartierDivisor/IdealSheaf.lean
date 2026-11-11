/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Characterization
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image

/-!
# The ideal sheaf of an effective Cartier divisor

On an integral scheme, an effective Cartier divisor given by rational local equations
cuts out a closed subscheme with invertible ideal sheaf. Its ideal is `𝒪_X(-D)`, and
hence its ideal line-bundle class is the inverse of the class of `𝒪_X(D)`.

This comparison allows computations with rational Cartier divisors to be used with the
closed-subscheme restriction sequences for effective Cartier divisors. No regularity,
dimension or Noetherian hypothesis is imposed on the integral scheme.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6.
* The Stacks Project, *Divisors*, Tag 01WQ.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

/-- The closed-subscheme ideal sheaf of an effective Cartier divisor, with ideal module
`𝒪_X(-D)`. -/
def IsEffective.idealSheaf (hD : D.IsEffective) : X.IdealSheafData :=
  hD.sheafToUnit.imageIdealSheaf

/-- The ideal sheaf of an effective Cartier divisor is canonically `𝒪_X(-D)`. -/
def IsEffective.idealSheafIso (hD : D.IsEffective) : (-D).sheaf ≅ hD.idealSheaf.sheaf :=
  hD.sheafToUnit.imageIdealSheafIso

/-- The ideal-sheaf isomorphism respects the inclusions into rational functions. -/
@[simp, reassoc]
lemma IsEffective.idealSheafIso_hom_ι (hD : D.IsEffective) :
    hD.idealSheafIso.hom ≫ hD.idealSheaf.sheafι ≫ Scheme.toRationalFunctions X =
      (-D).sheafι := by
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ Scheme.toRationalFunctions X)
      hD.sheafToUnit.imageIdealSheafIso_hom_ι).trans hD.sheafToUnit_toRationalFunctions

/-- A regular function belongs to the ideal of `D` exactly when, as a rational section,
it belongs to `𝒪_X(-D)`. This holds on arbitrary opens. -/
@[simp]
lemma IsEffective.mem_idealSheaf_sections_iff (hD : D.IsEffective) (U : X.Opens)
    (a : Γ(X, U)) :
    a ∈ hD.idealSheaf.sections U ↔
      (Scheme.toRationalFunctions X).app U a ∈ (-D).sections U := by
  have hm : a ∈ hD.idealSheaf.sections U ↔ ∃ t, hD.sheafToUnit.app U t = a := by
    rw [IsEffective.idealSheaf, Scheme.Modules.Hom.imageIdealSheaf_sections,
      Scheme.Modules.Hom.mem_imageIdeal]
  refine hm.trans ⟨?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact (hD.toRationalFunctions_app_sheafToUnit_app U t).symm ▸ (-D).sheafι_app_mem U t
  · intro ha
    refine ⟨sectionMk _ ha, Scheme.toRationalFunctions_app_injective U ?_⟩
    exact (hD.toRationalFunctions_app_sheafToUnit_app U _).trans (sheafι_app_sectionMk _ ha)

/-- On an affine open, the ideal is characterized by membership in `𝒪_X(-D)`. -/
@[simp]
lemma IsEffective.mem_idealSheaf_ideal_iff (hD : D.IsEffective) (U : X.affineOpens)
    (a : Γ(X, U)) :
    a ∈ hD.idealSheaf.ideal U ↔
      (Scheme.toRationalFunctions X).app U.1 a ∈ (-D).sections U.1 :=
  (congrArg (a ∈ ·) (hD.idealSheaf.sections_eq_ideal U)).to_iff.symm.trans
    (hD.mem_idealSheaf_sections_iff U.1 a)

/-- On an affine open carrying a regular equation `a` of `D`, the ideal of the
closed subscheme is exactly `(a)`. -/
lemma IsEffective.idealSheaf_ideal_eq_span (hD : D.IsEffective) (U : X.affineOpens)
    [Nonempty U.1] {f : X.functionFieldˣ}
    (hf : Scheme.rationalUnitClass X U.1 (Additive.ofMul f) = D |_ U.1)
    {a : Γ(X, U)} (ha : X.germToFunctionField U.1 a = f) :
    hD.idealSheaf.ideal U = Ideal.span {a} := by
  ext s
  rw [hD.mem_idealSheaf_ideal_iff,
    mem_sections_iff_of_rationalUnitClass_eq le_rfl (rationalUnitClass_inv_eq_neg_of_eq hf),
    Scheme.rationalFunctionsEquiv_toRationalFunctions_app, Ideal.mem_span_singleton']
  refine exists_congr fun b ↦ ?_
  rw [← (X.germToFunctionField_injective U.1).eq_iff, map_mul, ha]
  exact ⟨fun h ↦ by rw [h]; simp [mul_comm],
    fun h ↦ by rw [← h]; simp [mul_comm]⟩

/-- The zero Cartier divisor cuts out the empty closed subscheme. -/
@[simp]
lemma IsEffective.idealSheaf_zero (h : (0 : CartierDivisor X).IsEffective) :
    h.idealSheaf = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply eq_top_iff.mpr
  intro a _
  apply (h.mem_idealSheaf_ideal_iff U a).mpr
  simpa using (isEffective_iff_toRationalFunctions_mem_sections.mp isEffective_zero U.1 a)

/-- The ideal obtained from rational local equations is an effective Cartier ideal sheaf. -/
theorem IsEffective.isEffectiveCartier_idealSheaf (hD : D.IsEffective) :
    hD.idealSheaf.IsEffectiveCartier := by
  apply (Scheme.IdealSheafData.isEffectiveCartier_iff_isInvertible_sheaf hD.idealSheaf).mpr
  exact (SheafOfModules.isInvertible X).prop_of_iso hD.idealSheafIso
    (isInvertible_sheaf (-D))

/-- The ideal line bundle of the closed subscheme cut out by `D` has class `[𝒪_X(D)]⁻¹`.
In particular its dual, the bundle used by the effective-divisor Abel map, has class `[𝒪_X(D)]`. -/
theorem IsEffective.mk_idealSheaf_eq_inv (hD : D.IsEffective) :
    LineBundleClass.mk hD.isEffectiveCartier_idealSheaf.toInvertibleSheaf =
      D.toLineBundleClass⁻¹ := by
  exact ((toLineBundleClass_eq_mk_iff (D := -D)
    (L := hD.isEffectiveCartier_idealSheaf.toInvertibleSheaf)).mpr
      ⟨hD.idealSheafIso ≪≫
        (eqToIso hD.isEffectiveCartier_idealSheaf.toInvertibleSheaf_obj).symm⟩).symm.trans
    (toLineBundleClass_neg D)

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
