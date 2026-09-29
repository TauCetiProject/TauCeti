/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard

/-!
# Cartier divisors with trivial line bundle

On an integral scheme, `𝒪_X(D)` is trivial if and only if `D` is principal.
This identifies the kernel of the Cartier-divisor-to-line-bundle-class map, the
injectivity input to the Cartier class group–Picard group dictionary.

A global basis of `𝒪_X(D)` gives a nonzero rational function `q`. On an open set
with local equation `f`, both `q` and `f⁻¹` generate the same free rank-one module,
so `f q` is a regular unit. Thus `D` is the principal divisor of `q⁻¹`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.15.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

noncomputable section

universe u

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

open _root_.AlgebraicGeometry.Scheme.Modules

/-- A local equation times a global basis of `𝒪_X(D)`, viewed as a rational function,
is a regular unit. -/
private lemma exists_unit_of_unitIsoSheaf
    (e : (𝟙_ X.Modules) ≅ D.sheaf)
    {U : X.Opens} [Nonempty U] {f : X.functionFieldˣ}
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    ∃ r : Γ(X, U)ˣ, X.germToFunctionField U r =
      f * rationalFunctionsEquiv ⊤
        (Hom.app D.sheafι ⊤ (Hom.app e.hom ⊤ (1 : Γ(X, ⊤)))) := by
  let q := rationalFunctionsEquiv ⊤
    (Hom.app D.sheafι ⊤ (Hom.app e.hom ⊤ (1 : Γ(X, ⊤))))
  have he (a : Γ(X, U)) :
      rationalFunctionsEquiv U (Hom.app D.sheafι U (Hom.app e.hom U a)) =
        X.germToFunctionField U a * q :=
    Hom.rationalFunctionsEquiv_app_unit (e.hom ≫ D.sheafι) U a
  obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq le_rfl hf).mp
    (sheafι_app_mem D U (Hom.app e.hom U (1 : Γ(X, U))))
  rw [he, map_one, one_mul] at ha
  have hfinv : (rationalFunctionsEquiv U).symm (f⁻¹ : X.functionFieldˣ) ∈
      D.sections U := by
    apply (mem_sections_iff_of_rationalUnitClass_eq le_rfl hf).mpr
    exact ⟨1, by simp⟩
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (Hom.app e.hom U)).surjective
    (sectionMk _ hfinv)
  -- Sections of the monoidal unit are regular functions.
  change Γ(X, U) at b
  have hb' : X.germToFunctionField U b * q = (f⁻¹ : X.functionFieldˣ) := by
    rw [← he, hb, sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]
  have hab : a * b = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul, ha, map_one]
    calc
      _ = (f : X.functionField) * (X.germToFunctionField U b * q) := by ring
      _ = 1 := by
        rw [hb']
        simp
  exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

/-- **A Cartier divisor with trivial associated line bundle is principal.**
No Noetherian, dimension, or regularity hypothesis is needed. -/
theorem exists_principalCartierDivisor_eq_of_nonempty_iso
    (h : Nonempty ((𝟙_ X.Modules) ≅ D.sheaf)) :
    ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D := by
  obtain ⟨e⟩ := h
  let q := rationalFunctionsEquiv ⊤
    (Hom.app D.sheafι ⊤ (Hom.app e.hom ⊤ (1 : Γ(X, ⊤))))
  have hq : q ≠ 0 := by
    intro hq
    have hz : Hom.app D.sheafι ⊤ (Hom.app e.hom ⊤ (1 : Γ(X, ⊤))) = 0 := by
      apply (rationalFunctionsEquiv ⊤).injective
      exact hq.trans (map_zero _).symm
    have hone : (1 : Γ(X, ⊤)) = 0 :=
      (ConcreteCategory.bijective_of_isIso (Hom.app e.hom ⊤)).injective
        ((sheafι_app_injective D ⊤
          (hz.trans (map_zero (Hom.app D.sheafι ⊤).hom).symm)).trans
            (map_zero (Hom.app e.hom ⊤).hom).symm)
    exact one_ne_zero hone
  let g : X.functionFieldˣ := (Units.mk0 q hq)⁻¹
  refine ⟨g, TopCat.Presheaf.IsSheaf.section_ext (cartierDivisorSheaf X).property fun x _ ↦ ?_⟩
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨U, hx, hf⟩ := isLocalEquationAt_iff.mp hf
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨r, hr⟩ := exists_unit_of_unitIsoSheaf e hf
  refine ⟨U, le_top, hx, ?_⟩
  -- Restriction notation displays the components of the Cartier-divisor sheaf.
  change (principalCartierDivisor X g) |_ U = D |_ U
  rw [principalCartierDivisor_restrict, ← hf]
  symm
  apply (rationalUnitClass_eq_rationalUnitClass_iff X U f g).mpr
  refine ⟨r, Units.ext ?_⟩
  rw [Units.val_mul, regularUnitToFunctionField_apply]
  -- The chosen unit `g` is the inverse of the nonzero rational basis function `q`.
  change X.germToFunctionField U r * q⁻¹ = f
  rw [hr]
  exact mul_inv_cancel_right₀ hq _

/-- **The kernel of the Cartier-divisor-to-line-bundle-class map consists of principal
Cartier divisors.** -/
theorem toLineBundleClass_eq_one_iff :
    D.toLineBundleClass = 1 ↔ ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D := by
  constructor
  · intro h
    rw [toLineBundleClass_eq_mk, LineBundleClass.mk_eq_one_iff, toInvertibleSheaf_obj] at h
    obtain ⟨e⟩ := h
    exact exists_principalCartierDivisor_eq_of_nonempty_iso ⟨e.symm⟩
  · rintro ⟨f, rfl⟩
    exact toLineBundleClass_principalCartierDivisor f

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
