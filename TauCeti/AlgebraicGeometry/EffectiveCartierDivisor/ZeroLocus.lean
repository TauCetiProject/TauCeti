/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Characterization
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Hom
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation

/-!
# Effective Cartier divisors from nonzero sections

A nonzero functional on a line bundle on an integral scheme identifies that line bundle
with an effective Cartier ideal. Applying this to evaluation at a nonzero section of `L`
gives an effective Cartier divisor `D` with `𝒪_X(-D)` of class `L⁻¹`. This construction also
works on singular integral schemes; it does not require a Weil divisor theory or regular
local rings. It supplies effective divisors for the degree and positivity theory of curves.

## References

* The Stacks Project, Section 31.14, *Effective Cartier divisors and invertible sheaves*,
  especially Lemma 31.14.10 (Tag 01X0).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (L : InvertibleSheaf X)
  (φ : L.obj ⟶ 𝟙_ X.Modules)

/-- The image of an embedding of a line bundle in the structure sheaf is an effective
Cartier ideal. This statement works on arbitrary schemes. -/
theorem isEffectiveCartier_imageIdealSheaf [Mono φ] : φ.imageIdealSheaf.IsEffectiveCartier := by
  have := (SheafOfModules.isInvertible X).prop_of_iso φ.imageIdealSheafIso L.property
  exact Scheme.IdealSheafData.isEffectiveCartier_of_isInvertible_sheaf _

/-- The effective Cartier ideal obtained from an embedded line bundle has the original
line-bundle class. -/
@[simp]
theorem mk_toInvertibleSheaf_imageIdealSheaf [Mono φ] :
    LineBundleClass.mk (L.isEffectiveCartier_imageIdealSheaf φ).toInvertibleSheaf =
      LineBundleClass.mk L := by
  apply LineBundleClass.mk_eq_mk_iff.mpr
  exact ⟨eqToIso (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj _) ≪≫
    φ.imageIdealSheafIso.symm⟩

variable [IsIntegral X]

/-- A nonzero section of a line bundle on an integral scheme gives an effective Cartier
ideal whose associated line-bundle class is the inverse of the original class. -/
theorem exists_isEffectiveCartier_of_ne_zero (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      LineBundleClass.mk hI.toInvertibleSheaf = (LineBundleClass.mk L)⁻¹ := by
  let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  -- Retype the scheme-module wrapper so that the site-level freeness instances apply.
  let M : SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs M.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs M.IsFiniteType
  let φ₀ := (Scheme.Modules.dualHomUnitEquiv L.obj).symm (L.obj.unitHomEquivTop.symm s)
  have hφ₀ : φ₀ ≠ 0 := by
    intro hz
    have hrec := congrArg L.obj.unitHomEquivTop
      ((Scheme.Modules.dualHomUnitEquiv L.obj).apply_symm_apply (L.obj.unitHomEquivTop.symm s))
    apply hs
    calc
      s = L.obj.unitHomEquivTop (Scheme.Modules.dualHomUnitEquiv L.obj φ₀) :=
        (hrec.trans (L.obj.unitHomEquivTop.apply_symm_apply s)).symm
      _ = 0 := by
        simp only [hz, Scheme.Modules.dualHomUnitEquiv_zero, Scheme.Modules.unitHomEquivTop_zero]
  -- `dual_obj` compares the bundled dual with the internal Hom used by evaluation.
  let e : (dual L).obj ≅ (ihom L.obj).obj (𝟙_ X.Modules) := eqToIso (dual_obj L)
  let φ : (dual L).obj ⟶ 𝟙_ X.Modules := e.hom ≫ φ₀
  have hφ : φ ≠ 0 := fun hz ↦ hφ₀ ((Limits.comp_eq_zero_iff_of_epi e.hom).mp hz)
  have := (dual L).mono_of_ne_zero_to_unit φ hφ
  exact ⟨φ.imageIdealSheaf, (dual L).isEffectiveCartier_imageIdealSheaf φ,
    ((dual L).mk_toInvertibleSheaf_imageIdealSheaf φ).trans (LineBundleClass.inv_mk L).symm⟩

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
