/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LineBundle

/-!
# Comparing the Cartier and Weil divisor sheaves on a curve

On a Noetherian integral curve with discrete valuation rings at codimension-one points, a
Cartier divisor and its associated Weil divisor define the same subsheaf of rational functions.
Locally, a Cartier equation `f` makes a rational function `q` a section precisely when `f q` is
regular; the Weil condition says that the order of `f q` is nonnegative at every closed point.
The one-dimensional regularity criterion identifies these conditions.

The resulting isomorphism `𝒪_X(D) ≅ 𝒪_X(D_Weil)` commutes with both inclusions into the rational
function sheaf. It lets degree and cohomology computations on either presentation be used with the
other.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.11.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

/-- The Cartier and Weil conditions define the same rational-function sections on a curve. -/
theorem sections_eq_toWeilDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) (U : X.Opens) :
    D.sections U = SchemeWeilDivisor.sections D.toWeilDivisor U := by
  ext s
  constructor
  · intro hs
    apply SchemeWeilDivisor.mem_sections.mpr
    intro y hy
    have : Nonempty U := ⟨⟨y, hy⟩⟩
    by_cases hq : rationalFunctionsEquiv U s = 0
    · exact Or.inl hq
    right
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (y : X)
    obtain ⟨V, hyV, hV⟩ := isLocalEquationAt_iff.mp hf
    have : Nonempty V := ⟨⟨y, hyV⟩⟩
    let W : X.Opens := U ⊓ V
    have : Nonempty W := ⟨⟨y, hy, hyV⟩⟩
    let t := (rationalFunctions X).presheaf.map
      (homOfLE inf_le_left : W ⟶ U).op s
    have ht : t ∈ D.sections W := sections_map (homOfLE inf_le_left) hs
    obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq
      (W := W) inf_le_right hV).mp ht
    have hqW : rationalFunctionsEquiv W t = rationalFunctionsEquiv U s :=
      rationalFunctionsEquiv_map (homOfLE inf_le_left) s
    rw [hqW] at ha
    have hreg : 0 ≤ X.ord ((f : X.functionField) * rationalFunctionsEquiv U s) y := by
      rw [← ha]
      exact ord_germToFunctionField_nonneg a ⟨hy, hyV⟩
    have hcoeff : WeilDivisor.coeff D.toWeilDivisor y = X.ord (f : X.functionField) y := by
      rw [coeff_toWeilDivisor,
        orderAt_eq_of_restrict_eq_rationalUnitClass D y V hyV (Additive.ofMul f) hV.symm]
      simp
    rw [X.ord_mul (Units.ne_zero f) hq, ← hcoeff] at hreg
    omega
  · intro hs
    apply mem_sections_iff_exists.mpr
    intro x hx
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    obtain ⟨V, hxV, hV⟩ := isLocalEquationAt_iff.mp hf
    let W : X.Opens := U ⊓ V
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have : Nonempty W := ⟨⟨x, hx, hxV⟩⟩
    have hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ W →
        0 ≤ X.ord ((f : X.functionField) * rationalFunctionsEquiv U s) y := by
      intro y hyW
      have hyU : (y : X) ∈ U := hyW.1
      have hyV : (y : X) ∈ V := hyW.2
      have : Nonempty V := ⟨⟨y, hyV⟩⟩
      by_cases hq : rationalFunctionsEquiv U s = 0
      · simp [hq]
      have hbound := (SchemeWeilDivisor.mem_sections.mp hs y hyU).resolve_left hq
      have hcoeff : WeilDivisor.coeff D.toWeilDivisor y = X.ord (f : X.functionField) y := by
        rw [coeff_toWeilDivisor,
          orderAt_eq_of_restrict_eq_rationalUnitClass D y V hyV (Additive.ofMul f) hV.symm]
        simp
      rw [hcoeff] at hbound
      rw [X.ord_mul (Units.ne_zero f) hq]
      omega
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg
      (U := W) (fun _ _ ↦ inferInstance) (fun y _ ↦ hX y) hord
    have hxW : x ∈ W := ⟨hx, hxV⟩
    refine ⟨f, hf, ⟨X.presheaf.germ W x hxW a, ?_⟩⟩
    rw [X.algebraMap_germ_eq_germToFunctionField hxW, ha]

/-- The line bundle of a Cartier divisor is canonically the line bundle of its Weil divisor.
The isomorphism is induced by equality of their rational-function sections. -/
def sheafIsoToWeilDivisor (hX : ∀ x : X, coheight x ≤ 1) (D : CartierDivisor X) :
    D.sheaf ≅ SchemeWeilDivisor.sheaf D.toWeilDivisor :=
  let φ := SchemeWeilDivisor.sheafι D.toWeilDivisor
  have hφ : ∀ (U : X.Opens) (s : Γ(SchemeWeilDivisor.sheaf D.toWeilDivisor, U)),
      _root_.AlgebraicGeometry.Scheme.Modules.Hom.app φ U s ∈ D.sections U := fun U s ↦
    (sections_eq_toWeilDivisor hX D U).symm ▸
      SchemeWeilDivisor.sheafι_app_mem D.toWeilDivisor U s
  haveI : IsIso (D.sheafLift φ hφ) :=
    D.isIso_sheafLift φ hφ
      (SchemeWeilDivisor.sheafι_app_injective D.toWeilDivisor)
      (fun U s hs ↦ ⟨SchemeWeilDivisor.sectionMk s
        ((sections_eq_toWeilDivisor hX D U) ▸ hs), by
          exact SchemeWeilDivisor.sheafι_app_sectionMk s _⟩)
  (asIso (D.sheafLift φ hφ)).symm

/-- The inverse comparison map preserves the inclusion into rational functions. -/
@[reassoc (attr := simp)]
lemma sheafIsoToWeilDivisor_inv_ι (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) :
    (D.sheafIsoToWeilDivisor hX).inv ≫ D.sheafι =
      SchemeWeilDivisor.sheafι D.toWeilDivisor := by
  simp [sheafIsoToWeilDivisor, sheafLift_ι]

/-- The comparison map preserves the inclusion into rational functions. -/
@[reassoc (attr := simp)]
lemma sheafIsoToWeilDivisor_hom_ι (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) :
    (D.sheafIsoToWeilDivisor hX).hom ≫
      SchemeWeilDivisor.sheafι D.toWeilDivisor = D.sheafι := by
  calc
    _ = (D.sheafIsoToWeilDivisor hX).hom ≫
        ((D.sheafIsoToWeilDivisor hX).inv ≫ D.sheafι) := by
          rw [sheafIsoToWeilDivisor_inv_ι]
    _ = D.sheafι := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The Cartier and Weil divisor presentations give the same line-bundle class. -/
theorem toLineBundleClass_eq_toWeilDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) :
    D.toLineBundleClass = SchemeWeilDivisor.toLineBundleClass hX D.toWeilDivisor := by
  have hmk : SchemeWeilDivisor.toLineBundleClass hX D.toWeilDivisor =
      LineBundleClass.mk (SchemeWeilDivisor.toInvertibleSheaf hX D.toWeilDivisor) :=
    (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hX).mpr ⟨Iso.refl _⟩
  rw [hmk, toLineBundleClass_eq_mk_iff]
  exact ⟨D.sheafIsoToWeilDivisor hX ≪≫
    (eqToIso (SchemeWeilDivisor.toInvertibleSheaf_obj hX D.toWeilDivisor)).symm⟩

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
