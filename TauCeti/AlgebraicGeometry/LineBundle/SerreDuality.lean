/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality

/-!
# Canonical line bundles and Serre duality

On an integral separated Noetherian curve with discrete valuation rings at its closed points,
the divisor of a nonzero Weil differential determines a line bundle. When the curve has all the
places of its function field and the ground field is algebraically closed in that function
field, this line bundle is independent of the differential up to isomorphism.

This file constructs a representative `InvertibleSheaf.canonicalBundle` of that class and
transports the divisor-sheaf duality to arbitrary line bundles:

`H¹(X, L)ᵛ ≃ H⁰(X, ω ⊗ L⁻¹)` and `H⁰(X, L)ᵛ ≃ H¹(X, ω ⊗ L⁻¹)`.

The equivalence is asserted as an existence result: no canonical trace or naturality is claimed.
The construction uses Weil differentials, not a relative dualizing complex, and does not yet
identify the canonical bundle with the sheaf of Kähler differentials or provide base change.
The degree of the canonical bundle is `2g - 2` on a proper curve. These results allow line-bundle
cohomology to be used without choosing divisor presentations in the statements.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, Section 5.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Corollary 7.7, and Chapter IV, Section 1.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [X.IsSeparated]
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)

/-- A canonical line bundle, obtained by choosing a divisor in the canonical class of Weil
    differentials and forming its divisor sheaf. Its isomorphism class is characterized by
    `mk_canonicalBundle_eq_iff`. -/
def canonicalBundle : InvertibleSheaf X :=
  SchemeWeilDivisor.toInvertibleSheaf hdim <|
    (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
      ((Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hk)).choose

/-- A divisor represents the canonical line-bundle class precisely when its function-field
    divisor represents the canonical class of Weil differentials. -/
@[simp]
lemma mk_canonicalBundle_eq_iff (K : SchemeWeilDivisor X) :
    LineBundleClass.mk (canonicalBundle hex hdim hF hk) =
        SchemeWeilDivisor.toLineBundleClass hdim K ↔
      (Place.orderSystem hF).divisorClass
        (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim K) = canonicalClass hF hk := by
  let W := ((Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hk)).choose
  have hW : (Place.orderSystem hF).divisorClass W = canonicalClass hF hk :=
    ((Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hk)).choose_spec
  -- Both sides compare the chosen divisor with `K`; use the divisor dictionary before
  -- passing to the function-field class group.
  have hc : LineBundleClass.mk (canonicalBundle hex hdim hF hk) =
      SchemeWeilDivisor.toLineBundleClass hdim
        ((SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm W) :=
    ((SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mpr ⟨Iso.refl _⟩).symm
  rw [hc, SchemeWeilDivisor.toLineBundleClass_eq_iff,
    ← SchemeWeilDivisor.linearlyEquivalent_equivFunctionFieldDivisor_iff hex hdim hF,
    ← WeilDivisor.OrderSystem.divisorClass_eq_iff]
  simp [hW, eq_comm]

/-- The canonical bundle is isomorphic to the sheaf of every canonical divisor. -/
lemma nonempty_iso_canonicalBundle_sheaf {K : SchemeWeilDivisor X}
    (hK : (Place.orderSystem hF).divisorClass
      (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim K) = canonicalClass hF hk) :
    Nonempty ((canonicalBundle hex hdim hF hk).obj ≅ SchemeWeilDivisor.sheaf K) := by
  have h := (mk_canonicalBundle_eq_iff hex hdim hF hk K).mpr hK
  obtain ⟨e⟩ := (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mp h.symm
  rw [SchemeWeilDivisor.toInvertibleSheaf_obj] at e
  exact ⟨e.symm⟩

/-- **Serre duality for line bundles.** The dual of `H¹(X, L)` is linearly isomorphic to
    `H⁰(X, ω ⊗ L⁻¹)` for any representative `ω` of the canonical line-bundle class.
    The existence statement does not select a canonical pairing. -/
theorem nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual
    (L ω : InvertibleSheaf X)
    (hω : LineBundleClass.mk ω = LineBundleClass.mk (canonicalBundle hex hdim hF hk)) :
    Nonempty (Module.Dual k (Scheme.Modules.Cohomology L.obj 1) ≃ₗ[k]
      Scheme.Modules.Cohomology (tensorProduct ω (dual L)).obj 0) := by
  obtain ⟨D, ⟨eL⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  obtain ⟨K, ⟨eω⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim ω
  have hL : SchemeWeilDivisor.toLineBundleClass hdim D = LineBundleClass.mk L := by
    apply (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mpr
    simpa only [SchemeWeilDivisor.toInvertibleSheaf_obj] using Nonempty.intro eL.symm
  have hωK : SchemeWeilDivisor.toLineBundleClass hdim K = LineBundleClass.mk ω := by
    apply (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mpr
    simpa only [SchemeWeilDivisor.toInvertibleSheaf_obj] using Nonempty.intro eω.symm
  have hK := (mk_canonicalBundle_eq_iff hex hdim hF hk K).mp (hω.symm.trans hωK.symm)
  have hneg : SchemeWeilDivisor.toLineBundleClass hdim (-D) = (LineBundleClass.mk L)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hL, ← SchemeWeilDivisor.toLineBundleClass_add]
    simp
  have htensor : SchemeWeilDivisor.toLineBundleClass hdim (K - D) =
      LineBundleClass.mk (tensorProduct ω (dual L)) := by
    rw [sub_eq_add_neg, SchemeWeilDivisor.toLineBundleClass_add,
      LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk]
    simp [hneg, hωK]
  obtain ⟨etensor⟩ := (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mp htensor
  rw [SchemeWeilDivisor.toInvertibleSheaf_obj] at etensor
  obtain ⟨η, -, hη, hgreat⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hF hk hK
  exact ⟨(Scheme.Modules.cohomologyBaseLinearEquivOfIso k eL 1).dualMap.symm.trans <|
    (SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero hex hdim hF hk hη hgreat D).trans
      (Scheme.Modules.cohomologyBaseLinearEquivOfIso k etensor 0)⟩

/-- **Serre duality in degree zero.** The dual of `H⁰(X, L)` is linearly isomorphic to
    `H¹(X, ω ⊗ L⁻¹)` for any representative `ω` of the canonical class. -/
theorem nonempty_cohomologyZeroDualEquivCohomologyOne_tensor_dual
    (L ω : InvertibleSheaf X)
    (hω : LineBundleClass.mk ω = LineBundleClass.mk (canonicalBundle hex hdim hF hk)) :
    Nonempty (Module.Dual k (Scheme.Modules.Cohomology L.obj 0) ≃ₗ[k]
      Scheme.Modules.Cohomology (tensorProduct ω (dual L)).obj 1) := by
  let N := tensorProduct ω (dual L)
  have hNN : LineBundleClass.mk (tensorProduct ω (dual N)) = LineBundleClass.mk L := by
    simp only [N, LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk]
    simp [-LineBundleClass.inv_mk, mul_left_comm]
  obtain ⟨eNN⟩ := LineBundleClass.mk_eq_mk_iff.mp hNN
  obtain ⟨e⟩ := nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual
    hex hdim hF hk N ω hω
  obtain ⟨D, ⟨eN⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim N
  have := SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField
    hex hdim hF D
  have := (Scheme.Modules.finiteDimensional_cohomology_congr k eN 1).mpr this
  exact ⟨(e.trans (Scheme.Modules.cohomologyBaseLinearEquivOfIso k eNN 0)).dualMap.trans
    (Module.evalEquiv k (Scheme.Modules.Cohomology N.obj 1)).symm⟩

/-- The dimensions in Serre duality agree for every line bundle and every representative of
    the canonical class. -/
theorem finrank_cohomology_one_eq_finrank_cohomology_zero_tensor_dual
    (L ω : InvertibleSheaf X)
    (hω : LineBundleClass.mk ω = LineBundleClass.mk (canonicalBundle hex hdim hF hk)) :
    finrank k (Scheme.Modules.Cohomology L.obj 1) =
      finrank k (Scheme.Modules.Cohomology (tensorProduct ω (dual L)).obj 0) := by
  obtain ⟨D, ⟨eL⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  have := SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField
    hex hdim hF D
  have := (Scheme.Modules.finiteDimensional_cohomology_congr k eL 1).mpr this
  rw [← Subspace.dual_finrank_eq]
  exact (nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual
    hex hdim hF hk L ω hω).some.finrank_eq

/-- On a proper curve, the Euler-characteristic degree of the canonical line bundle is
    `2g - 2`, where `g = dim H¹(X, 𝒪_X)`. -/
@[simp]
theorem eulerDegree_canonicalBundle [IsProper (X ↘ Spec (.of k))] :
    haveI := (Scheme.Modules.finiteDimensional_cohomology_congr k
      (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
        (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF 0)
    (canonicalBundle hex hdim hF hk).eulerDegree k = 2 * X.genus k - 2 := by
  obtain ⟨K, ⟨eK⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim
    (canonicalBundle hex hdim hF hk)
  have hK : (Place.orderSystem hF).divisorClass
      (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim K) = canonicalClass hF hk := by
    apply (mk_canonicalBundle_eq_iff hex hdim hF hk K).mp
    apply Eq.symm
    apply (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mpr
    simpa only [SchemeWeilDivisor.toInvertibleSheaf_obj] using Nonempty.intro eK.symm
  have := (Scheme.Modules.finiteDimensional_cohomology_congr k
    (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
      (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF 0)
  rw [eulerDegree_eq_relativeDegree k hdim eK]
  exact SchemeWeilDivisor.relativeDegree_eq_two_mul_genus_sub_two hex hdim hF hk hK

end InvertibleSheaf

end

end TauCeti.AlgebraicGeometry
