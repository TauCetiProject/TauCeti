/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Top-degree coefficients and signed change of coordinates

Top forms retain the existing continuous alternating-map carrier. Their coefficients transform
by the signed determinant. Integration of these coefficients against a basis's Haar measure is
independent of an orientation-compatible change of basis, and the actual Jacobian theorem
transports their integrals and integrability under orientation-preserving coordinate changes.
These are the coordinate foundations for integration of manifold top forms.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace ContinuousAlternatingMap

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating form is determined by its scalar coefficient in a basis. -/
theorem apply_eq_det_mul (ω : E [⋀^ι]→L[ℝ] ℝ) (b : Module.Basis ι ℝ E) (v : ι → E) :
    ω v = b.det v * ω b := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[ℝ] ℝ ↦ f v) (ω.toAlternatingMap.eq_smul_basis_det b)
  simpa only [coe_toAlternatingMap, AlternatingMap.smul_apply, smul_eq_mul, mul_comm] using h

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback of a top-degree coefficient multiplies by the signed real determinant. -/
theorem compContinuousLinearMap_apply_basis [Finite ι] (ω : E [⋀^ι]→L[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    (ω.compContinuousLinearMap A) b = A.toLinearMap.det * ω b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [compContinuousLinearMap_apply, apply_eq_det_mul ω b]
  have hd := b.det_comp A.toLinearMap b
  simp only [ContinuousLinearMap.coe_coe, b.det_self, mul_one] at hd
  rw [hd]

end ContinuousAlternatingMap

namespace Module.Basis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

/-- A change of basis rescales its normalized Haar measure by the inverse absolute determinant. -/
theorem addHaar_eq_smul_of_basis (b b' : Basis ι ℝ E) :
    b'.addHaar = ENNReal.ofReal |(b.det b')⁻¹| • b.addHaar := by
  let e : E ≃ₗ[ℝ] E := b.equiv b' (Equiv.refl ι)
  have hmap : b.map e = b' := by
    ext i
    simp [e]
  have hdet : e.toLinearMap.det = b.det b' := by
    simpa only [e] using det_basis b' b
  calc
    b'.addHaar = Measure.map e.toContinuousLinearEquiv b.addHaar := by
      rw [b.map_addHaar, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, hmap]
    _ = _ := by
      simpa only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_coe, hdet] using
        Measure.map_linearMap_addHaar_eq_smul_addHaar b.addHaar e.isUnit_det'.ne_zero

/-- Arbitrary basis changes transform the actual top-form coefficient integral by their
orientation sign. Positive Haar scaling and signed form coefficients are both retained. -/
theorem integral_apply_basis_change (b b' : Basis ι ℝ E) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ x, ω x b' ∂b'.addHaar) = (b.det b' / |b.det b'|) * ∫ x, ω x b ∂b.addHaar := by
  rw [addHaar_eq_smul_of_basis b b', integral_smul_measure]
  simp_rw [ContinuousAlternatingMap.apply_eq_det_mul (b := b) (v := b')]
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp only [smul_eq_mul]
  field_simp

/-- The actual integral of a top-form coefficient is invariant under an orientation-compatible
basis change. The compensating Haar normalization is essential. -/
theorem integral_apply_eq_of_orientation_eq (b b' : Basis ι ℝ E)
    (ho : b.orientation = b'.orientation) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ x, ω x b ∂b.addHaar) = ∫ x, ω x b' ∂b'.addHaar := by
  have hd : 0 < b.det b' := (b.orientation_eq_iff_det_pos b').mp ho
  rw [integral_apply_basis_change b b' ω, abs_of_pos hd, div_self hd.ne', one_mul]

end Module.Basis

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ}

/-- The scalar coefficient of a manifold top form transforms by the signed Jacobian between
preferred charts, including derivatives taken within the model range at the boundary. -/
theorem inChartAt_apply_basis_eq_det_mul (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    φ.inChartAt x₀ z b =
      (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap.det *
        φ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z)) b := by
  rw [φ.inChartAt_eq_compContinuousLinearMap hz hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply_basis]

end TauCeti.RoughForm

namespace MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Finite ι]
  {μ : Measure E} [μ.IsAddHaarMeasure] {T : E → E} {T' : E → E →L[ℝ] E} {s : Set E}

/-- The actual Jacobian change-of-variables theorem for top-form coefficients. Positive
coordinate orientation converts the absolute measure Jacobian to the signed form Jacobian. -/
theorem integral_image_apply_basis_eq_integral_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (hdet : ∀ x ∈ s, 0 ≤ (T' x).toLinearMap.det) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ y in T '' s, ω y b ∂μ) =
      ∫ x in s, ((ω (T x)).compContinuousLinearMap (T' x)) b ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hT hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis,
    abs_of_nonneg (hdet x hx)]
  rfl

/-- Genuine integrability of top-form coefficients is invariant under an injective
orientation-preserving coordinate change. -/
theorem integrableOn_image_apply_basis_iff_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (hdet : ∀ x ∈ s, 0 ≤ (T' x).toLinearMap.det) (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    IntegrableOn (fun y ↦ ω y b) (T '' s) μ ↔
      IntegrableOn (fun x ↦ ((ω (T x)).compContinuousLinearMap (T' x)) b) s μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hT hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis,
    abs_of_nonneg (hdet x hx)]
  rfl

/-- The actual coefficient integral is compatible with chart signs, allowing reversing
coordinate changes. The signs need only agree with the signed Jacobian on the overlap. -/
theorem integral_image_signed_apply_basis_eq_integral_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (σsource σtarget : E → ℤˣ)
    (hσ : ∀ x ∈ s, (σsource x : ℝ) * (T' x).toLinearMap.det =
      |(T' x).toLinearMap.det| * (σtarget (T x) : ℝ))
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ y in T '' s, (σtarget y : ℝ) * ω y b ∂μ) =
      ∫ x in s, (σsource x : ℝ) * ((ω (T x)).compContinuousLinearMap (T' x)) b ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hT hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, smul_eq_mul,
    ← mul_assoc, ← mul_assoc, hσ x hx]

/-- Genuine integrability of signed top-form coefficients transports with the chart signs,
including orientation-reversing changes of coordinates. -/
theorem integrableOn_image_signed_apply_basis_iff_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (σsource σtarget : E → ℤˣ)
    (hσ : ∀ x ∈ s, (σsource x : ℝ) * (T' x).toLinearMap.det =
      |(T' x).toLinearMap.det| * (σtarget (T x) : ℝ))
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    IntegrableOn (fun y ↦ (σtarget y : ℝ) * ω y b) (T '' s) μ ↔
      IntegrableOn (fun x ↦ (σsource x : ℝ) *
        ((ω (T x)).compContinuousLinearMap (T' x)) b) s μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hT hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, smul_eq_mul,
    ← mul_assoc, ← mul_assoc, hσ x hx]

end MeasureTheory
