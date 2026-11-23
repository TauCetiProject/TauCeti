/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Symplectic.Complex.HilbertSchmidt
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Hilbert–Schmidt pairing of native zero-one forms

The native projection `j.zeroOnePart A` is `½ (A + I • A ∘ j)`. For a `j`-compatible tangent
metric and a Hermitian fibre metric, this projection is self-adjoint for the real metric-trace
pairing `ContinuousLinearMap.hilbertSchmidtInner`. In particular, pairing any native zero-one
form against `j.zeroOnePart A` gives the same result as pairing against `A`.

In real source dimension two, for every unit vector `v` and zero-one forms `η` and `θ`,
their Hilbert–Schmidt pairing is
`2 * ⟪η v, θ v⟫_ℝ`. Applying this to `θ = j.zeroOnePart A` cancels the projection's factor
`½`, giving `⟪η v, A v + I • A (j v)⟫_ℝ` for an arbitrary real-linear `A`.

The target fibres may have arbitrary dimension and need no completeness. The self-adjoint
pairing includes source dimension zero. All four statements are pointwise identities for
orthogonal almost complex structures, specialized here to tangent fibres.

## Main results

* `hilbertSchmidtInner_zeroOnePart_left_eq_right`: self-adjoint pairing.
* `IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_right`:
  a zero-one form pairs identically against a map and its zero-one part.
* `IsZeroOneForm.hilbertSchmidtInner_eq_two_mul_inner_apply`:
  the intrinsic factor-two formula in real dimension two.
* `IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_eq_inner_apply`:
  cancellation of the Hilbert–Schmidt factor two with the native half-normalized projection.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, in particular the metric convention preceding Lemma C.1.9.
-/

public section

open Bundle ContinuousLinearMap
open scoped InnerProductSpace Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothAlmostComplexStructure

-- Orthogonality makes multiplication by `i` continuous and hence real-linear, even when
-- no compatibility between the independently supplied real and complex scalar actions is given.
private def orthogonalSmulI {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Module ℂ V] (hV : ∀ u v : V, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ) :
    AlmostComplexStructure V := by
  let f : V →+ V :=
    { toFun := fun v ↦ Complex.I • v
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  have hf_apply (v : V) : f v = Complex.I • v := rfl
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm _ fun v ↦ by
    simp only [hf_apply]
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hV]
  exact
    { toLinearMap := (f.toRealLinearMap hf.continuous).toLinearMap
      square_neg := LinearMap.ext fun v ↦ by
        simp only [LinearMap.comp_apply, coe_coe, AddMonoidHom.coe_toRealLinearMap,
          hf_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
          LinearMap.neg_apply, LinearMap.id_apply] }

private theorem orthogonalSmulI_apply {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Module ℂ V]
    (hV : ∀ u v : V, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ) (v : V) :
    orthogonalSmulI hV v = Complex.I • v :=
  -- The continuous additive-to-real-linear conversion keeps the underlying function.
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (j : SmoothAlmostComplexStructure I M) (x : M)

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
private theorem zeroOnePart_eq_complexAntilinearPart
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePart A = (complexAntilinearPart (j.almostComplexStructureAt x).toLinearMap
      (orthogonalSmulI hV).toLinearMap A.toLinearMap).toContinuousLinearMap := by
  ext v
  simp only [zeroOnePart_apply, LinearMap.coe_toContinuousLinearMap',
    complexAntilinearPart_apply, almostComplexStructureAt_apply, orthogonalSmulI_apply, coe_coe]

variable {j x}

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
private theorem isZeroOneForm_iff_orthogonalSmulI
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (η : TangentSpace I x →L[ℝ] V x) :
    j.IsZeroOneForm η ↔ IsComplexAntilinear (j.almostComplexStructureAt x).toLinearMap
      (orthogonalSmulI hV).toLinearMap η.toLinearMap := by
  rw [isZeroOneForm_iff]
  exact ⟨fun h ↦ isComplexAntilinear_of_apply fun v ↦ by
    simpa only [almostComplexStructureAt_apply, orthogonalSmulI_apply, coe_coe] using h v,
    fun h v ↦ by
      simpa only [almostComplexStructureAt_apply, orthogonalSmulI_apply, coe_coe] using h.apply v⟩

variable (j x)

/-- For a compatible tangent metric and a Hermitian fibre metric, the actual zero-one projection
is self-adjoint for the real Hilbert–Schmidt pairing. -/
theorem hilbertSchmidtInner_zeroOnePart_left_eq_right
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A B : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner (j.zeroOnePart A) B = hilbertSchmidtInner A (j.zeroOnePart B) := by
  simpa only [zeroOnePart_eq_complexAntilinearPart j x hV] using
    (j.almostComplexStructureAt x).hilbertSchmidtInner_complexAntilinearPart_left_eq_right
      (orthogonalSmulI hV) (by simpa only [almostComplexStructureAt_apply] using hJ)
      (by simpa only [orthogonalSmulI_apply] using hV) A B

variable {j x}

/-- A native zero-one form pairs identically against a real-linear map and its zero-one part,
for compatible source and target metrics. -/
theorem IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_right
    {η : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner η (j.zeroOnePart A) = hilbertSchmidtInner η A := by
  simpa only [zeroOnePart_eq_complexAntilinearPart j x hV] using
    TauCeti.IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_right
      ((isZeroOneForm_iff_orthogonalSmulI hV η).mp hη)
        (by simpa only [almostComplexStructureAt_apply] using hJ)
        (by simpa only [orthogonalSmulI_apply] using hV) A

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- On a real two-dimensional tangent fibre, the Hilbert–Schmidt pairing of native zero-one
forms is twice their real fibre pairing on any unit vector, for compatible metrics. -/
theorem IsZeroOneForm.hilbertSchmidtInner_eq_two_mul_inner_apply
    {η θ : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η) (hθ : j.IsZeroOneForm θ)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ (TangentSpace I x) = 2)
    (v : TangentSpace I x) (hv : ‖v‖ = 1) :
    hilbertSchmidtInner η θ = 2 * ⟪η v, θ v⟫_ℝ :=
  ((isZeroOneForm_iff_orthogonalSmulI hV η).mp hη).hilbertSchmidtInner_eq_two_mul_inner_apply
    ((isZeroOneForm_iff_orthogonalSmulI hV θ).mp hθ)
    (by simpa only [almostComplexStructureAt_apply] using hJ)
    (by simpa only [orthogonalSmulI_apply] using hV) hDim v hv

/-- In real source dimension two, the Hilbert–Schmidt factor two cancels the native projection's
factor one half, giving `⟪η v, A v + I • A (j v)⟫_ℝ`. -/
theorem IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_eq_inner_apply
    {η : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ (TangentSpace I x) = 2)
    (v : TangentSpace I x) (hv : ‖v‖ = 1) (A : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner η (j.zeroOnePart A) = ⟪η v, A v + Complex.I • A (j x v)⟫_ℝ := by
  simpa only [zeroOnePart_eq_complexAntilinearPart j x hV,
    almostComplexStructureAt_apply, orthogonalSmulI_apply] using
    TauCeti.IsComplexAntilinear.hilbertSchmidtInner_complexAntilinearPart_eq_inner_apply
      ((isZeroOneForm_iff_orthogonalSmulI hV η).mp hη)
        (by simpa only [almostComplexStructureAt_apply] using hJ)
        (by simpa only [orthogonalSmulI_apply] using hV) hDim v hv A

end TauCeti.SmoothAlmostComplexStructure
