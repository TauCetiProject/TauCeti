/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import Mathlib.Topology.VectorBundle.Riemannian
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Hilbert–Schmidt pairing of native zero-one forms

The native projection `j.zeroOnePart A` is `½ (A + I • A ∘ j)`. For a `j`-compatible tangent
metric and a Hermitian fibre metric, this projection is self-adjoint for the real metric-trace
pairing `ContinuousLinearMap.hilbertSchmidtInner`. In particular, pairing any native zero-one
form against `j.zeroOnePart A` gives the same result as pairing against `A`.

In real source dimension two, every unit vector `v` gives the orthonormal basis `(v, j v)`.
For zero-one forms `η` and `θ`, their Hilbert–Schmidt pairing is therefore
`2 * ⟪η v, θ v⟫_ℝ`. Applying this to `θ = j.zeroOnePart A` cancels the projection's factor
`½`, giving `⟪η v, A v + I • A (j v)⟫_ℝ` for an arbitrary real-linear `A`.

All maps have their original carrier `TangentSpace I x →L[ℝ] V x`; the pairing is the existing
real metric trace and Hom retains its operator norm. The target fibres may have arbitrary rank
and need no completeness. The self-adjoint pairing includes source dimension zero. These are
pointwise identities supplying the normalization of the zero-one principal part; geometric
integration and boundary terms belong to the corresponding global adjunction statements.

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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (j : SmoothAlmostComplexStructure I M) (x : M)

/-- For a compatible tangent metric and a Hermitian fibre metric, the actual zero-one projection
is self-adjoint for the real Hilbert–Schmidt pairing on the original Hom fibre. -/
theorem hilbertSchmidtInner_zeroOnePart_left_eq_right
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A B : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner (j.zeroOnePart A) B = hilbertSchmidtInner A (j.zeroOnePart B) := by
  have hp (C : TangentSpace I x →L[ℝ] V x) : j.zeroOnePart C =
      (2⁻¹ : ℝ) • (C + Complex.I • C.comp (j.toEndomorphism x)) := by
    ext v
    exact zeroOnePart_apply C v
  rw [hp, hp]
  let e : TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace I x := LinearIsometryEquiv.ofSurjective
    ((j.toEndomorphism x).toLinearMap.isometryOfInner hJ) (j.surjective x)
  have he (v : TangentSpace I x) : e v = j x v := rfl
  have hIskew (u v : V x) : ⟪Complex.I • u, v⟫_ℝ = -⟪u, Complex.I • v⟫_ℝ := by
    have h := hV u (Complex.I • v)
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul, inner_neg_right] at h
    linarith
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have htwist : hilbertSchmidtInner (Complex.I • A.comp (j.toEndomorphism x)) B =
      hilbertSchmidtInner A (Complex.I • B.comp (j.toEndomorphism x)) := by
    rw [hilbertSchmidtInner_eq_sum _ _ b, hilbertSchmidtInner_eq_sum _ _ (b.map e)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_apply, comp_apply, OrthonormalBasis.map_apply, he, j.apply_apply,
      map_neg, smul_neg, inner_neg_right]
    exact hIskew _ _
  rw [hilbertSchmidtInner_smul_left, hilbertSchmidtInner_add_left,
    hilbertSchmidtInner_smul_right, hilbertSchmidtInner_add_right, htwist]

variable {j x}

/-- A native zero-one form pairs identically against a real-linear map and its zero-one part,
for compatible source and target metrics. -/
theorem IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_right
    {η : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (A : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner η (j.zeroOnePart A) = hilbertSchmidtInner η A := by
  rw [← j.hilbertSchmidtInner_zeroOnePart_left_eq_right x hJ hV η A, hη.zeroOnePart_eq]

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- On a real two-dimensional tangent fibre, the geometric Hilbert–Schmidt pairing of native
zero-one forms is twice their real fibre pairing on any unit tangent vector. The orthonormal
basis consisting of that vector and its `j`-image is derived from metric compatibility. -/
theorem IsZeroOneForm.hilbertSchmidtInner_eq_two_mul_inner_apply
    {η θ : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η) (hθ : j.IsZeroOneForm θ)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ (TangentSpace I x) = 2)
    (v : TangentSpace I x) (hv : ‖v‖ = 1) :
    hilbertSchmidtInner η θ = 2 * ⟪η v, θ v⟫_ℝ := by
  have hvself : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hjself : ⟪j x v, j x v⟫_ℝ = 1 := (hJ v v).trans hvself
  have hcross : ⟪v, j x v⟫_ℝ = 0 := by
    rw [real_inner_comm]
    simpa only [almostComplexStructureAt_apply] using
      (j.almostComplexStructureAt x).inner_apply_self
        (by simpa only [almostComplexStructureAt_apply] using hJ) v
  have hon : Orthonormal ℝ ![v, j x v] := by
    rw [orthonormal_iff_ite]
    intro i k
    fin_cases i <;> fin_cases k
    · exact hvself
    · exact hcross
    · exact (real_inner_comm _ _).trans hcross
    · exact hjself
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank
    (by simpa only [Fintype.card_fin] using hDim.symm)
  let b := OrthonormalBasis.mk hon hspan.ge
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = j x v := by simp [b]
  rw [hilbertSchmidtInner_eq_sum η θ b, Fin.sum_univ_two, hb0, hb1,
    isZeroOneForm_iff.mp hη, isZeroOneForm_iff.mp hθ, inner_neg_neg, hV]
  ring

/-- In real source dimension two, the geometric Hilbert–Schmidt factor two cancels the native
projection's factor one half. The resulting coefficient is the full Cauchy–Riemann expression
`A v + I • A (j v)` in the original fibre. -/
theorem IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_eq_inner_apply
    {η : TangentSpace I x →L[ℝ] V x} (hη : j.IsZeroOneForm η)
    (hJ : ∀ u v, ⟪j x u, j x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hDim : Module.finrank ℝ (TangentSpace I x) = 2)
    (v : TangentSpace I x) (hv : ‖v‖ = 1) (A : TangentSpace I x →L[ℝ] V x) :
    hilbertSchmidtInner η (j.zeroOnePart A) = ⟪η v, A v + Complex.I • A (j x v)⟫_ℝ := by
  rw [hη.hilbertSchmidtInner_eq_two_mul_inner_apply (isZeroOneForm_zeroOnePart A)
      hJ hV hDim v hv, zeroOnePart_apply, real_inner_smul_right]
  ring

end TauCeti.SmoothAlmostComplexStructure
