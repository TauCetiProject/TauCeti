/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChartDerivative
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# The Poincaré–Hopf theorem for gradients of Morse functions

Let `M` be a compact boundaryless manifold with a `C¹` Riemannian metric and `f` a Morse function
on `M`. The zeros of the gradient `grad f` are the critical points of `f`; each is a nondegenerate
zero, whose index, the sign of the determinant of the chart derivative of `grad f`, is `(-1)` to
the Morse index of `f` (`TauCeti.sign_det_vectorFieldChartDerivative_mgradient`). Summing over the
zeros and applying Euler's equality for Morse functions
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`) gives the Poincaré–Hopf
theorem for the vector field `grad f`: the sum of the indices of its zeros is the Euler
characteristic `∑ᵢ (-1)ⁱ dim Hᵢ(M; k)`, for singular homology with coefficients in any division
ring `k` (`TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`).

No orientability or connectedness of `M` is assumed. Only gradient fields of Morse functions are
treated here, not arbitrary vector fields with nondegenerate zeros.

## Main results

* `TauCeti.IsMorse.det_vectorFieldChartDerivative_mgradient_ne_zero`: every zero of the gradient
  of a Morse function is nondegenerate.
* `TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`: the sum of the indices
  of the zeros of the gradient of a Morse function is the Euler characteristic.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the index of a gradient field and the Poincaré–Hopf theorem).
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §5.
-/

public section

open Bundle Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ}

/-- For a `C¹` metric, the gradient of a Morse function is differentiable, and each of its zeros
is a nondegenerate critical point. -/
private theorem IsMorse.mdifferentiableAt_mgradient_and_isManifoldNondegenerateCriticalPoint
    (hf : IsMorse I f) {x : M} (hx : Manifold.mgradient I f x = 0) :
    MDifferentiableAt I I.tangent (fun y ↦ (Manifold.mgradient I f y : TangentBundle I M)) x ∧
      IsManifoldNondegenerateCriticalPoint I f x := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_num)
  refine ⟨Manifold.mdifferentiable_mgradient hf2 x, hf.isManifoldNondegenerateCriticalPoint ?_⟩
  rw [← mvfderiv_eq_fderiv_comp_extChartAt_symm]
  exact Manifold.mgradient_eq_zero_iff.mp hx

/-- **The zeros of the gradient of a Morse function are nondegenerate.** For a `C¹` metric, the
chart derivative of the gradient of a Morse function has nonzero determinant at every zero. -/
theorem IsMorse.det_vectorFieldChartDerivative_mgradient_ne_zero (hf : IsMorse I f) {x : M}
    (hx : Manifold.mgradient I f x = 0) :
    LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x) ≠ 0 := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  obtain ⟨hgrad, h⟩ :=
    hf.mdifferentiableAt_mgradient_and_isManifoldNondegenerateCriticalPoint hx
  exact (det_vectorFieldChartDerivative_mgradient_ne_zero_iff hgrad h.contMDiffAt
    (Manifold.mgradient_eq_zero_iff.mp hx)).mpr h

/-- **The Poincaré–Hopf theorem for gradients of Morse functions.** On a compact boundaryless
manifold with a `C¹` metric, the sum over the zeros of the gradient of a Morse function of their
indices, the signs of the determinants of the chart derivatives, is the Euler characteristic
`∑ᵢ (-1)ⁱ dim Hᵢ(M; k)` of singular homology with coefficients in any division ring `k`. The
sum is finite because a Morse function has finitely many critical points. -/
theorem IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient [T2Space M] [CompactSpace M]
    (hf : IsMorse I f) (k : Type u) [DivisionRing k] :
    ∑ᶠ x : {x // Manifold.mgradient I f x = 0},
        (SignType.sign (LinearMap.det (vectorFieldChartDerivative I (Manifold.mgradient I f) x)) :
          ℤ) =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) := by
  classical
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  -- The zeros of the gradient are the finitely many critical points.
  set s := hf.finite_criticalPoints.toFinset
  have hs : (s : Set M) = criticalPoints I f := by simp [s]
  have hmem (x : M) : x ∈ s ↔ Manifold.mgradient I f x = 0 := by
    rw [← Finset.mem_coe, hs, mem_criticalPoints, Manifold.mgradient_eq_zero_iff]
  let : Fintype {x // Manifold.mgradient I f x = 0} := Fintype.subtype s hmem
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_subtype s hmem
    (fun x ↦ (SignType.sign (LinearMap.det
      (vectorFieldChartDerivative I (Manifold.mgradient I f) x)) : ℤ)),
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (ModuleCat.of k k) le_rfl,
    sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum s hs le_rfl]
  -- At each zero, the index is `(-1)` to the Morse index.
  have hk : finrank k (ModuleCat.of k k) = 1 := finrank_self k
  rw [hk, Nat.cast_one, one_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  obtain ⟨hgrad, h⟩ :=
    hf.mdifferentiableAt_mgradient_and_isManifoldNondegenerateCriticalPoint ((hmem x).mp hx)
  rw [sign_det_vectorFieldChartDerivative_mgradient hgrad h, SignType.coe_pow, SignType.coe_neg_one]

end TauCeti
