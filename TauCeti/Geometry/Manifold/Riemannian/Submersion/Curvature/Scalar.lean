/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature.Sectional
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.NormSq

/-!
# O'Neill's scalar-curvature formula for totally geodesic fibres

Let `f : M → N` be a Riemannian submersion. At a point `x` of `M`, horizontal lifts `X_i` of an
orthonormal basis of `T_(f x) N` together with an orthonormal basis `V_a` of the vertical space
`ker (df_x)` form an orthonormal basis of `T_x M`
(`IsRiemannianSubmersion.horizontalVerticalBasis`, in
`TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic`). The squared norm
`|A|² = ∑ i j, ‖A_(X_i) X_j‖²` of O'Neill's horizontal tensor
(`IsRiemannianSubmersion.oneillANormSq`, in
`TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.NormSq`) also satisfies
`∑ i a, ‖A_(X_i) V_a‖² = |A|²`.

Splitting the double trace `Scal = ∑ Rm(e_β, e_α, e_α, e_β)` in this adapted basis gives three
kinds of terms. The horizontal-horizontal terms are `Scal_N(f x) - 3 |A|²` by O'Neill's horizontal
curvature equation. When the vertical tensor `T` vanishes near `x`, that is when the fibres are
totally geodesic there, each mixed term is `‖A_(X_i) V_a‖²` by O'Neill's mixed curvature equation,
and the mixed terms add up to `2 |A|²`. Hence

`Scal_M(x) = Scal_N(f x) + ∑ a b, Rm_M(V_b, V_a, V_a, V_b) - |A|²`

(`IsRiemannianSubmersion.scalarCurvature_eq_of_eventually_oneillT_eq_zero`). The middle term is the
trace of the curvature of `M` over the vertical space. For totally geodesic fibres the Gauss
equation identifies it with the scalar curvature of the fibre through `x`, which turns this into
O'Neill's formula `Scal_M = Scal_N ∘ f + Scal_F - |A|²`; that identification is not made here.
This is the formula behind the scalar curvature `Scal_N + ε⁻² Scal_F - ε² |A|²` of a connection
metric whose totally geodesic fibres are scaled by `ε²`.

## Main results

* `TauCeti.IsRiemannianSubmersion.scalarCurvature_eq_of_eventually_oneillT_eq_zero`: O'Neill's
  scalar-curvature formula for totally geodesic fibres.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 and Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (Proposition 9.36 and
  Corollary 9.37).
-/

public section

open Bundle CovariantDerivative Filter Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)
  {ι κ : Type*} [Fintype ι] [Fintype κ]

include h

/-! ### The scalar-curvature formula -/

section Scalar

variable [T2Space M] [T2Space N] {x : M}

/-- **O'Neill's scalar-curvature formula for totally geodesic fibres.** If the vertical tensor `T`
vanishes near `x`, then for any orthonormal basis `V_a` of the vertical space `ker (df_x)`,
`Scal_M(x) = Scal_N(f x) + ∑ a b, Rm_M(V_b, V_a, V_a, V_b) - |A|²`. The middle term is the trace
of the curvature of `M` over the vertical space. -/
theorem scalarCurvature_eq_of_eventually_oneillT_eq_zero (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0)
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).scalarCurvature x =
      (leviCivitaConnection J N).scalarCurvature (f x) +
        (∑ a, ∑ a', (leviCivitaConnection I M).riemannCurvatureTensor x
          (c a') (c a) (c a) (c a')) - h.oneillANormSq x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  -- Each mixed term is `‖A_(X_i) V_a‖²`, whichever slot pair holds the horizontal vector.
  have hmixed (i) (a : κ) : (leviCivitaConnection I M).riemannCurvatureTensor x
      (h.horizontalLift x (b i)) (c a) (c a) (h.horizontalLift x (b i)) =
      ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 := by
    rw [riemannCurvatureTensor_apply]
    exact h.inner_curvatureTensor_horizontal_vertical_self_of_eventually_oneillT_eq_zero hT
      (h.horizontalLift_mem_orthogonal_ker x (b i)) (c a).property
  have hmixed' (i) (a : κ) : (leviCivitaConnection I M).riemannCurvatureTensor x
      (c a) (h.horizontalLift x (b i)) (h.horizontalLift x (b i)) (c a) =
      ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 := by
    rw [← hmixed, IsMetricCompatible.riemannCurvatureTensor_swap_pairs _
      (isMetricCompatible_leviCivitaConnection I) (torsion_leviCivitaConnection_eq_zero I)]
  have hA := h.sum_sum_norm_oneillA_horizontalLift_vertical b c
  have hA' : ∑ a, ∑ i, ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 =
      h.oneillANormSq x := by
    rw [Finset.sum_comm]
    exact hA
  have hhor := h.scalarCurvature_eq_sum_horizontalLift b
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i ↦ ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2),
    ← h.oneillANormSq_eq_sum x b] at hhor
  rw [(leviCivitaConnection I M).scalarCurvature_eq_sum_riemannCurvatureTensor x
    (h.horizontalVerticalBasis x b c)]
  simp only [Fintype.sum_sum_type, horizontalVerticalBasis_inl, horizontalVerticalBasis_inr,
    Finset.sum_add_distrib, hmixed, hmixed']
  linarith

end Scalar

end TauCeti.IsRiemannianSubmersion
