/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
import TauCeti.Analysis.Calculus.Morse.GlobalChart
import TauCeti.Analysis.Calculus.Morse.Transversality
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Analysis.ODE.EnergyEstimate.HalfLine
import TauCeti.Dynamics.Flow.TangentCone

/-!
# The linearized trajectory operator detects Morse–Smale transversality

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, `φ` its negative-gradient flow, and `y` a point on a trajectory running from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. In
Schwarz's functional-analytic construction of Morse homology, the trajectories from `p` to `q`
are the zeros of a Fredholm section whose linearization along `s ↦ φ s y` is the trajectory
operator

`D ξ = ξ' + Hess f(φ s y) ξ : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`IsIntegralCurve.isFredholm_trajectoryOperator_hessianOperator`). This file shows that
this realization agrees with the finite-dimensional one: the kernel of `D` is the intersection
`T_y W^u(p) ∩ T_y W^s(q)` of the tangent spaces of the unstable and stable sets, and `D` is
surjective exactly when `W^u(p)` and `W^s(q)` meet transversally at `y`. So the Morse–Smale
condition, stated with tangent spaces, is the regularity of every trajectory in the sense of
Fredholm theory.

The comparison goes through the variational equation: for `v ∈ E`, `w(s) = Dφ_s(y) v` is the
solution of `w' = -Hess f(φ s y) w` with initial value `v`. The tangent space of the stable set
is carried along the trajectory by `Dφ_s(y)`, so we show that `T_y W^s(q)` is the space
`TauCeti.squareIntegrableSolutionsOn _ (Ioi 0)` of initial values of the solutions that are square
integrable on `(0, ∞)`.

* Near `q` the stable set is straightened by a chart tangent to the identity at `q`
  (`TauCeti.IsNondegenerateCriticalPoint.exists_stableSet_chart_hasFDerivAt_id`), onto the
  positive spectral subspace of `Hess f(q)`, on which the Hessian form is coercive. So for large
  `s`, the tangent vector `w(s)` has `⟪w(s), Hess f(q) w(s)⟫ ≥ 0`, and the Lyapunov argument of
  `TauCeti.memLp_restrict_Ici_of_eventually_inner_nonneg` makes `w` square integrable.
* Both spaces have dimension `dim E - ind q`
  (`TauCeti.IsNondegenerateCriticalPoint.finrank_span_tangentConeAt_stableSet_add_morseIndex` and
  `IsIntegralCurve.finrank_squareIntegrableSolutionsOn_Ioi_hessianOperator_add_morseIndex`), so
  the inclusion is an equality.

The unstable set is treated in the same way at `-∞`. A square-integrable solution on the whole
line is one that is square integrable on both half-lines, which identifies the kernel of `D`
(`TauCeti.squareIntegrableSolutions`) with `T_y W^u(p) ∩ T_y W^s(q)`. With these identifications
`IsIntegralCurve.surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top` becomes the
surjectivity criterion.

## Main results

* `IsNondegenerateCriticalPoint.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn`
  and `IsNondegenerateCriticalPoint.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn`
  (in namespace `TauCeti`):
  the tangent space of the stable (unstable) set is the space of initial values of the solutions
  of the linearized equation that are square integrable in forward (backward) time.
* `TauCeti.IsNondegenerateCriticalPoint.mem_span_tangentConeAt_stableSet_iff_memLp` and
  `TauCeti.IsNondegenerateCriticalPoint.mem_span_tangentConeAt_unstableSet_iff_memLp`: a vector is
  tangent to the stable (unstable) set exactly when its image under the derivative of the flow is
  square integrable in forward (backward) time.
* `TauCeti.squareIntegrableSolutions_hessianOperator_negativeGradientFlow`: the square-integrable
  solutions of the linearized equation are the common tangent vectors of `W^u(p)` and `W^s(q)`.
* `TauCeti.finrank_ker_trajectoryOperator_hessianOperator_negativeGradientFlow`: the kernel of the
  linearized operator has the dimension of `T_y W^u(p) ∩ T_y W^s(q)`.
* `TauCeti.surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff`: the linearized
  operator is surjective exactly when `W^u(p)` and `W^s(q)` are transverse at `y`.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, §2.3 (regularity of the linearized operator
  and transversality of unstable and stable manifolds).
* D. Salamon, *Morse theory, the Conley index and Floer homology*, Bull. London Math. Soc. **22**
  (1990), 113--140, §2.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient NNReal RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0} {p q y : E}

/-- The variational equation applied to a vector: `s ↦ Dφ_s(y) v` solves
`w' = -Hess f(φ s y) w`. -/
private theorem hasDerivAt_fderiv_negativeGradientFlow_apply (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (y v : E) (s : ℝ) :
    HasDerivAt (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v)
      (-hessianOperator f (negativeGradientFlow f hf s y)
        (fderiv ℝ (negativeGradientFlow f hf s) y v)) s := by
  have h := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_fderiv_negativeGradientFlow f hf hfs y s)
  simpa [fderiv_gradient, Function.comp_def] using h

/-- The coefficient `s ↦ Hess f(φ s y)` of the linearized equation is continuous. -/
private theorem continuous_hessianOperator_negativeGradientFlow (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (y : E) :
    Continuous fun s ↦ hessianOperator f (negativeGradientFlow f hf s y) :=
  (hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.comp
    ((contDiff_negativeGradientFlow f hf hfs).continuous.comp
      (continuous_id.prodMk continuous_const))

/-- The solution of the linearized equation with initial value `v` is `s ↦ Dφ_s(y) v`, so `v` is
the initial value of a solution square integrable on `S` exactly when that one is. -/
private theorem mem_squareIntegrableSolutionsOn_hessianOperator_negativeGradientFlow
    (hf : LipschitzWith K (∇ f)) (hfs : ContDiff ℝ 2 f) (y : E) {S : Set ℝ} {v : E} :
    v ∈ squareIntegrableSolutionsOn
        (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) S ↔
      MemLp (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v) 2 (volume.restrict S) := by
  have hw := hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v
  have hw0 : fderiv ℝ (negativeGradientFlow f hf 0) y v = v := by simp [Flow.map_zero]
  rw [mem_squareIntegrableSolutionsOn]
  refine ⟨fun ⟨w, hw0', hws, hw2⟩ ↦ ?_, fun h ↦ ⟨_, hw0, hw, h⟩⟩
  -- A solution is determined by its initial value.
  have hweq : w = fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v :=
    (continuous_hessianOperator_negativeGradientFlow hf hfs y).neg.eq_of_hasDerivAt_clm_apply
      (t₀ := 0) hws hw (hw0'.trans hw0.symm)
  exact hweq ▸ hw2

namespace IsNondegenerateCriticalPoint

/-- **The tangent space of a stable set is the space of stable linearized solutions.** Let `q` be
a nondegenerate critical point of a `C²` function with globally Lipschitz gradient, and `y` a
point of its stable set. The tangent space at `y` of the stable set of `q` consists of the initial
values of the solutions of the linearized equation `w' = -Hess f(φ s y) w` that are square
integrable on `(0, ∞)`. -/
theorem span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) =
      squareIntegrableSolutionsOn (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y))
        (Ioi 0) := by
  set φ := negativeGradientFlow f hf with hφ
  set B := hessianOperator f q
  have hBsym := hq.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨α, hα, hBα⟩ := hq.exists_pos_mul_norm_le_hessianOperator
  have hA : Tendsto (fun s ↦ hessianOperator f (φ s y)) atTop (𝓝 B) :=
    ((hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.tendsto q).comp
      (Flow.mem_stableSet.1 hy)
  have hd (t : ℝ) (z : E) : DifferentiableAt ℝ (φ t) z :=
    differentiable_negativeGradientFlow_apply f hf hfs t z
  obtain ⟨c, hc, hcs, -⟩ := hq.contDiffAt.exists_pos_mul_norm_sq_le_inner_hessianOperator
  have hγ : IsIntegralCurve (fun s ↦ φ s y) (fun _ x ↦ -∇ f x) :=
    (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
  refine Submodule.eq_of_le_of_finrank_le (fun v hv ↦ ?_) ?_
  -- Tangent vectors give solutions that are square integrable on `[0, ∞)`.
  · rw [mem_squareIntegrableSolutionsOn_hessianOperator_negativeGradientFlow hf hfs]
    obtain ⟨e, hqe, hed, heC, heCs, heS⟩ :=
      hq.exists_stableSet_chart_hasFDerivAt_id (n := 1) hfs hf
    have hcone := (isSliceChart_iff.2 heS).eventually_forall_mem_span_tangentConeAt_inner_nonneg
      (Submodule.closed_of_finiteDimensional _) (B := B) hqe hed heC heCs hc hcs
    refine (memLp_restrict_Ici_of_eventually_inner_nonneg hA hBsym hα hBα
      (hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v) ?_ 0).mono_measure
      (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)
    filter_upwards [(Flow.mem_stableSet.1 hy).eventually hcone] with s hs
    rw [real_inner_comm]
    refine hs (Flow.isInvariant_stableSet φ q s hy) _ ?_
    rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_stableSet φ q) (hd _ _) (hd _ _)]
    exact Submodule.mem_map_of_mem hv
  -- Both spaces have dimension `dim E - ind q`.
  · have h₁ := hγ.finrank_squareIntegrableSolutionsOn_Ioi_hessianOperator_add_morseIndex hfs hq
      (Flow.mem_stableSet.1 hy)
    have h₂ := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hy
    rw [← hφ] at h₂
    omega

/-- **The tangent space of an unstable set is the space of unstable linearized solutions.** Let
`p` be a nondegenerate critical point of a `C²` function with globally Lipschitz gradient, and `y`
a point of its unstable set. The tangent space at `y` of the unstable set of `p` consists of the
initial values of the solutions of the linearized equation `w' = -Hess f(φ s y) w` that are
square integrable on `(-∞, 0)`. -/
theorem span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn
    (hp : IsNondegenerateCriticalPoint f p) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) =
      squareIntegrableSolutionsOn (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y))
        (Iio 0) := by
  set φ := negativeGradientFlow f hf with hφ
  set B := hessianOperator f p
  have hBsym := hp.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨α, hα, hBα⟩ := hp.exists_pos_mul_norm_le_hessianOperator
  have hA : Tendsto (fun s ↦ hessianOperator f (φ s y)) atBot (𝓝 B) :=
    ((hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.tendsto p).comp
      (Flow.mem_unstableSet.1 hy)
  have hd (t : ℝ) (z : E) : DifferentiableAt ℝ (φ t) z :=
    differentiable_negativeGradientFlow_apply f hf hfs t z
  obtain ⟨c, hc, -, hcu⟩ := hp.contDiffAt.exists_pos_mul_norm_sq_le_inner_hessianOperator
  have hγ : IsIntegralCurve (fun s ↦ φ s y) (fun _ x ↦ -∇ f x) :=
    (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
  refine Submodule.eq_of_le_of_finrank_le (fun v hv ↦ ?_) ?_
  -- Tangent vectors give solutions that are square integrable on `(-∞, 0]`.
  · rw [mem_squareIntegrableSolutionsOn_hessianOperator_negativeGradientFlow hf hfs]
    obtain ⟨e, hpe, hed, heC, heCs, heS⟩ :=
      hp.exists_unstableSet_chart_hasFDerivAt_id (n := 1) hfs hf
    have hcone := (isSliceChart_iff.2 heS).eventually_forall_mem_span_tangentConeAt_inner_nonneg
      (Submodule.closed_of_finiteDimensional _) (B := -B) hpe hed heC heCs hc fun u hu ↦ by
        rw [neg_apply, inner_neg_left]
        linarith [hcu u hu]
    refine (memLp_restrict_Iic_of_eventually_inner_nonpos hA hBsym hα hBα
      (hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v) ?_ 0).mono_measure
      (Measure.restrict_mono Iio_subset_Iic_self le_rfl)
    filter_upwards [(Flow.mem_unstableSet.1 hy).eventually hcone] with s hs
    have h := hs (Flow.isInvariant_unstableSet φ p s hy) (fderiv ℝ (φ s) y v) (by
      rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_unstableSet φ p) (hd _ _) (hd _ _)]
      exact Submodule.mem_map_of_mem hv)
    rw [neg_apply, inner_neg_left, real_inner_comm] at h
    linarith
  -- Both spaces have dimension `ind p`.
  · have h₁ := hγ.finrank_squareIntegrableSolutionsOn_Iio_hessianOperator hfs hp
      (Flow.mem_unstableSet.1 hy)
    have h₂ := hp.finrank_span_tangentConeAt_unstableSet hfs hf hy
    rw [← hφ] at h₂
    omega

/-- **Tangent vectors of a stable set decay along the flow.** Let `q` be a nondegenerate critical
point of a `C²` function with globally Lipschitz gradient, and `y` a point of its stable set. A
vector `v` is tangent to the stable set of `q` at `y` exactly when `s ↦ Dφ_s(y) v`, the solution
of the linearized equation `w' = -Hess f(φ s y) w` with initial value `v`, is square integrable
on `[0, ∞)`. -/
theorem mem_span_tangentConeAt_stableSet_iff_memLp (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) {v : E} :
    v ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) ↔
      MemLp (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v) 2 (volume.restrict (Ici 0)) := by
  rw [hq.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hfs hf hy,
    mem_squareIntegrableSolutionsOn_hessianOperator_negativeGradientFlow hf hfs,
    Measure.restrict_congr_set Ioi_ae_eq_Ici]

/-- **Tangent vectors of an unstable set decay along the flow in backward time.** Let `p` be a
nondegenerate critical point of a `C²` function with globally Lipschitz gradient, and `y` a point
of its unstable set. A vector `v` is tangent to the unstable set of `p` at `y` exactly when
`s ↦ Dφ_s(y) v`, the solution of the linearized equation `w' = -Hess f(φ s y) w` with initial
value `v`, is square integrable on `(-∞, 0]`. -/
theorem mem_span_tangentConeAt_unstableSet_iff_memLp (hp : IsNondegenerateCriticalPoint f p)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p) {v : E} :
    v ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ↔
      MemLp (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v) 2 (volume.restrict (Iic 0)) := by
  rw [hp.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn hfs hf hy,
    mem_squareIntegrableSolutionsOn_hessianOperator_negativeGradientFlow hf hfs,
    Measure.restrict_congr_set Iio_ae_eq_Iic]

end IsNondegenerateCriticalPoint

/-- **Square-integrable linearized solutions are common tangent vectors.** Let `y` lie on a
trajectory from a nondegenerate critical point `p` to a nondegenerate critical point `q` of a
`C²` function with globally Lipschitz gradient. The initial values of the square-integrable
solutions of `w' = -Hess f(φ s y) w` are exactly the vectors tangent at `y` to both the unstable
set of `p` and the stable set of `q`. -/
theorem squareIntegrableSolutions_hessianOperator_negativeGradientFlow
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    squareIntegrableSolutions (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) =
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) := by
  rw [← squareIntegrableSolutionsOn_Iio_inf_Ioi
      (continuous_hessianOperator_negativeGradientFlow hf hfs y),
    hp.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn hfs hf hyu,
    hq.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hfs hf hys]

/-- **The kernel of the linearized operator.** Let `y` lie on a trajectory from a nondegenerate
critical point `p` to a nondegenerate critical point `q` of a `C²` function with globally
Lipschitz gradient. The kernel of `ξ ↦ ξ' + Hess f(φ s y) ξ` on `W^{1,2}(ℝ, E)` has the dimension
of `T_y W^u(p) ∩ T_y W^s(q)`. -/
theorem finrank_ker_trajectoryOperator_hessianOperator_negativeGradientFlow
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) :
    Module.finrank ℝ (WeakDerivStep.trajectoryOperator (p := 2) AL).ker =
      Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊓
          Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) :
            Submodule ℝ E) := by
  rw [WeakDerivStep.finrank_ker_trajectoryOperator
      (continuous_hessianOperator_negativeGradientFlow hf hfs y) AL hAL,
    squareIntegrableSolutions_hessianOperator_negativeGradientFlow hp hq hfs hf hyu hys]

/-- **The linearized operator is onto exactly at transverse trajectories.** Let `f` be a `C²`
function with globally Lipschitz gradient on a finite-dimensional real inner product space, and
`y` a point on a negative-gradient trajectory from a nondegenerate critical point `p` to a
nondegenerate critical point `q`. The linearized operator `ξ ↦ ξ' + Hess f(φ s y) ξ` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is surjective if and only if the unstable set of `p` and the stable
set of `q` are transverse at `y`: their tangent spaces at `y` span `E`. -/
theorem surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow f hf) q)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) :
    Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) ↔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) =
          ⊤ := by
  rw [hp.span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn hfs hf hyu,
    hq.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hfs hf hys]
  exact ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
    ).surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top hfs hp hq
      (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys) hAL

end TauCeti
