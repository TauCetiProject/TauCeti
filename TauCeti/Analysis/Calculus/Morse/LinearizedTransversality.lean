/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
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

The bridge is the variational equation: for `v ∈ E`, `w(s) = Dφ_s(y) v` solves
`w' = -Hess f(φ s y) w`. The tangent space of the stable set is carried along the trajectory by
`Dφ_s(y)`, so we must show that `v ∈ T_y W^s(q)` exactly when `w` is square integrable on
`[0, ∞)`.

* Near `q` the stable set is straightened by a chart tangent to the identity at `q`
  (`TauCeti.IsNondegenerateCriticalPoint.exists_stableSet_chart_hasFDerivAt_id`), onto the
  positive spectral subspace of `Hess f(q)`, on which the Hessian form is coercive. So for large
  `s`, the tangent vector `w(s)` has `⟪w(s), Hess f(q) w(s)⟫ ≥ 0`, and the Lyapunov argument of
  `TauCeti.memLp_restrict_Ici_of_eventually_inner_nonneg` makes `w` square integrable.
* Conversely, at a late time `T` the square-integrable solutions miss the negative spectral
  subspace of `Hess f(q)`, by `TauCeti.eventually_not_memLp_restrict_Ici_of_inner_neg`, so they
  form a space of dimension at most `dim E - ind q`, the dimension of `T_y W^s(q)`.

The unstable set is treated in the same way at `-∞`. A square-integrable solution on the whole
line is one that is square integrable on both half-lines, which identifies the kernel of `D`
(`TauCeti.squareIntegrableSolutions`) with `T_y W^u(p) ∩ T_y W^s(q)`. Comparing dimensions with
the index `ind p - ind q` of `D` gives the surjectivity criterion.

## Main results

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
* `TauCeti.isMorseSmale_iff_forall_surjective_trajectoryOperator_negativeGradientFlow`:
  a function is Morse–Smale exactly when the linearized operator along each trajectory between
  nondegenerate critical points is surjective.

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

/-- The initial values `v` for which `s ↦ Dφ_s(y) v` lies in `L²(μ)`. -/
private def memLpSolutions (hf : LipschitzWith K (∇ f)) (y : E) (μ : Measure ℝ) :
    Submodule ℝ E where
  carrier := {v | MemLp (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v) 2 μ}
  add_mem' {v w} hv hw := by simpa only [mem_ofPred_eq, map_add, Pi.add_def] using hv.add hw
  zero_mem' := by
    simpa only [mem_ofPred_eq, map_zero, Pi.zero_def] using (MemLp.zero : MemLp (0 : ℝ → E) 2 μ)
  smul_mem' c v hv := by
    simpa only [mem_ofPred_eq, map_smul, Pi.smul_def] using hv.const_smul c

private theorem mem_memLpSolutions (hf : LipschitzWith K (∇ f)) {y : E} {μ : Measure ℝ} {v : E} :
    v ∈ memLpSolutions hf y μ ↔ MemLp (fun s ↦ fderiv ℝ (negativeGradientFlow f hf s) y v) 2 μ :=
  Iff.rfl

/-- **The square-integrable solutions miss a subspace of the wrong sign.** Suppose that at a time
`T` no solution of the linearized equation with `⟪w T, B (w T)⟫ < 0` lies in `L²(μ)`, and that
the form of `B` is negative definite on `U`. Then `Dφ_T(y)` maps the initial values of the
square-integrable solutions to a subspace disjoint from `U`, so their dimensions add up to at
most `dim E`. -/
private theorem finrank_memLpSolutions_add_finrank_le (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (y : E) {μ : Measure ℝ} {B : E →L[ℝ] E} {U : Submodule ℝ E} {c : ℝ}
    (hc : 0 < c) (hU : ∀ u ∈ U, ⟪B u, u⟫ ≤ -(c * ‖u‖ ^ 2)) {T : ℝ}
    (hT : ∀ w : ℝ → E,
      (∀ s, HasDerivAt w (-hessianOperator f (negativeGradientFlow f hf s y) (w s)) s) →
        ⟪w T, B (w T)⟫ < 0 → ¬ MemLp w 2 μ) :
    Module.finrank ℝ (memLpSolutions hf y μ) + Module.finrank ℝ U ≤ Module.finrank ℝ E := by
  have hd (t : ℝ) (z : E) : DifferentiableAt ℝ (negativeGradientFlow f hf t) z :=
    differentiable_negativeGradientFlow_apply f hf hfs t z
  obtain ⟨L, hL⟩ := (negativeGradientFlow f hf).isInvertible_fderiv (t := T) (x := y)
    (hd _ _) (hd _ _)
  have hdisj : Disjoint ((memLpSolutions hf y μ).map (L : E →ₗ[ℝ] E)) U := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨v, hv, rfl⟩ hu
    by_contra hne
    have hneg := hU _ hu
    have hpos : 0 < c * ‖(L : E →ₗ[ℝ] E) v‖ ^ 2 := by positivity
    refine hT _ (hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v) ?_
      (mem_memLpSolutions hf |>.1 hv)
    rw [real_inner_comm, ← hL, ContinuousLinearEquiv.coe_coe]
    -- The coercions of `L` to a linear map and to a function agree definitionally.
    have hLv : (L : E →ₗ[ℝ] E) v = L v := rfl
    rw [hLv] at hneg hpos
    linarith
  have h := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  rwa [LinearEquiv.finrank_map_eq L.toLinearEquiv] at h

namespace IsNondegenerateCriticalPoint

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
  set φ := negativeGradientFlow f hf with hφ
  set B := hessianOperator f q
  have hBsym := hq.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨α, hα, hBα⟩ := hq.exists_pos_mul_norm_le_hessianOperator
  have hA : Tendsto (fun s ↦ hessianOperator f (φ s y)) atTop (𝓝 B) :=
    ((hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.tendsto q).comp
      (Flow.mem_stableSet.1 hy)
  have hw (v : E) := hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v
  have hd (t : ℝ) (z : E) : DifferentiableAt ℝ (φ t) z :=
    differentiable_negativeGradientFlow_apply f hf hfs t z
  obtain ⟨c, hc, hcs, hcu⟩ := hq.contDiffAt.exists_pos_mul_norm_sq_le_inner_hessianOperator
  -- Tangent vectors give solutions that are square integrable on `[0, ∞)`.
  have hle : Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet φ q) y) ≤
      memLpSolutions hf y (volume.restrict (Ici 0)) := by
    intro v hv
    obtain ⟨e, hqe, hed, heC, heCs, heS⟩ :=
      hq.exists_stableSet_chart_hasFDerivAt_id (n := 1) hfs hf
    have hcone := (isSliceChart_iff.2 heS).eventually_forall_mem_span_tangentConeAt_inner_nonneg
      (Submodule.isClosed_of_finiteDimensional _) (B := B) hqe hed heC heCs hc hcs
    refine memLp_restrict_Ici_of_eventually_inner_nonneg hA hBsym hα hBα (hw v) ?_ 0
    filter_upwards [(Flow.mem_stableSet.1 hy).eventually hcone] with s hs
    rw [real_inner_comm]
    refine hs (Flow.isInvariant_stableSet φ q s hy) _ ?_
    rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_stableSet φ q) (hd _ _) (hd _ _)]
    exact Submodule.mem_map_of_mem hv
  -- At a late time `T`, the square-integrable solutions miss the negative spectral subspace.
  have hfin : Module.finrank ℝ (memLpSolutions hf y (volume.restrict (Ici 0))) + morseIndex f q ≤
      Module.finrank ℝ E := by
    obtain ⟨T, hT⟩ := (eventually_not_memLp_restrict_Ici_of_inner_neg hA hBsym hα hBα 0).exists
    rw [← hq.contDiffAt.finrank_unstableLinearSubspace]
    exact finrank_memLpSolutions_add_finrank_le hf hfs y hc hcu hT
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    have := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hy
    rw [← hφ] at this
    omega)
  rw [heq, mem_memLpSolutions]

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
  set φ := negativeGradientFlow f hf with hφ
  set B := hessianOperator f p
  have hBsym := hp.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨α, hα, hBα⟩ := hp.exists_pos_mul_norm_le_hessianOperator
  have hA : Tendsto (fun s ↦ hessianOperator f (φ s y)) atBot (𝓝 B) :=
    ((hfs.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.tendsto p).comp
      (Flow.mem_unstableSet.1 hy)
  have hw (v : E) := hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v
  have hd (t : ℝ) (z : E) : DifferentiableAt ℝ (φ t) z :=
    differentiable_negativeGradientFlow_apply f hf hfs t z
  obtain ⟨c, hc, hcs, hcu⟩ := hp.contDiffAt.exists_pos_mul_norm_sq_le_inner_hessianOperator
  -- Tangent vectors give solutions that are square integrable on `(-∞, 0]`.
  have hle : Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet φ p) y) ≤
      memLpSolutions hf y (volume.restrict (Iic 0)) := by
    intro v hv
    obtain ⟨e, hpe, hed, heC, heCs, heS⟩ :=
      hp.exists_unstableSet_chart_hasFDerivAt_id (n := 1) hfs hf
    have hcone := (isSliceChart_iff.2 heS).eventually_forall_mem_span_tangentConeAt_inner_nonneg
      (Submodule.isClosed_of_finiteDimensional _) (B := -B) hpe hed heC heCs hc fun u hu ↦ by
        rw [neg_apply, inner_neg_left]
        linarith [hcu u hu]
    refine memLp_restrict_Iic_of_eventually_inner_nonpos hA hBsym hα hBα (hw v) ?_ 0
    filter_upwards [(Flow.mem_unstableSet.1 hy).eventually hcone] with s hs
    have h := hs (Flow.isInvariant_unstableSet φ p s hy) (fderiv ℝ (φ s) y v) (by
      rw [Flow.span_tangentConeAt_apply (Flow.isInvariant_unstableSet φ p) (hd _ _) (hd _ _)]
      exact Submodule.mem_map_of_mem hv)
    rw [neg_apply, inner_neg_left, real_inner_comm] at h
    linarith
  -- At an early time `T`, the square-integrable solutions miss the positive spectral subspace.
  have hfin : Module.finrank ℝ (memLpSolutions hf y (volume.restrict (Iic 0))) +
      Module.finrank ℝ hp.contDiffAt.stableLinearSubspace ≤ Module.finrank ℝ E := by
    obtain ⟨T, hT⟩ := (eventually_not_memLp_restrict_Iic_of_inner_pos hA hBsym hα hBα 0).exists
    -- Backward time is the forward-time argument for `-B`.
    refine finrank_memLpSolutions_add_finrank_le hf hfs y (B := -B) hc (fun u hu ↦ ?_)
      fun w hw' hneg ↦ hT w hw' (by simpa [inner_neg_right] using hneg)
    rw [neg_apply, inner_neg_left]
    linarith [hcs u hu]
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    have := hp.finrank_span_tangentConeAt_unstableSet hfs hf hy
    rw [← hφ] at this
    have := hp.finrank_stableLinearSubspace_add_morseIndex
    have := morseIndex_le_finrank (f := f) (x := p)
    omega)
  rw [heq, mem_memLpSolutions]

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
  set φ := negativeGradientFlow f hf
  have hAc := continuous_hessianOperator_negativeGradientFlow hf hfs y
  have hw (v : E) := hasDerivAt_fderiv_negativeGradientFlow_apply hf hfs y v
  have hw0 (v : E) : fderiv ℝ (φ 0) y v = v := by simp [φ, Flow.map_zero]
  have hwc (v : E) : Continuous fun s ↦ fderiv ℝ (φ s) y v :=
    continuous_iff_continuousAt.2 fun s ↦ (hw v s).continuousAt
  ext v
  rw [mem_squareIntegrableSolutions, Submodule.mem_inf,
    hp.mem_span_tangentConeAt_unstableSet_iff_memLp hfs hf hyu,
    hq.mem_span_tangentConeAt_stableSet_iff_memLp hfs hf hys]
  constructor
  · rintro ⟨w, rfl, hws, hw2⟩
    -- A solution is determined by its initial value, so `w` is `s ↦ Dφ_s(y) (w 0)`.
    have hweq : w = fun s ↦ fderiv ℝ (φ s) y (w 0) :=
      hAc.neg.eq_of_hasDerivAt_clm_apply (t₀ := 0) hws (hw (w 0)) (hw0 (w 0)).symm
    rw [← hweq]
    exact ⟨hw2.restrict _, hw2.restrict _⟩
  · rintro ⟨hbot, htop⟩
    refine ⟨_, hw0 v, hw v, (memLp_two_iff_integrable_sq_norm (hwc v).aestronglyMeasurable).2 ?_⟩
    have hIic := (memLp_two_iff_integrable_sq_norm (hwc v).aestronglyMeasurable).1 hbot
    have hIci := (memLp_two_iff_integrable_sq_norm (hwc v).aestronglyMeasurable).1 htop
    rw [← integrableOn_univ, ← Iic_union_Ici (a := (0 : ℝ))]
    exact IntegrableOn.union hIic hIci

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

open WeakDerivStep in
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
  have hγ : IsIntegralCurve (fun s ↦ negativeGradientFlow f hf s y) (fun _ x ↦ -∇ f x) :=
    (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
  have hbot := Flow.mem_unstableSet.1 hyu
  have htop := Flow.mem_stableSet.1 hys
  have hindex := hγ.index_trajectoryOperator_hessianOperator hfs hp hq hbot htop hAL
  have hclosed := (hγ.isFredholm_trajectoryOperator_hessianOperator hfs hp hq hbot htop
    hAL).isClosed_range
  -- The Hessian is symmetric, so the coefficient is its own pointwise adjoint.
  have hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact hfs.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric.clm_adjoint_eq.symm
  -- The kernel of the formal adjoint is finite dimensional: it is a space of solutions of a linear
  -- equation on `E`.
  have hA := (continuous_hessianOperator_negativeGradientFlow hf hfs y).neg
  have := (kerTrajectoryOperatorEquiv hA (-AL) (by
    filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs
    simp only [hs, Pi.neg_apply, hAs])).symm.finiteDimensional
  rw [index_trajectoryOperator_of_isClosed_range hadj hclosed,
    finrank_ker_trajectoryOperator_hessianOperator_negativeGradientFlow hp hq hfs hf hyu hys
      hAL] at hindex
  rw [surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj hclosed, ← Submodule.finrank_eq_zero]
  -- Compare dimensions: `dim (Tᵘ ⊔ Tˢ) + dim (Tᵘ ⊓ Tˢ) = ind p + (dim E - ind q)`.
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y))
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y))
  have hu := hp.finrank_span_tangentConeAt_unstableSet hfs hf hyu
  have hs := hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hys
  have hle := Submodule.finrank_le
    (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y))
  constructor
  · intro h0
    exact Submodule.eq_top_of_finrank_eq (by omega)
  · intro htop
    rw [htop, finrank_top] at hsum
    omega


/-- **Morse–Smale functions are those whose linearized operators are onto.** A `C²` function with
globally Lipschitz gradient on a finite-dimensional real inner product space is Morse–Smale if and
only if, along every trajectory of its negative-gradient flow joining two nondegenerate critical
points, the linearized operator `ξ ↦ ξ' + Hess f(φ s y) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is
surjective. -/
theorem isMorseSmale_iff_forall_surjective_trajectoryOperator_negativeGradientFlow
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q y : E⦄, IsNondegenerateCriticalPoint f p →
      IsNondegenerateCriticalPoint f q →
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      ∀ AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
        AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) →
        Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) := by
  refine ⟨fun h p q y hp hq hyu hys AL hAL ↦
    (surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp hq hfs hf hyu hys
      hAL).2 (h.transverse_at hp hq ⟨hyu, hys⟩),
    fun h ↦ .of_forall fun p q y hp hq hy ↦ ?_⟩
  obtain ⟨hyu, hys⟩ := hy
  -- The Hessian along the trajectory has an `L∞` class, to which the hypothesis applies.
  have hmem := hfs.memLp_top_hessianOperator_comp
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).continuous
    (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys)
    (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
  exact (surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp hq hfs hf hyu
    hys hmem.coeFn_toLp).1 (h hp hq hyu hys _ hmem.coeFn_toLp)

end TauCeti
