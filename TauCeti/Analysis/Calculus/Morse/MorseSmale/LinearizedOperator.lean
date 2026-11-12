/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.LocalInvariantManifold

/-!
# Morse–Smale transversality is surjectivity of the linearized operators

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, `φ` its negative gradient flow, and `γ(t) = φ_t y` the trajectory through a
point `y` of `W^u(p) ∩ W^s(q)`, for nondegenerate critical points `p` and `q`. There are two
descriptions of the regularity of `γ`:

* the dynamical one, the Morse–Smale condition at `y`: the tangent spaces at `y` of the unstable
  set of `p` and of the stable set of `q` span `E`;
* the functional-analytic one: the linearized operator `D_γ ξ = ξ' + Hess f(γ) ξ` from
  `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is surjective.

`IsIntegralCurve.surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top` reduces the second
to the condition that the initial values of the solutions of `v' + Hess f(γ) v = 0` that are
square integrable on `(-∞, 0)` and those square integrable on `(0, ∞)` span `E`. This file
identifies these two spaces of linearized solutions with the two tangent spaces, so the two
descriptions agree.

The tangent space of the stable set of `q` at `y` is mapped into the decaying solutions by the
derivative of the flow: `t ↦ Dφ_t(y) v` solves the linearized equation, by the variational
equation of the flow. It decays exponentially when `v` is tangent to the stable set, because the
flow contracts the stable set exponentially near `y`: near `q` two trajectories confined to a
small ball approach each other exponentially (the Lyapunov–Perron estimate
`TauCeti.IsNondegenerateCriticalPoint.exists_norm_sub_le_of_isIntegralCurveOn_mapsTo_closedBall`),
every trajectory of the stable set starting near `γ(T)` stays in that ball for large `T`
(`TauCeti.IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_stableSet`), and the
time-`T` map is Lipschitz. A Lipschitz bound along a set bounds the differential on its tangent cone
(`HasFDerivWithinAt.norm_apply_le_of_mem_tangentConeAt`). Both spaces have dimension
`dim E - ind(q)`, so the inclusion is an equality. The unstable set of `p` for `f` is the stable
set of `p` for `-f`, whose flow is that of `f` run backwards
(`TauCeti.negativeGradientFlow_neg`), and its decaying solutions are the reflected ones
(`TauCeti.squareIntegrableSolutionsOn_Iio_eq_Ioi`).

## Main results

In the namespace `TauCeti.IsNondegenerateCriticalPoint`:

* `exists_norm_negativeGradientFlow_sub_le_of_mem_stableSet`: the negative gradient flow contracts
  the stable set of a nondegenerate critical point exponentially near each of its points.
* `exists_norm_fderiv_negativeGradientFlow_apply_le`: the derivative of the
  flow makes the tangent vectors of the stable set decay exponentially.
* `span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn` and
  `span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn`: the tangent spaces of the
  stable set of `q` and of the unstable set of `p` at `y` are the initial values of the solutions
  of the linearized equation along `t ↦ φ_t y` that are square integrable on `(0, ∞)`,
  respectively on `(-∞, 0)`.
* `surjective_trajectoryOperator_hessianOperator_iff_span_tangentConeAt_sup_eq_top`: the
  linearized operator along the trajectory through `y ∈ W^u(p) ∩ W^s(q)` is surjective exactly
  when `W^u(p)` and `W^s(q)` are transverse at `y`.

In the namespace `TauCeti`:

* `isMorseSmale_iff_forall_surjective_trajectoryOperator`: a `C²` function with globally Lipschitz
  gradient is Morse–Smale exactly when the linearized operator along every trajectory joining two
  nondegenerate critical points is surjective.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (surjectivity of the linearized operator and transversality of unstable and stable manifolds).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. **7**, 1999, Lecture 2 (the linearized operator is onto exactly when the unstable and
  stable manifolds intersect transversally).
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Gradient NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0} {p q x y : E}

namespace IsNondegenerateCriticalPoint

/-- **The negative gradient flow contracts the stable set exponentially.** Let `x` be a
nondegenerate critical point of a differentiable function `f` with globally Lipschitz gradient,
and `y` a point of its stable set. There are a constant `C` and a rate `β > 0` such that every
point `z` of the stable set near `y` satisfies `‖φ_t z - φ_t y‖ ≤ C * exp (-β t) * ‖z - y‖` at
all times `t ≥ 0`. -/
theorem exists_norm_negativeGradientFlow_sub_le_of_mem_stableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) (hd : Differentiable ℝ f)
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) x) :
    ∃ C : ℝ, ∃ β > (0 : ℝ), ∀ᶠ z in 𝓝 y, z ∈ Flow.stableSet (negativeGradientFlow f hf) x →
      ∀ t, 0 ≤ t → ‖negativeGradientFlow f hf t z - negativeGradientFlow f hf t y‖ ≤
        C * Real.exp (-β * t) * ‖z - y‖ := by
  set φ := negativeGradientFlow f hf
  obtain ⟨r, hr, C, hC, β, hβ, hcontr⟩ :=
    h.exists_norm_sub_le_of_isIntegralCurveOn_mapsTo_closedBall
  -- Near `x`, the trajectories of points of the stable set stay within `r` of `x`, and the
  -- trajectory of `y` enters this neighbourhood at some time `T ≥ 0`.
  have hconf := h.eventually_forall_dist_le_of_mem_stableSet
    (isNegativeGradient_negativeGradientFlow f hf) hd hr
  obtain ⟨T, hTnhds, hT⟩ := (((Flow.mem_stableSet.1 hy).eventually hconf.eventually_nhds).and
    (eventually_ge_atTop 0)).exists
  have hLip := lipschitzWith_negativeGradientFlow f hf
  have hLip_le {t : ℝ} (ht : 0 ≤ t) (a b : E) : ‖φ t a - φ t b‖ ≤ Real.exp (K * t) * ‖a - b‖ := by
    simpa only [dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le, abs_of_nonneg ht] using
      (hLip t).dist_le_mul a b
  refine ⟨(C + 1) * Real.exp ((K + β) * T), β, hβ, ?_⟩
  filter_upwards [((hLip T).continuous.tendsto y).eventually hTnhds] with z hz hzs t ht
  rcases le_total T t with hTt | htT
  · -- After time `T`, both trajectories are confined near `x`, where they approach each other.
    have hconf' {w : E} (hw : ∀ s, 0 ≤ s → dist (φ s w) x ≤ r) :
        MapsTo (fun s ↦ φ s (x + (w - x)) - x) (Ici 0) (closedBall 0 r) := fun s hs ↦ by
      rw [add_sub_cancel, mem_closedBall_zero_iff, ← dist_eq_norm]
      exact hw s hs
    have hstep := hcontr _ _
      ((isIntegralCurve_centeredNegativeGradientFlow hf x (φ T z - x)).isIntegralCurveOn _)
      (hconf' (hz (Flow.isInvariant_stableSet _ x T hzs)))
      ((isIntegralCurve_centeredNegativeGradientFlow hf x (φ T y - x)).isIntegralCurveOn _)
      (hconf' (hTnhds.self_of_nhds (Flow.isInvariant_stableSet _ x T hy))) (t - T)
      (sub_nonneg.2 hTt)
    simp only [add_sub_cancel, sub_sub_sub_cancel_right, Flow.map_zero_apply] at hstep
    rw [← Flow.map_add, ← Flow.map_add, sub_add_cancel] at hstep
    calc ‖φ t z - φ t y‖ ≤ C * Real.exp (-β * (t - T)) * (Real.exp (K * T) * ‖z - y‖) :=
          hstep.trans (by gcongr; exact hLip_le hT _ _)
      _ = C * Real.exp ((K + β) * T) * Real.exp (-β * t) * ‖z - y‖ := by
          rw [show (K + β) * T = K * T + β * T by ring, Real.exp_add,
            show -β * (t - T) = β * T + -β * t by ring, Real.exp_add]
          ring
      _ ≤ (C + 1) * Real.exp ((K + β) * T) * Real.exp (-β * t) * ‖z - y‖ := by gcongr; linarith
  · -- Up to time `T`, the time-`t` map is Lipschitz.
    calc ‖φ t z - φ t y‖ ≤ Real.exp (K * t) * ‖z - y‖ := hLip_le ht _ _
      _ ≤ 1 * Real.exp ((K + β) * T) * Real.exp (-β * t) * ‖z - y‖ := by
          rw [one_mul, ← Real.exp_add]
          gcongr
          nlinarith [K.coe_nonneg]
      _ ≤ (C + 1) * Real.exp ((K + β) * T) * Real.exp (-β * t) * ‖z - y‖ := by gcongr; linarith

/-- **The linearized flow makes tangent vectors of the stable set decay.** Let `x` be a
nondegenerate critical point of a `C²` function `f` with globally Lipschitz gradient, and `y` a
point of its stable set. There are a constant `C` and a rate `β > 0` such that for every vector
`v` tangent to the stable set at `y`, `‖Dφ_t(y) v‖ ≤ C * exp (-β t) * ‖v‖` at all times
`t ≥ 0`. -/
theorem exists_norm_fderiv_negativeGradientFlow_apply_le
    (h : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) x) :
    ∃ C : ℝ, ∃ β > (0 : ℝ),
      ∀ v ∈ tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) x) y, ∀ t, 0 ≤ t →
        ‖fderiv ℝ (negativeGradientFlow f hf t) y v‖ ≤ C * Real.exp (-β * t) * ‖v‖ := by
  obtain ⟨C, β, hβ, hev⟩ := h.exists_norm_negativeGradientFlow_sub_le_of_mem_stableSet hf
    (hfs.differentiable (by norm_num)) hy
  refine ⟨C, β, hβ, fun v hv t ht ↦ ?_⟩
  refine (differentiable_negativeGradientFlow_apply f hf hfs t y).hasFDerivAt.hasFDerivWithinAt
    |>.norm_apply_le_of_mem_tangentConeAt ?_ hv
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin] with z hz hzs
  exact hz hzs t ht

/-- **The tangent space of a stable set is the space of decaying linearized solutions.** Let `q`
be a nondegenerate critical point of a `C²` function `f` with globally Lipschitz gradient, and `y`
a point of its stable set. Then the tangent space of the stable set of `q` at `y` is the space of
initial values of the solutions of `v' + Hess f(φ_t y) v = 0` that are square integrable on
`(0, ∞)`. Every tangent vector `v` is the initial value of `t ↦ Dφ_t(y) v`, which decays
exponentially, and both spaces have dimension `dim E - ind(q)`. -/
theorem span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn
    (hq : IsNondegenerateCriticalPoint f q) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) q) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow f hf) q) y) =
      squareIntegrableSolutionsOn (fun t ↦ hessianOperator f (negativeGradientFlow f hf t y))
        (Ioi 0) := by
  set φ := negativeGradientFlow f hf
  have hγ : IsIntegralCurve (fun t ↦ φ t y) (fun _ x ↦ -∇ f x) :=
    (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 fun v hv ↦ ?_) ?_
  · obtain ⟨C, β, hβ, hdecay⟩ :=
      hq.exists_norm_fderiv_negativeGradientFlow_apply_le hfs hf hy
    -- The solution with initial value `v` is `t ↦ Dφ_t(y) v`, by the variational equation.
    have hderiv (τ : ℝ) : HasDerivAt (fun t ↦ fderiv ℝ (φ t) y v)
        (-hessianOperator f (φ τ y) (fderiv ℝ (φ τ) y v)) τ := by
      simpa [fderiv_gradient] using
        (hasDerivAt_fderiv_negativeGradientFlow f hf hfs y τ).clm_apply (hasDerivAt_const τ v)
    have hcont : Continuous fun t ↦ fderiv ℝ (φ t) y v :=
      continuous_iff_continuousAt.2 fun τ ↦ (hderiv τ).continuousAt
    refine mem_squareIntegrableSolutionsOn.2
      ⟨fun t ↦ fderiv ℝ (φ t) y v, by simp [φ, Flow.map_zero], hderiv, ?_⟩
    -- It decays exponentially, hence is square integrable on `(0, ∞)`.
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    refine ((exp_neg_integrableOn_Ioi 0 (by positivity : 0 < 2 * β)).const_mul
      ((C * ‖v‖) ^ 2)).mono' (hcont.norm.pow 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖fderiv ℝ (φ t) y v‖ ^ 2 ≤ (C * Real.exp (-β * t) * ‖v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdecay v hv t ht.le) 2
      _ = (C * ‖v‖) ^ 2 * Real.exp (-(2 * β) * t) := by
          rw [show -(2 * β) * t = -β * t + -β * t by ring, Real.exp_add]
          ring
  · -- Both spaces have dimension `dim E - ind(q)`.
    exact Nat.add_right_cancel
      ((hq.finrank_span_tangentConeAt_stableSet_add_morseIndex hfs hf hy).trans
        (hγ.finrank_squareIntegrableSolutionsOn_Ioi_hessianOperator_add_morseIndex hfs hq
          (Flow.mem_stableSet.1 hy)).symm)

/-- **The tangent space of an unstable set is the space of linearized solutions decaying in
backward time.** Let `p` be a nondegenerate critical point of a `C²` function `f` with globally
Lipschitz gradient, and `y` a point of its unstable set. Then the tangent space of the unstable set
of `p` at `y` is the space of initial values of the solutions of `v' + Hess f(φ_t y) v = 0` that
are square integrable on `(-∞, 0)`. This is the stable case for `-f`, whose flow is that of `f`
run backwards. -/
theorem span_tangentConeAt_unstableSet_eq_squareIntegrableSolutionsOn
    (hp : IsNondegenerateCriticalPoint f p) (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) p) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow f hf) p) y) =
      squareIntegrableSolutionsOn (fun t ↦ hessianOperator f (negativeGradientFlow f hf t y))
        (Iio 0) := by
  have hgrad : ∇ (-f) = -∇ f := funext fun _ ↦ gradient_neg
  have hf' : LipschitzWith K (∇ (-f)) := hgrad ▸ hf.neg
  have hflow := negativeGradientFlow_neg f hf hf'
  have hset : Flow.unstableSet (negativeGradientFlow f hf) p =
      Flow.stableSet (negativeGradientFlow (-f) hf') p := by
    rw [hflow, Flow.stableSet_reverse]
  rw [hset] at hy ⊢
  rw [hp.neg.span_tangentConeAt_stableSet_eq_squareIntegrableSolutionsOn hfs.neg hf' hy,
    squareIntegrableSolutionsOn_Iio_eq_Ioi]
  simp only [hflow, Flow.reverse_apply, hessianOperator_neg]

/-- **The linearized operator is onto exactly when the unstable and stable sets are
transverse.** Let `p` and `q` be nondegenerate critical points of a `C²` function `f` with
globally Lipschitz gradient, and `y` a point of `W^u(p) ∩ W^s(q)`. Then the linearized operator
`ξ ↦ ξ' + Hess f(φ_t y) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` along the trajectory through `y` is
surjective if and only if the tangent spaces of `W^u(p)` and `W^s(q)` at `y` span `E`. -/
theorem surjective_trajectoryOperator_hessianOperator_iff_span_tangentConeAt_sup_eq_top
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
  exact ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y)
    |>.surjective_trajectoryOperator_hessianOperator_iff_sup_eq_top hfs hp hq
      (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys) hAL

end IsNondegenerateCriticalPoint

/-- **Morse–Smale functions are those whose linearized operators are onto.** A `C²` function with
globally Lipschitz gradient on a finite-dimensional real inner product space is Morse–Smale if and
only if, along every trajectory of its negative gradient flow joining two nondegenerate critical
points, the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is
surjective. -/
theorem isMorseSmale_iff_forall_surjective_trajectoryOperator (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) :
    IsMorseSmale f hf ↔ ∀ ⦃p q y : E⦄, IsNondegenerateCriticalPoint f p →
      IsNondegenerateCriticalPoint f q →
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p →
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q →
      ∀ AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
        AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          (fun s ↦ hessianOperator f (negativeGradientFlow f hf s y)) →
        Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) AL) := by
  refine ⟨fun h p q y hp hq hyu hys AL hAL ↦
    (hp.surjective_trajectoryOperator_hessianOperator_iff_span_tangentConeAt_sup_eq_top hq hfs hf
      hyu hys hAL).2 (h.transverse_at hp hq ⟨hyu, hys⟩),
    fun h ↦ .of_forall fun p q y hp hq hy ↦ ?_⟩
  obtain ⟨hyu, hys⟩ := hy
  -- The Hessian along the trajectory has an `L∞` class, to which the hypothesis applies.
  have hmem := hfs.memLp_top_hessianOperator_comp
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y).continuous
    (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys)
    (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
  exact (hp.surjective_trajectoryOperator_hessianOperator_iff_span_tangentConeAt_sup_eq_top hq hfs
    hf hyu hys hmem.coeFn_toLp).1 (h hp hq hyu hys _ hmem.coeFn_toLp)

end TauCeti
