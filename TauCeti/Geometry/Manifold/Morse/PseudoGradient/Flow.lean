/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Dynamics.Flow.Stable
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The flow of an adapted pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold and `X` a pseudo-gradient field
adapted to `f`. The flow of `X` decreases `f` along every non-constant orbit, its rest points are
the critical points of `f`, and every orbit converges to a critical point both forward and backward
in time. Consequently the manifold is the disjoint union of the stable sets `W^s(x)` of the
critical points `x`, and also of their unstable sets `W^u(x)`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.flow`: the flow of an adapted pseudo-gradient on a compact
  manifold.
* `TauCeti.IsAdaptedPseudoGradient.contMDiff_flow_uncurry` and
  `TauCeti.IsAdaptedPseudoGradient.flowDiffeomorph`: the flow is smooth in time and space, and its
  time-`t` map is a diffeomorphism.
* `TauCeti.IsAdaptedPseudoGradient.neg_flow`: the flow of `-X` is the reversed flow, so the unstable
  sets of `X` are the stable sets of `-X` and conversely.
* `TauCeti.IsAdaptedPseudoGradient.hasDerivAt_comp_flow`: the derivative of `f` along an orbit is
  `df(X)`.
* `TauCeti.IsAdaptedPseudoGradient.flow_apply_of_mfderiv_eq_zero`: critical points are rest points.
* `TauCeti.IsAdaptedPseudoGradient.mfderiv_flow_ne_zero`: so the orbit of a regular point consists
  of regular points.
* `TauCeti.IsAdaptedPseudoGradient.flow_apply_eq_of_isMIntegralCurve`: every integral curve is an
  orbit, and `TauCeti.IsAdaptedPseudoGradient.eqOn_flow_of_isMIntegralCurveOn`: so is every
  integral curve on an open interval, on that interval;
  `TauCeti.IsAdaptedPseudoGradient.eqOn_flow_of_isMIntegralCurveOn_Iio` and
  `TauCeti.IsAdaptedPseudoGradient.eqOn_flow_of_isMIntegralCurveOn_Ioi` are the versions for
  open half-lines.
* `TauCeti.IsAdaptedPseudoGradient.isMIntegralCurve_flow_mul` and
  `TauCeti.IsAdaptedPseudoGradient.flow_mul_eq_of_isMIntegralCurve`: the integral curves of a
  constant multiple `a • X` are the orbits of `X` run at speed `a`.
* `TauCeti.IsAdaptedPseudoGradient.mem_unstableSet_inter_stableSet_of_isMIntegralCurve`: an
  integral curve from `p` to `q` is the orbit of a point of `W^u(p) ∩ W^s(q)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atTop` and
  `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atBot`: every orbit converges to a critical point
  forward, respectively backward, in time.
* `TauCeti.IsAdaptedPseudoGradient.exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt`: a point
  of `W^u(p)` whose orbit passes below a level `c ≤ f p` lies on a trajectory from `p` to a
  critical point below `c`.
* `TauCeti.IsAdaptedPseudoGradient.mem_stableSet_of_forall_mem` and
  `TauCeti.IsAdaptedPseudoGradient.mem_unstableSet_of_forall_mem`: an orbit trapped in a closed set
  whose only critical point is `x` converges to `x`.
* `TauCeti.IsAdaptedPseudoGradient.eq_of_mem_unstableSet_inter_stableSet`: an orbit converging to
  the same point in both directions of time is that point.
* `TauCeti.IsAdaptedPseudoGradient.iUnion_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.iUnion_unstableSet`: the stable sets of the critical points
  cover the manifold, and so do their unstable sets. Together with
  `Flow.disjoint_stableSet` and `Flow.disjoint_unstableSet`, these are the
  partitions `M = ⊔ₓ W^s(x) = ⊔ₓ W^u(x)` over the critical points.
* `TauCeti.IsAdaptedPseudoGradient.exists_mem_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.exists_mem_unstableSet`: every point lies on the stable set of a
  critical point, and on the unstable set of one.
* `TauCeti.IsAdaptedPseudoGradient.stableSet_eq_singleton_of_lt` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_lt`: the stable set of a strict
  maximum, and the unstable set of a strict minimum, is a point.
* `TauCeti.IsAdaptedPseudoGradient.stableSet_eq_compl_of_critical_eq_or_eq` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_compl_of_critical_eq_or_eq`: with at most two
  critical points, one of which has a trivial stable (respectively unstable) set, the stable
  (respectively unstable) set of the other is the rest of the manifold.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6 and Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient on a compact boundaryless manifold is complete. -/
theorem isCompleteVectorField (hX : IsAdaptedPseudoGradient f X) :
    IsCompleteVectorField X :=
  isCompleteVectorField_of_compactSpace (hX.contMDiff.of_le (by simp))

/-- The flow of an adapted pseudo-gradient on a compact boundaryless manifold. -/
noncomputable def flow (hX : IsAdaptedPseudoGradient f X) : Flow ℝ M :=
  globalFlow X (hX.contMDiff.of_le (by simp)) hX.isCompleteVectorField

variable (hX : IsAdaptedPseudoGradient f X)

/-- The flow at time `t` is the maximal integral curve of the pseudo-gradient at time `t`. -/
theorem flow_apply (t : ℝ) (y : M) : hX.flow t y = maximalIntegralCurve X y t := by
  rw [flow, globalFlow_apply]

/-- The orbits of the flow are integral curves of the pseudo-gradient. -/
theorem isMIntegralCurve_flow (y : M) : IsMIntegralCurve (fun t ↦ hX.flow t y) X :=
  isMIntegralCurve_globalFlow _ hX.isCompleteVectorField y

/-- The flow of an adapted pseudo-gradient is smooth in time and space. -/
theorem contMDiff_flow_uncurry :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ fun p : ℝ × M ↦ hX.flow p.1 p.2 :=
  contMDiff_globalFlow_uncurry hX.isCompleteVectorField (n := ⊤) le_top
    hX.contMDiff

/-- For a fixed time `t`, the time-`t` map of the flow is smooth. -/
theorem contMDiff_flow_apply (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hX.flow t) :=
  contMDiff_globalFlow_apply hX.isCompleteVectorField (n := ⊤) le_top
    hX.contMDiff t

/-- The time-`t` map of the flow of an adapted pseudo-gradient, as a diffeomorphism. Its inverse
is the time-`(-t)` map. -/
noncomputable def flowDiffeomorph (t : ℝ) :
    M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  globalFlowDiffeomorph hX.isCompleteVectorField (n := ⊤) le_top hX.contMDiff t

/-- The diffeomorphism `flowDiffeomorph t` is the time-`t` map of the flow. -/
@[simp]
theorem flowDiffeomorph_apply (t : ℝ) (y : M) : hX.flowDiffeomorph t y = hX.flow t y := by
  rw [flowDiffeomorph, globalFlowDiffeomorph_apply, hX.flow_apply, globalFlow_apply]

/-- The inverse of `flowDiffeomorph t` is the time-`(-t)` map of the flow. -/
@[simp]
theorem flowDiffeomorph_symm_apply (t : ℝ) (y : M) :
    (hX.flowDiffeomorph t).symm y = hX.flow (-t) y := by
  rw [flowDiffeomorph, globalFlowDiffeomorph_symm_apply, hX.flow_apply, globalFlow_apply]

/-- **The flow preserves the pseudo-gradient.** The derivative of the time-`t` map of the flow
carries `X y` to `X` at the image of `y`. -/
theorem mfderiv_flow_apply_self (t : ℝ) (y : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y (X y) = X (hX.flow t y) :=
  mfderiv_globalFlow_apply_self _ hX.isCompleteVectorField t y

/-- The derivative of `f` along an orbit of the flow is `df(X)`. -/
theorem hasDerivAt_comp_flow (y : M) (t : ℝ) :
    HasDerivAt (fun s ↦ f (hX.flow s y)) (mvfderiv 𝓘(ℝ, E) f (hX.flow t y) (X (hX.flow t y))) t :=
  Manifold.hasDerivAt_comp_curve (γ := fun s ↦ hX.flow s y) (hX.mdifferentiable _)
    (hX.isMIntegralCurve_flow y t)

/-- `f` is antitone along every orbit of the flow. -/
theorem antitone_flow (y : M) : Antitone fun t ↦ f (hX.flow t y) :=
  hX.antitone_comp (hX.isMIntegralCurve_flow y)

/-- Critical points of `f` are rest points of the flow. -/
theorem flow_apply_of_mfderiv_eq_zero {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (t : ℝ) :
    hX.flow t x = x :=
  globalFlow_eq_of_isMIntegralCurve _ hX.isCompleteVectorField
    (isMIntegralCurve_const (hX.eq_zero_of_mfderiv_eq_zero hx)) t

/-- The orbit of a regular point consists of regular points: critical points are rest points. -/
theorem mfderiv_flow_ne_zero {y : M} (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0) (t : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (hX.flow t y) ≠ 0 := fun h ↦ hy <| by
  have := hX.flow_apply_of_mfderiv_eq_zero h (-t)
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
  rwa [this]

/-- **Integral curves are orbits.** Every integral curve of an adapted pseudo-gradient on a compact
boundaryless manifold is the orbit of its value at time `0`. -/
theorem flow_apply_eq_of_isMIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    hX.flow t (γ 0) = γ t :=
  globalFlow_eq_of_isMIntegralCurve _ hX.isCompleteVectorField hγ t

/-- **Integral curves on an open interval are orbits.** An integral curve of an adapted
pseudo-gradient on an open interval is, on that interval, the orbit of its value at any time
`t₀` of the interval, shifted by `t₀`. -/
theorem eqOn_flow_of_isMIntegralCurveOn {γ : ℝ → M} {a b t₀ : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b) :
    EqOn γ (fun t ↦ hX.flow (t - t₀) (γ t₀)) (Ioo a b) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ (hX.contMDiff.of_le (by simp)) hγ
    ((((hX.isMIntegralCurve_flow (γ t₀)).comp_add (-t₀)).isMIntegralCurveOn _).congr fun t _ ↦ by
      simp [sub_eq_add_neg]) (by simp)

/-- **Integral curves on a left half-line are orbits up to any earlier time.** An integral curve of
an adapted pseudo-gradient on `(-∞, b)` is, up to any time `a < b`, the orbit of its value at `a`,
shifted by `a`. -/
theorem eqOn_flow_of_isMIntegralCurveOn_Iio {γ : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Iio b)) (hab : a < b) :
    EqOn γ (fun t ↦ hX.flow (t - a) (γ a)) (Iic a) := fun t (ht : t ≤ a) ↦
  hX.eqOn_flow_of_isMIntegralCurveOn (hγ.mono Ioo_subset_Iio_self) (a := t - 1)
    ⟨(sub_one_lt t).trans_le ht, hab⟩ ⟨sub_one_lt t, ht.trans_lt hab⟩

/-- **Integral curves on a right half-line are orbits from any later time on.** An integral curve
of an adapted pseudo-gradient on `(a, ∞)` is, from any time `b > a` on, the orbit of its value at
`b`, shifted by `b`. -/
theorem eqOn_flow_of_isMIntegralCurveOn_Ioi {γ : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioi a)) (hab : a < b) :
    EqOn γ (fun t ↦ hX.flow (t - b) (γ b)) (Ici b) := fun t (ht : b ≤ t) ↦
  hX.eqOn_flow_of_isMIntegralCurveOn (hγ.mono Ioo_subset_Ioi_self) (b := t + 1)
    ⟨hab, ht.trans_lt (lt_add_one t)⟩ ⟨hab.trans_le ht, lt_add_one t⟩

/-- **Rescaling time rescales the field.** For every `a : ℝ`, the orbit `t ↦ φ_{a t}(y)` run at
speed `a` is an integral curve of `a • X`. -/
theorem isMIntegralCurve_flow_mul (a : ℝ) (y : M) :
    IsMIntegralCurve (fun t ↦ hX.flow (a * t) y) (a • X) := by
  simpa only [Function.comp_def, mul_comm] using (hX.isMIntegralCurve_flow y).comp_mul a

/-- **Integral curves of a rescaled field are orbits run at the rescaled speed.** Every integral
curve `γ` of `a • X` satisfies `γ t = φ_{a t}(γ 0)`, where `φ` is the flow of `X`. For `a = 0`
both sides are constant. -/
theorem flow_mul_eq_of_isMIntegralCurve {a : ℝ} {γ : ℝ → M} (hγ : IsMIntegralCurve γ (a • X))
    (t : ℝ) : hX.flow (a * t) (γ 0) = γ t := by
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, (a • X) x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    (ContMDiff.const_smul_section (a := a) hX.contMDiff).of_le (by simp)
  have h := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    (hX.isMIntegralCurve_flow_mul a (γ 0)) hγ (by simp [hX.flow_apply])
  exact congrFun h t

/-- An integral curve of an adapted pseudo-gradient from `p` to `q` is the orbit of a point of
`W^u(p) ∩ W^s(q)`. -/
theorem mem_unstableSet_inter_stableSet_of_isMIntegralCurve {γ : ℝ → M} {p q : M}
    (hγ : IsMIntegralCurve γ X) (hp : Tendsto γ atBot (𝓝 p)) (hq : Tendsto γ atTop (𝓝 q)) :
    γ 0 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ γ = fun s ↦ hX.flow s (γ 0) := by
  have hflow : γ = fun s ↦ hX.flow s (γ 0) := funext fun s ↦
    (hX.flow_apply_eq_of_isMIntegralCurve hγ s).symm
  rw [hflow] at hp hq
  exact ⟨⟨Flow.mem_unstableSet.2 hp, Flow.mem_stableSet.2 hq⟩, hflow⟩

/-- A point along whose orbit `f` is constant is a critical point of `f`. -/
theorem mfderiv_eq_zero_of_forall_eq {z : M}
    (hz : ∀ t, f (hX.flow t z) = f z) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 := by
  by_contra hcrit
  have hd := hX.hasDerivAt_comp_flow z 0
  have horbit : (fun s ↦ f (hX.flow s z)) = fun _ ↦ f z := funext hz
  rw [horbit, Flow.map_zero_apply] at hd
  exact (hX.mvfderiv_apply_lt_zero z hcrit).ne (hd.unique (hasDerivAt_const _ _))

/-- A point with a nonempty stable set is a critical point of `f`: it is fixed by the flow. -/
theorem mfderiv_eq_zero_of_mem_stableSet {a y : M} (hy : y ∈ hX.flow.stableSet a) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 := by
  exact hX.mfderiv_eq_zero_of_forall_eq fun t ↦ by rw [Flow.fixed_of_mem_stableSet hy t]

/-- A point with a nonempty unstable set is a critical point of `f`: it is fixed by the flow. -/
theorem mfderiv_eq_zero_of_mem_unstableSet {a y : M} (hy : y ∈ hX.flow.unstableSet a) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 := by
  exact hX.mfderiv_eq_zero_of_forall_eq fun t ↦ by rw [Flow.fixed_of_mem_unstableSet hy t]

/-- **Every orbit converges forward in time to a critical point.** -/
theorem exists_tendsto_atTop (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atTop (𝓝 x) :=
  Flow.exists_tendsto_atTop_of_antitone hX.flow hf.contMDiff.continuous hX.antitone_flow
    hf.finite_setOf_mfderiv_eq_zero (fun _ hz ↦ hX.mfderiv_eq_zero_of_forall_eq hz) y

/-- **Every orbit converges backward in time to a critical point.** -/
theorem exists_tendsto_atBot (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atBot (𝓝 x) := by
  obtain ⟨x, hx, htend⟩ := Flow.exists_tendsto_atTop_of_antitone hX.flow.reverse
    hf.contMDiff.continuous.neg
    (fun y ↦ fun s t hst ↦ by
      simp only [Flow.reverse_apply, Pi.neg_apply]
      exact neg_le_neg (hX.antitone_flow y (neg_le_neg hst)))
    hf.finite_setOf_mfderiv_eq_zero
    (fun z hz ↦ hX.mfderiv_eq_zero_of_forall_eq fun t ↦ by
      have := hz (-t)
      simp only [Flow.reverse_apply, neg_neg, Pi.neg_apply] at this
      exact neg_inj.1 this) y
  refine ⟨x, hx, ?_⟩
  have := htend.comp tendsto_neg_atBot_atTop
  simpa [comp_def, Flow.reverse_apply] using this

/-- A point of `W^u(p)` whose orbit passes below a level `c ≤ f p` lies on a trajectory from `p`
to a critical point `b ≠ p` below `c`. -/
theorem exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt (hf : IsMorse 𝓘(ℝ, E) f)
    {p w : M} (hw : w ∈ hX.flow.unstableSet p) {t c : ℝ} (ht : f (hX.flow t w) < c)
    (hcp : c ≤ f p) :
    ∃ b, p ≠ b ∧ w ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧ f b < c := by
  obtain ⟨b, -, hb⟩ := hX.exists_tendsto_atTop hf w
  have hb : w ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hb
  have hfb : f b ≤ f (hX.flow t w) :=
    Flow.le_of_mem_stableSet_of_antitone ((Flow.apply_mem_stableSet_iff _ t).2 hb)
      hX.mdifferentiable.continuous.continuousAt (hX.antitone_flow _)
  exact ⟨b, by rintro rfl; linarith, ⟨hw, hb⟩, hfb.trans_lt ht⟩

/-- **An orbit trapped near a critical point converges to it.** If the forward orbit of `w` stays
in a closed set `K` whose only critical point of the Morse function `f` is `x`, then the orbit
converges to `x`. -/
theorem mem_stableSet_of_forall_mem (hf : IsMorse 𝓘(ℝ, E) f) {x : M} {K : Set M} (hK : IsClosed K)
    (hKx : ∀ z ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x) {w : M}
    (hw : ∀ t, 0 ≤ t → hX.flow t w ∈ K) : w ∈ hX.flow.stableSet x := by
  obtain ⟨z, hz, hlim⟩ := hX.exists_tendsto_atTop hf w
  rw [hKx z (hK.mem_of_tendsto hlim (eventually_atTop.2 ⟨0, hw⟩)) hz] at hlim
  exact Flow.mem_stableSet.2 hlim

/-- **An orbit trapped near a critical point in backward time converges to it.** If the backward
orbit of `w` stays in a closed set `K` whose only critical point of the Morse function `f` is `x`,
then the orbit converges to `x` in backward time. -/
theorem mem_unstableSet_of_forall_mem (hf : IsMorse 𝓘(ℝ, E) f) {x : M} {K : Set M} (hK : IsClosed K)
    (hKx : ∀ z ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → z = x) {w : M}
    (hw : ∀ t, t ≤ 0 → hX.flow t w ∈ K) : w ∈ hX.flow.unstableSet x := by
  obtain ⟨z, hz, hlim⟩ := hX.exists_tendsto_atBot hf w
  rw [hKx z (hK.mem_of_tendsto hlim (eventually_atBot.2 ⟨0, hw⟩)) hz] at hlim
  exact Flow.mem_unstableSet.2 hlim

/-- **A trajectory from a critical point back to itself is constant.** If the orbit of `y`
converges to the same point `x` in backward and in forward time, then `y = x`: the function `f`,
which decreases along the orbit, is constant on it, so `y` is a rest point. -/
theorem eq_of_mem_unstableSet_inter_stableSet {x y : M}
    (hy : y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x) : y = x := by
  have hf := hX.mdifferentiable
  have hval : ∀ z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x, f z = f x := fun z hz ↦
    le_antisymm (Flow.le_of_mem_unstableSet_of_antitone hz.1 hf.continuous.continuousAt
      (hX.antitone_flow z))
      (Flow.le_of_mem_stableSet_of_antitone hz.2 hf.continuous.continuousAt (hX.antitone_flow z))
  have hcrit := hX.mfderiv_eq_zero_of_forall_eq fun t ↦ by
    rw [hval _ ⟨(Flow.apply_mem_unstableSet_iff _ t).2 hy.1,
      (Flow.apply_mem_stableSet_iff _ t).2 hy.2⟩, hval y hy]
  have hlim := Flow.mem_stableSet.1 hy.2
  simp only [hX.flow_apply_of_mfderiv_eq_zero hcrit] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **A critical point is a constant trajectory from itself to itself**: it lies in its own unstable
and stable sets, since it is a rest point of the flow. -/
theorem mem_unstableSet_inter_stableSet_self {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    x ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x :=
  ⟨Flow.self_mem_unstableSet_iff.2 (hX.flow_apply_of_mfderiv_eq_zero hx),
    Flow.self_mem_stableSet_iff.2 (hX.flow_apply_of_mfderiv_eq_zero hx)⟩

/-- **A critical point lies only on its own unstable manifold.** If `x` is a critical point of `f`
and `x ∈ W^u(p)`, then `x = p`: the flow fixes `x`, so `x ∈ W^u(x)`, and unstable sets of distinct
points are disjoint. -/
theorem eq_of_mem_unstableSet_of_mfderiv_eq_zero {x p : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (h : x ∈ hX.flow.unstableSet p) : x = p := by
  by_contra hxp
  exact disjoint_left.1 (Flow.disjoint_unstableSet hxp)
    (hX.mem_unstableSet_inter_stableSet_self hx).1 h

/-- A critical point lies in its own unstable set. -/
theorem mem_unstableSet_self {x : M} (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) :
    x ∈ hX.flow.unstableSet x :=
  (hX.mem_unstableSet_inter_stableSet_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)).1

/-- A critical point lies in its own stable set. -/
theorem mem_stableSet_self {x : M} (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) :
    x ∈ hX.flow.stableSet x :=
  (hX.mem_unstableSet_inter_stableSet_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)).2

/-- **The stable sets of the critical points cover the manifold.** -/
theorem iUnion_stableSet (hf : IsMorse 𝓘(ℝ, E) f) :
    ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.stableSet x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx, htend⟩ := hX.exists_tendsto_atTop hf y
  exact mem_iUnion₂.2 ⟨x, hx, Flow.mem_stableSet.2 htend⟩

/-- **The unstable sets of the critical points cover the manifold.** -/
theorem iUnion_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) :
    ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.unstableSet x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx, htend⟩ := hX.exists_tendsto_atBot hf y
  exact mem_iUnion₂.2 ⟨x, hx, Flow.mem_unstableSet.2 htend⟩

/-- **Every point lies on the stable set of a critical point.** -/
theorem exists_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ c, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 ∧ y ∈ hX.flow.stableSet c := by
  obtain ⟨c, hc, htend⟩ := hX.exists_tendsto_atTop hf y
  exact ⟨c, hc, Flow.mem_stableSet.2 htend⟩

/-- **Every point lies on the unstable set of a critical point.** -/
theorem exists_mem_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ c, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 ∧ y ∈ hX.flow.unstableSet c := by
  obtain ⟨c, hc, htend⟩ := hX.exists_tendsto_atBot hf y
  exact ⟨c, hc, Flow.mem_unstableSet.2 htend⟩

/-- **The stable set of a strict maximum is a point.** If `f` has a strict global maximum at `a`,
then no other orbit of the flow converges to `a` in forward time. -/
theorem stableSet_eq_singleton_of_lt {a : M}
    (hmax : ∀ y, y ≠ a → f y < f a) : hX.flow.stableSet a = {a} :=
  Flow.stableSet_eq_singleton_of_antitone hX.mdifferentiable.continuous.continuousAt
    hX.antitone_flow hmax

/-- **The unstable set of a strict minimum is a point.** If `f` has a strict global minimum at `a`,
then no other orbit of the flow converges to `a` in backward time. -/
theorem unstableSet_eq_singleton_of_lt {a : M}
    (hmin : ∀ y, y ≠ a → f a < f y) : hX.flow.unstableSet a = {a} :=
  Flow.unstableSet_eq_singleton_of_antitone hX.mdifferentiable.continuous.continuousAt
    hX.antitone_flow hmin

/-- **Two critical points.** If every critical point of a Morse function is one of two distinct
points `a` and `b`, and the stable set of `a` is `{a}`, then the stable set of `b` is everything
else. -/
theorem stableSet_eq_compl_of_critical_eq_or_eq (hf : IsMorse 𝓘(ℝ, E) f) {a b : M}
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = a ∨ y = b) (hab : a ≠ b)
    (ha : hX.flow.stableSet a = {a}) : hX.flow.stableSet b = {a}ᶜ := by
  ext p
  refine ⟨fun hp hpa ↦ ?_, fun hpa ↦ ?_⟩
  · rw [mem_singleton_iff] at hpa
    subst hpa
    exact disjoint_left.1 (Flow.disjoint_stableSet hab) (ha ▸ rfl) hp
  · obtain ⟨c, hc, hpc⟩ := hX.exists_mem_stableSet hf p
    rcases hcrit c hc with rfl | rfl
    · exact absurd (ha ▸ hpc) hpa
    · exact hpc

/-- **Two critical points.** If every critical point of a Morse function is one of two distinct
points `a` and `b`, and the unstable set of `b` is `{b}`, then the unstable set of `a` is everything
else. -/
theorem unstableSet_eq_compl_of_critical_eq_or_eq (hf : IsMorse 𝓘(ℝ, E) f) {a b : M}
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = a ∨ y = b) (hab : a ≠ b)
    (hb : hX.flow.unstableSet b = {b}) : hX.flow.unstableSet a = {b}ᶜ := by
  ext p
  refine ⟨fun hp hpb ↦ ?_, fun hpb ↦ ?_⟩
  · rw [mem_singleton_iff] at hpb
    subst hpb
    exact disjoint_left.1 (Flow.disjoint_unstableSet hab) hp (hb ▸ rfl)
  · obtain ⟨c, hc, hpc⟩ := hX.exists_mem_unstableSet hf p
    rcases hcrit c hc with rfl | rfl
    · exact hpc
    · exact absurd (hb ▸ hpc) hpb

/-- The flow of `-X` is the flow of `X` run backwards. -/
theorem neg_flow (hf : IsMorse 𝓘(ℝ, E) f) :
    (hX.neg hf).flow = hX.flow.reverse := by
  ext t y
  have hγ : IsMIntegralCurve ((fun s ↦ hX.flow s y) ∘ (· * (-1 : ℝ))) (-X) := by
    have := (hX.isMIntegralCurve_flow y).comp_mul (-1)
    rwa [neg_one_smul] at this
  have h := globalFlow_eq_of_isMIntegralCurve ((hX.neg hf).contMDiff.of_le (by simp))
    (hX.neg hf).isCompleteVectorField hγ t
  simp only [comp_apply, mul_neg_one, neg_zero, Flow.map_zero_apply] at h
  rw [Flow.reverse_apply, ← h, (hX.neg hf).flow_apply, globalFlow_apply]

/-- The unstable set of a critical point is its stable set for the reversed pseudo-gradient. -/
theorem unstableSet_eq_stableSet_neg (hf : IsMorse 𝓘(ℝ, E) f) (x : M) :
    hX.flow.unstableSet x = (hX.neg hf).flow.stableSet x := by
  rw [hX.neg_flow hf, Flow.stableSet_reverse]

/-- The stable set of a critical point is its unstable set for the reversed pseudo-gradient. -/
theorem stableSet_eq_unstableSet_neg (hf : IsMorse 𝓘(ℝ, E) f) (x : M) :
    hX.flow.stableSet x = (hX.neg hf).flow.unstableSet x := by
  rw [hX.neg_flow hf, Flow.unstableSet_reverse]

end IsAdaptedPseudoGradient

end TauCeti
