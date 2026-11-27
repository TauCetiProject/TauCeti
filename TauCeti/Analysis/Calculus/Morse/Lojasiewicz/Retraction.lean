/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Lojasiewicz
public import TauCeti.Dynamics.Flow.Stable.Retraction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Stable sets of a Łojasiewicz critical set of a negative gradient flow

Let `φ` be a negative gradient flow of a differentiable function `f` on a real Hilbert space
(`Flow.IsNegativeGradient`), and let `C` be a compact set of rest points of `φ` on which `f`
takes the value `b`. Suppose that `f` satisfies a **Łojasiewicz gradient inequality** on a
neighbourhood `U` of `C`:

`‖∇f(y)‖ ≥ c (f(y) - b) ^ θ` for `y ∈ U` with `f(y) ≥ b`, where `c > 0` and `θ < 1`.

Then the stable set `⋃ p ∈ C, stableSet φ p` of `C`, the points whose forward orbits converge to a
point of `C`, behaves as follows.

* On it, the time-`t` maps converge locally uniformly, as `t → ∞`, to the map sending a point to
  the limit of its orbit
  (`Flow.IsNegativeGradient.tendstoLocallyUniformlyOn_limUnder_of_lojasiewicz`), and this limit
  map is continuous (`Flow.IsNegativeGradient.continuousOn_limUnder_of_lojasiewicz`). On compact
  subsets of the stable set the convergence is uniform
  (`Flow.IsNegativeGradient.tendstoUniformlyOn_limUnder_of_lojasiewicz`).
* It strong deformation retracts onto `C`
  (`Flow.IsNegativeGradient.exists_strong_deformation_retraction_of_lojasiewicz`).

The input is the finite-length bound for gradient trajectories
(`IsIntegralCurveOn.norm_sub_le_of_lojasiewicz`): an orbit segment in `U` along which `f ≥ b`
moves by at most `(f(x) - b) ^ (1 - θ) / (c (1 - θ))`
(`Flow.IsNegativeGradient.dist_apply_le_of_lojasiewicz`). The topological consequences of such a
bound hold for every flow with a Lyapunov function and are proved in
`TauCeti.Dynamics.Flow.Stable.Retraction`. The exponent `θ` may exceed `1 / 2`, so degenerate
critical sets are allowed. The Łojasiewicz inequality, which holds near every critical point of
a real analytic function and for the norm square of a moment map, is a hypothesis here.

## References

* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, arXiv:math/0410568, proof of Theorem 1.1.
* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
-/

public section

open Filter Set Topology
open scoped Gradient

namespace Flow.IsNegativeGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {C U : Set E} {b c θ : ℝ}

/-- **Displacement of an orbit segment under a Łojasiewicz inequality.** If `f` satisfies
`‖∇f‖ ≥ c (f - b) ^ θ` on `U`, with `c > 0` and `θ < 1`, then an orbit segment of the negative
gradient flow that lies in `U` and ends with `f ≥ b` moves by at most
`(f(x) - b) ^ (1 - θ) / (c (1 - θ))`. -/
theorem dist_apply_le_of_lojasiewicz (hφ : IsNegativeGradient φ f) (hf : Differentiable ℝ f)
    (hc : 0 < c) (hθ : θ < 1) (hL : ∀ y ∈ U, b ≤ f y → c * (f y - b) ^ θ ≤ ‖∇ f y‖) {x : E}
    {T : ℝ} (hT : 0 ≤ T) (hU : ∀ t ∈ Icc 0 T, φ t x ∈ U) (hb : b ≤ f (φ T x)) :
    dist (φ T x) x ≤ (f x - b) ^ (1 - θ) / (c * (1 - θ)) := by
  have hanti := hφ.orbit_antitone x fun _ ↦ hf _
  have hbt : ∀ t ∈ Icc 0 T, b ≤ f (φ t x) := fun t ht ↦ hb.trans (hanti ht.2)
  have h := (hφ.isIntegralCurve x).isIntegralCurveOn (Icc 0 T) |>.norm_sub_le_of_lojasiewicz hT
    (fun t _ ↦ hf _) hc hθ hbt fun t ht ↦ hL _ (hU t (Ico_subset_Icc_self ht))
      (hbt t (Ico_subset_Icc_self ht))
  rw [Flow.map_zero_apply] at h
  rw [dist_eq_norm]
  refine h.trans ?_
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.2 hb) _)

/-- The length bound `e ↦ e ^ (1 - θ) / (c (1 - θ))` tends to `0` as `e → 0⁺`, the form taken by
the results on flows with a Lyapunov function. -/
private theorem tendsto_lengthBound (hθ : θ < 1) :
    Tendsto (fun e : ℝ ↦ e ^ (1 - θ) / (c * (1 - θ))) (𝓝[≥] 0) (𝓝 0) := by
  simpa using ((tendsto_id.rpow_const_nhds_zero (sub_pos.2 hθ)).div_const (c * (1 - θ))).mono_left
    nhdsWithin_le_nhds

variable (hφ : IsNegativeGradient φ f) (hf : Differentiable ℝ f) (hC : IsCompact C)
  (hCb : ∀ p ∈ C, f p = b) (hU : U ∈ 𝓝ˢ C) (hc : 0 < c) (hθ : θ < 1)
  (hL : ∀ y ∈ U, b ≤ f y → c * (f y - b) ^ θ ≤ ‖∇ f y‖)
include hφ hf hC hCb hU hc hθ hL

omit hC hCb hU in
/-- The displacement bound in the form taken by the results on flows with a Lyapunov function. -/
private theorem forall_dist_apply_le :
    ∀ x T, 0 ≤ T → (∀ t ∈ Icc 0 T, φ t x ∈ U) → b ≤ f (φ T x) →
      dist (φ T x) x ≤ (f x - b) ^ (1 - θ) / (c * (1 - θ)) :=
  fun _ _ hT hxU hb ↦ dist_apply_le_of_lojasiewicz hφ hf hc hθ hL hT hxU hb

/-- **Orbits converge locally uniformly on the stable set of a Łojasiewicz critical set.** If `f`
satisfies a Łojasiewicz inequality near the compact set `C`, on which `f = b`, then on the stable
set of `C` the time maps of the negative gradient flow converge locally uniformly to the limit
map `x ↦ limUnder atTop (φ · x)` as `t → ∞`. -/
theorem tendstoLocallyUniformlyOn_limUnder_of_lojasiewicz :
    TendstoLocallyUniformlyOn (fun t x ↦ φ t x) (fun x ↦ limUnder atTop fun t ↦ φ t x) atTop
      (⋃ p ∈ C, φ.stableSet p) :=
  tendstoLocallyUniformlyOn_limUnder_biUnion_stableSet hf.continuous
    (fun x ↦ hφ.orbit_antitone x fun _ ↦ hf _) hC hCb hU (tendsto_lengthBound hθ)
    (forall_dist_apply_le hφ hf hc hθ hL)

/-- **Orbits converge uniformly on compact subsets of the stable set of a Łojasiewicz critical
set.** Under the hypotheses of
`Flow.IsNegativeGradient.tendstoLocallyUniformlyOn_limUnder_of_lojasiewicz`, the time maps of the
negative gradient flow converge to the limit map uniformly on every compact subset of the stable
set of `C`. -/
theorem tendstoUniformlyOn_limUnder_of_lojasiewicz {K : Set E} (hK : IsCompact K)
    (hKS : K ⊆ ⋃ p ∈ C, φ.stableSet p) :
    TendstoUniformlyOn (fun t x ↦ φ t x) (fun x ↦ limUnder atTop fun t ↦ φ t x) atTop K :=
  tendstoUniformlyOn_limUnder_of_subset_biUnion_stableSet hf.continuous
    (fun x ↦ hφ.orbit_antitone x fun _ ↦ hf _) hC hCb hU (tendsto_lengthBound hθ)
    (forall_dist_apply_le hφ hf hc hθ hL) hK hKS

/-- **The limit map is continuous on the stable set of a Łojasiewicz critical set.** If `f`
satisfies a Łojasiewicz inequality near the compact set `C`, on which `f = b`, then the map
sending a point of the stable set of `C` to the limit of its orbit under the negative gradient
flow is continuous on that stable set. -/
theorem continuousOn_limUnder_of_lojasiewicz :
    ContinuousOn (fun x ↦ limUnder atTop fun t ↦ φ t x) (⋃ p ∈ C, φ.stableSet p) :=
  continuousOn_limUnder_biUnion_stableSet hf.continuous
    (fun x ↦ hφ.orbit_antitone x fun _ ↦ hf _) hC hCb hU (tendsto_lengthBound hθ)
    (forall_dist_apply_le hφ hf hc hθ hL)

/-- **The stable set of a Łojasiewicz critical set deformation retracts onto it.** Let `C` be a
compact set of rest points of the negative gradient flow of `f`, on which `f = b`, and suppose
`‖∇f‖ ≥ c (f - b) ^ θ` with `c > 0` and `θ < 1` near `C` wherever `f ≥ b`. Then the stable set
`⋃ p ∈ C, stableSet φ p` strong deformation retracts onto `C`. -/
theorem exists_strong_deformation_retraction_of_lojasiewicz
    (hfix : ∀ p ∈ C, ∀ t, φ t p = p) :
    ∃ r : C(↥(⋃ p ∈ C, φ.stableSet p), C),
      (∀ p, r (ContinuousMap.inclusion (subset_biUnion_stableSet hfix) p) = p) ∧
      (ContinuousMap.id _).HomotopicRel
        ((ContinuousMap.inclusion (subset_biUnion_stableSet hfix)).comp r) {x | (x : E) ∈ C} :=
  exists_strong_deformation_retraction_biUnion_stableSet hf.continuous
    (fun x ↦ hφ.orbit_antitone x fun _ ↦ hf _) hC hCb hU (tendsto_lengthBound hθ)
    (forall_dist_apply_le hφ hf hc hθ hL) hfix

end Flow.IsNegativeGradient
