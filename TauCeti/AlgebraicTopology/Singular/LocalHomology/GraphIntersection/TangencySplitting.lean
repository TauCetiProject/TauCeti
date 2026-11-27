/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.GraphIntersection
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Prod.Basic
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Normed.Ring.ProdSubProd
import TauCeti.Geometry.Symplectic.Complex.HolomorphicGraph

/-!
# Splitting a tangency into transverse intersections

The line `w = 0` and the curve `w = z ^ k` of `ℂ²` are tangent at the origin, where they meet with
local intersection number `k`. Replacing `z ^ k` near the origin by the polynomial
`∏_{j < k} (z + j ε)`, whose roots `-j ε` are simple for `ε ≠ 0`, splits this tangency into `k`
transverse intersections. To keep the curve unchanged away from the origin the two are joined by a
smooth cutoff: for a smooth bump function `β` on `ℂ`, equal to `1` on the closed ball of radius
`β.rIn` and supported in the open ball of radius `β.rOut` (`ContDiffBump`), the perturbed curve is
the graph of

`g z = z ^ k + β z (∏_{j < k} (z + j ε) - z ^ k)`

(`TauCeti.tangencySplitting`). It is a smooth function of `z` as a real variable, equal to `z ^ k`
outside the ball of radius `β.rOut` and to the polynomial on the ball of radius `β.rIn`; for
`ε = 0` it is `z ^ k` itself. This is the local model of the perturbation by which the
intersections of two branches of a pseudoholomorphic curve in a four-manifold are made transverse
before they are counted: after a normal form, two tangent branches are the line `w = 0` and the
graph of `z ^ k`.

When `ε` is small compared with `β.rIn`, precisely when `(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the
perturbed graph meets the line `w = 0` exactly at the points `(-j ε, 0)` for `j < k`
(`TauCeti.tangencySplitting_eq_zero_iff`). On the annulus where the cutoff varies, the polynomial
differs from `z ^ k` by at most `(‖z‖ + k ‖ε‖) ^ k - ‖z‖ ^ k`
(`TauCeti.norm_prod_add_sub_pow_card_le_of_norm_le`), which is smaller than `‖z‖ ^ k` there, so no
new zero appears. For `ε ≠ 0` each of these intersections is transverse
(`TauCeti.deriv_tangencySplitting_ne_zero`) and has local intersection number `1`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_of_apply_eq_sub_graph_tangencySplitting`),
while the unperturbed tangency has local intersection number `k`
(`TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_graph_pow`, in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.GraphIntersection`). So the local
intersection numbers of the perturbed graph add up to that of the tangency
(`HomologicalOrientation.sum_localIndex_eq_localIndex_of_apply_eq_sub_graph_tangencySplitting`):
the perturbation trades one intersection of multiplicity `k` for `k` positive transverse ones. Local
intersection numbers are computed as in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.GraphIntersection`, as the local index of
`(z, w) ↦ (z, 0) - (w, g w)` for a homological orientation of `ℂ²`.

For small `ε` the perturbed graph is moreover a symplectic curve: the standard symplectic form
`ω ⊕ ω` of `ℂ²` is positive on the image of the oriented frame `(1, I)` under the derivative of
`z ↦ (z, g z)` at every point
(`TauCeti.eventually_forall_prod_stdComplexSymplecticForm_fderiv_tangencySplitting_pos`). For
`ε = 0` this is the graph of the holomorphic function `z ^ k`, which is a symplectic curve
(`DifferentiableAt.prod_stdComplexSymplecticForm_fderiv_pos`). The positivity persists for small `ε`
by continuity in `(ε, z)` on the compact closed ball of radius `β.rOut`, and outside that ball the
perturbation is `z ^ k`.

## Main declarations

* `TauCeti.tangencySplitting`: the perturbation of `z ^ k` by `∏_{j < k} (z + j ε)` with a cutoff.
* `TauCeti.contDiff_tangencySplitting`, `TauCeti.contDiff_uncurry_tangencySplitting`: it is smooth,
  also jointly in `(ε, z)`.
* `TauCeti.tangencySplitting_eq_pow_of_rOut_le`, `TauCeti.tangencySplitting_eq_prod_of_norm_le`,
  `TauCeti.tangencySplitting_zero_right`: it is `z ^ k` outside the cutoff, the polynomial inside,
  and `z ^ k` for `ε = 0`.
* `TauCeti.tangencySplitting_eq_zero_iff`: for small `ε` its zeros are the points `-j ε`, `j < k`.
* `TauCeti.analyticOrderAt_tangencySplitting`, `TauCeti.deriv_tangencySplitting_ne_zero`: for
  `ε ≠ 0` these zeros are simple.
* `TauCeti.eventually_forall_prod_stdComplexSymplecticForm_fderiv_tangencySplitting_pos`: for
  small `ε` the perturbed graph is a symplectic curve in `ℂ²`.
* `TauCeti.apply_eq_zero_iff_of_apply_eq_sub_graph_tangencySplitting`: the perturbed graph meets the
  line `w = 0` exactly at the points `(-j ε, 0)`.

In the namespace `TauCeti.HomologicalOrientation`:

* `localIndex_eq_one_of_apply_eq_sub_graph_tangencySplitting`: each of these intersections counts
  `1`.
* `sum_localIndex_eq_localIndex_of_apply_eq_sub_graph_tangencySplitting`: together they count the
  local intersection number `k` of the tangency.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix E.2 (the perturbation of tangent and critical branches into
  transverse immersed ones, and the comparison of local intersection numbers).
* M. J. Micallef and B. White, *The structure of branch points in minimal surfaces and in
  pseudoholomorphic curves*, Ann. of Math. 141 (1995), 35–85.
-/

public section

noncomputable section

open Filter Finset Metric Module Topology

namespace TauCeti

variable (β : ContDiffBump (0 : ℂ)) (k : ℕ) (ε : ℂ)

/-- **The cutoff perturbation splitting the tangency `w = z ^ k`.** For a smooth bump function `β`
centred at `0`, the function `z ↦ z ^ k + β z (∏_{j < k} (z + j ε) - z ^ k)`. It is `z ^ k` outside
the ball of radius `β.rOut`, and the polynomial `∏_{j < k} (z + j ε)`, with the roots `-j ε`, on the
closed ball of radius `β.rIn`. -/
def tangencySplitting (z : ℂ) : ℂ :=
  z ^ k + (β z : ℂ) * (∏ j ∈ range k, (z + j * ε) - z ^ k)

variable {β k ε}

/-- The defining formula of the perturbation. -/
theorem tangencySplitting_apply (z : ℂ) :
    tangencySplitting β k ε z = z ^ k + (β z : ℂ) * (∏ j ∈ range k, (z + j * ε) - z ^ k) :=
  (rfl)

variable (β k) in
/-- The perturbation is jointly smooth in `(ε, z)`, as a function of real variables. -/
theorem contDiff_uncurry_tangencySplitting {n : ℕ∞} :
    ContDiff ℝ n (Function.uncurry (tangencySplitting β k)) := by
  have hβ : ContDiff ℝ n fun q : ℂ × ℂ ↦ (β q.2 : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (β.contDiff.comp contDiff_snd)
  have hP : ContDiff ℝ n fun q : ℂ × ℂ ↦ ∏ j ∈ range k, (q.2 + j * q.1) :=
    contDiff_prod fun j _ ↦ contDiff_snd.add (contDiff_const.mul contDiff_fst)
  exact (contDiff_snd.pow k).add (hβ.mul (hP.sub (contDiff_snd.pow k)))

variable (β k ε) in
/-- The perturbation is smooth as a function of a real variable. -/
theorem contDiff_tangencySplitting {n : ℕ∞} : ContDiff ℝ n (tangencySplitting β k ε) :=
  (contDiff_uncurry_tangencySplitting β k).comp (contDiff_const.prodMk contDiff_id)

/-- Outside the ball of radius `β.rOut` the perturbation is `z ^ k`. -/
theorem tangencySplitting_eq_pow_of_rOut_le {z : ℂ} (hz : β.rOut ≤ ‖z‖) :
    tangencySplitting β k ε z = z ^ k := by
  rw [tangencySplitting_apply, β.zero_of_le_dist (by rwa [dist_zero_right])]
  simp

/-- On the closed ball of radius `β.rIn` the perturbation is the polynomial
`∏_{j < k} (z + j ε)`. -/
theorem tangencySplitting_eq_prod_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ β.rIn) :
    tangencySplitting β k ε z = ∏ j ∈ range k, (z + j * ε) := by
  rw [tangencySplitting_apply, β.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz)]
  simp

/-- Near a point of the open ball of radius `β.rIn` the perturbation is the polynomial
`∏_{j < k} (z + j ε)`. -/
theorem tangencySplitting_eventuallyEq_prod {z : ℂ} (hz : ‖z‖ < β.rIn) :
    tangencySplitting β k ε =ᶠ[𝓝 z] fun z ↦ ∏ j ∈ range k, (z + j * ε) := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
  exact tangencySplitting_eq_prod_of_norm_le (mem_ball_zero_iff.1 hw).le

/-- Near a point outside the closed ball of radius `β.rOut` the perturbation is `z ^ k`. -/
theorem tangencySplitting_eventuallyEq_pow {z : ℂ} (hz : β.rOut < ‖z‖) :
    tangencySplitting β k ε =ᶠ[𝓝 z] (· ^ k) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  exact tangencySplitting_eq_pow_of_rOut_le hw.le

variable (β k) in
/-- For `ε = 0` the perturbation is `z ^ k` itself. -/
@[simp]
theorem tangencySplitting_zero_right : tangencySplitting β k 0 = (· ^ k) := by
  ext z
  simp [tangencySplitting_apply]

/-! ### The zeros of the perturbation -/

/-- The size condition `(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k` forces every root `-j ε`, `j < k`, into
the open ball of radius `β.rIn`. -/
private theorem mul_norm_lt_rIn (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) (hk : k ≠ 0) :
    k * ‖ε‖ < β.rIn := by
  have hr := β.rIn_pos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hA : 0 ≤ ((m + 1 : ℕ) : ℝ) * ‖ε‖ := by positivity
  have h₁ : β.rIn ^ m * (β.rIn + (m + 1 : ℕ) * ‖ε‖) ≤ (β.rIn + (m + 1 : ℕ) * ‖ε‖) ^ (m + 1) := by
    rw [pow_succ]
    gcongr
    linarith
  have h₂ : β.rIn ^ m * (β.rIn + (m + 1 : ℕ) * ‖ε‖) < β.rIn ^ m * (2 * β.rIn) := by
    calc _ < 2 * β.rIn ^ (m + 1) := h₁.trans_lt hε
      _ = β.rIn ^ m * (2 * β.rIn) := by ring
  linarith [lt_of_mul_lt_mul_left h₂ (by positivity)]

/-- Under the size condition every root `-j ε`, `j < k`, lies in the open ball of radius
`β.rIn`, where the perturbation is the polynomial. -/
private theorem norm_neg_mul_lt_rIn (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {j : ℕ}
    (hj : j < k) : ‖-((j : ℂ) * ε)‖ < β.rIn := by
  rw [norm_neg, norm_mul, Complex.norm_natCast]
  refine lt_of_le_of_lt ?_ (mul_norm_lt_rIn hε (by omega))
  gcongr

/-- Outside the closed ball of radius `β.rIn`, the size condition makes the polynomial so close to
`z ^ k` that the perturbation does not vanish. -/
private theorem tangencySplitting_ne_zero_of_rIn_lt
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {z : ℂ} (hz : β.rIn < ‖z‖) :
    tangencySplitting β k ε z ≠ 0 := by
  set r := ‖z‖
  set A := (k : ℝ) * ‖ε‖
  have hr₀ := β.rIn_pos
  have hA : 0 ≤ A := by positivity
  have hr : 0 < r := hr₀.trans hz
  -- The estimate `(β.rIn + A) ^ k < 2 β.rIn ^ k` propagates to every radius `r ≥ β.rIn`.
  have hlt : (r + A) ^ k < 2 * r ^ k := by
    have hmono : ((r + A) * β.rIn) ^ k ≤ ((β.rIn + A) * r) ^ k :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hz.le hA]) k
    rw [mul_pow, mul_pow] at hmono
    have : (r + A) ^ k * β.rIn ^ k < 2 * r ^ k * β.rIn ^ k := by
      calc _ ≤ (β.rIn + A) ^ k * r ^ k := hmono
        _ < 2 * β.rIn ^ k * r ^ k := by gcongr
        _ = 2 * r ^ k * β.rIn ^ k := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hP : ‖∏ j ∈ range k, (z + j * ε) - z ^ k‖ ≤ (r + A) ^ k - r ^ k := by
    have := norm_prod_add_sub_pow_card_le_of_norm_le (range k) z (a := fun j : ℕ ↦ (j : ℂ) * ε)
      (A := A) fun j hj ↦ by
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.1 hj).le) (norm_nonneg _)
    rwa [card_range] at this
  have hβ : ‖(β z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg β.nonneg]
    exact β.le_one
  have hcut : ‖(β z : ℂ) * (∏ j ∈ range k, (z + j * ε) - z ^ k)‖ ≤ (r + A) ^ k - r ^ k :=
    (norm_mul_le _ _).trans <| by
      calc _ ≤ 1 * ((r + A) ^ k - r ^ k) := by gcongr
        _ = _ := one_mul _
  intro h0
  have heq : z ^ k = -((β z : ℂ) * (∏ j ∈ range k, (z + j * ε) - z ^ k)) := by
    rw [tangencySplitting_apply] at h0
    linear_combination h0
  have hnorm := congrArg norm heq
  rw [norm_neg, norm_pow] at hnorm
  linarith

/-- **The zeros of the perturbation.** When `(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the perturbation
vanishes exactly at the points `-j ε` for `j < k`: the cutoff creates no new zero. -/
theorem tangencySplitting_eq_zero_iff (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {z : ℂ} :
    tangencySplitting β k ε z = 0 ↔ ∃ j < k, z = -(j * ε) := by
  constructor
  · intro h0
    by_cases hz : ‖z‖ ≤ β.rIn
    · rw [tangencySplitting_eq_prod_of_norm_le hz, prod_eq_zero_iff] at h0
      obtain ⟨j, hj, hzj⟩ := h0
      exact ⟨j, mem_range.1 hj, eq_neg_of_add_eq_zero_left hzj⟩
    · exact absurd h0 (tangencySplitting_ne_zero_of_rIn_lt hε (not_le.1 hz))
  · rintro ⟨j, hj, rfl⟩
    rw [tangencySplitting_eq_prod_of_norm_le (norm_neg_mul_lt_rIn hε hj).le]
    exact prod_eq_zero (mem_range.2 hj) (by ring)

variable (β k) in
/-- The size condition of `tangencySplitting_eq_zero_iff` holds for every small enough `ε`. -/
theorem eventually_rIn_add_mul_norm_pow_lt :
    ∀ᶠ ε : ℂ in 𝓝 0, (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k := by
  have hcont : Continuous fun ε : ℂ ↦ (β.rIn + k * ‖ε‖) ^ k := by fun_prop
  refine hcont.continuousAt.eventually_lt continuousAt_const ?_
  simp only [norm_zero, mul_zero, add_zero]
  linarith [pow_pos β.rIn_pos k]

/-! ### The zeros are simple -/

/-- For `ε ≠ 0` the roots `-j ε` of `∏_{i < k} (z + i ε)` are distinct, hence simple. -/
private theorem analyticOrderAt_prod_add_mul (hε : ε ≠ 0) {j : ℕ} (hj : j < k) :
    analyticOrderAt (fun z ↦ ∏ i ∈ range k, (z + i * ε)) (-(j * ε)) = 1 := by
  have hinj : Set.InjOn (fun i : ℕ ↦ -((i : ℂ) * ε)) (range k) := fun i _ i' _ h ↦ by
    simpa [hε] using h
  simpa only [sub_neg_eq_add] using analyticOrderAt_prod_sub_of_injOn hinj (mem_range.2 hj)

/-- **The zeros of the perturbation are simple.** When `ε ≠ 0` and
`(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the perturbation vanishes to order exactly `1` at each of its
zeros `-j ε`, `j < k`. -/
theorem analyticOrderAt_tangencySplitting (hε₀ : ε ≠ 0)
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {j : ℕ} (hj : j < k) :
    analyticOrderAt (tangencySplitting β k ε) (-(j * ε)) = 1 := by
  have hjk := norm_neg_mul_lt_rIn hε hj
  rw [analyticOrderAt_congr (tangencySplitting_eventuallyEq_prod hjk)]
  exact analyticOrderAt_prod_add_mul hε₀ hj

/-- **The perturbed graph crosses the line `w = 0` transversally.** When `ε ≠ 0` and
`(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the perturbation has a nonzero complex derivative at each of
its zeros `-j ε`, `j < k`. -/
theorem deriv_tangencySplitting_ne_zero (hε₀ : ε ≠ 0)
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {j : ℕ} (hj : j < k) :
    deriv (tangencySplitting β k ε) (-(j * ε)) ≠ 0 := by
  have hjk := norm_neg_mul_lt_rIn hε hj
  have hEq := tangencySplitting_eventuallyEq_prod (k := k) (ε := ε) hjk
  have hP : AnalyticAt ℂ (fun z ↦ ∏ i ∈ range k, (z + i * ε)) (-(j * ε)) := by fun_prop
  have h0 : ∏ i ∈ range k, (-((j : ℂ) * ε) + i * ε) = 0 :=
    prod_eq_zero (mem_range.2 hj) (by ring)
  rw [hEq.deriv_eq, ← hP.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero]
  simpa [h0] using analyticOrderAt_prod_add_mul hε₀ hj

/-! ### The perturbed graph is a symplectic curve -/

variable (β k) in
/-- **The perturbed graph is a symplectic curve.** For every small enough `ε`, the graph
`z ↦ (z, g z)` of the perturbation `g = tangencySplitting β k ε` is positive for the standard
symplectic form `ω ⊕ ω` of `ℂ²`: at every point `z` the form is positive on the images
`(1, Dg 1)` and `(I, Dg I)` of the oriented frame `(1, I)` under the derivative of the graph. -/
theorem eventually_forall_prod_stdComplexSymplecticForm_fderiv_tangencySplitting_pos :
    ∀ᶠ ε : ℂ in 𝓝 0, ∀ z : ℂ, 0 < stdComplexSymplecticForm.prod stdComplexSymplecticForm
      (1, fderiv ℝ (tangencySplitting β k ε) z 1)
      (Complex.I, fderiv ℝ (tangencySplitting β k ε) z Complex.I) := by
  -- The perturbation as a smooth function of `(ε, z)`; its derivative in `z` is a partial
  -- derivative, continuous in `(ε, z)`.
  set G : ℂ × ℂ → ℂ := fun q ↦ tangencySplitting β k q.1 q.2
  have hG : ContDiff ℝ 1 G := contDiff_uncurry_tangencySplitting β k
  have hpartial : ∀ ε z v, fderiv ℝ (tangencySplitting β k ε) z v = fderiv ℝ G (ε, z) (0, v) := by
    intro ε z v
    have h := ((hG.differentiable one_ne_zero) (ε, z)).hasFDerivAt.comp z
      ((hasFDerivAt_const ε z).prodMk (hasFDerivAt_id z))
    -- Unfolding `G`, the perturbation for this `ε` is `G` composed with `z ↦ (ε, z)`.
    have hGcomp : tangencySplitting β k ε = G ∘ fun z ↦ (ε, z) := funext fun _ ↦ rfl
    rw [hGcomp, h.fderiv]
    simp
  set Φ : ℂ × ℂ → ℝ := fun q ↦ stdComplexSymplecticForm.prod stdComplexSymplecticForm
    (1, fderiv ℝ G q (0, 1)) (Complex.I, fderiv ℝ G q (0, Complex.I))
  have hΦ : Continuous Φ := by
    have hD := hG.continuous_fderiv one_ne_zero
    simp only [Φ, prod_stdComplexSymplecticForm_one_I]
    exact continuous_const.add (Complex.continuous_im.comp
      ((Complex.continuous_conj.comp (hD.clm_apply continuous_const)).mul
        (hD.clm_apply continuous_const)))
  -- For `ε = 0` the graph is that of `z ^ k`, which is a symplectic curve; by compactness this
  -- persists for small `ε` on the closed ball where the cutoff is supported.
  have hΦ₀ : ∀ y, 0 < Φ (0, y) := fun y ↦ by
    simp only [Φ, ← hpartial, tangencySplitting_zero_right]
    exact (differentiableAt_pow k).prod_stdComplexSymplecticForm_fderiv_pos
  have hev := (isCompact_closedBall (0 : ℂ) β.rOut).eventually_forall_of_forall_eventually
    (x₀ := (0 : ℂ)) (P := fun ε z ↦ 0 < Φ (ε, z))
    fun y _ ↦ hΦ.continuousAt.eventually (lt_mem_nhds (hΦ₀ y))
  filter_upwards [hev] with ε hε z
  by_cases hz : ‖z‖ ≤ β.rOut
  · simpa only [Φ, ← hpartial] using hε z (mem_closedBall_zero_iff.2 hz)
  · -- Outside the closed ball the perturbation is `z ^ k` near `z`.
    rw [(tangencySplitting_eventuallyEq_pow (not_le.1 hz)).fderiv_eq]
    exact (differentiableAt_pow k).prod_stdComplexSymplecticForm_fderiv_pos

/-! ### Local intersection numbers -/

/-- **The perturbed graph meets the line `w = 0` at `k` points.** When
`(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the graph `w ↦ (w, g w)` of the perturbation
`g = tangencySplitting β k ε` meets the line `z ↦ (z, 0)` exactly at the points `(-j ε, 0)` for
`j < k`: the zeros of `F (z, w) = (z, 0) - (w, g w)` are the pairs `(-j ε, -j ε)`. -/
theorem apply_eq_zero_iff_of_apply_eq_sub_graph_tangencySplitting {F : C(ℂ × ℂ, ℂ × ℂ)}
    (hF : ∀ p, F p = (p.1, 0) - (p.2, tangencySplitting β k ε p.2))
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {p : ℂ × ℂ} :
    F p = 0 ↔ ∃ j < k, p = (-(j * ε), -(j * ε)) := by
  rw [hF, Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero, zero_sub, neg_eq_zero,
    tangencySplitting_eq_zero_iff hε]
  constructor
  · rintro ⟨h₁, j, hj, h₂⟩
    exact ⟨j, hj, Prod.ext (h₁.trans h₂) h₂⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨rfl, j, hj, rfl⟩

namespace HomologicalOrientation

variable {n : ℕ} (o : HomologicalOrientation (ℂ × ℂ) (ℂ × ℂ) n) (hn : finrank ℝ (ℂ × ℂ) = n)

include hn

/-- **Each new intersection is transverse and counts `1`.** When `ε ≠ 0` and
`(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the graph of the perturbation `g = tangencySplitting β k ε` and
the line `w = 0` meet at `(-j ε, 0)`, for `j < k`, with local intersection number `1`: the local
index at `(-j ε, -j ε)` of `F (z, w) = (z, 0) - (w, g w)` is `1`. -/
theorem localIndex_eq_one_of_apply_eq_sub_graph_tangencySplitting {F : C(ℂ × ℂ, ℂ × ℂ)}
    (hF : ∀ p, F p = (p.1, 0) - (p.2, tangencySplitting β k ε p.2)) (hε₀ : ε ≠ 0)
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) {j : ℕ} (hj : j < k) :
    o.localIndex o F (-(j * ε), -(j * ε)) = 1 := by
  set P : ℂ → ℂ := fun z ↦ ∏ i ∈ range k, (z + i * ε) with hPdef
  have hjk := norm_neg_mul_lt_rIn hε hj
  -- Near the intersection the perturbation is the polynomial `P`, whose graph is holomorphic.
  let G : C(ℂ × ℂ, ℂ × ℂ) := ⟨fun p ↦ (p.1, 0) - (p.2, P p.2), by fun_prop⟩
  have hFG : F =ᶠ[𝓝 (-(j * ε), -(j * ε))] G := by
    filter_upwards [continuous_snd.continuousAt.eventually
      (tangencySplitting_eventuallyEq_prod (k := k) (ε := ε) hjk)] with p hp
    simp only [hF, G, ContinuousMap.coe_mk, hPdef, hp]
  have hP0 : P (-(j * ε)) = 0 := prod_eq_zero (mem_range.2 hj) (by ring)
  rw [o.localIndex_congr o hn hFG,
    o.localIndex_eq_analyticOrderNatAt_sub_of_apply_eq_graph_sub_graph hn (f := fun _ ↦ 0) (g := P)
      (fun _ ↦ rfl) analyticAt_const (by fun_prop) hP0.symm]
  simp only [sub_zero, analyticOrderNatAt]
  rw [analyticOrderAt_prod_add_mul hε₀ hj]
  simp

/-- **The local intersection numbers are preserved.** When `k ≠ 0`, `ε ≠ 0` and
`(β.rIn + k ‖ε‖) ^ k < 2 β.rIn ^ k`, the local intersection numbers of the line `w = 0` with the
graph of the perturbation `g = tangencySplitting β k ε`, summed over their `k` meetings
`(-j ε, 0)`, equal the local intersection number `k` of the line with the curve `w = z ^ k` at the
origin. The perturbation is `z ^ k` outside the ball of radius `β.rOut`, and inside it the
tangency has split into `k` transverse intersections. -/
theorem sum_localIndex_eq_localIndex_of_apply_eq_sub_graph_tangencySplitting
    {F F₀ : C(ℂ × ℂ, ℂ × ℂ)} (hF : ∀ p, F p = (p.1, 0) - (p.2, tangencySplitting β k ε p.2))
    (hF₀ : ∀ p, F₀ p = (p.1, 0) - (p.2, p.2 ^ k)) (hk : k ≠ 0) (hε₀ : ε ≠ 0)
    (hε : (β.rIn + k * ‖ε‖) ^ k < 2 * β.rIn ^ k) :
    ∑ p ∈ (range k).image (fun j : ℕ ↦ (-(j * ε), -(j * ε))), o.localIndex o F p =
      o.localIndex o F₀ (0, 0) := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (-((j : ℂ) * ε), -((j : ℂ) * ε))) (range k) :=
    fun i _ j _ hij ↦ by
      have := congrArg Prod.fst hij
      simp only [neg_inj, mul_eq_mul_right_iff, hε₀, or_false] at this
      exact_mod_cast this
  rw [sum_image hinj, sum_congr rfl fun j hj ↦
    o.localIndex_eq_one_of_apply_eq_sub_graph_tangencySplitting hn hF hε₀ hε (mem_range.1 hj),
    o.localIndex_eq_of_apply_eq_sub_graph_pow hn hF₀ hk]
  simp

end HomologicalOrientation

end TauCeti
