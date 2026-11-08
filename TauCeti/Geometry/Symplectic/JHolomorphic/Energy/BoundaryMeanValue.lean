/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.BoundaryMeanValueInequality
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# The boundary mean-value inequality for `J`-holomorphic half-discs

Let `V` be a real inner product space, `J : V → (V →L[ℝ] V)` an almost complex structure on `V`
written as a matrix-valued function, and `L ⊆ V` a closed linear subspace. Consider a solution
`u` of the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` on a half-disc `{0 ≤ im z} ∩ ball x₀ r`
centred on the real axis, regular up to the straight edge, with the boundary condition
`u(s) ∈ L` on that edge. Derivatives are taken within the closed upper half-plane, so
`∂ₛu = du(1)` and `∂ₜu = du(i)` make sense on the edge.

Suppose that along `L` the structure `J` maps `L` into its orthogonal complement:
`⟪a, J(p) b⟫ = 0` for `p, a, b ∈ L`. In the boundary analysis of holomorphic curves with
totally real boundary conditions this is arranged by a choice of metric for which `J T L` is
orthogonal to `T L` and `L` is totally geodesic; here `L` is linear and the metric is the inner
product of `V`. Then the energy density `w = ‖∂ₛu‖²` satisfies the Neumann condition

`∂ₜ w = 0` on the real axis.

Indeed `∂ₜ w = 2 ⟪∂ₛu, ∂ₛ∂ₜu⟫` by symmetry of the second derivative, and differentiating the
Cauchy--Riemann equation along the axis gives `∂ₛ∂ₜu = dJ(u)[∂ₛu] ∂ₛu + J(u) ∂ₛ∂ₛu`. On the
axis `u`, `∂ₛu` and `∂ₛ∂ₛu` lie in `L`. So the second term is orthogonal to `∂ₛu`, and so is the
first, because the derivative of `J` along `L` inherits the orthogonality from `J`.

Together with the interior differential inequality `Δ w ≥ -A w²`
(`TauCeti.neg_mul_norm_fderiv_one_pow_four_le_laplacian`), the boundary mean-value inequality
`TauCeti.pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian` then
bounds `∂ₛu` at a point of the edge by its energy on the half-disc, when that energy is small:

`π r² ‖∂ₛu(x₀)‖² ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} ‖∂ₛu‖²`.

This is the boundary counterpart of the interior estimate
`TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`. As there, one smallness
threshold works for all curves with image in a fixed compact set.

## Main results

* `TauCeti.inner_fderiv_apply_apply_eq_zero`: if `J(q)` maps `L` into `Lᗮ` for `q ∈ L` near
  `p`, then so does the derivative of `J` at `p` in the directions of `L`.
* `TauCeti.fderivWithin_norm_fderivWithin_one_sq_apply_I_eq_zero`: the Neumann condition
  `∂ₜ ‖∂ₛu‖² = 0` on the real axis.
* `TauCeti.pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball`: the
  boundary mean-value inequality for `J`-holomorphic half-discs, with explicit constants.
* `TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral`:
  the same with a smallness threshold that is uniform over curves with image in a compact set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality, and its boundary
  version for curves with totally real boundary conditions, proved by reflecting the energy
  density, which satisfies the Neumann condition for a metric adapted to the boundary).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology Complex Metric MeasureTheory Real Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {L : Submodule ℝ V}

/-- If `J(q)` maps the closed subspace `L` into its orthogonal complement for every `q ∈ L` near
`p ∈ L`, then so does the derivative of `J` at `p` in every direction `v ∈ L`:
`⟪a, dJ(p)[v] b⟫ = 0` for `a, b ∈ L`. -/
theorem inner_fderiv_apply_apply_eq_zero (hL : IsClosed (L : Set V)) {p : V} (hp : p ∈ L)
    (hJ : DifferentiableAt ℝ J p)
    (hJL : ∀ᶠ q in 𝓝[(L : Set V)] p, ∀ a ∈ L, ∀ b ∈ L, ⟪a, J q b⟫_ℝ = 0)
    {v a b : V} (hv : v ∈ L) (ha : a ∈ L) (hb : b ∈ L) :
    ⟪a, fderiv ℝ J p v b⟫_ℝ = 0 := by
  have hφ := (innerSL ℝ a).hasFDerivAt.comp p (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const b p))
  have h0 : HasFDerivWithinAt (fun q ↦ ⟪a, J q b⟫_ℝ) (0 : V →L[ℝ] ℝ) L p :=
    (hasFDerivWithinAt_const (0 : ℝ) p _).congr_of_eventuallyEq
      (hJL.mono fun q hq ↦ hq a ha b hb) ((hJL.self_of_nhdsWithin hp) a ha b hb)
  have hv' : v ∈ tangentConeAt ℝ (L : Set V) p := by rwa [L.tangentConeAt_eq hL hp]
  simpa using hφ.hasFDerivWithinAt.unique_on h0 hv'

/-- The derivative along the real axis of a map sending the axis into a closed subspace lies in
that subspace. -/
private theorem apply_one_mem_of_hasFDerivWithinAt {f : ℂ → V} {f' : ℂ →L[ℝ] V} {U : Set ℂ}
    (hU : IsOpen U) (hL : IsClosed (L : Set V)) {x : ℂ} (hx : x ∈ U) (hx0 : x.im = 0)
    (hf : HasFDerivWithinAt f f' ({z | 0 ≤ z.im} ∩ U) x)
    (hfL : ∀ y ∈ U, y.im = 0 → f y ∈ L) : f' 1 ∈ L := by
  have hU' : ∀ᶠ t : ℝ in 𝓝 0, x + t • (1 : ℂ) ∈ U :=
    (Continuous.tendsto' (by fun_prop) 0 x (by simp)).eventually (hU.mem_nhds hx)
  have hline : HasDerivAt (fun t : ℝ ↦ f (x + t • (1 : ℂ))) (f' 1) 0 :=
    (hf.hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt' (hU'.mono fun t ht ↦ ⟨by simp [hx0], ht⟩)
  have h := hline.mem_tangentConeAt (S := (L : Set V))
    (hU'.mono fun t ht ↦ hfL _ ht (by simp [hx0]))
  simp only [zero_smul, add_zero] at h
  rwa [L.tangentConeAt_eq hL (hfL x hx hx0)] at h

/-- Differentiating the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` along the real axis gives
`∂ₛ∂ₜu = dJ(u)[∂ₛu] ∂ₛu + J(u) ∂ₛ∂ₛu`. Here `D₁` and `D₂` are the first derivative of `u` within a
set `S` containing a real segment through `x`, and its derivative at `x`. -/
private theorem apply_one_I_eq_of_hasFDerivWithinAt {S : Set ℂ} {D₁ : ℂ → ℂ →L[ℝ] V}
    {D₂ : ℂ →L[ℝ] ℂ →L[ℝ] V} {x : ℂ} (hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • (1 : ℂ) ∈ S)
    (hu : HasFDerivWithinAt u (D₁ x) S x) (hD₁ : HasFDerivWithinAt D₁ D₂ S x)
    (hJ : DifferentiableAt ℝ J (u x)) (hCR : ∀ y ∈ S, D₁ y I = J (u y) (D₁ y 1)) :
    D₂ 1 I = fderiv ℝ J (u x) (D₁ x 1) (D₁ x 1) + J (u x) (D₂ 1 1) := by
  have hlhs : HasDerivAt (fun t : ℝ ↦ D₁ (x + t • (1 : ℂ)) I) (D₂ 1 I) 0 :=
    (((ContinuousLinearMap.apply ℝ V I).hasFDerivAt.comp_hasFDerivWithinAt x
      hD₁).hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt' hline
  have hJline : HasDerivAt (fun t : ℝ ↦ J (u (x + t • (1 : ℂ)))) (fderiv ℝ J (u x) (D₁ x 1)) 0 :=
    hJ.hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hu.hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt' hline) (by simp)
  have hξline : HasDerivAt (fun t : ℝ ↦ D₁ (x + t • (1 : ℂ)) 1) (D₂ 1 1) 0 :=
    (((ContinuousLinearMap.apply ℝ V (1 : ℂ)).hasFDerivAt.comp_hasFDerivWithinAt x
      hD₁).hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt' hline
  have hrhs := (hJline.clm_apply hξline).congr_of_eventuallyEq
    (f₁ := fun t : ℝ ↦ D₁ (x + t • (1 : ℂ)) I) (hline.mono fun t ht ↦ hCR _ ht)
  simpa using hlhs.unique hrhs

/-- **The Neumann condition for the energy density.** Let `U` be open and let `u` be `C²` on
`{0 ≤ im z} ∩ U`, up to the real axis, solve the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` there,
and map the points of `U` on the axis into a closed subspace `L`. At a point `x` of `U` on the
axis, if `J` is differentiable at `u x` and `J(q)` maps `L` into `Lᗮ` for `q ∈ L` near `u x`, then
the energy density `‖∂ₛu‖²` has vanishing normal derivative: `∂ₜ ‖∂ₛu‖² = 0` at `x`. Derivatives
are taken within the closed upper half-plane. -/
theorem fderivWithin_norm_fderivWithin_one_sq_apply_I_eq_zero {U : Set ℂ} (hU : IsOpen U)
    (hL : IsClosed (L : Set V)) (hu : ContDiffOn ℝ 2 u ({z | 0 ≤ z.im} ∩ U))
    (hCR : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ U,
      fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1))
    (huL : ∀ y ∈ U, y.im = 0 → u y ∈ L) {x : ℂ} (hx : x ∈ U) (hx0 : x.im = 0)
    (hJ : DifferentiableAt ℝ J (u x))
    (hJL : ∀ᶠ p in 𝓝[(L : Set V)] (u x), ∀ a ∈ L, ∀ b ∈ L, ⟪a, J p b⟫_ℝ = 0) :
    fderivWithin ℝ (fun y ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2) {z | 0 ≤ z.im} x I = 0 := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  set S := H ∩ U
  set D₁ := fderivWithin ℝ u S
  set D₂ := fderivWithin ℝ D₁ S
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_setOfPred_le_im 0).inter hU
  have hxS : x ∈ S := ⟨hx0.ge, hx⟩
  have hHS : ∀ y ∈ U, fderivWithin ℝ u H y = D₁ y := fun y hy ↦
    (fderivWithin_inter (hU.mem_nhds hy)).symm
  have hD₁ : ContDiffOn ℝ 1 D₁ S := hu.fderivWithin hS (by norm_num)
  have hu1 : ∀ y ∈ S, HasFDerivWithinAt u (D₁ y) S y := fun y hy ↦
    ((hu.differentiableOn (by norm_num)) y hy).hasFDerivWithinAt
  have hD₁x : HasFDerivWithinAt D₁ (D₂ x) S x :=
    ((hD₁.differentiableOn (by norm_num)) x hxS).hasFDerivWithinAt
  have hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • (1 : ℂ) ∈ S :=
    ((Continuous.tendsto' (by fun_prop) 0 x (by simp)).eventually (hU.mem_nhds hx)).mono
      fun t ht ↦ ⟨by simp [H, hx0], ht⟩
  -- On the axis, `u`, `∂ₛu` and `∂ₛ∂ₛu` lie in `L`.
  have hvel : ∀ y ∈ U, y.im = 0 → D₁ y 1 ∈ L := fun y hy hy0 ↦
    apply_one_mem_of_hasFDerivWithinAt hU hL hy hy0 (hu1 y ⟨hy0.ge, hy⟩) huL
  have hξ : D₁ x 1 ∈ L := hvel x hx hx0
  have hD₁1 : HasFDerivWithinAt (fun y ↦ D₁ y 1)
      ((ContinuousLinearMap.apply ℝ V (1 : ℂ)).comp (D₂ x)) S x :=
    (ContinuousLinearMap.apply ℝ V (1 : ℂ)).hasFDerivAt.comp_hasFDerivWithinAt x hD₁x
  have hacc : D₂ x 1 1 ∈ L := by
    simpa using apply_one_mem_of_hasFDerivWithinAt hU hL hx hx0 hD₁1 hvel
  -- Differentiating `∂ₜu = J(u) ∂ₛu` along the axis gives `∂ₛ∂ₜu`.
  have hmix := apply_one_I_eq_of_hasFDerivWithinAt hline (hu1 x hxS) hD₁x hJ fun y hy ↦ by
    simpa only [hHS _ hy.2] using hCR _ hy
  -- The second derivative within the half-plane is symmetric, also on the axis.
  have hcl : x ∈ closure (interior S) := by
    rw [interior_inter, hU.interior_eq, interior_setOfPred_le_im, inter_comm]
    exact hU.inter_closure ⟨hx, by rw [closure_setOfPred_lt_im]; exact hx0.ge⟩
  have hsymm : D₂ x I 1 = D₂ x 1 I :=
    (hu x hxS).isSymmSndFDerivWithinAt (by simp) hS hcl hxS I 1
  have heq : fderivWithin ℝ (fun y ↦ ‖fderivWithin ℝ u H y 1‖ ^ 2) H x =
      fderivWithin ℝ (fun y ↦ ‖D₁ y 1‖ ^ 2) S x := by
    rw [← fderivWithin_inter (hU.mem_nhds hx)]
    exact fderivWithin_congr (fun y hy ↦ by simp only [hHS y hy.2]) (by simp only [hHS x hx])
  rw [heq, hD₁1.norm_sq.fderivWithin (hS x hxS)]
  have hJLx := hJL.self_of_nhdsWithin (huL x hx hx0)
  simp [hsymm, hmix, inner_add_right, hJLx _ hξ _ hacc,
    inner_fderiv_apply_apply_eq_zero hL (huL x hx hx0) hJ hJL hξ hξ hξ]

/-- **The boundary mean-value inequality for `J`-holomorphic half-discs.** Let `x₀` lie on the
real axis, and let `u : ℂ → V` be `C³` on the half-disc `{0 ≤ im z} ∩ ball x₀ r`, up to its
straight edge, with `∂ₛu` continuous on the closed half-disc, solving the Cauchy--Riemann equation
`∂ₜu = J(u) ∂ₛu` and mapping the edge into a closed subspace `L`. Derivatives are taken within the
closed upper half-plane. Suppose that `J` is `C²` along `u`, squares to `-1`, and `a`, `b`, `c`
bound the norms of `J`, of its derivative and of its second derivative along `u`, and that at the
boundary values `J(p)` maps `L` into `Lᗮ` for `p ∈ L` nearby. If the energy over the half-disc
is small, `16 (4ac + 2b² + 8a²b²) ∫ ‖∂ₛu‖² < π`, then

`π r² ‖∂ₛu(x₀)‖² ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} ‖∂ₛu‖²`. -/
theorem pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball {x₀ : ℂ}
    {r a b c : ℝ} (hx₀ : x₀.im = 0) (hr : 0 ≤ r) (hL : IsClosed (L : Set V))
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ ball x₀ r))
    (hu' : ContinuousOn (fun y ↦ fderivWithin ℝ u {z | 0 ≤ z.im} y 1)
      ({z | 0 ≤ z.im} ∩ closedBall x₀ r))
    (hCR : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
      fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1))
    (huL : ∀ y ∈ ball x₀ r, y.im = 0 → u y ∈ L)
    (hJL : ∀ y ∈ ball x₀ r, y.im = 0 →
      ∀ᶠ p in 𝓝[(L : Set V)] (u y), ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0)
    (hJ : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ContDiffAt ℝ 2 J (u y))
    (hJsq : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ∀ v, J (u y) (J (u y) v) = -v)
    (ha : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖J (u y)‖ ≤ a)
    (hb : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderiv ℝ J (u y)‖ ≤ b)
    (hc : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖iteratedFDeriv ℝ 2 J (u y)‖ ≤ c)
    (hsmall : 16 * (4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) *
      ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 < π) :
    π * r ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} x₀ 1‖ ^ 2 ≤
      16 * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  set S := H ∩ ball x₀ r
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_setOfPred_le_im 0).inter isOpen_ball
  have hHS : ∀ y ∈ ball x₀ r, fderivWithin ℝ u H y = fderivWithin ℝ u S y := fun y hy ↦
    (fderivWithin_inter (isOpen_ball.mem_nhds hy)).symm
  -- Above the axis the derivatives within the half-plane are ordinary derivatives.
  have hopen : ∀ y ∈ ball x₀ r, 0 < y.im → {z : ℂ | 0 < z.im} ∩ ball x₀ r ∈ 𝓝 y := fun y hy hy0 ↦
    ((isOpen_lt continuous_const continuous_im).inter isOpen_ball).mem_nhds ⟨hy0, hy⟩
  have hHfd : ∀ y : ℂ, 0 < y.im → fderivWithin ℝ u H y = fderiv ℝ u y := fun y hy0 ↦
    fderivWithin_of_mem_nhds (mem_of_superset
      ((isOpen_lt continuous_const continuous_im).mem_nhds hy0) fun z hz ↦ le_of_lt hz)
  refine pi_mul_sq_mul_le_sixteen_mul_setIntegral_inter_ball_of_neg_mul_sq_le_laplacian
    (w := fun y ↦ ‖fderivWithin ℝ u H y 1‖ ^ 2)
    (A := 4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) hx₀ hr ?_ (hu'.norm.pow 2)
    (fun _ _ ↦ by positivity) (fun x hx hx0 ↦ ?_) (fun z hz hz0 ↦ ?_) hsmall
  · exact (((hu.fderivWithin hS (by norm_num)).clm_apply
      (contDiffOn_const (c := (1 : ℂ)))).norm_sq ℝ).congr
      fun y hy ↦ by simp only [hHS y hy.2]
  · rw [fderivWithin_inter (isOpen_ball.mem_nhds hx)]
    exact fderivWithin_norm_fderivWithin_one_sq_apply_I_eq_zero isOpen_ball hL
      (hu.of_le (by norm_num)) hCR huL hx hx0
      ((hJ x ⟨hx0.ge, hx⟩).differentiableAt (by norm_num)) (hJL x hx hx0)
  · -- Above the axis this is the interior differential inequality.
    have hzS : z ∈ S := ⟨hz0.le, hz⟩
    have hnhds : S ∈ 𝓝 z :=
      mem_of_superset (hopen z hz hz0) fun y hy ↦ ⟨(le_of_lt hy.1 : 0 ≤ y.im), hy.2⟩
    have hcongr : (fun y ↦ ‖fderivWithin ℝ u H y 1‖ ^ 2) =ᶠ[𝓝 z]
        fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2 :=
      eventually_of_mem (hopen z hz hz0) fun y hy ↦ by simp only [hHfd y hy.1]
    rw [(laplacian_congr_nhds hcongr).eq_of_nhds, hHfd z hz0, ← pow_mul]
    have hJz := hJ z hzS
    exact neg_mul_norm_fderiv_one_pow_four_le_laplacian (hu.contDiffAt hnhds) hJz
      (eventually_of_mem (hopen z hz hz0) fun y hy ↦ by
        simpa only [hHfd y hy.1] using hCR y ⟨(le_of_lt hy.1 : 0 ≤ y.im), hy.2⟩)
      (hJsq z hzS) (ha z hzS) (hb z hzS) (hc z hzS)

/-- **The boundary mean-value inequality for `J`-holomorphic half-discs in a compact set.** Let
`J` be `C²` on an open set `W` containing a compact set `K`, with `J(x)² = -1` on `K`, and let
`L` be a closed subspace such that `J(p)` maps `L` into `Lᗮ` for every `p ∈ L ∩ W`. There is an
energy threshold `δ > 0` such that every solution `u` of `∂ₜu = J(u) ∂ₛu` on a half-disc
`{0 ≤ im z} ∩ ball x₀ r` centred on the real axis that is `C³` up to the straight edge, has
`∂ₛu` continuous on the closed half-disc, maps the edge into `L` and the half-disc into `K`, and
has energy `∫ ‖∂ₛu‖² < δ` over it, satisfies
`π r² ‖∂ₛu(x₀)‖² ≤ 16 ∫_{{0 ≤ im z} ∩ ball x₀ r} ‖∂ₛu‖²`. Derivatives are taken within the closed
upper half-plane. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral
    {W K : Set V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hL : IsClosed (L : Set V))
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫_ℝ = 0) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃x₀ : ℂ⦄ ⦃r : ℝ⦄, x₀.im = 0 → 0 ≤ r →
      ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ ball x₀ r) →
      ContinuousOn (fun y ↦ fderivWithin ℝ u {z | 0 ≤ z.im} y 1)
        ({z | 0 ≤ z.im} ∩ closedBall x₀ r) →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
        fderivWithin ℝ u {z | 0 ≤ z.im} y I = J (u y) (fderivWithin ℝ u {z | 0 ≤ z.im} y 1)) →
      (∀ y ∈ ball x₀ r, y.im = 0 → u y ∈ L) →
      (∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, u y ∈ K) →
      ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderivWithin ℝ u {z | 0 ≤ z.im} x₀ 1‖ ^ 2 ≤
        16 * ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    ((hJ.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hKW)
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn
    (((hJ.continuousOn_iteratedFDerivWithin le_rfl hW.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen 2 hW).symm).mono hKW)
  -- Nonnegative bounds, so that the constant of the differential inequality is nonnegative.
  set A := 4 * max a 0 * max c 0 + 2 * b ^ 2 + 8 * max a 0 ^ 2 * b ^ 2
  refine ⟨π / (16 * (A + 1)), by positivity,
    fun u x₀ r hx₀ hr hu hu' hCR huL huK hE ↦ ?_⟩
  have hI : 0 ≤ ∫ y in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
      ‖fderivWithin ℝ u {z | 0 ≤ z.im} y 1‖ ^ 2 := by
    positivity
  refine pi_mul_sq_mul_norm_fderivWithin_one_sq_le_sixteen_mul_setIntegral_inter_ball hx₀ hr hL
    hu hu' hCR huL (fun y hy hy0 ↦ ?_) (fun y hy ↦ hJ.contDiffAt (hW.mem_nhds (hKW (huK y hy))))
    (fun y hy ↦ hJsq _ (huK y hy)) (fun y hy ↦ (ha _ (huK y hy)).trans (le_max_left _ 0))
    (fun y hy ↦ hb _ (huK y hy)) (fun y hy ↦ (hc _ (huK y hy)).trans (le_max_left _ 0)) ?_
  · -- Near a boundary value, the points of `L` lie in `W`.
    have hyW : u y ∈ W := hKW (huK y ⟨hy0.ge, hy⟩)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW)]
      with p hpL hpW using hJL p ⟨hpL, hpW⟩
  · rw [lt_div_iff₀ (by positivity)] at hE
    nlinarith

end TauCeti
