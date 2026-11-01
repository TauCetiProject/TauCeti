/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Legendre

/-!
# Generating functions of the third kind

Changing from `(q,Q)` to `(p,Q)`, with `p = ∂_q S`, gives the partial Legendre
transform `F₃(p,Q) = S(q,Q) - p(q)`. Its differential is
`dF₃(δp,δQ) = -δp(q) - P(δQ)`, where `P = -∂_Q S`.
Thus this change of generating function describes the same cotangent relation.

The chart is constructed when the `q,q` Hessian is invertible. Its open source and
target specify where the inverse branch is valid. We reuse the second-kind transform
of the reversed generating function `R(Q,q) = -S(q,Q)`, rather than construct another
inverse function. All constructions work on real Banach spaces and hence on the local
models of finite-dimensional cotangent bundles. Covector evaluations express the
transition identities without identifying a space with its double dual.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition,
  Springer, 1989, §48 (generating functions).
-/

public section

noncomputable section

open ContinuousLinearMap Filter
open scoped Topology

namespace TauCeti

variable {V W : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The third-kind change of variables `(q,Q) ↦ (p,Q)`, with `p = ∂_q S`. -/
def cotangentThirdKindProjection (S : V × W → ℝ) (x : V × W) : StrongDual ℝ V × W :=
  ((cotangentGeneratingSource S x).2, x.2)

@[simp]
theorem cotangentThirdKindProjection_fst (S : V × W → ℝ) (x : V × W) :
    (cotangentThirdKindProjection S x).1 = (cotangentGeneratingSource S x).2 :=
  (rfl)

@[simp]
theorem cotangentThirdKindProjection_snd (S : V × W → ℝ) (x : V × W) :
    (cotangentThirdKindProjection S x).2 = x.2 :=
  (rfl)

/-- A `C^(n+1)` generating function has a `C^n` third-kind projection. -/
theorem contDiffAt_cotangentThirdKindProjection {S : V × W → ℝ} {x : V × W}
    {n : WithTop ℕ∞} (hS : ContDiffAt ℝ (n + 1) S x) :
    ContDiffAt ℝ n (cotangentThirdKindProjection S) x :=
  (contDiffAt_cotangentGeneratingSource hS).snd.prodMk contDiffAt_snd

/-- The third-kind projection is the second-kind projection of the reversed relation,
with source and target coordinates interchanged. -/
theorem cotangentLegendreProjection_reverse (S : V × W → ℝ) (x : V × W) :
    cotangentLegendreProjection (cotangentGeneratingReverse S) x.swap =
      (cotangentThirdKindProjection S x).swap := by
  ext a
  · simp
  · simp [cotangentGeneratingTarget_reverse S x]

/-- The `q,q` Hessian, whose invertibility permits replacing `q` by `p`. -/
def cotangentSourceHessian (S : V × W → ℝ) (x : V × W) :
    V →L[ℝ] StrongDual ℝ V :=
  precomp ℝ (inl ℝ V W) ∘L fderiv ℝ (fderiv ℝ S) x ∘L inl ℝ V W

@[simp]
theorem cotangentSourceHessian_apply_apply (S : V × W → ℝ) (x : V × W) (a b : V) :
    cotangentSourceHessian S x a b = fderiv ℝ (fderiv ℝ S) x (a, 0) (b, 0) :=
  (rfl)

/-- The second-kind Hessian of the reversed relation is the original `q,q` Hessian. -/
theorem cotangentLegendreHessian_reverse (S : V × W → ℝ) (x : V × W) :
    cotangentLegendreHessian (cotangentGeneratingReverse S) x.swap =
      cotangentSourceHessian S x := by
  let e := ContinuousLinearEquiv.prodComm ℝ W V
  let E : ((V × W) →L[ℝ] ℝ) ≃L[ℝ] ((W × V) →L[ℝ] ℝ) :=
    e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have he : fderiv ℝ (cotangentGeneratingReverse S) = fun y ↦ -(E ∘ fderiv ℝ S ∘ e) y := by
    funext y
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simpa [E, e] using fderiv_cotangentGeneratingReverse S y.swap u
  ext a b
  rw [cotangentLegendreHessian_apply_apply, he, fderiv_fun_neg, E.comp_fderiv,
    e.comp_right_fderiv]
  simp [E, e]

/-- An invertible `q,q` Hessian is an invertible second-kind Hessian of the reversed
relation. -/
theorem isInvertible_cotangentLegendreHessian_reverse {S : V × W → ℝ} {x : V × W}
    (hM : (cotangentSourceHessian S x).IsInvertible) :
    (cotangentLegendreHessian (cotangentGeneratingReverse S) x.swap).IsInvertible := by
  rwa [cotangentLegendreHessian_reverse]

section Chart

variable [CompleteSpace V] [CompleteSpace W] {S : V × W → ℝ} {x₀ : V × W}

/-- The third-kind chart `(q,Q) ↦ (p,Q)`, obtained from the second-kind chart
of the reversed relation. Its source and target are the valid coordinate domains. -/
def cotangentThirdKindChart (hS : ContDiffAt ℝ 2 S x₀)
    (hM : (cotangentSourceHessian S x₀).IsInvertible) :
    OpenPartialHomeomorph (V × W) (StrongDual ℝ V × W) :=
  ((Homeomorph.prodComm V W).toOpenPartialHomeomorph.trans
    (cotangentLegendreChart (contDiffAt_cotangentGeneratingReverse hS)
      (isInvertible_cotangentLegendreHessian_reverse hM))).trans
    (Homeomorph.prodComm W (StrongDual ℝ V)).toOpenPartialHomeomorph

variable (hS : ContDiffAt ℝ 2 S x₀)
  (hM : (cotangentSourceHessian S x₀).IsInvertible)

/-- The chart evaluates to `(∂_q S,Q)`. -/
@[simp]
theorem cotangentThirdKindChart_apply (x : V × W) :
    cotangentThirdKindChart hS hM x = cotangentThirdKindProjection S x := by
  simp only [cotangentThirdKindChart, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_prodComm,
    coe_cotangentLegendreChart, cotangentLegendreProjection_reverse S x, Prod.swap_swap]

/-- The distinguished point belongs to the position-coordinate domain. -/
theorem mem_cotangentThirdKindChart_source :
    x₀ ∈ (cotangentThirdKindChart hS hM).source := by
  simpa [cotangentThirdKindChart, OpenPartialHomeomorph.trans_source] using
    mem_cotangentLegendreChart_source (contDiffAt_cotangentGeneratingReverse hS)
      (isInvertible_cotangentLegendreHessian_reverse hM)

/-- The mixed-coordinate image belongs to the chart target. -/
theorem image_mem_cotangentThirdKindChart_target :
    cotangentThirdKindProjection S x₀ ∈ (cotangentThirdKindChart hS hM).target := by
  rw [← cotangentThirdKindChart_apply hS hM x₀]
  exact (cotangentThirdKindChart hS hM).map_source
    (mem_cotangentThirdKindChart_source hS hM)

/-- At the distinguished image the inverse branch returns the original point. -/
@[simp]
theorem cotangentThirdKindChart_symm_projection :
    (cotangentThirdKindChart hS hM).symm (cotangentThirdKindProjection S x₀) = x₀ := by
  rw [← cotangentThirdKindChart_apply hS hM x₀]
  exact (cotangentThirdKindChart hS hM).left_inv (mem_cotangentThirdKindChart_source hS hM)

/-- Every local left inverse of `(q,Q) ↦ (p,Q)` agrees with this inverse branch as a germ. -/
theorem eventuallyEq_cotangentThirdKindChart_symm {g : StrongDual ℝ V × W → V × W}
    (hg : ∀ᶠ x in 𝓝 x₀, g (cotangentThirdKindProjection S x) = x) :
    g =ᶠ[𝓝 (cotangentThirdKindProjection S x₀)] (cotangentThirdKindChart hS hM).symm := by
  have hc := cotangentThirdKindChart_apply hS hM x₀
  have hleft : ∀ᶠ x in 𝓝 x₀, g (cotangentThirdKindChart hS hM x) = x := by
    simpa only [cotangentThirdKindChart_apply] using hg
  have hu := eventuallyEq_of_left_inv_of_right_inv hleft
    ((cotangentThirdKindChart hS hM).eventually_right_inverse'
      (mem_cotangentThirdKindChart_source hS hM))
    ((cotangentThirdKindChart hS hM).tendsto_symm (mem_cotangentThirdKindChart_source hS hM))
  rwa [hc] at hu

/-- The inverse chart expressed by the second-kind inverse branch of the reversed relation. -/
theorem cotangentThirdKindChart_symm_apply (y : StrongDual ℝ V × W) :
    (cotangentThirdKindChart hS hM).symm y =
      ((cotangentLegendreChart (contDiffAt_cotangentGeneratingReverse hS)
        (isInvertible_cotangentLegendreHessian_reverse hM)).symm y.swap).swap := by
  simp [cotangentThirdKindChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

/-- The inverse chart is `C^n` at the distinguished mixed-coordinate point for
`C^(n+1)` input and `n ≠ 0`, including smooth input. -/
theorem contDiffAt_cotangentThirdKindChart_symm {n : WithTop ℕ∞}
    (hSn : ContDiffAt ℝ (n + 1) S x₀) (hn : n ≠ 0) :
    ContDiffAt ℝ n (cotangentThirdKindChart hS hM).symm
      (cotangentThirdKindProjection S x₀) := by
  have hb := contDiffAt_cotangentLegendreChart_symm
    (contDiffAt_cotangentGeneratingReverse hS)
    (isInvertible_cotangentLegendreHessian_reverse hM)
    (contDiffAt_cotangentGeneratingReverse hSn) hn
  rw [cotangentLegendreProjection_reverse S x₀] at hb
  have hdef := funext (cotangentThirdKindChart_symm_apply hS hM)
  rw [hdef]
  simpa only [Function.comp_def, ContinuousLinearEquiv.prodComm_apply] using
    (ContinuousLinearEquiv.prodComm ℝ W V).contDiff.contDiffAt.comp _
      (hb.comp _ (ContinuousLinearEquiv.prodComm ℝ (StrongDual ℝ V) W).contDiff.contDiffAt)

/-- The third-kind partial Legendre transform on the inverse mixed-coordinate branch.
Only its values on the chart target represent the change of generating function. -/
def cotangentThirdKindLegendre (y : StrongDual ℝ V × W) : ℝ :=
  S ((cotangentThirdKindChart hS hM).symm y) -
    y.1 ((cotangentThirdKindChart hS hM).symm y).1

theorem cotangentThirdKindLegendre_def (y : StrongDual ℝ V × W) :
    cotangentThirdKindLegendre hS hM y =
      S ((cotangentThirdKindChart hS hM).symm y) -
        y.1 ((cotangentThirdKindChart hS hM).symm y).1 :=
  (rfl)

/-- In position coordinates the transform is `S - p(q)`. -/
theorem cotangentThirdKindLegendre_cotangentThirdKindProjection {x : V × W}
    (hx : x ∈ (cotangentThirdKindChart hS hM).source) :
    cotangentThirdKindLegendre hS hM (cotangentThirdKindProjection S x) =
      S x - (cotangentGeneratingSource S x).2 x.1 := by
  rw [← cotangentThirdKindChart_apply hS hM x, cotangentThirdKindLegendre_def,
    (cotangentThirdKindChart hS hM).left_inv hx,
    cotangentThirdKindChart_apply hS hM x, cotangentThirdKindProjection_fst]

/-- The third-kind transform is the negative second-kind transform of the reversed relation. -/
private theorem thirdKindLegendre_eq_neg_partialLegendre :
    cotangentThirdKindLegendre hS hM = fun y ↦
      -cotangentPartialLegendre (contDiffAt_cotangentGeneratingReverse hS)
        (isInvertible_cotangentLegendreHessian_reverse hM) y.swap := by
  funext y
  rw [cotangentThirdKindLegendre_def, cotangentPartialLegendre_def,
    cotangentThirdKindChart_symm_apply, cotangentGeneratingReverse_apply]
  simp [sub_eq_add_neg, add_comm]

/-- The partial Legendre transform is `C^n` at the distinguished mixed-coordinate point
for `C^(n+1)` input and `n ≠ 0`. -/
theorem contDiffAt_cotangentThirdKindLegendre {n : WithTop ℕ∞}
    (hSn : ContDiffAt ℝ (n + 1) S x₀) (hn : n ≠ 0) :
    ContDiffAt ℝ n (cotangentThirdKindLegendre hS hM)
      (cotangentThirdKindProjection S x₀) := by
  rw [thirdKindLegendre_eq_neg_partialLegendre]
  have hf := contDiffAt_cotangentPartialLegendre
    (contDiffAt_cotangentGeneratingReverse hS)
    (isInvertible_cotangentLegendreHessian_reverse hM)
    (contDiffAt_cotangentGeneratingReverse hSn) hn
  rw [cotangentLegendreProjection_reverse S x₀] at hf
  exact (hf.comp _
    (ContinuousLinearEquiv.prodComm ℝ (StrongDual ℝ V) W).contDiff.contDiffAt).neg

/-- **Third-kind transition identities.** Near the distinguished mixed-coordinate point,
`dF₃(δp,δQ) = -δp(q) - P(δQ)`. Here `(q,Q)` is the constructed inverse branch,
and `P = -∂_Q S(q,Q)`. -/
theorem eventually_fderiv_cotangentThirdKindLegendre :
    ∀ᶠ y in 𝓝 (cotangentThirdKindProjection S x₀), ∀ u : StrongDual ℝ V × W,
      fderiv ℝ (cotangentThirdKindLegendre hS hM) y u =
        -u.1 ((cotangentThirdKindChart hS hM).symm y).1 -
          (cotangentGeneratingTarget S ((cotangentThirdKindChart hS hM).symm y)).2 u.2 := by
  let e := ContinuousLinearEquiv.prodComm ℝ (StrongDual ℝ V) W
  have ht := eventually_fderiv_cotangentPartialLegendre
    (contDiffAt_cotangentGeneratingReverse hS)
    (isInvertible_cotangentLegendreHessian_reverse hM)
  rw [cotangentLegendreProjection_reverse S x₀] at ht
  filter_upwards [e.continuousAt.tendsto.eventually ht] with y hty
  have hP := cotangentGeneratingSource_reverse S
    ((cotangentThirdKindChart hS hM).symm y)
  rw [cotangentThirdKindChart_symm_apply] at hP
  simp only [Prod.swap_swap] at hP
  have hcomp : (fun y ↦ cotangentPartialLegendre
      (contDiffAt_cotangentGeneratingReverse hS)
      (isInvertible_cotangentLegendreHessian_reverse hM) y.swap) =
      cotangentPartialLegendre (contDiffAt_cotangentGeneratingReverse hS)
        (isInvertible_cotangentLegendreHessian_reverse hM) ∘ e := by
    funext y
    simp [e]
  rw [thirdKindLegendre_eq_neg_partialLegendre]
  intro u
  rw [fderiv_fun_neg, hcomp, e.comp_right_fderiv]
  simp only [e, ContinuousLinearEquiv.prodComm_apply] at hty
  simp only [neg_apply, coe_comp, Function.comp_apply, e,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.prodComm_apply]
  rw [hty, hP, cotangentThirdKindChart_symm_apply]
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

end Chart

end TauCeti
