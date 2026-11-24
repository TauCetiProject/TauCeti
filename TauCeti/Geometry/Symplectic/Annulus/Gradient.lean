/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DotProduct
public import TauCeti.Geometry.Symplectic.Annulus.DiagonalQuotient

/-!
# The negative gradient of the cyclic action on the diagonal quotient

Let `S_i`, `i ∈ ℤ/N`, be generating functions of a chain of strip maps, in the convention
`y = -∂₁ S_i(x, X)`, `Y = ∂₂ S_i(x, X)`, invariant under the diagonal translation
`(x, X) ↦ (x + 1, X + 1)`. Their cyclic action `W(q) = Σ_i S_i(q_i, q_(i+1))` descends to the
quotient `(ℤ/N → ℝ) ⧸ ℤ 1` of the configuration space by the diagonal integers
(`TauCeti.quotientCyclicAction`), a circle times a vector space. This file equips that quotient with
the Euclidean metric inherited from the configuration space and computes the gradient of the
descended action, whose negative is the vector field of the gradient flow on the configurations.

The Euclidean metric `⟪v, w⟫ = Σ_i v_i w_i` of the configuration space is invariant under the
diagonal translations, and descends to the quotient
(`AddSubgroup.quotientDotProductMetric (AddSubgroup.zmultiples 1)`, installed as
`TauCeti.diagonalQuotientRiemannianBundle`), for which the projection is
a local Riemannian isometry (`AddSubgroup.isLocalRiemannianIsometry_quotientMk`). Read in the
charts of the quotient, the descended metric is again the dot product, so the gradient of the
descended action at the class of `q` is the vector of partial derivatives of `W` at `q`:

`(grad W)_i = ∂_(q_i) W = Y_(i-1) - y_i`,

where `y_i = -∂₁ S_i(q_i, q_(i+1))` is the momentum of the source point of the `i`-th map and
`Y_(i-1) = ∂₂ S_(i-1)(q_(i-1), q_i)` the momentum of the target point of the `(i-1)`-th map
(`TauCeti.mgradient_quotientCyclicAction`). So the negative gradient flow moves the positions with
velocity `dx_i / dt = y_i - Y_(i-1)`. Its zeros are the classes of the critical configurations, the
configurations along which every outgoing momentum is the next incoming momentum
(`TauCeti.mgradient_quotientCyclicAction_eq_zero_iff`). For `C^(n+1)` generating functions the
negative gradient is a `C^n` vector field on the quotient
(`TauCeti.contMDiffAt_neg_mgradient_quotientCyclicAction`,
`TauCeti.contMDiff_neg_mgradient_quotientCyclicAction`), and the projection of a solution of
`dx_i / dt = y_i - Y_(i-1)` on the configuration space is an integral curve of it
(`TauCeti.isMIntegralCurve_mk_comp_neg_mgradient_quotientCyclicAction`).

## Main definitions

* `TauCeti.diagonalQuotientRiemannianBundle`: the dot-product metric of the diagonal quotient.

## Main results

* `TauCeti.diagonalQuotientRiemannianBundle_inner`: this metric is the dot product in the charts of
  the quotient.
* `TauCeti.mgradient_quotientCyclicAction`: the gradient of the descended cyclic action is
  `(Y_(i-1) - y_i)_i`.
* `TauCeti.mgradient_quotientCyclicAction_eq_zero_iff`: its zeros are the classes of the critical
  configurations.
* `TauCeti.contMDiffAt_neg_mgradient_quotientCyclicAction`,
  `TauCeti.contMDiff_neg_mgradient_quotientCyclicAction`: the negative gradient is as smooth as the
  derivatives of the generating functions.
* `TauCeti.isMIntegralCurve_mk_comp_neg_mgradient_quotientCyclicAction`: solutions of
  `dx_i / dt = y_i - Y_(i-1)` project to negative gradient trajectories on the quotient.

## References

* C. C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Inventiones Mathematicae 73 (1983), 33–49 (the gradient flow of the action on
  broken configurations, on the quotient by the diagonal integers).
-/

public section

open Bundle TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

/-- The Riemannian metric of the diagonal quotient `(ι → ℝ) ⧸ ℤ 1`: the dot-product metric
`⟪v, w⟫ = Σ_i v_i w_i`, descended from `ι → ℝ`. -/
abbrev diagonalQuotientRiemannianBundle (ι : Type*) [Fintype ι] :
    RiemannianBundle (fun y : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ) ↦
      TangentSpace 𝓘(ℝ, ι → ℝ) y) :=
  ⟨(AddSubgroup.zmultiples (1 : ι → ℝ)).quotientDotProductMetric.toRiemannianMetric⟩

/-- The metric of the diagonal quotient is the dot product of the tangent vectors, read in the
charts of the quotient. -/
@[simp]
theorem diagonalQuotientRiemannianBundle_inner {ι : Type*} [Fintype ι]
    (y : (ι → ℝ) ⧸ AddSubgroup.zmultiples (1 : ι → ℝ)) (v w : TangentSpace 𝓘(ℝ, ι → ℝ) y) :
    letI := diagonalQuotientRiemannianBundle ι
    inner ℝ v w = dotProduct (v : ι → ℝ) w :=
  (AddSubgroup.zmultiples (1 : ι → ℝ)).quotientDotProductMetric_inner y v w

variable {N : ℕ} [NeZero N] {S : ZMod N → ℝ × ℝ → ℝ} (hS : ∀ i, Function.Periodic (S i) (1, 1))

/-- **The gradient of the cyclic action on the diagonal quotient.** For the Euclidean metric
descended from the configuration space, the gradient of the descended cyclic action at the class of
a configuration `q` is the vector of partial derivatives of `W` at `q`,
`(grad W)_i = Y_(i-1) - y_i`: the momentum `Y_(i-1) = ∂₂ S_(i-1)(q_(i-1), q_i)` of the target point
of the `(i-1)`-th map minus the momentum `y_i = -∂₁ S_i(q_i, q_(i+1))` of the source point of the
`i`-th map. -/
theorem mgradient_quotientCyclicAction {q : ZMod N → ℝ}
    (h : ∀ i, DifferentiableAt ℝ (S i) (q i, q (i + 1))) :
    letI := diagonalQuotientRiemannianBundle (ZMod N)
    mgradient 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS)
        (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) =
      fun i ↦ (stripGeneratingTarget (S (i - 1)) (q (i - 1), q i)).2 -
        (stripGeneratingSource (S i) (q i, q (i + 1))).2 := by
  let := diagonalQuotientRiemannianBundle (ZMod N)
  rw [mgradient_eq_of_inner_eq_dotProduct (diagonalQuotientRiemannianBundle_inner _)]
  funext i
  -- the differential of the descended action is the derivative of `W`, since the differential of
  -- the projection is the identity
  have hd (v : ZMod N → ℝ) : mvfderiv 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS)
      (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) v =
        fderiv ℝ (cyclicAction S) q v := by
    have h' := congrArg (fun L ↦ L v) (mvfderiv_quotientCyclicAction_comp hS q)
    simp only [AddSubgroup.mfderiv_quotientMk, mvfderiv_eq_fderiv] at h'
    -- both sides of `h'` evaluate the two derivatives at `v` through identity maps: the identity
    -- of the tangent space and `NormedSpace.fromTangentSpace q`, which are the identity of
    -- `ZMod N → ℝ` by Mathlib's definitional identification of the tangent spaces with the model
    exact h'
  rw [hd, fderiv_cyclicAction_apply h]
  simp [Pi.single_apply, sub_eq_add_neg, add_comm]

/-- **The zeros of the gradient of the cyclic action on the diagonal quotient.** The gradient of
the descended cyclic action vanishes at the class of a configuration `q` exactly when at every
vertex the target point `(q_i, Y_(i-1))` of the `(i-1)`-th map is the source point `(q_i, y_i)` of
the `i`-th map, that is when `q` is a critical configuration. -/
theorem mgradient_quotientCyclicAction_eq_zero_iff {q : ZMod N → ℝ}
    (h : ∀ i, DifferentiableAt ℝ (S i) (q i, q (i + 1))) :
    letI := diagonalQuotientRiemannianBundle (ZMod N)
    mgradient 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS)
        (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) = 0 ↔
      ∀ i, stripGeneratingTarget (S (i - 1)) (q (i - 1), q i) =
        stripGeneratingSource (S i) (q i, q (i + 1)) := by
  let := diagonalQuotientRiemannianBundle (ZMod N)
  rw [mgradient_eq_zero_iff, mvfderiv_quotientCyclicAction_eq_zero_iff,
    fderiv_cyclicAction_eq_zero_iff h]

/-- **The negative gradient of the cyclic action on the diagonal quotient is `C^n`** at the class of
a configuration `q` if every generating function `S_i` is `C^(n+1)` at the edge `(q_i, q_(i+1))`. -/
theorem contMDiffAt_neg_mgradient_quotientCyclicAction {n : ℕ∞} {q : ZMod N → ℝ}
    (h : ∀ i, ContDiffAt ℝ (n + 1) (S i) (q i, q (i + 1))) :
    letI := diagonalQuotientRiemannianBundle (ZMod N)
    ContMDiffAt 𝓘(ℝ, ZMod N → ℝ) 𝓘(ℝ, ZMod N → ℝ).tangent n
      (fun y ↦ (⟨y, -mgradient 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS) y⟩ :
        TangentBundle 𝓘(ℝ, ZMod N → ℝ) ((ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ))))
      (q : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)) := by
  let := diagonalQuotientRiemannianBundle (ZMod N)
  have := Bundle.instIsContMDiffRiemannianBundle
    (AddSubgroup.zmultiples (1 : ZMod N → ℝ)).quotientDotProductMetric
  simpa only [mgradient_neg] using
    contMDiffAt_mgradient (f := -quotientCyclicAction hS)
      (contMDiffAt_quotientCyclicAction hS (n := n + 1) (by exact_mod_cast h)).neg

/-- **The negative gradient of the cyclic action on the diagonal quotient is a `C^n` vector field**
if the generating functions are `C^(n+1)`. -/
theorem contMDiff_neg_mgradient_quotientCyclicAction {n : ℕ∞}
    (h : ∀ i, ContDiff ℝ (n + 1) (S i)) :
    letI := diagonalQuotientRiemannianBundle (ZMod N)
    ContMDiff 𝓘(ℝ, ZMod N → ℝ) 𝓘(ℝ, ZMod N → ℝ).tangent n
      (fun y ↦ (⟨y, -mgradient 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS) y⟩ :
        TangentBundle 𝓘(ℝ, ZMod N → ℝ)
          ((ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)))) := by
  intro y
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact contMDiffAt_neg_mgradient_quotientCyclicAction hS fun i ↦ (h i).contDiffAt

/-- **Negative gradient trajectories of the cyclic action.** If a curve `γ` of configurations solves
`dγ_i / dt = y_i - Y_(i-1)`, with `y_i = -∂₁ S_i(γ_i, γ_(i+1))` and
`Y_(i-1) = ∂₂ S_(i-1)(γ_(i-1), γ_i)`, then its projection to the diagonal quotient is an integral
curve of the negative gradient of the descended cyclic action. -/
theorem isMIntegralCurve_mk_comp_neg_mgradient_quotientCyclicAction {γ : ℝ → ZMod N → ℝ}
    (h : ∀ t i, DifferentiableAt ℝ (S i) (γ t i, γ t (i + 1)))
    (hγ : ∀ t, HasDerivAt γ (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) t) :
    letI := diagonalQuotientRiemannianBundle (ZMod N)
    IsMIntegralCurve
      (fun t ↦ (γ t : (ZMod N → ℝ) ⧸ AddSubgroup.zmultiples (1 : ZMod N → ℝ)))
      (fun y ↦ -mgradient 𝓘(ℝ, ZMod N → ℝ) (quotientCyclicAction hS) y) := by
  let := diagonalQuotientRiemannianBundle (ZMod N)
  intro t
  have hc := ((AddSubgroup.zmultiples (1 : ZMod N → ℝ)).hasMFDerivAt_quotientMk (𝕜 := ℝ)
    (γ t)).comp t (hγ t).hasFDerivAt.hasMFDerivAt
  beta_reduce
  rw [mgradient_quotientCyclicAction hS (h t)]
  refine hc.congr_mfderiv ?_
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  have hv : (fun i ↦ (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2) =
      -fun i ↦ (stripGeneratingTarget (S (i - 1)) (γ t (i - 1), γ t i)).2 -
        (stripGeneratingSource (S i) (γ t i, γ t (i + 1))).2 := by
    funext i
    simp only [Pi.neg_apply, neg_sub]
  -- the differential of the projection is the identity of the tangent spaces, which Mathlib
  -- identifies with `ZMod N → ℝ` by definition, so its composite with the map is the map itself
  exact congrArg (ContinuousLinearMap.toSpanSingleton ℝ) hv

end TauCeti
