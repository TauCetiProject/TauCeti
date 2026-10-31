/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Basic

/-!
# The second-kind partial Legendre transform

For a first-kind generating function `S(q, Q)`, the change of variables
`(q, Q) ↦ (q, P)`, where `P = -∂_Q S`, is locally invertible when the negative
`Q,Q` Hessian is invertible. On its inverse branch the partial Legendre transform is
`F₂(q, P) = S(q, Q(q, P)) + P(Q(q, P))`.

This file constructs that chart with specified open source and target, proves uniqueness
of the inverse branch, and establishes the transition identities
`dF₂(δq, δP) = p(δq) + δP(Q)`. Thus it describes the same cotangent relation by
`p = ∂_q F₂` and `Q = ∂_P F₂`, with the latter equality expressed by evaluation on
covectors. No identification of a space with its double dual is needed.

The construction works on real Banach spaces; in particular it applies to open local
models of finite-dimensional cotangent bundles. The transform has geometric meaning
only on the chart target, and the derivative identities hold on a neighborhood of the
distinguished point in that target.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition,
  Springer, 1989, §48 (generating functions).
-/

public section

noncomputable section

open ContinuousLinearMap Filter
open scoped Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The change from position variables to mixed position-momentum variables:
`(q, Q) ↦ (q, -∂_Q S(q, Q))`. -/
def cotangentLegendreProjection (S : V × W → ℝ) (x : V × W) : V × StrongDual ℝ W :=
  (x.1, (cotangentGeneratingTarget S x).2)

@[simp]
theorem cotangentLegendreProjection_fst (S : V × W → ℝ) (x : V × W) :
    (cotangentLegendreProjection S x).1 = x.1 :=
  (rfl)

@[simp]
theorem cotangentLegendreProjection_snd (S : V × W → ℝ) (x : V × W) :
    (cotangentLegendreProjection S x).2 = (cotangentGeneratingTarget S x).2 :=
  (rfl)

/-- The negative `Q,Q` Hessian, whose invertibility makes `(q, Q) ↦ (q, P)`
a valid local change of variables. -/
def cotangentLegendreHessian (S : V × W → ℝ) (x : V × W) :
    W →L[ℝ] StrongDual ℝ W :=
  -(precomp ℝ (inr ℝ V W) ∘L fderiv ℝ (fderiv ℝ S) x ∘L inr ℝ V W)

@[simp]
theorem cotangentLegendreHessian_apply_apply (S : V × W → ℝ) (x : V × W) (b c : W) :
    cotangentLegendreHessian S x b c = -fderiv ℝ (fderiv ℝ S) x (0, b) (0, c) :=
  (rfl)

variable {S : V × W → ℝ} {x : V × W}

/-- A `C^(n+1)` generating function gives a `C^n` mixed-variable projection. -/
theorem contDiffAt_cotangentLegendreProjection {n : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (n + 1) S x) : ContDiffAt ℝ n (cotangentLegendreProjection S) x :=
  contDiffAt_fst.prodMk (contDiffAt_cotangentGeneratingTarget hS).snd

/-- The derivative of the mixed-variable projection. -/
theorem hasFDerivAt_cotangentLegendreProjection
    (hS : DifferentiableAt ℝ (fderiv ℝ S) x) :
    HasFDerivAt (cotangentLegendreProjection S)
      ((fst ℝ V W).prod (-(precomp ℝ (inr ℝ V W) ∘L fderiv ℝ (fderiv ℝ S) x))) x :=
  hasFDerivAt_fst.prodMk (hasFDerivAt_cotangentGeneratingTarget hS).snd

/-- An invertible negative `Q,Q` Hessian makes the mixed-variable projection derivative
invertible. -/
theorem isInvertible_fderiv_cotangentLegendreProjection
    (hS : DifferentiableAt ℝ (fderiv ℝ S) x)
    (hM : (cotangentLegendreHessian S x).IsInvertible) :
    (fderiv ℝ (cotangentLegendreProjection S) x).IsInvertible := by
  obtain ⟨e, he⟩ := hM
  let A := -(precomp ℝ (inr ℝ V W) ∘L fderiv ℝ (fderiv ℝ S) x)
  refine ⟨(ContinuousLinearEquiv.refl ℝ V).skewProd e (A ∘L inl ℝ V W), ?_⟩
  rw [(hasFDerivAt_cotangentLegendreProjection hS).fderiv]
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · rfl
  · have he' : e u.2 = A (0, u.2) := by
      simpa [cotangentLegendreHessian, A] using
        DFunLike.congr_fun he u.2
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.skewProd_apply,
      coe_comp, Function.comp_apply, inl_apply, ContinuousLinearMap.prod_apply, he']
    have hadd := A.map_add (u.1, 0) (0, u.2)
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
    exact (add_comm _ _).trans hadd.symm

section Chart

variable [CompleteSpace V] [CompleteSpace W] {x₀ : V × W}

private def legendreDerivEquiv (hS : ContDiffAt ℝ 2 S x₀)
    (hM : (cotangentLegendreHessian S x₀).IsInvertible) :
    (V × W) ≃L[ℝ] V × StrongDual ℝ W :=
  (isInvertible_fderiv_cotangentLegendreProjection
    ((hS.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero) hM).choose

omit [CompleteSpace V] [CompleteSpace W] in
private theorem hasStrictFDerivAt_legendreDerivEquiv (hS : ContDiffAt ℝ 2 S x₀)
    (hM : (cotangentLegendreHessian S x₀).IsInvertible) :
    HasStrictFDerivAt (cotangentLegendreProjection S)
      (legendreDerivEquiv hS hM : _ →L[ℝ] _) x₀ := by
  have he := (isInvertible_fderiv_cotangentLegendreProjection
    ((hS.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero) hM).choose_spec
  rw [legendreDerivEquiv, he]
  exact (contDiffAt_cotangentLegendreProjection (n := 1) hS).hasStrictFDerivAt one_ne_zero

/-- The local change of variables `(q, Q) ↦ (q, P)` near a point with invertible
negative `Q,Q` Hessian. Its source and target specify the domains of this chart. -/
def cotangentLegendreChart (hS : ContDiffAt ℝ 2 S x₀)
    (hM : (cotangentLegendreHessian S x₀).IsInvertible) :
    OpenPartialHomeomorph (V × W) (V × StrongDual ℝ W) :=
  (hasStrictFDerivAt_legendreDerivEquiv hS hM).toOpenPartialHomeomorph _

variable (hS : ContDiffAt ℝ 2 S x₀) (hM : (cotangentLegendreHessian S x₀).IsInvertible)

@[simp]
theorem coe_cotangentLegendreChart :
    ⇑(cotangentLegendreChart hS hM) = cotangentLegendreProjection S :=
  (rfl)

/-- The distinguished point belongs to the position-coordinate domain. -/
theorem mem_cotangentLegendreChart_source : x₀ ∈ (cotangentLegendreChart hS hM).source :=
  (hasStrictFDerivAt_legendreDerivEquiv hS hM).mem_toOpenPartialHomeomorph_source

/-- Its mixed-coordinate image belongs to the mixed-coordinate domain. -/
theorem image_mem_cotangentLegendreChart_target :
    cotangentLegendreProjection S x₀ ∈ (cotangentLegendreChart hS hM).target :=
  (hasStrictFDerivAt_legendreDerivEquiv hS hM).image_mem_toOpenPartialHomeomorph_target

/-- The inverse mixed-coordinate chart is as smooth as the first derivatives of `S`
at the distinguished point. -/
theorem contDiffAt_cotangentLegendreChart_symm {n : WithTop ℕ∞}
    (hSn : ContDiffAt ℝ (n + 1) S x₀) (hn : n ≠ 0) :
    ContDiffAt ℝ n (cotangentLegendreChart hS hM).symm (cotangentLegendreProjection S x₀) :=
  (contDiffAt_cotangentLegendreProjection hSn).to_localInverse
    (hasStrictFDerivAt_legendreDerivEquiv hS hM).hasFDerivAt hn

/-- Every local inverse agrees with this inverse branch as a germ. -/
theorem eventuallyEq_cotangentLegendreChart_symm {g : V × StrongDual ℝ W → V × W}
    (hg : ∀ᶠ x in 𝓝 x₀, g (cotangentLegendreProjection S x) = x) :
    g =ᶠ[𝓝 (cotangentLegendreProjection S x₀)] (cotangentLegendreChart hS hM).symm :=
  (hasStrictFDerivAt_legendreDerivEquiv hS hM).localInverse_unique hg

/-- The second-kind partial Legendre transform `F₂(q,P) = S(q,Q) + P(Q)`,
where `(q,Q)` is the inverse mixed-coordinate branch. Only its values on the
target of `cotangentLegendreChart` represent the change of generating function. -/
def cotangentPartialLegendre (y : V × StrongDual ℝ W) : ℝ :=
  S ((cotangentLegendreChart hS hM).symm y) + y.2 ((cotangentLegendreChart hS hM).symm y).2

theorem cotangentPartialLegendre_def (y : V × StrongDual ℝ W) :
    cotangentPartialLegendre hS hM y =
      S ((cotangentLegendreChart hS hM).symm y) +
        y.2 ((cotangentLegendreChart hS hM).symm y).2 :=
  (rfl)

/-- In the original coordinates, the transform is precisely `S + P(Q)`. -/
theorem cotangentPartialLegendre_cotangentLegendreProjection {x : V × W}
    (hx : x ∈ (cotangentLegendreChart hS hM).source) :
    cotangentPartialLegendre hS hM (cotangentLegendreProjection S x) =
      S x + (cotangentGeneratingTarget S x).2 x.2 := by
  have hb : (cotangentLegendreChart hS hM).symm (cotangentLegendreProjection S x) = x := by
    simpa only [coe_cotangentLegendreChart] using (cotangentLegendreChart hS hM).left_inv hx
  rw [cotangentPartialLegendre_def, hb, cotangentLegendreProjection_snd]

/-- The partial Legendre transform is `C^n` at the distinguished mixed-coordinate point
when `S` is `C^(n+1)` there and `n ≠ 0`. -/
theorem contDiffAt_cotangentPartialLegendre {n : WithTop ℕ∞}
    (hSn : ContDiffAt ℝ (n + 1) S x₀) (hn : n ≠ 0) :
    ContDiffAt ℝ n (cotangentPartialLegendre hS hM) (cotangentLegendreProjection S x₀) := by
  have hb := contDiffAt_cotangentLegendreChart_symm hS hM hSn hn
  have hx : (cotangentLegendreChart hS hM).symm (cotangentLegendreProjection S x₀) = x₀ :=
    (hasStrictFDerivAt_legendreDerivEquiv hS hM).localInverse_apply_image
  exact ((hx ▸ hSn.of_le (by simp)).comp _ hb).add (contDiffAt_snd.clm_apply hb.snd)

/-- **The transition identities for a generating function of the second kind.** On a
neighborhood of the distinguished mixed-coordinate point, `dF₂(δq,δP) = p(δq) + δP(Q)`.
Here `(q,Q)` is the inverse branch and `p = ∂_q S(q,Q)`. -/
theorem eventually_fderiv_cotangentPartialLegendre :
    ∀ᶠ y in 𝓝 (cotangentLegendreProjection S x₀), ∀ u : V × StrongDual ℝ W,
      fderiv ℝ (cotangentPartialLegendre hS hM) y u =
        (cotangentGeneratingSource S ((cotangentLegendreChart hS hM).symm y)).2 u.1 +
          u.2 ((cotangentLegendreChart hS hM).symm y).2 := by
  let b := (cotangentLegendreChart hS hM).symm
  have hb := contDiffAt_cotangentLegendreChart_symm hS hM hS one_ne_zero
  have hi : ∀ᶠ y in 𝓝 (cotangentLegendreProjection S x₀),
      cotangentLegendreProjection S (b y) = y :=
    (hasStrictFDerivAt_legendreDerivEquiv hS hM).eventually_right_inverse
  have hs : ∀ᶠ y in 𝓝 (cotangentLegendreProjection S x₀), ContDiffAt ℝ 2 S (b y) :=
    (hasStrictFDerivAt_legendreDerivEquiv hS hM).localInverse_tendsto.eventually
      (hS.eventually (by simp))
  filter_upwards [hb.eventually (by simp), hs, hi.eventually_nhds] with y hby hSy hiy
  have hb' : DifferentiableAt ℝ b y := hby.differentiableAt one_ne_zero
  have hfirst : (fun z ↦ (b z).1) =ᶠ[𝓝 y] Prod.fst :=
    hiy.mono fun z hz ↦ congrArg Prod.fst hz
  have hdfirst := hfirst.fderiv_eq (𝕜 := ℝ)
  rw [fderiv.fst hb', fderiv_fst] at hdfirst
  have hfst (u : V × StrongDual ℝ W) : (fderiv ℝ b y u).1 = u.1 := by
    simpa only [coe_comp, Function.comp_apply, coe_fst'] using
      congrArg (fun L : (V × StrongDual ℝ W) →L[ℝ] V ↦ L u) hdfirst
  have hP (c : W) : fderiv ℝ S (b y) (0, c) = -y.2 c := by
    have hp := congrArg (fun z : V × StrongDual ℝ W ↦ z.2 c) hiy.self_of_nhds
    simpa only [cotangentLegendreProjection_snd, cotangentGeneratingTarget_snd_apply,
      neg_eq_iff_eq_neg] using hp
  have hd := ((hSy.differentiableAt two_ne_zero).hasFDerivAt.comp y hb'.hasFDerivAt).add
    (hasFDerivAt_snd.clm_apply hb'.hasFDerivAt.snd)
  simp only [Function.comp_def, Pi.add_def] at hd
  intro u
  have hdef : cotangentPartialLegendre hS hM =
      fun z ↦ S (b z) + z.2 (b z).2 :=
    funext (cotangentPartialLegendre_def hS hM)
  rw [hdef, hd.fderiv]
  have hu : fderiv ℝ b y u = (u.1, 0) + (0, (fderiv ℝ b y u).2) := by
    ext <;> simp [hfst]
  simp only [_root_.add_apply, coe_comp, coe_snd', Function.comp_apply, flip_apply]
  rw [hu, map_add, hP, cotangentGeneratingSource_snd_apply]
  simp [b]

end Chart

end TauCeti
