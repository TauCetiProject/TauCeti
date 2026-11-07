/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma
import TauCeti.Analysis.InnerProductSpace.TouchingBall
import TauCeti.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The strong maximum principle

The weak maximum principles of `TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple`
and `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple` bound a subsolution
by its frontier values; with a zeroth-order term `c ≥ 0`, by a nonnegative upper bound of its
frontier values. This file proves the **strong maximum principle** in a finite-dimensional
real inner product space, first for the operator `-Δ - b·∇ + c` with locally bounded drift `b` and
locally bounded zeroth-order coefficient `c ≥ 0`, and then for the Laplacian: a `C²` subsolution
`c u ≤ Δ u + ⟪b, ∇u⟫` on a preconnected open set that attains a nonnegative maximum over the set at
some point of it is constant there. For the Laplacian the sign condition disappears, since a
constant may be subtracted. The minimum principles, the strong comparison principles, and the
harmonic specializations follow.

The proof is the classical one via **Hopf's boundary-point lemma**
(`TauCeti.fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere`), and needs neither a
mean-value property nor analyticity, so it works in every dimension and for variable lower-order
coefficients. The local step is
`TauCeti.eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax`: near a local maximum `x`, if
`u` took a smaller value at some point `x₂`, then the largest ball about `x₂` on which `u < u x`
touches the level set `{u = u x}` at a point `x₀` of its sphere. There `u` is strictly below
`u x₀` inside the ball and weakly below it on the sphere, so Hopf's lemma makes the outward
derivative at `x₀` strictly positive; but `x₀` is again a local maximum, where the derivative
vanishes. This touching-ball argument is
`TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`. Hence `u` is locally constant near
every point where it attains its maximum, and preconnectedness spreads this over the whole set
(`IsPreconnected.eqOn_const_of_eventually_eq`).

Unlike the planar statements of `TauCeti.Analysis.PDE.Harnack.StrongPrinciple`, which use the
analyticity of planar harmonic functions, the results here need the set to be open: a subharmonic
function may be constant near a local maximum and increase further away.

## Main declarations

* `TauCeti.eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax`: a `C²` subsolution of
  `-Δ - b·∇ + c` with a nonnegative local maximum is constant near it; its supersolution mirror
  image is `TauCeti.eventually_eq_of_laplacian_add_fderiv_le_mul_of_isLocalMin`.
* `TauCeti.eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn`: **the strong maximum
  principle** for `-Δ - b·∇ + c` on a preconnected open set.
* `TauCeti.eqOn_const_of_laplacian_add_fderiv_le_mul_of_isMinOn`: the strong minimum principle
  for supersolutions of `-Δ - b·∇ + c`.
* `TauCeti.eqOn_of_laplacian_add_fderiv_sub_mul_le_of_le_of_eq`: the strong comparison principle
  for `-Δ - b·∇ + c`, which needs no sign condition on `c`, `u` or `v`.
* `TauCeti.eventually_eq_of_laplacian_nonneg_of_isLocalMax`: a function that is `C²` at a local
  maximum point and subharmonic near it is constant near it; its superharmonic mirror image is
  `TauCeti.eventually_eq_of_laplacian_nonpos_of_isLocalMin`.
* `TauCeti.eqOn_const_of_laplacian_nonneg_of_isMaxOn`: the strong maximum principle for
  subharmonic functions on a preconnected open set.
* `TauCeti.eqOn_const_of_laplacian_nonpos_of_isMinOn`: the strong minimum principle for
  superharmonic functions.
* `TauCeti.eqOn_of_laplacian_le_of_le_of_eq`: the strong comparison principle for the Laplacian.
* `TauCeti.eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn`,
  `TauCeti.eqOn_const_closure_of_laplacian_nonpos_of_isMinOn`,
  `TauCeti.eqOn_closure_of_laplacian_le_of_le_of_eq`: the same three statements for functions
  continuous up to the boundary, extremal (respectively dominated) over `closure U` at a point
  of `U`.
* `TauCeti.eqOn_const_of_harmonicOnNhd_of_isMaxOn_of_isOpen`,
  `TauCeti.eqOn_const_of_harmonicOnNhd_of_isMinOn_of_isOpen`,
  `TauCeti.eqOn_of_harmonicOnNhd_of_le_of_eq_of_isOpen`,
  `TauCeti.eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero_of_isOpen`,
  `TauCeti.eq_zero_on_or_pos_on_of_harmonicOnNhd_of_nonneg`: the harmonic specializations.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Theorem 3.5; L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.4.2.
-/

public section

noncomputable section

namespace TauCeti

open Filter Function InnerProductSpace Laplacian Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section LowerOrder

variable {U : Set E} {u v c : E → ℝ} {b : E → E} {a : E}

/-- **Local strong maximum principle for `-Δ - b·∇ + c`.** Let `u` be `C²` at a local maximum
point `x` with `0 ≤ u x`, and near `x` let `u` be a subsolution `c u ≤ Δ u + ⟪b, ∇u⟫` with
coefficients bounded as `‖b‖ ≤ β` and `0 ≤ c ≤ γ`. Then `u` is constant on a neighbourhood of
`x`. -/
theorem eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax {x : E} {β γ : ℝ}
    (hcd : ContDiffAt ℝ 2 u x) (hc : ∀ᶠ y in 𝓝 x, 0 ≤ c y) (hcγ : ∀ᶠ y in 𝓝 x, c y ≤ γ)
    (hb : ∀ᶠ y in 𝓝 x, ‖b y‖ ≤ β)
    (hsub : ∀ᶠ y in 𝓝 x, c y * u y ≤ Δ u y + fderiv ℝ u y (b y)) (hnonneg : 0 ≤ u x)
    (hmax : IsLocalMax u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  -- A ball inside the neighbourhood where `u` is `C²` and a subsolution with bounded
  -- coefficients, touching the level set `{u = u x}` from inside at a local maximum `x₀`, would
  -- make the outward derivative at `x₀` positive by Hopf's lemma.
  refine eventually_eq_of_isLocalMax_of_forall_not_lt_ball
    ((hcd.eventually (by simp)).and (hmax.and (hc.and (hcγ.and (hb.and hsub)))))
    ((hcd.eventually (by simp)).mono fun y hy => hy.continuousAt) hmax
    fun y e R hR he hball hx₀max hx₀ hlt => ?_
  choose hcdB hleB hcB hcγB hbB hsubB using fun z (hz : z ∈ closedBall y R) => hball hz
  have hx₀mem : y + R • e ∈ closedBall y R := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_of_nonneg hR.le]
  have hpos := fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere hR he
    (fun z hz => (hcdB z hz).continuousAt.continuousWithinAt)
    (fun z hz => hcdB z (ball_subset_closedBall hz))
    ((hcdB _ hx₀mem).differentiableAt (by simp))
    (fun z hz => hcB z (ball_subset_closedBall hz)) (fun z hz => hcγB z (ball_subset_closedBall hz))
    (fun z hz => hbB z (ball_subset_closedBall hz))
    (fun z hz => hsubB z (ball_subset_closedBall hz)) (hx₀ ▸ hnonneg) hlt
    (fun z hz => hx₀ ▸ hleB z (sphere_subset_closedBall hz))
  rw [hx₀max.fderiv_eq_zero] at hpos
  exact lt_irrefl _ hpos

/-- **Local strong minimum principle for `-Δ - b·∇ + c`.** A `C²` supersolution
`Δ u + ⟪b, ∇u⟫ ≤ c u` near a local minimum point `x` with `u x ≤ 0`, whose coefficients are bounded
as `‖b‖ ≤ β` and `0 ≤ c ≤ γ` near `x`, is constant on a neighbourhood of `x`. -/
theorem eventually_eq_of_laplacian_add_fderiv_le_mul_of_isLocalMin {x : E} {β γ : ℝ}
    (hcd : ContDiffAt ℝ 2 u x) (hc : ∀ᶠ y in 𝓝 x, 0 ≤ c y) (hcγ : ∀ᶠ y in 𝓝 x, c y ≤ γ)
    (hb : ∀ᶠ y in 𝓝 x, ‖b y‖ ≤ β)
    (hsuper : ∀ᶠ y in 𝓝 x, Δ u y + fderiv ℝ u y (b y) ≤ c y * u y) (hnonpos : u x ≤ 0)
    (hmin : IsLocalMin u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  have h := eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax (u := -u) hcd.neg hc hcγ hb
    (hsuper.mono fun y hy => by
      rw [congrFun laplacian_neg y, fderiv_neg]
      simp only [Pi.neg_apply, neg_apply, mul_neg]
      linarith)
    (neg_nonneg.mpr hnonpos) hmin.neg
  exact h.mono fun y hy => by simpa only [Pi.neg_apply, neg_inj] using hy

/-- **Strong maximum principle for `-Δ - b·∇ + c`.** Let `U` be a preconnected open set, and let
`b` and `c ≥ 0` be locally bounded on `U`. A function that is `C²` on `U`, is a subsolution
`c u ≤ Δ u + ⟪b, ∇u⟫` there, and attains a nonnegative maximum over `U` at a point `a ∈ U`, is
constant on `U`.

The sign condition `0 ≤ u a` is needed only because of `c`: for `c = 0` it can be arranged by
subtracting a constant. -/
theorem eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : ∀ x ∈ U, 0 ≤ c x)
    (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hbbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖)
    (hsub : ∀ x ∈ U, c x * u x ≤ Δ u x + fderiv ℝ u x (b x)) (hnonneg : 0 ≤ u a)
    (hmax : IsMaxOn u U a) :
    EqOn u (const E (u a)) U := by
  -- By preconnectedness it suffices that `u` is identically `u a` near every point of `U` at which
  -- it takes the value `u a`: this is the local principle.
  refine hUconn.eqOn_const_of_eventually_eq ha (fun x hx => (hcd x hx).continuousAt)
    fun x hx hxa => ?_
  have hxmax : IsMaxOn u U x := fun y hy => hxa ▸ hmax hy
  obtain ⟨γ, hγ⟩ := hcbdd x hx
  obtain ⟨β, hβ⟩ := hbbdd x hx
  simpa only [hxa] using eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax
    (b := b) (hcd x hx) (eventually_of_mem (hU.mem_nhds hx) hc) (eventually_map.mp hγ)
    (eventually_map.mp hβ) (eventually_of_mem (hU.mem_nhds hx) hsub) (hxa ▸ hnonneg)
    (hxmax.isLocalMax (hU.mem_nhds hx))

/-- **Strong minimum principle for `-Δ - b·∇ + c`.** Let `U` be a preconnected open set, and let
`b` and `c ≥ 0` be locally bounded on `U`. A function that is `C²` on `U`, is a supersolution
`Δ u + ⟪b, ∇u⟫ ≤ c u` there, and attains a nonpositive minimum over `U` at a point `a ∈ U`, is
constant on `U`. -/
theorem eqOn_const_of_laplacian_add_fderiv_le_mul_of_isMinOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : ∀ x ∈ U, 0 ≤ c x)
    (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hbbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖)
    (hsuper : ∀ x ∈ U, Δ u x + fderiv ℝ u x (b x) ≤ c x * u x) (hnonpos : u a ≤ 0)
    (hmin : IsMinOn u U a) :
    EqOn u (const E (u a)) U := by
  have h := eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn (u := -u) hU ha hUconn
    (fun x hx => (hcd x hx).neg) hc hcbdd hbbdd
    (fun x hx => by
      rw [congrFun laplacian_neg x, fderiv_neg]
      simp only [Pi.neg_apply, neg_apply, mul_neg]
      linarith [hsuper x hx])
    (neg_nonneg.mpr hnonpos) hmin.neg
  intro x hx
  simpa only [Pi.neg_apply, const_apply, neg_inj] using h hx

/-- **Strong comparison principle for `-Δ - b·∇ + c`.** Let `U` be a preconnected open set, let
`b` be locally bounded and `c` locally bounded above on `U`, and let `u` and `v` be `C²` on `U`
with `Δ v + ⟪b, ∇v⟫ - c v ≤ Δ u + ⟪b, ∇u⟫ - c u` there. If `u ≤ v` on `U` and they agree at a
point of `U`, then they agree on all of `U`. No sign condition on `c`, `u` or `v` is needed: since
`u - v ≤ 0`, the difference is a subsolution for the coefficient `max c 0`. -/
theorem eqOn_of_laplacian_add_fderiv_sub_mul_le_of_le_of_eq (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hucd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hvcd : ∀ x ∈ U, ContDiffAt ℝ 2 v x) (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hbbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖)
    (hL : ∀ x ∈ U,
      Δ v x + fderiv ℝ v x (b x) - c x * v x ≤ Δ u x + fderiv ℝ u x (b x) - c x * u x)
    (hle : ∀ x ∈ U, u x ≤ v x) (heq : u a = v a) :
    EqOn u v U := by
  -- Since `u - v ≤ 0`, replacing `c` by `max c 0` keeps `u - v` a subsolution.
  have h := eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn (u := u - v)
    (c := fun x ↦ max (c x) 0) hU ha hUconn
    (fun x hx => (hucd x hx).sub (hvcd x hx)) (fun _ _ => le_max_right _ _)
    (fun x hx => by
      obtain ⟨γ, hγ⟩ := hcbdd x hx
      exact isBoundedUnder_of_eventually_le
        ((eventually_map.mp hγ).mono fun _ hy => max_le_max_right 0 hy))
    hbbdd
    (fun x hx => by
      rw [(hucd x hx).laplacian_sub (hvcd x hx),
        fderiv_sub ((hucd x hx).differentiableAt (by simp))
          ((hvcd x hx).differentiableAt (by simp))]
      simp only [Pi.sub_apply, sub_apply]
      have := mul_le_mul_of_nonpos_right (le_max_left (c x) 0) (sub_nonpos.mpr (hle x hx))
      linarith [hL x hx])
    (by simp [heq])
    (fun x hx => by
      simp only [mem_ofPred_eq, Pi.sub_apply, heq, sub_self, sub_nonpos]
      exact hle x hx)
  intro x hx
  have hx' := h hx
  simp only [Pi.sub_apply, const_apply, heq, sub_self, sub_eq_zero] at hx'
  exact hx'

end LowerOrder

section Laplacian

variable {U : Set E} {u v : E → ℝ} {a : E}

/-- **Local strong maximum principle.** A function that is `C²` at a local maximum point `x` and
subharmonic (`0 ≤ Δ u`) near `x` is constant on a neighbourhood of `x`. -/
theorem eventually_eq_of_laplacian_nonneg_of_isLocalMax {x : E} (hcd : ContDiffAt ℝ 2 u x)
    (hlap : ∀ᶠ y in 𝓝 x, 0 ≤ Δ u y) (hmax : IsLocalMax u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  -- Apply the lower-order principle, with `b = 0` and `c = 0`, to `u - u x`, which vanishes at `x`.
  have h := eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax
    (u := fun y ↦ u y - u x) (c := 0) (b := 0) (β := 0) (γ := 0) (hcd.sub contDiffAt_const)
    (.of_forall fun _ ↦ le_rfl) (.of_forall fun _ ↦ le_rfl) (.of_forall fun _ ↦ by simp)
    ((hcd.eventually (by simp)).and hlap |>.mono fun y hy ↦ by
      have h1 : Δ (fun z ↦ u z - u x) y = Δ u y - Δ (fun _ : E ↦ u x) y :=
        hy.1.laplacian_sub contDiffAt_const
      simpa [h1] using hy.2)
    (by simp) (by simpa [IsLocalMax, IsMaxFilter] using hmax)
  exact h.mono fun y hy ↦ by simpa [sub_eq_zero] using hy

/-- **Local strong minimum principle.** A function that is `C²` at a local minimum point `x` and
superharmonic (`Δ u ≤ 0`) near `x` is constant on a neighbourhood of `x`. -/
theorem eventually_eq_of_laplacian_nonpos_of_isLocalMin {x : E} (hcd : ContDiffAt ℝ 2 u x)
    (hlap : ∀ᶠ y in 𝓝 x, Δ u y ≤ 0) (hmin : IsLocalMin u x) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  have h := eventually_eq_of_laplacian_nonneg_of_isLocalMax (u := -u) hcd.neg
    (hlap.mono fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]
      exact neg_nonneg.mpr hy)
    hmin.neg
  exact h.mono fun y hy => by simpa only [Pi.neg_apply, neg_inj] using hy

/-- **Strong maximum principle for subharmonic functions.** A function that is `C²` and
subharmonic (`0 ≤ Δ u`) on a preconnected open set `U`, and attains its maximum over `U` at a
point `a ∈ U`, is constant on `U`. -/
theorem eqOn_const_of_laplacian_nonneg_of_isMaxOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hlap : ∀ x ∈ U, 0 ≤ Δ u x) (hmax : IsMaxOn u U a) :
    EqOn u (const E (u a)) U := by
  -- Apply the lower-order principle, with `b = 0` and `c = 0`, to `u - u a`, which vanishes at `a`.
  have h := eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn
    (u := fun x ↦ u x - u a) (c := 0) (b := 0) hU ha hUconn
    (fun x hx ↦ (hcd x hx).sub contDiffAt_const) (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ isBoundedUnder_const)
    (fun _ _ ↦ by simpa only [Pi.zero_apply, norm_zero] using isBoundedUnder_const)
    (fun x hx ↦ by
      have h1 : Δ (fun z ↦ u z - u a) x = Δ u x - Δ (fun _ : E ↦ u a) x :=
        (hcd x hx).laplacian_sub contDiffAt_const
      simpa [h1] using hlap x hx)
    (by simp) (fun x hx ↦ by simpa using hmax hx)
  intro x hx
  simpa [sub_eq_zero] using h hx

/-- **Strong minimum principle for superharmonic functions.** A function that is `C²` and
superharmonic (`Δ u ≤ 0`) on a preconnected open set `U`, and attains its minimum over `U` at a
point `a ∈ U`, is constant on `U`. -/
theorem eqOn_const_of_laplacian_nonpos_of_isMinOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hlap : ∀ x ∈ U, Δ u x ≤ 0) (hmin : IsMinOn u U a) :
    EqOn u (const E (u a)) U := by
  have h := eqOn_const_of_laplacian_nonneg_of_isMaxOn (u := -u) hU ha hUconn
    (fun x hx => (hcd x hx).neg)
    (fun x hx => by
      rw [congrFun laplacian_neg x, Pi.neg_apply]
      exact neg_nonneg.mpr (hlap x hx))
    hmin.neg
  intro x hx
  simpa only [Pi.neg_apply, const_apply, neg_inj] using h hx

/-- **Strong comparison principle for the Laplacian.** Let `u` and `v` be `C²` on a preconnected
open set `U`, with `u` at least as subharmonic as `v` there (`Δ v ≤ Δ u`). If `u ≤ v` on `U` and
they agree at a point of `U`, then they agree on all of `U`. -/
theorem eqOn_of_laplacian_le_of_le_of_eq (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hucd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hvcd : ∀ x ∈ U, ContDiffAt ℝ 2 v x) (hlap : ∀ x ∈ U, Δ v x ≤ Δ u x)
    (hle : ∀ x ∈ U, u x ≤ v x) (heq : u a = v a) :
    EqOn u v U := by
  have h := eqOn_const_of_laplacian_nonneg_of_isMaxOn (u := u - v) hU ha hUconn
    (fun x hx => (hucd x hx).sub (hvcd x hx))
    (fun x hx => by
      rw [(hucd x hx).laplacian_sub (hvcd x hx), sub_nonneg]
      exact hlap x hx)
    (fun x hx => by
      simp only [mem_ofPred_eq, Pi.sub_apply, heq, sub_self, sub_nonpos]
      exact hle x hx)
  intro x hx
  have hx' := h hx
  simp only [Pi.sub_apply, const_apply, heq, sub_self, sub_eq_zero] at hx'
  exact hx'

/-- **Strong maximum principle up to the boundary.** If `u` is continuous on `closure U`, is `C²`
and subharmonic on the preconnected open set `U`, and attains its maximum over `closure U` at a
point `a ∈ U`, then `u` is constant on `closure U`. -/
theorem eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcont : ContinuousOn u (closure U))
    (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ U, 0 ≤ Δ u x)
    (hmax : IsMaxOn u (closure U) a) :
    EqOn u (const E (u a)) (closure U) :=
  (eqOn_const_of_laplacian_nonneg_of_isMaxOn hU ha hUconn hcd hlap
    (hmax.of_subset subset_closure)).of_subset_closure hcont continuousOn_const subset_closure
    Subset.rfl

/-- **Strong minimum principle up to the boundary.** If `u` is continuous on `closure U`, is `C²`
and superharmonic on the preconnected open set `U`, and attains its minimum over `closure U` at a
point `a ∈ U`, then `u` is constant on `closure U`. -/
theorem eqOn_const_closure_of_laplacian_nonpos_of_isMinOn (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hcont : ContinuousOn u (closure U))
    (hcd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ U, Δ u x ≤ 0)
    (hmin : IsMinOn u (closure U) a) :
    EqOn u (const E (u a)) (closure U) :=
  (eqOn_const_of_laplacian_nonpos_of_isMinOn hU ha hUconn hcd hlap
    (hmin.of_subset subset_closure)).of_subset_closure hcont continuousOn_const subset_closure
    Subset.rfl

/-- **Strong comparison principle up to the boundary.** Let `u` and `v` be continuous on
`closure U` and `C²` on the preconnected open set `U`, with `Δ v ≤ Δ u` on `U`. If `u ≤ v` on
`closure U` and they agree at a point of `U`, then they agree on all of `closure U`. -/
theorem eqOn_closure_of_laplacian_le_of_le_of_eq (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hucont : ContinuousOn u (closure U))
    (hvcont : ContinuousOn v (closure U)) (hucd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hvcd : ∀ x ∈ U, ContDiffAt ℝ 2 v x) (hlap : ∀ x ∈ U, Δ v x ≤ Δ u x)
    (hle : ∀ x ∈ closure U, u x ≤ v x) (heq : u a = v a) :
    EqOn u v (closure U) :=
  (eqOn_of_laplacian_le_of_le_of_eq hU ha hUconn hucd hvcd hlap
    (fun x hx => hle x (subset_closure hx)) heq).of_subset_closure hucont hvcont subset_closure
    Subset.rfl

end Laplacian

section Harmonic

variable {Ω : Set E} {f g : E → ℝ} {a : E}

/-- **Strong maximum principle for harmonic functions.** A real-valued harmonic function on a
preconnected open set that attains its maximum over the set at one of its points is constant
there. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMaxOn_of_isOpen
    (hΩopen : IsOpen Ω) (ha : a ∈ Ω) (hΩconn : IsPreconnected Ω)
    (hf : HarmonicOnNhd f Ω) (hmax : IsMaxOn f Ω a) :
    EqOn f (const E (f a)) Ω :=
  eqOn_const_of_laplacian_nonneg_of_isMaxOn hΩopen ha hΩconn (fun x hx => (hf x hx).1)
    (fun x hx => le_of_eq (hf x hx).2.eq_of_nhds.symm) hmax

/-- **Strong minimum principle for harmonic functions.** A real-valued harmonic function on a
preconnected open set that attains its minimum over the set at one of its points is constant
there. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMinOn_of_isOpen
    (hΩopen : IsOpen Ω) (ha : a ∈ Ω) (hΩconn : IsPreconnected Ω)
    (hf : HarmonicOnNhd f Ω) (hmin : IsMinOn f Ω a) :
    EqOn f (const E (f a)) Ω :=
  eqOn_const_of_laplacian_nonpos_of_isMinOn hΩopen ha hΩconn (fun x hx => (hf x hx).1)
    (fun x hx => le_of_eq (hf x hx).2.eq_of_nhds) hmin

/-- **Strong comparison principle for harmonic functions.** Two harmonic functions on a
preconnected open set, one below the other, that agree at one point of the set agree throughout
it. -/
theorem eqOn_of_harmonicOnNhd_of_le_of_eq_of_isOpen
    (hΩopen : IsOpen Ω) (ha : a ∈ Ω) (hΩconn : IsPreconnected Ω)
    (hf : HarmonicOnNhd f Ω) (hg : HarmonicOnNhd g Ω)
    (hfg : ∀ z ∈ Ω, f z ≤ g z) (hfg_a : f a = g a) : EqOn f g Ω :=
  eqOn_of_laplacian_le_of_le_of_eq hΩopen ha hΩconn (fun x hx => (hf x hx).1)
    (fun x hx => (hg x hx).1)
    (fun x hx => le_of_eq ((hg x hx).2.eq_of_nhds.trans (hf x hx).2.eq_of_nhds.symm)) hfg hfg_a

/-- A nonnegative harmonic function on a preconnected open set that vanishes at one point of the
set vanishes throughout it. -/
theorem eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero_of_isOpen
    (hΩopen : IsOpen Ω) (ha : a ∈ Ω) (hΩconn : IsPreconnected Ω)
    (hf : HarmonicOnNhd f Ω) (hnonneg : ∀ z ∈ Ω, 0 ≤ f z) (hfa : f a = 0) :
    EqOn f 0 Ω := by
  have h := eqOn_const_of_harmonicOnNhd_of_isMinOn_of_isOpen hΩopen ha hΩconn hf
    fun z hz => hfa ▸ hnonneg z hz
  intro z hz
  simpa only [const_apply, hfa, Pi.zero_apply] using h hz

/-- A nonnegative harmonic function on a preconnected open set either vanishes identically or is
strictly positive everywhere on the set. -/
theorem eq_zero_on_or_pos_on_of_harmonicOnNhd_of_nonneg
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hnonneg : ∀ z ∈ Ω, 0 ≤ f z) :
    EqOn f 0 Ω ∨ ∀ z ∈ Ω, 0 < f z := by
  by_cases hzero : ∃ a ∈ Ω, f a = 0
  · obtain ⟨a, ha, hfa⟩ := hzero
    exact Or.inl <| eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero_of_isOpen
      hΩopen ha hΩconn hf hnonneg hfa
  · right
    intro z hz
    exact lt_of_le_of_ne (hnonneg z hz) fun h => hzero ⟨z, hz, h.symm⟩

end Harmonic

end TauCeti

end

end
