/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The strong maximum principle

The weak maximum principles of `TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple`
and `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple` bound a subsolution
by its frontier values. This file proves the **strong maximum principle** in a finite-dimensional
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
vanishes. Hence `u` is locally constant near every point where it attains its maximum, and
preconnectedness spreads this over the whole set.

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
  for `-Δ - b·∇ + c`, which needs no sign condition.
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

/-- A `C²` subsolution of `-Δ - b·∇ + c` in a ball, with bounded coefficients `‖b‖ ≤ β` and
`0 ≤ c ≤ γ`, that is nonnegative at a point `x₀` of the bounding sphere, strictly below `u x₀`
inside the ball and weakly below it on the sphere, has no local maximum at `x₀`: by Hopf's lemma
its outward derivative there is positive. -/
private theorem not_isLocalMax_of_lt_ball_of_le_sphere {y x₀ : E} {R β γ : ℝ} (hR : 0 < R)
    (hx₀ : x₀ ∈ sphere y R) (hucont : ContinuousOn u (closedBall y R))
    (huinterior : ∀ x ∈ ball y R, ContDiffAt ℝ 2 u x) (hderiv : DifferentiableAt ℝ u x₀)
    (hc : ∀ x ∈ ball y R, 0 ≤ c x) (hcγ : ∀ x ∈ ball y R, c x ≤ γ)
    (hb : ∀ x ∈ ball y R, ‖b x‖ ≤ β)
    (hsub : ∀ x ∈ ball y R, c x * u x ≤ Δ u x + fderiv ℝ u x (b x)) (hnonneg : 0 ≤ u x₀)
    (hlt : ∀ x ∈ ball y R, u x < u x₀) (hle : ∀ x ∈ sphere y R, u x ≤ u x₀) :
    ¬IsLocalMax u x₀ := by
  intro hmax
  -- Write `x₀ = y + R • e` for the unit outward normal `e`.
  set e := R⁻¹ • (x₀ - y) with he_def
  have hx₀e : y + R • e = x₀ := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, Real.norm_of_nonneg hR.le, ← dist_eq_norm, mem_sphere.mp hx₀,
      inv_mul_cancel₀ hR.ne']
  have hpos := fderiv_pos_of_mul_le_laplacian_add_fderiv_of_lt_ball_of_le_sphere hR he hucont
    huinterior (hx₀e ▸ hderiv) hc hcγ hb hsub (hx₀e ▸ hnonneg) (hx₀e ▸ hlt) (hx₀e ▸ hle)
  rw [hx₀e, hmax.fderiv_eq_zero] at hpos
  exact lt_irrefl _ hpos

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
  -- Work on a ball `ball x (3 * r)` on which `u` is `C²`, bounded by `u x`, and a subsolution
  -- with bounded coefficients.
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hcd.eventually (by simp)).and (hmax.and (hc.and (hcγ.and (hb.and hsub)))))
  set r := r₀ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hball : ∀ ⦃y⦄, dist y x < 3 * r →
      ContDiffAt ℝ 2 u y ∧ u y ≤ u x ∧ 0 ≤ c y ∧ c y ≤ γ ∧ ‖b y‖ ≤ β ∧
        c y * u y ≤ Δ u y + fderiv ℝ u y (b y) := fun y hy =>
    hr₀sub y (by rw [mem_ball]; linarith)
  by_contra hne
  -- Some point `x₂` close to `x` has a strictly smaller value.
  obtain ⟨x₂, hx₂x, hx₂ne⟩ : ∃ x₂, dist x₂ x < r ∧ u x₂ ≠ u x := by
    by_contra! h
    exact hne (Metric.eventually_nhds_iff.mpr ⟨r, hr, fun y hy => h y hy⟩)
  -- The part `Z` of the level set `{u = u x}` in `closedBall x (2 * r)` is compact.
  set Z := closedBall x (2 * r) ∩ u ⁻¹' {u x}
  have hcont : ContinuousOn u (closedBall x (2 * r)) := fun y hy =>
    (hball (by rw [mem_closedBall] at hy; linarith)).1.continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z :=
    hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hZcompact : IsCompact Z :=
    (isCompact_closedBall x (2 * r)).of_isClosed_subset hZclosed inter_subset_left
  have hxZ : x ∈ Z := ⟨mem_closedBall_self (by positivity), rfl⟩
  have hx₂Z : x₂ ∉ Z := fun h => hx₂ne h.2
  -- `ρ` is the distance from `x₂` to `Z`, attained at `x₀ ∈ Z`.
  set ρ := infDist x₂ Z
  have hρ : 0 < ρ := (hZclosed.notMem_iff_infDist_pos ⟨x, hxZ⟩).mp hx₂Z
  have hρr : ρ < r := (infDist_le_dist_of_mem hxZ).trans_lt hx₂x
  obtain ⟨x₀, hx₀Z, hx₀dist⟩ := hZcompact.exists_infDist_eq_dist ⟨x, hxZ⟩ x₂
  have hnear : ∀ ⦃y⦄, dist y x₂ ≤ ρ → dist y x < 2 * r := fun y hy => by
    linarith [dist_triangle y x₂ x]
  have hin : ∀ y ∈ ball x₂ ρ, dist y x < 3 * r := fun y hy => by
    rw [mem_ball] at hy
    linarith [hnear hy.le]
  have hlt : ∀ y ∈ ball x₂ ρ, u y < u x₀ := fun y hy => by
    rw [mem_ball] at hy
    have hyx := hnear hy.le
    refine hx₀Z.2 ▸ lt_of_le_of_ne (hball (by linarith)).2.1 fun hyu => ?_
    have hyZ : y ∈ Z := ⟨mem_closedBall.mpr hyx.le, hyu⟩
    have := infDist_le_dist_of_mem (x := x₂) hyZ
    rw [dist_comm] at this
    linarith
  have hle : ∀ y ∈ sphere x₂ ρ, u y ≤ u x₀ := fun y hy => by
    rw [mem_sphere] at hy
    exact hx₀Z.2 ▸ (hball (by linarith [hnear hy.le])).2.1
  -- `x₀` is again a local maximum, on the sphere touching `Z`: this contradicts Hopf's lemma.
  have hx₀x : dist x₀ x < 3 * r := by
    linarith [hnear (y := x₀) (by rw [dist_comm, ← hx₀dist])]
  refine not_isLocalMax_of_lt_ball_of_le_sphere hρ (by rw [mem_sphere, dist_comm, ← hx₀dist])
    (fun y hy => (hball (by rw [mem_closedBall] at hy; linarith [hnear hy])).1.continuousAt
      |>.continuousWithinAt)
    (fun y hy => (hball (hin y hy)).1) ((hball hx₀x).1.differentiableAt (by simp))
    (fun y hy => (hball (hin y hy)).2.2.1) (fun y hy => (hball (hin y hy)).2.2.2.1)
    (fun y hy => (hball (hin y hy)).2.2.2.2.1) (fun y hy => (hball (hin y hy)).2.2.2.2.2)
    (hx₀Z.2 ▸ hnonneg) hlt hle ?_
  refine Metric.eventually_nhds_iff_ball.mpr ⟨3 * r - dist x₀ x, by linarith, fun y hy => ?_⟩
  rw [mem_ball] at hy
  exact hx₀Z.2 ▸ (hball (by linarith [dist_triangle y x₀ x])).2.1

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
  -- The points near which `u` is identically `u a` form an open set, which is relatively closed
  -- in `U` by continuity and the local principle, and contains `a`.
  have hlocal : ∀ x ∈ U, u x = u a → ∀ᶠ y in 𝓝 x, u y = u a := fun x hx hxa => by
    have hxmax : IsMaxOn u U x := fun y hy => hxa ▸ hmax hy
    obtain ⟨γ, hγ⟩ := hcbdd x hx
    obtain ⟨β, hβ⟩ := hbbdd x hx
    simpa only [hxa] using eventually_eq_of_mul_le_laplacian_add_fderiv_of_isLocalMax
      (b := b) (hcd x hx) (eventually_of_mem (hU.mem_nhds hx) hc) (eventually_map.mp hγ)
      (eventually_map.mp hβ) (eventually_of_mem (hU.mem_nhds hx) hsub) (hxa ▸ hnonneg)
      (hxmax.isLocalMax (hU.mem_nhds hx))
  have hsubset : U ⊆ {x | ∀ᶠ y in 𝓝 x, u y = u a} := by
    refine hUconn.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds
      ⟨a, ha, hlocal a ha rfl⟩ ?_
    rintro x ⟨hxcl, hxU⟩
    refine hlocal x hxU (by_contra fun hxa => ?_)
    obtain ⟨y, hy, hyO⟩ := mem_closure_iff_nhds.mp hxcl _
      ((hcd x hxU).continuousAt.eventually_ne hxa)
    exact hy hyO.self_of_nhds
  exact fun x hx => (hsubset hx).self_of_nhds

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
`b` and `c ≥ 0` be locally bounded on `U`, and let `u` and `v` be `C²` on `U` with
`Δ v + ⟪b, ∇v⟫ - c v ≤ Δ u + ⟪b, ∇u⟫ - c u` there. If `u ≤ v` on `U` and they agree at a point of
`U`, then they agree on all of `U`. No sign condition on `u` or `v` is needed. -/
theorem eqOn_of_laplacian_add_fderiv_sub_mul_le_of_le_of_eq (hU : IsOpen U) (ha : a ∈ U)
    (hUconn : IsPreconnected U) (hucd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hvcd : ∀ x ∈ U, ContDiffAt ℝ 2 v x) (hc : ∀ x ∈ U, 0 ≤ c x)
    (hcbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) c)
    (hbbdd : ∀ x ∈ U, (𝓝 x).IsBoundedUnder (· ≤ ·) fun y ↦ ‖b y‖)
    (hL : ∀ x ∈ U,
      Δ v x + fderiv ℝ v x (b x) - c x * v x ≤ Δ u x + fderiv ℝ u x (b x) - c x * u x)
    (hle : ∀ x ∈ U, u x ≤ v x) (heq : u a = v a) :
    EqOn u v U := by
  have h := eqOn_const_of_mul_le_laplacian_add_fderiv_of_isMaxOn (u := u - v) hU ha hUconn
    (fun x hx => (hucd x hx).sub (hvcd x hx)) hc hcbdd hbbdd
    (fun x hx => by
      rw [(hucd x hx).laplacian_sub (hvcd x hx),
        fderiv_sub ((hucd x hx).differentiableAt (by simp))
          ((hvcd x hx).differentiableAt (by simp))]
      simp only [Pi.sub_apply, sub_apply]
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
