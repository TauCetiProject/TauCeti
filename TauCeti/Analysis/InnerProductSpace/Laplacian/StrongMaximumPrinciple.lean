/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The strong maximum principle for subharmonic functions

The weak maximum principle of
`TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple` bounds a subharmonic
function on a compact set by its frontier values, but says nothing about what happens when
the bound is attained inside.  This file proves the **strong maximum principle**: a
subharmonic function on an open preconnected set that attains its supremum over that set at
one of its points is constant on the whole set.

The proof is the classical Hopf argument.  Write `M` for the attained maximum.  The domain
is covered by the set where `u = M` and the open set where `u < M`, which are disjoint, so
preconnectedness empties the second as soon as the first is known to be open.  Openness is
where the geometry enters: if a ball `closedBall z r` inside the domain has `u z = M` but
carries a point `p` with `u p < M` near its centre, enlarge the ball around `p` until it
first meets `{u = M}`.  Its radius is the distance from `p` to the complement of the open
set `{u < M}`, attained at a point `w` of the resulting sphere because the ambient space is
proper.  Then `u < M` strictly inside that ball, `u ≤ M` on its sphere, and `u w = M`, so
`TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere` — Hopf's boundary-point
lemma — makes the outward derivative at `w` strictly positive.  But `w` is an interior
maximum point of `u`, where the derivative vanishes.

Negating gives the strong minimum principle for superharmonic functions, and applying the
maximum form to a difference gives the strong comparison principle.

In the plane there is a different route, sharper in one respect: planar harmonic functions
are real-analytic, so an identity propagates along any preconnected set, open or not.  That
is what `TauCeti.Analysis.PDE.Harnack.StrongPrinciple` exploits: it applies to harmonic
functions on `ℂ` without assuming the domain open, whereas the results here cover
subharmonic functions in every dimension, on an open domain.

## Main declarations

* `TauCeti.eqOn_const_of_laplacian_nonneg_of_isMaxOn`: **strong maximum principle**. A `C²`
  subharmonic (`0 ≤ Δ u`) function on an open preconnected set which attains its maximum over
  that set at one of its points is constant there.
* `TauCeti.eqOn_const_of_laplacian_nonpos_of_isMinOn`: the strong minimum principle for
  superharmonic (`Δ u ≤ 0`) functions.
* `TauCeti.eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn`,
  `TauCeti.eqOn_const_closure_of_laplacian_nonpos_of_isMinOn`: the same statements for a
  function continuous up to the boundary, extremal over `closure Ω` at an interior point.
* `TauCeti.eqOn_of_laplacian_le_of_le_of_eq`: **strong comparison principle**. If `Δ v ≤ Δ u`
  on an open preconnected set and `u ≤ v` there with equality at a single point, then `u = v`
  everywhere on the set.
* `TauCeti.eqOn_closure_of_laplacian_le_of_le_of_eq`: the same statement for functions
  continuous up to the boundary, dominated on `closure Ω` and equal at an interior point.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Theorem 3.5; L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.4.2.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u v : E → ℝ} {Ω : Set E} {a : E}

/-- The local step of the strong maximum principle: a subharmonic function bounded by `M` on a
closed ball and equal to `M` at its centre is equal to `M` on the concentric ball of half the
radius.

Hopf's boundary-point lemma is applied to the largest ball around a hypothetical point with
`u < M` that still avoids `{u = M}`. -/
private theorem eqOn_const_of_laplacian_nonneg_of_le_closedBall {z : E} {r M : ℝ} (hr : 0 < r)
    (hcd : ∀ x ∈ closedBall z r, ContDiffAt ℝ 2 u x)
    (hlap : ∀ x ∈ closedBall z r, 0 ≤ Δ u x)
    (hle : ∀ x ∈ closedBall z r, u x ≤ M) (hz : u z = M) :
    ∀ x ∈ ball z (r / 2), u x = M := by
  intro p hp
  by_contra hne
  have hpr : dist p z < r / 2 := mem_ball.1 hp
  have hpball : p ∈ ball z r := mem_ball.2 (by linarith)
  -- The open set of points of `ball z r` where `u` stays strictly below `M`.
  set V : Set E := ball z r ∩ u ⁻¹' Iio M
  have hVopen : IsOpen V :=
    ContinuousOn.isOpen_inter_preimage
      (fun x hx => (hcd x (ball_subset_closedBall hx)).continuousAt.continuousWithinAt)
      isOpen_ball isOpen_Iio
  have hpV : p ∈ V := ⟨hpball, lt_of_le_of_ne (hle p (ball_subset_closedBall hpball)) hne⟩
  have hzV : z ∉ V := fun h => absurd hz h.2.ne
  have hVcne : (Vᶜ : Set E).Nonempty := ⟨z, hzV⟩
  -- The distance from `p` to the complement of `V` is positive, at most `dist p z`, and
  -- attained, because a finite-dimensional normed space is a proper metric space.
  set d : ℝ := infDist p Vᶜ
  have hdpos : 0 < d := (hVopen.isClosed_compl.notMem_iff_infDist_pos hVcne).1 (by simpa using hpV)
  have hdle : d ≤ dist p z := infDist_le_dist_of_mem hzV
  obtain ⟨w, hwV, hwd⟩ := hVopen.isClosed_compl.exists_infDist_eq_dist hVcne p
  have hpw : dist p w = d := hwd.symm
  -- The open ball of radius `d` around `p` stays inside `V`.
  have hballV : ball p d ⊆ V := by
    intro x hx
    by_contra hxV
    have hxc : x ∈ (Vᶜ : Set E) := hxV
    have : d ≤ dist p x := infDist_le_dist_of_mem hxc
    rw [dist_comm] at this
    exact absurd (mem_ball.1 hx) (not_lt.2 this)
  -- The closed ball of radius `d` around `p` stays inside the original ball.
  have hsub : closedBall p d ⊆ ball z r := by
    intro x hx
    have h₁ : dist x z ≤ dist x p + dist p z := dist_triangle x p z
    have h₂ : dist x p ≤ d := mem_closedBall.1 hx
    exact mem_ball.2 (by linarith)
  -- The touching point `w` lies in the original ball, so `u w = M` there.
  have hwmem : w ∈ closedBall p d := mem_closedBall.2 (by rw [dist_comm]; exact hpw.le)
  have hwball : w ∈ ball z r := hsub hwmem
  have hwM : u w = M := by
    rcases lt_or_ge (u w) M with h | h
    · exact absurd (⟨hwball, h⟩ : w ∈ V) hwV
    · exact le_antisymm (hle w (ball_subset_closedBall hwball)) h
  -- The outward unit normal at `w`, and the identification `p + d • e = w`.
  set e : E := d⁻¹ • (w - p) with hedef
  have hwp : ‖w - p‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hpw
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hdpos, hwp,
      inv_mul_cancel₀ hdpos.ne']
  have hde : p + d • e = w := by
    rw [hedef, smul_inv_smul₀ hdpos.ne', add_sub_cancel]
  have hcd' : ∀ x ∈ closedBall p d, ContDiffAt ℝ 2 u x :=
    fun x hx => hcd x (ball_subset_closedBall (hsub hx))
  -- Hopf's boundary-point lemma at `w`.
  have hpos : 0 < fderiv ℝ u (p + d • e) e := by
    refine fderiv_pos_of_laplacian_nonneg_of_lt_ball_of_le_sphere hdpos he
      (fun x hx => (hcd' x hx).continuousAt.continuousWithinAt)
      (fun x hx => hcd' x (ball_subset_closedBall hx)) ?_
      (fun x hx => hlap x (ball_subset_closedBall (hsub (ball_subset_closedBall hx)))) ?_ ?_
    · rw [hde]
      exact (hcd' w hwmem).differentiableAt (by norm_num)
    · intro x hx
      rw [hde, hwM]
      exact (hballV hx).2
    · intro x hx
      rw [hde, hwM]
      exact hle x (ball_subset_closedBall (hsub (sphere_subset_closedBall hx)))
  -- But `w` is an interior maximum point of `u`, so the derivative there vanishes.
  have hmax : IsLocalMax u w := by
    filter_upwards [isOpen_ball.mem_nhds hwball] with x hx
    rw [hwM]
    exact hle x (ball_subset_closedBall hx)
  rw [hde, IsLocalMax.fderiv_eq_zero hmax] at hpos
  simp at hpos

/-- **Strong maximum principle for subharmonic functions.**

Let `Ω` be an open preconnected subset of a finite-dimensional real inner product space and let
`u` be `C²` and subharmonic (`0 ≤ Δ u`) on `Ω`.  If `u` attains its maximum over `Ω` at a point
`a` of `Ω`, then `u` is constant on `Ω`.

Attaining the maximum at an interior point is essential: `Ω` may well be a bounded domain on
which `u` is nonconstant and attains its supremum only on the boundary. -/
theorem eqOn_const_of_laplacian_nonneg_of_isMaxOn (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (ha : a ∈ Ω) (hcd : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ Ω, 0 ≤ Δ u x)
    (hmax : IsMaxOn u Ω a) :
    EqOn u (fun _ => u a) Ω := by
  -- The subset of `Ω` where the maximum is attained is open, by the local step, and its
  -- complement in `Ω` is open by continuity; preconnectedness leaves no room for the latter.
  set S : Set E := {x ∈ Ω | u x = u a}
  set T : Set E := Ω ∩ u ⁻¹' Iio (u a)
  have hTopen : IsOpen T :=
    ContinuousOn.isOpen_inter_preimage
      (fun x hx => (hcd x hx).continuousAt.continuousWithinAt) hΩ isOpen_Iio
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxΩ, hxM⟩
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
    have hclosed : closedBall x (r / 2) ⊆ Ω :=
      (closedBall_subset_ball (by linarith)).trans hrsub
    have hball : ball x (r / 4) ⊆ S := by
      intro y hy
      have hyΩ : y ∈ Ω := hclosed (ball_subset_closedBall
        (ball_subset_ball (by linarith) hy))
      refine ⟨hyΩ, ?_⟩
      refine eqOn_const_of_laplacian_nonneg_of_le_closedBall (by linarith)
        (fun t ht => hcd t (hclosed ht)) (fun t ht => hlap t (hclosed ht))
        (fun t ht => isMaxOn_iff.1 hmax t (hclosed ht)) hxM y (mem_ball.2 ?_)
      have := mem_ball.1 hy
      linarith
    exact Filter.mem_of_superset (ball_mem_nhds x (by linarith)) hball
  have hcover : Ω ⊆ S ∪ T := by
    intro x hxΩ
    rcases eq_or_lt_of_le (isMaxOn_iff.1 hmax x hxΩ) with h | h
    · exact Or.inl ⟨hxΩ, h⟩
    · exact Or.inr ⟨hxΩ, h⟩
  intro x hxΩ
  by_contra hne
  obtain ⟨y, _, hyS, hyT⟩ :=
    hconn S T hSopen hTopen hcover ⟨a, ha, ha, rfl⟩
      ⟨x, hxΩ, hxΩ, lt_of_le_of_ne (isMaxOn_iff.1 hmax x hxΩ) hne⟩
  exact absurd hyS.2 hyT.2.ne

/-- **Strong maximum principle up to the boundary.**

If `u` is continuous on `closure Ω`, is `C²` and subharmonic on the open preconnected set `Ω`,
and attains its maximum over `closure Ω` at a point of `Ω`, then `u` is constant on
`closure Ω`.  This is the form used to rule out interior maxima for the Dirichlet problem on a
bounded domain. -/
theorem eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (ha : a ∈ Ω) (hcont : ContinuousOn u (closure Ω))
    (hcd : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ Ω, 0 ≤ Δ u x)
    (hmax : IsMaxOn u (closure Ω) a) :
    EqOn u (fun _ => u a) (closure Ω) := by
  have hint : EqOn u (fun _ => u a) Ω :=
    eqOn_const_of_laplacian_nonneg_of_isMaxOn hΩ hconn ha hcd hlap
      (hmax.on_subset subset_closure)
  intro x hx
  have : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  refine tendsto_nhds_unique ((hcont x hx).mono subset_closure) ?_
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with y hy using (hint hy).symm

/-- **Strong minimum principle for superharmonic functions.**

The mirror image of `TauCeti.eqOn_const_of_laplacian_nonneg_of_isMaxOn`: a `C²` superharmonic
(`Δ u ≤ 0`) function on an open preconnected set that attains its minimum over the set at one
of its points is constant there. -/
theorem eqOn_const_of_laplacian_nonpos_of_isMinOn (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (ha : a ∈ Ω) (hcd : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ Ω, Δ u x ≤ 0)
    (hmin : IsMinOn u Ω a) :
    EqOn u (fun _ => u a) Ω := by
  have h := eqOn_const_of_laplacian_nonneg_of_isMaxOn (u := -u) hΩ hconn ha
    (fun x hx => (hcd x hx).neg)
    (fun x hx => by rw [congrFun laplacian_neg x, Pi.neg_apply]; linarith [hlap x hx])
    hmin.neg
  intro x hx
  have := h hx
  simp only [Pi.neg_apply] at this
  linarith [this]

/-- **Strong minimum principle up to the boundary.**

The mirror image of `TauCeti.eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn` for
superharmonic functions. -/
theorem eqOn_const_closure_of_laplacian_nonpos_of_isMinOn (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (ha : a ∈ Ω) (hcont : ContinuousOn u (closure Ω))
    (hcd : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hlap : ∀ x ∈ Ω, Δ u x ≤ 0)
    (hmin : IsMinOn u (closure Ω) a) :
    EqOn u (fun _ => u a) (closure Ω) := by
  have h := eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn (u := -u) hΩ hconn ha hcont.neg
    (fun x hx => (hcd x hx).neg)
    (fun x hx => by rw [congrFun laplacian_neg x, Pi.neg_apply]; linarith [hlap x hx])
    hmin.neg
  intro x hx
  have := h hx
  simp only [Pi.neg_apply] at this
  linarith [this]

/-- **Strong comparison principle.**

If `u` and `v` are `C²` on an open preconnected set `Ω` with `Δ v ≤ Δ u` there, and `u ≤ v`
throughout `Ω` with equality at one point `a`, then `u = v` on all of `Ω`.

The hypothesis on the Laplacians says exactly that `u - v` is subharmonic; the case of a
subharmonic `u` dominated by a superharmonic `v` is the instance `0 ≤ Δ u` and `Δ v ≤ 0`. -/
theorem eqOn_of_laplacian_le_of_le_of_eq (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (ha : a ∈ Ω)
    (hcdu : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hcdv : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hlap : ∀ x ∈ Ω, Δ v x ≤ Δ u x)
    (hle : ∀ x ∈ Ω, u x ≤ v x) (heq : u a = v a) :
    EqOn u v Ω := by
  have hmax : IsMaxOn (u - v) Ω a := by
    refine isMaxOn_iff.2 fun x hx => ?_
    simp only [Pi.sub_apply, heq, sub_self]
    linarith [hle x hx]
  have h := eqOn_const_of_laplacian_nonneg_of_isMaxOn (u := u - v) hΩ hconn ha
    (fun x hx => (hcdu x hx).sub (hcdv x hx))
    (fun x hx => by
      rw [(hcdu x hx).laplacian_sub (hcdv x hx)]
      linarith [hlap x hx])
    hmax
  intro x hx
  have hx' := h hx
  simp only [Pi.sub_apply, heq, sub_self] at hx'
  linarith [hx']

/-- **Strong comparison principle up to the boundary.**

The counterpart of `TauCeti.eqOn_of_laplacian_le_of_le_of_eq` for functions continuous on
`closure Ω`: if `u ≤ v` on `closure Ω` and the two agree at a point of `Ω`, then they agree on
all of `closure Ω`. -/
theorem eqOn_closure_of_laplacian_le_of_le_of_eq (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (ha : a ∈ Ω) (hcontu : ContinuousOn u (closure Ω)) (hcontv : ContinuousOn v (closure Ω))
    (hcdu : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x) (hcdv : ∀ x ∈ Ω, ContDiffAt ℝ 2 v x)
    (hlap : ∀ x ∈ Ω, Δ v x ≤ Δ u x)
    (hle : ∀ x ∈ closure Ω, u x ≤ v x) (heq : u a = v a) :
    EqOn u v (closure Ω) := by
  have hmax : IsMaxOn (u - v) (closure Ω) a := by
    refine isMaxOn_iff.2 fun x hx => ?_
    simp only [Pi.sub_apply, heq, sub_self]
    linarith [hle x hx]
  have h := eqOn_const_closure_of_laplacian_nonneg_of_isMaxOn (u := u - v) hΩ hconn ha
    (hcontu.sub hcontv)
    (fun x hx => (hcdu x hx).sub (hcdv x hx))
    (fun x hx => by
      rw [(hcdu x hx).laplacian_sub (hcdv x hx)]
      linarith [hlap x hx])
    hmax
  intro x hx
  have hx' := h hx
  simp only [Pi.sub_apply, heq, sub_self] at hx'
  linarith [hx']

end TauCeti

end
