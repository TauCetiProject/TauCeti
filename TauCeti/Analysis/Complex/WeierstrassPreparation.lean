/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ExtractZeros
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Polynomial.Order
public import TauCeti.Analysis.Polynomial.RootSum
public import TauCeti.Analysis.Polynomial.SimpleRoots.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# The Weierstrass preparation theorem for holomorphic germs

Let `f (z, w)` be holomorphic near `(z₀, 0)`, with `z` in a finite-dimensional complex space and
`w` a distinguished complex variable. If `w ↦ f (z₀, w)` vanishes to finite order `d` at `0`, then
near `(z₀, 0)`

```text
f (z, w) = u (z, w) * (w ^ d + a_{d-1}(z) * w ^ (d-1) + ⋯ + a_0(z)),
```

with `u` holomorphic and `u (z₀, 0) ≠ 0`, and with each `a_i` holomorphic at `z₀` and vanishing
there. The germs of `u` and of the `a_i` are uniquely determined by `f`. This reduces the local
study of zero sets of holomorphic functions, and through complexification of real analytic
functions, to polynomials in one variable with analytic coefficients.

The proof is the classical contour argument. For `z` near `z₀`, the function `f (z, ·)` has no zero
on a fixed circle `C(0, R)`, so the zeros in the disc are the roots of a monic polynomial `P z`. The
power sums of these roots are contour integrals of `w ^ j * ∂f/∂w / f`, which depend analytically
on `z`, and Newton's identities pass this on to the coefficients of `P z`. The quotient `f / P` is
recovered by the Cauchy integral formula over the same circle, and this formula shows that it is
jointly analytic.

## Main definitions

* `TauCeti.IsWeierstrassFactorizationAt f z₀ a u`: the germ of `f` at `(z₀, 0)` is the unit `u`
  times the monic polynomial with lower coefficients `a z`, the *Weierstrass polynomial* of `f`.

## Main results

* `AnalyticAt.exists_isWeierstrassFactorizationAt`: the **Weierstrass preparation theorem**.
* `TauCeti.IsWeierstrassFactorizationAt.analyticOrderAt_eq`: the degree of the Weierstrass
  polynomial is the order of `f (z₀, ·)` at `0`.
* `TauCeti.IsWeierstrassFactorizationAt.unique`: the factorization is unique, as a pair of germs.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter II, Section B.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Theorem 6.1.1.
-/

public section

open Filter Metric Polynomial Set Topology TauCeti.Polynomial
open scoped Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

namespace TauCeti

/-- The germ of `f` at `(z₀, 0)` *has the Weierstrass factorization* `u * P`: `P z` is the monic
polynomial of degree `d` in the distinguished variable with lower coefficients `a z`, which are
analytic at `z₀` and vanish there, and `u` is analytic and nonzero at `(z₀, 0)`. This is the
analytic counterpart of Mathlib's `PowerSeries.IsWeierstrassFactorizationAt`. -/
structure IsWeierstrassFactorizationAt {d : ℕ} (f : V × ℂ → ℂ) (z₀ : V) (a : V → Fin d → ℂ)
    (u : V × ℂ → ℂ) : Prop where
  /-- The lower coefficients of the Weierstrass polynomial are analytic at `z₀`. -/
  analyticAt_coeff : AnalyticAt ℂ a z₀
  /-- The lower coefficients of the Weierstrass polynomial vanish at `z₀`. -/
  coeff_center : a z₀ = 0
  /-- The unit factor is analytic at `(z₀, 0)`. -/
  analyticAt_unit : AnalyticAt ℂ u (z₀, 0)
  /-- The unit factor does not vanish at `(z₀, 0)`. -/
  unit_center_ne_zero : u (z₀, 0) ≠ 0
  /-- Near `(z₀, 0)`, `f` is the unit times the Weierstrass polynomial. -/
  eventuallyEq : f =ᶠ[𝓝 (z₀, 0)] fun p => u p * (monicOfCoeff (a p.1)).eval p.2

section Existence

variable {f : V × ℂ → ℂ} {z₀ : V} {R : ℝ}

/-- For `f` of finite slice order at `0`, a radius `R` such that `f (z₀, ·)` vanishes on the closed
disc only at `0`, and such that for `z` near `z₀` the function `f (z, ·)` is analytic on the closed
disc without zeros on its boundary. -/
private theorem exists_radius {d : ℕ} (hf : AnalyticAt ℂ f (z₀, 0))
    (hd : analyticOrderAt (fun w => f (z₀, w)) 0 = d) :
    ∃ R : ℝ, 0 < R ∧ (∀ w ∈ closedBall (0 : ℂ) R, f (z₀, w) = 0 → w = 0) ∧
      ∀ᶠ z in 𝓝 z₀, (∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (z, w)) ∧
        ∀ w ∈ sphere (0 : ℂ) R, f (z, w) ≠ 0 := by
  have hne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), f (z₀, w) ≠ 0 :=
    hf.curry_right.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
      ENat.natCast_ne_top d (hd ▸ analyticOrderAt_eq_top.2 h)
  have han : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ f (z₀, w) :=
    (Continuous.prodMk_right z₀).continuousAt.eventually (f := fun w : ℂ => (z₀, w))
      hf.eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (han.and (eventually_nhdsWithin_iff.1 hne))
  have hR : 0 < ε / 2 := half_pos hε
  have hsub : closedBall (0 : ℂ) (ε / 2) ⊆ ball 0 ε := closedBall_subset_ball (half_lt_self hε)
  refine ⟨ε / 2, hR, fun w hw h0 => by_contra fun hw0 => (hball w (hsub hw)).2 hw0 h0, ?_⟩
  have hsphere : ∀ w ∈ sphere (0 : ℂ) (ε / 2), f (z₀, w) ≠ 0 := fun w hw =>
    (hball w (hsub (sphere_subset_closedBall hw))).2 (ne_of_mem_sphere hw hR.ne')
  exact (isCompact_closedBall (0 : ℂ) _ |>.eventually_forall_of_forall_eventually fun w hw =>
      (hball w (hsub hw)).1.eventually_analyticAt).and
    (isCompact_sphere (0 : ℂ) _ |>.eventually_forall_of_forall_eventually fun w hw =>
      (hball w (hsub (sphere_subset_closedBall hw))).1.continuousAt.eventually_ne (hsphere w hw))

/-- The family of Weierstrass polynomials: for `z` near `z₀`, the zeros of `f (z, ·)` in the disc
of radius `R` are the roots of a monic polynomial `P z`, and the elementary symmetric functions and
the power sums of these roots are analytic at `z₀`. -/
private theorem exists_family [FiniteDimensional ℂ V] (hR : 0 < R)
    (hU : ∀ᶠ z in 𝓝 z₀, (∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (z, w)) ∧
      ∀ w ∈ sphere (0 : ℂ) R, f (z, w) ≠ 0) :
    ∃ (P : V → ℂ[X]) (H : V → ℂ → ℂ),
      (∀ᶠ z in 𝓝 z₀, (P z).Monic ∧ (∀ ζ, (P z).IsRoot ζ → ζ ∈ ball (0 : ℂ) R) ∧
        AnalyticOnNhd ℂ (H z) (closedBall 0 R) ∧ (∀ w ∈ closedBall (0 : ℂ) R, H z w ≠ 0) ∧
        ∀ w, f (z, w) = (P z).eval w * H z w) ∧
      ∀ k, AnalyticAt ℂ (fun z => (P z).roots.esymm k) z₀ ∧
        AnalyticAt ℂ (fun z => (((P z).roots.map (· ^ k)).sum : ℂ)) z₀ := by
  have key (z : V) (hz : (∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ f (z, w)) ∧
      ∀ w ∈ sphere (0 : ℂ) R, f (z, w) ≠ 0) :=
    AnalyticOnNhd.exists_monic_eval_mul_eq (g := fun w => f (z, w)) hR
      (fun w hw => (hz.1 w hw).curry_right) hz.2
  choose! P H hP using key
  have hzero := hU.self_of_nhds
  have hint (j : ℕ) : ∀ᶠ z in 𝓝 z₀, (((P z).roots.map (· ^ j)).sum : ℂ) =
      (2 * π * Complex.I)⁻¹ *
        ∮ w in C((0 : ℂ), R), w ^ j * (fderiv ℂ f (z, w) (0, 1) / f (z, w)) := by
    filter_upwards [hU] with z hz
    obtain ⟨-, hroots, hH, hH0, heq⟩ := hP z hz
    have hcongr : EqOn (fun w => w ^ j * (deriv (fun w => f (z, w)) w / f (z, w)))
        (fun w => w ^ j * (fderiv ℂ f (z, w) (0, 1) / f (z, w))) (sphere (0 : ℂ) R) :=
      fun w hw => by
        simp only [deriv_slice_right (hz.1 w (sphere_subset_closedBall hw)).differentiableAt]
    rw [← circleIntegral.integral_congr hR.le hcongr,
      circleIntegral_mul_deriv_div_eq_sum_roots (φ := fun w => w ^ j) hR hroots hH hH0
        (fun w _ => analyticAt_id.pow j) heq,
      inv_mul_cancel_left₀ (by simp [Real.pi_ne_zero])]
  have hsph : sphere (0 : ℂ) |R| = sphere 0 R := by rw [abs_of_pos hR]
  have hsum (j : ℕ) : AnalyticAt ℂ (fun z => (((P z).roots.map (· ^ j)).sum : ℂ)) z₀ :=
    (analyticAt_const.mul (analyticAt_circleIntegral_mul_fderiv_div (c := 0) (R := R)
      (φ := fun w => w ^ j) (hsph ▸ fun w hw => hzero.1 w (sphere_subset_closedBall hw))
      (hsph ▸ hzero.2) fun w _ => analyticAt_id.pow j)).congr ((hint j).mono fun _ hz => hz.symm)
  exact ⟨P, H, hU.mono hP, fun k =>
    ⟨analyticAt_esymm_of_forall_analyticAt_sum_map_pow k fun j _ _ => hsum j, hsum k⟩⟩

/-- **The Weierstrass preparation theorem.** If `f` is holomorphic near `(z₀, 0)`, with `z₀` in a
finite-dimensional space, and `f (z₀, ·)` vanishes to finite order `d` at `0`, then the germ of `f`
at `(z₀, 0)` is a unit times a monic polynomial of degree `d` in the second variable, whose lower
coefficients are analytic at `z₀` and vanish there. -/
theorem _root_.AnalyticAt.exists_isWeierstrassFactorizationAt [FiniteDimensional ℂ V] {d : ℕ}
    (hf : AnalyticAt ℂ f (z₀, 0)) (hd : analyticOrderAt (fun w => f (z₀, w)) 0 = d) :
    ∃ (a : V → Fin d → ℂ) (u : V × ℂ → ℂ), IsWeierstrassFactorizationAt f z₀ a u := by
  obtain ⟨R, hR, hzero, hU⟩ := exists_radius hf hd
  obtain ⟨P, H, hP, hsym⟩ := exists_family hR hU
  obtain ⟨hPm, hProots, hH, hH0, heq⟩ := hP.self_of_nhds
  have hsph (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) := sphere_subset_closedBall hw
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hcenter : P z₀ = X ^ d := by
    simpa using hPm.eq_X_sub_C_pow_of_analyticOrderAt_eq
      (fun ζ hζ => hzero ζ (ball_subset_closedBall (hProots ζ hζ))
        (by rw [heq, hζ.eq_zero, zero_mul])) (hH 0 h0) (hH0 0 h0) heq hd
  have hdeg : ∀ᶠ z in 𝓝 z₀, (P z).natDegree = d := by
    have hcont : ContinuousAt (fun z => ((P z).natDegree : ℝ)) z₀ := by
      refine (Complex.continuous_re.continuousAt.comp (hsym 0).2.continuousAt).congr
        (.of_forall fun z => ?_)
      simp [(IsAlgClosed.splits (P z)).natDegree_eq_card_roots]
    have hnat : ContinuousAt (fun z => (P z).natDegree) z₀ :=
      Nat.isClosedEmbedding_coe_real.isInducing.continuousAt_iff.2 hcont
    exact hnat.eventually (p := (· = d)) (by simp [hcenter, nhds_discrete])
  set a : V → Fin d → ℂ := fun z i => (P z).coeff i with ha_def
  have hmon : ∀ᶠ z in 𝓝 z₀, monicOfCoeff (a z) = P z := by
    filter_upwards [hP, hdeg] with z hz hz'
    exact monicOfCoeff_coeff hz.1 hz'
  have ha : AnalyticAt ℂ a z₀ :=
    analyticAt_coeff_of_forall_analyticAt_esymm_roots (hP.mono fun _ h => h.1) hdeg
      fun k => (hsym k).1
  have hcenter' : monicOfCoeff (a z₀) = X ^ d := hmon.self_of_nhds.trans hcenter
  have ha0 : a z₀ = 0 := funext fun i => by
    simp [ha_def, hcenter, coeff_X_pow, i.2.ne]
  set u : V × ℂ → ℂ := fun q => (2 * π * Complex.I)⁻¹ • ∮ w in C((0 : ℂ), R), (w - q.2)⁻¹ •
    (f (q.1, w) / (monicOfCoeff (a q.1)).eval w) with hu_def
  have huH : ∀ᶠ z in 𝓝 z₀, ∀ w ∈ ball (0 : ℂ) R, u (z, w) = H z w := by
    filter_upwards [hP, hmon, hU] with z hz hmz hUz w hw
    simp only [hu_def, hmz]
    exact circleIntegral_sub_inv_smul_div_eq (p := fun ξ => (P z).eval ξ) hR hz.2.2.1
      (fun ξ _ => hz.2.2.2.2 ξ) (fun ξ hξ h0 => hUz.2 ξ hξ (by rw [hz.2.2.2.2, h0, zero_mul])) hw
  have hP0 : ∀ w ∈ sphere (0 : ℂ) R, (monicOfCoeff (a z₀)).eval w ≠ 0 := fun w hw => by
    simpa only [hcenter', eval_pow, eval_X] using pow_ne_zero d (ne_of_mem_sphere hw hR.ne')
  have hu : AnalyticAt ℂ u (z₀, 0) := by
    refine analyticAt_const.fun_smul (analyticAt_circleIntegral_sub_inv_smul
      (f := fun q : V × ℂ => f q / (monicOfCoeff (a q.1)).eval q.2) (fun w hw => ?_)
      (by simp [abs_of_pos hR, hR.ne]))
    rw [abs_of_pos hR] at hw
    exact (hU.self_of_nhds.1 w (hsph w hw)).div
      ((ha.comp_of_eq analyticAt_fst rfl).eval_monicOfCoeff analyticAt_snd) (hP0 w hw)
  refine ⟨a, u, ha, ha0, hu, ?_, ?_⟩
  · rw [huH.self_of_nhds 0 (mem_ball_self hR)]
    exact hH0 0 h0
  · filter_upwards [(huH.and (hP.and hmon)).prod_nhds (ball_mem_nhds (0 : ℂ) hR)] with q hq
    obtain ⟨⟨hu, hPq, hm⟩, hw⟩ := hq
    rw [hu _ hw, hm, hPq.2.2.2.2 q.2, mul_comm]

end Existence

namespace IsWeierstrassFactorizationAt

variable {f : V × ℂ → ℂ} {z₀ : V} {d : ℕ} {a : V → Fin d → ℂ} {u : V × ℂ → ℂ}

/-- A germ with a Weierstrass factorization is analytic. -/
protected theorem analyticAt (h : IsWeierstrassFactorizationAt f z₀ a u) :
    AnalyticAt ℂ f (z₀, 0) :=
  (h.analyticAt_unit.mul ((h.analyticAt_coeff.comp_of_eq analyticAt_fst rfl).eval_monicOfCoeff
    analyticAt_snd)).congr h.eventuallyEq.symm

/-- The degree of the Weierstrass polynomial is the order of `f (z₀, ·)` at `0`. -/
theorem analyticOrderAt_eq (h : IsWeierstrassFactorizationAt f z₀ a u) :
    analyticOrderAt (fun w => f (z₀, w)) 0 = d := by
  have hslice : ∀ᶠ w in 𝓝 (0 : ℂ), f (z₀, w) = u (z₀, w) * (monicOfCoeff (a z₀)).eval w :=
    (Continuous.prodMk_right z₀).continuousAt.eventually (f := fun w : ℂ => (z₀, w))
      h.eventuallyEq
  refine h.analyticAt.curry_right.analyticOrderAt_eq_natCast.2 ⟨fun w => u (z₀, w),
    h.analyticAt_unit.curry_right, h.unit_center_ne_zero, hslice.mono fun w hw => ?_⟩
  simp [hw, h.coeff_center, eval_monicOfCoeff, mul_comm]

/-- **Uniqueness of the Weierstrass factorization.** The germs at `z₀` of the coefficients of the
Weierstrass polynomial and the germ at `(z₀, 0)` of the unit are determined by `f`. -/
theorem unique {a₁ a₂ : V → Fin d → ℂ} {u₁ u₂ : V × ℂ → ℂ}
    (h₁ : IsWeierstrassFactorizationAt f z₀ a₁ u₁)
    (h₂ : IsWeierstrassFactorizationAt f z₀ a₂ u₂) :
    a₁ =ᶠ[𝓝 z₀] a₂ ∧ u₁ =ᶠ[𝓝 (z₀, 0)] u₂ := by
  have hunit {u : V × ℂ → ℂ} (hu : AnalyticAt ℂ u (z₀, 0)) (hu0 : u (z₀, 0) ≠ 0) :
      ∀ᶠ p in 𝓝 (z₀, (0 : ℂ)), AnalyticAt ℂ u p ∧ u p ≠ 0 :=
    hu.eventually_analyticAt.and (hu.continuousAt.eventually_ne hu0)
  have hG := ((hunit h₁.analyticAt_unit h₁.unit_center_ne_zero).and
    (hunit h₂.analyticAt_unit h₂.unit_center_ne_zero)).and
    (h₁.eventuallyEq.symm.trans h₂.eventuallyEq)
  obtain ⟨pa, hpa, pb, hpb, hG⟩ :=
    eventually_prod_iff.1 (nhds_prod_eq (x := z₀) (y := (0 : ℂ)) ▸ hG)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hpb
  have hroots {a : V → Fin d → ℂ} (ha : ContinuousAt a z₀) (ha0 : a z₀ = 0) :
      ∀ᶠ z in 𝓝 z₀, ∀ ζ, (monicOfCoeff (a z)).IsRoot ζ → ζ ∈ ball (0 : ℂ) ε := by
    have hcenter : (monicOfCoeff (a z₀)).roots = Multiset.replicate d 0 := by
      have hX : monicOfCoeff (a z₀) = X ^ d :=
        Polynomial.funext fun w => by simp [ha0, eval_monicOfCoeff]
      rw [hX, roots_pow, roots_X, Multiset.nsmul_singleton]
    filter_upwards [eventually_rel_roots_norm_sub_lt (F := fun z => monicOfCoeff (a z)) (x₀ := z₀)
      (d := d) (fun i _ => (continuous_coeff_monicOfCoeff i).continuousAt.comp ha)
      (.of_forall fun z => by
        rw [degree_eq_natDegree (monic_monicOfCoeff _).ne_zero, natDegree_monicOfCoeff]) hε]
      with z hz ζ hζ
    rw [hcenter, Multiset.rel_replicate_left] at hz
    simpa [mem_ball, dist_eq_norm] using
      hz.2 ζ ((mem_roots (monic_monicOfCoeff _).ne_zero).2 hζ)
  have hcoeff : ∀ᶠ z in 𝓝 z₀, pa z ∧ a₁ z = a₂ z := by
    filter_upwards [hpa, hroots h₁.analyticAt_coeff.continuousAt h₁.coeff_center,
      hroots h₂.analyticAt_coeff.continuousAt h₂.coeff_center] with z hz hr₁ hr₂
    have hgood (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) := hG hz (hball w hw)
    exact ⟨hz, (monicOfCoeff_inj _ _).1 <| (monic_monicOfCoeff _).eq_of_forall_mem_mul_eval_eq
      (monic_monicOfCoeff _) (v₁ := fun w => u₁ (z, w)) (v₂ := fun w => u₂ (z, w)) isOpen_ball
      hr₁ hr₂ (fun w hw => ⟨(hgood w hw).1.1.1.curry_right, (hgood w hw).1.1.2⟩)
      (fun w hw => ⟨(hgood w hw).1.2.1.curry_right, (hgood w hw).1.2.2⟩)
      fun w hw => (hgood w hw).2⟩
  refine ⟨hcoeff.mono fun _ h => h.2, ?_⟩
  filter_upwards [hcoeff.prod_nhds (ball_mem_nhds (0 : ℂ) hε)] with q hq
  obtain ⟨z, w⟩ := q
  obtain ⟨⟨hz, hc⟩, hw⟩ := hq
  have hgood (t : ℂ) (ht : t ∈ ball (0 : ℂ) ε) := hG hz (hball t ht)
  exact eq_of_eventually_mul_eval_eq (p := monicOfCoeff (a₂ z)) (monic_monicOfCoeff _).ne_zero
    (v₁ := fun t => u₁ (z, t)) (v₂ := fun t => u₂ (z, t))
    (hgood w hw).1.1.1.curry_right.continuousAt
    (hgood w hw).1.2.1.curry_right.continuousAt
    (eventually_of_mem (isOpen_ball.mem_nhds hw) fun t ht => by
      simpa [hc] using (hgood t ht).2)

end IsWeierstrassFactorizationAt

end TauCeti
