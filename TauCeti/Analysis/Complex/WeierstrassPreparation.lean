/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ExtractZeros
public import TauCeti.Analysis.Analytic.IsolatedZeros
public import TauCeti.Analysis.Analytic.Multiset
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Polynomial.Monic.OfCoeff
public import TauCeti.Analysis.Polynomial.Order
public import TauCeti.Analysis.Polynomial.RootSum
public import TauCeti.Analysis.Polynomial.SimpleRoots.Basic

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

* `AnalyticOnNhd.exists_monic_eval_mul_eq`: a function holomorphic on a closed disc without zeros
  on its boundary is a monic polynomial with roots in the open disc times a zero-free function.
* `TauCeti.circleIntegral_mul_deriv_div_eq_sum_roots`: the argument principle on a disc, weighted
  by a holomorphic function.
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

/-- A function holomorphic on a closed disc, without zeros on the boundary circle, is a monic
polynomial with all its roots in the open disc times a function which is holomorphic and zero-free
on the closed disc. -/
theorem AnalyticOnNhd.exists_monic_eval_mul_eq {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hne : ∀ w ∈ sphere c R, g w ≠ 0) :
    ∃ (p : ℂ[X]) (h : ℂ → ℂ), p.Monic ∧ (∀ ζ, p.IsRoot ζ → ζ ∈ ball c R) ∧
      AnalyticOnNhd ℂ h (closedBall c R) ∧ (∀ w ∈ closedBall c R, h w ≠ 0) ∧
      ∀ w, g w = p.eval w * h w := by
  classical
  have hconn : IsPreconnected (closedBall c R) := (convex_closedBall c R).isPreconnected
  have hx₀ : c + R ∈ sphere c R := by simp [abs_of_pos hR]
  have hx₀' : c + R ∈ closedBall c R := sphere_subset_closedBall hx₀
  have hord : ∀ x ∈ closedBall c R, analyticOrderAt g x ≠ ⊤ := fun x hx =>
    hg.analyticOrderAt_ne_top_of_isPreconnected hconn hx₀' hx
      (by simp [(hg _ hx₀').analyticOrderAt_eq_zero.2 (hne _ hx₀)])
  have hfin := hg.finite_setOf_mem_and_eq_zero_of_isCompact hconn hx₀' (hne _ hx₀)
    (isCompact_closedBall c R) subset_rfl
  set S := hfin.toFinset
  have hS (x : ℂ) : x ∈ S ↔ x ∈ closedBall c R ∧ g x = 0 := by simp [S]
  obtain ⟨h, hh, heq⟩ := hg.exists_eq_prod_pow_smul S (analyticOrderNatAt g) fun x hx =>
    (Nat.cast_analyticOrderNatAt (hord x ((hS x).1 hx).1)).le
  set p : ℂ[X] := ∏ x ∈ S, (X - C x) ^ analyticOrderNatAt g x
  have heval (w : ℂ) : p.eval w = ∏ x ∈ S, (w - x) ^ analyticOrderNatAt g x := by
    simp [p, eval_prod]
  have hgp (w : ℂ) : g w = p.eval w * h w := by rw [heval, heq w, smul_eq_mul]
  refine ⟨p, h, monic_prod_of_monic _ _ fun x _ => (monic_X_sub_C x).pow _, fun ζ hζ => ?_, hh,
    fun w hw hw0 => ?_, hgp⟩
  · have hgζ : g ζ = 0 := by rw [hgp, hζ.eq_zero, zero_mul]
    obtain ⟨x, hx, hxζ⟩ := Finset.prod_eq_zero_iff.1 ((heval ζ).symm.trans hζ.eq_zero)
    have hζx : ζ = x := sub_eq_zero.1 (eq_zero_of_pow_eq_zero hxζ)
    have hζ' : ζ ∈ closedBall c R := hζx ▸ ((hS x).1 hx).1
    exact mem_ball.2 ((mem_closedBall.1 hζ').lt_of_ne fun hsph => hne ζ (mem_sphere.2 hsph) hgζ)
  · have hgw : g w = 0 := by rw [hgp, hw0, mul_zero]
    have hwS : w ∈ S := (hS w).2 ⟨hw, hgw⟩
    set q : ℂ[X] := ∏ x ∈ S.erase w, (X - C x) ^ analyticOrderNatAt g x
    have hp : p = (X - C w) ^ analyticOrderNatAt g w * q := (Finset.mul_prod_erase S _ hwS).symm
    have hq : q.eval w ≠ 0 := by
      simp only [q, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      exact Finset.prod_ne_zero_iff.2 fun x hx =>
        pow_ne_zero _ (sub_ne_zero.2 (Finset.ne_of_mem_erase hx).symm)
    have hpow : AnalyticAt ℂ (fun z => (z - w) ^ analyticOrderNatAt g w) w := by fun_prop
    have hr : AnalyticAt ℂ (fun z => q.eval z * h z) w :=
      (AnalyticOnNhd.eval_polynomial q w (mem_univ w)).mul (hh w hw)
    have hgfun : g = (fun z => (z - w) ^ analyticOrderNatAt g w) * fun z => q.eval z * h z := by
      funext z
      simp only [hgp z, hp, Pi.mul_apply, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      ring
    have hpowOrd : analyticOrderAt (fun z => (z - w) ^ analyticOrderNatAt g w) w =
        analyticOrderNatAt g w :=
      hpow.analyticOrderAt_eq_natCast.2
        ⟨fun _ => 1, analyticAt_const, one_ne_zero, by simp⟩
    have hrOrd : analyticOrderAt (fun z => q.eval z * h z) w ≠ 0 :=
      hr.analyticOrderAt_ne_zero.2 (by simp [hw0])
    have hgOrd := Nat.cast_analyticOrderNatAt (hord w hw)
    rw [hgfun, analyticOrderAt_mul hpow hr, hpowOrd, ← hgfun] at hgOrd
    exact hrOrd (by simpa using hgOrd.symm)

namespace TauCeti

/-- **The argument principle on a disc, weighted by a holomorphic function.** If `g = p * h`, with
`h` holomorphic and zero-free on a closed disc and every root of `p` in the open disc, then
integrating `φ`, holomorphic on the closed disc, against the logarithmic derivative of `g` over the
circle gives `2πi` times the sum of the values of `φ` at the roots of `p`, counted with
multiplicity. -/
theorem circleIntegral_mul_deriv_div_eq_sum_roots {g h φ : ℂ → ℂ} {p : ℂ[X]} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hroots : ∀ ζ, p.IsRoot ζ → ζ ∈ ball c R)
    (hh : AnalyticOnNhd ℂ h (closedBall c R)) (hh0 : ∀ w ∈ closedBall c R, h w ≠ 0)
    (hφ : AnalyticOnNhd ℂ φ (closedBall c R)) (hg : ∀ w, g w = p.eval w * h w) :
    ∮ w in C(c, R), φ w * (deriv g w / g w) =
      2 * π * Complex.I * (p.roots.map φ).sum := by
  classical
  have hsph {w : ℂ} (hw : w ∈ sphere c R) : w ∈ closedBall c R := sphere_subset_closedBall hw
  have hp {w : ℂ} (hw : w ∈ sphere c R) : p.eval w ≠ 0 := fun h0 =>
    (mem_ball.1 (hroots w h0)).ne (mem_sphere.1 hw)
  have hgfun : g = fun w => p.eval w * h w := funext hg
  have hlog : EqOn (fun w => φ w * (deriv g w / g w))
      (fun w => φ w * (p.derivative.eval w / p.eval w) + φ w * (deriv h w / h w))
      (sphere c R) := by
    intro w hw
    have hderiv : deriv g w = p.derivative.eval w * h w + p.eval w * deriv h w := by
      rw [hgfun, deriv_fun_mul p.differentiable.differentiableAt
        (hh w (hsph hw)).differentiableAt, Polynomial.deriv]
    have hh' := hh0 w (hsph hw)
    have hp' := hp hw
    simp only [hderiv, hg w]
    field_simp
  have hquot : AnalyticOnNhd ℂ (fun w => φ w * (deriv h w / h w)) (closedBall c R) :=
    hφ.mul (hh.deriv.div hh hh0)
  have hweight : DiffContOnCl ℂ φ (ball c R) := hφ.differentiableOn.diffContOnCl_ball subset_rfl
  have hint₁ : CircleIntegrable (fun w => φ w * (p.derivative.eval w / p.eval w)) c R :=
    ContinuousOn.circleIntegrable hR.le <| (hφ.continuousOn.mono fun _ => hsph).mul <|
      p.derivative.continuous.continuousOn.div p.continuous.continuousOn fun _ hw => hp hw
  have hint₂ : CircleIntegrable (fun w => φ w * (deriv h w / h w)) c R :=
    ContinuousOn.circleIntegrable hR.le (hquot.continuousOn.mono fun _ => hsph)
  rw [circleIntegral.integral_congr hR.le hlog, circleIntegral.integral_add hint₁ hint₂,
    p.circleIntegral_mul_derivative_div_eval hR hweight fun z hz hzs =>
      (mem_ball.1 (hroots z (isRoot_of_mem_roots hz))).ne (mem_sphere.1 hzs),
    (hquot.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le, add_zero,
    Multiset.filter_eq_self.2 fun z hz => hroots z (isRoot_of_mem_roots hz)]

/-- The partial derivative of `f` in the second variable is the derivative of its slice. -/
private theorem deriv_slice {f : V × ℂ → ℂ} {z : V} {w : ℂ} (hf : AnalyticAt ℂ f (z, w)) :
    deriv (fun w => f (z, w)) w = fderiv ℂ f (z, w) (0, 1) := by
  have hslice : HasDerivAt (fun w : ℂ => (z, w)) ((0 : V), (1 : ℂ)) w :=
    (hasDerivAt_const w z).prodMk (hasDerivAt_id w)
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt w hslice).deriv

/-- The polynomial evaluation map, composed with a coefficient family analytic at `z`, is jointly
analytic. -/
private theorem analyticAt_eval_comp {d : ℕ} {a : V → Fin d → ℂ} {z : V} (ha : AnalyticAt ℂ a z)
    (w : ℂ) : AnalyticAt ℂ (fun p : V × ℂ => (monicOfCoeff (a p.1)).eval p.2) (z, w) :=
  AnalyticAt.comp_of_eq (g := fun q : (Fin d → ℂ) × ℂ => (monicOfCoeff q.1).eval q.2)
    (f := fun p : V × ℂ => (a p.1, p.2)) (analyticAt_eval_monicOfCoeff (a z, w))
    ((ha.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) rfl

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

/-- If `g = p * h` with `p` monic with no root but `0` and `h` a unit at `0`, and `g` has order `d`
at `0`, then `p = X ^ d`. -/
private theorem eq_X_pow_of_eval_mul_eq {g h : ℂ → ℂ} {p : ℂ[X]} {d : ℕ} (hp : p.Monic)
    (hroot : ∀ ζ, p.IsRoot ζ → ζ = 0) (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (hg : ∀ w, g w = p.eval w * h w) (hd : analyticOrderAt g 0 = d) : p = X ^ d := by
  have hgfun : (fun w => p.eval w) * h = g := funext fun w => (hg w).symm
  have hord := analyticOrderAt_mul (AnalyticOnNhd.eval_polynomial p 0 (mem_univ 0)) hh
  rw [hgfun, hd, hh.analyticOrderAt_eq_zero.2 hh0, add_zero,
    analyticOrderAt_eval hp.ne_zero] at hord
  have hmul : p.rootMultiplicity 0 = d := by exact_mod_cast hord.symm
  have hroots : p.roots = Multiset.replicate d 0 := by
    refine Multiset.eq_replicate.2 ⟨?_, fun b hb => hroot b (isRoot_of_mem_roots hb)⟩
    rw [← hmul, ← count_roots]
    exact (Multiset.count_eq_card.2 fun x hx => (hroot x (isRoot_of_mem_roots hx)).symm).symm
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp, hroots]
  simp

/-- The Cauchy integral formula recovers the quotient `h` of `g = p * h` from its boundary values
`g / p`. -/
private theorem circleIntegral_sub_inv_smul_div_eq {g h : ℂ → ℂ} {p : ℂ[X]} {R : ℝ} {w : ℂ}
    (hR : 0 < R) (hh : AnalyticOnNhd ℂ h (closedBall 0 R)) (hg : ∀ w, g w = p.eval w * h w)
    (hne : ∀ ξ ∈ sphere (0 : ℂ) R, g ξ ≠ 0) (hw : w ∈ ball (0 : ℂ) R) :
    (2 * π * Complex.I)⁻¹ • ∮ ξ in C((0 : ℂ), R), (ξ - w)⁻¹ • (g ξ / p.eval ξ) = h w := by
  have hcongr : EqOn (fun ξ => (ξ - w)⁻¹ • (g ξ / p.eval ξ)) (fun ξ => (ξ - w)⁻¹ • h ξ)
      (sphere (0 : ℂ) R) := fun ξ hξ => by
    have hp : p.eval ξ ≠ 0 := fun h0 => hne ξ hξ (by rw [hg, h0, zero_mul])
    simp only [hg ξ, mul_div_cancel_left₀ _ hp]
  rw [circleIntegral.integral_congr hR.le hcongr]
  exact (hh.differentiableOn.diffContOnCl_ball subset_rfl
    ).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- The contour integrals computing the power sums of the zeros of `f (z, ·)` are analytic in
`z`. -/
private theorem analyticAt_circleIntegral_pow_mul_div [FiniteDimensional ℂ V] (hR : 0 < R)
    (hf : ∀ w ∈ sphere (0 : ℂ) R, AnalyticAt ℂ f (z₀, w))
    (hf0 : ∀ w ∈ sphere (0 : ℂ) R, f (z₀, w) ≠ 0) (j : ℕ) :
    AnalyticAt ℂ
      (fun z => ∮ w in C((0 : ℂ), R), w ^ j * (fderiv ℂ f (z, w) (0, 1) / f (z, w))) z₀ := by
  refine analyticAt_circleIntegral (f := fun q : V × ℂ => q.2 ^ j * (fderiv ℂ f q (0, 1) / f q))
    fun w hw => ?_
  rw [abs_of_pos hR] at hw
  have hderiv : AnalyticAt ℂ (fun q : V × ℂ => fderiv ℂ f q (0, 1)) (z₀, w) :=
    (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : V × ℂ)).analyticAt _ |>.comp (hf w hw).fderiv
  exact (analyticAt_snd.pow j).mul (hderiv.div (hf w hw) (hf0 w hw))

/-- The Cauchy integral of `f / P` over a circle on which `f / P` is analytic is jointly analytic
in the parameter and in the evaluation point. -/
private theorem analyticAt_circleIntegral_sub_inv_smul_div [FiniteDimensional ℂ V] {d : ℕ}
    {a : V → Fin d → ℂ} (hR : 0 < R) (hf : ∀ w ∈ sphere (0 : ℂ) R, AnalyticAt ℂ f (z₀, w))
    (ha : AnalyticAt ℂ a z₀) (hP : ∀ w ∈ sphere (0 : ℂ) R, (monicOfCoeff (a z₀)).eval w ≠ 0) :
    AnalyticAt ℂ (fun q : V × ℂ => ∮ w in C((0 : ℂ), R), (w - q.2)⁻¹ •
      (f (q.1, w) / (monicOfCoeff (a q.1)).eval w)) (z₀, 0) := by
  refine analyticAt_circleIntegral (f := fun r : (V × ℂ) × ℂ => (r.2 - r.1.2)⁻¹ •
    (f (r.1.1, r.2) / (monicOfCoeff (a r.1.1)).eval r.2)) fun w hw => ?_
  rw [abs_of_pos hR] at hw
  have hfst : AnalyticAt ℂ (fun r : (V × ℂ) × ℂ => (r.1.1, r.2)) ((z₀, 0), w) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hf' : AnalyticAt ℂ (fun r : (V × ℂ) × ℂ => f (r.1.1, r.2)) ((z₀, 0), w) :=
    AnalyticAt.comp_of_eq (hf w hw) hfst rfl
  have hP' : AnalyticAt ℂ (fun r : (V × ℂ) × ℂ => (monicOfCoeff (a r.1.1)).eval r.2)
      ((z₀, 0), w) := AnalyticAt.comp_of_eq (analyticAt_eval_comp ha w) hfst rfl
  have hsub : AnalyticAt ℂ (fun r : (V × ℂ) × ℂ => r.2 - r.1.2) ((z₀, 0), w) :=
    analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)
  refine (hsub.inv ?_).smul (hf'.div hP' (hP w hw))
  simpa using ne_of_mem_sphere hw hR.ne'

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
      fun w hw => by simp only [deriv_slice (hz.1 w (sphere_subset_closedBall hw))]
    rw [← circleIntegral.integral_congr hR.le hcongr,
      circleIntegral_mul_deriv_div_eq_sum_roots (φ := fun w => w ^ j) hR hroots hH hH0
        (fun w _ => analyticAt_id.pow j) heq,
      inv_mul_cancel_left₀ (by simp [Real.pi_ne_zero])]
  have hsum (j : ℕ) : AnalyticAt ℂ (fun z => (((P z).roots.map (· ^ j)).sum : ℂ)) z₀ :=
    (analyticAt_const.mul (analyticAt_circleIntegral_pow_mul_div hR
      (fun w hw => hzero.1 w (sphere_subset_closedBall hw)) hzero.2 j)).congr
      ((hint j).mono fun _ hz => hz.symm)
  exact ⟨P, H, hU.mono hP, fun k =>
    ⟨analyticAt_esymm_of_forall_analyticAt_sum_map_pow k fun j _ _ => hsum j, hsum k⟩⟩

/-- The lower coefficients of monic polynomials of degree `d` are analytic when the elementary
symmetric functions of their roots are. -/
private theorem analyticAt_coeff_of_family {d : ℕ} {P : V → ℂ[X]}
    (hm : ∀ᶠ z in 𝓝 z₀, (P z).Monic) (hdeg : ∀ᶠ z in 𝓝 z₀, (P z).natDegree = d)
    (hsym : ∀ k, AnalyticAt ℂ (fun z => (P z).roots.esymm k) z₀) :
    AnalyticAt ℂ (fun z (i : Fin d) => (P z).coeff i) z₀ := by
  refine analyticAt_pi_iff.2 fun i =>
    ((analyticAt_const (v := ((-1 : ℂ) ^ (d - i)))).mul (hsym (d - i))).congr ?_
  filter_upwards [hm, hdeg] with z hmz hz
  rw [coeff_eq_esymm_roots_of_card (IsAlgClosed.splits (P z)).natDegree_eq_card_roots.symm
    (hz ▸ i.2.le), hmz.leadingCoeff, hz, one_mul, Pi.mul_apply]

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
  have hcenter : P z₀ = X ^ d :=
    eq_X_pow_of_eval_mul_eq hPm (fun ζ hζ => hzero ζ (ball_subset_closedBall (hProots ζ hζ))
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
    analyticAt_coeff_of_family (hP.mono fun _ h => h.1) hdeg fun k => (hsym k).1
  have hcenter' : monicOfCoeff (a z₀) = X ^ d := hmon.self_of_nhds.trans hcenter
  have ha0 : a z₀ = 0 := funext fun i => by
    simp [ha_def, hcenter, coeff_X_pow, i.2.ne]
  set u : V × ℂ → ℂ := fun q => (2 * π * Complex.I)⁻¹ • ∮ w in C((0 : ℂ), R), (w - q.2)⁻¹ •
    (f (q.1, w) / (monicOfCoeff (a q.1)).eval w) with hu_def
  have huH : ∀ᶠ z in 𝓝 z₀, ∀ w ∈ ball (0 : ℂ) R, u (z, w) = H z w := by
    filter_upwards [hP, hmon, hU] with z hz hmz hUz w hw
    simp only [hu_def, hmz]
    exact circleIntegral_sub_inv_smul_div_eq hR hz.2.2.1 hz.2.2.2.2 hUz.2 hw
  have hP0 : ∀ w ∈ sphere (0 : ℂ) R, (monicOfCoeff (a z₀)).eval w ≠ 0 := fun w hw => by
    simpa only [hcenter', eval_pow, eval_X] using pow_ne_zero d (ne_of_mem_sphere hw hR.ne')
  have hu : AnalyticAt ℂ u (z₀, 0) := analyticAt_const.fun_smul
    (analyticAt_circleIntegral_sub_inv_smul_div hR (fun w hw => hU.self_of_nhds.1 w (hsph w hw))
      ha hP0)
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
  (h.analyticAt_unit.mul (analyticAt_eval_comp h.analyticAt_coeff 0)).congr h.eventuallyEq.symm

/-- The degree of the Weierstrass polynomial is the order of `f (z₀, ·)` at `0`. -/
theorem analyticOrderAt_eq (h : IsWeierstrassFactorizationAt f z₀ a u) :
    analyticOrderAt (fun w => f (z₀, w)) 0 = d := by
  have hslice : ∀ᶠ w in 𝓝 (0 : ℂ), f (z₀, w) = u (z₀, w) * (monicOfCoeff (a z₀)).eval w :=
    (Continuous.prodMk_right z₀).continuousAt.eventually (f := fun w : ℂ => (z₀, w))
      h.eventuallyEq
  refine h.analyticAt.curry_right.analyticOrderAt_eq_natCast.2 ⟨fun w => u (z₀, w),
    h.analyticAt_unit.curry_right, h.unit_center_ne_zero, hslice.mono fun w hw => ?_⟩
  simp [hw, h.coeff_center, eval_monicOfCoeff, mul_comm]

/-- All the roots of a monic polynomial with small coefficients are small. -/
private theorem eventually_forall_isRoot_mem_ball {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : Fin d → ℂ in 𝓝 0, ∀ ζ, (monicOfCoeff c).IsRoot ζ → ζ ∈ ball (0 : ℂ) ε := by
  have hK : IsCompact (closedBall (0 : ℂ) 2 \ ball 0 ε) :=
    (isCompact_closedBall _ _).diff isOpen_ball
  have hne : ∀ᶠ c : Fin d → ℂ in 𝓝 0, ∀ ζ ∈ closedBall (0 : ℂ) 2 \ ball 0 ε,
      (monicOfCoeff c).eval ζ ≠ 0 :=
    hK.eventually_forall_of_forall_eventually fun ζ hζ =>
      (analyticAt_eval_monicOfCoeff (0, ζ)).continuousAt.eventually_ne <| by
        have hζ0 : ζ ≠ 0 := fun h0 => hζ.2 (h0 ▸ mem_ball_self hε)
        simp [eval_monicOfCoeff, hζ0]
  filter_upwards [hne, ball_mem_nhds (0 : Fin d → ℂ) one_pos] with c hc hc1 ζ hζ
  by_contra hnot
  have hc1' : ‖c‖ < 1 := by simpa using hc1
  have hζ2 := norm_lt_of_isRoot_monicOfCoeff c hζ
  exact hc ζ ⟨mem_closedBall_zero_iff.2 (by linarith), hnot⟩ hζ

/-- Polynomials which agree near `ζ` up to analytic units have the same multiplicity at `ζ`. -/
private theorem rootMultiplicity_eq_of_eventuallyEq {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {v₁ v₂ : ℂ → ℂ} {ζ : ℂ} (hv₁ : AnalyticAt ℂ v₁ ζ) (hv₂ : AnalyticAt ℂ v₂ ζ)
    (h₁ : v₁ ζ ≠ 0) (h₂ : v₂ ζ ≠ 0)
    (h : (v₁ * fun w => p.eval w) =ᶠ[𝓝 ζ] v₂ * fun w => q.eval w) :
    p.rootMultiplicity ζ = q.rootMultiplicity ζ := by
  have hord₁ := analyticOrderAt_mul hv₁ (AnalyticOnNhd.eval_polynomial p ζ (mem_univ ζ))
  have hord₂ := analyticOrderAt_mul hv₂ (AnalyticOnNhd.eval_polynomial q ζ (mem_univ ζ))
  rw [hv₁.analyticOrderAt_eq_zero.2 h₁, zero_add, analyticOrderAt_eval hp] at hord₁
  rw [hv₂.analyticOrderAt_eq_zero.2 h₂, zero_add, analyticOrderAt_eval hq] at hord₂
  exact_mod_cast hord₁.symm.trans ((analyticOrderAt_congr h).trans hord₂)

/-- Two monic polynomials with all roots in a ball, agreeing there up to analytic units, are
equal. -/
private theorem coeff_eq_of_forall_mem_ball {c₁ c₂ : Fin d → ℂ} {v₁ v₂ : ℂ → ℂ} {ε : ℝ}
    (hroot₁ : ∀ ζ, (monicOfCoeff c₁).IsRoot ζ → ζ ∈ ball (0 : ℂ) ε)
    (hroot₂ : ∀ ζ, (monicOfCoeff c₂).IsRoot ζ → ζ ∈ ball (0 : ℂ) ε)
    (hv₁ : ∀ w ∈ ball (0 : ℂ) ε, AnalyticAt ℂ v₁ w ∧ v₁ w ≠ 0)
    (hv₂ : ∀ w ∈ ball (0 : ℂ) ε, AnalyticAt ℂ v₂ w ∧ v₂ w ≠ 0)
    (h : ∀ w ∈ ball (0 : ℂ) ε,
      v₁ w * (monicOfCoeff c₁).eval w = v₂ w * (monicOfCoeff c₂).eval w) : c₁ = c₂ := by
  classical
  have hne₁ := (monic_monicOfCoeff c₁).ne_zero
  have hne₂ := (monic_monicOfCoeff c₂).ne_zero
  have hroots : (monicOfCoeff c₁).roots = (monicOfCoeff c₂).roots := Multiset.ext.2 fun ζ => by
    rw [count_roots, count_roots]
    by_cases hζ : ζ ∈ ball (0 : ℂ) ε
    · exact rootMultiplicity_eq_of_eventuallyEq hne₁ hne₂ (hv₁ ζ hζ).1 (hv₂ ζ hζ).1 (hv₁ ζ hζ).2
        (hv₂ ζ hζ).2 (eventually_of_mem (isOpen_ball.mem_nhds hζ) h)
    · rw [rootMultiplicity_eq_zero (mt (hroot₁ ζ) hζ),
        rootMultiplicity_eq_zero (mt (hroot₂ ζ) hζ)]
  refine (monicOfCoeff_inj c₁ c₂).1 ?_
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (monic_monicOfCoeff c₁),
    (IsAlgClosed.splits (monicOfCoeff c₂)).eq_prod_roots_of_monic (monic_monicOfCoeff c₂), hroots]

/-- Two functions continuous at `w` which agree near `w` after multiplication by a nonzero
polynomial agree at `w`. -/
private theorem eq_of_eventually_mul_eval_eq {p : ℂ[X]} (hp : p ≠ 0) {v₁ v₂ : ℂ → ℂ} {w : ℂ}
    (h₁ : ContinuousAt v₁ w) (h₂ : ContinuousAt v₂ w)
    (h : ∀ᶠ t in 𝓝 w, v₁ t * p.eval t = v₂ t * p.eval t) : v₁ w = v₂ w := by
  have hne : ∀ᶠ t in 𝓝[≠] w, p.eval t ≠ 0 :=
    (AnalyticOnNhd.eval_polynomial p w (mem_univ w)
      ).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ENat.natCast_ne_top
        (p.rootMultiplicity w)
        ((analyticOrderAt_eval hp w).symm.trans (analyticOrderAt_eq_top.2 h0))
  exact tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)
    (((h.filter_mono nhdsWithin_le_nhds).and hne).mono fun _ ht => mul_right_cancel₀ ht.2 ht.1)

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
      ∀ᶠ z in 𝓝 z₀, ∀ ζ, (monicOfCoeff (a z)).IsRoot ζ → ζ ∈ ball (0 : ℂ) ε :=
    ha.eventually (f := a) (ha0 ▸ eventually_forall_isRoot_mem_ball hε)
  have hcoeff : ∀ᶠ z in 𝓝 z₀, pa z ∧ a₁ z = a₂ z := by
    filter_upwards [hpa, hroots h₁.analyticAt_coeff.continuousAt h₁.coeff_center,
      hroots h₂.analyticAt_coeff.continuousAt h₂.coeff_center] with z hz hr₁ hr₂
    have hgood (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) := hG hz (hball w hw)
    exact ⟨hz, coeff_eq_of_forall_mem_ball (v₁ := fun w => u₁ (z, w)) (v₂ := fun w => u₂ (z, w))
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
