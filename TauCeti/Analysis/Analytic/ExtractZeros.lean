/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Analytic.Order
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Analytic.IsolatedZeros

/-!
# Dividing an analytic function by prescribed zeros

If an analytic function `f` vanishes to order at least `k x` at each point `x` of a finite set
`s`, then `f` factors globally as `f z = (∏ x ∈ s, (z - x) ^ k x) • g z`, where `g` is analytic
wherever `f` is. The quotient `g` is obtained by repeatedly taking divided differences
`dslope · x`, each of which lowers the order of vanishing at `x` by one
(`AnalyticAt.analyticOrderAt_dslope_add_one`).

Over `ℂ` this is the factorization of an entire function with zeros of prescribed multiplicities
used in transcendence proofs, where `g` is then estimated by the maximum modulus principle. The
order hypotheses may be given as vanishing of derivatives through Mathlib's
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`.

Taking `s` to be the zeros of a holomorphic function on a closed disc, without zeros on the boundary
circle, writes it as a monic polynomial carrying all its zeros there times a zero-free function.

## Main results

* `HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff`: the iterated divided differences of `f` at
  `a` take the Taylor coefficients of `f` at `a` as their values at `a`.
* `TauCeti.iterate_dslope_apply_eq_zero_of_lt`: if `f` vanishes to order at least `n` at `a`,
  then the first `n` iterated divided differences of `f` at `a` vanish at `a`.
* `AnalyticOnNhd.exists_eq_prod_pow_smul`: an analytic function with zeros of orders at least
  `k x` at the points `x ∈ s` is `∏ x ∈ s, (z - x) ^ k x` times an analytic function.
* `AnalyticOnNhd.exists_monic_eval_mul_eq`: a function holomorphic on a closed disc without zeros
  on its boundary is a monic polynomial with roots in the open disc times a zero-free function.

## References

* J.-H. Evertse, *Diophantine approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.24.
-/

public section

open Function

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : 𝕜}

/-- Iterated divided differences at `a` preserve analyticity at every point where `f` is
analytic. -/
theorem AnalyticAt.iterate_dslope {z : 𝕜} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 ((swap dslope a)^[n] f) z := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iterate_succ_apply']; exact ih.dslope a

/-- The `n`-th iterated divided difference at `z₀` of a function with power series `p` at `z₀`
takes the value `p.coeff n` at `z₀`: these values are the Taylor coefficients. -/
theorem HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {z₀ : 𝕜} (hp : HasFPowerSeriesAt f p z₀) (n : ℕ) : (swap dslope z₀)^[n] f z₀ = p.coeff n := by
  rw [← (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1,
    ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]

namespace TauCeti

/-- If `f` vanishes to order at least `n` at `a`, then each of the first `n` iterated divided
differences `(swap dslope a)^[k] f`, `k < n`, vanishes at `a`. -/
theorem iterate_dslope_apply_eq_zero_of_lt {n k : ℕ} (hn : (n : ℕ∞) ≤ analyticOrderAt f a)
    (hk : k < n) : (swap dslope a)^[k] f a = 0 := by
  induction k generalizing f n with
  | zero => exact apply_eq_zero_of_analyticOrderAt_ne_zero (lt_of_lt_of_le (mod_cast hk) hn).ne'
  | succ k ih =>
    obtain ⟨hfa, ha⟩ := analyticOrderAt_ne_zero.mp
      (lt_of_lt_of_le (mod_cast Nat.zero_lt_of_lt hk) hn).ne'
    rw [iterate_succ_apply]
    refine ih (n := n - 1) ?_ (by lia)
    -- `n` is positive, so its cast is `↑(n - 1) + 1`; cancelling the `+ 1` against the order
    -- `analyticOrderAt (dslope f a) a + 1` of `f` gives the hypothesis for the next divided
    -- difference.
    have hn₁ : (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; lia
    rw [← hfa.analyticOrderAt_dslope_add_one ha, hn₁] at hn
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hn

end TauCeti

/-- **Division by prescribed zeros.** If `f` is analytic on a neighbourhood of `U` and vanishes
to order at least `k x` at each point `x` of a finite set `s`, then
`f z = (∏ x ∈ s, (z - x) ^ k x) • g z` for all `z` and some `g` analytic on a neighbourhood of
`U`. -/
theorem AnalyticOnNhd.exists_eq_prod_pow_smul {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (s : Finset 𝕜) (k : 𝕜 → ℕ) (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ ∀ z, f z = (∏ x ∈ s, (z - x) ^ k x) • g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | insert a s ha ih =>
    set g₁ := (swap dslope a)^[k a] f
    have hfg₁ (z : 𝕜) : f z = (z - a) ^ k a • g₁ z :=
      (pow_sub_smul_iterate_dslope_of_zero (k a)
        (fun j hj ↦ TauCeti.iterate_dslope_apply_eq_zero_of_lt
          (hk a (Finset.mem_insert_self a s)) hj)
        z).symm
    have hk₁ : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt g₁ x := by
      intro x hx
      rcases eq_or_ne (k x) 0 with h0 | h0
      · simp [h0]
      have hkx := hk x (Finset.mem_insert_of_mem hx)
      have hfx : AnalyticAt 𝕜 f x :=
        (analyticOrderAt_ne_zero.mp (lt_of_lt_of_le (mod_cast Nat.pos_of_ne_zero h0) hkx).ne').1
      have hxa : x ≠ a := fun h ↦ ha (h ▸ hx)
      have hpow : analyticOrderAt (fun z ↦ (z - a) ^ k a) x = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr (pow_ne_zero _ (sub_ne_zero.mpr hxa)))
      have hfeq : f = (fun z ↦ (z - a) ^ k a) • g₁ := funext hfg₁
      rwa [hfeq, analyticOrderAt_smul (by fun_prop) (hfx.iterate_dslope (k a)), hpow,
        zero_add] at hkx
    obtain ⟨g, hg, hg₁⟩ := ih (f := g₁) (fun z hz ↦ (hf z hz).iterate_dslope (k a)) hk₁
    refine ⟨g, hg, fun z ↦ ?_⟩
    rw [hfg₁, hg₁, Finset.prod_insert ha, mul_smul]

section Disc

open Metric Polynomial Set

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

end Disc
