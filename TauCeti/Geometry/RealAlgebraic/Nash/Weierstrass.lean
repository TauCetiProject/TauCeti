/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.RingTheory.Polynomial.Vieta

/-!
# The Nash Weierstrass preparation and division theorems

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, where `σ` is
finite, and suppose that its vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite
order `d` at `t₀`. Then `f` factors near `p₀` as `(P_x).eval (t - t₀) * u (x, t)`, where `P_x` is
the monic polynomial `TauCeti.Polynomial.monicOfCoeff (c · x)` of degree `d` whose lower
coefficients `c i` are Nash germs at `x₀` vanishing at `x₀`, and `u` is a Nash germ nonvanishing
at `p₀` (`TauCeti.IsNashAt.exists_weierstrassPreparation`). Likewise, any Nash germ `g` at `p₀`
can be divided by such a Nash Weierstrass polynomial
(`TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`), or by any Nash germ `f` of finite
vertical order `d` (`TauCeti.IsNashAt.exists_weierstrassDivision`), with a Nash quotient germ at
`p₀` and Nash remainder coefficient germs at `x₀`.

Existence of a real analytic preparation or division is supplied by
`AnalyticAt.exists_weierstrassPreparation_real` and
`AnalyticAt.exists_weierstrassDivision_monicOfCoeff_real`. The content of this file is that
**every** real analytic Weierstrass preparation or division of Nash germs is automatically Nash
(`TauCeti.IsNashAt.of_weierstrassPreparation`,
`TauCeti.IsNashAt.of_weierstrassDivision_monicOfCoeff`).

## Proof outline

To avoid losing control on the discriminant locus where roots of `P_x` coalesce, we pass to a
holomorphic extension `F` of `f` near `z₀ = (p₀ · : ℂ)` and examine the full complex root cluster
`w : Fin d → ℂ` of `P_x(ζ - t₀)` inside a disc `Metric.ball (t₀ : ℂ) R` where the complexified
unit `U` is nonvanishing:

1. **Nash vertical jets.** For each `k`, the complex vertical derivative
   `z ↦ iteratedDeriv k (ζ ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ ζ))) (z (Sum.inr ()))` is a
   holomorphic extension of the real vertical derivative of `f`, which is Nash by
   `TauCeti.IsNashAt.iteratedDeriv_sumElim`. By `TauCeti.IsNashAt.complexification_re_im`, its real
   and imaginary parts are Nash in doubled real coordinates and hence have semialgebraic graphs on
   a common ball around `z₀`.
2. **Semialgebraic root-cluster characterization.** For `x` near `x₀`, continuity of roots confines
   all `d` complex roots of `P_x` to `Metric.ball 0 R`. Because `U` does not vanish on
   `Metric.ball (t₀ : ℂ) R`, the multiplicity of `w_j - t₀` in `P_x` equals the order of vanishing
   of `F(x, ·)` at `w_j`. Thus a tuple `w : Fin d → ℂ` in `Metric.ball (t₀ : ℂ) R` lists the roots
   of `P_x(· - t₀)` with multiplicity if and only if for each `j` the cluster size
   `#{l | w_l = w_j}` matches the first nonvanishing vertical derivative of `F(x, ·)` at `w_j`.
   Eliminating `w` by Tarski–Seidenberg (`TauCeti.IsSemialgebraic.setOf_exists_sumElim`) shows that
   `x ↦ c · x` has a semialgebraic graph near `x₀`, so each `c i` is Nash by the local Nash graph
   criterion (`TauCeti.forall_isNashAt_apply_iff_exists_isSemialgebraicOn`).
3. **Hermite characterization of the remainder.** For division of a Nash germ `g` by a Nash
   Weierstrass polynomial `P_x`, a degree-`< d` polynomial `R_x(ζ - t₀)` agrees with the Weierstrass
   remainder if and only if at each complex root `w_j` of `P_x(· - t₀)` of multiplicity `m` its
   vertical derivatives of order `< m` match those of the holomorphic extension `G(x, ·)`.
   Eliminating the root cluster `w` again makes each remainder coefficient `r i` Nash at `x₀`.
4. **Exact quotient descent.** Once the polynomial part is Nash, `P_x(t - t₀)` is a Nash germ not
   vanishing identically near `p₀`, so `TauCeti.IsNashAt.of_mul_eventuallyEq` shows in one step
   that the analytic unit `u` and quotient `q` are Nash at `p₀`.

## Main results

* `TauCeti.IsNashAt.of_weierstrassPreparation`: in any real analytic Weierstrass preparation of a
  Nash germ, the Weierstrass polynomial coefficients and unit are Nash germs.
* `TauCeti.IsNashAt.exists_weierstrassPreparation`: the Nash Weierstrass preparation theorem.
* `TauCeti.IsNashAt.of_weierstrassDivision_monicOfCoeff`: in any real analytic Weierstrass division
  of a Nash germ by a Nash Weierstrass polynomial, the quotient and remainder coefficients are Nash
  germs.
* `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`: Nash Weierstrass division by a Nash
  Weierstrass polynomial.
* `TauCeti.IsNashAt.exists_weierstrassDivision`: the general Nash Weierstrass division theorem.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.2 (Weierstrass preparation and division for Nash
  functions, Theorem 8.2.2 and Proposition 8.2.3).
-/

public section

open Complex Filter Function Metric Polynomial Set Topology

namespace TauCeti

section AuxNoFintype

variable {σ : Type*}

/-- A Weierstrass polynomial `P_x(t - t₀)` does not vanish identically near `(x₀, t₀)`. -/
private theorem not_eventuallyEq_zero_eval_monicOfCoeff {d : ℕ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} (hc0 : ∀ i, c i x₀ = 0) :
    ¬ (fun p : σ ⊕ Unit → ℝ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀))
      =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] 0 := by
  intro h0
  have hcont : Continuous (fun t : ℝ ↦ Sum.elim x₀ (fun _ : Unit ↦ t)) :=
    continuous_pi <| Sum.rec (fun _ ↦ continuous_const) (fun _ ↦ continuous_id)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ((hcont.tendsto t₀).eventually h0)
  have hmem : t₀ + ε / 2 ∈ ball t₀ ε := by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have heval : ((Polynomial.monicOfCoeff (fun i ↦ c i x₀)).eval (t₀ + ε / 2 - t₀)) = 0 := by
    simpa [Sum.elim_comp_inl] using hball hmem
  rw [Polynomial.eval_monicOfCoeff, add_sub_cancel_left] at heval
  simp only [hc0, zero_mul, Finset.sum_const_zero, add_zero] at heval
  exact pow_ne_zero d (half_pos hε).ne' heval

/-! ### Complex polynomial root clusters and derivative characterizations -/

/-- Near `x₀`, all `d` complex roots of `monicOfCoeff (c · x)` lie in `ball 0 R`, so `P_x` splits
as `∏ j : Fin d, (X - C (w j - t₀))` with `‖w j - t₀‖ < R`. -/
private theorem eventually_exists_roots_mem_ball {d : ℕ} {x₀ : σ → ℝ} (t₀ : ℝ) {R : ℝ}
    (hR : 0 < R) {c : Fin d → (σ → ℝ) → ℝ} (hc : ∀ i, ContinuousAt (c i) x₀)
    (hc0 : ∀ i, c i x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀,
      (∀ α ∈ (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).roots, ‖α‖ < R) ∧
      ∃ w : Fin d → ℂ, (∀ j, ‖w j - t₀‖ < R) ∧
        Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ)) = ∏ j : Fin d, (X - C (w j - t₀)) := by
  obtain ⟨η, hη, hcont⟩ :=
    (monic_X_pow d : (X ^ d : ℂ[X]).Monic).exists_prod_X_sub_C_norm_sub_lt hR
  rw [natDegree_X_pow] at hcont
  have hsmall : ∀ᶠ x in 𝓝 x₀, ∀ i : Fin d, ‖(c i x : ℂ)‖ < η :=
    eventually_all.2 fun i ↦ by
      have hci : ContinuousAt (fun x ↦ ‖(c i x : ℂ)‖) x₀ :=
        continuous_norm.continuousAt.comp (Complex.continuous_ofReal.continuousAt.comp (hc i))
      have hci0 : Tendsto (fun x ↦ ‖(c i x : ℂ)‖) (𝓝 x₀) (𝓝 0) := by
        simpa [hc0 i] using hci.tendsto
      exact hci0.eventually (gt_mem_nhds hη)
  filter_upwards [hsmall] with x hx
  set P : ℂ[X] := Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))
  obtain ⟨a, b, ha, hb, hab⟩ := hcont P (Polynomial.monic_monicOfCoeff _)
    (Polynomial.natDegree_monicOfCoeff _) fun k hk ↦ by
      simpa [P, Polynomial.coeff_monicOfCoeff _ ⟨k, hk⟩, coeff_X_pow, hk.ne] using hx ⟨k, hk⟩
  have ha0 (j : Fin d) : a j = 0 := by
    have hev := congrArg (Polynomial.eval (a j)) ha
    rw [eval_pow, eval_X, eval_prod] at hev
    exact eq_zero_of_pow_eq_zero (hev.trans (Finset.prod_eq_zero (Finset.mem_univ j) (by simp)))
  have hbR (j : Fin d) : ‖b j‖ < R := by simpa [ha0 j] using hab j
  refine ⟨fun α hα ↦ ?_, fun j ↦ (t₀ : ℂ) + b j, fun j ↦ by simpa using hbR j, ?_⟩
  · rw [hb, Polynomial.roots_prod_X_sub_C_map, Multiset.mem_map] at hα
    obtain ⟨j, -, rfl⟩ := hα
    exact hbR j
  · simp [hb]

/-- Analytic order of a shifted polynomial `ζ ↦ P.eval (ζ - t₀)` at `ζ₀`. -/
private theorem analyticOrderAt_eval_sub {P : ℂ[X]} (hP : P ≠ 0) (t₀ ζ₀ : ℂ) :
    analyticOrderAt (fun ζ : ℂ ↦ P.eval (ζ - t₀)) ζ₀ = P.rootMultiplicity (ζ₀ - t₀) := by
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP (ζ₀ - t₀)
  have hanP : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - t₀)) ζ₀ :=
    ((AnalyticOnNhd.eval_polynomial P) _ (mem_univ _)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  have hanQ : AnalyticAt ℂ (fun ζ : ℂ ↦ Q.eval (ζ - t₀)) ζ₀ :=
    ((AnalyticOnNhd.eval_polynomial Q) _ (mem_univ _)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  refine hanP.analyticOrderAt_eq_natCast.2 ⟨fun ζ ↦ Q.eval (ζ - t₀), hanQ,
    fun h0 ↦ hQ (dvd_iff_isRoot.2 h0), .of_forall fun ζ ↦ ?_⟩
  conv_lhs => rw [hPQ]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_sub_sub_cancel_right, smul_eq_mul]

/-- If `F₁ = P(· - t₀) * U₁` on `ball t₀ R` with `U₁` nonvanishing there, then the root
multiplicity of `ζ₀ - t₀` in `P` is characterized by the iterated derivatives of `F₁` at `ζ₀`. -/
private theorem rootMultiplicity_eq_iff_iteratedDeriv {P : ℂ[X]} (hP : P ≠ 0) {F₁ U₁ : ℂ → ℂ}
    {t₀ : ℂ} {R : ℝ} (hF₁ : AnalyticOnNhd ℂ F₁ (ball t₀ R))
    (hU₁ : AnalyticOnNhd ℂ U₁ (ball t₀ R)) (hU₀ : ∀ ζ ∈ ball t₀ R, U₁ ζ ≠ 0)
    (hfac : ∀ ζ ∈ ball t₀ R, F₁ ζ = P.eval (ζ - t₀) * U₁ ζ) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ ball t₀ R)
    (m : ℕ) :
    P.rootMultiplicity (ζ₀ - t₀) = m ↔
      (∀ k < m, iteratedDeriv k F₁ ζ₀ = 0) ∧ iteratedDeriv m F₁ ζ₀ ≠ 0 := by
  have hanP : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - t₀)) ζ₀ :=
    ((AnalyticOnNhd.eval_polynomial P) _ (mem_univ _)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  have heq : F₁ =ᶠ[𝓝 ζ₀] (fun ζ ↦ P.eval (ζ - t₀)) * U₁ := by
    filter_upwards [isOpen_ball.mem_nhds hζ₀] with ζ hζ
    exact hfac ζ hζ
  have hord : analyticOrderAt F₁ ζ₀ = P.rootMultiplicity (ζ₀ - t₀) := by
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hanP (hU₁ ζ₀ hζ₀),
      analyticOrderAt_eval_sub hP, (hU₁ ζ₀ hζ₀).analyticOrderAt_eq_zero.2 (hU₀ ζ₀ hζ₀), add_zero]
  rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hF₁ ζ₀ hζ₀), hord, Nat.cast_inj]

/-- Multiplicity of `w j - t₀` in the multiset `Finset.univ.val.map (w · - t₀)`. -/
private theorem count_map_sub_univ {d : ℕ} (w : Fin d → ℂ) (t₀ : ℂ) (j : Fin d) :
    Multiset.count (w j - t₀) (Finset.univ.val.map fun l : Fin d ↦ w l - t₀) =
      (Finset.univ.filter fun l : Fin d ↦ w l = w j).card := by
  rw [Multiset.count_eq_card_filter_eq, Multiset.filter_map, Multiset.card_map, Finset.card_def]
  congr 1
  exact Multiset.filter_congr fun l _ ↦ by
    simp only [Function.comp_apply, sub_left_inj]
    tauto

/-- Root-cluster characterization of a Weierstrass polynomial `P`: a tuple `w : Fin d → ℂ` in
`ball t₀ R` lists the roots of `P(· - t₀)` with multiplicity if and only if for each `j` the
cluster `{l | w l = w j}` has cardinality equal to the order of vanishing of `F₁` at `w j`. -/
private theorem eq_prod_X_sub_C_iff_iteratedDeriv {d : ℕ} {P : ℂ[X]} (hPm : P.Monic)
    (hPd : P.natDegree = d) {F₁ U₁ : ℂ → ℂ} {t₀ : ℂ} {R : ℝ}
    (hF₁ : AnalyticOnNhd ℂ F₁ (ball t₀ R)) (hU₁ : AnalyticOnNhd ℂ U₁ (ball t₀ R))
    (hU₀ : ∀ ζ ∈ ball t₀ R, U₁ ζ ≠ 0) (hfac : ∀ ζ ∈ ball t₀ R, F₁ ζ = P.eval (ζ - t₀) * U₁ ζ)
    (w : Fin d → ℂ) (hw : ∀ j, w j ∈ ball t₀ R) :
    P = ∏ j : Fin d, (X - C (w j - t₀)) ↔
      ∀ (j : Fin d) (S : Finset (Fin d)), S.Nonempty → (∀ l, l ∈ S ↔ w l = w j) →
        (∀ k < S.card, iteratedDeriv k F₁ (w j) = 0) ∧ iteratedDeriv S.card F₁ (w j) ≠ 0 := by
  constructor
  · rintro hP j S - hS
    have hScard : S = Finset.univ.filter (fun l : Fin d ↦ w l = w j) := by
      ext l; simp [hS l]
    refine (rootMultiplicity_eq_iff_iteratedDeriv hPm.ne_zero hF₁ hU₁ hU₀ hfac (hw j) S.card).1 ?_
    rw [← count_roots, hP, Polynomial.roots_prod_X_sub_C_map, count_map_sub_univ, hScard]
  · intro hcond
    have hmult (j : Fin d) :
        P.rootMultiplicity (w j - t₀) = (Finset.univ.filter fun l : Fin d ↦ w l = w j).card := by
      set S := Finset.univ.filter fun l : Fin d ↦ w l = w j
      have hne : S.Nonempty := ⟨j, by simp [S]⟩
      exact (rootMultiplicity_eq_iff_iteratedDeriv hPm.ne_zero hF₁ hU₁ hU₀ hfac (hw j) S.card).2
        (hcond j S hne fun l ↦ by simp [S])
    have hle : (Finset.univ.val.map fun l : Fin d ↦ w l - t₀) ≤ P.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ Finset.univ.val.map fun l : Fin d ↦ w l - t₀
      · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hα
        rw [count_map_sub_univ, ← hmult j, count_roots]
      · rw [Multiset.count_eq_zero_of_notMem hα]
        exact Nat.zero_le _
    have hroots : P.roots = Finset.univ.val.map fun l : Fin d ↦ w l - t₀ :=
      (Multiset.eq_of_le_of_card_le hle ((card_roots' P).trans (by simp [hPd]))).symm
    exact Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq hPm (by simp [hPd]) hroots

/-- Explicit formula for the `k`-th iterated derivative of `ζ ↦ ∑ i : Fin d, y i * (ζ - t₀) ^ i`. -/
private theorem iteratedDeriv_sum_pow_sub {d : ℕ} (y : Fin d → ℂ) (t₀ ζ₀ : ℂ) (k : ℕ) :
    iteratedDeriv k (fun ζ : ℂ ↦ ∑ i : Fin d, y i * (ζ - t₀) ^ (i : ℕ)) ζ₀ =
      ∑ i : Fin d, y i * ((i : ℕ).descFactorial k : ℂ) * (ζ₀ - t₀) ^ ((i : ℕ) - k) := by
  rw [iteratedDeriv_fun_sum fun i _ ↦ by fun_prop]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hshift := congrFun
    (iteratedDeriv_comp_sub_const k (fun z : ℂ ↦ (z : ℂ) ^ (i : ℕ)) t₀) ζ₀
  rw [iteratedDeriv_const_mul_field, hshift, iteratedDeriv_pow, mul_assoc]

/-- Hermite interpolation characterization of the Weierstrass remainder: if `G₁ = P(· - t₀) * Q₁ +
∑ i, r₀ i * (· - t₀) ^ i` on `ball t₀ R`, then `y = r₀` if and only if there is a root cluster `w`
of `P(· - t₀)` in `ball t₀ R` at which the derivatives of `∑ i, y i * (· - t₀) ^ i` up to each
cluster size match those of `G₁`. -/
private theorem eq_rem_iff_iteratedDeriv {d : ℕ} {P : ℂ[X]} (hPm : P.Monic)
    {G₁ Q₁ : ℂ → ℂ} {t₀ : ℂ} {R : ℝ}
    (hQ₁ : AnalyticOnNhd ℂ Q₁ (ball t₀ R)) {r₀ : Fin d → ℂ}
    (hdiv : ∀ ζ ∈ ball t₀ R,
      G₁ ζ = P.eval (ζ - t₀) * Q₁ ζ + ∑ i : Fin d, r₀ i * (ζ - t₀) ^ (i : ℕ))
    (hw₀ : ∃ w₀ : Fin d → ℂ, (∀ j, w₀ j ∈ ball t₀ R) ∧ P = ∏ j : Fin d, (X - C (w₀ j - t₀)))
    (y : Fin d → ℂ) :
    y = r₀ ↔ ∃ w : Fin d → ℂ, (∀ j, w j ∈ ball t₀ R) ∧ P = ∏ j : Fin d, (X - C (w j - t₀)) ∧
      ∀ (j : Fin d) (S : Finset (Fin d)), (∀ l ∈ S, w l = w j) → ∀ k : Fin d, (k : ℕ) < S.card →
        iteratedDeriv (k : ℕ) G₁ (w j) =
          ∑ i : Fin d, y i * ((i : ℕ).descFactorial (k : ℕ) : ℂ) *
            (w j - t₀) ^ ((i : ℕ) - (k : ℕ)) := by
  have hG_jet (ζ₀ : ℂ) (hζ₀ : ζ₀ ∈ ball t₀ R) (k : ℕ) (hk : k < P.rootMultiplicity (ζ₀ - t₀)) :
      iteratedDeriv k G₁ ζ₀ =
        ∑ i : Fin d, r₀ i * ((i : ℕ).descFactorial k : ℂ) * (ζ₀ - t₀) ^ ((i : ℕ) - k) := by
    have hanP : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - t₀)) ζ₀ :=
      ((AnalyticOnNhd.eval_polynomial P) _ (mem_univ _)).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl
    have hanPQ : AnalyticAt ℂ (fun ζ : ℂ ↦ P.eval (ζ - t₀) * Q₁ ζ) ζ₀ :=
      hanP.fun_mul (hQ₁ ζ₀ hζ₀)
    have hPQ0 : iteratedDeriv k (fun ζ : ℂ ↦ P.eval (ζ - t₀) * Q₁ ζ) ζ₀ = 0 := by
      refine ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanPQ).1 ?_) k hk
      rw [show (fun ζ : ℂ ↦ P.eval (ζ - t₀) * Q₁ ζ) = (fun ζ ↦ P.eval (ζ - t₀)) * Q₁ from rfl,
        analyticOrderAt_mul hanP (hQ₁ ζ₀ hζ₀), analyticOrderAt_eval_sub hPm.ne_zero]
      exact le_self_add
    have heq : G₁ =ᶠ[𝓝 ζ₀]
        (fun ζ ↦ P.eval (ζ - t₀) * Q₁ ζ) + (fun ζ ↦ ∑ i : Fin d, r₀ i * (ζ - t₀) ^ (i : ℕ)) := by
      filter_upwards [isOpen_ball.mem_nhds hζ₀] with ζ hζ
      exact hdiv ζ hζ
    rw [heq.iteratedDeriv_eq k, iteratedDeriv_add hanPQ.contDiffAt (by fun_prop), hPQ0, zero_add,
      iteratedDeriv_sum_pow_sub]
  constructor
  · rintro rfl
    obtain ⟨w₀, hw₀R, hPw₀⟩ := hw₀
    refine ⟨w₀, hw₀R, hPw₀, fun j S hS k hk ↦ hG_jet (w₀ j) (hw₀R j) k ?_⟩
    have hsub : S ⊆ Finset.univ.filter (fun l : Fin d ↦ w₀ l = w₀ j) := fun l hl ↦ by
      simp [hS l hl]
    have hcnt : (Finset.univ.filter fun l : Fin d ↦ w₀ l = w₀ j).card =
        P.rootMultiplicity (w₀ j - t₀) := by
      rw [← count_roots, hPw₀, Polynomial.roots_prod_X_sub_C_map, count_map_sub_univ]
    exact hk.trans_le ((Finset.card_le_card hsub).trans_eq hcnt)
  · rintro ⟨w, hwR, hPw, hjet⟩
    set D : ℂ[X] := ∑ i : Fin d, monomial (i : ℕ) (y i - r₀ i)
    by_cases hD : D = 0
    · ext i
      have hi : D.coeff (i : ℕ) = 0 := by simp [hD]
      simp only [D, finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hi
      exact sub_eq_zero.1 hi
    exfalso
    have hdeg : D.natDegree < d := by
      have hlt : D.degree < d := by
        simpa only [D, C_mul_X_pow_eq_monomial] using degree_sum_fin_lt fun i : Fin d ↦ y i - r₀ i
      exact WithBot.coe_lt_coe.1 ((degree_eq_natDegree hD).symm.trans_lt hlt)
    have hle : P.roots ≤ D.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ P.roots
      · rw [hPw, Polynomial.roots_prod_X_sub_C_map, Multiset.mem_map] at hα
        obtain ⟨j, -, rfl⟩ := hα
        rw [count_roots, count_roots]
        set S := Finset.univ.filter fun l : Fin d ↦ w l = w j
        have hScard : P.rootMultiplicity (w j - t₀) = S.card := by
          rw [← count_roots, hPw, Polynomial.roots_prod_X_sub_C_map, count_map_sub_univ]
        have hanD : AnalyticAt ℂ (fun ζ : ℂ ↦ D.eval (ζ - t₀)) (w j) :=
          ((AnalyticOnNhd.eval_polynomial D) _ (mem_univ _)).comp_of_eq
            (analyticAt_id.sub analyticAt_const) rfl
        have hordD : (P.rootMultiplicity (w j - t₀) : ℕ∞) ≤
            analyticOrderAt (fun ζ : ℂ ↦ D.eval (ζ - t₀)) (w j) := by
          refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanD).2 fun k hk ↦ ?_
          have hkd : k < d := hk.trans_le (hScard.trans_le
            (S.card_le_univ.trans_eq (Fintype.card_fin d)))
          have hy_eq := hjet j S (fun l hl ↦ (Finset.mem_filter.1 hl).2) ⟨k, hkd⟩ (hScard ▸ hk)
          have hr_eq := hG_jet (w j) (hwR j) k hk
          have hDeval : (fun ζ : ℂ ↦ D.eval (ζ - t₀)) =
              (fun ζ ↦ ∑ i : Fin d, y i * (ζ - t₀) ^ (i : ℕ)) -
                (fun ζ ↦ ∑ i : Fin d, r₀ i * (ζ - t₀) ^ (i : ℕ)) := by
            ext ζ; simp [D, eval_finsetSum, Finset.sum_sub_distrib]
          rw [hDeval, iteratedDeriv_sub (by fun_prop) (by fun_prop), iteratedDeriv_sum_pow_sub,
            iteratedDeriv_sum_pow_sub, ← hy_eq, ← hr_eq, sub_self]
        rw [analyticOrderAt_eval_sub hD] at hordD
        exact Nat.cast_le.1 hordD
      · rw [Multiset.count_eq_zero_of_notMem hα]
        exact Nat.zero_le _
    have hcardP : P.roots.card = d := by
      rw [hPw, Polynomial.roots_prod_X_sub_C_map]
      simp
    exact absurd ((hcardP ▸ Multiset.card_le_card hle).trans (card_roots' D)) (not_le_of_gt hdeg)

/-! ### Semialgebraic building blocks without finiteness of `σ` -/

/-- The `k`-th iterated derivative of `F : (σ ⊕ Unit → ℂ) → ℂ` in the vertical coordinate. -/
private noncomputable def verticalIteratedDeriv (F : (σ ⊕ Unit → ℂ) → ℂ) (k : ℕ)
    (z : σ ⊕ Unit → ℂ) : ℂ :=
  iteratedDeriv k (fun ζ : ℂ ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ ζ))) (z (.inr ()))

/-- A constant-proposition guard `P → a ∈ s` preserves semialgebraicity. -/
private theorem IsSemialgebraic.imp_of_const {τ : Type*} (P : Prop) {s : Set (τ → ℝ)}
    (hs : IsSemialgebraic s) : IsSemialgebraic {a : τ → ℝ | P → a ∈ s} := by
  by_cases hP : P <;> simp [hP, hs]

/-- A complex polynomial `q : MvPolynomial τ ℂ` evaluated at real points defines a semialgebraic
map into `Unit ⊕ Unit → ℝ` via `complexToRealPi Unit`. -/
private theorem isSemialgebraicMap_complexToRealPi_eval {τ : Type*} (q : MvPolynomial τ ℂ) :
    IsSemialgebraicMap (fun a : τ → ℝ ↦
      complexToRealPi Unit (fun _ ↦ MvPolynomial.eval (fun s ↦ (a s : ℂ)) q)) := by
  rw [← isSemialgebraicOn_univ, isSemialgebraicOn_iff_graph]
  let r : MvPolynomial (τ ⊕ (Unit ⊕ Unit)) ℂ :=
    MvPolynomial.rename Sum.inl q -
      (MvPolynomial.X (.inr (.inl ())) + MvPolynomial.X (.inr (.inr ())) * MvPolynomial.C I)
  convert isSemialgebraic_setOf_eval_ofReal_eq_zero r using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_univ, true_and, mem_ofPred_eq, r, map_sub, MvPolynomial.eval_rename, map_add,
    map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]
  rw [← ContinuousLinearEquiv.eq_symm_apply]
  simp [funext_iff, Function.comp_def, Unique.forall_iff]

/-- Abbreviation for the combined real coordinate index `(σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)`. -/
private abbrev RootClusterIdx (σ : Type*) (d : ℕ) := (σ ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)

/-- Extracts the complex root cluster `w : Fin d → ℂ` from `a : RootClusterIdx σ d → ℝ`. -/
private noncomputable def rootClusterOf (σ : Type*) {d : ℕ} (a : RootClusterIdx σ d → ℝ) :
    Fin d → ℂ :=
  (complexToRealPi (Fin d)).symm (a ∘ Sum.inr)

/-- Extracts the complexified `j`-th slice point `(x_ℂ(a), w_j(a)) : σ ⊕ Unit → ℂ` from `a`. -/
private noncomputable def slicePointOf (σ : Type*) {d : ℕ} (j : Fin d)
    (a : RootClusterIdx σ d → ℝ) : σ ⊕ Unit → ℂ :=
  Sum.elim (fun s : σ ↦ (a (.inl (.inl s)) : ℂ)) (fun _ : Unit ↦ rootClusterOf σ a j)

/-- The `j`-th complex root variable `X (.inr (.inl j)) + X (.inr (.inr j)) * I` as a polynomial. -/
private noncomputable def rootVarPoly (σ : Type*) {d : ℕ} (j : Fin d) :
    MvPolynomial (RootClusterIdx σ d) ℂ :=
  MvPolynomial.X (.inr (.inl j)) + MvPolynomial.X (.inr (.inr j)) * MvPolynomial.C I

/-- Polynomial map sending `(x, y, ω)` to the doubled real coordinates of `(x_ℂ, w_j)`. -/
private noncomputable def sliceCoordPoly (σ : Type*) {d : ℕ} (j : Fin d) :
    (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → MvPolynomial (RootClusterIdx σ d) ℝ
  | .inl (.inl s) => MvPolynomial.X (.inl (.inl s))
  | .inl (.inr ()) => MvPolynomial.X (.inr (.inl j))
  | .inr (.inl _) => 0
  | .inr (.inr ()) => MvPolynomial.X (.inr (.inr j))

/-- Semialgebraicity of the locus `{a | (y_i : ℂ) = (∏ j, (X - C (w_j - t₀))).coeff i}`. -/
private theorem isSemialgebraic_coeff_eq_vieta {d : ℕ} (t₀ : ℝ) (i : Fin d) :
    IsSemialgebraic {a : RootClusterIdx σ d → ℝ |
      (a (.inl (.inr i)) : ℂ) =
        (∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀))).coeff (i : ℕ)} := by
  let P_mv : (MvPolynomial (RootClusterIdx σ d) ℂ)[X] :=
    ∏ j : Fin d, (X - C (rootVarPoly σ j - MvPolynomial.C (t₀ : ℂ)))
  convert isSemialgebraic_setOf_eval_ofReal_eq_zero
      (MvPolynomial.X (.inl (.inr i)) - P_mv.coeff (i : ℕ)) using 1
  ext a
  have hmap : P_mv.map (MvPolynomial.eval fun idx ↦ (a idx : ℂ)) =
      ∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀)) := by
    simp [P_mv, rootVarPoly, rootClusterOf, Polynomial.map_prod]
  have hcoeff := congrArg (fun Q : ℂ[X] ↦ Q.coeff (i : ℕ)) hmap
  simp only [Polynomial.coeff_map] at hcoeff
  rw [mem_ofPred_eq, mem_ofPred_eq, ← hcoeff]
  simp [sub_eq_zero]

/-- Semialgebraicity of `{a | w_l(a) = w_j(a)}`. -/
private theorem isSemialgebraic_rootVar_eq {d : ℕ} (l j : Fin d) :
    IsSemialgebraic {a : RootClusterIdx σ d → ℝ | rootClusterOf σ a l = rootClusterOf σ a j} := by
  convert isSemialgebraic_setOf_eval_ofReal_eq_zero (rootVarPoly σ l - rootVarPoly σ j) using 1
  ext a
  simp [rootVarPoly, rootClusterOf, sub_eq_zero]

/-- Locus in `(x, y, ω)` coordinates characterizing the graph of the Weierstrass polynomial
coefficients together with the complex root cluster of `P_x(· - t₀)`. -/
private noncomputable def prepClusterLocus {d : ℕ} (D : Set (RootClusterIdx σ d → ℝ)) (t₀ : ℝ)
    (F : (σ ⊕ Unit → ℂ) → ℂ) : Set (RootClusterIdx σ d → ℝ) :=
  D ∩ (⋂ i : Fin d, {a | (a (.inl (.inr i)) : ℂ) =
      (∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀))).coeff (i : ℕ)}) ∩
    ⋂ (j : Fin d) (S : Finset (Fin d)),
      {a | S.Nonempty → a ∈
        (⋂ l : Fin d, if l ∈ S then {a | rootClusterOf σ a l = rootClusterOf σ a j}
          else {a | rootClusterOf σ a l = rootClusterOf σ a j}ᶜ)ᶜ ∪
        ((⋂ k : Fin (d + 1),
            {a | (k : ℕ) < S.card →
              a ∈ D ∩ {a | verticalIteratedDeriv F (k : ℕ) (slicePointOf σ j a) = 0}}) ∩
          (D \ (D ∩ {a | verticalIteratedDeriv F S.card (slicePointOf σ j a) = 0})))}

private theorem mem_prepClusterLocus_iff {d : ℕ} {D : Set (RootClusterIdx σ d → ℝ)} {t₀ : ℝ}
    {F : (σ ⊕ Unit → ℂ) → ℂ} (xy : σ ⊕ Fin d → ℝ) (ω : Fin d ⊕ Fin d → ℝ) :
    let w := (complexToRealPi (Fin d)).symm ω
    Sum.elim xy ω ∈ prepClusterLocus D t₀ F ↔
      Sum.elim xy ω ∈ D ∧
      (∀ i : Fin d, (xy (.inr i) : ℂ) =
        (∏ j : Fin d, (X - C (w j - t₀))).coeff (i : ℕ)) ∧
      ∀ (j : Fin d) (S : Finset (Fin d)), S.Nonempty → (∀ l : Fin d, l ∈ S ↔ w l = w j) →
        (∀ k < S.card, verticalIteratedDeriv F k
          (Sum.elim (fun s ↦ (xy (.inl s) : ℂ)) (fun _ ↦ w j)) = 0) ∧
        verticalIteratedDeriv F S.card
          (Sum.elim (fun s ↦ (xy (.inl s) : ℂ)) (fun _ ↦ w j)) ≠ 0 := by
  intro w
  set a : RootClusterIdx σ d → ℝ := Sum.elim xy ω
  have hw : rootClusterOf σ a = w := by simp [a, w, rootClusterOf, Sum.elim_comp_inr]
  have hslice (j : Fin d) :
      slicePointOf σ j a = Sum.elim (fun s ↦ (xy (.inl s) : ℂ)) (fun _ ↦ w j) := by
    simp [slicePointOf, hw, a]
  have hcl_iff (j : Fin d) (S : Finset (Fin d)) :
      (a ∈ ⋂ l : Fin d, if l ∈ S then {a | rootClusterOf σ a l = rootClusterOf σ a j}
        else {a | rootClusterOf σ a l = rootClusterOf σ a j}ᶜ) ↔
      ∀ l : Fin d, l ∈ S ↔ w l = w j := by
    rw [mem_iInter]
    refine forall_congr' fun l ↦ ?_
    by_cases hl : l ∈ S <;> simp [hl, hw]
  constructor
  · rintro ⟨⟨haD, hvieta⟩, hjet⟩
    refine ⟨haD, fun i ↦ by simpa [a, hw] using mem_iInter.1 hvieta i, fun j S hSne hS ↦ ?_⟩
    rcases (mem_iInter.1 (mem_iInter.1 hjet j) S) hSne with hnot | ⟨hk0, -, hne0⟩
    · exact False.elim (hnot ((hcl_iff j S).2 hS))
    · refine ⟨fun k hk ↦ ?_, fun h0 ↦ hne0 ⟨haD, by simpa [hslice] using h0⟩⟩
      have hkd : k < d + 1 :=
        Nat.lt_succ_of_le (hk.le.trans (S.card_le_univ.trans_eq (Fintype.card_fin d)))
      simpa [hslice] using ((mem_iInter.1 hk0 ⟨k, hkd⟩) hk).2
  · rintro ⟨haD, hvieta, hjet⟩
    refine ⟨⟨haD, mem_iInter.2 fun i ↦ by simpa [a, hw] using hvieta i⟩,
      mem_iInter.2 fun j ↦ mem_iInter.2 fun S hSne ↦ ?_⟩
    by_cases hS : ∀ l : Fin d, l ∈ S ↔ w l = w j
    · obtain ⟨hk0, hne0⟩ := hjet j S hSne hS
      refine Or.inr ⟨mem_iInter.2 fun k hk ↦ ⟨haD, by simpa [hslice] using hk0 k hk⟩, haD,
        fun h ↦ hne0 (by simpa [hslice] using h.2)⟩
    · exact Or.inl (mt (hcl_iff j S).1 hS)

/-- Locus in `(x, y, ω)` coordinates characterizing the graph of the Weierstrass remainder
coefficients via Hermite interpolation on the root cluster of `P_x(· - t₀)`. -/
private noncomputable def divClusterLocus {d : ℕ} (D : Set (RootClusterIdx σ d → ℝ)) (t₀ : ℝ)
    (c : Fin d → (σ → ℝ) → ℝ) (G : (σ ⊕ Unit → ℂ) → ℂ) : Set (RootClusterIdx σ d → ℝ) :=
  (D ∩ ⋂ i : Fin d, D ∩ {a | (c i (fun s ↦ a (.inl (.inl s))) : ℂ) =
      (∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀))).coeff (i : ℕ)}) ∩
    ⋂ (j : Fin d) (S : Finset (Fin d)),
      (⋂ l : Fin d, {a | l ∈ S → rootClusterOf σ a l = rootClusterOf σ a j})ᶜ ∪
      ⋂ k : Fin d, {a | (k : ℕ) < S.card → a ∈ D ∩
        {a | verticalIteratedDeriv G (k : ℕ) (slicePointOf σ j a) =
          ∑ i : Fin d, (a (.inl (.inr i)) : ℂ) * ((i : ℕ).descFactorial (k : ℕ) : ℂ) *
            (rootClusterOf σ a j - t₀) ^ ((i : ℕ) - (k : ℕ))}}

private theorem mem_divClusterLocus_iff {d : ℕ} {D : Set (RootClusterIdx σ d → ℝ)} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {G : (σ ⊕ Unit → ℂ) → ℂ}
    (xy : σ ⊕ Fin d → ℝ) (ω : Fin d ⊕ Fin d → ℝ) :
    let w := (complexToRealPi (Fin d)).symm ω
    Sum.elim xy ω ∈ divClusterLocus D t₀ c G ↔
      Sum.elim xy ω ∈ D ∧
      (∀ i : Fin d, (c i (xy ∘ Sum.inl) : ℂ) =
        (∏ j : Fin d, (X - C (w j - t₀))).coeff (i : ℕ)) ∧
      ∀ (j : Fin d) (S : Finset (Fin d)), (∀ l ∈ S, w l = w j) → ∀ k : Fin d, (k : ℕ) < S.card →
        verticalIteratedDeriv G (k : ℕ)
          (Sum.elim (fun s ↦ (xy (.inl s) : ℂ)) (fun _ ↦ w j)) =
          ∑ i : Fin d, (xy (.inr i) : ℂ) * ((i : ℕ).descFactorial (k : ℕ) : ℂ) *
            (w j - t₀) ^ ((i : ℕ) - (k : ℕ)) := by
  intro w
  set a : RootClusterIdx σ d → ℝ := Sum.elim xy ω
  have hw : rootClusterOf σ a = w := by simp [a, w, rootClusterOf, Sum.elim_comp_inr]
  have hslice (j : Fin d) :
      slicePointOf σ j a = Sum.elim (fun s ↦ (xy (.inl s) : ℂ)) (fun _ ↦ w j) := by
    simp [slicePointOf, hw, a]
  have hcl_iff (j : Fin d) (S : Finset (Fin d)) :
      (a ∈ ⋂ l : Fin d, {a | l ∈ S → rootClusterOf σ a l = rootClusterOf σ a j}) ↔
      ∀ l ∈ S, w l = w j := by
    simp [hw]
  constructor
  · rintro ⟨⟨haD, hvieta⟩, hjet⟩
    refine ⟨haD, fun i ↦ by simpa [a, hw, Function.comp_def] using (mem_iInter.1 hvieta i).2,
      fun j S hS k hk ↦ ?_⟩
    rcases mem_iInter.1 (mem_iInter.1 hjet j) S with hnot | hk_eq
    · exact False.elim (hnot ((hcl_iff j S).2 hS))
    · simpa [a, hw, hslice] using (mem_iInter.1 hk_eq k hk).2
  · rintro ⟨haD, hvieta, hjet⟩
    refine ⟨⟨haD, mem_iInter.2 fun i ↦
        ⟨haD, by simpa [a, hw, Function.comp_def] using hvieta i⟩⟩,
      mem_iInter.2 fun j ↦ mem_iInter.2 fun S ↦ ?_⟩
    by_cases hS : ∀ l ∈ S, w l = w j
    · exact Or.inr (mem_iInter.2 fun k hk ↦
        ⟨haD, by simpa [a, hw, hslice] using hjet j S hS k hk⟩)
    · exact Or.inl (mt (hcl_iff j S).1 hS)

end AuxNoFintype

section AuxFintype

variable {σ : Type*} [Fintype σ]

/-- Combining parameter and vertical coordinates `(x, t) ↦ Sum.elim x (fun _ ↦ t)` is analytic. -/
private theorem analyticAt_sumElim_prod {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (x₀ : σ → 𝕜) (t₀ : 𝕜) :
    AnalyticAt 𝕜 (fun q : (σ → 𝕜) × 𝕜 ↦ Sum.elim q.1 (fun _ : Unit ↦ q.2)) (x₀, t₀) :=
  analyticAt_pi_iff.2 <| Sum.rec
    (fun i ↦ ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i).analyticAt x₀).comp_of_eq
      analyticAt_fst rfl)
    (fun _ ↦ analyticAt_snd)

/-- Splitting `p : σ ⊕ Unit → 𝕜` into `(p ∘ Sum.inl, p (Sum.inr ()))` is analytic. -/
private theorem analyticAt_prod_comp_inl_inr {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (p₀ : σ ⊕ Unit → 𝕜) :
    AnalyticAt 𝕜 (fun p : σ ⊕ Unit → 𝕜 ↦ (p ∘ Sum.inl, p (Sum.inr ()))) p₀ :=
  (analyticAt_pi_iff.2 fun i ↦
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ⊕ Unit ↦ 𝕜) (.inl i)).analyticAt p₀).prod
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ⊕ Unit ↦ 𝕜) (.inr ())).analyticAt p₀)

/-- Reindexing coordinates along an equivalence is analytic. -/
private theorem analyticAt_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (y₀ : β → ℝ) : AnalyticAt ℝ (fun y : β → ℝ ↦ y ∘ e) y₀ :=
  analyticAt_pi_iff.2 fun a ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : β ↦ ℝ) (e a)).analyticAt y₀

/-- Identifies `(Fin (Fintype.card σ) → ℝ) × ℝ` with `σ ⊕ Unit → ℝ` via `Fintype.equivFin σ`. -/
private noncomputable def finProdToSumArrow (σ : Type*) [Fintype σ]
    (q : (Fin (Fintype.card σ) → ℝ) × ℝ) : σ ⊕ Unit → ℝ :=
  Sum.elim (q.1 ∘ Fintype.equivFin σ) (fun _ ↦ q.2)

/-- Inverse coordinate map `σ ⊕ Unit → ℝ` to `(Fin (Fintype.card σ) → ℝ) × ℝ`. -/
private noncomputable def sumArrowToFinProd (σ : Type*) [Fintype σ]
    (p : σ ⊕ Unit → ℝ) : (Fin (Fintype.card σ) → ℝ) × ℝ :=
  (p ∘ Sum.inl ∘ (Fintype.equivFin σ).symm, p (.inr ()))

private theorem analyticAt_finProdToSumArrow (q₀ : (Fin (Fintype.card σ) → ℝ) × ℝ) :
    AnalyticAt ℝ (finProdToSumArrow σ) q₀ :=
  analyticAt_pi_iff.2 fun idx ↦ by
    cases idx with
    | inl s =>
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
        (Fintype.equivFin σ s)).analyticAt q₀.1).comp_of_eq analyticAt_fst rfl
    | inr _ => exact analyticAt_snd

private theorem analyticAt_sumArrowToFinProd (p₀ : σ ⊕ Unit → ℝ) :
    AnalyticAt ℝ (sumArrowToFinProd σ) p₀ :=
  (analyticAt_pi_iff.2 fun j ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ)
      (.inl ((Fintype.equivFin σ).symm j))).analyticAt p₀).prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (.inr ())).analyticAt p₀)

private theorem finProdToSumArrow_sumArrowToFinProd (p : σ ⊕ Unit → ℝ) :
    finProdToSumArrow σ (sumArrowToFinProd σ p) = p := by
  ext (s | ⟨⟩) <;> simp [finProdToSumArrow, sumArrowToFinProd]

/-- Vertical slice `ζ ↦ H (Sum.elim z_x (fun _ ↦ ζ))` is analytic on `ball w₀ R` if `H` is analytic
at every `(z_x, ζ)` for `ζ ∈ ball w₀ R`. -/
private theorem analyticOnNhd_verticalSlice {H : (σ ⊕ Unit → ℂ) → ℂ} {z_x : σ → ℂ} {w₀ : ℂ}
    {R : ℝ} (hH : ∀ ζ ∈ ball w₀ R, AnalyticAt ℂ H (Sum.elim z_x (fun _ ↦ ζ))) :
    AnalyticOnNhd ℂ (fun ζ : ℂ ↦ H (Sum.elim z_x (fun _ ↦ ζ))) (ball w₀ R) := by
  intro ζ hζ
  have hline : AnalyticAt ℂ (fun ζ' : ℂ ↦ Sum.elim z_x (fun _ : Unit ↦ ζ')) ζ :=
    analyticAt_pi_iff.2 fun idx ↦ by
      cases idx with
      | inl _ => exact analyticAt_const
      | inr _ => exact analyticAt_id
  exact (hH ζ hζ).comp_of_eq hline rfl

/-- Complexifies a finite family of real analytic germs at `x₀`. -/
private theorem exists_complexification_pi_family {κ : Type*} [Finite κ] {x₀ : σ → ℝ}
    {c : κ → (σ → ℝ) → ℝ} (hc : ∀ i, AnalyticAt ℝ (c i) x₀) :
    ∃ c_cpx : κ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (c_cpx i) (fun j ↦ (x₀ j : ℂ))) ∧
      ∀ᶠ x in 𝓝 x₀, ∀ i, c_cpx i (fun j ↦ (x j : ℂ)) = c i x := by
  choose ρ hρ c_cpx hc_cpx hcc _ using fun i ↦ (hc i).exists_complexification
  exact ⟨c_cpx, fun i ↦ hc_cpx i _ (mem_ball_self (hρ i)),
    eventually_all.2 fun i ↦ mem_of_superset (ball_mem_nhds x₀ (hρ i)) (hcc i)⟩

/-- Analyticity of `z ↦ (monicOfCoeff (c_cpx · (z ∘ Sum.inl))).eval (z (Sum.inr ()) - w₀)`. -/
private theorem analyticAt_eval_monicOfCoeff_sumElim {d : ℕ} {z₀ : σ ⊕ Unit → ℂ} {w₀ : ℂ}
    {c_cpx : Fin d → (σ → ℂ) → ℂ} (hc_cpx : ∀ i, AnalyticAt ℂ (c_cpx i) (z₀ ∘ Sum.inl)) :
    AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦
      (Polynomial.monicOfCoeff (fun i ↦ c_cpx i (z ∘ Sum.inl))).eval (z (.inr ()) - w₀)) z₀ := by
  have hproj : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z ∘ Sum.inl) z₀ :=
    analyticAt_pi_iff.2 fun i ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inl i)).analyticAt z₀
  have hlast : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z (.inr ()) - w₀) z₀ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inr ())).analyticAt
      z₀).fun_sub analyticAt_const
  simp_rw [Polynomial.eval_monicOfCoeff]
  refine (hlast.fun_pow d).fun_add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
  exact ((hc_cpx i).comp_of_eq hproj rfl).fun_mul (hlast.fun_pow (i : ℕ))

/-- Analyticity of `z ↦ ∑ i : Fin d, r_cpx i (z ∘ Sum.inl) * (z (Sum.inr ()) - w₀) ^ i`. -/
private theorem analyticAt_sum_rem_sumElim {d : ℕ} {z₀ : σ ⊕ Unit → ℂ} {w₀ : ℂ}
    {r_cpx : Fin d → (σ → ℂ) → ℂ} (hr_cpx : ∀ i, AnalyticAt ℂ (r_cpx i) (z₀ ∘ Sum.inl)) :
    AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦
      ∑ i : Fin d, r_cpx i (z ∘ Sum.inl) * (z (.inr ()) - w₀) ^ (i : ℕ)) z₀ := by
  have hproj : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z ∘ Sum.inl) z₀ :=
    analyticAt_pi_iff.2 fun i ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inl i)).analyticAt z₀
  have hlast : AnalyticAt ℂ (fun z : σ ⊕ Unit → ℂ ↦ z (.inr ()) - w₀) z₀ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ⊕ Unit ↦ ℂ) (.inr ())).analyticAt
      z₀).fun_sub analyticAt_const
  exact Finset.analyticAt_fun_sum _ fun i _ ↦
    ((hr_cpx i).comp_of_eq hproj rfl).fun_mul (hlast.fun_pow (i : ℕ))

/-- Nashness of `p ↦ (monicOfCoeff (c · (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀)`. -/
private theorem isNashAt_eval_monicOfCoeff {d : ℕ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} (hc : ∀ i, IsNashAt (c i) x₀) :
    IsNashAt (fun p : σ ⊕ Unit → ℝ ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀))
      (Sum.elim x₀ (fun _ ↦ t₀)) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  have hproj (i : Fin d) : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦ c i (p ∘ Sum.inl)) p₀ :=
    (hc i).comp (x := p₀) (g := fun p ↦ p ∘ Sum.inl) fun s ↦ isNashAt_apply (Sum.inl s)
  have hlast : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦ p (.inr ()) - t₀) p₀ :=
    (isNashAt_apply (Sum.inr ())).fun_sub (isNashAt_const t₀)
  have hsum : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦
      ∑ i : Fin d, c i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) p₀ := by
    have hfn : (∑ i : Fin d, fun p : σ ⊕ Unit → ℝ ↦
        c i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) =
      fun p ↦ ∑ i : Fin d, c i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by ext p; simp
    exact hfn ▸ Finset.isNashAt_sum (Finset.univ : Finset (Fin d)) fun i _ ↦
      (hproj i).fun_mul (hlast.fun_pow (i : ℕ))
  simp_rw [Polynomial.eval_monicOfCoeff]
  exact (hlast.fun_pow d).fun_add hsum

/-- Nashness of `p ↦ ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ i`. -/
private theorem isNashAt_sum_rem {d : ℕ} {x₀ : σ → ℝ} {t₀ : ℝ}
    {r : Fin d → (σ → ℝ) → ℝ} (hr : ∀ i, IsNashAt (r i) x₀) :
    IsNashAt (fun p : σ ⊕ Unit → ℝ ↦
      ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ))
      (Sum.elim x₀ (fun _ ↦ t₀)) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  have hproj (i : Fin d) : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦ r i (p ∘ Sum.inl)) p₀ :=
    (hr i).comp (x := p₀) (g := fun p ↦ p ∘ Sum.inl) fun s ↦ isNashAt_apply (Sum.inl s)
  have hlast : IsNashAt (fun p : σ ⊕ Unit → ℝ ↦ p (.inr ()) - t₀) p₀ :=
    (isNashAt_apply (Sum.inr ())).fun_sub (isNashAt_const t₀)
  have hfn : (∑ i : Fin d, fun p : σ ⊕ Unit → ℝ ↦
      r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) =
    fun p ↦ ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by ext p; simp
  exact hfn ▸ Finset.isNashAt_sum (Finset.univ : Finset (Fin d)) fun i _ ↦
    (hproj i).fun_mul (hlast.fun_pow (i : ℕ))

/-- Membership of `(x_ℂ, ζ)` in the complex `L^∞` ball of radius `R` around `(x₀, t₀)`. -/
private theorem sumElim_ofReal_mem_ball {x₀ x : σ → ℝ} {t₀ : ℝ} {ζ : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : dist x x₀ < R) (hζ : ζ ∈ ball (t₀ : ℂ) R) :
    Sum.elim (fun s : σ ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ) ∈
      ball (fun idx ↦ ((Sum.elim x₀ (fun _ : Unit ↦ t₀) : σ ⊕ Unit → ℝ) idx : ℂ)) R := by
  refine mem_ball.2 ((dist_pi_lt_iff hR).2 <| Sum.rec (fun s ↦ ?_) (fun _ ↦ mem_ball.1 hζ))
  simpa [Complex.isometry_ofReal.dist_eq] using (dist_le_pi_dist x x₀ s).trans_lt hx

/-! ### Complex vertical slice jets of Nash germs -/

/-- `verticalIteratedDeriv F k` is holomorphic wherever `F` is. -/
private theorem analyticAt_verticalIteratedDeriv {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ ⊕ Unit → ℂ}
    (hF : AnalyticAt ℂ F z₀) (k : ℕ) :
    AnalyticAt ℂ (verticalIteratedDeriv F k) z₀ := by
  have hF_prod : AnalyticAt ℂ (fun q : (σ → ℂ) × ℂ ↦ F (Sum.elim q.1 (fun _ ↦ q.2)))
      (z₀ ∘ Sum.inl, z₀ (.inr ())) :=
    hF.comp_of_eq (analyticAt_sumElim_prod _ _) (by ext (_ | _) <;> rfl)
  exact (hF_prod.iteratedDeriv_snd k).comp_of_eq (analyticAt_prod_comp_inl_inr z₀) rfl

/-- On real points near `p₀`, `verticalIteratedDeriv F k` agrees with the real vertical
iterated derivative of `f`. -/
private theorem verticalIteratedDeriv_eventually_real {f : (σ ⊕ Unit → ℝ) → ℝ}
    {p₀ : σ ⊕ Unit → ℝ} (hf : AnalyticAt ℝ f p₀) {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun s ↦ (p₀ s : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 p₀, F (fun s ↦ (y s : ℂ)) = f y) (k : ℕ) :
    ∀ᶠ y in 𝓝 p₀, verticalIteratedDeriv F k (fun s ↦ (y s : ℂ)) =
      iteratedDeriv k (fun t : ℝ ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ t))) (y (.inr ())) := by
  set z₀ : σ ⊕ Unit → ℂ := fun s ↦ (p₀ s : ℂ)
  obtain ⟨r₀, hr₀, hballf⟩ := Metric.mem_nhds_iff.1 hf.eventually_analyticAt
  obtain ⟨r₁, hr₁, hballF⟩ := Metric.mem_nhds_iff.1 hF.eventually_analyticAt
  obtain ⟨r₂, hr₂, hballr⟩ := Metric.mem_nhds_iff.1 hFr
  set r := min r₀ (min r₁ r₂)
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  filter_upwards [ball_mem_nhds p₀ (half_pos hr)] with y hy
  have hy_lt : dist y p₀ < r / 2 := mem_ball.1 hy
  set yℂ : σ ⊕ Unit → ℂ := fun s ↦ (y s : ℂ)
  have hf_slice : AnalyticAt ℝ (fun s : ℝ ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ s)))
      (y (.inr ())) := by
    have hyr₀ : y ∈ ball p₀ r₀ :=
      mem_ball.2 (hy_lt.trans ((half_lt_self hr).trans_le (min_le_left _ _)))
    have hline : AnalyticAt ℝ (fun s : ℝ ↦ Sum.elim (y ∘ Sum.inl) (fun _ : Unit ↦ s))
        (y (.inr ())) :=
      analyticAt_pi_iff.2 fun idx ↦ by
        cases idx with
        | inl _ => exact analyticAt_const
        | inr _ => exact analyticAt_id
    exact (hballf hyr₀).comp_of_eq hline (by ext (_ | _) <;> rfl)
  have hslice_an : AnalyticAt ℂ (fun ζ : ℂ ↦ F (Sum.elim (yℂ ∘ Sum.inl) (fun _ ↦ ζ)))
      (y (.inr ()) : ℂ) := by
    have hyz : dist yℂ z₀ < r₁ := by
      refine (dist_pi_lt_iff hr₁).2 fun idx ↦ ?_
      have hlt₁ : dist y p₀ < r₁ :=
        hy_lt.trans ((half_lt_self hr).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      simpa [yℂ, z₀, Complex.isometry_ofReal.dist_eq] using (dist_le_pi_dist y p₀ idx).trans_lt hlt₁
    have hline : AnalyticAt ℂ (fun ζ : ℂ ↦ Sum.elim (yℂ ∘ Sum.inl) (fun _ : Unit ↦ ζ))
        (y (.inr ()) : ℂ) :=
      analyticAt_pi_iff.2 fun idx ↦ by
        cases idx with
        | inl _ => exact analyticAt_const
        | inr _ => exact analyticAt_id
    exact (hballF (mem_ball.2 hyz)).comp_of_eq hline (by ext (_ | _) <;> rfl)
  have hr_le_r₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hslice_eq : (fun s : ℝ ↦ F (Sum.elim (yℂ ∘ Sum.inl) (fun _ ↦ (s : ℂ)))) =ᶠ[𝓝 (y (.inr ()))]
      Complex.ofRealCLM ∘ (fun s : ℝ ↦ f (Sum.elim (y ∘ Sum.inl) (fun _ ↦ s))) := by
    filter_upwards [ball_mem_nhds (y (.inr ())) (half_pos hr)] with s hs
    have hmem : Sum.elim (y ∘ Sum.inl) (fun _ : Unit ↦ s) ∈ ball p₀ r₂ := by
      refine mem_ball.2 ((dist_pi_lt_iff hr₂).2 <| Sum.rec (fun i ↦ ?_) (fun _ ↦ ?_))
      · exact (dist_le_pi_dist y p₀ (.inl i)).trans_lt
          (hy_lt.trans ((half_lt_self hr).trans_le hr_le_r₂))
      · calc dist s (p₀ (.inr ()))
            ≤ dist s (y (.inr ())) + dist (y (.inr ())) (p₀ (.inr ())) := dist_triangle _ _ _
          _ < r / 2 + r / 2 := add_lt_add (mem_ball.1 hs)
              ((dist_le_pi_dist y p₀ (.inr ())).trans_lt hy_lt)
          _ = r := add_halves r
          _ ≤ r₂ := hr_le_r₂
    have hcast : (Sum.elim (yℂ ∘ Sum.inl) (fun _ : Unit ↦ (s : ℂ))) =
        fun idx ↦ ((Sum.elim (y ∘ Sum.inl) (fun _ : Unit ↦ s) : σ ⊕ Unit → ℝ) idx : ℂ) := by
      ext (_ | _) <;> rfl
    simpa [Function.comp_apply, hcast] using hballr hmem
  rw [verticalIteratedDeriv, ← hslice_an.iteratedDeriv_comp_ofReal (n := k),
    hslice_eq.iteratedDeriv_eq k, Complex.ofRealCLM.iteratedDeriv_comp_left hf_slice.contDiffAt
      le_rfl]
  rfl

/-- All complex vertical slice derivatives up to order `N` of a holomorphic extension `F` of a
Nash germ `f` have semialgebraic graphs on a common open ball in doubled real coordinates. -/
private theorem exists_ball_isSemialgebraicOn_verticalIteratedDeriv {f : (σ ⊕ Unit → ℝ) → ℝ}
    {p₀ : σ ⊕ Unit → ℝ} (hf : IsNashAt f p₀) {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun s ↦ (p₀ s : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 p₀, F (fun s ↦ (y s : ℂ)) = f y) (N : ℕ) :
    ∃ ρ > 0, ∀ k ≤ N, IsSemialgebraicOn
      (fun b ↦ complexToRealPi Unit
        (fun _ ↦ verticalIteratedDeriv F k ((complexToRealPi (σ ⊕ Unit)).symm b)))
      (ball (complexToRealPi (σ ⊕ Unit) (fun s ↦ (p₀ s : ℂ))) ρ) := by
  let e := complexToRealPi (σ ⊕ Unit)
  set z₀ : σ ⊕ Unit → ℂ := fun s ↦ (p₀ s : ℂ)
  have hNash (p : Fin (N + 1) × (Unit ⊕ Unit)) :
      IsNashAt (fun b ↦ complexToRealPi Unit
        (fun _ ↦ verticalIteratedDeriv F (p.1 : ℕ) (e.symm b)) p.2) (e z₀) := by
    have hreim := (hf.iteratedDeriv_sumElim (p.1 : ℕ)).complexification_re_im
      (analyticAt_verticalIteratedDeriv hF (p.1 : ℕ))
      (verticalIteratedDeriv_eventually_real hf.analyticAt hF hFr (p.1 : ℕ))
    cases p.2 with
    | inl _ => simpa only [complexToRealPi_apply, Sum.elim_inl, e, z₀] using hreim.1
    | inr _ => simpa only [complexToRealPi_apply, Sum.elim_inr, e, z₀] using hreim.2
  obtain ⟨W, hWo, hzW, -, hGW⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hNash
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hWo (e z₀) hzW
  have hball : IsSemialgebraic (ball (e z₀) ρ) := isSemialgebraic_ball _ _
  refine ⟨ρ, hρ, fun k hk ↦ .pi hball fun s ↦ ?_⟩
  exact (hGW (⟨k, Nat.lt_succ_of_le hk⟩, s)).mono hball hB

/-! ### Semialgebraic root-cluster loci in `(x, y, ω)` coordinates -/

private theorem eval_sliceCoordPoly {d : ℕ} (j : Fin d) (a : RootClusterIdx σ d → ℝ) :
    (fun idx ↦ MvPolynomial.eval a (sliceCoordPoly σ j idx)) =
      complexToRealPi (σ ⊕ Unit) (slicePointOf σ j a) := by
  ext ((s | ⟨⟩) | (s | ⟨⟩)) <;> simp [sliceCoordPoly, slicePointOf, rootClusterOf]

/-- Semialgebraicity of the tube `{a | x(a) ∈ ball x₀ δ ∧ ∀ j, w_j(a) ∈ ball t₀ R}`. -/
private theorem isSemialgebraic_rootClusterTube {d : ℕ} (x₀ : σ → ℝ) (t₀ : ℝ) (δ R : ℝ)
    (hR : 0 < R) :
    IsSemialgebraic {a : RootClusterIdx σ d → ℝ |
      (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ ∧
        ∀ j : Fin d, rootClusterOf σ a j ∈ ball (t₀ : ℂ) R} := by
  have hballx : IsSemialgebraic
      {a : RootClusterIdx σ d → ℝ | (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ} :=
    (isSemialgebraic_ball x₀ δ).preimage_comp (Sum.inl ∘ Sum.inl)
  have hballw (j : Fin d) :
      IsSemialgebraic {a : RootClusterIdx σ d → ℝ | rootClusterOf σ a j ∈ ball (t₀ : ℂ) R} := by
    let p : MvPolynomial (RootClusterIdx σ d) ℝ :=
      (MvPolynomial.X (.inr (.inl j)) - MvPolynomial.C t₀) ^ 2 + MvPolynomial.X (.inr (.inr j)) ^ 2
    convert isSemialgebraic_eval_lt p (MvPolynomial.C (R ^ 2)) using 1
    ext a
    simp only [mem_ofPred_eq, mem_ball, dist_eq_norm, p, rootClusterOf, map_add, map_pow, map_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [← sq_lt_sq₀ (norm_nonneg _) hR.le, Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  convert hballx.inter (.iInter hballw) using 1
  ext a
  simp

/-- Pulls back a semialgebraic jet `J` along `(x, y, ω) ↦ (x_ℂ, w_j)` on a tube mapped into `W`. -/
private theorem isSemialgebraicOn_jet_comp_slice {d : ℕ} {D : Set (RootClusterIdx σ d → ℝ)}
    (hD : IsSemialgebraic D) {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {J : ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ) → (Unit ⊕ Unit → ℝ)} (hJ : IsSemialgebraicOn J W)
    (j : Fin d)
    (hmaps : ∀ a ∈ D, complexToRealPi (σ ⊕ Unit) (slicePointOf σ j a) ∈ W) :
    IsSemialgebraicOn (fun a ↦ J (complexToRealPi (σ ⊕ Unit) (slicePointOf σ j a))) D := by
  have hcomp := (hJ.comp_eval (sliceCoordPoly σ j)).mono hD fun a ha ↦ by
    simpa only [mem_preimage, eval_sliceCoordPoly] using hmaps a ha
  exact hcomp.congr fun a _ ↦ by simp [Function.comp_apply, eval_sliceCoordPoly]

/-- Semialgebraicity of `{a ∈ D | (ci (x a) : ℂ) = (∏ j, (X - C (w_j - t₀))).coeff i}` given
semialgebraicity of `ci` on `ball x₀ δ`. -/
private theorem isSemialgebraic_inter_coeff_eq_vieta {d : ℕ} {x₀ : σ → ℝ} {δ : ℝ} (t₀ : ℝ)
    {D : Set (RootClusterIdx σ d → ℝ)} (hD : IsSemialgebraic D)
    (hxD : ∀ a ∈ D, (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ)
    {ci : (σ → ℝ) → ℝ} (hci : IsSemialgebraicOn (fun x (_ : Unit) ↦ ci x) (ball x₀ δ))
    (i : Fin d) :
    IsSemialgebraic (D ∩ {a : RootClusterIdx σ d → ℝ |
      (ci (fun s ↦ a (.inl (.inl s))) : ℂ) =
        (∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀))).coeff (i : ℕ)}) := by
  let P_mv : (MvPolynomial (RootClusterIdx σ d) ℂ)[X] :=
    ∏ j : Fin d, (X - C (rootVarPoly σ j - MvPolynomial.C (t₀ : ℂ)))
  have hci_pull : IsSemialgebraicOn
      (fun a : RootClusterIdx σ d → ℝ ↦ fun _ : Unit ↦ ci (fun s ↦ a (.inl (.inl s)))) D :=
    ((hci.comp_eval fun s ↦ MvPolynomial.X (.inl (.inl s))).mono hD fun a ha ↦ by
      simpa using hxD a ha).congr fun a _ ↦ by simp [Function.comp_apply]
  have hci_cpx : IsSemialgebraicOn
      (fun a : RootClusterIdx σ d → ℝ ↦
        complexToRealPi Unit (fun _ ↦ (ci (fun s ↦ a (.inl (.inl s))) : ℂ))) D :=
    (hci_pull.sumElim (isSemialgebraicOn_const 0 hD)).congr fun a _ ↦ by
      ext (_ | _) <;> simp
  have hvieta :=
    (isSemialgebraicMap_complexToRealPi_eval (P_mv.coeff (i : ℕ))).isSemialgebraicOn hD
  convert hci_cpx.isSemialgebraic_inter_setOf_eq hvieta using 2
  ext a
  have hmap : P_mv.map (MvPolynomial.eval fun idx ↦ (a idx : ℂ)) =
      ∏ j : Fin d, (X - C (rootClusterOf σ a j - t₀)) := by
    simp [P_mv, rootVarPoly, rootClusterOf, Polynomial.map_prod]
  have hcoeff := congrArg (fun Q : ℂ[X] ↦ Q.coeff (i : ℕ)) hmap
  simp only [Polynomial.coeff_map] at hcoeff
  rw [mem_ofPred_eq, mem_ofPred_eq, ← hcoeff]
  simp [funext_iff]

private theorem isSemialgebraic_prepClusterLocus {d : ℕ} {D : Set (RootClusterIdx σ d → ℝ)}
    (hD : IsSemialgebraic D) (t₀ : ℝ) {F : (σ ⊕ Unit → ℂ) → ℂ}
    {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    (hmaps : ∀ a ∈ D, ∀ j : Fin d, complexToRealPi (σ ⊕ Unit) (slicePointOf σ j a) ∈ W)
    (hJW : ∀ k ≤ d, IsSemialgebraicOn
      (fun b ↦ complexToRealPi Unit (fun _ ↦ verticalIteratedDeriv F k
        ((complexToRealPi (σ ⊕ Unit)).symm b))) W) :
    IsSemialgebraic (prepClusterLocus D t₀ F) := by
  have hJ0 (j : Fin d) (k : ℕ) (hk : k ≤ d) :
      IsSemialgebraic (D ∩ {a | verticalIteratedDeriv F k (slicePointOf σ j a) = 0}) := by
    have hpull := isSemialgebraicOn_jet_comp_slice hD (hJW k hk) j fun a ha ↦ hmaps a ha j
    convert hpull.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const 0 hD) using 2
    ext a
    simp [funext_iff]
  refine (hD.inter (.iInter fun i ↦ isSemialgebraic_coeff_eq_vieta t₀ i)).inter
    (.iInter fun j ↦ .iInter fun S ↦ IsSemialgebraic.imp_of_const _ ?_)
  have hS_le : S.card ≤ d := S.card_le_univ.trans_eq (Fintype.card_fin d)
  have hcl : IsSemialgebraic (⋂ l : Fin d,
      if l ∈ S then {a | rootClusterOf σ a l = rootClusterOf σ a j}
      else {a | rootClusterOf σ a l = rootClusterOf σ a j}ᶜ) :=
    .iInter fun l ↦ by
      split_ifs <;> [exact isSemialgebraic_rootVar_eq l j;
        exact (isSemialgebraic_rootVar_eq l j).compl]
  exact hcl.compl.union
    ((IsSemialgebraic.iInter fun k : Fin (d + 1) ↦
      IsSemialgebraic.imp_of_const _ (hJ0 j (k : ℕ) (Nat.le_of_lt_succ k.2))).inter
      (hD.sdiff (hJ0 j S.card hS_le)))

private theorem isSemialgebraic_divClusterLocus {d : ℕ} {x₀ : σ → ℝ} {δ : ℝ} (t₀ : ℝ)
    {D : Set (RootClusterIdx σ d → ℝ)} (hD : IsSemialgebraic D)
    (hxD : ∀ a ∈ D, (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ)
    {c : Fin d → (σ → ℝ) → ℝ}
    (hc : ∀ i, IsSemialgebraicOn (fun x (_ : Unit) ↦ c i x) (ball x₀ δ))
    {G : (σ ⊕ Unit → ℂ) → ℂ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    (hmaps : ∀ a ∈ D, ∀ j : Fin d, complexToRealPi (σ ⊕ Unit) (slicePointOf σ j a) ∈ W)
    (hJW : ∀ k ≤ d, IsSemialgebraicOn
      (fun b ↦ complexToRealPi Unit (fun _ ↦ verticalIteratedDeriv G k
        ((complexToRealPi (σ ⊕ Unit)).symm b))) W) :
    IsSemialgebraic (divClusterLocus D t₀ c G) := by
  let hermitePoly (j : Fin d) (k : ℕ) : MvPolynomial (RootClusterIdx σ d) ℂ :=
    ∑ i : Fin d, MvPolynomial.X (.inl (.inr i)) * MvPolynomial.C ((i : ℕ).descFactorial k : ℂ) *
      (rootVarPoly σ j - MvPolynomial.C (t₀ : ℂ)) ^ ((i : ℕ) - k)
  have hJherm (j k : Fin d) :
      IsSemialgebraic (D ∩ {a | verticalIteratedDeriv G (k : ℕ) (slicePointOf σ j a) =
        ∑ i : Fin d, (a (.inl (.inr i)) : ℂ) * ((i : ℕ).descFactorial (k : ℕ) : ℂ) *
          (rootClusterOf σ a j - t₀) ^ ((i : ℕ) - (k : ℕ))}) := by
    have hpull := isSemialgebraicOn_jet_comp_slice hD (hJW (k : ℕ) k.2.le) j fun a ha ↦ hmaps a ha j
    have hrhs :=
      (isSemialgebraicMap_complexToRealPi_eval (hermitePoly j (k : ℕ))).isSemialgebraicOn hD
    convert hpull.isSemialgebraic_inter_setOf_eq hrhs using 2
    ext a
    simp [hermitePoly, rootVarPoly, rootClusterOf, funext_iff]
  refine (hD.inter (.iInter fun i ↦
      isSemialgebraic_inter_coeff_eq_vieta t₀ hD hxD (hc i) i)).inter
    (.iInter fun j ↦ .iInter fun S ↦ ?_)
  have hcl : IsSemialgebraic (⋂ l : Fin d,
      {a : RootClusterIdx σ d → ℝ | l ∈ S → rootClusterOf σ a l = rootClusterOf σ a j}) :=
    .iInter fun l ↦ IsSemialgebraic.imp_of_const _ (isSemialgebraic_rootVar_eq l j)
  exact hcl.compl.union (.iInter fun k ↦ IsSemialgebraic.imp_of_const _ (hJherm j k))

end AuxFintype

/-! ### Main theorems -/

section Main

variable {σ : Type*} [Fintype σ]

/-- **Automatic Nashness of the Weierstrass preparation.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash
germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`. In any real analytic Weierstrass preparation
`f (x, t) = (monicOfCoeff (c · x)).eval (t - t₀) * u (x, t)` near `p₀`, with `c i x₀ = 0` and
`u p₀ ≠ 0`, every coefficient `c i` is a Nash germ at `x₀` and the unit `u` is a Nash germ at
`p₀`. -/
theorem IsNashAt.of_weierstrassPreparation {d : ℕ} {f u : (σ ⊕ Unit → ℝ) → ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀))) (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p) :
    (∀ i, IsNashAt (c i) x₀) ∧ IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  suffices hc_nash : ∀ i, IsNashAt (c i) x₀ from
    ⟨hc_nash, hf.of_mul_eventuallyEq (isNashAt_eval_monicOfCoeff hc_nash) hu hfac
      (not_eventuallyEq_zero_eval_monicOfCoeff hc0)⟩
  -- Complexify `f`, `u`, and `c`, and lift the factorization to a complex ball around `z₀`.
  obtain ⟨rf, hrf, F, hFon, hFf, -⟩ := hf.analyticAt.exists_complexification
  obtain ⟨ru, hru, U, hUon, hUu, -⟩ := hu.exists_complexification
  obtain ⟨c_cpx, hc_an, hc_ev⟩ := exists_complexification_pi_family hc
  set z₀ : σ ⊕ Unit → ℂ := fun idx ↦ (p₀ idx : ℂ)
  have hF : AnalyticAt ℂ F z₀ := hFon z₀ (mem_ball_self hrf)
  have hU : AnalyticAt ℂ U z₀ := hUon z₀ (mem_ball_self hru)
  have hUz₀ : U z₀ ≠ 0 := by rw [hUu p₀ (mem_ball_self hru)]; exact_mod_cast hu0
  have hF_ev : ∀ᶠ y in 𝓝 p₀, F (fun s ↦ (y s : ℂ)) = f y :=
    mem_of_superset (ball_mem_nhds p₀ hrf) hFf
  have hU_ev : ∀ᶠ y in 𝓝 p₀, U (fun s ↦ (y s : ℂ)) = u y :=
    mem_of_superset (ball_mem_nhds p₀ hru) hUu
  have hc_an' : ∀ i, AnalyticAt ℂ (c_cpx i) (z₀ ∘ Sum.inl) := fun i ↦ by
    simpa [z₀, p₀, Function.comp_def] using hc_an i
  have hFfac : ∀ᶠ z in 𝓝 z₀, F z =
      (Polynomial.monicOfCoeff (fun i ↦ c_cpx i (z ∘ Sum.inl))).eval (z (.inr ()) - t₀) *
        U z := by
    refine hF.eventuallyEq_of_eventually_real
      ((analyticAt_eval_monicOfCoeff_sumElim hc_an').fun_mul hU) ?_
    have hproj : Continuous (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) :=
      continuous_pi fun s ↦ continuous_apply (Sum.inl s)
    filter_upwards [hF_ev, hU_ev, hfac, (hproj.tendsto p₀).eventually hc_ev] with p hFp hUp hp hcp
    have hcp' (i : Fin d) : c_cpx i ((fun s ↦ (p s : ℂ)) ∘ Sum.inl) = c i (p ∘ Sum.inl) := hcp i
    rw [hFp, hp, hUp]
    simp only [Polynomial.eval_monicOfCoeff, hcp']
    push_cast
    rfl
  obtain ⟨ρW, hρW, hJW⟩ := exists_ball_isSemialgebraicOn_verticalIteratedDeriv hf hF hF_ev d
  let e := complexToRealPi (σ ⊕ Unit)
  obtain ⟨R, hR, hballR⟩ := Metric.mem_nhds_iff.1 <| inter_mem
    (inter_mem hF.eventually_analyticAt (inter_mem hU.eventually_analyticAt
      (hU.continuousAt.eventually_ne hUz₀)))
    (inter_mem hFfac ((e.continuous.tendsto z₀).eventually (ball_mem_nhds (e z₀) hρW)))
  obtain ⟨δ, hδ, hballδ⟩ := Metric.mem_nhds_iff.1 <| inter_mem (ball_mem_nhds x₀ hR) <|
    inter_mem hc_ev (eventually_exists_roots_mem_ball t₀ hR (fun i ↦ (hc i).continuousAt) hc0)
  -- Eliminate the complex root cluster `w` to show `x ↦ c · x` is semialgebraic on `ball x₀ δ`.
  refine forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨AnalyticAt.pi hc, ball x₀ δ, isOpen_ball, mem_ball_self hδ, isSemialgebraicOn_iff_graph.2 ?_⟩
  let D : Set (RootClusterIdx σ d → ℝ) :=
    {a | (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ ∧
      ∀ j : Fin d, rootClusterOf σ a j ∈ ball (t₀ : ℂ) R}
  have hz_mem {x : σ → ℝ} (hx : x ∈ ball x₀ δ) {ζ : ℂ} (hζ : ζ ∈ ball (t₀ : ℂ) R) :
      Sum.elim (fun s : σ ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ) ∈ ball z₀ R :=
    sumElim_ofReal_mem_ball hR (mem_ball.1 (hballδ hx).1) hζ
  have hΦ : IsSemialgebraic (prepClusterLocus D t₀ F) :=
    isSemialgebraic_prepClusterLocus (isSemialgebraic_rootClusterTube x₀ t₀ δ R hR) t₀
      (fun a ha j ↦ (hballR (hz_mem ha.1 (ha.2 j))).2.2) hJW
  convert hΦ.setOf_exists_sumElim using 1
  ext xy
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_ofPred_eq]
  set x : σ → ℝ := xy ∘ Sum.inl
  set y : Fin d → ℝ := xy ∘ Sum.inr
  constructor
  · rintro ⟨hx, hxy⟩
    obtain ⟨-, hcx, -, w, hwR, hPw⟩ := hballδ hx
    have hw_mem (j : Fin d) : w j ∈ ball (t₀ : ℂ) R := by
      simpa [mem_ball, dist_eq_norm] using hwR j
    have hcx' : (fun i : Fin d ↦ c_cpx i (fun s ↦ (x s : ℂ))) = fun i ↦ (c i x : ℂ) := funext hcx
    have hfac_x (ζ : ℂ) (hζ : ζ ∈ ball (t₀ : ℂ) R) :
        F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) =
          (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (ζ - t₀) *
            U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) := by
      simpa only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr, hcx'] using
        (hballR (hz_mem hx hζ)).2.1
    have hF_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.1
    have hU_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.2.1
    have hcond := (eq_prod_X_sub_C_iff_iteratedDeriv (Polynomial.monic_monicOfCoeff _)
      (Polynomial.natDegree_monicOfCoeff _) hF_an hU_an
      (fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.2.2) hfac_x w hw_mem).1 hPw
    refine ⟨complexToRealPi (Fin d) w, (mem_prepClusterLocus_iff xy _).2 ?_⟩
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨⟨hx, fun j ↦ by simpa [rootClusterOf] using hw_mem j⟩, fun i ↦ ?_,
      fun j S hSne hS ↦ ?_⟩
    · rw [← hPw, Polynomial.coeff_monicOfCoeff]
      exact congrArg Complex.ofReal (congrFun hxy i).symm
    · simpa [verticalIteratedDeriv, Sum.elim_comp_inl, x] using hcond j S hSne hS
  · rintro ⟨ω, hω⟩
    obtain ⟨haD, hvieta, hjet⟩ := (mem_prepClusterLocus_iff xy ω).1 hω
    have hx : x ∈ ball x₀ δ := haD.1
    set w : Fin d → ℂ := (complexToRealPi (Fin d)).symm ω
    have hw_mem (j : Fin d) : w j ∈ ball (t₀ : ℂ) R := by
      simpa [w, rootClusterOf] using haD.2 j
    obtain ⟨-, hcx, -⟩ := hballδ hx
    have hcx' : (fun i : Fin d ↦ c_cpx i (fun s ↦ (x s : ℂ))) = fun i ↦ (c i x : ℂ) := funext hcx
    have hfac_x (ζ : ℂ) (hζ : ζ ∈ ball (t₀ : ℂ) R) :
        F (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) =
          (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (ζ - t₀) *
            U (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) := by
      simpa only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr, hcx'] using
        (hballR (hz_mem hx hζ)).2.1
    have hF_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.1
    have hU_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.2.1
    have hPw : Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ)) =
        ∏ j : Fin d, (X - C (w j - t₀)) :=
      (eq_prod_X_sub_C_iff_iteratedDeriv (Polynomial.monic_monicOfCoeff _)
        (Polynomial.natDegree_monicOfCoeff _) hF_an hU_an
        (fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1.2.2) hfac_x w hw_mem).2 fun j S hSne hS ↦ by
          simpa [verticalIteratedDeriv, Sum.elim_comp_inl, x, w] using hjet j S hSne hS
    refine ⟨hx, funext fun i ↦ Complex.ofReal_injective ?_⟩
    have hi : (y i : ℂ) = (∏ j : Fin d, (X - C (w j - t₀))).coeff (i : ℕ) := hvieta i
    rw [hi, ← hPw, Polynomial.coeff_monicOfCoeff]

/-- **The Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose that its vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite analytic order `d` at `t₀`. Then there exist Nash
coefficient germs `c : Fin d → (σ → ℝ) → ℝ` at `x₀` vanishing at `x₀` and a Nash unit germ `u` at
`p₀` nonvanishing at `p₀` such that near `p₀`,
`f p = (monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * u p`. -/
theorem IsNashAt.exists_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let x₀' : Fin (Fintype.card σ) → ℝ := x₀ ∘ e.symm
  have hφ0 : finProdToSumArrow σ (x₀', t₀) = p₀ := by
    ext (s | ⟨⟩) <;> simp [finProdToSumArrow, p₀, x₀', e]
  have hf' : AnalyticAt ℝ (fun q ↦ f (finProdToSumArrow σ q)) (x₀', t₀) :=
    hf.analyticAt.comp_of_eq (analyticAt_finProdToSumArrow (x₀', t₀)) hφ0
  have hd' : analyticOrderAt (fun t ↦ f (finProdToSumArrow σ (x₀', t))) t₀ = d := by
    have hslice : (fun t ↦ f (finProdToSumArrow σ (x₀', t))) =
        fun t ↦ f (Sum.elim x₀ (fun _ ↦ t)) := by
      ext t; congr 1; ext (s | ⟨⟩) <;> simp [finProdToSumArrow, x₀', e]
    exact hslice ▸ hd
  obtain ⟨c', u', hc', hc'0, hu', hu'0, hfac'⟩ := hf'.exists_weierstrassPreparation_real hd'
  have hψ0 : sumArrowToFinProd σ p₀ = (x₀', t₀) := by
    ext j <;> simp [sumArrowToFinProd, p₀, x₀', e]
  let c : Fin d → (σ → ℝ) → ℝ := fun i x ↦ c' i (x ∘ e.symm)
  let u : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦ u' (sumArrowToFinProd σ p)
  have hc (i : Fin d) : AnalyticAt ℝ (c i) x₀ :=
    (hc' i).comp_of_eq (analyticAt_comp_equiv e.symm x₀) rfl
  have hc0 (i : Fin d) : c i x₀ = 0 := hc'0 i
  have hu : AnalyticAt ℝ u p₀ := hu'.comp_of_eq (analyticAt_sumArrowToFinProd p₀) hψ0
  have hu0 : u p₀ ≠ 0 := by simpa [u, hψ0] using hu'0
  have hfac : f =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
    have hψ_tendsto : Tendsto (sumArrowToFinProd σ) (𝓝 p₀) (𝓝 (x₀', t₀)) :=
      hψ0 ▸ (analyticAt_sumArrowToFinProd p₀).continuousAt.tendsto
    filter_upwards [hψ_tendsto.eventually hfac'] with p hp
    rw [finProdToSumArrow_sumArrowToFinProd] at hp
    simpa [c, u, sumArrowToFinProd, e, Function.comp_assoc] using hp
  obtain ⟨hc_nash, hu_nash⟩ := hf.of_weierstrassPreparation hc hc0 hu hu0 hfac
  exact ⟨c, u, hc_nash, hc0, hu_nash, hu0, hfac⟩

/-- **Automatic Nashness of the Weierstrass division.** Let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash
germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)` and `c : Fin d → (σ → ℝ) → ℝ` be Nash germs at `x₀`
vanishing at `x₀`. In any real analytic Weierstrass division
`g p = (monicOfCoeff (c · (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
  ∑ i, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ i`
near `p₀`, the quotient `q` is a Nash germ at `p₀` and every remainder coefficient `r i` is a Nash
germ at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision_monicOfCoeff {d : ℕ} {g q : (σ ⊕ Unit → ℝ) → ℝ}
    {c r : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀))) (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  suffices hr_nash : ∀ i, IsNashAt (r i) x₀ by
    have hq_eq : (fun p ↦ g p - ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ))
        =ᶠ[𝓝 p₀] fun p ↦
          (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p :=
      hdiv.mono fun p hp ↦ by linear_combination hp
    exact ⟨(hg.fun_sub (isNashAt_sum_rem hr_nash)).of_mul_eventuallyEq
      (isNashAt_eval_monicOfCoeff hc) hq hq_eq (not_eventuallyEq_zero_eval_monicOfCoeff hc0),
      hr_nash⟩
  -- Complexify `g`, `q`, `c`, and `r`, and lift the division to a complex ball around `z₀`.
  obtain ⟨rg, hrg, G, hGon, hGg, -⟩ := hg.analyticAt.exists_complexification
  obtain ⟨rq, hrq, Q, hQon, hQq, -⟩ := hq.exists_complexification
  obtain ⟨c_cpx, hc_an, hc_ev⟩ := exists_complexification_pi_family fun i ↦ (hc i).analyticAt
  obtain ⟨r_cpx, hr_an, hr_ev⟩ := exists_complexification_pi_family hr
  set z₀ : σ ⊕ Unit → ℂ := fun idx ↦ (p₀ idx : ℂ)
  have hG : AnalyticAt ℂ G z₀ := hGon z₀ (mem_ball_self hrg)
  have hQ : AnalyticAt ℂ Q z₀ := hQon z₀ (mem_ball_self hrq)
  have hG_ev : ∀ᶠ y in 𝓝 p₀, G (fun s ↦ (y s : ℂ)) = g y :=
    mem_of_superset (ball_mem_nhds p₀ hrg) hGg
  have hQ_ev : ∀ᶠ y in 𝓝 p₀, Q (fun s ↦ (y s : ℂ)) = q y :=
    mem_of_superset (ball_mem_nhds p₀ hrq) hQq
  have hc_an' : ∀ i, AnalyticAt ℂ (c_cpx i) (z₀ ∘ Sum.inl) := fun i ↦ by
    simpa [z₀, p₀, Function.comp_def] using hc_an i
  have hr_an' : ∀ i, AnalyticAt ℂ (r_cpx i) (z₀ ∘ Sum.inl) := fun i ↦ by
    simpa [z₀, p₀, Function.comp_def] using hr_an i
  have hGdiv : ∀ᶠ z in 𝓝 z₀, G z =
      (Polynomial.monicOfCoeff (fun i ↦ c_cpx i (z ∘ Sum.inl))).eval (z (.inr ()) - t₀) * Q z +
        ∑ i : Fin d, r_cpx i (z ∘ Sum.inl) * (z (.inr ()) - t₀) ^ (i : ℕ) := by
    refine hG.eventuallyEq_of_eventually_real
      (((analyticAt_eval_monicOfCoeff_sumElim hc_an').fun_mul hQ).fun_add
        (analyticAt_sum_rem_sumElim hr_an')) ?_
    have hproj : Continuous (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) :=
      continuous_pi fun s ↦ continuous_apply (Sum.inl s)
    filter_upwards [hG_ev, hQ_ev, hdiv, (hproj.tendsto p₀).eventually hc_ev,
      (hproj.tendsto p₀).eventually hr_ev] with p hGp hQp hp hcp hrp
    have hcp' (i : Fin d) : c_cpx i ((fun s ↦ (p s : ℂ)) ∘ Sum.inl) = c i (p ∘ Sum.inl) := hcp i
    have hrp' (i : Fin d) : r_cpx i ((fun s ↦ (p s : ℂ)) ∘ Sum.inl) = r i (p ∘ Sum.inl) := hrp i
    rw [hGp, hp, hQp]
    simp only [Polynomial.eval_monicOfCoeff, hcp', hrp']
    push_cast
    rfl
  obtain ⟨ρW, hρW, hJW⟩ := exists_ball_isSemialgebraicOn_verticalIteratedDeriv hg hG hG_ev d
  obtain ⟨Uc, hUco, hxUc, -, hc_semi⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hc
  let e := complexToRealPi (σ ⊕ Unit)
  obtain ⟨R, hR, hballR⟩ := Metric.mem_nhds_iff.1 <| inter_mem hQ.eventually_analyticAt
    (inter_mem hGdiv ((e.continuous.tendsto z₀).eventually (ball_mem_nhds (e z₀) hρW)))
  obtain ⟨δ, hδ, hballδ⟩ := Metric.mem_nhds_iff.1 <| inter_mem (ball_mem_nhds x₀ hR) <|
    inter_mem (hUco.mem_nhds hxUc) <| inter_mem (inter_mem hc_ev hr_ev)
      (eventually_exists_roots_mem_ball t₀ hR (fun i ↦ (hc i).analyticAt.continuousAt) hc0)
  -- Show `x ↦ r · x` is semialgebraic on `ball x₀ δ` via Hermite interpolation on the roots.
  refine forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨AnalyticAt.pi hr, ball x₀ δ, isOpen_ball, mem_ball_self hδ, isSemialgebraicOn_iff_graph.2 ?_⟩
  let D : Set (RootClusterIdx σ d → ℝ) :=
    {a | (fun s ↦ a (.inl (.inl s))) ∈ ball x₀ δ ∧
      ∀ j : Fin d, rootClusterOf σ a j ∈ ball (t₀ : ℂ) R}
  have hz_mem {x : σ → ℝ} (hx : x ∈ ball x₀ δ) {ζ : ℂ} (hζ : ζ ∈ ball (t₀ : ℂ) R) :
      Sum.elim (fun s : σ ↦ (x s : ℂ)) (fun _ : Unit ↦ ζ) ∈ ball z₀ R :=
    sumElim_ofReal_mem_ball hR (mem_ball.1 (hballδ hx).1) hζ
  have hΨ : IsSemialgebraic (divClusterLocus D t₀ c G) :=
    isSemialgebraic_divClusterLocus t₀ (isSemialgebraic_rootClusterTube x₀ t₀ δ R hR)
      (fun _ ha ↦ ha.1)
      (fun i ↦ (hc_semi i).mono (isSemialgebraic_ball x₀ δ) fun _ hx ↦ (hballδ hx).2.1)
      (fun a ha j ↦ (hballR (hz_mem ha.1 (ha.2 j))).2.2) hJW
  convert hΨ.setOf_exists_sumElim using 1
  ext xy
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_ofPred_eq]
  set x : σ → ℝ := xy ∘ Sum.inl
  set y : Fin d → ℝ := xy ∘ Sum.inr
  constructor
  · rintro ⟨hx, hxy⟩
    obtain ⟨-, -, ⟨hcx, hrx⟩, -, w₀, hw₀R, hPw₀⟩ := hballδ hx
    have hw₀_mem (j : Fin d) : w₀ j ∈ ball (t₀ : ℂ) R := by
      simpa [mem_ball, dist_eq_norm] using hw₀R j
    have hdiv_x (ζ : ℂ) (hζ : ζ ∈ ball (t₀ : ℂ) R) :
        G (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) =
          (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (ζ - t₀) *
            Q (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) +
            ∑ i : Fin d, (r i x : ℂ) * (ζ - t₀) ^ (i : ℕ) := by
      have hcx' : (fun i : Fin d ↦ c_cpx i (fun s ↦ (x s : ℂ))) = fun i ↦ (c i x : ℂ) :=
        funext hcx
      have hrx' (i : Fin d) : r_cpx i (fun s ↦ (x s : ℂ)) = r i x := hrx i
      simpa only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr, hcx', hrx'] using
        (hballR (hz_mem hx hζ)).2.1
    have hQ_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1
    have hy_eq : (fun i : Fin d ↦ (y i : ℂ)) = fun i ↦ (r i x : ℂ) := by
      ext i; exact congrArg Complex.ofReal (congrFun hxy i).symm
    obtain ⟨w, hw_mem, hPw, hjet⟩ :=
      (eq_rem_iff_iteratedDeriv (Polynomial.monic_monicOfCoeff _) hQ_an hdiv_x
        ⟨w₀, hw₀_mem, hPw₀⟩ (fun i ↦ (y i : ℂ))).1 hy_eq
    refine ⟨complexToRealPi (Fin d) w, (mem_divClusterLocus_iff xy _).2 ?_⟩
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨⟨hx, fun j ↦ by simpa [rootClusterOf] using hw_mem j⟩,
      fun i ↦ by rw [← hPw, Polynomial.coeff_monicOfCoeff], fun j S hS k hk ↦ ?_⟩
    simpa [verticalIteratedDeriv, Sum.elim_comp_inl, x, y] using hjet j S hS k hk
  · rintro ⟨ω, hω⟩
    obtain ⟨haD, hvieta, hjet⟩ := (mem_divClusterLocus_iff xy ω).1 hω
    have hx : x ∈ ball x₀ δ := haD.1
    set w : Fin d → ℂ := (complexToRealPi (Fin d)).symm ω
    have hw_mem (j : Fin d) : w j ∈ ball (t₀ : ℂ) R := by
      simpa [w, rootClusterOf] using haD.2 j
    obtain ⟨-, -, ⟨hcx, hrx⟩, -, w₀, hw₀R, hPw₀⟩ := hballδ hx
    have hw₀_mem (j : Fin d) : w₀ j ∈ ball (t₀ : ℂ) R := by
      simpa [mem_ball, dist_eq_norm] using hw₀R j
    have hPw : Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ)) =
        ∏ j : Fin d, (X - C (w j - t₀)) := by
      have hprod_monic : (∏ j : Fin d, (X - C (w j - t₀))).Monic :=
        monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _
      have hprod_deg : (∏ j : Fin d, (X - C (w j - t₀))).natDegree = d := by
        rw [natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
        simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one]
      rw [← Polynomial.monicOfCoeff_coeff hprod_monic hprod_deg]
      congr 1
      ext i
      exact hvieta i
    have hdiv_x (ζ : ℂ) (hζ : ζ ∈ ball (t₀ : ℂ) R) :
        G (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) =
          (Polynomial.monicOfCoeff (fun i ↦ (c i x : ℂ))).eval (ζ - t₀) *
            Q (Sum.elim (fun s ↦ (x s : ℂ)) (fun _ ↦ ζ)) +
            ∑ i : Fin d, (r i x : ℂ) * (ζ - t₀) ^ (i : ℕ) := by
      have hcx' : (fun i : Fin d ↦ c_cpx i (fun s ↦ (x s : ℂ))) = fun i ↦ (c i x : ℂ) :=
        funext hcx
      have hrx' (i : Fin d) : r_cpx i (fun s ↦ (x s : ℂ)) = r i x := hrx i
      simpa only [mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_inr, hcx', hrx'] using
        (hballR (hz_mem hx hζ)).2.1
    have hQ_an := analyticOnNhd_verticalSlice fun ζ hζ ↦ (hballR (hz_mem hx hζ)).1
    have hy_eq : (fun i : Fin d ↦ (y i : ℂ)) = fun i ↦ (r i x : ℂ) :=
      (eq_rem_iff_iteratedDeriv (Polynomial.monic_monicOfCoeff _) hQ_an hdiv_x
        ⟨w₀, hw₀_mem, hPw₀⟩ (fun i ↦ (y i : ℂ))).2 ⟨w, hw_mem, hPw, fun j S hS k hk ↦ by
          simpa [verticalIteratedDeriv, Sum.elim_comp_inl, x, y, w] using hjet j S hS k hk⟩
    exact ⟨hx, funext fun i ↦ Complex.ofReal_injective (congrFun hy_eq i).symm⟩

/-- **Nash Weierstrass division by a Weierstrass polynomial.** Let `g : (σ ⊕ Unit → ℝ) → ℝ` be a
Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and let `c : Fin d → (σ → ℝ) → ℝ`
be Nash germs at `x₀` with `c i x₀ = 0`. Then there exist a Nash quotient germ `q` at `p₀` and
Nash remainder coefficient germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = (monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (Sum.inr ()) - t₀) * q p +
  ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {d : ℕ} {g : (σ ⊕ Unit → ℝ) → ℝ}
    {c : Fin d → (σ → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  set p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let x₀' : Fin (Fintype.card σ) → ℝ := x₀ ∘ e.symm
  have hφ0 : finProdToSumArrow σ (x₀', t₀) = p₀ := by
    ext (s | ⟨⟩) <;> simp [finProdToSumArrow, p₀, x₀', e]
  have hg' : AnalyticAt ℝ (fun q ↦ g (finProdToSumArrow σ q)) (x₀', t₀) :=
    hg.analyticAt.comp_of_eq (analyticAt_finProdToSumArrow (x₀', t₀)) hφ0
  let c' : Fin d → (Fin (Fintype.card σ) → ℝ) → ℝ := fun i y ↦ c i (y ∘ e)
  have hc' (i : Fin d) : AnalyticAt ℝ (c' i) x₀' :=
    (hc i).analyticAt.comp_of_eq (analyticAt_comp_equiv e x₀') (by ext s; simp [x₀', e])
  have hc'0 (i : Fin d) : c' i x₀' = 0 := by
    have hx₀ : x₀' ∘ e = x₀ := by ext s; simp [x₀', e]
    simpa [c', hx₀] using hc0 i
  obtain ⟨q', r', hq', hr', hdiv'⟩ := hg'.exists_weierstrassDivision_monicOfCoeff_real hc' hc'0
  have hψ0 : sumArrowToFinProd σ p₀ = (x₀', t₀) := by
    ext j <;> simp [sumArrowToFinProd, p₀, x₀', e]
  let q : (σ ⊕ Unit → ℝ) → ℝ := fun p ↦ q' (sumArrowToFinProd σ p)
  let r : Fin d → (σ → ℝ) → ℝ := fun i x ↦ r' i (x ∘ e.symm)
  have hq : AnalyticAt ℝ q p₀ := hq'.comp_of_eq (analyticAt_sumArrowToFinProd p₀) hψ0
  have hr (i : Fin d) : AnalyticAt ℝ (r i) x₀ :=
    (hr' i).comp_of_eq (analyticAt_comp_equiv e.symm x₀) rfl
  have hdiv : g =ᶠ[𝓝 p₀] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
    have hψ_tendsto : Tendsto (sumArrowToFinProd σ) (𝓝 p₀) (𝓝 (x₀', t₀)) :=
      hψ0 ▸ (analyticAt_sumArrowToFinProd p₀).continuousAt.tendsto
    filter_upwards [hψ_tendsto.eventually hdiv'] with p hp
    rw [finProdToSumArrow_sumArrowToFinProd] at hp
    have hcomp_p : (p ∘ Sum.inl ∘ (Fintype.equivFin σ).symm) ∘ Fintype.equivFin σ = p ∘ Sum.inl :=
      by ext s; simp
    simpa [c', q, r, sumArrowToFinProd, e, Function.comp_assoc, hcomp_p] using hp
  obtain ⟨hq_nash, hr_nash⟩ := hg.of_weierstrassDivision_monicOfCoeff hc hc0 hq hr hdiv
  exact ⟨q, r, hq_nash, hr_nash, hdiv⟩

/-- **The Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose that the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite analytic order `d` at `t₀`. Then there exist a Nash
quotient germ `q` at `p₀` and Nash remainder coefficient germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀`
such that near `p₀`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (Sum.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision {f g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end Main

end TauCeti
