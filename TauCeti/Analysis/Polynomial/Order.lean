/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.RingTheory.Polynomial.Monic.Roots

/-!
# Analytic order of polynomial evaluation

At zero, the analytic order of polynomial evaluation equals its trailing degree, including
infinite order for the zero polynomial. This connects coefficient calculations for polynomial
slices to the analytic order used in preparation theorems. At an arbitrary point, the analytic
order of a nonzero polynomial function is the root multiplicity of the polynomial there. When an
analytic function factors on a ball as `P (w - w₀) * Ψ w` with `Ψ` nonvanishing, this identifies
ordered root tuples of a split monic polynomial `P` in terms of the vanishing of iterated
derivatives at each root cluster (`Polynomial.Monic.prod_X_sub_C_eq_iff_iteratedDeriv_eq_zero`).

Dividing a power by the evaluation of the reversal of a nonzero polynomial gives a function
analytic at zero, since the reversal takes the nonzero leading coefficient there. This is the
reciprocal-coordinate form of a polynomial near infinity.
-/

public section

open Filter Metric Set Topology

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The analytic order at zero of a polynomial function is its trailing degree. -/
@[simp]
theorem analyticOrderAt_eval_zero (p : Polynomial 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) 0 = p.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp]
    simpa only [eval_zero, Pi.zero_def, trailingDegree_zero] using
      (analyticOrderAt_zero (𝕜 := 𝕜) (E := 𝕜) (z₀ := 0))
  rw [trailingDegree_eq_natTrailingDegree hp]
  have ha : AnalyticAt 𝕜 (fun t ↦ p.eval t) 0 :=
    (AnalyticOnNhd.eval_polynomial p) 0 (Set.mem_univ _)
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.2
    (fun k hk ↦ coeff_eq_zero_of_lt_natTrailingDegree hk :
      ∀ k < p.natTrailingDegree, p.coeff k = 0)
  have hq0 : q.eval 0 ≠ 0 := by
    have hc := coeff_natTrailingDegree_ne_zero.2 hp
    have hcoeff : (X ^ p.natTrailingDegree * q).coeff p.natTrailingDegree = q.coeff 0 := by
      simpa only [zero_add] using coeff_X_pow_mul q p.natTrailingDegree 0
    have heq := congrArg (fun r : Polynomial 𝕜 ↦ r.coeff p.natTrailingDegree) hq
    rw [hcoeff] at heq
    simpa only [← coeff_zero_eq_eval_zero, ← heq] using hc
  refine ha.analyticOrderAt_eq_natCast.2 ⟨fun t ↦ q.eval t,
    (AnalyticOnNhd.eval_polynomial q) 0 (Set.mem_univ _), hq0, ?_⟩
  exact Eventually.of_forall fun t ↦ by
    conv_lhs => rw [hq]
    simp only [eval_mul, eval_pow, eval_X, sub_zero, smul_eq_mul]

/-- The analytic order of a nonzero polynomial function at a point is the multiplicity of that
point as a root of the polynomial. -/
theorem analyticOrderAt_eval {p : Polynomial 𝕜} (hp : p ≠ 0) (a : 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) a = p.rootMultiplicity a := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  refine ((AnalyticOnNhd.eval_polynomial p) a (Set.mem_univ _)).analyticOrderAt_eq_natCast.2
    ⟨fun t ↦ q.eval t, (AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ _),
      fun h ↦ hq (dvd_iff_isRoot.2 h), .of_forall fun t ↦ ?_⟩
  conv_lhs => rw [hpq]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]

/-- For a polynomial `p`, the function `w ↦ w ^ n / p.reverse.eval w` is analytic at `0`: for
nonzero `p` the reversal does not vanish at `0`, where it takes the leading coefficient of `p`,
and for `p = 0` the function is identically `0`. -/
theorem analyticAt_pow_div_eval_reverse (p : Polynomial 𝕜) (n : ℕ) :
    AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ n / p.reverse.eval w) 0 := by
  by_cases hp : p = 0
  · subst hp
    simpa using analyticAt_const (v := (0 : 𝕜))
  · exact ((analyticAt_id (𝕜 := 𝕜)).pow _).div ((AnalyticOnNhd.eval_polynomial _) 0
      (Set.mem_univ _)) (eval_zero_reverse_ne_zero hp)

/-- On a ball `ball w₀ R` where an analytic function `Φ` factors as `P (w - w₀) * Ψ w` with
nonvanishing `Ψ`, an ordered tuple `z : Fin d → 𝕜` in `ball 0 R` lists the roots of the split monic
degree-`d` polynomial `P` with multiplicity if and only if for every subset `S` on which `z` takes a
single value `z j`, all derivatives of `Φ` of order `k < S.card` vanish at `w₀ + z j`. -/
theorem Monic.prod_X_sub_C_eq_iff_iteratedDeriv_eq_zero [CompleteSpace 𝕜] [CharZero 𝕜]
    {d : ℕ} {w₀ : 𝕜} {R : ℝ} {P : 𝕜[X]} (hPm : P.Monic) (hPs : P.Splits) (hPd : P.natDegree = d)
    {Φ Ψ : 𝕜 → 𝕜} (hΦ : AnalyticOnNhd 𝕜 Φ (ball w₀ R)) (hΨ : AnalyticOnNhd 𝕜 Ψ (ball w₀ R))
    (hΨ0 : ∀ w ∈ ball w₀ R, Ψ w ≠ 0) (hfac : ∀ w ∈ ball w₀ R, Φ w = P.eval (w - w₀) * Ψ w)
    {z : Fin d → 𝕜} (hz : ∀ j, ‖z j‖ < R) :
    ∏ j : Fin d, (X - C (z j)) = P ↔
      ∀ (j : Fin d) (S : Finset (Fin d)) (k : ℕ),
        k < S.card → (∀ l ∈ S, z l = z j) → iteratedDeriv k Φ (w₀ + z j) = 0 := by
  classical
  have hw_mem (j : Fin d) : w₀ + z j ∈ ball w₀ R := by simpa [dist_eq_norm] using hz j
  have hord (j : Fin d) : analyticOrderAt Φ (w₀ + z j) = P.rootMultiplicity (z j) := by
    set w : 𝕜 := w₀ + z j
    have hw : w ∈ ball w₀ R := hw_mem j
    have hsub : AnalyticAt 𝕜 (fun ζ : 𝕜 ↦ ζ - w₀) w := analyticAt_id.sub analyticAt_const
    have hsub' : deriv (fun ζ : 𝕜 ↦ ζ - w₀) w ≠ 0 := by
      rw [deriv_sub_const, deriv_id'']; exact one_ne_zero
    have hPan : AnalyticAt 𝕜 (fun ζ : 𝕜 ↦ P.eval (ζ - w₀)) w :=
      ((AnalyticOnNhd.eval_polynomial P) _ (mem_univ _)).comp hsub
    have hPord : analyticOrderAt (fun ζ : 𝕜 ↦ P.eval (ζ - w₀)) w = P.rootMultiplicity (z j) := by
      refine (analyticOrderAt_comp_of_deriv_ne_zero (f := fun ξ ↦ P.eval ξ) hsub hsub').trans ?_
      simpa [w] using analyticOrderAt_eval hPm.ne_zero (z j)
    have hΨord : analyticOrderAt Ψ w = 0 := (hΨ w hw).analyticOrderAt_eq_zero.2 (hΨ0 w hw)
    have heq : Φ =ᶠ[𝓝 w] (fun ζ : 𝕜 ↦ P.eval (ζ - w₀)) * Ψ :=
      eventually_of_mem (isOpen_ball.mem_nhds hw) hfac
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hPan (hΨ w hw), hPord, hΨord, add_zero]
  rw [hPm.prod_X_sub_C_eq_iff_forall_le_rootMultiplicity hPs hPd z]
  constructor
  · intro hrm j S k hk hS
    have hle : S.card ≤ P.rootMultiplicity (z j) :=
      (Finset.card_le_card fun l hl ↦ Finset.mem_filter.2 ⟨Finset.mem_univ l, hS l hl⟩).trans
        (hrm j)
    have hord_le : ((P.rootMultiplicity (z j) : ℕ) : ℕ∞) ≤ analyticOrderAt Φ (w₀ + z j) :=
      le_of_eq (hord j).symm
    exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hΦ _ (hw_mem j))).1 hord_le)
      k (hk.trans_le hle)
  · intro hjet j
    set S := Finset.univ.filter fun l ↦ z l = z j
    have hord_le : (S.card : ℕ∞) ≤ analyticOrderAt Φ (w₀ + z j) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hΦ _ (hw_mem j))).2 fun k hk ↦
        hjet j S k hk fun l hl ↦ (Finset.mem_filter.1 hl).2
    exact Nat.cast_le.1 (hord_le.trans_eq (hord j))

end Polynomial
