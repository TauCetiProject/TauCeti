/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Data.Multiset.Filter
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Analytic order and derivative characterizations of polynomial evaluation

At zero, the analytic order of polynomial evaluation equals its trailing degree, including
infinite order for the zero polynomial. This connects coefficient calculations for polynomial
slices to the analytic order used in preparation theorems. At an arbitrary point, the analytic
order of a nonzero polynomial function (or of a shifted polynomial `t ↦ p.eval (t - t₀)`) is the
root multiplicity of the polynomial (`Polynomial.analyticOrderAt_eval`,
`Polynomial.analyticOrderAt_eval_sub`).

Over a complete characteristic-zero normed field, when `F` factors locally as
`(fun t ↦ p.eval (t - t₀)) * U` with `U` analytic and nonvanishing, the root multiplicity of
`z - t₀` in `p` is characterized by the iterated derivatives of `F` at `z`
(`Polynomial.rootMultiplicity_sub_eq_iff_iteratedDeriv`), giving a derivative criterion for a tuple
`w` to list all roots of a monic polynomial `p` with multiplicity
(`Polynomial.Monic.eq_prod_X_sub_C_iff_iteratedDeriv`) and a Hermite interpolation characterization
of polynomial division remainders (`Polynomial.Monic.eq_iff_exists_prod_X_sub_C_and_iteratedDeriv`).

Dividing a power by the evaluation of the reversal of a nonzero polynomial gives a function
analytic at zero, since the reversal takes the nonzero leading coefficient there. This is the
reciprocal-coordinate form of a polynomial near infinity.
-/

public section

open Filter Topology

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

/-- The analytic order of a shifted nonzero polynomial `t ↦ p.eval (t - t₀)` at `a` is the
multiplicity of `a - t₀` as a root of `p`. -/
theorem analyticOrderAt_eval_sub {p : Polynomial 𝕜} (hp : p ≠ 0) (t₀ a : 𝕜) :
    analyticOrderAt (fun t ↦ p.eval (t - t₀)) a = p.rootMultiplicity (a - t₀) := by
  have hcomp := ((AnalyticOnNhd.eval_polynomial p) (a - t₀) (Set.mem_univ _)).analyticOrderAt_comp
    (g := (· - t₀)) (z₀ := a) (by fun_prop)
  simpa only [Function.comp_def, sub_sub_sub_cancel_right, analyticOrderAt_id_sub_const_self,
    mul_one, analyticOrderAt_eval hp] using hcomp

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

section IteratedDeriv

variable [CharZero 𝕜] [CompleteSpace 𝕜]

/-- If `F` agrees near `z` with `(fun t ↦ p.eval (t - t₀)) * U`, where `p` is nonzero and `U` is
analytic and nonvanishing at `z`, then the multiplicity of `z - t₀` as a root of `p` is `m` if and
only if the iterated derivatives of `F` at `z` vanish below `m` and not at `m`. -/
theorem rootMultiplicity_sub_eq_iff_iteratedDeriv {p : Polynomial 𝕜} (hp : p ≠ 0) {F U : 𝕜 → 𝕜}
    {t₀ z : 𝕜} (hU : AnalyticAt 𝕜 U z) (hU₀ : U z ≠ 0)
    (hfac : F =ᶠ[𝓝 z] (fun t ↦ p.eval (t - t₀)) * U) (m : ℕ) :
    p.rootMultiplicity (z - t₀) = m ↔
      (∀ k < m, iteratedDeriv k F z = 0) ∧ iteratedDeriv m F z ≠ 0 := by
  have hanP : AnalyticAt 𝕜 (fun t ↦ p.eval (t - t₀)) z :=
    ((AnalyticOnNhd.eval_polynomial p) _ (Set.mem_univ _)).comp_of_eq (by fun_prop) rfl
  have hF : AnalyticAt 𝕜 F z := (hanP.mul hU).congr hfac.symm
  have hord : analyticOrderAt F z = p.rootMultiplicity (z - t₀) := by
    rw [analyticOrderAt_congr hfac, analyticOrderAt_mul hanP hU, analyticOrderAt_eval_sub hp,
      hU.analyticOrderAt_eq_zero.2 hU₀, add_zero]
  rw [← analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hF, hord, Nat.cast_inj]

/-- **Root-cluster characterization by iterated derivatives.** Let `p` be a monic polynomial of
degree `Fintype.card ι` and let `F` agree near each `w j` with `(fun t ↦ p.eval (t - t₀)) * U`,
where `U` is analytic and nonvanishing at each `w j`. Then `p = ∏ j, (X - C (w j - t₀))` if and only
if for every `j` and every nonempty cluster `S` representing `{l | w l = w j}`, the iterated
derivatives of `F` at `w j` vanish below `S.card` and not at `S.card`. -/
theorem Monic.eq_prod_X_sub_C_iff_iteratedDeriv {ι : Type*} [Fintype ι] {p : Polynomial 𝕜}
    (hpm : p.Monic) (hpd : p.natDegree = Fintype.card ι) {F U : 𝕜 → 𝕜} {t₀ : 𝕜} (w : ι → 𝕜)
    (hU : ∀ j, AnalyticAt 𝕜 U (w j)) (hU₀ : ∀ j, U (w j) ≠ 0)
    (hfac : ∀ j, F =ᶠ[𝓝 (w j)] (fun t ↦ p.eval (t - t₀)) * U) :
    p = ∏ j : ι, (X - C (w j - t₀)) ↔
      ∀ (j : ι) (S : Finset ι), S.Nonempty → (∀ l, l ∈ S ↔ w l = w j) →
        (∀ k < S.card, iteratedDeriv k F (w j) = 0) ∧ iteratedDeriv S.card F (w j) ≠ 0 := by
  classical
  constructor
  · rintro hp j S - hS
    have hScard : S = Finset.univ.filter fun l : ι ↦ w l - t₀ = w j - t₀ := by
      ext l
      simp [sub_left_inj, hS l]
    refine (rootMultiplicity_sub_eq_iff_iteratedDeriv hpm.ne_zero (hU j) (hU₀ j) (hfac j)
      S.card).1 ?_
    rw [hp, rootMultiplicity_prod_X_sub_C, hScard]
  · intro hcond
    have hmult (j : ι) : p.rootMultiplicity (w j - t₀) =
        (Finset.univ.filter fun l : ι ↦ w l - t₀ = w j - t₀).card := by
      set S := Finset.univ.filter fun l : ι ↦ w l - t₀ = w j - t₀
      have hne : S.Nonempty := ⟨j, by simp [S]⟩
      exact (rootMultiplicity_sub_eq_iff_iteratedDeriv hpm.ne_zero (hU j) (hU₀ j) (hfac j)
        S.card).2 (hcond j S hne fun l ↦ by simp [S, sub_left_inj])
    have hle : (Finset.univ.val.map fun l : ι ↦ w l - t₀) ≤ p.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ Finset.univ.val.map fun l : ι ↦ w l - t₀
      · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hα
        rw [Finset.univ.count_map_val, ← hmult j, count_roots]
      · rw [Multiset.count_eq_zero_of_notMem hα]
        exact Nat.zero_le _
    have hroots : p.roots = Finset.univ.val.map fun l : ι ↦ w l - t₀ :=
      (Multiset.eq_of_le_of_card_le hle ((card_roots' p).trans (by simp [hpd]))).symm
    exact eq_prod_X_sub_C_of_monic_of_roots_eq hpm (by simp [hpd]) hroots

/-- **Hermite interpolation characterization of a polynomial remainder.** Suppose `p` is monic and
splits on a set `s` as `∏ j : Fin d, (X - C (w₀ j - t₀))` with each `w₀ j ∈ s`, and suppose `G`
agrees near each point of `s` with `(fun t ↦ p.eval (t - t₀)) * Q +
fun t ↦ ∑ i : Fin d, r₀ i * (t - t₀) ^ (i : ℕ)` for `Q` analytic on `s`. Then `y = r₀` if and only
if there is a root tuple `w : Fin d → 𝕜` in `s` factoring `p` at which the iterated derivatives of
`t ↦ ∑ i : Fin d, y i * (t - t₀) ^ (i : ℕ)` below each cluster size match those of `G`. -/
theorem Monic.eq_iff_exists_prod_X_sub_C_and_iteratedDeriv {d : ℕ} {p : Polynomial 𝕜}
    (hpm : p.Monic) {s : Set 𝕜} {G Q : 𝕜 → 𝕜} {t₀ : 𝕜} (hQ : AnalyticOnNhd 𝕜 Q s)
    {r₀ : Fin d → 𝕜}
    (hdiv : ∀ ζ ∈ s, G =ᶠ[𝓝 ζ]
      (fun t ↦ p.eval (t - t₀)) * Q + fun t ↦ ∑ i : Fin d, r₀ i * (t - t₀) ^ (i : ℕ))
    (hw₀ : ∃ w₀ : Fin d → 𝕜, (∀ j, w₀ j ∈ s) ∧ p = ∏ j : Fin d, (X - C (w₀ j - t₀)))
    (y : Fin d → 𝕜) :
    y = r₀ ↔ ∃ w : Fin d → 𝕜, (∀ j, w j ∈ s) ∧ p = ∏ j : Fin d, (X - C (w j - t₀)) ∧
      ∀ (j : Fin d) (S : Finset (Fin d)), (∀ l ∈ S, w l = w j) → ∀ k < S.card,
        iteratedDeriv k G (w j) =
          ∑ i : Fin d, y i * ((i : ℕ).descFactorial k : 𝕜) * (w j - t₀) ^ ((i : ℕ) - k) := by
  classical
  have hG_jet (ζ₀ : 𝕜) (hζ₀ : ζ₀ ∈ s) (k : ℕ) (hk : k < p.rootMultiplicity (ζ₀ - t₀)) :
      iteratedDeriv k G ζ₀ =
        ∑ i : Fin d, r₀ i * ((i : ℕ).descFactorial k : 𝕜) * (ζ₀ - t₀) ^ ((i : ℕ) - k) := by
    have hanP : AnalyticAt 𝕜 (fun t ↦ p.eval (t - t₀)) ζ₀ :=
      ((AnalyticOnNhd.eval_polynomial p) _ (Set.mem_univ _)).comp_of_eq (by fun_prop) rfl
    have hanPQ : AnalyticAt 𝕜 ((fun t ↦ p.eval (t - t₀)) * Q) ζ₀ := hanP.mul (hQ ζ₀ hζ₀)
    have hPQ0 : iteratedDeriv k ((fun t ↦ p.eval (t - t₀)) * Q) ζ₀ = 0 := by
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanPQ).1 ?_ k hk
      rw [analyticOrderAt_mul hanP (hQ ζ₀ hζ₀), analyticOrderAt_eval_sub hpm.ne_zero]
      exact le_self_add
    rw [(hdiv ζ₀ hζ₀).iteratedDeriv_eq k, iteratedDeriv_add hanPQ.contDiffAt (by fun_prop), hPQ0,
      zero_add, TauCeti.iteratedDeriv_sum_mul_sub_pow]
  constructor
  · rintro rfl
    obtain ⟨w₀, hw₀s, hpw₀⟩ := hw₀
    refine ⟨w₀, hw₀s, hpw₀, fun j S hS k hk ↦ hG_jet (w₀ j) (hw₀s j) k ?_⟩
    have hsub : S ⊆ Finset.univ.filter fun l : Fin d ↦ w₀ l - t₀ = w₀ j - t₀ := fun l hl ↦ by
      simp [sub_left_inj, hS l hl]
    have hcnt : (Finset.univ.filter fun l : Fin d ↦ w₀ l - t₀ = w₀ j - t₀).card =
        p.rootMultiplicity (w₀ j - t₀) := by
      rw [hpw₀, rootMultiplicity_prod_X_sub_C]
    exact hk.trans_le ((Finset.card_le_card hsub).trans_eq hcnt)
  · rintro ⟨w, hws, hpw, hjet⟩
    set D : Polynomial 𝕜 := ∑ i : Fin d, monomial (i : ℕ) (y i - r₀ i)
    by_cases hD : D = 0
    · ext i
      have hi : D.coeff (i : ℕ) = 0 := by simp [hD]
      simp only [D, finsetSum_coeff, coeff_monomial_apply, Fin.val_inj, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] at hi
      exact sub_eq_zero.1 hi
    exfalso
    have hdeg : D.natDegree < d := by
      have hlt : D.degree < d := by
        simpa only [D, C_mul_X_pow_eq_monomial] using degree_sum_fin_lt fun i : Fin d ↦ y i - r₀ i
      exact WithBot.coe_lt_coe.1 ((degree_eq_natDegree hD).symm.trans_lt hlt)
    have hle : p.roots ≤ D.roots := by
      rw [Multiset.le_iff_count]
      intro α
      by_cases hα : α ∈ p.roots
      · rw [hpw, roots_prod_X_sub_C_map, Multiset.mem_map] at hα
        obtain ⟨j, -, rfl⟩ := hα
        rw [count_roots, count_roots]
        set S := Finset.univ.filter fun l : Fin d ↦ w l - t₀ = w j - t₀
        have hScard : p.rootMultiplicity (w j - t₀) = S.card := by
          rw [hpw, rootMultiplicity_prod_X_sub_C]
        have hanD : AnalyticAt 𝕜 (fun t ↦ D.eval (t - t₀)) (w j) :=
          ((AnalyticOnNhd.eval_polynomial D) _ (Set.mem_univ _)).comp_of_eq (by fun_prop) rfl
        have hordD : (p.rootMultiplicity (w j - t₀) : ℕ∞) ≤
            analyticOrderAt (fun t ↦ D.eval (t - t₀)) (w j) := by
          refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanD).2 fun k hk ↦ ?_
          have hy_eq := hjet j S (fun l hl ↦ sub_left_inj.1 (Finset.mem_filter.1 hl).2) k
            (hScard ▸ hk)
          have hr_eq := hG_jet (w j) (hws j) k hk
          have hDeval : (fun t : 𝕜 ↦ D.eval (t - t₀)) =
              (fun t ↦ ∑ i : Fin d, y i * (t - t₀) ^ (i : ℕ)) -
                fun t ↦ ∑ i : Fin d, r₀ i * (t - t₀) ^ (i : ℕ) := by
            ext t
            simp [D, eval_finsetSum, Finset.sum_sub_distrib]
          rw [hDeval, iteratedDeriv_sub (by fun_prop) (by fun_prop),
            TauCeti.iteratedDeriv_sum_mul_sub_pow, TauCeti.iteratedDeriv_sum_mul_sub_pow,
            ← hy_eq, ← hr_eq, sub_self]
        rw [analyticOrderAt_eval_sub hD] at hordD
        exact Nat.cast_le.1 hordD
      · rw [Multiset.count_eq_zero_of_notMem hα]
        exact Nat.zero_le _
    have hcardP : p.roots.card = d := by
      rw [hpw, roots_prod_X_sub_C_map]
      simp
    exact absurd ((hcardP ▸ Multiset.card_le_card hle).trans (card_roots' D)) (not_le_of_gt hdeg)

end IteratedDeriv

end Polynomial
