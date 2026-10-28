/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
import Mathlib.RingTheory.Int.Basic
import TauCeti.RingTheory.UniqueFactorizationDomain.SubsetProduct
import Mathlib.Tactic.LinearCombination

/-!
# United representatives of pairs of primitive forms

Dirichlet composition is defined on pairs of forms in the *united* shape `(a, B, a'C)`,
`(a', B, aC)`: the same middle coefficient, and last coefficients exchanging the leading ones.
Their composition is `(aa', B, C)`. This file proves that every pair of primitive integral forms
of the same discriminant is properly equivalent to a pair in this shape, so Dirichlet composition
is defined on all pairs of proper classes.

The argument has two steps.

* A primitive form properly represents an integer prime to any given nonzero `M`
  (`IsPrimitive.exists_isCoprime_eval`, Cox Lemma 2.25). For each prime `p ∣ M` at least one of
  `a`, `c`, `b` is prime to `p`; the value at `x = ∏ p` over the primes `p ∣ M` with `p ∣ a`,
  `p ∤ c`, and `y = ∏ p` over the primes `p ∣ M` with `p ∤ a`, is then prime to every `p ∣ M`.
* Two forms of the same discriminant with coprime leading coefficients become united after
  translations `T ^ k` and `T ^ l` (`exists_T_zpow_smul_eq_united`, the coprime case of Cox
  Lemma 3.2). The middle coefficients have the same parity, so a Bézout relation between
  the leading coefficients makes them equal; the equality `a c₁ = a' c₂` of the two products of
  outer coefficients then forces the united shape.

Moving a value prime to `a` into the leading coefficient of the second form and combining both
steps gives `exists_smul_eq_united`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, Lemma 2.25, and §3, Lemma 3.2.
-/

public section

open scoped MatrixGroups
open UniqueFactorizationMonoid

namespace TauCeti.BinaryQuadraticForm

/-! ### Values prime to a given integer -/

section CoprimeValue

/-- **A primitive form properly represents an integer prime to any given nonzero integer**
(Cox, Lemma 2.25). -/
theorem IsPrimitive.exists_isCoprime_eval {f : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive)
    {M : ℤ} (hM : M ≠ 0) : ∃ x y : ℤ, IsCoprime x y ∧ IsCoprime (f.eval x y) M := by
  classical
  -- `y` collects the primes `p ∣ M` with `p ∤ a`, and `x` those with `p ∣ a` and `p ∤ c`.
  set y := ∏ q ∈ (normalizedFactors M).toFinset.filter (fun q ↦ ¬ q ∣ f.a), q
  set x := ∏ q ∈ (normalizedFactors M).toFinset.filter (fun q ↦ q ∣ f.a ∧ ¬ q ∣ f.c), q
  have hy {p : ℤ} (hp : Prime p) : p ∣ y ↔ p ∣ M ∧ ¬ p ∣ f.a :=
    prime_dvd_prod_filter_normalizedFactors_iff hM hp _ fun h ↦ not_congr h.dvd_iff_dvd_left
  have hx {p : ℤ} (hp : Prime p) : p ∣ x ↔ p ∣ M ∧ p ∣ f.a ∧ ¬ p ∣ f.c :=
    prime_dvd_prod_filter_normalizedFactors_iff hM hp _ fun h ↦
      and_congr h.dvd_iff_dvd_left (not_congr h.dvd_iff_dvd_left)
  have hy0 : y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq ↦
    (prime_of_normalized_factor q (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1)).ne_zero
  refine ⟨x, y, isCoprime_of_prime_dvd (fun h ↦ hy0 h.2) fun p hp hpx hpy ↦
    ((hy hp).mp hpy).2 ((hx hp).mp hpx).2.1, isCoprime_of_prime_dvd (fun h ↦ hM h.2)
    fun p hp hpv hpM ↦ ?_⟩
  obtain ⟨u, v, w, huvw⟩ := hf.exists_linearCombination_eq_one
  rw [eval_def] at hpv
  by_cases ha : p ∣ f.a
  · by_cases hc : p ∣ f.c
    · -- `p` divides `a` and `c`, hence not `b`, `x` or `y`; but it divides `bxy`.
      have hpx : ¬ p ∣ x := fun h ↦ ((hx hp).mp h).2.2 hc
      have hpy : ¬ p ∣ y := fun h ↦ ((hy hp).mp h).2 ha
      have hb : p ∣ f.b * x * y :=
        (dvd_add_right (ha.mul_right _)).mp ((dvd_add_left (hc.mul_right _)).mp hpv)
      have hpb : p ∣ f.b := by
        rcases hp.dvd_or_dvd hb with h | h
        · exact (hp.dvd_or_dvd h).resolve_right hpx
        · exact absurd h hpy
      exact hp.not_dvd_one (huvw ▸ dvd_add (dvd_add (ha.mul_left u) (hpb.mul_left v))
        (hc.mul_left w))
    · -- `p` divides `a` and `x` but not `c` or `y`; but it divides `cy²`.
      have hpx : p ∣ x := (hx hp).mpr ⟨hpM, ha, hc⟩
      have hpy : ¬ p ∣ y := fun h ↦ ((hy hp).mp h).2 ha
      have h : p ∣ f.c * y ^ 2 :=
        (dvd_add_right (dvd_add (ha.mul_right _) ((hpx.mul_left f.b).mul_right y))).mp hpv
      rcases hp.dvd_or_dvd h with h | h
      · exact hc h
      · exact hpy (hp.dvd_of_dvd_pow h)
  · -- `p` divides `y` but not `a` or `x`; but it divides `ax²`.
    have hpy : p ∣ y := (hy hp).mpr ⟨hpM, ha⟩
    have hpx : ¬ p ∣ x := fun h ↦ ha ((hx hp).mp h).2.1
    have h : p ∣ f.a * x ^ 2 := (dvd_add_left (hpy.mul_left (f.b * x))).mp
      ((dvd_add_left ((hpy.pow two_ne_zero).mul_left f.c)).mp hpv)
    rcases hp.dvd_or_dvd h with h | h
    · exact ha h
    · exact hpx (hp.dvd_of_dvd_pow h)

end CoprimeValue

/-! ### United representatives -/

section United

/-- **Forms with coprime leading coefficients become united after translations** (the coprime
case of Cox, Lemma 3.2). If `f` and `g` have the same discriminant and coprime leading
coefficients, then translations `T ^ k` and `T ^ l` take them to `(f.a, B, g.a C)` and
`(g.a, B, f.a C)`. -/
theorem exists_T_zpow_smul_eq_united {f g : BinaryQuadraticForm ℤ}
    (hD : f.discrim = g.discrim) (hco : IsCoprime f.a g.a) :
    ∃ k l B C : ℤ, ModularGroup.T ^ k • f = ⟨f.a, B, g.a * C⟩ ∧
      ModularGroup.T ^ l • g = ⟨g.a, B, f.a * C⟩ := by
  have hD' : f.b ^ 2 - 4 * f.a * f.c = g.b ^ 2 - 4 * g.a * g.c := by
    simpa only [discrim_def, discrim, sq] using hD
  -- The middle coefficients have the same parity, since `b² ≡ D mod 4`.
  obtain ⟨e, he⟩ : 2 ∣ f.b - g.b := by
    have hprod : Even ((f.b - g.b) * (f.b + g.b)) :=
      ⟨2 * (f.a * f.c - g.a * g.c), by linear_combination hD'⟩
    rcases Int.even_mul.mp hprod with h | h
    · exact h.two_dvd
    · rw [show f.b - g.b = f.b + g.b - 2 * g.b by ring]
      exact (h.sub (even_two_mul g.b)).two_dvd
  -- A Bézout relation `u a + v a' = 1` equalizes the translated middle coefficients.
  have ⟨u, v, huv⟩ := hco
  have hb : f.b - 2 * f.a * (u * e) = g.b - 2 * g.a * -(v * e) := by
    linear_combination he - 2 * e * huv
  -- Equal discriminants and middle coefficients give `a c₁ = a' c₂`, hence the united shape.
  have hac : f.a * (f.a * (u * e) ^ 2 - f.b * (u * e) + f.c) =
      g.a * (g.a * (-(v * e)) ^ 2 - g.b * -(v * e) + g.c) :=
    mul_left_cancel₀ four_ne_zero <| by
      linear_combination (f.b - 2 * f.a * (u * e) + (g.b - 2 * g.a * -(v * e))) * hb - hD'
  -- Coprimality splits the common value `a c₁ = a' c₂` as `a a' C`; cancel the nonzero factor.
  obtain ⟨C, hc, hC⟩ : ∃ C, f.a * (u * e) ^ 2 - f.b * (u * e) + f.c = g.a * C ∧
      g.a * (-(v * e)) ^ 2 - g.b * -(v * e) + g.c = f.a * C := by
    rcases eq_or_ne f.a 0 with ha | ha
    · have hga : g.a ≠ 0 := fun h ↦ not_isCoprime_zero_zero (ha ▸ h ▸ hco)
      obtain ⟨C, hc⟩ := hco.symm.dvd_of_dvd_mul_left ⟨_, hac⟩
      exact ⟨C, hc, mul_left_cancel₀ hga (by rw [← hac, hc]; ring)⟩
    · obtain ⟨C, hC⟩ := hco.dvd_of_dvd_mul_left ⟨_, hac.symm⟩
      exact ⟨C, mul_left_cancel₀ ha (by rw [hac, hC]; ring), hC⟩
  refine ⟨u * e, -(v * e), f.b - 2 * f.a * (u * e), C, ?_, ?_⟩
  · rw [T_zpow_smul, hc]
  · rw [T_zpow_smul, ← hb, ← hC]

/-- **Every pair of primitive forms of the same discriminant has united representatives.** Two
primitive integral forms of the same discriminant are properly equivalent to forms
`(a, B, a'C)` and `(a', B, aC)` with `a` and `a'` coprime. The Dirichlet composition of these
representatives is `(aa', B, C)`. -/
theorem exists_smul_eq_united {f g : BinaryQuadraticForm ℤ} (hf : f.IsPrimitive)
    (hg : g.IsPrimitive) (hD : f.discrim = g.discrim) :
    ∃ (γ δ : SL(2, ℤ)) (a a' B C : ℤ), IsCoprime a a' ∧
      γ • f = ⟨a, B, a' * C⟩ ∧ δ • g = ⟨a', B, a * C⟩ := by
  -- First move an odd, hence nonzero, value of `f` into its leading coefficient.
  obtain ⟨x, y, hxy, h2⟩ := hf.exists_isCoprime_eval two_ne_zero
  obtain ⟨γ, hγ⟩ := f.exists_smul_a_eq_eval hxy
  have ha : (γ • f).a ≠ 0 := by
    rw [hγ]
    rintro h
    rw [h, isCoprime_zero_left, Int.isUnit_iff] at h2
    omega
  -- Then move a value of `g` prime to that coefficient into the leading coefficient of `g`.
  obtain ⟨x', y', hxy', hco⟩ := hg.exists_isCoprime_eval ha
  obtain ⟨δ, hδ⟩ := g.exists_smul_a_eq_eval hxy'
  rw [← hδ] at hco
  obtain ⟨k, l, B, C, hk, hl⟩ :=
    exists_T_zpow_smul_eq_united (by simpa using hD) hco.symm
  exact ⟨ModularGroup.T ^ k * γ, ModularGroup.T ^ l * δ, _, _, B, C, hco.symm,
    by rw [mul_smul, hk], by rw [mul_smul, hl]⟩

end United

end TauCeti.BinaryQuadraticForm
