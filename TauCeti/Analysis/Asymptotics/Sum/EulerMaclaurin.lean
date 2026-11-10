/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Data.Int.Interval
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module

/-!
# The Euler–Maclaurin formula

For integers `a ≤ n`, an integer `m ≥ 1` and a function `f` that is `C^{2m}` on `[a, n]`, with
values in a real Banach space, the Euler–Maclaurin formula (DLMF 2.10.1) expresses the sum
`∑_{j=a}^n f(j)` through the integral `∫_a^n f`, the endpoint values, the odd derivatives of `f`
at the endpoints weighted by the Bernoulli numbers `B_{2s}`, and an explicit remainder integral
against the periodic Bernoulli function `B̃_{2m}(x) = B_{2m}(x - ⌊x⌋)`:

```text
∑_{j=a}^n f(j) = ∫_a^n f + ½f(a) + ½f(n)
                 + ∑_{s=1}^{m−1} B_{2s}/(2s)! (f^{(2s−1)}(n) − f^{(2s−1)}(a))
                 + ∫_a^n (B_{2m} − B̃_{2m}(x))/(2m)! f^{(2m)}(x) dx.
```

The derivatives are taken within `[a, n]`, so `f` need only be smooth on the closed interval.
This is the exact identity behind the asymptotic expansions of sums such as `∑ j^α`, `∑ 1/j`
and `∑ j log j`, whose remainders are estimated through the last integral.

The proof integrates by parts repeatedly against the Bernoulli polynomials on each unit interval
`[c, c + 1]`, using `B_k′ = k B_{k−1}` and `B_k(1) = B_k(0)` for `k ≠ 1`, and then sums over the
unit intervals of `[a, n]`, where the boundary terms telescope.

## Main results

* `Asymptotics.sum_Icc_eq_eulerMaclaurin`: the Euler–Maclaurin formula of order `2m`.

## References

* F. W. J. Olver, R. Wong, *Asymptotic Approximations*, NIST Digital Library of Mathematical
  Functions, §2.10(i), equation 2.10.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §1.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped Nat Topology

namespace Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One integration by parts against the Bernoulli polynomial `B_k(x - c) / k!` on `[c, c + 1]`,
whose antiderivative is `B_{k+1}(x - c) / (k + 1)!`. -/
private theorem integral_bernoulliFun_smul_eq {c : ℝ} {g g' : ℝ → E} (k : ℕ)
    (hg : ContinuousOn g (Icc c (c + 1))) (hg' : ContinuousOn g' (Icc c (c + 1)))
    (hgg' : ∀ x ∈ Ioo c (c + 1), HasDerivAt g (g' x) x) :
    ∫ x in c..c + 1, (bernoulliFun k (x - c) / k !) • g x =
      (bernoulliFun (k + 1) 1 / (k + 1)!) • g (c + 1) -
        (bernoulliFun (k + 1) 0 / (k + 1)!) • g c -
        ∫ x in c..c + 1, (bernoulliFun (k + 1) (x - c) / (k + 1)!) • g' x := by
  have hc : c ≤ c + 1 := by linarith
  have hu (x : ℝ) : HasDerivAt (fun x ↦ bernoulliFun (k + 1) (x - c) / (k + 1)!)
      (bernoulliFun k (x - c) / k !) x := by
    have h := ((hasDerivAt_bernoulliFun (k + 1) (x - c)).comp x
      ((hasDerivAt_id x).sub_const c)).div_const ((k + 1)! : ℝ)
    simp only [Function.comp_def, id, add_tsub_cancel_right, mul_one] at h
    convert h using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have key := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun x ↦ bernoulliFun (k + 1) (x - c) / (k + 1)!)
    (u' := fun x ↦ bernoulliFun k (x - c) / k !) (v := g) (v' := g')
    (by fun_prop) (by rwa [uIcc_of_le hc]) (fun x _ ↦ hu x)
    (by simpa [hc] using hgg') (Continuous.intervalIntegrable (by fun_prop) _ _)
    (hg'.intervalIntegrable_of_Icc hc)
  simp only [add_sub_cancel_left, sub_self] at key
  rw [key, sub_sub_cancel]

/-- Iterated integration by parts on `[c, c + 1]`: the integral of `g 0` is a sum of boundary
terms of the successive derivatives `g s` against the Bernoulli polynomials, plus the integral
of `g k` against `B_k(x - c) / k!`. -/
private theorem integral_eq_sum_add_integral_bernoulliFun {c : ℝ} {g : ℕ → ℝ → E} (k : ℕ)
    (hg : ∀ s ≤ k, ContinuousOn (g s) (Icc c (c + 1)))
    (hgg : ∀ s < k, ∀ x ∈ Ioo c (c + 1), HasDerivAt (g s) (g (s + 1) x) x) :
    ∫ x in c..c + 1, g 0 x =
      ∑ s ∈ Finset.range k, (-1 : ℝ) ^ s •
          ((bernoulliFun (s + 1) 1 / (s + 1)!) • g s (c + 1) -
            (bernoulliFun (s + 1) 0 / (s + 1)!) • g s c) +
        (-1 : ℝ) ^ k • ∫ x in c..c + 1, (bernoulliFun k (x - c) / k !) • g k x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (fun s hs ↦ hg s (by omega)) (fun s hs ↦ hgg s (by omega)),
      integral_bernoulliFun_smul_eq k (hg k (by omega)) (hg (k + 1) le_rfl) (hgg k (by omega)),
      Finset.sum_range_succ, pow_succ]
    module

omit [CompleteSpace E] in
/-- The boundary terms of the iterated integration by parts up to order `2M + 1`: the term of
order `0` gives the trapezoidal value, the odd Bernoulli numbers of index at least `3` vanish,
and the remaining terms are the even Bernoulli numbers. -/
private theorem sum_range_bernoulliFun_boundary {c : ℝ} (g : ℕ → ℝ → E) (M : ℕ) :
    ∑ s ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ s •
        ((bernoulliFun (s + 1) 1 / (s + 1)!) • g s (c + 1) -
          (bernoulliFun (s + 1) 0 / (s + 1)!) • g s c) =
      (2 : ℝ)⁻¹ • (g 0 c + g 0 (c + 1)) -
        ∑ t ∈ Finset.range M, ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
          (g (2 * t + 1) (c + 1) - g (2 * t + 1) c) := by
  induction M with
  | zero =>
    norm_num [bernoulliFun_one]
    module
  | succ M ih =>
    have hodd : bernoulli (2 * M + 3) = 0 :=
      bernoulli_eq_zero_of_odd ⟨M + 1, by ring⟩ (by omega)
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [show 2 * M + 1 + 1 + 1 = 2 * M + 3 by ring, show 2 * M + 1 + 1 = 2 * M + 2 by ring,
      bernoulliFun_endpoints_eq_of_ne_one (show 2 * M + 3 ≠ 1 by omega),
      bernoulliFun_endpoints_eq_of_ne_one (show 2 * M + 2 ≠ 1 by omega), bernoulliFun_eval_zero,
      hodd, Rat.cast_zero, zero_div, zero_smul, sub_zero, smul_zero, add_zero, pow_succ,
      pow_mul, smul_sub]
    module

/-- The Euler–Maclaurin formula of order `2m` on a unit interval `[c, c + 1]`, for a family
`g s` of successive derivatives. -/
private theorem integral_eq_eulerMaclaurin_unit {c : ℝ} {g : ℕ → ℝ → E} {m : ℕ} (hm : m ≠ 0)
    (hg : ∀ s ≤ 2 * m, ContinuousOn (g s) (Icc c (c + 1)))
    (hgg : ∀ s < 2 * m, ∀ x ∈ Ioo c (c + 1), HasDerivAt (g s) (g (s + 1) x) x) :
    ∫ x in c..c + 1, g 0 x =
      (2 : ℝ)⁻¹ • (g 0 c + g 0 (c + 1)) -
        ∑ t ∈ Finset.range (m - 1), ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
          (g (2 * t + 1) (c + 1) - g (2 * t + 1) c) -
        ∫ x in c..c + 1,
          (((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (x - c)) / (2 * m)!) • g (2 * m) x := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  have hc : c ≤ c + 1 := by linarith
  have h2 : 2 * (M + 1) = 2 * M + 1 + 1 := by ring
  have hcont : ContinuousOn (g (2 * (M + 1))) (Icc c (c + 1)) := hg _ le_rfl
  -- the constant part `B_{2m}` of the remainder kernel integrates to a boundary term
  have hftc : ∫ x in c..c + 1, ((bernoulli (2 * (M + 1)) : ℝ) / (2 * (M + 1))!) •
      g (2 * (M + 1)) x = ((bernoulli (2 * (M + 1)) : ℝ) / (2 * (M + 1))!) •
        (g (2 * M + 1) (c + 1) - g (2 * M + 1) c) := by
    rw [intervalIntegral.integral_smul, h2,
      integral_eq_sub_of_hasDerivAt_of_le hc (hg _ (by omega))
        (hgg _ (by omega)) ((h2 ▸ hcont).intervalIntegrable_of_Icc hc)]
  have hint₁ : IntervalIntegrable (fun x ↦ ((bernoulli (2 * (M + 1)) : ℝ) / (2 * (M + 1))!) •
      g (2 * (M + 1)) x) volume c (c + 1) :=
    (continuousOn_const.smul hcont).intervalIntegrable_of_Icc hc
  have hint₂ : IntervalIntegrable (fun x ↦ (bernoulliFun (2 * (M + 1)) (x - c) /
      (2 * (M + 1))!) • g (2 * (M + 1)) x) volume c (c + 1) :=
    ((Continuous.continuousOn (by fun_prop)).smul hcont).intervalIntegrable_of_Icc hc
  rw [integral_eq_sum_add_integral_bernoulliFun (2 * (M + 1)) hg hgg, h2, Finset.sum_range_succ,
    sum_range_bernoulliFun_boundary, ← h2]
  simp only [sub_div, sub_smul]
  have e₁ : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  have e₂ : (-1 : ℝ) ^ (2 * (M + 1)) = 1 := by rw [pow_mul]; norm_num
  rw [intervalIntegral.integral_sub hint₁ hint₂, hftc, e₁, e₂,
    bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero, Nat.add_sub_cancel]
  module

/-- For `k ≠ 1`, the periodic Bernoulli function `B_k(x - ⌊x⌋)` agrees with `B_k(x - z)` on the
closed interval `[z, z + 1]`, including the right endpoint, since `B_k(1) = B_k(0)`. -/
private theorem bernoulliFun_fract_eq {k : ℕ} (hk : k ≠ 1) {z : ℤ} {x : ℝ}
    (hx : x ∈ Icc (z : ℝ) (z + 1)) :
    bernoulliFun k (Int.fract x) = bernoulliFun k (x - z) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · rw [Int.fract_eq_iff.2 ⟨sub_nonneg.2 hx.1, by linarith, z, by ring⟩]
  · rw [show (z : ℝ) + 1 = ((z + 1 : ℤ) : ℝ) by push_cast; ring, Int.fract_intCast,
      show ((z + 1 : ℤ) : ℝ) - z = 1 by push_cast; ring, bernoulliFun_endpoints_eq_of_ne_one hk]

/-- **The Euler–Maclaurin formula** (DLMF 2.10.1). For integers `a ≤ n`, `m ≥ 1` and `f` of
class `C^{2m}` on `[a, n]`, with derivatives `f^{(k)}` taken within `[a, n]`, the sum
`∑_{j=a}^n f(j)` equals `∫_a^n f + ½(f(a) + f(n))`, plus the endpoint corrections
`∑_{s=1}^{m-1} B_{2s}/(2s)! (f^{(2s-1)}(n) - f^{(2s-1)}(a))`, plus the remainder
`∫_a^n (B_{2m} - B̃_{2m}(x))/(2m)! f^{(2m)}(x) dx`, where `B̃_{2m}(x) = B_{2m}(x - ⌊x⌋)` is the
periodic Bernoulli function. -/
theorem sum_Icc_eq_eulerMaclaurin {a n : ℤ} (han : a ≤ n) {m : ℕ} (hm : m ≠ 0) {f : ℝ → E}
    (hf : ContDiffOn ℝ (2 * m : ℕ) f (Icc (a : ℝ) n)) :
    ∑ j ∈ Finset.Icc a n, f j =
      (∫ x in (a : ℝ)..n, f x) + (2 : ℝ)⁻¹ • (f a + f n) +
        ∑ s ∈ Finset.Ico 1 m, ((bernoulli (2 * s) : ℝ) / (2 * s)!) •
          (iteratedDerivWithin (2 * s - 1) f (Icc (a : ℝ) n) n -
            iteratedDerivWithin (2 * s - 1) f (Icc (a : ℝ) n) a) +
        ∫ x in (a : ℝ)..n, (((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) /
          (2 * m)!) • iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = a + N := ⟨(n - a).toNat, by omega⟩
  -- the nodes `c i = a + i`, as reals
  set c : ℕ → ℝ := fun i ↦ ((a + i : ℤ) : ℝ) with hc
  have hcs (i : ℕ) : c (i + 1) = c i + 1 := by simp only [hc]; push_cast; ring
  have hc0 : c 0 = a := by simp [hc]
  have hsum : ∑ j ∈ Finset.Icc a (a + N), f j = ∑ i ∈ Finset.range (N + 1), f (c i) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map, show (a + N + 1 - a).toNat = N + 1 by omega]
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply, hc]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [hsum]
    simp [hc0]
    module
  set I := Icc (a : ℝ) ((a + N : ℤ) : ℝ)
  set D : ℕ → ℝ → E := fun s ↦ iteratedDerivWithin s f I
  set R : ℝ → E := fun x ↦ (((bernoulli (2 * m) : ℝ) - bernoulliFun (2 * m) (Int.fract x)) /
    (2 * m)!) • D (2 * m) x with hR
  have hcN : c N = ((a + N : ℤ) : ℝ) := rfl
  have hD0 : D 0 = f := iteratedDerivWithin_zero
  have hU : UniqueDiffOn ℝ I :=
    uniqueDiffOn_Icc (by push_cast; linarith [(Nat.cast_pos.2 hN : (0 : ℝ) < N)])
  have hDc (s : ℕ) (hs : s ≤ 2 * m) : ContinuousOn (D s) I :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hs) hU
  have hsub {i : ℕ} (hi : i < N) : Icc (c i) (c i + 1) ⊆ I := by
    have : ((i : ℤ) : ℝ) + 1 ≤ N := by exact_mod_cast hi
    exact Icc_subset_Icc (by simp only [hc]; push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
      (by simp only [hc]; push_cast at this ⊢; linarith)
  have hB : Continuous fun x ↦ bernoulliFun (2 * m) (Int.fract x) :=
    (continuous_bernoulliFun _).continuousOn.comp_fract''
      (bernoulliFun_endpoints_eq_of_ne_one (by omega)).symm
  have hRc : ContinuousOn R I :=
    ((continuous_const.sub hB).div_const _).continuousOn.smul (hDc _ le_rfl)
  -- the Euler–Maclaurin formula on each unit interval `[c i, c (i + 1)]`
  have hunit (i : ℕ) (hi : i < N) : ∫ x in c i..c (i + 1), f x =
      (2 : ℝ)⁻¹ • (f (c i) + f (c (i + 1))) -
        ∑ t ∈ Finset.range (m - 1), ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
          (D (2 * t + 1) (c (i + 1)) - D (2 * t + 1) (c i)) -
        ∫ x in c i..c (i + 1), R x := by
    rw [hcs, ← hD0]
    rw [integral_eq_eulerMaclaurin_unit hm (fun s hs ↦ (hDc s hs).mono (hsub hi))
      (fun s hs x hx ↦ hf.hasDerivAt_iteratedDerivWithin (by exact_mod_cast hs) hU
        (Icc_mem_nhds ((hsub hi ⟨le_rfl, by linarith⟩).1.trans_lt hx.1)
          (hx.2.trans_le (hsub hi ⟨by linarith, le_rfl⟩).2)))]
    congr 1
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by linarith)] at hx
    simp only [hR, hc, bernoulliFun_fract_eq (by omega : 2 * m ≠ 1) hx]
  have hint {F : ℝ → E} (hF : ContinuousOn F I) (i : ℕ) (hi : i < N) :
      IntervalIntegrable F volume (c i) (c (i + 1)) := by
    rw [hcs]
    exact (hF.mono (hsub hi)).intervalIntegrable_of_Icc (by linarith)
  have hglue {F : ℝ → E} (hF : ContinuousOn F I) :
      ∫ x in (a : ℝ)..((a + N : ℤ) : ℝ), F x =
        ∑ i ∈ Finset.range N, ∫ x in c i..c (i + 1), F x := by
    rw [sum_integral_adjacent_intervals (hint hF), hc0, hcN]
  have hfc : ContinuousOn f I := hD0 ▸ hDc 0 (Nat.zero_le _)
  -- sum the unit-interval formulas; the boundary terms telescope
  have htrap : ∑ i ∈ Finset.range N, (f (c i) + f (c (i + 1))) =
      (2 : ℝ) • ∑ i ∈ Finset.range (N + 1), f (c i) - (f (c 0) + f (c N)) := by
    rw [Finset.sum_add_distrib, two_smul]
    nth_rw 1 [Finset.sum_range_succ]
    rw [Finset.sum_range_succ' (fun i ↦ f (c i))]
    abel
  have htel : ∑ i ∈ Finset.range N, ∑ t ∈ Finset.range (m - 1),
      ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
        (D (2 * t + 1) (c (i + 1)) - D (2 * t + 1) (c i)) =
      ∑ t ∈ Finset.range (m - 1), ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
        (D (2 * t + 1) (c N) - D (2 * t + 1) (c 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Finset.smul_sum, Finset.sum_range_sub (fun i ↦ D (2 * t + 1) (c i))]
  have hIco : ∑ s ∈ Finset.Ico 1 m, ((bernoulli (2 * s) : ℝ) / (2 * s)!) •
      (iteratedDerivWithin (2 * s - 1) f I ((a + N : ℤ) : ℝ) -
        iteratedDerivWithin (2 * s - 1) f I a) =
      ∑ t ∈ Finset.range (m - 1), ((bernoulli (2 * t + 2) : ℝ) / (2 * t + 2)!) •
        (D (2 * t + 1) (c N) - D (2 * t + 1) (c 0)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show 2 * (1 + t) = 2 * t + 2 by ring, show 2 * t + 2 - 1 = 2 * t + 1 by omega, hc0]
  rw [hsum, hglue hfc, hglue hRc, Finset.sum_congr rfl fun i hi ↦ hunit i (Finset.mem_range.1 hi),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, htrap, htel, hIco, hc0]
  module

end Asymptotics
