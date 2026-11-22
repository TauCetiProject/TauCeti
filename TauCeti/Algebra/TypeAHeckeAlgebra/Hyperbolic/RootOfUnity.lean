/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.RootOfUnity
import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Wenzl
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Root-of-unity hyperbolic Markov trace parameters

In `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic`, at the Hecke parameter `q = exp (-θ)` and
rescaled braid generators `γ i = I * exp (-α) • T i`, the positive and negative stabilization
constants of a Markov trace with native projection parameter `η` agree (for `cosh α * cosh θ ≠ 0`)
if and only if `η = (1 - tanh α * tanh θ) / 2` (`TauCeti.hyperbolicProjParam`), while Wenzl's
complementary projection convention assigns `η_W = 1 - η = (1 + tanh α * tanh θ) / 2`
(`TauCeti.hyperbolicWenzlProjParam`).

This file specializes the exceptional-line hyperbolic dictionary
(`TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Wenzl`) to the root-of-unity exceptional points
`θ = π * I / l` and `α = (k / l + 1 / 2) * π * I = k * θ + π * I / 2` (`l ≥ 3`, `0 < k < l`,
`Q = exp (-2 * π * I / l)`):

* Specializing `hyperbolicProjParam_mul_add_pi_mul_I_div_two` gives the native parameter
  `a_(-k)(Q)` and Wenzl parameter `a_k(Q)`.
* Replacing `k` by `l - k` exchanges the two projection conventions, `k = m` at `l = 2 * m` gives
  `1 / 2`, and `k ∈ {1, l - 1}` (all of `l = 3`) gives scalar endpoints `{0, 1}` whereas
  `2 ≤ k ≤ l - 2` (`l ≥ 4`) lies strictly in `(0, 1)`.

## Main results

* `TauCeti.wenzlParam_neg_two_hyperbolicHeckeParam_rootOfUnity_sq`: the squared-cosine Jones
  parameter `a_(-2)(q ^ 2) = (4 * cos (π / l) ^ 2)⁻¹` at `θ = π * I / l`.
* `TauCeti.hyperbolicProjParam_rootOfUnity`, `TauCeti.hyperbolicWenzlProjParam_rootOfUnity`,
  `TauCeti.hyperbolicProjParam_rootOfUnity_sub`,
  `TauCeti.hyperbolicWenzlProjParam_rootOfUnity_sub`,
  `TauCeti.hyperbolicProjParam_rootOfUnity_middle`,
  `TauCeti.exists_mem_Ioo_hyperbolicProjParam_rootOfUnity_iff`, and
  `TauCeti.hyperbolicProjParam_rootOfUnity_mem_pair_iff`: the root-of-unity exceptional point
  values, complementary states, middle value, and separation of scalar endpoints from `(0, 1)`
  interior parameters.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff_wenzl`:
  the Markov trace characterizations at the root-of-unity exceptional points.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5–6, 11.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- **Squared-cosine Jones parameter at `θ = π * I / l`.** For
`q = hyperbolicHeckeParam (π * I / l)` (so `Q = q ^ 2 = exp (-2 * π * I / l)`), the Jones parameter
`a_(-2)(Q)` is `(4 * cos (π / l) ^ 2)⁻¹` for every `l : ℕ`. -/
theorem wenzlParam_neg_two_hyperbolicHeckeParam_rootOfUnity_sq (l : ℕ) :
    wenzlParam (-2) ((hyperbolicHeckeParam (π * I / l) : ℂ) ^ 2) =
      (((4 * Real.cos (π / l) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have harg : -2 * ((π : ℂ) * I / l) = -(2 * (π / (l : ℂ)) * I) := by ring
  rw [val_hyperbolicHeckeParam_sq, harg, wenzlParam_exp_neg, wenzlParam_neg_two_exp_mul_I,
    ← ofReal_natCast, ← ofReal_div, ← ofReal_cos]
  norm_cast

private theorem rootOfUnity_alpha_eq (l k : ℕ) :
    ((k : ℂ) / l + 1 / 2) * π * I = (k : ℤ) * (π * I / l) + π * I / 2 := by
  push_cast
  ring

private theorem neg_two_mul_pi_mul_I_div (l : ℕ) :
    -2 * (π * I / (l : ℂ)) = -(2 * π * I / l) := by
  ring

/-- **Native projection parameter at the root-of-unity exceptional points.** For `l ≥ 3` and
`0 < k < l`, at `θ = π * I / l` and `α = (k / l + 1 / 2) * π * I = k * θ + π * I / 2`,
specializing `hyperbolicProjParam_mul_add_pi_mul_I_div_two` identifies the native parameter
`hyperbolicProjParam α θ` with `a_(-k)(exp (-2 * π * I / l))`. -/
theorem hyperbolicProjParam_rootOfUnity {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  have hθ : cosh (π * I / l) ≠ 0 := by
    rw [← ofReal_natCast]
    exact cosh_pi_mul_I_div_ne_zero (by exact_mod_cast (by omega : 2 < l))
  have hk : sinh ((k : ℤ) * (π * I / l)) ≠ 0 := by
    simpa using sinh_ofReal_mul_pi_mul_I_div_ne_zero (Nat.cast_pos.2 hk₀) (Nat.cast_lt.2 hkl)
  rw [rootOfUnity_alpha_eq, hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ hk,
    neg_two_mul_pi_mul_I_div]

/-- **Wenzl projection parameter at the root-of-unity exceptional points.** For `l ≥ 3` and
`0 < k < l`, at `θ = π * I / l` and `α = (k / l + 1 / 2) * π * I`, Wenzl's parameter
`hyperbolicWenzlProjParam α θ = 1 - hyperbolicProjParam α θ` equals
`a_k(exp (-2 * π * I / l))`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) := by
  have hsum := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl
  rw [hyperbolicWenzlProjParam_eq_one_sub, hyperbolicProjParam_rootOfUnity hl hk₀ hkl]
  simp only [wenzlParam_exp_neg]
  linear_combination -hsum

/-- **Complementary state `l - k` at the roots of unity (Wenzl convention).** Replacing `k` by
`l - k` in `{1, ..., l - 1}` exchanges Wenzl's parameter with the native parameter at `k`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_sub {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicWenzlProjParam ((((l - k : ℕ) : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl (by omega) (by omega),
    hyperbolicProjParam_rootOfUnity hl hk₀ hkl,
    wenzlParam_sub_exp_neg_two_pi_mul_I_div (by omega) hkl.le]

/-- **Complementary state `l - k` at the roots of unity (native convention).** Replacing `k` by
`l - k` in `{1, ..., l - 1}` exchanges the native parameter with Wenzl's parameter at `k`. -/
theorem hyperbolicProjParam_rootOfUnity_sub {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicProjParam ((((l - k : ℕ) : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) := by
  have h := hyperbolicWenzlProjParam_rootOfUnity_sub (l := l) (k := l - k) hl
    (by omega) (by omega)
  rw [Nat.sub_sub_self hkl.le] at h
  exact h.symm

/-- **Middle value at even `l = 2 * m`.** For every `m : ℕ`, the native root-of-unity
exceptional parameter at `l = 2 * m` and `k = m` is `1 / 2`. -/
theorem hyperbolicProjParam_rootOfUnity_middle (m : ℕ) :
    hyperbolicProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  rw [hyperbolicProjParam_def]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hα : ((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I = π * I := by
      push_cast
      field_simp [hmC]
      ring
    have htanh : tanh (π * I) = 0 := by
      simpa using tanh_add_pi_mul_I 0
    rw [hα, htanh, zero_mul, sub_zero]

/-- **Middle value at even `l = 2 * m` (Wenzl convention).** For every `m : ℕ`, Wenzl's
root-of-unity exceptional parameter at `l = 2 * m` and `k = m` is `1 / 2`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_middle (m : ℕ) :
    hyperbolicWenzlProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  rw [hyperbolicWenzlProjParam_eq_one_sub, hyperbolicProjParam_rootOfUnity_middle m]
  norm_num

/-- **Nontrivial `(0, 1)` interior characterization at the roots of unity (Wenzl convention).**
For `l ≥ 3` and `0 < k < l`, Wenzl's root-of-unity parameter lies strictly in `(0, 1)` if and only
if `2 ≤ k` and `k + 2 ≤ l`. -/
theorem exists_mem_Ioo_hyperbolicWenzlProjParam_rootOfUnity_iff {l k : ℕ} (hl : 3 ≤ l)
    (hk₀ : 0 < k) (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1,
      hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) = η) ↔
        2 ≤ k ∧ k + 2 ≤ l := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl, wenzlParam_exp_neg,
    exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff hl hk₀ hkl]

/-- **Nontrivial `(0, 1)` interior characterization at the roots of unity (native convention).**
For `l ≥ 3` and `0 < k < l`, the native root-of-unity parameter lies strictly in `(0, 1)` if and
only if `2 ≤ k` and `k + 2 ≤ l` (hence `l ≥ 4`). -/
theorem exists_mem_Ioo_hyperbolicProjParam_rootOfUnity_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1,
      hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) = η) ↔
        2 ≤ k ∧ k + 2 ≤ l := by
  rw [← hyperbolicWenzlProjParam_rootOfUnity_sub hl hk₀ hkl,
    exists_mem_Ioo_hyperbolicWenzlProjParam_rootOfUnity_iff hl (by omega) (by omega)]
  omega

/-- **Scalar-endpoint `{0, 1}` characterization at the roots of unity (Wenzl convention).** For
`l ≥ 3` and `0 < k < l`, Wenzl's root-of-unity parameter belongs to `{0, 1}` if and only if
`k = 1` or `k + 1 = l`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) ∈ ({0, 1} : Set ℂ) ↔
      k = 1 ∨ k + 1 = l := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl, wenzlParam_exp_neg,
    wenzlParam_exp_two_pi_mul_I_div_mem_pair_iff hl hk₀ hkl]

/-- **Scalar-endpoint `{0, 1}` characterization at the roots of unity (native convention).** For
`l ≥ 3` and `0 < k < l`, the native root-of-unity parameter belongs to `{0, 1}` if and only if
`k = 1` or `k + 1 = l` (which covers every `0 < k < 3` when `l = 3`). -/
theorem hyperbolicProjParam_rootOfUnity_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) ∈ ({0, 1} : Set ℂ) ↔
      k = 1 ∨ k + 1 = l := by
  rw [← hyperbolicWenzlProjParam_rootOfUnity_sub hl hk₀ hkl,
    hyperbolicWenzlProjParam_rootOfUnity_mem_pair_iff hl (by omega) (by omega)]
  omega

namespace InfiniteTypeAHeckeAlgebra

/-- **Markov trace characterization at the root-of-unity exceptional points (native convention).**
For `l ≥ 3` and `0 < k < l`, on the Hecke algebra at `θ = π * I / l` (`Q = exp (-2 * π * I / l)`),
a Markov trace with native projection parameter `η` has equal stabilization constants at
`α = (k / l + 1 / 2) * π * I` if and only if `η = a_(-k)(Q)`. -/
theorem IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) {z η : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam (π * I / l)) →ₗ[ℂ] ℂ}
    (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-(π * I / l)) * η - exp (π * I / l) * (1 - η)) (n : ℕ) :
    τ (hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n) =
        τ ↑(hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n)⁻¹ ↔
      η = wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  have hθ : cosh (π * I / l) ≠ 0 := by
    rw [← ofReal_natCast]
    exact cosh_pi_mul_I_div_ne_zero (by exact_mod_cast (by omega : 2 < l))
  have hk : sinh ((k : ℤ) * (π * I / l)) ≠ 0 := by
    simpa using sinh_ofReal_mul_pi_mul_I_div_ne_zero (Nat.cast_pos.2 hk₀) (Nat.cast_lt.2 hkl)
  rw [rootOfUnity_alpha_eq, hτ.map_hyperbolicGen_line_eq_iff hz hθ hk n,
    neg_two_mul_pi_mul_I_div]

/-- **Markov trace characterization at the root-of-unity exceptional points (Wenzl convention).**
For `l ≥ 3` and `0 < k < l`, a Markov trace with Wenzl projection parameter `η_W` has equal
stabilization constants at `θ = π * I / l`, `α = (k / l + 1 / 2) * π * I` if and only if
`η_W = a_k(exp (-2 * π * I / l))`. -/
theorem IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff_wenzl {l k : ℕ} (hl : 3 ≤ l)
    (hk₀ : 0 < k) (hkl : k < l) {z ηW : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam (π * I / l)) →ₗ[ℂ] ℂ}
    (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-(π * I / l)) * (1 - ηW) - exp (π * I / l) * ηW) (n : ℕ) :
    τ (hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n) =
        τ ↑(hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n)⁻¹ ↔
      ηW = wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) := by
  rw [hτ.map_hyperbolicGen_rootOfUnity_eq_iff hl hk₀ hkl (η := 1 - ηW)
      (by rw [sub_sub_cancel, hz]) n,
    ← hyperbolicProjParam_rootOfUnity hl hk₀ hkl, ← hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl,
    hyperbolicWenzlProjParam_eq_one_sub]
  constructor <;> intro h <;> linear_combination -h

end InfiniteTypeAHeckeAlgebra

end TauCeti
