/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.NumberTheory.UnitEquation.SubspaceCover

import TauCeti.Analysis.SpecialFunctions.Choose
import TauCeti.NumberTheory.UnitEquation.Specialization

/-!
# The explicit bound for nondegenerate solutions of unit equations

Evertse, Schlickewei and Schmidt prove that over a field `K` of characteristic zero, for a
subgroup `Γ ≤ (Kˣ)ⁿ` of rank at most `r`, the equation `a₁x₁ + ⋯ + aₙxₙ = 1` has at most
`exp ((6n)^(3n) (r + 1))` nondegenerate solutions `x ∈ Γ` (their Theorem 1.1). They deduce it
from their subspace theorem for unit equations over the algebraic closure `Q` of `ℚ` (their
Theorem 2.1, at zero perturbation): for `m ≥ 2` and a subgroup of `(Qˣ)ᵐ` of rank at most `s`,
the solutions of `y₁ + ⋯ + yₘ = 1` lie in at most `exp ((5m)^(3m) (s + 1))` proper linear
subspaces of `Qᵐ`.

`TauCeti.encard_isNondegenerateSolution_le_of_subspaceCover` performs the combinatorial
deduction for any cover bound `N`, producing the recursive bound
`TauCeti.unitEquationNondegenerateBound N n r`. This file evaluates that recursion for a cover
bound `N m s ≤ exp ((5m)^(3m) (s + 1))` and shows that it stays below
`exp ((6n)^(3n) (r + 1))`. Each step of the recursion, in `n` unknowns and rank `r`, multiplies
the cover bound in `n` unknowns at rank `r + 1` by a sum over the possible index sets `I` of a
minimal vanishing subsum of the homogeneous linear relation supplied by a covering subspace. There
are at most `2ⁿ` such index sets, and the summand for `I` is the product of the two bounds at rank
`r + 1` in `|I| - 1` and `n - |I| + 1` unknowns. The increase of the base from `5n` to `6n` absorbs
these factors and the increase of the rank.

The subspace theorem enters as a hypothesis, `TauCeti.IsUnitEquationCoverBound` for the cover bound
`⌊exp ((5m)^(3m) (s + 1))⌋₊`: this file does not prove it, and it does not extend to arbitrary
fields of positive characteristic. The bound is stated twice. The first version is conditional on a
cover bound over the field `K` itself. The second assumes the cover bound only over an algebraically
closed field `L`, such as `AlgebraicClosure ℚ` as in the cited Theorem 2.1, and transfers the
resulting bound to every domain `K` sharing a subfield with `L` by specialization
(`TauCeti.encard_isNondegenerateSolution_le_of_isAlgClosed`). Each version bounds the whole solution
set by `⌊exp ((6n)^(3n) (r + 1))⌋₊` and then every finite set of solutions by
`exp ((6n)^(3n) (r + 1))`.

## Main results

* `TauCeti.unitEquationNondegenerateBound_le_exp`: if `N m s ≤ exp ((5m)^(3m) (s + 1))` for
  `2 ≤ m ≤ n` and `m + s ≤ n + r + 1`, then
  `unitEquationNondegenerateBound N n r ≤ exp ((6n)^(3n) (r + 1))`.
* `TauCeti.encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover`: the
  Evertse–Schlickewei–Schmidt bound `⌊exp ((6n)^(3n) (r + 1))⌋₊` for the set of nondegenerate
  solutions in `Γ ≤ (Kˣ)ⁿ` of rank at most `r`, assuming their cover bound over `K`.
* `TauCeti.card_isNondegenerateSolution_le_exp_of_subspaceCover`: its corollary
  `#M ≤ exp ((6n)^(3n) (r + 1))` for every finite set `M` of such solutions.
* `TauCeti.encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover_of_isAlgClosed` and
  `TauCeti.card_isNondegenerateSolution_le_exp_of_subspaceCover_of_isAlgClosed`: the same bounds
  over a domain `K`, assuming the cover bound over an algebraically closed field `L`, both
  algebras over a common field.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables which lie in
  a multiplicative group*, Ann. of Math. 155 (2002), 807–836, Theorems 1.1 and 2.1, Lemma 3.2 and
  the deduction of Theorem 1.1 from Theorem 2.1 in §§3–4.
-/

public section

open Finset Real

namespace TauCeti

universe u v w

/-- The numerical inequality behind one step of the recursion, in `n + 2` unknowns:
`2 (5(n+2))^(3(n+2)) + (n + 2) + 4 (6(n+1))^(3(n+1)) ≤ (6(n+2))^(3(n+2))`. -/
private lemma two_mul_five_mul_pow_add_le_six_mul_pow (n : ℕ) :
    2 * (5 * (n + 2 : ℕ) : ℝ) ^ (3 * (n + 2)) + (n + 2 : ℕ) +
        4 * (6 * (n + 1 : ℕ) : ℝ) ^ (3 * (n + 1)) ≤
      (6 * (n + 2 : ℕ) : ℝ) ^ (3 * (n + 2)) := by
  set x : ℝ := 6 * (n + 2 : ℕ)
  have hx : 12 ≤ x := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    simp only [x]
    push_cast
    linarith
  have hn : ((n + 2 : ℕ) : ℝ) = x / 6 := by
    simp only [x]
    ring
  set y : ℝ := x ^ (3 * (n + 1))
  have hy : 1 ≤ y := one_le_pow₀ (by linarith)
  have hQ : x ^ (3 * (n + 2)) = y * x ^ 3 := by
    rw [← pow_add]
    ring_nf
  -- `(6(n+1))^(3(n+1)) ≤ x^(3(n+1))`.
  have hP : (6 * (n + 1 : ℕ) : ℝ) ^ (3 * (n + 1)) ≤ y :=
    pow_le_pow_left₀ (by positivity) (by simp only [x]; gcongr; omega) _
  -- `(5(n+2))^(3(n+2)) = (5/6)^(3(n+2)) x^(3(n+2)) ≤ (5/6)^6 x^(3(n+2))`.
  have h5 : (5 * (n + 2 : ℕ) : ℝ) ^ (3 * (n + 2)) ≤ 15625 / 46656 * (y * x ^ 3) := by
    have he : (5 * (n + 2 : ℕ) : ℝ) ^ (3 * (n + 2)) = (5 / 6) ^ (3 * (n + 2)) * x ^ (3 * (n + 2)) :=
      by rw [← mul_pow]; simp only [x]; ring_nf
    rw [he, hQ]
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega : 6 ≤ 3 * (n + 2))) (by positivity)).trans_eq ?_
    norm_num
  have hx2 : 144 ≤ x ^ 2 := (by norm_num : (144 : ℝ) = 12 ^ 2).trans_le
    (pow_le_pow_left₀ (by norm_num) hx 2)
  have hx3 : 1728 ≤ x ^ 3 := (by norm_num : (1728 : ℝ) = 12 ^ 3).trans_le
    (pow_le_pow_left₀ (by norm_num) hx 3)
  have h1 : y * 1728 ≤ y * x ^ 3 := mul_le_mul_of_nonneg_left hx3 (by linarith)
  have h2 : x ^ 3 ≤ y * x ^ 3 := le_mul_of_one_le_left (by positivity) hy
  have h3 : 144 * x ≤ x ^ 3 := by
    have := mul_le_mul_of_nonneg_right hx2 (by linarith : 0 ≤ x)
    rwa [← pow_succ] at this
  rw [hQ]
  linarith [hn]

/-- **The explicit Evertse–Schlickewei–Schmidt bound.** If the cover bound in `m` unknowns and
rank `s` is at most `exp ((5m)^(3m) (s + 1))` whenever `2 ≤ m ≤ n` and `m + s ≤ n + r + 1`, a
range containing all cases the recursion reaches, then the bound
`unitEquationNondegenerateBound N n r` for the number of nondegenerate solutions in `n` unknowns
and rank `r` is at most `exp ((6n)^(3n) (r + 1))`. -/
theorem unitEquationNondegenerateBound_le_exp {N : ℕ → ℕ → ℕ} (n r : ℕ)
    (hN : ∀ m s, 2 ≤ m → m ≤ n → m + s ≤ n + r + 1 →
      (N m s : ℝ) ≤ exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))) :
    (unitEquationNondegenerateBound N n r : ℝ) ≤ exp ((6 * n : ℝ) ^ (3 * n) * (r + 1)) := by
  induction n using Nat.strong_induction_on generalizing r with | _ n ih => ?_
  rcases n with _ | _ | n
  · simpa using (exp_pos _).le
  · simpa using one_le_exp (by positivity)
  set P : ℝ := (6 * (n + 1 : ℕ) : ℝ) ^ (3 * (n + 1))
  have hP : 0 ≤ P := by positivity
  -- Each bound in fewer unknowns, at rank `r + 1`, is at most `exp (P (r + 2))`.
  have hbound (a : ℕ) (ha : a ≤ n + 1) :
      (unitEquationNondegenerateBound N a (r + 1) : ℝ) ≤ exp (P * (r + 2)) := by
    -- `(6a)^(3a) ≤ P`, by monotonicity of `b ^ e` in the base and, as `1 ≤ 6(n+1)`, the exponent.
    have hmono : (6 * a : ℝ) ^ (3 * a) ≤ P := by
      simp only [P]
      exact_mod_cast (pow_le_pow (by omega) (by omega) (by omega) :
        (6 * a) ^ (3 * a) ≤ (6 * (n + 1)) ^ (3 * (n + 1)))
    refine (ih a (by omega) (r + 1) fun m s hm hma hms ↦ hN m s hm (by omega) (by omega)).trans
      (exp_le_exp.mpr ?_)
    push_cast
    rw [add_assoc, one_add_one_eq_two]
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  have hterm (k : Fin (n + 1)) :
      (unitEquationNondegenerateBound N (k + 1) (r + 1) : ℝ) *
          unitEquationNondegenerateBound N (n + 1 - k) (r + 1) ≤ exp (2 * P * (r + 2)) :=
    (mul_le_mul (hbound _ (by omega)) (hbound _ (by omega)) (Nat.cast_nonneg _)
      (exp_pos _).le).trans_eq (by rw [← exp_add]; ring_nf)
  -- The index sets, of size at least two, of the minimal vanishing subsums of the homogeneous
  -- relation supplied by a covering subspace number at most `2^(n+2) ≤ exp (n + 2)`.
  have hchoose : ∑ k : Fin (n + 1), (((n + 2).choose (k + 2) : ℕ) : ℝ) ≤ exp (n + 2 : ℕ) := by
    have hrange : n + 2 + 1 - 2 = n + 1 := by omega
    simpa only [Fin.sum_univ_eq_sum_range (fun j ↦ (((n + 2).choose (j + 2) : ℕ) : ℝ)), hrange]
      using sum_range_choose_add_le_exp (n + 2) 2
  have hN' := hN (n + 2) (r + 1) (by omega) le_rfl (by omega)
  set A : ℝ := (5 * (n + 2 : ℕ) : ℝ) ^ (3 * (n + 2))
  have hA : 0 ≤ A := by positivity
  have hkey := two_mul_five_mul_pow_add_le_six_mul_pow n
  rw [unitEquationNondegenerateBound_add_two]
  push_cast only [Nat.cast_mul, Nat.cast_sum]
  calc _ ≤ exp (A * (r + 2)) * (exp (n + 2 : ℕ) * exp (2 * P * (r + 2))) := by
        refine mul_le_mul (hN'.trans_eq (by push_cast; ring_nf)) ?_
          (sum_nonneg fun _ _ ↦ by positivity) (exp_pos _).le
        calc _ ≤ ∑ k : Fin (n + 1), (((n + 2).choose (k + 2) : ℕ) : ℝ) * exp (2 * P * (r + 2)) :=
              sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hterm k) (Nat.cast_nonneg _)
          _ = _ := by rw [← sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hchoose (exp_pos _).le
    _ = exp (A * (r + 2) + (n + 2 : ℕ) + 2 * P * (r + 2)) := by
        rw [exp_add, exp_add]; ring
    _ ≤ _ := by
        refine exp_le_exp.mpr ?_
        nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ r + 1),
          (Nat.cast_nonneg _ : (0 : ℝ) ≤ (n + 2 : ℕ)), (r.cast_nonneg : (0 : ℝ) ≤ r)]

/-- **The Evertse–Schlickewei–Schmidt bound, from the subspace theorem for unit equations.**
Suppose that `⌊exp ((5m)^(3m) (s + 1))⌋₊` bounds the subspace covers for unit equations over `K`
(`TauCeti.IsUnitEquationCoverBound`): for every `m ≥ 2` and every subgroup of `(Fin m → Kˣ)` of
rank at most `s` over `ℤ`, the nondegenerate solutions `y` of `y₁ + ⋯ + yₘ = 1` in it lie in the
union of at most `exp ((5m)^(3m) (s + 1))` proper subspaces of `Fin m → K`. Then for a subgroup
`Γ ≤ (ι → Kˣ)` of rank at most `r` and any coefficients `a`, the set of nondegenerate solutions
`x ∈ Γ` of `∑ aᵢxᵢ = 1` has at most `⌊exp ((6n)^(3n) (r + 1))⌋₊` elements, where `n` is the
number of unknowns. The cover bound is a hypothesis, not proved here. -/
theorem encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover {K : Type u} [Field K]
    (hN : IsUnitEquationCoverBound K fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) :
    {x | x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)}.encard ≤
      ⌊exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1))⌋₊ :=
  (encard_isNondegenerateSolution_le_of_subspaceCover hN Γ hΓ a).trans <| Nat.cast_le.mpr <|
    Nat.le_floor <| unitEquationNondegenerateBound_le_exp _ r fun _ _ _ _ _ ↦
      Nat.floor_le (exp_pos _).le

/-- **The Evertse–Schlickewei–Schmidt bound for finite sets of solutions.** Under the cover
hypothesis of `TauCeti.encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover`, for a
subgroup `Γ ≤ (ι → Kˣ)` of rank at most `r` and any coefficients `a`, every finite set of
nondegenerate solutions `x ∈ Γ` of `∑ aᵢxᵢ = 1` has at most `exp ((6n)^(3n) (r + 1))` elements,
where `n` is the number of unknowns. The cover bound is a hypothesis, not proved here. -/
theorem card_isNondegenerateSolution_le_exp_of_subspaceCover {K : Type u} [Field K]
    (hN : IsUnitEquationCoverBound K fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) (M : Finset (ι → Kˣ))
    (hM : ∀ x ∈ M, x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)) :
    (#M : ℝ) ≤ exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1)) :=
  (Nat.le_floor_iff (exp_pos _).le).mp <| Nat.cast_le.mp <| (M.card_le_encard hM).trans
    (encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover hN Γ hΓ a)

/-- **The Evertse–Schlickewei–Schmidt bound over every domain, from the subspace theorem over an
algebraically closed field.** Let `K` be a domain and `L` an algebraically closed field, both
algebras over a common field `k`; for instance `K` a field of characteristic zero,
`L = AlgebraicClosure ℚ` and `k = ℚ`. Suppose that `⌊exp ((5m)^(3m) (s + 1))⌋₊` bounds the
subspace covers for unit equations over `L` (`TauCeti.IsUnitEquationCoverBound`): for every
`m ≥ 2` and every subgroup of `(Fin m → Lˣ)` of rank at most `s`, the nondegenerate solutions of
`y₁ + ⋯ + yₘ = 1` in it lie in the union of at most `exp ((5m)^(3m) (s + 1))` proper subspaces.
Then for a subgroup `Γ ≤ (ι → Kˣ)` of rank at most `r` and any coefficients `a`, the set of
nondegenerate solutions `x ∈ Γ` of `∑ aᵢxᵢ = 1` has at most `⌊exp ((6n)^(3n) (r + 1))⌋₊`
elements, where `n` is the number of unknowns. The cover bound over `L` is a hypothesis, not
proved here. -/
theorem encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover_of_isAlgClosed (k : Type*)
    [Field k] {K : Type u} {L : Type w} [CommRing K] [IsDomain K] [Field L] [IsAlgClosed L]
    [Algebra k K] [Algebra k L]
    (hN : IsUnitEquationCoverBound L fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) :
    {x | x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)}.encard ≤
      ⌊exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1))⌋₊ :=
  encard_isNondegenerateSolution_le_of_isAlgClosed k
    (fun b Δ hΔ ↦ encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover hN Δ hΔ b) a Γ hΓ

/-- **The Evertse–Schlickewei–Schmidt bound for finite sets of solutions over every domain.**
Under the hypotheses of
`TauCeti.encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover_of_isAlgClosed`, every
finite set of nondegenerate solutions `x ∈ Γ` of `∑ aᵢxᵢ = 1` has at most
`exp ((6n)^(3n) (r + 1))` elements, where `n` is the number of unknowns. The cover bound over `L`
is a hypothesis, not proved here. -/
theorem card_isNondegenerateSolution_le_exp_of_subspaceCover_of_isAlgClosed (k : Type*)
    [Field k] {K : Type u} {L : Type w} [CommRing K] [IsDomain K] [Field L] [IsAlgClosed L]
    [Algebra k K] [Algebra k L]
    (hN : IsUnitEquationCoverBound L fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) (M : Finset (ι → Kˣ))
    (hM : ∀ x ∈ M, x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)) :
    (#M : ℝ) ≤ exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1)) :=
  (Nat.le_floor_iff (exp_pos _).le).mp <| Nat.cast_le.mp <| (M.card_le_encard hM).trans
    (encard_isNondegenerateSolution_le_floor_exp_of_subspaceCover_of_isAlgClosed k hN Γ hΓ a)

end TauCeti
