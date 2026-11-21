/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.NumberTheory.UnitEquation.Specialization
public import TauCeti.NumberTheory.UnitEquation.SubspaceCover

/-!
# The explicit bound for nondegenerate solutions of unit equations

Evertse, Schlickewei and Schmidt prove that over a field of characteristic zero, for a subgroup
`Γ ≤ (Kˣ)ⁿ` of rank at most `r`, the equation `a₁x₁ + ⋯ + aₙxₙ = 1` has at most
`exp ((6n)^(3n) (r + 1))` nondegenerate solutions `x ∈ Γ` (their Theorem 1.1). They deduce it
from their subspace theorem for unit equations (their Theorem 2.1, at zero perturbation): for
`m ≥ 2` and a subgroup of `(Kˣ)ᵐ` of rank at most `s`, the solutions of `y₁ + ⋯ + yₘ = 1` lie in
at most `exp ((5m)^(3m) (s + 1))` proper linear subspaces of `Kᵐ`.

`TauCeti.encard_isNondegenerateSolution_le_of_subspaceCover` performs the combinatorial
deduction for any cover bound `N`, producing the recursive bound
`TauCeti.unitEquationNondegenerateBound N n r`. This file evaluates that recursion for the cover
bound `exp ((5m)^(3m) (s + 1))` and shows that it stays below `exp ((6n)^(3n) (r + 1))`. Each step
of the recursion multiplies the cover bound in `n` unknowns, at most `2ⁿ` choices of a minimal
vanishing subsum, and two bounds in fewer unknowns at rank one higher. The increase of the base
from `5n` to `6n` absorbs these factors and the increase of the rank.

The subspace theorem enters as a hypothesis: this file does not prove it, and it fails in
positive characteristic. The bound is stated twice: with the cover hypothesis over the field `K`
itself, and with the cover hypothesis over an algebraically closed field `L`, such as the
algebraic closure of `ℚ`, from which it transfers to every domain `K` sharing a subfield with `L`
by specialization (`TauCeti.encard_isNondegenerateSolution_le_of_isAlgClosed`).

## Main results

* `TauCeti.unitEquationNondegenerateBound_le_exp`: if `N m s ≤ exp ((5m)^(3m) (s + 1))` for
  `m ≥ 2`, then `unitEquationNondegenerateBound N n r ≤ exp ((6n)^(3n) (r + 1))`.
* `TauCeti.card_le_exp_of_subspaceCover`: the Evertse–Schlickewei–Schmidt bound
  `exp ((6n)^(3n) (r + 1))` for the nondegenerate solutions in `Γ ≤ (Kˣ)ⁿ` of rank at most `r`,
  assuming their cover bound over `K`.
* `TauCeti.card_le_exp_of_subspaceCover_of_isAlgClosed`: the same bound over a domain `K`,
  assuming the cover bound over an algebraically closed field `L`, both algebras over a common
  field.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables which lie in
  a multiplicative group*, Ann. of Math. 155 (2002), 807–836, Theorems 1.1 and 2.1, Lemma 3.2 and
  the deduction of Theorem 1.1 from Theorem 2.1 in §§3–4.
-/

public section

open Finset Real

namespace TauCeti

universe u v w

/-- The base `(6n)^(3n)` of the bound is monotone in `n`. -/
private lemma six_mul_pow_le_six_mul_pow {a b : ℕ} (h : a ≤ b) :
    (6 * a : ℝ) ^ (3 * a) ≤ (6 * b : ℝ) ^ (3 * b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.le_zero.mp h]
  have hb' : (1 : ℝ) ≤ 6 * b := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  calc (6 * a : ℝ) ^ (3 * a) ≤ (6 * b : ℝ) ^ (3 * a) :=
        pow_le_pow_left₀ (by positivity) (by gcongr) _
    _ ≤ (6 * b : ℝ) ^ (3 * b) := pow_le_pow_right₀ hb' (by omega)

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
  have hx3 : 1728 ≤ x ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx 3]
  have h1 : y * 1728 ≤ y * x ^ 3 := mul_le_mul_of_nonneg_left hx3 (by linarith)
  have h2 : x ^ 3 ≤ y * x ^ 3 := le_mul_of_one_le_left (by positivity) hy
  have h3 : 144 * x ≤ x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left (show 144 ≤ x ^ 2 by nlinarith) (by linarith : 0 ≤ x)]
  rw [hQ]
  linarith [show ((n + 2 : ℕ) : ℝ) = x / 6 by simp only [x]; ring]

/-- The binomial coefficients `(n + 2).choose (k + 2)`, `k ≤ n`, of the minimal vanishing subsums
on at least two of `n + 2` indices add up to at most `2 ^ (n + 2) ≤ exp (n + 2)`. -/
private lemma sum_choose_add_two_le_exp (n : ℕ) :
    ∑ k : Fin (n + 1), (((n + 2).choose (k + 2) : ℕ) : ℝ) ≤ exp (n + 2 : ℕ) := by
  have hsum : ∑ k : Fin (n + 1), (n + 2).choose (k + 2) ≤ 2 ^ (n + 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ (n + 2).choose (k + 2)), ← Nat.sum_range_choose,
      sum_range_succ' _ (n + 2), sum_range_succ' _ (n + 1)]
    exact le_add_right (le_add_right le_rfl)
  calc _ ≤ ((2 ^ (n + 2) : ℕ) : ℝ) := by exact_mod_cast hsum
    _ ≤ exp 1 ^ (n + 2) := by
        push_cast
        exact pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (1 : ℝ)]) _
    _ = exp (n + 2 : ℕ) := by rw [← exp_natCast_mul, mul_one]

/-- **The explicit Evertse–Schlickewei–Schmidt bound.** If the cover bound in `m ≥ 2` unknowns
and rank `s` is at most `exp ((5m)^(3m) (s + 1))`, then the bound
`unitEquationNondegenerateBound N n r` for the number of nondegenerate solutions in `n` unknowns
and rank `r` is at most `exp ((6n)^(3n) (r + 1))`. -/
theorem unitEquationNondegenerateBound_le_exp {N : ℕ → ℕ → ℕ}
    (hN : ∀ m s, 2 ≤ m → (N m s : ℝ) ≤ exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))) (n r : ℕ) :
    (unitEquationNondegenerateBound N n r : ℝ) ≤ exp ((6 * n : ℝ) ^ (3 * n) * (r + 1)) := by
  induction n using Nat.strong_induction_on generalizing r with | _ n ih => ?_
  rcases n with _ | _ | n
  · simpa using (exp_pos _).le
  · simpa using one_le_exp (by positivity)
  set P : ℝ := (6 * (n + 1 : ℕ) : ℝ) ^ (3 * (n + 1))
  have hP : 0 ≤ P := by positivity
  -- Each product of two bounds in fewer unknowns, at rank `r + 1`, is at most `exp (2 P (r + 2))`.
  have hterm (k : Fin (n + 1)) :
      (unitEquationNondegenerateBound N (k + 1) (r + 1) : ℝ) *
          unitEquationNondegenerateBound N (n + 1 - k) (r + 1) ≤ exp (2 * P * (r + 2)) := by
    have hbound (a : ℕ) (ha : a ≤ n + 1) :
        (unitEquationNondegenerateBound N a (r + 1) : ℝ) ≤ exp (P * (r + 2)) := by
      refine (ih a (by omega) (r + 1)).trans (exp_le_exp.mpr ?_)
      push_cast
      rw [add_assoc, one_add_one_eq_two]
      exact mul_le_mul_of_nonneg_right (six_mul_pow_le_six_mul_pow ha) (by positivity)
    calc _ ≤ exp (P * (r + 2)) * exp (P * (r + 2)) :=
          mul_le_mul (hbound _ (by omega)) (hbound _ (by omega)) (Nat.cast_nonneg _)
            (exp_pos _).le
      _ = exp (2 * P * (r + 2)) := by rw [← exp_add]; ring_nf
  have hN' := hN (n + 2) (r + 1) (by omega)
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
          _ ≤ _ := mul_le_mul_of_nonneg_right (sum_choose_add_two_le_exp n) (exp_pos _).le
    _ = exp (A * (r + 2) + (n + 2 : ℕ) + 2 * P * (r + 2)) := by
        rw [exp_add, exp_add]; ring
    _ ≤ _ := by
        refine exp_le_exp.mpr ?_
        nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ r + 1),
          (Nat.cast_nonneg _ : (0 : ℝ) ≤ (n + 2 : ℕ)), (r.cast_nonneg : (0 : ℝ) ≤ r)]

/-- A cover bound `exp ((5m)^(3m) (s + 1))` gives the natural-number cover bound
`⌊exp ((5m)^(3m) (s + 1))⌋₊`, to which the combinatorial deduction applies. -/
private lemma subspaceCover_floor {K : Type u} [Field K]
    (hN : ∀ m : ℕ, 2 ≤ m → ∀ (s : ℕ) (Γ : Subgroup (Fin m → Kˣ)),
      Module.rank ℤ (Additive Γ) ≤ s → ∃ 𝒲 : Finset (Submodule K (Fin m → K)),
        (#𝒲 : ℝ) ≤ exp ((5 * m : ℝ) ^ (3 * m) * (s + 1)) ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧
          ∀ y ∈ Γ, IsNondegenerateSolution 1 (fun i ↦ (y i : K)) →
            ∃ W ∈ 𝒲, (fun i ↦ (y i : K)) ∈ W)
    (m : ℕ) (hm : 2 ≤ m) (s : ℕ) (Γ : Subgroup (Fin m → Kˣ))
    (hΓ : Module.rank ℤ (Additive Γ) ≤ s) :
    ∃ 𝒲 : Finset (Submodule K (Fin m → K)),
      #𝒲 ≤ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊ ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧
        ∀ y ∈ Γ, IsNondegenerateSolution 1 (fun i ↦ (y i : K)) →
          ∃ W ∈ 𝒲, (fun i ↦ (y i : K)) ∈ W := by
  obtain ⟨𝒲, h𝒲, hW, hcov⟩ := hN m hm s Γ hΓ
  exact ⟨𝒲, Nat.le_floor h𝒲, hW, hcov⟩

/-- A finite set of solutions inside a set whose cardinality is at most the recursive bound for
the cover bound `⌊exp ((5m)^(3m) (s + 1))⌋₊` has at most `exp ((6n)^(3n) (r + 1))` elements. -/
private lemma card_le_exp_of_encard_le {α : Type*} {S : Set α} {M : Finset α} (hM : ∀ x ∈ M, x ∈ S)
    {n r : ℕ} (hS : S.encard ≤ unitEquationNondegenerateBound
      (fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊) n r) :
    (#M : ℝ) ≤ exp ((6 * n : ℝ) ^ (3 * n) * (r + 1)) := by
  have hcard : (#M : ℕ∞) ≤ unitEquationNondegenerateBound
      (fun m s ↦ ⌊exp ((5 * m : ℝ) ^ (3 * m) * (s + 1))⌋₊) n r :=
    (Set.encard_coe_eq_coe_finsetCard M ▸ Set.encard_le_encard hM).trans hS
  exact (Nat.cast_le.mpr (ENat.natCast_le_natCast.mp hcard)).trans
    (unitEquationNondegenerateBound_le_exp (fun _ _ _ ↦ Nat.floor_le (exp_pos _).le) n r)

/-- **The Evertse–Schlickewei–Schmidt bound, from the subspace theorem for unit equations.**
Suppose that for every `m ≥ 2` and every subgroup of `(Fin m → Kˣ)` of rank at most `s` over `ℤ`,
the nondegenerate solutions `y` of `y₁ + ⋯ + yₘ = 1` in it lie in the union of at most
`exp ((5m)^(3m) (s + 1))` proper subspaces of `Fin m → K`. Then for a subgroup `Γ ≤ (ι → Kˣ)` of
rank at most `r` and any coefficients `a`, every finite set of nondegenerate solutions `x ∈ Γ` of
`∑ aᵢxᵢ = 1` has at most `exp ((6n)^(3n) (r + 1))` elements, where `n` is the number of
unknowns. The cover bound is a hypothesis, not proved here. -/
theorem card_le_exp_of_subspaceCover {K : Type u} [Field K]
    (hN : ∀ m : ℕ, 2 ≤ m → ∀ (s : ℕ) (Γ : Subgroup (Fin m → Kˣ)),
      Module.rank ℤ (Additive Γ) ≤ s → ∃ 𝒲 : Finset (Submodule K (Fin m → K)),
        (#𝒲 : ℝ) ≤ exp ((5 * m : ℝ) ^ (3 * m) * (s + 1)) ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧
          ∀ y ∈ Γ, IsNondegenerateSolution 1 (fun i ↦ (y i : K)) →
            ∃ W ∈ 𝒲, (fun i ↦ (y i : K)) ∈ W)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) (M : Finset (ι → Kˣ))
    (hM : ∀ x ∈ M, x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)) :
    (#M : ℝ) ≤ exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1)) :=
  card_le_exp_of_encard_le hM
    (encard_isNondegenerateSolution_le_of_subspaceCover (subspaceCover_floor hN) Γ hΓ a)

/-- **The Evertse–Schlickewei–Schmidt bound over every domain, from the subspace theorem over an
algebraically closed field.** Let `K` be a domain and `L` an algebraically closed field, both
algebras over a common field `k`; for instance `K` a field of characteristic zero,
`L = AlgebraicClosure ℚ` and `k = ℚ`. Suppose that over `L`, for every `m ≥ 2` and every subgroup
of `(Fin m → Lˣ)` of rank at most `s`, the nondegenerate solutions of `y₁ + ⋯ + yₘ = 1` in it lie
in the union of at most `exp ((5m)^(3m) (s + 1))` proper subspaces. Then for a subgroup
`Γ ≤ (ι → Kˣ)` of rank at most `r` and any coefficients `a`, every finite set of nondegenerate
solutions `x ∈ Γ` of `∑ aᵢxᵢ = 1` has at most `exp ((6n)^(3n) (r + 1))` elements, where `n` is
the number of unknowns. The cover bound over `L` is a hypothesis, not proved here. -/
theorem card_le_exp_of_subspaceCover_of_isAlgClosed (k : Type*) [Field k] {K : Type u}
    {L : Type w} [CommRing K] [IsDomain K] [Field L] [IsAlgClosed L] [Algebra k K] [Algebra k L]
    (hN : ∀ m : ℕ, 2 ≤ m → ∀ (s : ℕ) (Δ : Subgroup (Fin m → Lˣ)),
      Module.rank ℤ (Additive Δ) ≤ s → ∃ 𝒲 : Finset (Submodule L (Fin m → L)),
        (#𝒲 : ℝ) ≤ exp ((5 * m : ℝ) ^ (3 * m) * (s + 1)) ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧
          ∀ y ∈ Δ, IsNondegenerateSolution 1 (fun i ↦ (y i : L)) →
            ∃ W ∈ 𝒲, (fun i ↦ (y i : L)) ∈ W)
    {ι : Type v} [Fintype ι] (Γ : Subgroup (ι → Kˣ)) {r : ℕ}
    (hΓ : Module.rank ℤ (Additive Γ) ≤ r) (a : ι → K) (M : Finset (ι → Kˣ))
    (hM : ∀ x ∈ M, x ∈ Γ ∧ IsNondegenerateSolution a fun i ↦ (x i : K)) :
    (#M : ℝ) ≤ exp ((6 * Fintype.card ι : ℝ) ^ (3 * Fintype.card ι) * (r + 1)) :=
  card_le_exp_of_encard_le hM <| encard_isNondegenerateSolution_le_of_isAlgClosed k
    (fun b Δ hΔ ↦ encard_isNondegenerateSolution_le_of_subspaceCover (subspaceCover_floor hN)
      Δ hΔ b) a Γ hΓ

end TauCeti
