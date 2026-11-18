/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Algebra.BigOperators.Field
public import TauCeti.Algebra.LinearRecurrence.ClosedForm
public import TauCeti.Algebra.LinearRecurrence.Nondegenerate
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

/-!
# Zeros of simple exponential sums from unit equations

Let `α₁, …, αₖ` be units of a field `K`, no quotient `αᵢ / αⱼ` with `i ≠ j` being a root of
unity, and let `g₁, …, gₖ ∈ K` be not all zero. The Skolem–Mahler–Lech theorem for the simple
exponential sum `m ↦ ∑ gᵢ αᵢ ^ m` says that it has only finitely many zeros. This file derives that
conclusion from the finiteness of nondegenerate solutions of unit equations, which is taken as an
explicit hypothesis on a subgroup `Γ ≤ Kˣ` containing every `αᵢ`: for every finite index type `κ`
and every `a : κ → K` with nonzero entries, the equation `∑ aᵢ xᵢ = 1` should have only finitely
many solutions `x : κ → Γ` with no vanishing nonempty subsum (`TauCeti.IsNondegenerateSolution`).
Over a field of characteristic zero this holds for every finitely generated `Γ`, by the unit
equation theorem of Evertse, Schlickewei and Schmidt; that theorem is not proved here. In positive
characteristic the conclusion can fail: over `𝔽_p(t)` the sum `(1 + t) ^ m - t ^ m - 1` vanishes at
every power `m` of `p`.

The reduction is the classical one. At a zero `m`, choose `i₀` with `g_{i₀} ≠ 0` and divide by
`-g_{i₀} α_{i₀} ^ m`: the unknowns `(αᵢ / α_{i₀}) ^ m`, for `i ≠ i₀`, solve the unit equation with
coefficients `-gᵢ / g_{i₀}`. Removing a maximal vanishing subsum
(`TauCeti.exists_sum_eq_zero_and_isNondegenerateSolution_compl`) leaves a nondegenerate solution
over a nonempty set `J` of indices, whose coefficients are then nonzero. There are finitely many
choices of `i₀` and `J`, each equation has finitely many nondegenerate solutions, and for `j ∈ J`
the coordinate `(αⱼ / α_{i₀}) ^ m` determines `m`, because `αⱼ / α_{i₀}` has infinite order.

## Main results

* `TauCeti.finite_setOf_sum_mul_zpow_eq_zero_of_finite_isNondegenerateSolution`: the integer
  zeros of `m ↦ ∑ gᵢ αᵢ ^ m` form a finite set.
* `TauCeti.finite_setOf_sum_mul_pow_eq_zero_of_finite_isNondegenerateSolution`: the same for
  natural exponents.
* `LinearRecurrence.IsNondegenerate.finite_setOf_eq_zero_of_finite_isNondegenerateSolution`: a
  nonzero solution of a nondegenerate linear recurrence over a field of characteristic zero, whose
  characteristic polynomial splits with distinct roots, has finitely many zeros. It combines the
  closed form `LinearRecurrence.exists_eq_sum_eval_mul_pow` with the result above.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 8, §8.4,
  Theorem 8.18 and its proof.
* J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a
  multiplicative group*, Ann. of Math. 155 (2002), 807–836.
-/

public section

open Finset

namespace TauCeti

universe u

variable {K : Type*} {ι : Type u} [Field K]

/-- **Skolem–Mahler–Lech for simple exponential sums, from the unit equation theorem.** Let
`α : ι → Kˣ` have no quotient `αᵢ / αⱼ` with `i ≠ j` of finite order, and let `g : ι → K` be
nonzero. If the `αᵢ` lie in a subgroup `Γ` of `Kˣ` for which every unit equation
`∑ aᵢ xᵢ = 1` with nonzero coefficients has only finitely many nondegenerate solutions with
coordinates in `Γ`, then `∑ gᵢ αᵢ ^ m` vanishes for only finitely many integers `m`.

The hypothesis on `Γ` is the conclusion of the unit equation theorem, which holds for finitely
generated `Γ` in characteristic zero; it is not proved here. -/
theorem finite_setOf_sum_mul_zpow_eq_zero_of_finite_isNondegenerateSolution [Fintype ι]
    {Γ : Subgroup Kˣ}
    (hΓ : ∀ (κ : Type u) [Fintype κ] (a : κ → K), (∀ i, a i ≠ 0) →
      {x : κ → Kˣ | (∀ i, x i ∈ Γ) ∧ IsNondegenerateSolution a fun i ↦ (x i : K)}.Finite)
    {α : ι → Kˣ} (hαΓ : ∀ i, α i ∈ Γ) (hα : Pairwise fun i j ↦ ¬IsOfFinOrder (α i / α j))
    {g : ι → K} (hg : g ≠ 0) :
    {m : ℤ | ∑ i, g i * (α i : K) ^ m = 0}.Finite := by
  classical
  -- Dividing the sum by its term at `i₀` turns a zero `m` into a solution of the unit equation
  -- with coefficients `coef i₀` and unknowns `sol i₀ m` indexed by `{i // i ≠ i₀}`. Each
  -- restriction of it to a set `J` of indices is a unit equation in `Γ`.
  let coef (i₀ : ι) (i : {i // i ≠ i₀}) : K := -g i / g i₀
  let sol (i₀ : ι) (m : ℤ) (i : {i // i ≠ i₀}) : Kˣ := (α i / α i₀) ^ m
  let X (i₀ : ι) (J : Finset {i // i ≠ i₀}) : Set (J → Kˣ) :=
    {x | (∀ i, x i ∈ Γ) ∧ IsNondegenerateSolution (fun i : J ↦ coef i₀ i) fun i ↦ (x i : K)}
  refine Set.Finite.subset (s := ⋃ (i₀ : ι) (J : Finset {i // i ≠ i₀}) (j : {i // i ≠ i₀})
      (_ : (∀ i ∈ J, coef i₀ i ≠ 0) ∧ j ∈ J), (fun m (i : J) ↦ sol i₀ m i) ⁻¹' X i₀ J)
    (Set.finite_iUnion fun i₀ ↦ Set.finite_iUnion fun J ↦ Set.finite_iUnion fun j ↦
      Set.finite_iUnion fun h ↦ ?_) ?_
  · -- Each unit equation has finitely many nondegenerate solutions, and the coordinate `j`
    -- of `sol i₀ m` determines `m`, since `α j / α i₀` has infinite order.
    refine (hΓ J _ fun i ↦ h.1 i i.2).preimage fun m _ m' _ hm ↦
      injective_zpow_iff_not_isOfFinOrder.mpr (hα j.2) ?_
    simpa [sol] using congrFun hm ⟨j, h.2⟩
  · -- At a zero `m`, the complement of a maximal vanishing subsum of the divided equation is
    -- a nondegenerate solution.
    intro m hm
    obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := Function.ne_iff.mp hg
    have hα₀ : (α i₀ : K) ^ m ≠ 0 := zpow_ne_zero _ (α i₀).ne_zero
    have hterm (i : {i // i ≠ i₀}) :
        coef i₀ i * (sol i₀ m i : K) = g i * (α i : K) ^ m / -(g i₀ * (α i₀ : K) ^ m) := by
      simp only [coef, sol, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, div_zpow]
      field_simp
    have hone : ∑ i, coef i₀ i * (sol i₀ m i : K) = 1 := by
      simp only [hterm, ← sum_div]
      rw [← sum_subtype (univ.erase i₀) (by simp) fun i ↦ g i * (α i : K) ^ m,
        div_eq_one_iff_eq (neg_ne_zero.mpr (mul_ne_zero hi₀ hα₀)), eq_neg_iff_add_eq_zero,
        add_comm]
      exact (add_sum_erase _ (fun i ↦ g i * (α i : K) ^ m) (mem_univ i₀)).trans hm
    obtain ⟨I, -, hI⟩ := exists_sum_eq_zero_and_isNondegenerateSolution_compl hone
    obtain ⟨⟨j, hj⟩, -, -⟩ := exists_ne_zero_of_sum_ne_zero (ne_zero_of_eq_one hI.sum_eq_one)
    simp only [Set.mem_iUnion, Set.mem_preimage]
    exact ⟨i₀, Iᶜ, j, ⟨fun i hi ↦ left_ne_zero_of_mul (hI.ne_zero ⟨i, hi⟩), hj⟩,
      fun i ↦ zpow_mem (div_mem (hαΓ _) (hαΓ _)) m, hI⟩

/-- **Skolem–Mahler–Lech for simple exponential sums, from the unit equation theorem**, for
natural exponents: under the hypotheses of
`TauCeti.finite_setOf_sum_mul_zpow_eq_zero_of_finite_isNondegenerateSolution`, the sum
`∑ gᵢ αᵢ ^ m` vanishes for only finitely many natural numbers `m`. -/
theorem finite_setOf_sum_mul_pow_eq_zero_of_finite_isNondegenerateSolution [Fintype ι]
    {Γ : Subgroup Kˣ}
    (hΓ : ∀ (κ : Type u) [Fintype κ] (a : κ → K), (∀ i, a i ≠ 0) →
      {x : κ → Kˣ | (∀ i, x i ∈ Γ) ∧ IsNondegenerateSolution a fun i ↦ (x i : K)}.Finite)
    {α : ι → Kˣ} (hαΓ : ∀ i, α i ∈ Γ) (hα : Pairwise fun i j ↦ ¬IsOfFinOrder (α i / α j))
    {g : ι → K} (hg : g ≠ 0) :
    {m : ℕ | ∑ i, g i * (α i : K) ^ m = 0}.Finite :=
  ((finite_setOf_sum_mul_zpow_eq_zero_of_finite_isNondegenerateSolution hΓ hαΓ hα hg).preimage
    Nat.cast_injective.injOn).subset fun m hm ↦ by simpa using hm

end TauCeti

namespace LinearRecurrence

variable {K : Type u} [Field K] {E : LinearRecurrence K}

/-- **Skolem–Mahler–Lech for simple nondegenerate recurrences, from the unit equation theorem.**
Let `E` be a nondegenerate linear recurrence over a field of characteristic zero whose
characteristic polynomial splits with distinct roots. If the characteristic roots lie in a
subgroup `Γ` of `Kˣ` for which every unit equation `∑ aᵢ xᵢ = 1` with nonzero coefficients has
only finitely many nondegenerate solutions with coordinates in `Γ`, then every nonzero solution
of `E` has only finitely many zeros.

The hypothesis on `Γ` is the conclusion of the unit equation theorem, which holds for the
subgroup generated by the characteristic roots; it is not proved here. -/
theorem IsNondegenerate.finite_setOf_eq_zero_of_finite_isNondegenerateSolution [CharZero K]
    (hE : E.IsNondegenerate) (hsplit : E.charPoly.Splits) (hnodup : E.charPoly.roots.Nodup)
    {Γ : Subgroup Kˣ}
    (hΓ : ∀ (κ : Type u) [Fintype κ] (a : κ → K), (∀ i, a i ≠ 0) →
      {x : κ → Kˣ | (∀ i, x i ∈ Γ) ∧
        TauCeti.IsNondegenerateSolution a fun i ↦ (x i : K)}.Finite)
    (hΓE : ∀ γ : Kˣ, (γ : K) ∈ E.charPoly.roots → γ ∈ Γ) {u : ℕ → K} (hu : E.IsSolution u)
    (hu0 : u ≠ 0) :
    {n : ℕ | u n = 0}.Finite := by
  classical
  obtain ⟨P, hP, hPu⟩ := E.exists_eq_sum_eval_mul_pow hsplit hE.coeff_zero_ne_zero hu
  set s := E.charPoly.roots.toFinset
  have hroot {θ : K} (hθ : θ ∈ s) : θ ∈ E.charPoly.roots := Multiset.mem_toFinset.mp hθ
  have hne (θ : s) : (θ : K) ≠ 0 := fun h0 ↦ hE.coeff_zero_ne_zero <| by
    have := (Polynomial.mem_roots'.mp (hroot θ.2)).2
    rwa [h0, Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at this
  -- Simple roots make the coefficient polynomials of the closed form constant.
  have hconst (θ : K) (hθ : θ ∈ s) (n : ℕ) : (P θ).eval (n : K) = (P θ).coeff 0 := by
    have hdeg := hP θ (hroot hθ)
    rw [← Polynomial.count_roots, Multiset.count_eq_one_of_mem hnodup (hroot hθ), Nat.cast_one,
      Nat.WithBot.lt_one_iff_le_zero] at hdeg
    rw [Polynomial.eq_C_of_degree_le_zero hdeg, Polynomial.eval_C, Polynomial.coeff_C_zero]
  let α (θ : s) : Kˣ := Units.mk0 θ (hne θ)
  let g (θ : s) : K := (P θ).coeff 0
  have hsum (n : ℕ) : u n = ∑ θ : s, g θ * (α θ : K) ^ n := by
    rw [hPu n, ← sum_coe_sort s]
    exact Fintype.sum_congr _ _ fun θ ↦ by simp only [g, α, Units.val_mk0, hconst θ θ.2]
  have hg : g ≠ 0 := fun hg0 ↦ hu0 <| funext fun n ↦ by simp [hsum n, hg0]
  have hα : Pairwise fun θ θ' : s ↦ ¬IsOfFinOrder (α θ / α θ') := by
    intro θ θ' hθθ' hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hrs (θ : s) : (θ : K) ∈ E.charPoly.rootSet K := by
      rw [Polynomial.mem_rootSet', Polynomial.coe_aeval_eq_eval]
      exact ⟨by simpa using E.charPoly_monic.ne_zero, (Polynomial.mem_roots'.mp (hroot θ.2)).2⟩
    refine ((E.isNondegenerate_iff_pow_of_splits hsplit).mp hE).2 (hrs θ) (hrs θ')
      (Subtype.coe_ne_coe.mpr hθθ') n hn ?_
    have := congrArg Units.val hpow
    rwa [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one, div_pow,
      div_eq_one_iff_eq (pow_ne_zero _ (α θ').ne_zero)] at this
  refine (TauCeti.finite_setOf_sum_mul_pow_eq_zero_of_finite_isNondegenerateSolution hΓ
    (fun θ ↦ hΓE _ (hroot θ.2)) hα hg).subset fun n hn ↦ ?_
  rwa [Set.mem_ofPred_eq, ← hsum]

end LinearRecurrence
