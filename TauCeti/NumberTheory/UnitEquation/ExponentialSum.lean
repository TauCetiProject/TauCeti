/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import TauCeti.Algebra.LinearRecurrence.ClosedForm
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Zeros of simple exponential sums as unit-equation solutions

Let `α₁, …, αₖ` be units of a field `K` and let `g₁, …, gₖ ∈ K`. When `K` has characteristic
zero, the Skolem–Mahler–Lech theorem for the simple exponential sum `m ↦ ∑ gᵢ αᵢ ^ m`, with `g`
not identically zero and no quotient `αᵢ / αⱼ` (`i ≠ j`) a root of unity, says that it has only
finitely many zeros; this fails in positive characteristic. Its classical proof reduces each zero
to a nondegenerate solution of a unit equation; this file proves that reduction over any field,
with no hypothesis on `α` or `g` beyond `g ≠ 0`.

At a zero `m`, choose `i₀` with `g_{i₀} ≠ 0` and divide by `-g_{i₀} α_{i₀} ^ m`: the unknowns
`(αᵢ / α_{i₀}) ^ m`, for `i ≠ i₀`, solve the unit equation with coefficients `-gᵢ / g_{i₀}`.
Removing a maximal vanishing subsum
(`TauCeti.exists_sum_eq_zero_and_isNondegenerateSolution_compl`) leaves a nondegenerate solution
over a set `J` of indices.

The finiteness of nondegenerate solutions of unit equations in a finitely generated subgroup of
`Kˣ` in characteristic zero (Evertse–Schlickewei–Schmidt) is not proved here. Once it is
available, it bounds the solutions for each of the finitely many choices of `i₀` and `J`, and
for `j ∈ J` the coordinate `(αⱼ / α_{i₀}) ^ m` determines `m` when `αⱼ / α_{i₀}` has infinite
order (`injective_zpow_iff_not_isOfFinOrder`).

A solution `u` of a linear recurrence over a field of characteristic zero whose characteristic
polynomial splits with distinct nonzero roots is such a sum, `u n = ∑ θ, g θ * θ ^ n` over the
characteristic roots (`LinearRecurrence.exists_eq_sum_mul_pow`), so the same reduction applies
to its zeros. When the recurrence is nondegenerate, the quotients of distinct characteristic
roots have infinite order (`LinearRecurrence.IsNondegenerate.not_isOfFinOrder_div_of_mem_roots`).

## Main results

* `TauCeti.exists_isNondegenerateSolution_of_sum_mul_zpow_eq_zero`: every integer zero `m` of
  `∑ gᵢ αᵢ ^ m` gives a nondegenerate solution `((αᵢ / α_{i₀}) ^ m)_{i ∈ J}` of the unit equation
  with coefficients `-gᵢ / g_{i₀}`, for some `i₀` and some set `J` of indices other than `i₀`.
* `LinearRecurrence.exists_isNondegenerateSolution_of_eq_zero`: the same for the zeros of a
  nonzero solution of a recurrence with distinct nonzero characteristic roots, with coefficients
  `g` fixed independently of the zero.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 8, §8.4,
  Theorem 8.18 and its proof.
* J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a
  multiplicative group*, Ann. of Math. 155 (2002), 807–836.
-/

public section

open Finset

namespace TauCeti

variable {K ι : Type*} [Field K] [Fintype ι]

/-- **Zeros of simple exponential sums as unit-equation solutions.** If `∑ gᵢ αᵢ ^ m = 0` for
units `αᵢ` of a field and `g ≠ 0`, then for some index `i₀` and some set `J` of indices other
than `i₀`, the unknowns `(αᵢ / α_{i₀}) ^ m`, `i ∈ J`, form a nondegenerate solution of the unit
equation `∑_{i ∈ J} (-gᵢ / g_{i₀}) xᵢ = 1`.

A nondegenerate solution has nonzero terms and sums to `1`, so necessarily `g_{i₀} ≠ 0`, `J` is
nonempty and `gᵢ ≠ 0` for `i ∈ J`. This is the reduction in the proof of the Skolem–Mahler–Lech
theorem for simple exponential sums. -/
theorem exists_isNondegenerateSolution_of_sum_mul_zpow_eq_zero {α : ι → Kˣ} {g : ι → K}
    (hg : g ≠ 0) {m : ℤ} (hm : ∑ i, g i * (α i : K) ^ m = 0) :
    ∃ (i₀ : ι) (J : Finset {i // i ≠ i₀}), IsNondegenerateSolution
      (fun i : J ↦ -g i / g i₀) fun i ↦ (((α i / α i₀) ^ m : Kˣ) : K) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := Function.ne_iff.mp hg
  have hα₀ : (α i₀ : K) ^ m ≠ 0 := zpow_ne_zero _ (α i₀).ne_zero
  -- Dividing the sum by `-g i₀ * α i₀ ^ m` turns its terms with `i ≠ i₀` into a unit equation.
  have hterm (i : {i // i ≠ i₀}) : -g i / g i₀ * (((α i / α i₀) ^ m : Kˣ) : K) =
      g i * (α i : K) ^ m / -(g i₀ * (α i₀ : K) ^ m) := by
    simp only [Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val, div_zpow]
    field_simp
  have hone : ∑ i : {i // i ≠ i₀}, -g i / g i₀ * (((α i / α i₀) ^ m : Kˣ) : K) = 1 := by
    simp only [hterm, ← sum_div]
    rw [← sum_subtype (univ.erase i₀) (by simp) fun i ↦ g i * (α i : K) ^ m,
      div_eq_one_iff_eq (neg_ne_zero.mpr (mul_ne_zero hi₀ hα₀)), eq_neg_iff_add_eq_zero,
      add_comm]
    exact (add_sum_erase _ (fun i ↦ g i * (α i : K) ^ m) (mem_univ i₀)).trans hm
  -- The complement of a maximal vanishing subsum is a nondegenerate solution.
  obtain ⟨I, -, hI⟩ := exists_sum_eq_zero_and_isNondegenerateSolution_compl hone
  exact ⟨i₀, Iᶜ, hI⟩

end TauCeti

namespace LinearRecurrence

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] {E : LinearRecurrence K}

/-- **Zeros of simple recurrences as unit-equation solutions.** Let the characteristic polynomial
of `E` split with distinct roots and nonzero constant term, and let `u ≠ 0` solve `E`. Then
`u n = ∑ θ, g θ * θ ^ n` over the characteristic roots `θ`, and for every zero `m` of `u` there
are a root `θ₀` and a set `J` of roots other than `θ₀` such that the powers `(θ / θ₀) ^ m`,
`θ ∈ J`, form a nondegenerate solution of the unit equation `∑_{θ ∈ J} (-g θ / g θ₀) x_θ = 1`.

The coefficients `g` do not depend on `m`, so every zero gives a solution of one of the finitely
many equations indexed by `θ₀` and `J`. When `E` is moreover nondegenerate, each `θ / θ₀` with
`θ ∈ J` has infinite order (`LinearRecurrence.IsNondegenerate.not_isOfFinOrder_div_of_mem_roots`),
so the solution determines `m`. -/
theorem exists_isNondegenerateSolution_of_eq_zero (hsplit : E.charPoly.Splits)
    (h0 : E.charPoly.coeff 0 ≠ 0) (hnodup : E.charPoly.roots.Nodup) {u : ℕ → K}
    (hu : E.IsSolution u) (hu0 : u ≠ 0) :
    ∃ g : K → K, (∀ n : ℕ, u n = ∑ θ ∈ E.charPoly.roots.toFinset, g θ * θ ^ n) ∧
      ∀ m : ℕ, u m = 0 → ∃ θ₀ ∈ E.charPoly.roots, ∃ J ⊆ E.charPoly.roots.toFinset.erase θ₀,
        TauCeti.IsNondegenerateSolution (fun θ : J ↦ -g θ / g θ₀) fun θ ↦ ((θ : K) / θ₀) ^ m := by
  obtain ⟨g, hg⟩ := E.exists_eq_sum_mul_pow hsplit h0 hnodup hu
  refine ⟨g, hg, fun m hm ↦ ?_⟩
  set s := E.charPoly.roots.toFinset
  have hs0 (θ : s) : (θ : K) ≠ 0 := fun hθ ↦ h0 <| coeff_zero_eq_zero_of_zero_isRoot <|
    hθ ▸ (mem_roots'.mp (Multiset.mem_toFinset.mp θ.property)).2
  -- `u` is the simple exponential sum with the characteristic roots as units.
  let α (θ : s) : Kˣ := Units.mk0 θ (hs0 θ)
  have hsum (n : ℕ) : u n = ∑ θ : s, g θ * (α θ : K) ^ (n : ℤ) := by
    rw [hg n, ← Finset.sum_coe_sort s]
    simp [α]
  have hg0 : (fun θ : s ↦ g θ) ≠ 0 := fun hg0 ↦
    hu0 <| funext fun n ↦ by simp [hsum n, show ∀ θ : s, g θ = 0 from congrFun hg0]
  obtain ⟨θ₀, J, hJ⟩ :=
    TauCeti.exists_isNondegenerateSolution_of_sum_mul_zpow_eq_zero hg0 ((hsum m).symm.trans hm)
  -- Transport the index set `J` of roots other than `θ₀` into `K`.
  let f : {θ : s // θ ≠ θ₀} ↪ K := (Function.Embedding.subtype _).trans (.subtype _)
  refine ⟨θ₀, Multiset.mem_toFinset.mp θ₀.property, J.map f, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨θ, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_erase.mpr ⟨fun h ↦ θ.property (Subtype.ext h), θ.val.property⟩
  · have hf (θ : J.map f) : (((J.equivMap f).symm θ : {θ : s // θ ≠ θ₀}) : K) = θ := by
      have := congrArg Subtype.val ((J.equivMap f).apply_symm_apply θ)
      rwa [Finset.equivMap_apply_coe, Function.Embedding.trans_apply,
        Function.Embedding.coe_subtype, Function.Embedding.coe_subtype] at this
    convert hJ.comp_equiv (J.equivMap f).symm using 1 <;> funext θ
    · simp only [Function.comp_apply, hf θ]
    · simp only [α, Function.comp_apply, zpow_natCast, Units.val_pow_eq_pow_val,
        Units.val_div_eq_div_val, Units.val_mk0, hf θ]

end LinearRecurrence
