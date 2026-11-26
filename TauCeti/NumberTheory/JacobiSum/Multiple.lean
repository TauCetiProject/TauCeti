/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
import TauCeti.Algebra.Group.AddChar.Basic
import TauCeti.NumberTheory.AddCharacter.FiniteField
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.MulChar.Real

/-!
# Multiple Jacobi sums

For a family `χ = (χᵢ)_{i ∈ ι}` of multiplicative characters of a finite commutative ring `R` and
`t ∈ R`, the multiple Jacobi sum is `J_t(χ) = ∑_{x₁ + ⋯ + x_r = t} χ₁(x₁) ⋯ χ_r(x_r)`. The sums
`J(χ) = J_1(χ)` and `J₀(χ) = J_0(χ)` are the multiple Jacobi sums of Ireland and Rosen; for two
characters `J(χ, φ)` is Mathlib's `jacobiSum χ φ`. Over a finite field these sums relate products
of Gauss sums to a single Gauss sum, and they count the solutions of diagonal equations
`∑ᵢ aᵢ xᵢ ^ dᵢ = b` (`TauCeti.card_sum_mul_pow_eq`).

As in Mathlib, every character vanishes at `0`, the trivial one included, in contrast with
sources that set `1(0) = 1`. So the trivial character gives no exceptional cases in the scaling
results, the vanishing of `J₀`, the Gauss-sum relation and the recursion for `J₀`: there only the
product `∏ᵢ χᵢ` decides which formula applies. The recursion `J(χ) = -χ_p(-1) J(χ')` needs `χ_p`
to be nontrivial, and the absolute-value formulas need every `χᵢ` to be nontrivial, since
`g(1, ψ) = -1`.

## Main definitions

* `TauCeti.multiJacobiSum χ t`: the multiple Jacobi sum `J_t(χ)`.

## Main results

* `TauCeti.multiJacobiSum_def`: `J_t(χ)` is the sum of `∏ᵢ χᵢ(xᵢ)` over `∑ᵢ xᵢ = t`.
* `TauCeti.multiJacobiSum_fin_two_one`: for two characters, `J(χ, φ)` is `jacobiSum χ φ`.
* `TauCeti.multiJacobiSum_eq_sum_mul`: removing the `p`-th character,
  `J_t(χ) = ∑_y χ_p(y) J_{t - y}(χ')`.
* `TauCeti.multiJacobiSum_eq_mul_multiJacobiSum_one`: at a unit `t`, `J_t(χ) = (∏ᵢ χᵢ)(t) J(χ)`.
* `TauCeti.sum_filter_sum_mul_eq_prod_mul_multiJacobiSum`: the sum over `∑ᵢ aᵢ xᵢ = t` for units
  `aᵢ` is `∏ᵢ χᵢ(aᵢ⁻¹) J_t(χ)`.
* `TauCeti.multiJacobiSum_zero_eq_zero`: `J₀(χ) = 0` if `∏ᵢ χᵢ ≠ 1`.
* `TauCeti.prod_gaussSum_eq_gaussSum_prod_mul_add`: over a finite field,
  `∏ᵢ g(χᵢ, ψ) = g(∏ᵢ χᵢ, ψ) J(χ) + J₀(χ)` for every additive character `ψ`.
* `TauCeti.gaussSum_prod_mul_multiJacobiSum_one`: if `∏ᵢ χᵢ ≠ 1`, then
  `g(∏ᵢ χᵢ, ψ) J(χ) = ∏ᵢ g(χᵢ, ψ)` for every additive character `ψ`.
* `TauCeti.multiJacobiSum_one_eq_prod_gaussSum_div`: if moreover `ψ` is primitive and the number
  of elements of the field is nonzero in the value field, then `J(χ) = ∏ᵢ g(χᵢ, ψ) / g(∏ᵢ χᵢ, ψ)`.
* `TauCeti.multiJacobiSum_zero_of_prod_eq_one`: if `∏ᵢ χᵢ = 1`, then
  `J₀(χ) = χ_p(-1) (q - 1) J(χ')`.
* `TauCeti.multiJacobiSum_one_eq_mul_jacobiSum`, `TauCeti.multiJacobiSum_one_of_prod_eq_one`: the
  recursions `J(χ) = J(χ') J(χ_p, ∏ᵢ χ'ᵢ)` if `∏ᵢ χ'ᵢ ≠ 1`, and `J(χ) = -χ_p(-1) J(χ')` if
  `∏ᵢ χᵢ = 1 ≠ χ_p`.
* `TauCeti.norm_multiJacobiSum_one_of_prod_ne_one`,
  `TauCeti.norm_multiJacobiSum_one_of_prod_eq_one`: for `r ≥ 1` nontrivial complex characters,
  `‖J(χ)‖ = √q ^ (r - 1)` if `∏ᵢ χᵢ ≠ 1` and `‖J(χ)‖ = √q ^ (r - 2)` if `∏ᵢ χᵢ = 1`.

Here `χ'` is the family `χ` with its `p`-th character removed, `Fin.removeNth p χ`, and `q` is the
number of elements of the field.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed., Chapter 8,
  §5 (Proposition 8.5.1, Theorem 3 and its corollaries).
* B. C. Berndt, R. J. Evans and K. S. Williams, *Gauss and Jacobi Sums*, Chapter 10.
-/

public section

open Finset

namespace TauCeti

section CommRing

variable {ι R R' : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Fintype R] [DecidableEq R]
  [CommRing R']

/-- The **multiple Jacobi sum** `J_t(χ) = ∑_{x₁ + ⋯ + x_r = t} χ₁(x₁) ⋯ χ_r(x_r)` of a family
`χ` of multiplicative characters of a finite commutative ring `R`, summed over the tuples
`x : ι → R` with `∑ᵢ xᵢ = t`. The classical multiple Jacobi sum `J(χ₁, …, χ_r)` is the sum at
`t = 1` and the sum `J₀(χ₁, …, χ_r)` is the sum at `t = 0`; for two characters the former is
Mathlib's `jacobiSum` (`TauCeti.multiJacobiSum_fin_two_one`). -/
def multiJacobiSum (χ : ι → MulChar R R') (t : R) : R' :=
  ∑ x : ι → R with ∑ i, x i = t, ∏ i, χ i (x i)

/-- The multiple Jacobi sum `J_t(χ)` is the sum of `∏ᵢ χᵢ(xᵢ)` over the tuples with
`∑ᵢ xᵢ = t`. -/
theorem multiJacobiSum_def (χ : ι → MulChar R R') (t : R) :
    multiJacobiSum χ t = ∑ x : ι → R with ∑ i, x i = t, ∏ i, χ i (x i) :=
  (rfl)

/-- With no characters the only tuple is the empty one, whose sum is `0`. -/
@[simp]
theorem multiJacobiSum_of_isEmpty [IsEmpty ι] (χ : ι → MulChar R R') (t : R) :
    multiJacobiSum χ t = if t = 0 then 1 else 0 := by
  split_ifs with ht <;> simp [multiJacobiSum_def, eq_comm, ht]

/-- For a single character `χ`, `J_t(χ) = χ(t)`. -/
@[simp]
theorem multiJacobiSum_of_unique [Unique ι] (χ : ι → MulChar R R') (t : R) :
    multiJacobiSum χ t = χ default t := by
  rw [multiJacobiSum_def, sum_filter, ← (Equiv.funUnique ι R).symm.sum_comp]
  simp

/-- Reindexing the family of characters along a bijection does not change the multiple Jacobi
sum. -/
@[simp]
theorem multiJacobiSum_comp_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (χ : ι → MulChar R R') (t : R) : multiJacobiSum (χ ∘ e) t = multiJacobiSum χ t := by
  rw [multiJacobiSum_def, multiJacobiSum_def, sum_filter, sum_filter,
    ← (e.arrowCongr (Equiv.refl R)).symm.sum_comp]
  refine sum_congr rfl fun x _ ↦ ?_
  simp [e.sum_comp (fun i ↦ x i), e.prod_comp (fun i ↦ χ i (x i))]

/-- **Splitting off one character.** Separating the `p`-th coordinate,
`J_t(χ) = ∑_y χ_p(y) J_{t - y}(χ')`, where `χ'` is the family with `χ_p` removed. -/
theorem multiJacobiSum_eq_sum_mul {n : ℕ} (χ : Fin (n + 1) → MulChar R R') (p : Fin (n + 1))
    (t : R) : multiJacobiSum χ t = ∑ y, χ p y * multiJacobiSum (p.removeNth χ) (t - y) := by
  simp only [multiJacobiSum_def, sum_filter, mul_sum]
  rw [← (Fin.insertNthEquiv (fun _ ↦ R) p).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ ?_
  simp [Fin.sum_univ_succAbove _ p, Fin.prod_univ_succAbove _ p, eq_sub_iff_add_eq, add_comm y,
    Fin.removeNth]

/-- For two characters, `J_t(χ, φ) = ∑_x χ(x) φ(t - x)`. -/
theorem multiJacobiSum_fin_two (χ φ : MulChar R R') (t : R) :
    multiJacobiSum ![χ, φ] t = ∑ x, χ x * φ (t - x) := by
  rw [multiJacobiSum_eq_sum_mul _ 0]
  simp [multiJacobiSum_of_unique]

/-- For two characters, the multiple Jacobi sum at `1` is Mathlib's `jacobiSum`. -/
@[simp]
theorem multiJacobiSum_fin_two_one (χ φ : MulChar R R') :
    multiJacobiSum ![χ, φ] 1 = jacobiSum χ φ :=
  multiJacobiSum_fin_two χ φ 1

/-- **Scaling.** Multiplying the target `t` by a unit `u` multiplies the multiple Jacobi sum by
the value at `u` of the product of the characters. -/
theorem multiJacobiSum_mul_of_isUnit (χ : ι → MulChar R R') {u : R} (hu : IsUnit u) (t : R) :
    multiJacobiSum χ (u * t) = (∏ i, χ i) u * multiJacobiSum χ t := by
  obtain ⟨u, rfl⟩ := hu
  rw [multiJacobiSum_def, multiJacobiSum_def, sum_filter, sum_filter, mul_sum,
    ← (Equiv.piCongrRight fun _ ↦ Units.mulLeft u).sum_comp]
  refine sum_congr rfl fun x _ ↦ ?_
  simp [← mul_sum, MulChar.prod_apply_coe, prod_mul_distrib]

/-- **Weighted sums.** For units `aᵢ`, the sum of `∏ᵢ χᵢ(xᵢ)` over the tuples with
`∑ᵢ aᵢ xᵢ = t` is `∏ᵢ χᵢ(aᵢ⁻¹) J_t(χ)`. -/
theorem sum_filter_sum_mul_eq_prod_mul_multiJacobiSum (χ : ι → MulChar R R') (a : ι → Rˣ)
    (t : R) :
    ∑ x : ι → R with ∑ i, (a i : R) * x i = t, ∏ i, χ i (x i) =
      (∏ i, χ i ↑(a i)⁻¹) * multiJacobiSum χ t := by
  rw [multiJacobiSum_def, sum_filter, sum_filter, mul_sum,
    ← (Equiv.piCongrRight fun i ↦ Units.mulLeft (a i)⁻¹).sum_comp]
  refine sum_congr rfl fun x _ ↦ ?_
  simp [prod_mul_distrib]

/-- At a unit `t`, the multiple Jacobi sum is `(∏ᵢ χᵢ)(t) J(χ)`. -/
theorem multiJacobiSum_eq_mul_multiJacobiSum_one (χ : ι → MulChar R R') {t : R}
    (ht : IsUnit t) : multiJacobiSum χ t = (∏ i, χ i) t * multiJacobiSum χ 1 := by
  simpa using multiJacobiSum_mul_of_isUnit χ ht 1

/-- If the product of the characters is nontrivial, then `J₀(χ) = 0`. -/
theorem multiJacobiSum_zero_eq_zero [IsDomain R'] {χ : ι → MulChar R R'}
    (hχ : ∏ i, χ i ≠ 1) : multiJacobiSum χ 0 = 0 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  refine eq_zero_of_mul_eq_self_left hu ?_
  simpa using (multiJacobiSum_mul_of_isUnit χ u.isUnit 0).symm

end CommRing

section FiniteField

variable {ι F R : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
  [CommRing R]

/-- **Products of Gauss sums.** For any additive character `ψ`,
`∏ᵢ g(χᵢ, ψ) = g(∏ᵢ χᵢ, ψ) J(χ) + J₀(χ)`. -/
theorem prod_gaussSum_eq_gaussSum_prod_mul_add (χ : ι → MulChar F R) (ψ : AddChar F R) :
    ∏ i, gaussSum (χ i) ψ =
      gaussSum (∏ i, χ i) ψ * multiJacobiSum χ 1 + multiJacobiSum χ 0 := by
  have hfib : ∀ t, ψ t * multiJacobiSum χ t =
      (∏ i, χ i) t * ψ t * multiJacobiSum χ 1 + if t = 0 then multiJacobiSum χ 0 else 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [MulChar.map_zero]
    · rw [multiJacobiSum_eq_mul_multiJacobiSum_one χ (IsUnit.mk0 t ht)]
      simp only [ht, ↓reduceIte, add_zero]
      ring
  calc ∏ i, gaussSum (χ i) ψ = ∑ x : ι → F, ψ (∑ i, x i) * ∏ i, χ i (x i) := by
        simp only [gaussSum, prod_univ_sum, Fintype.piFinset_univ, prod_mul_distrib,
          AddChar.map_sum_eq_prod, mul_comm]
    _ = ∑ t, ψ t * multiJacobiSum χ t := by
        rw [← sum_fiberwise univ (fun x : ι → F ↦ ∑ i, x i)]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [multiJacobiSum_def, mul_sum]
        exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2]
    _ = _ := by
        simp_rw [hfib, sum_add_distrib, ← sum_mul, gaussSum, sum_ite_eq', mem_univ, ite_true]

/-- **The Gauss-sum relation.** If the product of the characters is nontrivial, then
`g(∏ᵢ χᵢ, ψ) J(χ) = ∏ᵢ g(χᵢ, ψ)` for any additive character `ψ`. -/
theorem gaussSum_prod_mul_multiJacobiSum_one [IsDomain R] {χ : ι → MulChar F R}
    (hχ : ∏ i, χ i ≠ 1) (ψ : AddChar F R) :
    gaussSum (∏ i, χ i) ψ * multiJacobiSum χ 1 = ∏ i, gaussSum (χ i) ψ := by
  rw [prod_gaussSum_eq_gaussSum_prod_mul_add, multiJacobiSum_zero_eq_zero hχ, add_zero]

/-- **Multiple Jacobi sums as quotients of Gauss sums.** If the product of the characters is
nontrivial, `ψ` is primitive and the number of elements of `F` is nonzero in `F'`, then
`J(χ) = ∏ᵢ g(χᵢ, ψ) / g(∏ᵢ χᵢ, ψ)`. -/
theorem multiJacobiSum_one_eq_prod_gaussSum_div {F' : Type*} [Field F']
    (h : (Fintype.card F : F') ≠ 0) {χ : ι → MulChar F F'} (hχ : ∏ i, χ i ≠ 1)
    {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    multiJacobiSum χ 1 = (∏ i, gaussSum (χ i) ψ) / gaussSum (∏ i, χ i) ψ := by
  rw [eq_div_iff (gaussSum_ne_zero_of_nontrivial h hχ hψ), mul_comm]
  exact gaussSum_prod_mul_multiJacobiSum_one hχ ψ

/-- **The recursion for `J₀`.** If the product of the characters is trivial, then removing the
`p`-th character gives `J₀(χ) = χ_p(-1) (q - 1) J(χ')`. -/
theorem multiJacobiSum_zero_of_prod_eq_one {n : ℕ} {χ : Fin (n + 1) → MulChar F R}
    (hχ : ∏ i, χ i = 1) (p : Fin (n + 1)) :
    multiJacobiSum χ 0 =
      χ p (-1) * (Fintype.card F - 1) * multiJacobiSum (p.removeNth χ) 1 := by
  have hp : χ p * ∏ i, p.removeNth χ i = 1 := (Fin.mul_prod_removeNth p χ).trans hχ
  have hneg : (∏ i, p.removeNth χ i) (-1) = χ p (-1) := by
    rw [eq_inv_of_mul_eq_one_right hp, MulChar.inv_apply', inv_neg, inv_one]
  have hterm : ∀ y : F, χ p y * multiJacobiSum (p.removeNth χ) (0 - y) =
      χ p (-1) * (1 : MulChar F R) y * multiJacobiSum (p.removeNth χ) 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [MulChar.map_zero]
    · rw [zero_sub, multiJacobiSum_eq_mul_multiJacobiSum_one _ (IsUnit.mk0 _ (neg_ne_zero.mpr hy)),
        neg_eq_neg_one_mul, map_mul, hneg, ← hp, MulChar.mul_apply]
      ring
  rw [multiJacobiSum_eq_sum_mul χ p, sum_congr rfl fun y _ ↦ hterm y, ← sum_mul, ← mul_sum,
    MulChar.sum_one_eq_card_units, Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- **The recursion for `J`.** If the product of the characters other than the `p`-th one is
nontrivial, then removing the `p`-th character gives `J(χ) = J(χ') J(χ_p, ∏ᵢ χ'ᵢ)`, the last
factor being Mathlib's `jacobiSum`. -/
theorem multiJacobiSum_one_eq_mul_jacobiSum [IsDomain R] {n : ℕ} {χ : Fin (n + 1) → MulChar F R}
    {p : Fin (n + 1)} (hχ : ∏ i, p.removeNth χ i ≠ 1) :
    multiJacobiSum χ 1 =
      multiJacobiSum (p.removeNth χ) 1 * jacobiSum (χ p) (∏ i, p.removeNth χ i) := by
  have hterm : ∀ y : F, χ p y * multiJacobiSum (p.removeNth χ) (1 - y) =
      multiJacobiSum (p.removeNth χ) 1 * (χ p y * (∏ i, p.removeNth χ i) (1 - y)) := by
    intro y
    rcases eq_or_ne (1 - y) 0 with hy | hy
    · simp [hy, MulChar.map_zero, multiJacobiSum_zero_eq_zero hχ]
    · rw [multiJacobiSum_eq_mul_multiJacobiSum_one _ (IsUnit.mk0 _ hy)]
      ring
  rw [multiJacobiSum_eq_sum_mul χ p, sum_congr rfl fun y _ ↦ hterm y, ← mul_sum, jacobiSum]

/-- If the product of the characters is trivial and the `p`-th character `χ_p` is not, then
removing it gives `J(χ) = -χ_p(-1) J(χ')`. -/
theorem multiJacobiSum_one_of_prod_eq_one [IsDomain R] {n : ℕ} {χ : Fin (n + 1) → MulChar F R}
    (hχ : ∏ i, χ i = 1) {p : Fin (n + 1)} (hp : χ p ≠ 1) :
    multiJacobiSum χ 1 = -χ p (-1) * multiJacobiSum (p.removeNth χ) 1 := by
  have hinv : ∏ i, p.removeNth χ i = (χ p)⁻¹ :=
    eq_inv_of_mul_eq_one_right ((Fin.mul_prod_removeNth p χ).trans hχ)
  rw [multiJacobiSum_one_eq_mul_jacobiSum (hinv ▸ inv_ne_one.mpr hp), hinv,
    jacobiSum_nontrivial_inv hp, mul_comm]

end FiniteField

section Complex

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- **The absolute value of `J`, nontrivial product.** If every character and their product are
nontrivial, then `‖J(χ)‖ = √q ^ (r - 1)`, for `r` characters on a field with `q` elements. -/
theorem norm_multiJacobiSum_one_of_prod_ne_one {χ : ι → MulChar F ℂ} (hχ : ∀ i, χ i ≠ 1)
    (hprod : ∏ i, χ i ≠ 1) :
    ‖multiJacobiSum χ 1‖ = √(Fintype.card F) ^ (Fintype.card ι - 1) := by
  have hψ := FiniteField.isPrimitive_stdAddChar F
  have hι : 0 < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · exact absurd (by simp) hprod
    · exact Fintype.card_pos
  have hq : 0 < √(Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h := congrArg norm (gaussSum_prod_mul_multiJacobiSum_one hprod (FiniteField.stdAddChar F))
  rw [norm_mul, norm_prod, norm_gaussSum hprod hψ, prod_congr rfl fun i _ ↦ norm_gaussSum (hχ i) hψ,
    prod_const, card_univ, ← Nat.sub_add_cancel hι, pow_succ, mul_comm] at h
  exact mul_right_cancel₀ hq.ne' h

/-- **The absolute value of `J`, trivial product.** If every character is nontrivial but their
product is trivial, then `‖J(χ)‖ = √q ^ (r - 2)`, for `r ≥ 1` characters on a field with `q`
elements. -/
theorem norm_multiJacobiSum_one_of_prod_eq_one [Nonempty ι] {χ : ι → MulChar F ℂ}
    (hχ : ∀ i, χ i ≠ 1) (hprod : ∏ i, χ i = 1) :
    ‖multiJacobiSum χ 1‖ = √(Fintype.card F) ^ (Fintype.card ι - 2) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e := Fintype.equivFinOfCardEq hn
  have hprod' : ∏ i, (χ ∘ e.symm) i = 1 := by
    rwa [Function.comp_def, e.symm.prod_comp (fun i ↦ χ i)]
  have hp : (χ ∘ e.symm) 0 ≠ 1 := hχ _
  have hrem : ∏ i, Fin.removeNth 0 (χ ∘ e.symm) i ≠ 1 := fun h ↦ hp <| by
    simpa only [h, mul_one] using (Fin.mul_prod_removeNth 0 (χ ∘ e.symm)).trans hprod'
  rw [← multiJacobiSum_comp_equiv e.symm, multiJacobiSum_one_of_prod_eq_one hprod' hp, norm_mul,
    norm_neg, ← Units.coe_neg_one, MulChar.norm_apply_unit, one_mul,
    norm_multiJacobiSum_one_of_prod_ne_one (χ := Fin.removeNth 0 (χ ∘ e.symm)) (fun _ ↦ hχ _) hrem,
    Fintype.card_fin, hn]
  exact congrArg (√(Fintype.card F) ^ ·) (by omega)

end Complex

end TauCeti
