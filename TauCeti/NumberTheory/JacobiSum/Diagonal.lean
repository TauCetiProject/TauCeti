/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Multiple
public import TauCeti.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.MulChar.Cyclic
import TauCeti.NumberTheory.MulChar.Orthogonality
import TauCeti.NumberTheory.MulChar.Real

/-!
# Diagonal equations over finite fields

Let `F` be a finite field with `q` elements. For units `aᵢ ∈ F`, exponents `dᵢ ≥ 1` and `b ∈ F`,
the number `N` of solutions `x ∈ F ^ r` of the diagonal equation `∑ᵢ aᵢ xᵢ ^ dᵢ = b` is expressed
through multiple Jacobi sums. Writing the number of `d`-th roots of `u` as `1 + ∑ χ(u)`, over the
nontrivial characters with `χ ^ d = 1` (`TauCeti.card_pow_eq_eq_one_add_sum_filter_mulChar`), and
expanding the product over `i`, the terms with some trivial factor contribute `q ^ (r - 1)` and
`0`, and the others are multiple Jacobi sums:
`N = q ^ (r - 1) + ∑_χ ∏ᵢ χᵢ(aᵢ⁻¹) J_b(χ)`.

For `b ≠ 0` every `J_b(χ)` has absolute value at most `√q ^ (r - 1)`, and there are at most
`∏ᵢ (dᵢ - 1)` families `χ`, which bounds the error `|N - q ^ (r - 1)|`. For `b = 0` no such bound
holds: `x² + y² = 0` has `2q - 1` solutions when `q ≡ 1 (mod 4)`.

The characters take complex values, so no divisibility `dᵢ ∣ q - 1` is needed: the characters
with `χ ^ dᵢ = 1` are those with `χ ^ gcd(dᵢ, q - 1) = 1`.

## Main results

* `TauCeti.card_sum_mul_pow_eq`: the number of solutions of `∑ᵢ aᵢ xᵢ ^ dᵢ = b` is
  `q ^ (r - 1) + ∑_χ ∏ᵢ χᵢ(aᵢ⁻¹) J_b(χ)`.
* `TauCeti.abs_card_sum_mul_pow_eq_sub_le`: for `b ≠ 0` it differs from `q ^ (r - 1)` by at most
  `∏ᵢ (dᵢ - 1) · √q ^ (r - 1)`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed., Chapter 8,
  §7 (Theorem 5), and Chapter 10, §3.
* A. Weil, *Numbers of solutions of equations in finite fields*, Bull. Amer. Math. Soc. 55 (1949),
  497–508.
-/

public section

open Finset

namespace TauCeti

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- The solutions of `∑ᵢ aᵢ xᵢ ^ dᵢ = b`, counted through the values `uᵢ = xᵢ ^ dᵢ`. -/
private theorem card_sum_mul_pow_eq_sum_prod_card (a : ι → F) (d : ι → ℕ) (b : F) :
    #{x : ι → F | ∑ i, a i * x i ^ d i = b} =
      ∑ u : ι → F with ∑ i, a i * u i = b, ∏ i, #{y : F | y ^ d i = u i} := by
  rw [card_eq_sum_ones, ← sum_fiberwise_of_maps_to (g := fun x i ↦ x i ^ d i)
    (t := {u : ι → F | ∑ i, a i * u i = b}) (fun x hx ↦ by simpa using hx)]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [← card_eq_sum_ones, ← Fintype.card_piFinset]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and] at hu
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by simp [h, hu], h⟩⟩

/-- If `aⱼ ≠ 0` and `g` is invariant under translation of the `j`-th coordinate, then summing `g`
over all tuples is summing it over the `q` parallel hyperplanes `∑ᵢ aᵢ uᵢ = c`, on each of which
it has the same sum. -/
private theorem card_smul_sum_filter_sum_mul_eq {M : Type*} [AddCommMonoid M] {a : ι → F} {j : ι}
    (hj : a j ≠ 0) {g : (ι → F) → M} (hg : ∀ u c, g (u + Pi.single j c) = g u) (b : F) :
    Fintype.card F • ∑ u : ι → F with ∑ i, a i * u i = b, g u = ∑ u, g u := by
  have key : ∀ c, ∑ u : ι → F with ∑ i, a i * u i = c, g u =
      ∑ u : ι → F with ∑ i, a i * u i = b, g u := by
    intro c
    rw [sum_filter, sum_filter, ← Equiv.sum_comp (Equiv.addRight (Pi.single j ((c - b) / a j)))]
    refine sum_congr rfl fun u _ ↦ ?_
    have hsum : ∑ i, a i * (u i + Pi.single (M := fun _ ↦ F) j ((c - b) / a j) i) =
        ∑ i, a i * u i + (c - b) := by
      simp [mul_add, sum_add_distrib, Pi.single_apply, mul_div_cancel₀ _ hj]
    have hiff : ∑ i, a i * u i + (c - b) = c ↔ ∑ i, a i * u i = b := by
      constructor <;> intro h <;> linear_combination h
    simp only [Equiv.coe_addRight, Pi.add_apply, hsum, hg, hiff]
  rw [← sum_fiberwise univ (fun u : ι → F ↦ ∑ i, a i * u i) g]
  simp [key, card_univ]

/-- Over a hyperplane `∑ᵢ aᵢ uᵢ = b` with nonzero `aᵢ`, a product `∏_{i ∈ T} fᵢ(uᵢ)` over a proper
subset `T` of the coordinates, of functions with `∑_y fᵢ(y) = 0`, sums to `q ^ (r - 1)` when `T`
is empty and to `0` otherwise. -/
private theorem sum_filter_sum_mul_eq_prod_eq_ite {a : ι → F} (ha : ∀ i, a i ≠ 0)
    {f : ι → F → ℂ} (hf : ∀ i, ∑ y, f i y = 0) {T : Finset ι} (hT : T ≠ univ) (b : F) :
    ∑ u : ι → F with ∑ i, a i * u i = b, ∏ i ∈ T, f i (u i) =
      if T = ∅ then (Fintype.card F : ℂ) ^ (Fintype.card ι - 1) else 0 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ T := by simpa [eq_univ_iff_forall] using hT
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := card_smul_sum_filter_sum_mul_eq (ha j) (g := fun u ↦ ∏ i ∈ T, f i (u i))
    (fun u c ↦ prod_congr rfl fun i hi ↦ by
      rw [Pi.add_apply, Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj), add_zero]) b
  have hall : ∑ u : ι → F, ∏ i ∈ T, f i (u i) = ∏ i, ∑ y, if i ∈ T then f i y else 1 := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
    exact sum_congr rfl fun u _ ↦ by rw [prod_ite_mem, univ_inter]
  rw [nsmul_eq_mul, hall] at h
  split_ifs with hT0
  · have hι : Fintype.card ι = Fintype.card ι - 1 + 1 :=
      (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨j⟩)).symm
    refine mul_left_cancel₀ hq (h.trans ?_)
    simp [hT0, card_univ, ← pow_succ', ← hι]
  · obtain ⟨i, hi⟩ := ne_empty_iff_nonempty.mp hT0
    refine (mul_eq_zero.mp (h.trans (prod_eq_zero (mem_univ i) ?_))).resolve_left hq
    simpa [hi] using hf i

open scoped Classical in
/-- **Solutions of a diagonal equation.** For units `aᵢ`, positive exponents `dᵢ` and any `b`, the
number of solutions of `∑ᵢ aᵢ xᵢ ^ dᵢ = b` in `F ^ r`, `r ≥ 1`, is
`q ^ (r - 1) + ∑_χ ∏ᵢ χᵢ(aᵢ⁻¹) J_b(χ)`, the sum over the families of nontrivial characters `χᵢ`
with `χᵢ ^ dᵢ = 1`. For `b ≠ 0` the Jacobi sum `J_b(χ)` is `(∏ᵢ χᵢ)(b) J(χ)`
(`TauCeti.multiJacobiSum_eq_mul_multiJacobiSum_one`); for `b = 0` it is `J₀(χ)`. -/
theorem card_sum_mul_pow_eq [Nonempty ι] (a : ι → Fˣ) {d : ι → ℕ} (hd : ∀ i, d i ≠ 0) (b : F) :
    (#{x : ι → F | ∑ i, (a i : F) * x i ^ d i = b} : ℂ) =
      (Fintype.card F : ℂ) ^ (Fintype.card ι - 1) +
        ∑ χ ∈ Fintype.piFinset fun i ↦ ({χ | χ ^ d i = 1 ∧ χ ≠ 1} : Finset (MulChar F ℂ)),
          (∏ i, χ i ↑(a i)⁻¹) * multiJacobiSum χ b := by
  set S : ι → Finset (MulChar F ℂ) := fun i ↦ {χ | χ ^ d i = 1 ∧ χ ≠ 1}
  have hcount : ∀ i c, (#{y : F | y ^ d i = c} : ℂ) = 1 + ∑ χ ∈ S i, χ c := by
    intro i c
    have : NeZero (Monoid.exponent (Fˣ ⧸ (powMonoidHom (d i) : Fˣ →* Fˣ).range)) :=
      ⟨Monoid.exponent_ne_zero_of_finite⟩
    rw [← card_pow_eq_eq_one_add_sum_filter_mulChar (hd i), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hf : ∀ i, ∑ y, ∑ χ ∈ S i, χ y = 0 := fun i ↦ by
    rw [sum_comm]
    exact sum_eq_zero fun χ hχ ↦ MulChar.sum_eq_zero_of_ne_one (mem_filter.mp hχ).2.2
  have hne : (∅ : Finset ι) ≠ univ := (univ_nonempty (α := ι)).ne_empty.symm
  rw [card_sum_mul_pow_eq_sum_prod_card, Nat.cast_sum]
  simp_rw [Nat.cast_prod, hcount, prod_one_add]
  rw [sum_comm, sum_eq_add_of_mem ∅ univ (empty_mem_powerset _) (mem_powerset_self _) hne
    fun T _ hT ↦ (sum_filter_sum_mul_eq_prod_eq_ite (fun i ↦ (a i).ne_zero) hf hT.2 b).trans
      (ite_eq_right hT.1)]
  rw [sum_filter_sum_mul_eq_prod_eq_ite (fun i ↦ (a i).ne_zero) hf hne b, ite_eq_left rfl]
  congr 1
  simp_rw [prod_univ_sum]
  rw [sum_comm]
  exact sum_congr rfl fun χ _ ↦ sum_filter_sum_mul_eq_prod_mul_multiJacobiSum χ a b

omit [Fintype F] [DecidableEq F] in
/-- There are at most `d - 1` nontrivial characters `χ` with `χ ^ d = 1`, the character group
being cyclic. -/
private theorem card_filter_pow_eq_one_and_ne_one_le [Finite F] [DecidableEq (MulChar F ℂ)]
    {d : ℕ} (hd : d ≠ 0) : #{χ : MulChar F ℂ | χ ^ d = 1 ∧ χ ≠ 1} ≤ d - 1 := by
  have h := IsCyclic.card_pow_eq_one_le (α := MulChar F ℂ) (Nat.pos_of_ne_zero hd)
  have he : ({χ | χ ^ d = 1 ∧ χ ≠ 1} : Finset (MulChar F ℂ)) =
      ({χ | χ ^ d = 1} : Finset _).erase 1 := by
    ext; simp [and_comm]
  rw [he, card_erase_of_mem (by simp)]
  omega

/-- **The error term of a diagonal equation.** For units `aᵢ`, positive exponents `dᵢ` and
`b ≠ 0`, the number `N` of solutions of `∑ᵢ aᵢ xᵢ ^ dᵢ = b` in `F ^ r`, `r ≥ 1`, satisfies
`|N - q ^ (r - 1)| ≤ ∏ᵢ (dᵢ - 1) · √q ^ (r - 1)`. -/
theorem abs_card_sum_mul_pow_eq_sub_le [Nonempty ι] (a : ι → Fˣ) {d : ι → ℕ}
    (hd : ∀ i, d i ≠ 0) {b : F} (hb : b ≠ 0) :
    |(#{x : ι → F | ∑ i, (a i : F) * x i ^ d i = b} : ℝ) -
        (Fintype.card F : ℝ) ^ (Fintype.card ι - 1)| ≤
      (∏ i, (d i - 1) : ℕ) * √(Fintype.card F) ^ (Fintype.card ι - 1) := by
  classical
  have hq : 1 ≤ √(Fintype.card F : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos)
  have hterm : ∀ χ : ι → MulChar F ℂ, (∀ i, χ i ≠ 1) →
      ‖(∏ i, χ i ↑(a i)⁻¹) * multiJacobiSum χ b‖ ≤ √(Fintype.card F) ^ (Fintype.card ι - 1) := by
    intro χ hχ
    rw [norm_mul, norm_prod, prod_eq_one fun i _ ↦ MulChar.norm_apply_unit _ _, one_mul,
      multiJacobiSum_eq_mul_multiJacobiSum_one χ (IsUnit.mk0 b hb), norm_mul,
      ← Units.val_mk0 hb, MulChar.norm_apply_unit, one_mul]
    by_cases hprod : ∏ i, χ i = 1
    · rw [norm_multiJacobiSum_one_of_prod_eq_one hχ hprod]
      exact pow_le_pow_right₀ hq (by omega)
    · rw [norm_multiJacobiSum_one_of_prod_ne_one hχ hprod]
  have h := card_sum_mul_pow_eq a hd b
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [h, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ fun χ hχ ↦ hterm χ fun i ↦
    (mem_filter.mp (Fintype.mem_piFinset.mp hχ i)).2.2).trans ?_)
  rw [nsmul_eq_mul, Fintype.card_piFinset]
  gcongr
  exact_mod_cast prod_le_prod fun i _ ↦ card_filter_pow_eq_one_and_ne_one_le (hd i)

end TauCeti
