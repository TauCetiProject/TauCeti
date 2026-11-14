/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Residue bijections and floor-sum reciprocity for coprime naturals

For coprime natural numbers `m` and `n`, multiplication by `m` modulo `n` permutes the nonzero
residues `Finset.Ico 1 n`, and the open diagonal `n * y = m * x` misses every lattice point of the
rectangle `Finset.Ico 1 n ×ˢ Finset.Ico 1 m`. Partitioning that rectangle into the triangles below
and above the diagonal yields a general two-variable reciprocity identity for sums (and products)
indexed by integer quotients `m * x / n` and `n * y / m`, from which both Gauss's floor-sum
reciprocity and Rademacher's weighted square floor-sum identity follow by specialization.

## Main results

* `Nat.Coprime.bijOn_mul_mod_Ico`: `x ↦ m * x % n` is a bijection on `Finset.Ico 1 n`.
* `Nat.Coprime.image_mul_mod_Ico`, `Nat.Coprime.prod_Ico_mul_mod`, `Nat.Coprime.sum_Ico_mul_mod`:
  image and reindexing formulas for `x ↦ m * x % n` on `Finset.Ico 1 n`.
* `Nat.Coprime.prod_Ico_mul_div_mul_prod_Ico_mul_div`,
  `Nat.Coprime.sum_Ico_mul_div_add_sum_Ico_mul_div`: partitioning `Ico 1 n ×ˢ Ico 1 m` across the
  diagonal `n * y = m * x`.
* `Nat.Coprime.sum_mul_div_add_sum_mul_div`: Gauss's floor-sum reciprocity
  `∑ x ∈ Ico 1 n, m * x / n + ∑ y ∈ Ico 1 m, n * y / m = (n - 1) * (m - 1)`.
* `Nat.Coprime.sum_sq_mul_div_add_sum_odd_mul_div`: weighted square floor-sum reciprocity
  `∑ x ∈ Ico 1 n, (m * x / n) ^ 2 + ∑ y ∈ Ico 1 m, (2 * y - 1) * (n * y / m) =
  (n - 1) * (m - 1) ^ 2`.

## References

* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, 1972, Ch. 1.
-/

public section

namespace Nat

/-- For coprime `m` and `n`, the residue map `x ↦ m * x % n` is a bijection from `Finset.Ico 1 n`
to itself. No positivity hypothesis on `m` or `n` is needed, since `Finset.Ico 1 n` is empty for
`n ≤ 1`. -/
theorem Coprime.bijOn_mul_mod_Ico {m n : ℕ} (hmn : m.Coprime n) :
    Set.BijOn (fun x ↦ m * x % n) (Finset.Ico 1 n) (Finset.Ico 1 n) := by
  rcases le_or_gt n 1 with hn | hn
  · have hempty : (Finset.Ico 1 n : Set ℕ) = ∅ := by simp [hn]
    rw [hempty]
    exact Set.bijOn_empty _
  · have hmaps : Set.MapsTo (fun x ↦ m * x % n) (Finset.Ico 1 n) (Finset.Ico 1 n) := by
      intro x hx
      simp only [Finset.coe_Ico, Set.mem_Ico] at hx ⊢
      refine ⟨?_, Nat.mod_lt _ (by omega)⟩
      by_contra h0
      have hdvd : n ∣ m * x := Nat.dvd_of_mod_eq_zero (by omega)
      have hnx : n ∣ x := hmn.symm.dvd_of_dvd_mul_left hdvd
      exact absurd (Nat.le_of_dvd (by omega) hnx) (by omega)
    have hinj : Set.InjOn (fun x ↦ m * x % n) (Finset.Ico 1 n) := by
      intro x₁ hx₁ x₂ hx₂ hmod
      simp only [Finset.coe_Ico, Set.mem_Ico] at hx₁ hx₂
      have hcongr : x₁ ≡ x₂ [MOD n] := Nat.ModEq.cancel_left_of_coprime hmn.symm hmod
      exact hcongr.eq_of_lt_of_lt hx₁.2 hx₂.2
    have himg : (Finset.Ico 1 n).image (fun x ↦ m * x % n) = Finset.Ico 1 n :=
      Finset.eq_of_subset_of_card_le
        (fun y hy ↦ by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact hmaps hx)
        (by rw [Finset.card_image_of_injOn hinj])
    refine ⟨hmaps, hinj, fun y hy ↦ ?_⟩
    rw [← himg, Finset.coe_image] at hy
    exact hy

/-- For coprime `m` and `n`, the image of `Finset.Ico 1 n` under `x ↦ m * x % n` is
`Finset.Ico 1 n`. -/
theorem Coprime.image_mul_mod_Ico {m n : ℕ} (hmn : m.Coprime n) :
    (Finset.Ico 1 n).image (fun x ↦ m * x % n) = Finset.Ico 1 n :=
  Finset.coe_injective <| by simpa [Finset.coe_image] using hmn.bijOn_mul_mod_Ico.image_eq

/-- Reindex a product over `Finset.Ico 1 n` along the permutation `x ↦ m * x % n` for coprime
`m` and `n`. -/
@[to_additive Coprime.sum_Ico_mul_mod
  /-- Reindex a sum over `Finset.Ico 1 n` along the permutation `x ↦ m * x % n` for coprime `m`
  and `n`. -/]
theorem Coprime.prod_Ico_mul_mod {M : Type*} [CommMonoid M] {m n : ℕ} (hmn : m.Coprime n)
    (f : ℕ → M) :
    ∏ x ∈ Finset.Ico 1 n, f (m * x % n) = ∏ r ∈ Finset.Ico 1 n, f r := by
  rw [← Finset.prod_image hmn.bijOn_mul_mod_Ico.injOn, hmn.image_mul_mod_Ico]

private theorem Ico_mul_div_add_one_eq_filter {m n x : ℕ} (hm : 0 < m) (hn : 0 < n) (hx : x < n) :
    Finset.Ico 1 (m * x / n + 1) = {y ∈ Finset.Ico 1 m | n * y ≤ m * x} := by
  ext y
  have hlt : m * x / n < m :=
    (Nat.div_lt_iff_lt_mul hn).mpr (Nat.mul_lt_mul_of_pos_left hx hm)
  have hle : n * y ≤ m * x ↔ y ≤ m * x / n := by
    rw [Nat.le_div_iff_mul_le hn, mul_comm]
  simp only [Finset.mem_Ico, Finset.mem_filter, Nat.lt_succ_iff, hle]
  omega

/-- For coprime `m` and `n`, the open diagonal `n * y = m * x` avoids every lattice point of
`Finset.Ico 1 n ×ˢ Finset.Ico 1 m`, partitioning a two-variable product into the products over the
two triangles `1 ≤ y ≤ m * x / n` and `1 ≤ x ≤ n * y / m`. -/
@[to_additive Coprime.sum_Ico_mul_div_add_sum_Ico_mul_div
  /-- For coprime `m` and `n`, the open diagonal `n * y = m * x` avoids every lattice point of
  `Finset.Ico 1 n ×ˢ Finset.Ico 1 m`, partitioning a two-variable sum into the sums over the two
  triangles `1 ≤ y ≤ m * x / n` and `1 ≤ x ≤ n * y / m`. -/]
theorem Coprime.prod_Ico_mul_div_mul_prod_Ico_mul_div {M : Type*} [CommMonoid M] {m n : ℕ}
    (hmn : m.Coprime n) (F : ℕ → ℕ → M) :
    (∏ x ∈ Finset.Ico 1 n, ∏ y ∈ Finset.Ico 1 (m * x / n + 1), F x y) *
        (∏ y ∈ Finset.Ico 1 m, ∏ x ∈ Finset.Ico 1 (n * y / m + 1), F x y) =
      ∏ x ∈ Finset.Ico 1 n, ∏ y ∈ Finset.Ico 1 m, F x y := by
  rcases eq_or_ne m 0 with rfl | hm0
  · obtain rfl : n = 1 := (Nat.coprime_zero_left n).mp hmn
    simp
  rcases eq_or_ne n 0 with rfl | hn0
  · obtain rfl : m = 1 := (Nat.coprime_zero_right m).mp hmn
    simp
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let R := Finset.Ico 1 n ×ˢ Finset.Ico 1 m
  have h1 : ∏ x ∈ Finset.Ico 1 n, ∏ y ∈ Finset.Ico 1 (m * x / n + 1), F x y =
      ∏ p ∈ {p ∈ R | n * p.2 ≤ m * p.1}, F p.1 p.2 := by
    have hcongr : ∀ x ∈ Finset.Ico 1 n,
        ∏ y ∈ Finset.Ico 1 (m * x / n + 1), F x y =
          ∏ y ∈ Finset.Ico 1 m with n * y ≤ m * x, F x y := fun x hx ↦
      congrArg (fun s ↦ ∏ y ∈ s, F x y)
        (Ico_mul_div_add_one_eq_filter hm hn (Finset.mem_Ico.mp hx).2)
    rw [Finset.prod_congr rfl hcongr]
    simp [R, Finset.prod_filter, Finset.prod_product]
  have h2 : ∏ y ∈ Finset.Ico 1 m, ∏ x ∈ Finset.Ico 1 (n * y / m + 1), F x y =
      ∏ p ∈ {p ∈ R | m * p.1 ≤ n * p.2}, F p.1 p.2 := by
    have hcongr : ∀ y ∈ Finset.Ico 1 m,
        ∏ x ∈ Finset.Ico 1 (n * y / m + 1), F x y =
          ∏ x ∈ Finset.Ico 1 n with m * x ≤ n * y, F x y := fun y hy ↦
      congrArg (fun s ↦ ∏ x ∈ s, F x y)
        (Ico_mul_div_add_one_eq_filter hn hm (Finset.mem_Ico.mp hy).2)
    rw [Finset.prod_congr rfl hcongr]
    simp [R, Finset.prod_filter, Finset.prod_product_right]
  have hdisj : Disjoint {p ∈ R | n * p.2 ≤ m * p.1} {p ∈ R | m * p.1 ≤ n * p.2} := by
    refine Finset.disjoint_filter.mpr fun p hp hle hge ↦ ?_
    simp only [R, Finset.mem_product, Finset.mem_Ico] at hp
    have heq : m * p.1 = n * p.2 := le_antisymm hge hle
    have hdvd : n ∣ m * p.1 := ⟨p.2, heq⟩
    have hnp : n ∣ p.1 := hmn.symm.dvd_of_dvd_mul_left hdvd
    exact absurd (Nat.le_of_dvd (by omega) hnp) (by omega)
  have hunion : {p ∈ R | n * p.2 ≤ m * p.1} ∪ {p ∈ R | m * p.1 ≤ n * p.2} = R := by
    ext p
    have htot := Nat.le_total (n * p.2) (m * p.1)
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  rw [h1, h2, ← Finset.prod_union hdisj, hunion, Finset.prod_product]

/-- **Gauss's floor-sum reciprocity** for coprime natural numbers `m` and `n`:
`∑ x ∈ Ico 1 n, m * x / n + ∑ y ∈ Ico 1 m, n * y / m = (n - 1) * (m - 1)`. -/
theorem Coprime.sum_mul_div_add_sum_mul_div {m n : ℕ} (hmn : m.Coprime n) :
    ∑ x ∈ Finset.Ico 1 n, m * x / n + ∑ y ∈ Finset.Ico 1 m, n * y / m = (n - 1) * (m - 1) := by
  simpa using hmn.sum_Ico_mul_div_add_sum_Ico_mul_div fun _ _ ↦ (1 : ℕ)

private theorem sum_Ico_two_mul_sub_one (k : ℕ) :
    ∑ y ∈ Finset.Ico 1 (k + 1), (2 * y - 1) = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring

/-- **Weighted square floor-sum reciprocity** (Rademacher): for coprime natural numbers `m` and `n`,
`∑ x ∈ Ico 1 n, (m * x / n) ^ 2 + ∑ y ∈ Ico 1 m, (2 * y - 1) * (n * y / m) =
(n - 1) * (m - 1) ^ 2`. -/
theorem Coprime.sum_sq_mul_div_add_sum_odd_mul_div {m n : ℕ} (hmn : m.Coprime n) :
    ∑ x ∈ Finset.Ico 1 n, (m * x / n) ^ 2 +
        ∑ y ∈ Finset.Ico 1 m, (2 * y - 1) * (n * y / m) =
      (n - 1) * (m - 1) ^ 2 := by
  have h := hmn.sum_Ico_mul_div_add_sum_Ico_mul_div fun _ y ↦ 2 * y - 1
  have h1 : ∀ x ∈ Finset.Ico 1 n,
      ∑ y ∈ Finset.Ico 1 (m * x / n + 1), (2 * y - 1) = (m * x / n) ^ 2 := fun x _ ↦
    sum_Ico_two_mul_sub_one _
  have h2 : ∀ y ∈ Finset.Ico 1 m,
      ∑ _ ∈ Finset.Ico 1 (n * y / m + 1), (2 * y - 1) = (2 * y - 1) * (n * y / m) := by
    intro y _
    rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, Nat.nsmul_eq_mul, mul_comm]
  have h3 : ∑ y ∈ Finset.Ico 1 m, (2 * y - 1) = (m - 1) ^ 2 := by
    rcases m with _ | m
    · simp
    · simpa using sum_Ico_two_mul_sub_one m
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h
  simpa [h3] using h

end Nat
