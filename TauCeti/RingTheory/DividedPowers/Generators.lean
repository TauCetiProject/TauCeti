/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import TauCeti.RingTheory.PowerSeries.DividedPowerSequence

/-!
# Divided powers from identities on generators

An additive divided-power candidate (`DividedPowers.AdditivePowers I`) on an ideal `I` of a
commutative semiring `A` is a family of maps `δ : ℕ → A → A`, vanishing outside `I`, that satisfies
the degree-zero, degree-one, ideal-membership, addition, and scalar-homogeneity axioms of a divided
power structure, without assuming the multiplication or iteration identities.

This file proves the generator criterion for divided powers (Stacks Project, Lemma 23.2.4, tag
07GP): if `I = Ideal.span S` and an additive candidate `δ` satisfies the multiplication identity
`δ m s * δ n s = (m + n).choose m * δ (m + n) s` and the iteration identity
`δ m (δ n s) = Nat.uniformBell m n * δ (m * n) s` (`n ≠ 0`) on every generator `s ∈ S`, then `δ`
extends to a `DividedPowers I` structure with the exact same operations.

Stability of the multiplication identity under sums follows directly from
`PowerSeries.coeff_mul_coeff_mul_eq_choose_nsmul`. Stability of the iteration identity under sums
is proved by expanding `δ m (δ n (x + y))` into a universal `ℕ`-linear combination of products
`δ a x * δ (m * n - a) y`, and evaluating the universal `ℕ`-valued coefficients once in the
polynomial ring `MvPolynomial (Fin 2) ℚ` using `DividedPowers.RatAlgebra.dividedPowers`, without
requiring `A` to embed in a `ℚ`-algebra.

## Main declarations

* `DividedPowers.AdditivePowers`: additive divided-power candidates on an ideal `I`.
* `DividedPowers.toAdditivePowers`: forgetting `mul_dpow` and `dpow_comp` from a `DividedPowers I`.
* `DividedPowers.AdditivePowers.mul_dpow_add`: stability of the multiplication identity under sums.
* `DividedPowers.AdditivePowers.dpow_comp_add`: stability of the iteration identity under sums.
* `DividedPowers.AdditivePowers.toDividedPowers`: constructing `DividedPowers I` from identities on
  a generating set `S` with `I = Ideal.span S`.
* `DividedPowers.AdditivePowers.toDividedPowers_unique`: uniqueness of a `DividedPowers I` with the
  same operations.

## References

* [Stacks Project, Divided Power Algebra, Lemma 23.2.4 (Tag 07GP)](https://stacks.math.columbia.edu/tag/07GP)
-/

public section

open Finset Nat

namespace DividedPowers

section CommSemiring

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/-- An additive divided-power candidate on an ideal `I` of a commutative semiring `A`: a family of
maps `ℕ → A → A`, vanishing outside `I`, satisfying the degree-zero, degree-one, ideal-membership,
addition, and scalar-homogeneity axioms of `DividedPowers`, without assuming multiplication or
iteration identities. -/
structure AdditivePowers where
  /-- The underlying family of divided-power candidate operations. -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x}, x ∉ I → dpow n x = 0
  dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1
  dpow_one : ∀ {x}, x ∈ I → dpow 1 x = x
  dpow_mem : ∀ {n x}, n ≠ 0 → x ∈ I → dpow n x ∈ I
  dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
    dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ {n} {a : A} {x}, x ∈ I → dpow n (a * x) = a ^ n * dpow n x

instance : CoeFun (AdditivePowers I) fun _ ↦ ℕ → A → A := ⟨fun δ ↦ δ.dpow⟩

variable {I}

/-- Two additive divided-power candidates on `I` that agree on `I` are equal. -/
@[ext]
theorem AdditivePowers.ext {δ δ' : AdditivePowers I}
    (h : ∀ (n : ℕ) {x : A}, x ∈ I → δ.dpow n x = δ'.dpow n x) : δ = δ' := by
  obtain ⟨d, h₀, _⟩ := δ
  obtain ⟨d', h₀', _⟩ := δ'
  simp only [AdditivePowers.mk.injEq]
  grind

/-- The coercion `AdditivePowers I → (ℕ → A → A)` is injective. -/
theorem AdditivePowers.coe_injective :
    Function.Injective (fun (δ : AdditivePowers I) ↦ (δ : ℕ → A → A)) := fun _ _ h ↦ by
  ext n x _
  exact congrFun (congrFun h n) x

/-- Forget the multiplication and iteration axioms of a `DividedPowers` structure to obtain an
`AdditivePowers` candidate with the same operations. -/
def toAdditivePowers (hI : DividedPowers I) : AdditivePowers I where
  dpow := hI.dpow
  dpow_null := hI.dpow_null
  dpow_zero := hI.dpow_zero
  dpow_one := hI.dpow_one
  dpow_mem := hI.dpow_mem
  dpow_add := hI.dpow_add
  dpow_mul := hI.dpow_mul

/-- The operations of `hI.toAdditivePowers` coincide with `hI.dpow` everywhere on `A`. -/
@[simp]
theorem toAdditivePowers_dpow (hI : DividedPowers I) (n : ℕ) (x : A) :
    hI.toAdditivePowers.dpow n x = hI.dpow n x := (rfl)

namespace AdditivePowers

variable (δ : AdditivePowers I)

/-- In positive degree, an additive candidate vanishes at `0`. -/
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : δ.dpow n 0 = 0 := by
  rw [← mul_zero (0 : A), δ.dpow_mul I.zero_mem, zero_pow hn, zero_mul, zero_mul]

/-- Variant of `AdditivePowers.dpow_add` indexed over `Finset.range (n + 1)`. -/
theorem dpow_add' {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    δ.dpow n (x + y) = ∑ k ∈ range (n + 1), δ.dpow k x * δ.dpow (n - k) y := by
  rw [δ.dpow_add hx hy, sum_antidiagonal_eq_sum_range_succ_mk]

/-- Multinomial expansion of an additive candidate on a finite sum of elements of `I`. -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    δ.dpow n (∑ i ∈ s, x i) =
      ∑ k ∈ s.sym n, ∏ i ∈ s, δ.dpow (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' δ.dpow δ.dpow_zero δ.dpow_add δ.dpow_eval_zero hx

/-- At an element `x ∈ I` where the multiplication identity holds, any finite product of candidate
operations at `x` reduces to a multinomial coefficient times a single operation. -/
theorem prod_dpow {ι : Type*} {s : Finset ι} {n : ι → ℕ} {x : A} (hx : x ∈ I)
    (hmul : ∀ p q, δ.dpow p x * δ.dpow q x = (p + q).choose p * δ.dpow (p + q) x) :
    (∏ i ∈ s, δ.dpow (n i) x) = Nat.multinomial s n * δ.dpow (∑ i ∈ s, n i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [δ.dpow_zero hx]
  | insert a s ha ih =>
    rw [prod_insert ha, ih, ← mul_assoc, mul_comm (δ.dpow (n a) x), mul_assoc, hmul,
      ← sum_insert ha, ← mul_assoc, Nat.multinomial_insert ha, mul_comm, Nat.cast_mul,
      sum_insert ha]
    ring

/-- The multiplication identity is stable under scalar multiplication. -/
theorem mul_dpow_mul {a x : A} (hx : x ∈ I)
    (hmul : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    (m n : ℕ) :
    δ.dpow m (a * x) * δ.dpow n (a * x) = (m + n).choose m * δ.dpow (m + n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul hx, δ.dpow_mul hx, mul_mul_mul_comm, ← pow_add, hmul m n]
  ring

/-- The multiplication identity is stable under sums. -/
theorem mul_dpow_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmulx : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    (hmuly : ∀ m n, δ.dpow m y * δ.dpow n y = (m + n).choose m * δ.dpow (m + n) y)
    (m n : ℕ) :
    δ.dpow m (x + y) * δ.dpow n (x + y) = (m + n).choose m * δ.dpow (m + n) (x + y) := by
  have hexp : PowerSeries.mk (fun k ↦ δ.dpow k (x + y)) =
      PowerSeries.mk (fun k ↦ δ.dpow k x) * PowerSeries.mk (fun k ↦ δ.dpow k y) :=
    DividedPowers.exp_add' δ.dpow fun _ ↦ δ.dpow_add hx hy
  have h := PowerSeries.coeff_mul_coeff_mul_eq_choose_nsmul
    (f := PowerSeries.mk fun k ↦ δ.dpow k x)
    (g := PowerSeries.mk fun k ↦ δ.dpow k y)
    (fun p q ↦ by simpa [nsmul_eq_mul] using hmulx p q)
    (fun p q ↦ by simpa [nsmul_eq_mul] using hmuly p q) m n
  simpa [← hexp, nsmul_eq_mul] using h

/-- The iteration identity is stable under scalar multiplication. -/
theorem dpow_comp_mul {a x : A} (hx : x ∈ I)
    (hcomp : ∀ m {n}, n ≠ 0 → δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (a * x)) = uniformBell m n * δ.dpow (m * n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul (δ.dpow_mem hn hx), hcomp m hn, δ.dpow_mul hx, ← pow_mul,
    mul_comm n m]
  ring

/-! ### Stability of the iteration identity under sums -/

/-- Universal `ℕ`-valued factor arising from expanding `δ c (δ k x * δ (n - k) y)` into
`(compTermWeight n k c) * (δ (c * k) x * δ (c * (n - k)) y)`. -/
private def compTermWeight (n k c : ℕ) : ℕ :=
  if k = 0 then uniformBell c n
  else Nat.multinomial (range c) (fun _ ↦ n - k) * uniformBell c k

/-- Total `x`-degree contributed by a multiset `μ` of summands in `δ n (x + y)`. -/
private def compXDeg (n : ℕ) {m : ℕ} (μ : Sym ℕ m) : ℕ :=
  ∑ k ∈ range (n + 1), Multiset.count k μ * k

/-- Total `y`-degree contributed by a multiset `μ` of summands in `δ n (x + y)`. -/
private def compYDeg (n : ℕ) {m : ℕ} (μ : Sym ℕ m) : ℕ :=
  ∑ k ∈ range (n + 1), Multiset.count k μ * (n - k)

/-- Universal `ℕ`-valued weight attached to a multiset `μ ∈ (range (n + 1)).sym m` when expanding
`δ m (δ n (x + y))`. -/
private def compSymWeight (n : ℕ) {m : ℕ} (μ : Sym ℕ m) : ℕ :=
  (∏ k ∈ range (n + 1), compTermWeight n k (Multiset.count k μ)) *
    Nat.multinomial (range (n + 1)) (fun k ↦ Multiset.count k μ * k) *
    Nat.multinomial (range (n + 1)) (fun k ↦ Multiset.count k μ * (n - k))

/-- Universal `ℕ`-valued coefficient of `δ a x * δ (m * n - a) y` in `δ m (δ n (x + y))`. -/
private def compCoeff (m n a : ℕ) : ℕ :=
  ∑ μ ∈ ((range (n + 1)).sym m).filter (fun μ ↦ compXDeg n μ = a), compSymWeight n μ

private theorem compXDeg_add_compYDeg {m n : ℕ} {μ : Sym ℕ m}
    (hμ : μ ∈ (range (n + 1)).sym m) :
    compXDeg n μ + compYDeg n μ = m * n := by
  have hsum : ∑ k ∈ range (n + 1), Multiset.count k (μ : Multiset ℕ) = m := by
    have hsub : (μ : Multiset ℕ).toFinset ⊆ range (n + 1) := fun k hk ↦
      (mem_sym_iff.mp hμ) k (Multiset.mem_toFinset.mp hk)
    rw [← sum_subset hsub (fun k _ hk ↦ Multiset.count_eq_zero.mpr
      (fun h ↦ hk (Multiset.mem_toFinset.mpr h))), Multiset.toFinset_sum_count_eq, μ.card_coe]
  unfold compXDeg compYDeg
  rw [← sum_add_distrib]
  calc ∑ k ∈ range (n + 1), (Multiset.count k μ * k + Multiset.count k μ * (n - k))
      = ∑ k ∈ range (n + 1), Multiset.count k μ * n := by
        refine sum_congr rfl fun k hk ↦ ?_
        rw [← mul_add, add_tsub_cancel_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    _ = (∑ k ∈ range (n + 1), Multiset.count k μ) * n := by rw [sum_mul]
    _ = m * n := by rw [hsum]

private theorem dpow_comp_term {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmuly : ∀ p q, δ.dpow p y * δ.dpow q y = (p + q).choose p * δ.dpow (p + q) y)
    (hcompx : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q x) = uniformBell p q * δ.dpow (p * q) x)
    (hcompy : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q y) = uniformBell p q * δ.dpow (p * q) y)
    {n : ℕ} (hn : n ≠ 0) (k c : ℕ) :
    δ.dpow c (δ.dpow k x * δ.dpow (n - k) y) =
      (compTermWeight n k c : A) * (δ.dpow (c * k) x * δ.dpow (c * (n - k)) y) := by
  unfold compTermWeight
  split_ifs with hk
  · subst hk
    simp only [Nat.sub_zero, mul_zero, δ.dpow_zero hx, one_mul, hcompy c hn]
  · have hpow : δ.dpow (n - k) y ^ c =
        Nat.multinomial (range c) (fun _ ↦ n - k) * δ.dpow (c * (n - k)) y := by
      have h := δ.prod_dpow (s := range c) (n := fun _ ↦ n - k) hy hmuly
      simpa only [prod_const, card_range, sum_const, smul_eq_mul] using h
    rw [mul_comm (δ.dpow k x), δ.dpow_mul (δ.dpow_mem hk hx), hpow, hcompx c hk, Nat.cast_mul]
    ring

private theorem dpow_comp_add_term {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmulx : ∀ p q, δ.dpow p x * δ.dpow q x = (p + q).choose p * δ.dpow (p + q) x)
    (hmuly : ∀ p q, δ.dpow p y * δ.dpow q y = (p + q).choose p * δ.dpow (p + q) y)
    (hcompx : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q x) = uniformBell p q * δ.dpow (p * q) x)
    (hcompy : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q y) = uniformBell p q * δ.dpow (p * q) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) {μ : Sym ℕ m} (hμ : μ ∈ (range (n + 1)).sym m) :
    (∏ k ∈ range (n + 1), δ.dpow (Multiset.count k μ) (δ.dpow k x * δ.dpow (n - k) y)) =
      (compSymWeight n μ : A) *
        (δ.dpow (compXDeg n μ) x * δ.dpow (m * n - compXDeg n μ) y) := by
  have hdeg := compXDeg_add_compYDeg hμ
  have hydeg : compYDeg n μ = m * n - compXDeg n μ := by omega
  calc ∏ k ∈ range (n + 1), δ.dpow (Multiset.count k μ) (δ.dpow k x * δ.dpow (n - k) y)
      = ∏ k ∈ range (n + 1),
          ((compTermWeight n k (Multiset.count k μ) : A) *
            (δ.dpow (Multiset.count k μ * k) x *
              δ.dpow (Multiset.count k μ * (n - k)) y)) :=
        prod_congr rfl fun k _ ↦ δ.dpow_comp_term hx hy hmuly hcompx hcompy hn k _
    _ = (∏ k ∈ range (n + 1), (compTermWeight n k (Multiset.count k μ) : A)) *
          ((∏ k ∈ range (n + 1), δ.dpow (Multiset.count k μ * k) x) *
            (∏ k ∈ range (n + 1), δ.dpow (Multiset.count k μ * (n - k)) y)) := by
        simp only [prod_mul_distrib]
    _ = (compSymWeight n μ : A) *
          (δ.dpow (compXDeg n μ) x * δ.dpow (m * n - compXDeg n μ) y) := by
        rw [δ.prod_dpow hx hmulx, δ.prod_dpow hy hmuly]
        unfold compSymWeight
        rw [← hydeg]
        unfold compXDeg compYDeg
        push_cast
        ring

private theorem dpow_comp_add_eq_sum {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmulx : ∀ p q, δ.dpow p x * δ.dpow q x = (p + q).choose p * δ.dpow (p + q) x)
    (hmuly : ∀ p q, δ.dpow p y * δ.dpow q y = (p + q).choose p * δ.dpow (p + q) y)
    (hcompx : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q x) = uniformBell p q * δ.dpow (p * q) x)
    (hcompy : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q y) = uniformBell p q * δ.dpow (p * q) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) =
      ∑ a ∈ range (m * n + 1),
        (compCoeff m n a : A) * (δ.dpow a x * δ.dpow (m * n - a) y) := by
  have hmem : ∀ k ∈ range (n + 1), δ.dpow k x * δ.dpow (n - k) y ∈ I := fun k _ ↦ by
    by_cases hk : k = 0
    · subst hk
      simpa [δ.dpow_zero hx] using δ.dpow_mem hn hy
    · exact I.mul_mem_right _ (δ.dpow_mem hk hx)
  rw [δ.dpow_add' hx hy, δ.dpow_sum hmem m,
    sum_congr rfl fun μ hμ ↦ δ.dpow_comp_add_term hx hy hmulx hmuly hcompx hcompy m hn hμ]
  have hmaps : ∀ μ ∈ (range (n + 1)).sym m, compXDeg n μ ∈ range (m * n + 1) := by
    intro μ hμ
    have hdeg := compXDeg_add_compYDeg hμ
    exact mem_range.mpr (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun a _ ↦ ?_
  unfold compCoeff
  rw [Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun μ hμ ↦ ?_
  rw [(mem_filter.mp hμ).2]

private theorem coeff_sum_ratDpow (d a : ℕ) (ha : a ≤ d) (c : ℕ → ℕ)
    (γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ))) :
    (∑ k ∈ range (d + 1),
      (c k : MvPolynomial (Fin 2) ℚ) *
        (γ.dpow k (MvPolynomial.X 0) * γ.dpow (d - k) (MvPolynomial.X 1))).coeff
      (Finsupp.single 0 a + Finsupp.single 1 (d - a)) =
    (c a : ℚ) * ((a ! : ℚ)⁻¹ * ((d - a)! : ℚ)⁻¹) := by
  have hmon : ∀ k : ℕ, γ.dpow k (MvPolynomial.X 0) * γ.dpow (d - k) (MvPolynomial.X 1) =
      MvPolynomial.monomial (Finsupp.single 0 k + Finsupp.single 1 (d - k))
        ((k ! : ℚ)⁻¹ * ((d - k)! : ℚ)⁻¹) := fun k ↦ by
    rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul ⊤ γ Submodule.mem_top,
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul ⊤ γ Submodule.mem_top,
      Ring.inverse_eq_inv']
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.smul_monomial, smul_eq_mul,
      mul_one, MvPolynomial.monomial_mul_monomial]
  rw [MvPolynomial.coeff_sum, sum_eq_single a]
  · rw [hmon, ← map_natCast MvPolynomial.C, MvPolynomial.C_mul_monomial,
      MvPolynomial.coeff_monomial, ite_eq_left rfl]
  · intro k _ hka
    rw [hmon, ← map_natCast MvPolynomial.C, MvPolynomial.C_mul_monomial,
      MvPolynomial.coeff_monomial, ite_eq_right]
    intro hdeg
    have h0 := DFunLike.congr_fun hdeg 0
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] at h0
    exact hka h0
  · intro ha'
    exact absurd (mem_range.mpr (Nat.lt_succ_of_le ha)) ha'

private theorem compCoeff_eq_uniformBell (m : ℕ) {n : ℕ} (hn : n ≠ 0) {a : ℕ}
    (ha : a ≤ m * n) :
    compCoeff m n a = uniformBell m n := by
  classical
  let γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
    DividedPowers.RatAlgebra.dividedPowers ⊤
  have h1 := γ.toAdditivePowers.dpow_comp_add_eq_sum
    (x := MvPolynomial.X 0) (y := MvPolynomial.X 1) Submodule.mem_top Submodule.mem_top
    (fun p q ↦ γ.mul_dpow Submodule.mem_top)
    (fun p q ↦ γ.mul_dpow Submodule.mem_top)
    (fun p {q} hq ↦ γ.dpow_comp hq Submodule.mem_top)
    (fun p {q} hq ↦ γ.dpow_comp hq Submodule.mem_top) m hn
  have h2 : γ.dpow m (γ.dpow n (MvPolynomial.X 0 + MvPolynomial.X 1)) =
      ∑ k ∈ range (m * n + 1),
        (uniformBell m n : MvPolynomial (Fin 2) ℚ) *
          (γ.dpow k (MvPolynomial.X 0) * γ.dpow (m * n - k) (MvPolynomial.X 1)) := by
    rw [γ.dpow_comp hn Submodule.mem_top, γ.dpow_add' Submodule.mem_top Submodule.mem_top,
      mul_sum]
  have heq : ∑ k ∈ range (m * n + 1),
        (compCoeff m n k : MvPolynomial (Fin 2) ℚ) *
          (γ.dpow k (MvPolynomial.X 0) * γ.dpow (m * n - k) (MvPolynomial.X 1)) =
      ∑ k ∈ range (m * n + 1),
        (uniformBell m n : MvPolynomial (Fin 2) ℚ) *
          (γ.dpow k (MvPolynomial.X 0) * γ.dpow (m * n - k) (MvPolynomial.X 1)) := by
    simpa only [toAdditivePowers_dpow] using h1.symm.trans h2
  have hq : (compCoeff m n a : ℚ) * ((a ! : ℚ)⁻¹ * ((m * n - a)! : ℚ)⁻¹) =
      (uniformBell m n : ℚ) * ((a ! : ℚ)⁻¹ * ((m * n - a)! : ℚ)⁻¹) := by
    rw [← coeff_sum_ratDpow (m * n) a ha (compCoeff m n) γ,
      ← coeff_sum_ratDpow (m * n) a ha (fun _ ↦ uniformBell m n) γ, heq]
  have hne : ((a ! : ℚ)⁻¹ * ((m * n - a)! : ℚ)⁻¹) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)))
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m * n - a))))
  exact Nat.cast_injective (R := ℚ) (mul_right_cancel₀ hne hq)

/-- The iteration identity is stable under sums when the multiplication identity holds at the two
summands. -/
theorem dpow_comp_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmulx : ∀ p q, δ.dpow p x * δ.dpow q x = (p + q).choose p * δ.dpow (p + q) x)
    (hmuly : ∀ p q, δ.dpow p y * δ.dpow q y = (p + q).choose p * δ.dpow (p + q) y)
    (hcompx : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q x) = uniformBell p q * δ.dpow (p * q) x)
    (hcompy : ∀ p {q}, q ≠ 0 → δ.dpow p (δ.dpow q y) = uniformBell p q * δ.dpow (p * q) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) = uniformBell m n * δ.dpow (m * n) (x + y) := by
  rw [δ.dpow_comp_add_eq_sum hx hy hmulx hmuly hcompx hcompy m hn, δ.dpow_add' hx hy, mul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [compCoeff_eq_uniformBell m hn (Nat.lt_succ_iff.mp (mem_range.mp ha))]

/-! ### Construction of `DividedPowers` from identities on generators -/

private theorem mul_dpow_zero (m n : ℕ) :
    δ.dpow m 0 * δ.dpow n 0 = (m + n).choose m * δ.dpow (m + n) 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [δ.dpow_zero I.zero_mem]
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [δ.dpow_zero I.zero_mem]
    · rw [δ.dpow_eval_zero hm, zero_mul, δ.dpow_eval_zero (by omega), mul_zero]

private theorem dpow_comp_zero (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n 0) = uniformBell m n * δ.dpow (m * n) 0 := by
  rw [δ.dpow_eval_zero hn]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [δ.dpow_zero I.zero_mem, uniformBell_zero_left]
  · rw [δ.dpow_eval_zero hm, δ.dpow_eval_zero (mul_ne_zero hm hn), mul_zero]

private theorem mul_dpow_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    {x : A} (hx : x ∈ I) :
    ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x := by
  rw [hS] at hx
  refine Submodule.span_induction (fun s hs ↦ hmul s hs) (δ.mul_dpow_zero)
    (fun a b ha hb iha ihb ↦ δ.mul_dpow_add (hS ▸ ha) (hS ▸ hb) iha ihb)
    (fun r a ha iha ↦ by simpa only [smul_eq_mul] using δ.mul_dpow_mul (hS ▸ ha) iha) hx

private theorem dpow_comp_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    {x : A} (hx : x ∈ I) :
    ∀ m {n}, n ≠ 0 → δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x := by
  have hmulI := fun {z} (hz : z ∈ I) ↦ δ.mul_dpow_of_span hS hmul hz
  rw [hS] at hx
  refine Submodule.span_induction (fun s hs ↦ hcomp s hs) (fun m {n} hn ↦ δ.dpow_comp_zero m hn)
    (fun a b ha hb iha ihb m {n} hn ↦
      δ.dpow_comp_add (hS ▸ ha) (hS ▸ hb) (hmulI (hS ▸ ha)) (hmulI (hS ▸ hb)) iha ihb m hn)
    (fun r a ha iha m {n} hn ↦ by
      simpa only [smul_eq_mul] using δ.dpow_comp_mul (hS ▸ ha) iha m hn) hx

/-- **Divided powers from identities on generators** (Stacks 23.2.4, tag 07GP): if an additive
divided-power candidate `δ` on `I = Ideal.span S` satisfies the multiplication and positive-degree
iteration identities at every generator `s ∈ S`, then `δ` is a `DividedPowers I` structure with the
exact same operations. -/
def toDividedPowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s) :
    DividedPowers I where
  dpow := δ.dpow
  dpow_null := δ.dpow_null
  dpow_zero := δ.dpow_zero
  dpow_one := δ.dpow_one
  dpow_mem := δ.dpow_mem
  dpow_add := δ.dpow_add
  dpow_mul := δ.dpow_mul
  mul_dpow hx := δ.mul_dpow_of_span hS hmul hx _ _
  dpow_comp hn hx := δ.dpow_comp_of_span hS hmul hcomp hx _ hn

/-- `AdditivePowers.toDividedPowers` preserves the underlying operations everywhere on `A`. -/
@[simp]
theorem toDividedPowers_dpow {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    (n : ℕ) (x : A) :
    (δ.toDividedPowers hS hmul hcomp).dpow n x = δ.dpow n x := (rfl)

/-- Forgetting back to `AdditivePowers` recovers `δ`. -/
@[simp]
theorem toDividedPowers_toAdditivePowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s) :
    (δ.toDividedPowers hS hmul hcomp).toAdditivePowers = δ := by
  ext n x _
  rfl

/-- Any `DividedPowers I` whose operations agree with `δ` on `I` equals `δ.toDividedPowers`. -/
theorem toDividedPowers_unique {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    (hI : DividedPowers I) (h : ∀ n {x}, x ∈ I → hI.dpow n x = δ.dpow n x) :
    hI = δ.toDividedPowers hS hmul hcomp := by
  ext n x hx
  exact h n hx

/-- `AdditivePowers.toDividedPowers` is independent of the choice of generating set. -/
theorem toDividedPowers_congr {S S' : Set A} (hS : I = Ideal.span S) (hS' : I = Ideal.span S')
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    (hmul' : ∀ s ∈ S', ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp' : ∀ s ∈ S', ∀ m {n}, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s) :
    δ.toDividedPowers hS hmul hcomp = δ.toDividedPowers hS' hmul' hcomp' := by
  ext n x _
  rfl

end AdditivePowers

end CommSemiring

end DividedPowers
