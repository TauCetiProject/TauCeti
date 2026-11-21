/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import TauCeti.Algebra.BigOperators.NatAntidiagonal
import TauCeti.Data.Finsupp.Single
import TauCeti.Data.Nat.Choose.Sum

/-!
# Divided powers from identities on generators

Let `A` be a commutative semiring and `I` an ideal of `A`. To construct a `DividedPowers`
structure on `I`, it suffices to construct a family of maps `δ : ℕ → A → A` vanishing outside `I`
and satisfying the additive, homogeneous, degree-zero, degree-one, and ideal-membership axioms
(`TauCeti.AdditivePowers I`), and then check the multiplication identity
`δ m s * δ n s = (m + n).choose m * δ (m + n) s` and the positive-inner-index iteration identity
`δ m (δ n s) = Nat.uniformBell m n * δ (m * n) s` only on a generating set `S` of `I`.

Both missing identities are shown to be stable under scalar multiplication and finite sums.
Stability of the multiplication identity reduces to Vandermonde's identity (`Nat.add_choose_eq`).
Stability of the iteration identity is proved over an arbitrary commutative semiring by factoring
the expanded left-hand side into universal natural-number coefficients independent of the ring and
determining those coefficients via `DividedPowers.RatAlgebra.dividedPowers` on `ℚ[X, Y]`.

## Main definitions

* `TauCeti.AdditivePowers`: an additive divided-power candidate on an ideal `I`, recording all
  axioms of `DividedPowers I` except `mul_dpow` and `dpow_comp`.
* `DividedPowers.toAdditivePowers`: the forgetful map `DividedPowers I → TauCeti.AdditivePowers I`.
* `TauCeti.AdditivePowers.toDividedPowers`: promotes an `AdditivePowers I` satisfying the
  multiplication and iteration identities on a generating set `S` of `I` to `DividedPowers I`.

## Main results

* `TauCeti.AdditivePowers.mul_dpow_add`: stability of the multiplication identity under sums.
* `TauCeti.AdditivePowers.dpow_comp_add`: stability of the iteration identity under sums.
* `TauCeti.AdditivePowers.toDividedPowers_toAdditivePowers` and
  `DividedPowers.toAdditivePowers_toDividedPowers`: round-trip identities between `AdditivePowers`
  and `DividedPowers`.

## References

* [Stacks: Divided Power Algebra, Lemma 07GP](https://stacks.math.columbia.edu/tag/07GP).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*,
  Lecture Notes in Math. 407, Springer (1974), I §1.
* N. Roby, *Les algèbres à puissances dividées*, Bull. Sci. Math. (2) 89 (1965), 75–91.
* Mathlib's `DividedPowers`, from the formalization of A. Chambert-Loir and
  M. I. de Frutos-Fernández.
-/

public section

open Finset

namespace TauCeti

/-- An additive divided-power candidate on an ideal `I` of a commutative semiring `A`: a family of
total operations `dpow : ℕ → A → A`, zero outside `I`, satisfying the degree-zero, degree-one,
ideal-membership, addition, and scalar-homogeneity axioms of `DividedPowers I`, without assuming
the multiplication (`mul_dpow`) or iteration (`dpow_comp`) identities. -/
structure AdditivePowers {A : Type*} [CommSemiring A] (I : Ideal A) where
  /-- The underlying divided-power candidate operations. -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x}, x ∉ I → dpow n x = 0
  dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1
  dpow_one : ∀ {x}, x ∈ I → dpow 1 x = x
  dpow_mem : ∀ {n x}, n ≠ 0 → x ∈ I → dpow n x ∈ I
  dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
    dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ {n a x}, x ∈ I → dpow n (a * x) = a ^ n * dpow n x

end TauCeti

namespace DividedPowers

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- Every `DividedPowers` structure yields an `AdditivePowers` candidate with the same
operations. -/
def toAdditivePowers (hI : DividedPowers I) : TauCeti.AdditivePowers I where
  dpow := hI.dpow
  dpow_null := hI.dpow_null
  dpow_zero := hI.dpow_zero
  dpow_one := hI.dpow_one
  dpow_mem := hI.dpow_mem
  dpow_add := hI.dpow_add
  dpow_mul := hI.dpow_mul

/-- The operations of `hI.toAdditivePowers` coincide with `hI.dpow` everywhere, including outside
`I`. -/
@[simp]
theorem toAdditivePowers_dpow (hI : DividedPowers I) (n : ℕ) (x : A) :
    hI.toAdditivePowers.dpow n x = hI.dpow n x := (rfl)

end DividedPowers

namespace TauCeti.AdditivePowers

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- Coercion from an additive divided-power candidate to its underlying function `ℕ → A → A`. -/
instance : CoeFun (AdditivePowers I) fun _ ↦ ℕ → A → A := ⟨fun δ ↦ δ.dpow⟩

/-- Two additive divided-power candidates on `I` are equal if they agree on every element of `I`. -/
@[ext]
theorem ext {δ δ' : AdditivePowers I}
    (h : ∀ n, ∀ x ∈ I, δ.dpow n x = δ'.dpow n x) : δ = δ' := by
  rcases δ with ⟨d, hnull, _, _, _, _, _⟩
  rcases δ' with ⟨d', hnull', _, _, _, _, _⟩
  simp only [mk.injEq]
  funext n x
  by_cases hx : x ∈ I
  · exact h n x hx
  · rw [hnull hx, hnull' hx]

/-- The coercion `AdditivePowers I → (ℕ → A → A)` is injective. -/
theorem coe_injective : Function.Injective (fun δ : AdditivePowers I ↦ (δ : ℕ → A → A)) :=
  fun _ _ h ↦ ext fun n x _ ↦ congrFun (congrFun h n) x

variable (δ : AdditivePowers I)

/-- An additive candidate vanishes at `0` in every positive degree. -/
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : δ.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), δ.dpow_mul I.zero_mem, zero_pow hn, zero_mul, zero_mul]

/-- Right-multiplication form of `dpow_mul`. -/
theorem dpow_mul_right {n : ℕ} {x : A} (hx : x ∈ I) (a : A) :
    δ.dpow n (x * a) = δ.dpow n x * a ^ n := by
  rw [mul_comm, δ.dpow_mul hx, mul_comm]

/-- Range-indexed form of `dpow_add`. -/
theorem dpow_add' {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    δ.dpow n (x + y) = ∑ k ∈ range (n + 1), δ.dpow k x * δ.dpow (n - k) y := by
  rw [δ.dpow_add hx hy, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Multinomial expansion of an additive candidate on a finite sum of elements of `I`. -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) {n : ℕ} :
    δ.dpow n (∑ i ∈ s, x i) =
      ∑ k ∈ s.sym n, ∏ i ∈ s, δ.dpow (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' δ.dpow δ.dpow_zero δ.dpow_add δ.dpow_eval_zero hx

/-- A finite product of candidate operations at an element satisfying the multiplication identity is
a multinomial coefficient times a single operation. -/
theorem prod_dpow {ι : Type*} {s : Finset ι} {f : ι → ℕ} {x : A} (hx : x ∈ I)
    (hx_mul : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x) :
    ∏ i ∈ s, δ.dpow (f i) x = (Nat.multinomial s f : A) * δ.dpow (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [δ.dpow_zero hx]
  | insert a s ha ih =>
    rw [prod_insert ha, ih, ← mul_assoc, mul_comm (δ.dpow (f a) x), mul_assoc, hx_mul,
      Nat.multinomial_insert ha, sum_insert ha]
    push_cast
    ring

/-- The multiplication identity is stable under left scalar multiplication. -/
theorem mul_dpow_mul {a x : A} (hx : x ∈ I) {m n : ℕ}
    (hx_mul : δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x) :
    δ.dpow m (a * x) * δ.dpow n (a * x) = ((m + n).choose m : A) * δ.dpow (m + n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul hx, δ.dpow_mul hx, pow_add]
  calc
    a ^ m * δ.dpow m x * (a ^ n * δ.dpow n x)
      = a ^ m * a ^ n * (δ.dpow m x * δ.dpow n x) := by ring
    _ = a ^ m * a ^ n * (((m + n).choose m : A) * δ.dpow (m + n) x) := by rw [hx_mul]
    _ = ((m + n).choose m : A) * (a ^ m * a ^ n * δ.dpow (m + n) x) := by ring

/-- The multiplication identity is stable under sums of elements of `I`. -/
theorem mul_dpow_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hx_mul : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x)
    (hy_mul : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (m n : ℕ) :
    δ.dpow m (x + y) * δ.dpow n (x + y) = ((m + n).choose m : A) * δ.dpow (m + n) (x + y) := by
  rw [δ.dpow_add hx hy, δ.dpow_add hx hy, δ.dpow_add hx hy, sum_mul_sum, mul_sum, ← sum_product']
  have hmaps : ∀ pq ∈ antidiagonal m ×ˢ antidiagonal n,
      (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) ∈ antidiagonal (m + n) := by
    intro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hpq
    simp only [mem_product, mem_antidiagonal] at hpq ⊢
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  have hab' : a + b = m + n := mem_antidiagonal.mp hab
  have hterm : ∀ pq ∈ (antidiagonal m ×ˢ antidiagonal n).filter
      (fun pq ↦ (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) = (a, b)),
      δ.dpow pq.1.1 x * δ.dpow pq.1.2 y * (δ.dpow pq.2.1 x * δ.dpow pq.2.2 y) =
        ((a.choose pq.1.1 * b.choose pq.1.2 : ℕ) : A) * (δ.dpow a x * δ.dpow b y) := by
    intro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hpq
    simp only [mem_filter, Prod.mk.injEq] at hpq
    obtain ⟨_, rfl, rfl⟩ := hpq
    calc
      δ.dpow i x * δ.dpow j y * (δ.dpow k x * δ.dpow l y)
        = (δ.dpow i x * δ.dpow k x) * (δ.dpow j y * δ.dpow l y) := by ring
      _ = (((i + k).choose i : A) * δ.dpow (i + k) x) *
            (((j + l).choose j : A) * δ.dpow (j + l) y) := by rw [hx_mul i k, hy_mul j l]
      _ = (((i + k).choose i * (j + l).choose j : ℕ) : A) *
            (δ.dpow (i + k) x * δ.dpow (j + l) y) := by push_cast; ring
  rw [sum_congr rfl hterm, ← sum_mul, ← Nat.cast_sum, sum_filter_antidiagonal_choose hab']

/-- The iteration identity is stable under left scalar multiplication. -/
theorem dpow_comp_mul {a x : A} (hx : x ∈ I) {m n : ℕ} (hn : n ≠ 0)
    (hx_comp : δ.dpow m (δ.dpow n x) = (Nat.uniformBell m n : A) * δ.dpow (m * n) x) :
    δ.dpow m (δ.dpow n (a * x)) = (Nat.uniformBell m n : A) * δ.dpow (m * n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul (δ.dpow_mem hn hx), δ.dpow_mul hx, hx_comp, ← pow_mul,
    mul_comm n m]
  ring

section IterationAdd

private def powDpowCoeff (c j : ℕ) : ℕ :=
  Nat.multinomial (univ : Finset (Fin c)) fun _ ↦ j

private def factorCoeff (c i j : ℕ) : ℕ :=
  if i = 0 then Nat.uniformBell c j else powDpowCoeff c j * Nat.uniformBell c i

private def degX {m : ℕ} (n : ℕ) (k : Sym (ℕ × ℕ) m) : ℕ :=
  ∑ p ∈ antidiagonal n, Multiset.count p k * p.1

private def degY {m : ℕ} (n : ℕ) (k : Sym (ℕ × ℕ) m) : ℕ :=
  ∑ p ∈ antidiagonal n, Multiset.count p k * p.2

private def termCoeff {m : ℕ} (n : ℕ) (k : Sym (ℕ × ℕ) m) : ℕ :=
  (∏ p ∈ antidiagonal n, factorCoeff (Multiset.count p k) p.1 p.2) *
    Nat.multinomial (antidiagonal n) (fun p ↦ Multiset.count p k * p.1) *
    Nat.multinomial (antidiagonal n) (fun p ↦ Multiset.count p k * p.2)

private def compSumCoeff (m n : ℕ) (r : ℕ × ℕ) : ℕ :=
  ∑ k ∈ ((antidiagonal n).sym m).filter (fun k ↦ (degX n k, degY n k) = r), termCoeff n k

private theorem pow_dpow {y : A} (hy : y ∈ I)
    (hy_mul : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (c j : ℕ) :
    δ.dpow j y ^ c = (powDpowCoeff c j : A) * δ.dpow (c * j) y := by
  have h := δ.prod_dpow (s := (univ : Finset (Fin c))) (f := fun _ ↦ j) hy hy_mul
  simpa [powDpowCoeff] using h

private theorem dpow_mul_dpow_pair {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hy_mul : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (hx_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n x) = (Nat.uniformBell m n : A) * δ.dpow (m * n) x)
    (hy_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n y) = (Nat.uniformBell m n : A) * δ.dpow (m * n) y)
    {c i j : ℕ} (hij : i + j ≠ 0) :
    δ.dpow c (δ.dpow i x * δ.dpow j y) =
      (factorCoeff c i j : A) * (δ.dpow (c * i) x * δ.dpow (c * j) y) := by
  by_cases hi : i = 0
  · subst hi
    have hj : j ≠ 0 := by omega
    simp [factorCoeff, δ.dpow_zero hx, hy_comp c j hj]
  · rw [mul_comm (δ.dpow i x), δ.dpow_mul (δ.dpow_mem hi hx),
      pow_dpow δ hy hy_mul c j, hx_comp c i hi]
    simp only [factorCoeff, hi, ↓reduceIte, Nat.cast_mul]
    ring

private theorem degX_add_degY {m n : ℕ} {k : Sym (ℕ × ℕ) m} (hk : k ∈ (antidiagonal n).sym m) :
    degX n k + degY n k = m * n :=
  Finset.Nat.sum_count_mul_fst_add_sum_count_mul_snd_antidiagonal hk

private theorem dpow_comp_add_eq_sum {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hx_mul : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x)
    (hy_mul : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (hx_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n x) = (Nat.uniformBell m n : A) * δ.dpow (m * n) x)
    (hy_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n y) = (Nat.uniformBell m n : A) * δ.dpow (m * n) y)
    {m n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) =
      ∑ r ∈ antidiagonal (m * n),
        (compSumCoeff m n r : A) * (δ.dpow r.1 x * δ.dpow r.2 y) := by
  have hmem : ∀ p ∈ antidiagonal n, δ.dpow p.1 x * δ.dpow p.2 y ∈ I := by
    intro ⟨i, j⟩ hp
    have hij : i + j = n := mem_antidiagonal.mp hp
    by_cases hi : i = 0
    · exact I.mul_mem_left _ (δ.dpow_mem (by omega) hy)
    · exact I.mul_mem_right _ (δ.dpow_mem hi hx)
  rw [δ.dpow_add hx hy, δ.dpow_sum hmem]
  have hmaps : ∀ k ∈ (antidiagonal n).sym m, (degX n k, degY n k) ∈ antidiagonal (m * n) :=
    fun k hk ↦ mem_antidiagonal.mpr (degX_add_degY hk)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun r _ ↦ ?_
  have hprod : ∀ k ∈ ((antidiagonal n).sym m).filter (fun k ↦ (degX n k, degY n k) = r),
      ∏ p ∈ antidiagonal n, δ.dpow (Multiset.count p k) (δ.dpow p.1 x * δ.dpow p.2 y) =
        (termCoeff n k : A) * (δ.dpow r.1 x * δ.dpow r.2 y) := by
    intro k hk
    have hdeg : (degX n k, degY n k) = r := (mem_filter.mp hk).2
    have hstep : ∏ p ∈ antidiagonal n,
        δ.dpow (Multiset.count p k) (δ.dpow p.1 x * δ.dpow p.2 y) =
        ∏ p ∈ antidiagonal n, (factorCoeff (Multiset.count p k) p.1 p.2 : A) *
          (δ.dpow (Multiset.count p k * p.1) x * δ.dpow (Multiset.count p k * p.2) y) :=
      prod_congr rfl fun p hp ↦
        dpow_mul_dpow_pair δ hx hy hy_mul hx_comp hy_comp (by rw [mem_antidiagonal.mp hp]; exact hn)
    rw [hstep, prod_mul_distrib, prod_mul_distrib,
      δ.prod_dpow hx hx_mul, δ.prod_dpow hy hy_mul, ← Nat.cast_prod]
    have hrx : ∑ p ∈ antidiagonal n, Multiset.count p k * p.1 = r.1 := congrArg Prod.fst hdeg
    have hry : ∑ p ∈ antidiagonal n, Multiset.count p k * p.2 = r.2 := congrArg Prod.snd hdeg
    rw [hrx, hry]
    simp only [termCoeff, Nat.cast_mul]
    ring
  rw [sum_congr rfl hprod, ← sum_mul, ← Nat.cast_sum, compSumCoeff]

private theorem coeff_ratDpow_X_mul_Y
    (γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ))) (a b c d : ℕ) :
    (γ.dpow a (MvPolynomial.X 0) * γ.dpow b (MvPolynomial.X 1)).coeff
        (Finsupp.single 0 c + Finsupp.single 1 d) =
      if (a, b) = (c, d) then (a.factorial : ℚ)⁻¹ * (b.factorial : ℚ)⁻¹ else 0 := by
  have hx0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ∈ (⊤ : Ideal _) := trivial
  have hx1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∈ (⊤ : Ideal _) := trivial
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ γ hx0,
    DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ γ hx1,
    Ring.inverse_eq_inv', MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, smul_mul_smul_comm, MvPolynomial.monomial_mul_monomial,
    mul_one, MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  simp only [Finsupp.single_add_single_eq_single_add_single_iff (by decide : (0 : Fin 2) ≠ 1),
    ← Prod.mk.injEq, mul_ite, mul_one, mul_zero]

private theorem compSumCoeff_eq_uniformBell {m n : ℕ} (hn : n ≠ 0) {r : ℕ × ℕ}
    (hr : r ∈ antidiagonal (m * n)) :
    compSumCoeff m n r = Nat.uniformBell m n := by
  let _ : DecidablePred fun x : MvPolynomial (Fin 2) ℚ ↦ x ∈ (⊤ : Ideal _) :=
    fun _ ↦ isTrue trivial
  let γ := DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ))
  have h1 := dpow_comp_add_eq_sum γ.toAdditivePowers
    (x := (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ))
    (y := (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)) trivial trivial
    (fun _ _ ↦ γ.mul_dpow trivial) (fun _ _ ↦ γ.mul_dpow trivial)
    (fun _ _ hk ↦ γ.dpow_comp hk trivial) (fun _ _ hk ↦ γ.dpow_comp hk trivial) (m := m) hn
  have h2 : γ.dpow m (γ.dpow n ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) + MvPolynomial.X 1)) =
      ∑ p ∈ antidiagonal (m * n), (Nat.uniformBell m n : MvPolynomial (Fin 2) ℚ) *
        (γ.dpow p.1 (MvPolynomial.X 0) * γ.dpow p.2 (MvPolynomial.X 1)) := by
    rw [γ.dpow_comp hn trivial, γ.dpow_add trivial trivial, mul_sum]
  have heq : ∑ p ∈ antidiagonal (m * n), (compSumCoeff m n p : MvPolynomial (Fin 2) ℚ) *
        (γ.dpow p.1 (MvPolynomial.X 0) * γ.dpow p.2 (MvPolynomial.X 1)) =
      ∑ p ∈ antidiagonal (m * n), (Nat.uniformBell m n : MvPolynomial (Fin 2) ℚ) *
        (γ.dpow p.1 (MvPolynomial.X 0) * γ.dpow p.2 (MvPolynomial.X 1)) :=
    h1.symm.trans h2
  have hcoeff := congrArg
    (MvPolynomial.coeffAddMonoidHom (Finsupp.single 0 r.1 + Finsupp.single 1 r.2)) heq
  simp only [map_sum, MvPolynomial.coeffAddMonoidHom_apply, ← MvPolynomial.C_eq_natCast,
    MvPolynomial.coeff_C_mul, coeff_ratDpow_X_mul_Y, mul_ite, mul_zero, Prod.mk.eta, sum_ite_eq',
    hr, ↓reduceIte] at hcoeff
  have hne : (r.1.factorial : ℚ)⁻¹ * (r.2.factorial : ℚ)⁻¹ ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
  exact Nat.cast_injective (R := ℚ) (mul_right_cancel₀ hne hcoeff)

/-- The iteration identity is stable under sums of elements of `I` at which the multiplication
identity holds. -/
theorem dpow_comp_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hx_mul : ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x)
    (hy_mul : ∀ m n, δ.dpow m y * δ.dpow n y = ((m + n).choose m : A) * δ.dpow (m + n) y)
    (hx_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n x) = (Nat.uniformBell m n : A) * δ.dpow (m * n) x)
    (hy_comp : ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n y) = (Nat.uniformBell m n : A) * δ.dpow (m * n) y)
    {m n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) = (Nat.uniformBell m n : A) * δ.dpow (m * n) (x + y) := by
  rw [dpow_comp_add_eq_sum δ hx hy hx_mul hy_mul hx_comp hy_comp hn, δ.dpow_add hx hy, mul_sum]
  exact sum_congr rfl fun r hr ↦ by rw [compSumCoeff_eq_uniformBell hn hr]

end IterationAdd

section Generators

private theorem mul_dpow_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    {x : A} (hx : x ∈ I) :
    ∀ m n, δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x := by
  rw [hS] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · exact fun s hs m n ↦ hmul m n s hs
  · intro m n
    by_cases hm : m = 0
    · subst hm; simp [δ.dpow_zero I.zero_mem]
    · rw [δ.dpow_eval_zero hm, zero_mul, δ.dpow_eval_zero (by omega), mul_zero]
  · intro x y hx' hy' ihx ihy m n
    exact δ.mul_dpow_add (hS ▸ hx') (hS ▸ hy') ihx ihy m n
  · intro a x hx' ihx m n
    exact δ.mul_dpow_mul (hS ▸ hx') (ihx m n)

private theorem dpow_comp_of_span {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ m n, n ≠ 0 → ∀ s ∈ S,
      δ.dpow m (δ.dpow n s) = (Nat.uniformBell m n : A) * δ.dpow (m * n) s)
    {x : A} (hx : x ∈ I) :
    ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n x) = (Nat.uniformBell m n : A) * δ.dpow (m * n) x := by
  have hall_mul : ∀ z ∈ I, ∀ m n,
      δ.dpow m z * δ.dpow n z = ((m + n).choose m : A) * δ.dpow (m + n) z :=
    fun _ hz ↦ mul_dpow_of_span δ hS hmul hz
  rw [hS] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · exact fun s hs m n hn ↦ hcomp m n hn s hs
  · intro m n hn
    rw [δ.dpow_eval_zero hn]
    by_cases hm : m = 0
    · subst hm; simp [δ.dpow_zero I.zero_mem, Nat.uniformBell_zero_left]
    · rw [δ.dpow_eval_zero hm, δ.dpow_eval_zero (mul_ne_zero hm hn), mul_zero]
  · intro x y hx' hy' ihx ihy m n hn
    exact δ.dpow_comp_add (hS ▸ hx') (hS ▸ hy') (hall_mul x (hS ▸ hx'))
      (hall_mul y (hS ▸ hy')) ihx ihy hn
  · intro a x hx' ihx m n hn
    exact δ.dpow_comp_mul (hS ▸ hx') hn (ihx m n hn)

/-- Promote an additive divided-power candidate on `I = Ideal.span S` to a `DividedPowers I`
structure by checking the multiplication and positive-inner-index iteration identities only on the
generating set `S` (Stacks Project Lemma 23.2.4, Tag 07GP). -/
def toDividedPowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ m n, n ≠ 0 → ∀ s ∈ S,
      δ.dpow m (δ.dpow n s) = (Nat.uniformBell m n : A) * δ.dpow (m * n) s) :
    DividedPowers I where
  dpow := δ.dpow
  dpow_null := δ.dpow_null
  dpow_zero := δ.dpow_zero
  dpow_one := δ.dpow_one
  dpow_mem := δ.dpow_mem
  dpow_add := δ.dpow_add
  dpow_mul := δ.dpow_mul
  mul_dpow hx := mul_dpow_of_span δ hS hmul hx _ _
  dpow_comp hn hx := dpow_comp_of_span δ hS hmul hcomp hx _ _ hn

/-- `toDividedPowers` preserves the underlying operations of `δ` everywhere. -/
@[simp]
theorem toDividedPowers_dpow {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ m n, n ≠ 0 → ∀ s ∈ S,
      δ.dpow m (δ.dpow n s) = (Nat.uniformBell m n : A) * δ.dpow (m * n) s)
    (n : ℕ) (x : A) :
    (δ.toDividedPowers hS hmul hcomp).dpow n x = δ.dpow n x := (rfl)

/-- Forgetting a promoted additive divided-power candidate recovers it. -/
@[simp]
theorem toDividedPowers_toAdditivePowers {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      δ.dpow m s * δ.dpow n s = ((m + n).choose m : A) * δ.dpow (m + n) s)
    (hcomp : ∀ m n, n ≠ 0 → ∀ s ∈ S,
      δ.dpow m (δ.dpow n s) = (Nat.uniformBell m n : A) * δ.dpow (m * n) s) :
    (δ.toDividedPowers hS hmul hcomp).toAdditivePowers = δ :=
  ext fun n x _ ↦ by rw [DividedPowers.toAdditivePowers_dpow, δ.toDividedPowers_dpow]

end Generators

end TauCeti.AdditivePowers

namespace DividedPowers

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- Promoting the additive candidate of an existing `DividedPowers` structure recovers it. -/
@[simp]
theorem toAdditivePowers_toDividedPowers (hI : DividedPowers I) {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ m n, ∀ s ∈ S,
      hI.toAdditivePowers.dpow m s * hI.toAdditivePowers.dpow n s =
        ((m + n).choose m : A) * hI.toAdditivePowers.dpow (m + n) s)
    (hcomp : ∀ m n, n ≠ 0 → ∀ s ∈ S,
      hI.toAdditivePowers.dpow m (hI.toAdditivePowers.dpow n s) =
        (Nat.uniformBell m n : A) * hI.toAdditivePowers.dpow (m * n) s) :
    hI.toAdditivePowers.toDividedPowers hS hmul hcomp = hI :=
  DividedPowers.ext _ _ fun _ _ _ ↦ rfl

end DividedPowers
