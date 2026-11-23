/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Divided powers from identities on generators

An *additive divided-power candidate* on an ideal `I` of a commutative semiring `A` is a family of
maps `δₙ : A → A`, vanishing outside `I` as for Mathlib's `DividedPowers`, that satisfies every
axiom of a divided power structure except two: the multiplication identity
`δₘ(x) δₙ(x) = (m + n).choose m * δₘ₊ₙ(x)` and the iteration identity
`δₘ(δₙ(x)) = uniformBell m n * δₘₙ(x)` for `n ≠ 0`. Both identities are stable under sums, so they
hold on all of `I` as soon as they hold on a generating set, and the candidate is then a divided
power structure. This is how divided powers are usually constructed: by gluing them on a sum of
ideals (`TauCeti.RingTheory.DividedPowers.Glue`), on divided power polynomial algebras and on
divided power envelopes, where only the generators are under control.

## Main definitions

* `TauCeti.PD.AdditivePowers I`: additive divided-power candidates on `I`.
* `TauCeti.PD.AdditivePowers.ofDividedPowers`: the candidate underlying a divided power structure.
* `TauCeti.PD.AdditivePowers.toDividedPowers`: the divided power structure on `I = span S` built
  from a candidate satisfying both identities at every `s ∈ S`.

## Main results

* `TauCeti.PD.AdditivePowers.mul_dpow_add`: the multiplication identity is stable under sums.
* `TauCeti.PD.AdditivePowers.dpow_comp_add`: the iteration identity is stable under sums.
* `TauCeti.PD.AdditivePowers.toDividedPowers_unique`: a divided power structure is determined by
  its candidate.

## Implementation notes

For the iteration identity at `x + y`, the expansion of `δₘ(δₙ(x + y))` by the axioms of a
candidate and the identities at `x` and `y` is `∑_{a + b = m n} c_{a,b} δₐ(x) δ_b(y)`, with natural
number coefficients `c_{a,b}` that do not depend on `A`. Carrying out the same expansion in `ℚ[X]`,
with the divided powers `f ↦ fⁿ / n!`, `x = X` and `y = 1`, and comparing the coefficients of
`Xᵃ` shows `c_{a,b} = uniformBell m n`.

## References

* [Stacks Project, Tag 07GP](https://stacks.math.columbia.edu/tag/07GP)
-/

public section

open Finset Nat

namespace TauCeti.PD

variable {A : Type*} [CommSemiring A] (I : Ideal A)

/-- An additive divided-power candidate on an ideal `I`: maps `δₙ : A → A`, zero outside `I`, with
`δ₀ = 1` and `δ₁ = id` on `I`, `δₙ(I) ⊆ I` for `n ≠ 0`, the addition law and homogeneity. Unlike a
divided power structure, it need not satisfy the multiplication and iteration identities. -/
structure AdditivePowers where
  /-- The operations `δₙ`, as total functions vanishing outside `I`. -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x}, x ∉ I → dpow n x = 0
  dpow_zero : ∀ {x}, x ∈ I → dpow 0 x = 1
  dpow_one : ∀ {x}, x ∈ I → dpow 1 x = x
  dpow_mem : ∀ {n x}, n ≠ 0 → x ∈ I → dpow n x ∈ I
  dpow_add : ∀ {n x y}, x ∈ I → y ∈ I →
    dpow n (x + y) = ∑ k ∈ antidiagonal n, dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ {n a x}, x ∈ I → dpow n (a * x) = a ^ n * dpow n x

namespace AdditivePowers

variable {I}

/-- Candidates with the same operations on `I` are equal. -/
@[ext]
theorem ext {δ δ' : AdditivePowers I} (h : ∀ n, ∀ x ∈ I, δ.dpow n x = δ'.dpow n x) :
    δ = δ' := by
  obtain ⟨f, hf, _, _, _, _, _⟩ := δ
  obtain ⟨f', hf', _, _, _, _, _⟩ := δ'
  congr
  funext n x
  by_cases hx : x ∈ I
  · exact h n x hx
  · rw [hf hx, hf' hx]

/-- The additive candidate underlying a divided power structure. -/
def ofDividedPowers (γ : DividedPowers I) : AdditivePowers I where
  dpow := γ.dpow
  dpow_null := γ.dpow_null
  dpow_zero := γ.dpow_zero
  dpow_one := γ.dpow_one
  dpow_mem := γ.dpow_mem
  dpow_add := γ.dpow_add
  dpow_mul := γ.dpow_mul

@[simp]
theorem ofDividedPowers_dpow (γ : DividedPowers I) (n : ℕ) (x : A) :
    (ofDividedPowers γ).dpow n x = γ.dpow n x :=
  (rfl)

variable (δ : AdditivePowers I)

/-- In positive degree a candidate vanishes at `0`. -/
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : δ.dpow n 0 = 0 := by
  have h := δ.dpow_mul (n := n) (a := 0) I.zero_mem
  rwa [zero_mul, zero_pow hn, zero_mul] at h

/-- `AdditivePowers.dpow_add` with a sum over `range (n + 1)`. -/
theorem dpow_add' {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    δ.dpow n (x + y) = ∑ k ∈ range (n + 1), δ.dpow k x * δ.dpow (n - k) y := by
  rw [δ.dpow_add hx hy, sum_antidiagonal_eq_sum_range_succ_mk]

/-- At an element where the multiplication identity holds, a product of operations is a multinomial
coefficient times one operation. -/
theorem prod_dpow {x : A} (hx : x ∈ I)
    (hmul : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    {ι : Type*} {s : Finset ι} {n : ι → ℕ} :
    ∏ i ∈ s, δ.dpow (n i) x = multinomial s n * δ.dpow (∑ i ∈ s, n i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [δ.dpow_zero hx]
  | insert a s ha ih =>
    rw [prod_insert ha, ih, mul_left_comm, hmul, sum_insert ha, multinomial_insert ha]
    push_cast
    ring

/-- At an element where the multiplication identity holds, `δⱼ(x) ^ c` is a multinomial coefficient
times `δ_{c j}(x)`. -/
theorem pow_dpow {x : A} (hx : x ∈ I)
    (hmul : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x) (c j : ℕ) :
    δ.dpow j x ^ c = multinomial (range c) (fun _ ↦ j) * δ.dpow (c * j) x := by
  have h := δ.prod_dpow hx hmul (s := range c) (n := fun _ ↦ j)
  rwa [prod_const, card_range, sum_const, card_range, smul_eq_mul] at h

/-- Vandermonde's identity, summed over the pairs of decompositions of `m` and `n` adding up to a
fixed decomposition `r` of `m + n`. -/
private theorem sum_choose_mul_choose_filter {m n : ℕ} {r : ℕ × ℕ} (hr : r ∈ antidiagonal (m + n)) :
    ∑ pq ∈ antidiagonal m ×ˢ antidiagonal n with pq.1 + pq.2 = r,
      (pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 = (m + n).choose m := by
  rw [mem_antidiagonal] at hr
  rw [← hr, Nat.add_choose_eq]
  refine sum_bij_ne_zero (fun pq _ _ ↦ pq.1) ?_ ?_ ?_ ?_
  · intro pq hpq _
    simp only [mem_filter, mem_product] at hpq
    exact hpq.1.1
  · intro pq hpq _ pq' hpq' _ h
    simp only [mem_filter, mem_product, mem_antidiagonal, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add] at hpq hpq' h ⊢
    omega
  · intro p hp hne
    have h1 : p.1 ≤ r.1 := by
      by_contra h
      exact hne (by rw [choose_eq_zero_of_lt (n := r.1) (by omega), zero_mul])
    have h2 : p.2 ≤ r.2 := by
      by_contra h
      exact hne (by rw [choose_eq_zero_of_lt (n := r.2) (by omega), mul_zero])
    rw [mem_antidiagonal] at hp
    refine ⟨(p, (r.1 - p.1, r.2 - p.2)), ?_, ?_, rfl⟩
    · simp only [mem_filter, mem_product, mem_antidiagonal, Prod.ext_iff, Prod.fst_add,
        Prod.snd_add]
      omega
    · dsimp only
      rwa [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2]
  · intro pq hpq _
    simp only [mem_filter] at hpq
    rw [← hpq.2, Prod.fst_add, Prod.snd_add]

/-- The multiplication identity `δₘ(z) δₙ(z) = (m + n).choose m * δₘ₊ₙ(z)` for all `m, n`, if it
holds at `x` and at `y`, also holds at `x + y`. -/
theorem mul_dpow_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    (hmy : ∀ m n, δ.dpow m y * δ.dpow n y = (m + n).choose m * δ.dpow (m + n) y) (m n : ℕ) :
    δ.dpow m (x + y) * δ.dpow n (x + y) = (m + n).choose m * δ.dpow (m + n) (x + y) := by
  let F : ℕ × ℕ → A := fun r ↦ δ.dpow r.1 x * δ.dpow r.2 y
  have hL : δ.dpow m (x + y) * δ.dpow n (x + y) =
      ∑ pq ∈ antidiagonal m ×ˢ antidiagonal n,
        (((pq.1.1 + pq.2.1).choose pq.1.1 * (pq.1.2 + pq.2.2).choose pq.1.2 : ℕ) : A) *
          F (pq.1 + pq.2) := by
    rw [δ.dpow_add hx hy, δ.dpow_add hx hy, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun pq _ ↦ ?_
    calc _ = (δ.dpow pq.1.1 x * δ.dpow pq.2.1 x) * (δ.dpow pq.1.2 y * δ.dpow pq.2.2 y) := by
          ring
      _ = _ := by simp only [F, hmx, hmy, Prod.fst_add, Prod.snd_add]; push_cast; ring
  have hmaps : ∀ pq ∈ antidiagonal m ×ˢ antidiagonal n, pq.1 + pq.2 ∈ antidiagonal (m + n) := by
    intro pq hpq
    simp only [mem_product, mem_antidiagonal, Prod.fst_add, Prod.snd_add] at hpq ⊢
    omega
  rw [hL, ← sum_fiberwise_of_maps_to hmaps, δ.dpow_add hx hy, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [← sum_choose_mul_choose_filter hr, Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun pq hpq ↦ ?_
  rw [(mem_filter.mp hpq).2]

/-! ### The iteration identity at a sum -/

/-- The coefficient of `δ_{c i}(x) δ_{c (n - i)}(y)` in `δ_c(δ_i(x) δ_{n - i}(y))`. -/
private def termCoeff (n c i : ℕ) : ℕ :=
  if i = 0 then uniformBell c n else uniformBell c i * multinomial (range c) (fun _ ↦ n - i)

/-- The `x`-weight and the `y`-weight of a multiset of indices `i ≤ n`, each `i` standing for the
term `δ_i(x) δ_{n - i}(y)` of `δ_n(x + y)`. -/
private def symWeight (n : ℕ) {m : ℕ} (k : Sym ℕ m) : ℕ × ℕ :=
  (∑ i ∈ range (n + 1), Multiset.count i k * i, ∑ i ∈ range (n + 1), Multiset.count i k * (n - i))

/-- The coefficient contributed by a multiset of indices to `δ_m(δ_n(x + y))`. -/
private def symCoeff (n : ℕ) {m : ℕ} (k : Sym ℕ m) : ℕ :=
  (∏ i ∈ range (n + 1), termCoeff n (Multiset.count i k) i) *
    (multinomial (range (n + 1)) (fun i ↦ Multiset.count i k * i) *
      multinomial (range (n + 1)) (fun i ↦ Multiset.count i k * (n - i)))

/-- The coefficient of `δ_a(x) δ_b(y)` in `δ_m(δ_n(x + y))`, for `(a, b) = p`. -/
private def compCoeff (m n : ℕ) (p : ℕ × ℕ) : ℕ :=
  ∑ k ∈ (range (n + 1)).sym m with symWeight n k = p, symCoeff n k

private theorem symWeight_mem {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (range (n + 1)).sym m) :
    symWeight n k ∈ antidiagonal (m * n) := by
  rw [mem_antidiagonal, symWeight, ← sum_add_distrib]
  calc _ = ∑ i ∈ range (n + 1), Multiset.count i k * n := by
        refine sum_congr rfl fun i hi ↦ ?_
        rw [← mul_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]
    _ = m * n := by
        rw [← sum_mul, Multiset.sum_count_eq_card (m := (k : Multiset ℕ)) (mem_sym_iff.mp hk),
          Sym.card_coe]

variable {δ} in
private theorem dpow_dpow_mul_dpow {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmy : ∀ m n, δ.dpow m y * δ.dpow n y = (m + n).choose m * δ.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n y) = uniformBell m n * δ.dpow (m * n) y)
    {n i : ℕ} (hn : n ≠ 0) (c : ℕ) :
    δ.dpow c (δ.dpow i x * δ.dpow (n - i) y) =
      termCoeff n c i * (δ.dpow (c * i) x * δ.dpow (c * (n - i)) y) := by
  by_cases hi : i = 0
  · subst hi
    simp [termCoeff, δ.dpow_zero hx, hcy c n hn]
  · rw [mul_comm (δ.dpow i x), δ.dpow_mul (δ.dpow_mem hi hx), hcx c i hi, δ.pow_dpow hy hmy,
      termCoeff, ite_eq_right hi]
    push_cast
    ring

variable {δ} in
private theorem dpow_dpow_add_eq_sum {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    (hmy : ∀ m n, δ.dpow m y * δ.dpow n y = (m + n).choose m * δ.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n y) = uniformBell m n * δ.dpow (m * n) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) =
      ∑ p ∈ antidiagonal (m * n), (compCoeff m n p : A) * (δ.dpow p.1 x * δ.dpow p.2 y) := by
  have hmem : ∀ i ∈ range (n + 1), δ.dpow i x * δ.dpow (n - i) y ∈ I := by
    intro i _
    by_cases hi : i = 0
    · subst hi
      rw [δ.dpow_zero hx, one_mul, Nat.sub_zero]
      exact δ.dpow_mem hn hy
    · exact I.mul_mem_right _ (δ.dpow_mem hi hx)
  rw [δ.dpow_add' hx hy, DividedPowers.dpow_sum' (I := I.toAddSubmonoid) δ.dpow δ.dpow_zero
    δ.dpow_add δ.dpow_eval_zero hmem]
  have hterm : ∀ k ∈ (range (n + 1)).sym m,
      ∏ i ∈ range (n + 1), δ.dpow (Multiset.count i k) (δ.dpow i x * δ.dpow (n - i) y) =
        (symCoeff n k : A) * (δ.dpow (symWeight n k).1 x * δ.dpow (symWeight n k).2 y) := by
    intro k _
    rw [prod_congr rfl fun i _ ↦ dpow_dpow_mul_dpow hx hy hmy hcx hcy hn _, prod_mul_distrib,
      prod_mul_distrib, δ.prod_dpow hx hmx, δ.prod_dpow hy hmy, symCoeff, symWeight]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← sum_fiberwise_of_maps_to fun k hk ↦ symWeight_mem hk]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [compCoeff, Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [(mem_filter.mp hk).2]

section Rational

open Polynomial

/-- The divided powers `f ↦ fⁿ / n!` on the unit ideal of `ℚ[X]`. -/
private noncomputable abbrev ratDP : DividedPowers (⊤ : Ideal ℚ[X]) :=
  open scoped Classical in DividedPowers.RatAlgebra.dividedPowers ⊤

private theorem ratDP_dpow (k : ℕ) (f : ℚ[X]) : ratDP.dpow k f = C (k ! : ℚ)⁻¹ * f ^ k := by
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul (I := ⊤) ratDP (x := f) Submodule.mem_top,
    Ring.inverse_eq_inv',
    smul_eq_C_mul]

private theorem coeff_sum_ratDP {N : ℕ} (e : ℕ × ℕ → ℕ) {p : ℕ × ℕ} (hp : p ∈ antidiagonal N) :
    (∑ q ∈ antidiagonal N, (e q : ℚ[X]) * (ratDP.dpow q.1 X * ratDP.dpow q.2 1)).coeff p.1 =
      e p * ((p.1 ! : ℚ)⁻¹ * (p.2 ! : ℚ)⁻¹) := by
  have hterm : ∀ q : ℕ × ℕ, (e q : ℚ[X]) * (ratDP.dpow q.1 X * ratDP.dpow q.2 1) =
      C (e q * ((q.1 ! : ℚ)⁻¹ * (q.2 ! : ℚ)⁻¹)) * X ^ q.1 := by
    intro q
    simp only [ratDP_dpow, one_pow, mul_one, C_mul, ← Polynomial.C_eq_natCast]
    ring
  simp only [hterm, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_eq_single p (fun q hq hqp ↦ ite_eq_right ?_) (fun h ↦ absurd hp h), ite_eq_left rfl]
  rw [mem_antidiagonal] at hp hq
  exact fun h ↦ hqp (Prod.ext h.symm (by omega))

/-- Two natural-number coefficient families agree on `antidiagonal N` once they give the same
combination of the rational divided powers `Xᵃ / a! * 1 / b!`. -/
private theorem eq_of_sum_ratDP_eq {N : ℕ} {c d : ℕ × ℕ → ℕ}
    (h : ∑ q ∈ antidiagonal N, (c q : ℚ[X]) * (ratDP.dpow q.1 X * ratDP.dpow q.2 1) =
      ∑ q ∈ antidiagonal N, (d q : ℚ[X]) * (ratDP.dpow q.1 X * ratDP.dpow q.2 1))
    {p : ℕ × ℕ} (hp : p ∈ antidiagonal N) : c p = d p := by
  have h' := congrArg (fun f : ℚ[X] ↦ f.coeff p.1) h
  simp only [coeff_sum_ratDP _ hp] at h'
  exact_mod_cast mul_right_cancel₀ (by simp [factorial_ne_zero]) h'

private theorem compCoeff_eq_uniformBell (m : ℕ) {n : ℕ} (hn : n ≠ 0) {p : ℕ × ℕ}
    (hp : p ∈ antidiagonal (m * n)) : compCoeff m n p = uniformBell m n := by
  refine eq_of_sum_ratDP_eq (c := compCoeff m n) (d := fun _ ↦ uniformBell m n) ?_ hp
  have h := dpow_dpow_add_eq_sum (δ := ofDividedPowers ratDP) (x := X) (y := 1) Submodule.mem_top
    Submodule.mem_top (fun _ _ ↦ ratDP.mul_dpow Submodule.mem_top)
    (fun _ _ ↦ ratDP.mul_dpow Submodule.mem_top)
    (fun _ _ hn ↦ ratDP.dpow_comp hn Submodule.mem_top)
    (fun _ _ hn ↦ ratDP.dpow_comp hn Submodule.mem_top) m hn
  simp only [ofDividedPowers_dpow] at h
  rw [← h, ratDP.dpow_comp hn (Submodule.mem_top (x := X + 1)),
    ratDP.dpow_add Submodule.mem_top Submodule.mem_top, mul_sum]

end Rational

/-- The iteration identity `δₘ(δₙ(z)) = uniformBell m n * δₘₙ(z)` for all `m` and all `n ≠ 0`,
if it holds at `x` and at `y` together with the multiplication identity, also holds at `x + y`. -/
theorem dpow_comp_add {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hmx : ∀ m n, δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x)
    (hmy : ∀ m n, δ.dpow m y * δ.dpow n y = (m + n).choose m * δ.dpow (m + n) y)
    (hcx : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x)
    (hcy : ∀ m n, n ≠ 0 → δ.dpow m (δ.dpow n y) = uniformBell m n * δ.dpow (m * n) y)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n (x + y)) = uniformBell m n * δ.dpow (m * n) (x + y) := by
  rw [dpow_dpow_add_eq_sum hx hy hmx hmy hcx hcy m hn, δ.dpow_add hx hy, mul_sum]
  exact sum_congr rfl fun p hp ↦ by rw [compCoeff_eq_uniformBell m hn hp]

/-! ### Divided powers from identities on generators -/

section Generators

variable {S : Set A} (hS : I = Ideal.span S)
include hS

private theorem mul_dpow_of_span
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    {x : A} (hx : x ∈ I) (m n : ℕ) :
    δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x := by
  have hI : ∀ {z}, z ∈ Ideal.span S → z ∈ I := fun hz ↦ hS ▸ hz
  rw [hS] at hx
  induction hx using Submodule.span_induction generalizing m n with
  | mem s hs => exact hmul s hs m n
  | zero =>
    by_cases hm : m = 0
    · simp [hm, δ.dpow_zero I.zero_mem]
    · rw [δ.dpow_eval_zero hm, δ.dpow_eval_zero (n := m + n) (by omega), zero_mul, mul_zero]
  | add x y hx hy ihx ihy => exact δ.mul_dpow_add (hI hx) (hI hy) ihx ihy m n
  | smul a x hx ih =>
    rw [smul_eq_mul, δ.dpow_mul (hI hx), δ.dpow_mul (hI hx), δ.dpow_mul (hI hx), pow_add,
      mul_mul_mul_comm, ih m n]
    ring

private theorem dpow_comp_of_span
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    {x : A} (hx : x ∈ I) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n x) = uniformBell m n * δ.dpow (m * n) x := by
  have hI : ∀ {z}, z ∈ Ideal.span S → z ∈ I := fun hz ↦ hS ▸ hz
  have hmul' : ∀ z ∈ I, ∀ m n, δ.dpow m z * δ.dpow n z = (m + n).choose m * δ.dpow (m + n) z :=
    fun z hz ↦ δ.mul_dpow_of_span hS hmul hz
  rw [hS] at hx
  induction hx using Submodule.span_induction generalizing m n with
  | mem s hs => exact hcomp s hs m n hn
  | zero =>
    rw [δ.dpow_eval_zero hn]
    by_cases hm : m = 0
    · simp [hm, δ.dpow_zero I.zero_mem, uniformBell_zero_left]
    · rw [δ.dpow_eval_zero hm, δ.dpow_eval_zero (Nat.mul_ne_zero hm hn), mul_zero]
  | add x y hx hy ihx ihy =>
    exact δ.dpow_comp_add (hI hx) (hI hy) (hmul' x (hI hx)) (hmul' y (hI hy))
      (fun m n hn ↦ ihx m hn) (fun m n hn ↦ ihy m hn) m hn
  | smul a x hx ih =>
    rw [smul_eq_mul, δ.dpow_mul (hI hx), δ.dpow_mul (δ.dpow_mem hn (hI hx)), ih m hn,
      δ.dpow_mul (hI hx), ← pow_mul, mul_comm n m]
    ring

/-- The divided power structure on `I = span S` with the operations of an additive candidate `δ`
satisfying the multiplication and iteration identities at every generator `s ∈ S`.

[Stacks Project, Tag 07GP](https://stacks.math.columbia.edu/tag/07GP) -/
def toDividedPowers
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
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

variable (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
  (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
    δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)

@[simp]
theorem toDividedPowers_dpow (n : ℕ) (x : A) :
    (δ.toDividedPowers hS hmul hcomp).dpow n x = δ.dpow n x :=
  (rfl)

@[simp]
theorem ofDividedPowers_toDividedPowers :
    ofDividedPowers (δ.toDividedPowers hS hmul hcomp) = δ :=
  ext fun _ _ _ ↦ by simp

/-- A divided power structure whose operations are those of `δ` is the structure built from `δ`
and any generating set. -/
theorem toDividedPowers_unique {γ : DividedPowers I} (h : ofDividedPowers γ = δ) :
    γ = δ.toDividedPowers hS hmul hcomp := by
  subst h
  exact DividedPowers.ext _ _ fun _ _ ↦ by simp

omit hS in
/-- The structure built from `δ` does not depend on the generating set. -/
theorem toDividedPowers_generators {S' : Set A} (hS : I = Ideal.span S) (hS' : I = Ideal.span S')
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s)
    (hmul' : ∀ s ∈ S', ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    (hcomp' : ∀ s ∈ S', ∀ m n, n ≠ 0 →
      δ.dpow m (δ.dpow n s) = uniformBell m n * δ.dpow (m * n) s) :
    δ.toDividedPowers hS hmul hcomp = δ.toDividedPowers hS' hmul' hcomp' :=
  DividedPowers.ext _ _ fun _ _ ↦ by simp

end Generators

end AdditivePowers

end TauCeti.PD
