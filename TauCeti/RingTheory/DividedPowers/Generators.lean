/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.ZMod.Basic
import TauCeti.Data.Nat.Choose.Vandermonde

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

We also record a witness over `TrivSqZeroExt (ZMod 2) (ZMod 2)` showing that an `AdditivePowers`
structure need not satisfy `mul_dpow`, so the generator hypotheses cannot be omitted.

## Main definitions

* `TauCeti.PD.AdditivePowers I`: additive divided-power candidates on `I`.
* `TauCeti.PD.AdditivePowers.ofDividedPowers`: the candidate underlying a divided power structure.
* `TauCeti.PD.AdditivePowers.toDividedPowers`: the divided power structure on `I = span S` built
  from a candidate satisfying both identities at every `s ∈ S`.

## Main results

* `TauCeti.PD.AdditivePowers.dpow_eq_from_gens`: candidates agreeing on generators are equal.
* `TauCeti.PD.AdditivePowers.mul_dpow_add`: the multiplication identity is stable under sums.
* `TauCeti.PD.AdditivePowers.mul_dpow_of_span`: propagation of `mul_dpow` from a generating set.
* `TauCeti.PD.AdditivePowers.dpow_comp_add`: the iteration identity is stable under sums.
* `TauCeti.PD.AdditivePowers.dpow_comp_of_span`: propagation of `dpow_comp` from a generating set.
* `TauCeti.PD.AdditivePowers.toDividedPowers_unique`: a divided power structure is determined by
  its candidate.
* `TauCeti.PD.AdditivePowers.exists_not_dividedPowers`: existence of an `AdditivePowers` structure
  that does not underlie any `DividedPowers` structure.

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

/-- Two `DividedPowers` structures are equal if and only if their underlying additive candidates
are equal. -/
@[simp]
theorem ofDividedPowers_inj {γ γ' : DividedPowers I} :
    ofDividedPowers γ = ofDividedPowers γ' ↔ γ = γ' :=
  ⟨fun h ↦ DividedPowers.ext γ γ' fun n x _ ↦
    congrFun (congrFun (congrArg AdditivePowers.dpow h) n) x,
   fun h ↦ h ▸ rfl⟩

variable (δ : AdditivePowers I)

/-- In positive degree a candidate vanishes at `0`. -/
theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : δ.dpow n 0 = 0 := by
  have h := δ.dpow_mul (n := n) (a := 0) I.zero_mem
  rwa [zero_mul, zero_pow hn, zero_mul] at h

/-- `AdditivePowers.dpow_add` with a sum over `range (n + 1)`. -/
theorem dpow_add' {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    δ.dpow n (x + y) = ∑ k ∈ range (n + 1), δ.dpow k x * δ.dpow (n - k) y := by
  rw [δ.dpow_add hx hy, sum_antidiagonal_eq_sum_range_succ_mk]

/-- Scalar homogeneity with the scalar on the right. -/
theorem dpow_mul_right {n : ℕ} {a x : A} (hx : x ∈ I) :
    δ.dpow n (x * a) = δ.dpow n x * a ^ n := by
  rw [mul_comm, δ.dpow_mul hx, mul_comm]

/-- The multinomial expansion of an additive divided-power candidate on a finite sum. -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) {n : ℕ} :
    δ.dpow n (∑ i ∈ s, x i) =
      ∑ k ∈ s.sym n, ∏ i ∈ s, δ.dpow (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' δ.dpow δ.dpow_zero δ.dpow_add δ.dpow_eval_zero hx

/-- If two additive divided-power candidates on `I` agree on a generating set of `I`, then they
are equal. -/
theorem dpow_eq_from_gens (δ' : AdditivePowers I) {S : Set A} (hS : I = Ideal.span S)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, δ.dpow n a = δ'.dpow n a) : δ' = δ := by
  suffices ∀ z ∈ Ideal.span S, ∀ n, δ.dpow n z = δ'.dpow n z by
    ext n x hx
    exact (this x (hS ▸ hx) n).symm
  intro z hz
  induction hz using Submodule.span_induction with
  | mem s hs => exact fun n ↦ hdp s hs
  | zero =>
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [δ.dpow_zero I.zero_mem, δ'.dpow_zero I.zero_mem]
    · rw [δ.dpow_eval_zero hn, δ'.dpow_eval_zero hn]
  | add x y hxS hyS ihx ihy =>
    intro n
    rw [δ.dpow_add (hS ▸ hxS) (hS ▸ hyS), δ'.dpow_add (hS ▸ hxS) (hS ▸ hyS)]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [ihx k.1, ihy k.2]
  | smul a x hxS ihx =>
    intro n
    rw [smul_eq_mul, δ.dpow_mul (hS ▸ hxS), δ'.dpow_mul (hS ▸ hxS), ihx n]

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
          F (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) := by
    rw [δ.dpow_add hx hy, δ.dpow_add hx hy, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun pq _ ↦ ?_
    calc _ = (δ.dpow pq.1.1 x * δ.dpow pq.2.1 x) * (δ.dpow pq.1.2 y * δ.dpow pq.2.2 y) := by
          ring
      _ = _ := by simp only [F, hmx, hmy]; push_cast; ring
  have hmaps : ∀ pq ∈ antidiagonal m ×ˢ antidiagonal n,
      (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2) ∈ antidiagonal (m + n) := by
    intro pq hpq
    simp only [mem_product, mem_antidiagonal] at hpq ⊢
    omega
  rw [hL, ← sum_fiberwise_of_maps_to hmaps, δ.dpow_add hx hy, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [← Finset.sum_filter_antidiagonal_choose m n r.1 r.2 (mem_antidiagonal.mp hr), Nat.cast_sum,
    sum_mul]
  refine sum_congr rfl fun pq hpq ↦ ?_
  have heq := (mem_filter.mp hpq).2
  have h1 : pq.1.1 + pq.2.1 = r.1 := congrArg Prod.fst heq
  have h2 : pq.1.2 + pq.2.2 = r.2 := congrArg Prod.snd heq
  rw [h1, h2]

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

/-- The multiplication identity holds automatically at `0`. -/
theorem mul_dpow_zero (m n : ℕ) :
    δ.dpow m 0 * δ.dpow n 0 = ((m + n).choose m : A) * δ.dpow (m + n) 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [δ.dpow_zero I.zero_mem]
  · rw [δ.dpow_eval_zero hm, zero_mul, δ.dpow_eval_zero (by omega), mul_zero]

/-- The multiplication identity is preserved under multiplication by any scalar `a : A`. -/
theorem mul_dpow_mul {x : A} (hx : x ∈ I) (a : A) {m n : ℕ}
    (h : δ.dpow m x * δ.dpow n x = ((m + n).choose m : A) * δ.dpow (m + n) x) :
    δ.dpow m (a * x) * δ.dpow n (a * x) =
      ((m + n).choose m : A) * δ.dpow (m + n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul hx, δ.dpow_mul hx]
  calc
    a ^ m * δ.dpow m x * (a ^ n * δ.dpow n x)
        = a ^ (m + n) * (δ.dpow m x * δ.dpow n x) := by rw [pow_add]; ring
    _ = a ^ (m + n) * (((m + n).choose m : A) * δ.dpow (m + n) x) := by rw [h]
    _ = ((m + n).choose m : A) * (a ^ (m + n) * δ.dpow (m + n) x) := by ring

/-- The iteration identity holds automatically at `0`. -/
theorem dpow_comp_zero (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    δ.dpow m (δ.dpow n 0) = (uniformBell m n : A) * δ.dpow (m * n) 0 := by
  rw [δ.dpow_eval_zero hn]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [δ.dpow_zero I.zero_mem, uniformBell_zero_left]
  · rw [δ.dpow_eval_zero hm, δ.dpow_eval_zero (Nat.mul_ne_zero hm hn), mul_zero]

/-- The iteration identity is preserved under multiplication by any scalar `a : A`. -/
theorem dpow_comp_mul {x : A} (hx : x ∈ I) (a : A) {m n : ℕ} (hn : n ≠ 0)
    (h : δ.dpow m (δ.dpow n x) = (uniformBell m n : A) * δ.dpow (m * n) x) :
    δ.dpow m (δ.dpow n (a * x)) = (uniformBell m n : A) * δ.dpow (m * n) (a * x) := by
  rw [δ.dpow_mul hx, δ.dpow_mul (δ.dpow_mem hn hx), h, δ.dpow_mul hx, ← pow_mul, mul_comm n m]
  ring

/-! ### Divided powers from identities on generators -/

section Generators

variable {S : Set A} (hS : I = Ideal.span S)
include hS

/-- If the multiplication identity holds on a generating set `S` of `I`, then it holds on all of
`I`. -/
theorem mul_dpow_of_span
    (hmul : ∀ s ∈ S, ∀ m n, δ.dpow m s * δ.dpow n s = (m + n).choose m * δ.dpow (m + n) s)
    {x : A} (hx : x ∈ I) (m n : ℕ) :
    δ.dpow m x * δ.dpow n x = (m + n).choose m * δ.dpow (m + n) x := by
  have hI : ∀ {z}, z ∈ Ideal.span S → z ∈ I := fun hz ↦ hS ▸ hz
  rw [hS] at hx
  induction hx using Submodule.span_induction generalizing m n with
  | mem s hs => exact hmul s hs m n
  | zero => exact δ.mul_dpow_zero m n
  | add x y hx hy ihx ihy => exact δ.mul_dpow_add (hI hx) (hI hy) ihx ihy m n
  | smul a x hx ih => exact δ.mul_dpow_mul (hI hx) a (ih m n)

/-- If the multiplication and iteration identities hold on a generating set `S` of `I`, then the
iteration identity holds on all of `I`. -/
theorem dpow_comp_of_span
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
  | zero => exact δ.dpow_comp_zero m hn
  | add x y hx hy ihx ihy =>
    exact δ.dpow_comp_add (hI hx) (hI hy) (hmul' x (hI hx)) (hmul' y (hI hy))
      (fun m n hn ↦ ihx m hn) (fun m n hn ↦ ihy m hn) m hn
  | smul a x hx ih => exact δ.dpow_comp_mul (hI hx) a hn (ih m hn)

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

omit hS in
/-- Applying `toDividedPowers` to the additive candidate of an existing `DividedPowers I`
recovers that structure. -/
@[simp]
theorem toDividedPowers_ofDividedPowers (γ : DividedPowers I) {S : Set A} (hS : I = Ideal.span S)
    (hmul : ∀ s ∈ S, ∀ m n,
      (ofDividedPowers γ).dpow m s * (ofDividedPowers γ).dpow n s =
        ((m + n).choose m : A) * (ofDividedPowers γ).dpow (m + n) s)
    (hcomp : ∀ s ∈ S, ∀ m n, n ≠ 0 →
      (ofDividedPowers γ).dpow m ((ofDividedPowers γ).dpow n s) =
        (uniformBell m n : A) * (ofDividedPowers γ).dpow (m * n) s) :
    (ofDividedPowers γ).toDividedPowers hS hmul hcomp = γ :=
  DividedPowers.ext _ _ fun _ _ ↦ by simp

end Generators

/-! ### Strictness of `AdditivePowers` -/

private noncomputable def counterexampleDpow (n : ℕ)
    (x : TrivSqZeroExt (ZMod 2) (ZMod 2)) : TrivSqZeroExt (ZMod 2) (ZMod 2) := by
  classical
  exact if x ∈ Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} then
    match n with
    | 0 => 1
    | 1 => x
    | 3 => x
    | _ => 0
  else 0

private lemma counterexampleDpow_mem {n : ℕ} (hn : n ≠ 0)
    {x : TrivSqZeroExt (ZMod 2) (ZMod 2)}
    (hx : x ∈ Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}) :
    counterexampleDpow n x ∈ Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} := by
  classical
  match n with
  | 0 => exact absurd rfl hn
  | 1 | 2 | 3 | _ + 4 => simp [counterexampleDpow, hx]

private noncomputable def counterexampleAdditivePowers :
    AdditivePowers
      (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} : Ideal (TrivSqZeroExt (ZMod 2) (ZMod 2))) where
  dpow := counterexampleDpow
  dpow_null hx := by
    classical
    simp [counterexampleDpow, hx]
  dpow_zero hx := by
    classical
    simp [counterexampleDpow, hx]
  dpow_one hx := by
    classical
    simp [counterexampleDpow, hx]
  dpow_mem hn hx := counterexampleDpow_mem hn hx
  dpow_add {n x y} hx hy := by
    classical
    have hxy : x + y ∈ Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} := Ideal.add_mem _ hx hy
    match n with
    | 0 => simp [counterexampleDpow, hx, hy, hxy]
    | 1 =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp [counterexampleDpow, hx, hy, hxy, add_comm]
    | k + 2 =>
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
      have hmid : ∑ p ∈ antidiagonal k,
          counterexampleDpow (p.1 + 1) x * counterexampleDpow (p.2 + 1) y = 0 :=
        Finset.sum_eq_zero fun p _ ↦ by
          rcases Ideal.mem_span_singleton.mp (counterexampleDpow_mem p.1.succ_ne_zero hx) with
            ⟨u, hu⟩
          rcases Ideal.mem_span_singleton.mp (counterexampleDpow_mem p.2.succ_ne_zero hy) with
            ⟨v, hv⟩
          rw [hu, hv, mul_mul_mul_comm, TrivSqZeroExt.inr_mul_inr, zero_mul]
      rw [hmid, add_zero]
      match k with
      | 0 | 1 => simp [counterexampleDpow, hx, hy, hxy, add_comm]
      | _ + 2 => simp [counterexampleDpow, hx, hy, hxy]
  dpow_mul {n a x} hx := by
    classical
    have hax : a * x ∈ Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} := Ideal.mul_mem_left _ a hx
    match n with
    | 0 | 1 | 2 | _ + 4 => simp [counterexampleDpow, hx, hax]
    | 3 =>
      simp only [counterexampleDpow, hx, hax, ↓reduceIte]
      rcases Ideal.mem_span_singleton.mp hx with ⟨b, rfl⟩
      have hcube : a.fst * a.fst * a.fst = a.fst := by
        have : ∀ u : ZMod 2, u * u * u = u := by decide
        exact this a.fst
      ext
      · simp
      · simp [pow_succ, hcube]

/-- Not every `AdditivePowers` structure underlies a `DividedPowers` structure: on the dual
numbers `𝔽₂[ε]/(ε²)` with `I = (ε)`, the family `δ₀ = 1`, `δ₁ = δ₃ = id`, and `δₙ = 0` for
`n = 2` and `n ≥ 4` satisfies all additive divided power axioms, yet fails `mul_dpow` at
`m = 1, n = 2` because `δ₁(ε) * δ₂(ε) = 0 ≠ ε = 3 * δ₃(ε)`. -/
theorem exists_not_dividedPowers :
    ∃ δ : AdditivePowers (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}),
      δ.dpow 1 (TrivSqZeroExt.inr 1) * δ.dpow 2 (TrivSqZeroExt.inr 1) ≠
        (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
          δ.dpow (1 + 2) (TrivSqZeroExt.inr 1) ∧
      ∀ γ : DividedPowers (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)}), γ.dpow ≠ δ.dpow := by
  classical
  let δ := counterexampleAdditivePowers
  have hε : TrivSqZeroExt.inr (1 : ZMod 2) ∈
      (Ideal.span {TrivSqZeroExt.inr (1 : ZMod 2)} : Ideal (TrivSqZeroExt (ZMod 2) (ZMod 2))) :=
    Ideal.subset_span rfl
  -- Verify `mul_dpow` fails at `(m, n) = (1, 2)` on `ε = TrivSqZeroExt.inr 1`.
  have hlhs : δ.dpow 1 (TrivSqZeroExt.inr 1) * δ.dpow 2 (TrivSqZeroExt.inr 1) = 0 := by
    simp [δ, counterexampleAdditivePowers, counterexampleDpow, hε]
  have hrhs : (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
      δ.dpow (1 + 2) (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
    simp only [δ, counterexampleAdditivePowers, counterexampleDpow, hε, ↓reduceIte]
    have h3 : (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) = 1 := by
      simp only [TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast,
        TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, Nat.choose_one_right, and_true]
      decide
    rw [h3, one_mul]
  have hne : δ.dpow 1 (TrivSqZeroExt.inr 1) * δ.dpow 2 (TrivSqZeroExt.inr 1) ≠
      (((1 + 2).choose 1 : ℕ) : TrivSqZeroExt (ZMod 2) (ZMod 2)) *
        δ.dpow (1 + 2) (TrivSqZeroExt.inr 1) := by
    rw [hlhs, hrhs]
    exact fun h01 ↦ zero_ne_one (congrArg TrivSqZeroExt.snd h01)
  -- No `DividedPowers` structure can share `δ.dpow`, since it would satisfy `mul_dpow`.
  refine ⟨δ, hne, fun γ hγ ↦ hne ?_⟩
  have hmul := γ.mul_dpow (m := 1) (n := 2) hε
  rwa [hγ] at hmul

end AdditivePowers

end TauCeti.PD
