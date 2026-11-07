/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.Index
import TauCeti.Data.ZMod.FinEquiv

/-!
# Counting residues by a condition on their reduction

A condition on `x : ZMod n` that only reads the reduction of `x` modulo a divisor of `n` can be
counted after reducing. This file records the two counting laws that result.

Reducing along a single divisor `m ∣ n` multiplies the count: the reduction `ZMod n → ZMod m`,
written here as `fun x ↦ (x.val : ZMod m)`, is a surjective additive homomorphism, so all of its
fibres have the same size and a condition pulled back along it holds proportionally often. The
identity is stated as `m * (count over ZMod n) = n * (count over ZMod m)`, which carries the same
information as a division by `m` without a quotient appearing.

Splitting a modulus into pairwise coprime factors multiplies the counts: conditions imposed on
the separate factors are independent, so the number of residues satisfying all of them is the
product of the individual counts. This is the Chinese remainder theorem `ZMod.prodEquivPi` in
counting form. In particular the number of roots modulo `n` of an integer polynomial is the product
of its numbers of roots modulo the prime powers exactly dividing `n`, by `ZMod.equivPi`.

Sums over the residues modulo `n` of a function of the least nonnegative representative are sums
over `range n`; summed over the representatives that are multiples of `n / m`, for `m ∣ n`, they
become sums over the residues modulo `m`.

## Main results

* `ZMod.mul_card_filter_natCast_val`: counting a condition on the reduction modulo `m ∣ n`.
* `ZMod.sum_comp_natCast_val`: summing a function of the reduction modulo `m ∣ n`.
* `ZMod.sum_val_eq_sum_range`: summing a function of the representatives over `range n`.
* `ZMod.sum_Ico_mul`: splitting an integer interval into complete residue blocks.
* `ZMod.sum_ite_dvd_val`: summing over the representatives that are multiples of `n / m`.
* `ZMod.card_filter_forall_natCast_val`: counting independent conditions on coprime factors.
* `ZMod.natCard_aeval_eq_zero_eq_prod_primeFactors`: the number of roots of an integer polynomial
  modulo `n` is multiplicative over the prime-power factorization of `n`.
* `ZMod.natCard_aeval_eq_zero_eq_zero_of_dvd`: an integer polynomial with no roots modulo `m` has
  none modulo any multiple of `m`.
* `ZMod.card_filter_not_self_dvd_val`: the residues whose representative the modulus does not
  divide, the base case of such a count.
-/

public section

open Finset

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

namespace ZMod

variable {m n : ℕ}

/-- The residues modulo `n` satisfying a condition on their reduction modulo `m ∣ n` are as many
as the residues modulo `m` satisfying it, times the common size of a fibre of the reduction. -/
private theorem card_filter_natCast_val_eq_mul_card_fiber [NeZero m] [NeZero n] (hmn : m ∣ n)
    (Q : ZMod m → Prop) [DecidablePred Q] :
    #{x : ZMod n | Q (x.val : ZMod m)}
      = #{y : ZMod m | Q y} * #{x : ZMod n | (x.val : ZMod m) = 0} := by
  have hval : ∀ x : ZMod n, ((x.val : ZMod m)) = castHom hmn (ZMod m) x := fun x => by
    rw [castHom_apply, natCast_val]
  have hsurj : Function.Surjective (castHom hmn (ZMod m)) := castHom_surjective hmn
  simp only [hval]
  have hfib : ∀ y : ZMod m, #{x : ZMod n | castHom hmn (ZMod m) x = y}
      = #{x : ZMod n | castHom hmn (ZMod m) x = 0} := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range (castHom hmn (ZMod m)) (hsurj y) (hsurj 0)
  -- split the count into the fibres over the residues modulo `m` satisfying `Q`; the hole left
  -- by `Finset.sum_congr` is the identification of each of those fibres with the fibre over `0`
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod n => castHom hmn (ZMod m) x)
      (t := {y : ZMod m | Q y})
      (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩),
    Finset.sum_congr rfl fun y hy => ?_, Finset.sum_const, smul_eq_mul]
  have hy' : Q y := (Finset.mem_filter.mp hy).2
  rw [← hfib y]
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hy', h⟩⟩

/-- **Counting a condition on the reduction modulo a divisor.** For `m ∣ n`, the residues modulo
`n` whose reduction modulo `m` satisfies `Q` are `n / m` times as many as the residues modulo `m`
satisfying `Q`, stated without the quotient. -/
theorem mul_card_filter_natCast_val [NeZero m] [NeZero n] (hmn : m ∣ n)
    (Q : ZMod m → Prop) [DecidablePred Q] :
    m * #{x : ZMod n | Q (x.val : ZMod m)} = n * #{y : ZMod m | Q y} := by
  have h2 := card_filter_natCast_val_eq_mul_card_fiber hmn (fun _ => True)
  simp only [Finset.filter_true, Finset.card_univ, ZMod.card] at h2
  rw [card_filter_natCast_val_eq_mul_card_fiber hmn Q]
  calc m * (#{y : ZMod m | Q y} * #{x : ZMod n | (x.val : ZMod m) = 0})
      = m * #{x : ZMod n | (x.val : ZMod m) = 0} * #{y : ZMod m | Q y} := by ring
    _ = n * #{y : ZMod m | Q y} := by rw [← h2]

/-- **Summing a function of the reduction modulo a divisor.** For `m ∣ n`, a function of the
reduction modulo `m` summed over the residues modulo `n` is `n / m` times its sum over the residues
modulo `m`: every fibre of the reduction has `n / m` elements. -/
theorem sum_comp_natCast_val {M : Type*} [AddCommMonoid M] [NeZero m] [NeZero n] (hmn : m ∣ n)
    (f : ZMod m → M) : ∑ x : ZMod n, f (x.val : ZMod m) = (n / m) • ∑ y : ZMod m, f y := by
  classical
  have hsurj : Function.Surjective fun x : ZMod n ↦ (x.val : ZMod m) := fun y ↦ by
    obtain ⟨x, hx⟩ := castHom_surjective hmn y
    exact ⟨x, by dsimp only; rwa [natCast_val, ← castHom_apply]⟩
  have hfib (y : ZMod m) : #{x : ZMod n | (x.val : ZMod m) = y} = n / m := by
    have h := mul_card_filter_natCast_val hmn (· = y)
    simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.card_singleton,
      mul_one] at h
    exact Nat.eq_div_of_mul_eq_right (NeZero.ne m) h
  rw [Finset.sum_comp, Finset.image_univ_of_surjective hsurj, Finset.smul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by rw [hfib]

/-- **Summing over the representatives.** A function of the least nonnegative representative
summed over the residues modulo `n` is its sum over `range n`. -/
theorem sum_val_eq_sum_range {M : Type*} [AddCommMonoid M] [NeZero n] (f : ℕ → M) :
    ∑ x : ZMod n, f x.val = ∑ i ∈ range n, f i := by
  rw [Finset.sum_range, ← (finEquiv n).symm.toEquiv.sum_comp]
  simp

/-- Split a sum over an integer interval with endpoints divisible by the modulus into
complete residue blocks. The summand need not be periodic. -/
theorem sum_Ico_mul {A : Type*} [AddCommMonoid A] [NeZero n] (l u : ℤ) (f : ℤ → A) :
    ∑ z ∈ Ico l u, ∑ a : ZMod n, f ((a.val : ℤ) + n * z) =
      ∑ k ∈ Ico (n * l) (n * u), f k := by
  classical
  rw [← sum_product' (Ico l u) univ (fun z (a : ZMod n) ↦ f ((a.val : ℤ) + n * z))]
  refine sum_bij (fun p _ ↦ (p.2.val : ℤ) + n * p.1) ?_ ?_ ?_ (by intros; rfl)
  · rintro ⟨z, a⟩ hp
    have hz := mem_Ico.mp (mem_product.mp hp).1
    have ha := a.val_lt
    have hn := NeZero.pos n
    simp only [mem_Ico]
    constructor <;> nlinarith
  · rintro ⟨z, a⟩ hp ⟨w, b⟩ hq hab
    have hab' := congrArg (fun k : ℤ ↦ (k : ZMod n)) hab
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul,
      ZMod.natCast_self, zero_mul, add_zero] at hab'
    subst b
    have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have : z = w := mul_left_cancel₀ hn (add_left_cancel hab)
    simp [this]
  · intro k hk
    obtain ⟨z, hz⟩ := (ZMod.intCast_eq_iff n k (k : ZMod n)).mp rfl
    refine ⟨(z, k), mem_product.mpr ⟨?_, mem_univ _⟩, hz.symm⟩
    have ha := (k : ZMod n).val_lt
    have hn := NeZero.pos n
    have hk := mem_Ico.mp hk
    simp only [mem_Ico]
    constructor <;> nlinarith

/-- **Summing over the multiples of `n / m`.** For `m ∣ n`, the representatives modulo `n` that
are multiples of `n / m` are the `(n / m) y` with `y < m`, so a function of the quotient summed
over them is its sum over the residues modulo `m`. -/
theorem sum_ite_dvd_val {M : Type*} [AddCommMonoid M] [NeZero m] [NeZero n] (hmn : m ∣ n)
    (f : ℕ → M) :
    ∑ x : ZMod n, (if n / m ∣ x.val then f (x.val / (n / m)) else 0) = ∑ y : ZMod m, f y.val := by
  obtain ⟨L, rfl⟩ := hmn
  have hL : 0 < L := Nat.pos_of_ne_zero fun h ↦ NeZero.ne (m * L) (by rw [h, mul_zero])
  rw [Nat.mul_div_cancel_left _ (NeZero.pos m),
    sum_val_eq_sum_range (fun i ↦ if L ∣ i then f (i / L) else 0), sum_val_eq_sum_range f]
  -- the block `[k L, (k + 1) L)` contains the single multiple `k L` of `L`
  have key (k : ℕ) :
      ∑ i ∈ range (k * L), (if L ∣ i then f (i / L) else 0) = ∑ q ∈ range k, f q := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hblock :
          ∑ x ∈ range L, (if L ∣ k * L + x then f ((k * L + x) / L) else 0) = f k := by
        rw [sum_eq_single_of_mem 0 (mem_range.mpr hL) fun x hx hx0 ↦ ite_eq_right_iff.mpr
          fun h ↦ absurd ((Nat.dvd_add_right (dvd_mul_left L k)).mp h)
            (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hx0) (mem_range.mp hx))]
        simp [hL.ne']
      rw [Nat.succ_mul, sum_range_add, sum_range_succ, ih, hblock]
  exact key m

/-- **All residues but zero have a representative the modulus does not divide.** A representative
is smaller than the modulus, so the modulus divides it exactly when it vanishes. -/
@[simp]
theorem card_filter_not_self_dvd_val [NeZero m] : #{z : ZMod m | ¬m ∣ z.val} = m - 1 := by
  have hzero : ∀ z : ZMod m, m ∣ z.val ↔ z = 0 := fun z =>
    ⟨fun hdvd => (ZMod.val_eq_zero z).mp (Nat.eq_zero_of_dvd_of_lt hdvd z.val_lt),
      fun h => by simp [h]⟩
  have herase : ({z : ZMod m | ¬m ∣ z.val} : Finset (ZMod m)) = Finset.univ.erase 0 := by
    ext z
    simp [hzero, Finset.mem_erase]
  rw [herase, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

/-- **Counting independent conditions on coprime factors.** If the moduli `a i` are pairwise
coprime, the residues modulo `∏ i, a i` whose reduction modulo each `a i` satisfies `Q i` are
counted by the product over `i` of the residues modulo `a i` satisfying `Q i`. -/
theorem card_filter_forall_natCast_val {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (Q : ∀ i, ZMod (a i) → Prop) [∀ i, DecidablePred (Q i)] :
    #{x : ZMod (∏ i, a i) | ∀ i, Q i (x.val : ZMod (a i))}
      = ∏ i, #{y : ZMod (a i) | Q i y} := by
  classical
  have hval : ∀ (x : ZMod (∏ i, a i)) (i : ι),
      ((x.val : ZMod (a i))) = prodEquivPi a hcop x i := fun x i => by
    rw [prodEquivPi_apply, castHom_apply, natCast_val]
  have e : {x : ZMod (∏ i, a i) // ∀ i, Q i (x.val : ZMod (a i))} ≃
      ∀ i, {y : ZMod (a i) // Q i y} :=
    ((prodEquivPi a hcop).toEquiv.subtypeEquiv fun x => by simp only [hval]; rfl).trans
      Equiv.subtypePiEquivPi
  simpa only [Fintype.card_subtype, Fintype.card_pi] using Fintype.card_congr e

/-- **Counting roots prime power by prime power.** For `n ≠ 0`, the number of roots modulo `n` of
an integer polynomial `P` is the product, over the primes `p ∣ n`, of its numbers of roots modulo
the exact prime powers `p ^ vₚ(n)`. -/
theorem natCard_aeval_eq_zero_eq_prod_primeFactors (hn : n ≠ 0) (P : Polynomial ℤ) :
    Nat.card {x : ZMod n // Polynomial.aeval x P = 0} =
      ∏ p ∈ n.primeFactors,
        Nat.card {x : ZMod (p ^ n.factorization p) // Polynomial.aeval x P = 0} := by
  let e := equivPi n hn
  have he (x : ZMod n) (p : n.primeFactors) :
      Polynomial.aeval (e x p) P = e (Polynomial.aeval x P) p :=
    Polynomial.aeval_algHom_apply ((Pi.evalRingHom _ p).comp e.toRingHom).toIntAlgHom x P
  have e' : {x : ZMod n // Polynomial.aeval x P = 0} ≃
      ∀ p : n.primeFactors, {y : ZMod (p ^ n.factorization p) // Polynomial.aeval y P = 0} :=
    (e.toEquiv.subtypeEquiv fun x ↦ by
      rw [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_eq_zero_iff e e.injective,
        funext_iff]
      simp only [he, Pi.zero_apply]).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e', Nat.card_pi, Finset.prod_coe_sort n.primeFactors
    (fun p ↦ Nat.card {y : ZMod (p ^ n.factorization p) // Polynomial.aeval y P = 0})]

/-- **No roots modulo a divisor.** If an integer polynomial `P` has no roots modulo `m`, then it
has none modulo any multiple `n` of `m`, since a root modulo `n` reduces to one modulo `m`. -/
theorem natCard_aeval_eq_zero_eq_zero_of_dvd (hmn : m ∣ n) {P : Polynomial ℤ}
    (hP : ∀ y : ZMod m, Polynomial.aeval y P ≠ 0) :
    Nat.card {x : ZMod n // Polynomial.aeval x P = 0} = 0 := by
  refine Nat.card_eq_zero.mpr (.inl ⟨fun ⟨x, hx⟩ ↦ hP (castHom hmn (ZMod m) x) ?_⟩)
  have h := Polynomial.aeval_algHom_apply (castHom hmn (ZMod m)).toIntAlgHom x P
  rwa [hx, map_zero] at h

end ZMod
