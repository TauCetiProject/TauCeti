/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.Index

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
counting form.

## Main results

* `ZMod.mul_card_filter_natCast_val`: counting a condition on the reduction modulo `m ∣ n`.
* `ZMod.card_filter_forall_natCast_val`: counting independent conditions on coprime factors.
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

end ZMod
