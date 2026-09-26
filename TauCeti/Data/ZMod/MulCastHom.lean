/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Multiplication by `k` from `ZMod m` to `ZMod (m * k)`

For natural numbers `m`, `k` and `n = m * k`, multiplication by `k` is a well-defined additive
homomorphism `ZMod m →+ ZMod n`: the class of an integer `a` modulo `m` goes to the class of
`a * k` modulo `n`. Together with the reduction `ZMod.castHom : ZMod n →+* ZMod k` it forms, for
`k ≠ 0`, the short exact sequence of cyclic groups

```text
0 → ZMod m → ZMod n → ZMod k → 0
```

since multiplication by `k ≠ 0` is injective, the reduction is surjective, and the classes killed
by the reduction are exactly the multiples of `k` (for `k = 0` the multiplication is the zero map,
and only the exactness at `ZMod n` and the surjectivity survive). The multiplications compose, and
they commute with the reductions. The instance of interest is `m = pⁱ`, `k = pʲ`, `n = pⁱ⁺ʲ`, which
gives the sequences `0 → ℤ/pⁱ → ℤ/pⁱ⁺ʲ → ℤ/pʲ → 0` of the coefficient systems of `p`-adic
characters.

## Main definitions

* `ZMod.mulCastHom k h`: multiplication by `k`, `ZMod m →+ ZMod n`, for `h : m * k = n`.

## Main results

* `ZMod.mulCastHom_injective`: multiplication by `k ≠ 0` is injective.
* `ZMod.exact_mulCastHom_castHom`: exactness of `ZMod m → ZMod n → ZMod k`.
* `ZMod.mulCastHom_mulCastHom`: two successive multiplications compose to one.
* `ZMod.castHom_mulCastHom_eq_mulCastHom_castHom`: the reductions commute with the
  multiplications.
-/

public section

namespace ZMod

variable {m n : ℕ} (k : ℕ) (h : m * k = n)

/-- **Multiplication by `k`, `ZMod m →+ ZMod n`** for `n = m * k`: the class of an integer `a`
modulo `m` goes to the class of `a * k` modulo `n`. -/
def mulCastHom : ZMod m →+ ZMod n :=
  ZMod.lift m ⟨zmultiplesHom (ZMod n) (k : ZMod n), by
    rw [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, h, natCast_self]⟩

/-- Multiplication by `k` on the class of an integer `a` is the class of `a * k`. -/
@[simp]
theorem mulCastHom_intCast (a : ℤ) : mulCastHom k h (a : ZMod m) = (a : ZMod n) * k := by
  rw [mulCastHom, lift_coe, zmultiplesHom_apply, zsmul_eq_mul]

/-- Multiplication by `k` sends a class to `k` times its cast, for any representative. -/
theorem mulCastHom_apply (a : ZMod m) : mulCastHom k h a = (a.cast : ZMod n) * k := by
  conv_lhs => rw [← intCast_zmod_cast a]
  rw [mulCastHom_intCast, intCast_cast]

/-- Multiplication by `k ≠ 0` is injective on `ZMod m`: if `m * k ∣ a * k` then `m ∣ a`. -/
theorem mulCastHom_injective (hk : k ≠ 0) : Function.Injective (mulCastHom k h) := by
  rw [mulCastHom, lift_injective]
  intro a ha
  have ha' : ((a * k : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_mul, Int.cast_natCast]
    simpa only [zmultiplesHom_apply, zsmul_eq_mul] using ha
  rw [intCast_zmod_eq_zero_iff_dvd, ← h, Nat.cast_mul,
    mul_dvd_mul_iff_right (by exact_mod_cast hk)] at ha'
  exact (intCast_zmod_eq_zero_iff_dvd a m).2 ha'

/-- Multiplication by `1` is the identity. -/
@[simp]
theorem mulCastHom_one : mulCastHom 1 (mul_one m) = AddMonoidHom.id (ZMod m) :=
  AddMonoidHom.ext fun a ↦ by
    obtain ⟨a, rfl⟩ := intCast_surjective a
    rw [mulCastHom_intCast, Nat.cast_one, mul_one, AddMonoidHom.id_apply]

/-- Two successive multiplications, by `k` and then by `k₂`, compose to the multiplication by
`k * k₂`. The index equation of the composite is taken as a hypothesis, so that any proof of it
may be used. -/
theorem mulCastHom_mulCastHom {n₂ : ℕ} (k₂ : ℕ) (h₂ : n * k₂ = n₂) (h₁₂ : m * (k * k₂) = n₂)
    (a : ZMod m) : mulCastHom k₂ h₂ (mulCastHom k h a) = mulCastHom (k * k₂) h₁₂ a := by
  obtain ⟨a, rfl⟩ := intCast_surjective a
  rw [mulCastHom_intCast, ← Int.cast_natCast k, ← Int.cast_mul, mulCastHom_intCast,
    mulCastHom_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, mul_assoc]

/-- Multiplication by `k` is semilinear for the reduction `ZMod n → ZMod m`: scaling a class of
`ZMod m` by the reduction of `b : ZMod n` and then multiplying by `k` is scaling the result by
`b`. -/
theorem mulCastHom_castHom_mul (b : ZMod n) (a : ZMod m) :
    mulCastHom k h (castHom (Dvd.intro k h) (ZMod m) b * a) = b * mulCastHom k h a := by
  obtain ⟨a, rfl⟩ := intCast_surjective a
  obtain ⟨b, rfl⟩ := intCast_surjective b
  rw [map_intCast, ← Int.cast_mul, mulCastHom_intCast, mulCastHom_intCast, Int.cast_mul,
    mul_assoc]

-- Not `@[simp]`: Mathlib's simp lemma `ZMod.castHom_apply` rewrites the left-hand side to
-- `(mulCastHom k h a).cast` first, so the tagged lemma fails the `simpNF` linter; the simp normal
-- form is `cast_mulCastHom` below.
/-- The reduction modulo `k` kills the multiples of `k`. -/
theorem castHom_mulCastHom (a : ZMod m) :
    castHom (Dvd.intro_left m h) (ZMod k) (mulCastHom k h a) = 0 := by
  obtain ⟨a, rfl⟩ := intCast_surjective a
  rw [mulCastHom_intCast, map_mul, map_natCast, natCast_self, mul_zero]

/-- The cast of a multiple of `k` to `ZMod k` vanishes: the simp normal form of
`castHom_mulCastHom`. -/
@[simp]
theorem cast_mulCastHom (a : ZMod m) : ((mulCastHom k h a).cast : ZMod k) = 0 := by
  rw [← castHom_apply (h := Dvd.intro_left m h), castHom_mulCastHom]

/-- **Exactness of `ZMod m → ZMod n → ZMod k`**: the classes modulo `n = m * k` killed by the
reduction modulo `k` are exactly the multiples of `k`. -/
theorem exact_mulCastHom_castHom :
    Function.Exact (mulCastHom k h) (castHom (Dvd.intro_left m h) (ZMod k)) := by
  intro y
  obtain ⟨b, rfl⟩ := intCast_surjective y
  rw [map_intCast, intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mulCastHom_intCast, Int.cast_mul, Int.cast_natCast, mul_comm]⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := intCast_surjective x
    have hx' : ((a * k : ℤ) : ZMod n) = b := by
      rw [Int.cast_mul, Int.cast_natCast, ← mulCastHom_intCast k h]
      exact hx
    rw [intCast_eq_intCast_iff_dvd_sub] at hx'
    have hk : (k : ℤ) ∣ n := by exact_mod_cast Dvd.intro_left m h
    simpa using (hk.trans hx').add (dvd_mul_left (k : ℤ) a)

/-- The reductions commute with the multiplications: reducing `k * a` modulo `n'` is `k` times the
reduction of `a` modulo `m'`, for `m' * k = n'`. Both divisibilities are hypotheses, so that any
proofs of them may be used. -/
theorem castHom_mulCastHom_eq_mulCastHom_castHom {m' n' : ℕ} (h' : m' * k = n') (hm : m' ∣ m)
    (hn : n' ∣ n) (a : ZMod m) :
    castHom hn (ZMod n') (mulCastHom k h a) = mulCastHom k h' (castHom hm (ZMod m') a) := by
  obtain ⟨a, rfl⟩ := intCast_surjective a
  rw [mulCastHom_intCast, map_mul, map_intCast, map_natCast, map_intCast, mulCastHom_intCast]

end ZMod
