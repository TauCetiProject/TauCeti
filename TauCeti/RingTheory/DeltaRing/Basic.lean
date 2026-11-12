/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.FieldTheory.Finite.Basic

/-!
# δ-rings

Fix a prime `p`. A `δ`-ring is a commutative ring `A` with a map `δ : A → A` such that
`δ 0 = δ 1 = 0`, `δ (x * y) = x ^ p * δ y + y ^ p * δ x + p * δ x * δ y` and
`δ (x + y) = δ x + δ y + (x ^ p + y ^ p - (x + y) ^ p) / p`. The last quotient is the integral
polynomial `DeltaRing.addCorrection p x y`, a sum over the binomial coefficients `p.choose i`
with `0 < i < p`, each divided by `p`.

The map `φ x = x ^ p + p * δ x` is a ring endomorphism lifting Frobenius modulo `p`
(`DeltaRing.frobenius`). Conversely, on a ring in which `p` is a nonzerodivisor, a ring
endomorphism lifting Frobenius modulo `p` determines a unique `δ`-structure with that Frobenius
(`DeltaRing.ofFrobeniusLift` and `DeltaRing.ext_of_frobenius`). In particular `ℤ` has a unique
`δ`-structure, with `δ n = (n - n ^ p) / p`.

## Main definitions

* `TauCeti.DeltaRing.addCorrection`: the polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`.
* `TauCeti.DeltaRing`: a `δ`-structure on a commutative ring.
* `TauCeti.DeltaRing.frobenius`: the Frobenius lift `x ↦ x ^ p + p * δ x`.
* `TauCeti.DeltaRing.ofFrobeniusLift`: the `δ`-structure of a Frobenius lift on a ring in which
  `p` is a nonzerodivisor.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  §2.1, Definition 2.1, Remarks 2.2 and 2.4.
-/

@[expose] public section

namespace TauCeti

namespace DeltaRing

variable (p : ℕ) {A : Type*} [CommRing A]

/-- The integral polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`, written as
`-∑_{0 < i < p} (p.choose i / p) x ^ i y ^ (p - i)`. For prime `p` it satisfies
`p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p` (`natCast_mul_addCorrection`). -/
def addCorrection (x y : A) : A :=
  ∑ i ∈ Finset.Ioo 0 p, -(((p.choose i / p : ℕ) : A) * x ^ i * y ^ (p - i))

variable {p}

theorem natCast_mul_addCorrection [hp : Fact p.Prime] (x y : A) :
    (p : A) * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p := by
  have hp0 : 0 < p := hp.out.pos
  have hsum : (x + y) ^ p = x ^ p + y ^ p +
      ∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * (p.choose i : A) := by
    rw [add_pow, Finset.range_eq_Ico, Finset.sum_Ico_succ_top (Nat.zero_le p),
      ← Finset.Ioo_insert_left hp0, Finset.sum_insert Finset.left_notMem_Ioo]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
      Nat.sub_self, Nat.choose_self]
    ring
  rw [hsum, addCorrection, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.Ioo 0 p, (p : A) * -(((p.choose i / p : ℕ) : A) * x ^ i *
      y ^ (p - i)) = -(x ^ i * y ^ (p - i) * (p.choose i : A)) := by
    intro i hi
    rw [Finset.mem_Ioo] at hi
    have hdvd : p ∣ p.choose i := hp.out.dvd_choose_self hi.1.ne' hi.2
    have hcast : (p : A) * ((p.choose i / p : ℕ) : A) = (p.choose i : A) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    linear_combination (-(x ^ i * y ^ (p - i))) * hcast
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  ring

end DeltaRing

/-- A `δ`-structure on a commutative ring `A` for the prime `p` ([BS22], Definition 2.1): a map
`delta` with `delta 0 = delta 1 = 0`, the product rule
`delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y` and the sum rule
`delta (x + y) = delta x + delta y + (x ^ p + y ^ p - (x + y) ^ p) / p`, where the last quotient
is the polynomial `DeltaRing.addCorrection p x y`.

The prime `p` is a parameter rather than a hypothesis of the class; the results that need its
primality assume `Fact p.Prime`. -/
@[ext]
class DeltaRing (p : ℕ) (A : Type*) [CommRing A] where
  /-- The `δ`-operation. -/
  delta : A → A
  delta_zero : delta 0 = 0
  delta_one : delta 1 = 0
  delta_add (x y : A) : delta (x + y) = delta x + delta y + DeltaRing.addCorrection p x y
  delta_mul (x y : A) :
    delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y

namespace DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A]

attribute [simp] delta_zero delta_one

section Frobenius

variable [Fact p.Prime] [DeltaRing p A]

variable (p A) in
/-- The Frobenius lift `φ x = x ^ p + p * δ x` of a `δ`-ring, a ring endomorphism
([BS22], Remark 2.2). -/
def frobenius : A →+* A where
  toFun x := x ^ p + p * delta p x
  map_one' := by simp
  map_mul' x y := by
    simp only [delta_mul, mul_pow]
    ring
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    simp only [delta_add, mul_add, natCast_mul_addCorrection]
    ring

theorem frobenius_apply (x : A) : frobenius p A x = x ^ p + p * delta p x := rfl

theorem frobenius_sub_pow (x : A) : frobenius p A x - x ^ p = p * delta p x := by
  rw [frobenius_apply]
  ring

/-- The Frobenius of a `δ`-ring lifts the `p`-th power map modulo `p`. -/
theorem natCast_dvd_frobenius_sub_pow (x : A) : (p : A) ∣ frobenius p A x - x ^ p :=
  ⟨delta p x, frobenius_sub_pow x⟩

omit [DeltaRing p A] in
/-- On a ring in which `p` is a nonzerodivisor, a `δ`-structure is determined by its Frobenius
([BS22], Remark 2.4). -/
theorem ext_of_frobenius (hA : IsRegular (p : A)) {δ₁ δ₂ : DeltaRing p A}
    (h : ∀ x, @frobenius p A _ _ δ₁ x = @frobenius p A _ _ δ₂ x) : δ₁ = δ₂ := by
  ext x
  apply hA.left
  dsimp only
  have h₁ := @frobenius_sub_pow p A _ _ δ₁ x
  have h₂ := @frobenius_sub_pow p A _ _ δ₂ x
  rw [← h₁, ← h₂, h x]

end Frobenius

section OfFrobeniusLift

variable [hp : Fact p.Prime]

/-- The `δ`-structure of a Frobenius lift `φ` on a ring in which `p` is a nonzerodivisor
([BS22], Remark 2.4): `δ x` is the unique element with `p * δ x = φ x - x ^ p`. -/
@[instance_reducible]
noncomputable def ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) : DeltaRing p A where
  delta x := (hφ x).choose
  delta_zero := by
    apply hA.left
    change (p : A) * (hφ 0).choose = p * 0
    rw [mul_zero, ← (hφ 0).choose_spec, map_zero, zero_pow hp.out.ne_zero, sub_zero]
  delta_one := by
    apply hA.left
    change (p : A) * (hφ 1).choose = p * 0
    rw [mul_zero, ← (hφ 1).choose_spec, map_one, one_pow, sub_self]
  delta_add x y := by
    apply hA.left
    have hx := (hφ x).choose_spec
    have hy := (hφ y).choose_spec
    have hxy : φ x + φ y - (x + y) ^ p = p * (hφ (x + y)).choose := by
      rw [← map_add]
      exact (hφ (x + y)).choose_spec
    have hc := natCast_mul_addCorrection (p := p) x y
    dsimp only
    linear_combination -hxy + hx + hy - hc
  delta_mul x y := by
    apply hA.left
    have hx := (hφ x).choose_spec
    have hy := (hφ y).choose_spec
    have hxy : φ x * φ y - (x * y) ^ p = p * (hφ (x * y)).choose := by
      rw [← map_mul]
      exact (hφ (x * y)).choose_spec
    dsimp only
    linear_combination -hxy + φ x * hy + (y ^ p + p * (hφ y).choose) * hx

theorem natCast_mul_delta_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) (x : A) :
    (p : A) * @delta p A _ (ofFrobeniusLift hA φ hφ) x = φ x - x ^ p :=
  ((hφ x).choose_spec).symm

/-- The Frobenius of `ofFrobeniusLift hA φ hφ` is `φ`. -/
theorem frobenius_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) :
    @frobenius p A _ _ (ofFrobeniusLift hA φ hφ) = φ := by
  ext x
  rw [@frobenius_apply, natCast_mul_delta_ofFrobeniusLift]
  ring

end OfFrobeniusLift

section Int

variable [hp : Fact p.Prime]

/-- The unique `δ`-structure on `ℤ`, whose Frobenius is the identity ([BS22], Remark 2.4). -/
noncomputable instance instInt : DeltaRing p ℤ :=
  ofFrobeniusLift (A := ℤ)
    (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) (RingHom.id ℤ) fun n => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [ZMod.pow_card]

theorem frobenius_int : frobenius p ℤ = RingHom.id ℤ :=
  frobenius_ofFrobeniusLift _ _ _

theorem delta_int (n : ℤ) : delta p n = (n - n ^ p) / p := by
  have h := frobenius_sub_pow (p := p) n
  rw [frobenius_int, RingHom.id_apply] at h
  rw [h, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]

end Int

end DeltaRing

end TauCeti
