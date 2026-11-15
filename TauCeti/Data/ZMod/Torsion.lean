/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.Data.ZMod.MulCastHom

/-!
# Torsion in residue rings

For `N = m * k` with `m ≠ 0`, the elements of `ZMod N` killed by `m` are described by the
exactness at `ZMod N` of `ZMod m → ZMod N → ZMod k`, multiplication by `k` followed by reduction
(`ZMod.exact_mulCastHom_castHom` in `TauCeti.Data.ZMod.MulCastHom`). Such an element
is exactly the class of an integer multiple of `k`
(`ZMod.natCast_mul_eq_zero_iff_exists_eq_mul`). It is exactly one whose reduction modulo `k`
vanishes (`ZMod.natCast_mul_eq_zero_iff`). For `N ≠ 0`, it is exactly one whose representative is
divisible by `k` (`ZMod.dvd_val_iff_natCast_mul_eq_zero`).

Consequently, for nonzero `m` and `n`, the subgroup of `ZMod (m * n)` killed by `m` is additively
equivalent to `ZMod m`, by multiplication by `n` (`TauCeti.zmodTorsionByEquiv`). With `m = p` and
`n = p ^ k` this counts the elements killed by `p` in the prime-power cyclic factor
`ZMod (p * p ^ k)`, as required by the rank-two finite-abelian criterion.

In prime-power moduli, for every nonzero `p`, an element of `ZMod (p ^ (n + 1))` is killed by `p`
exactly when it is the reduction of a multiple of `p ^ n`
(`ZMod.zsmul_eq_zero_iff_exists_eq_pow_mul`). In the first nontrivial case, an element of
`ZMod (p ^ 2)` is killed by `p` exactly when it reduces to `0` modulo `p`
(`ZMod.cast_eq_zero_iff_natCast_mul_eq_zero`); this is what prevents a character of order `p`
from lifting modulo `p ^ 2`. More generally, for a prime `p` and `c ≠ 0`, multiplying by `c` in
`ZMod (p ^ (n + v))` with `c.factorization p ≤ v` determines reduction modulo `p ^ n`
(`ZMod.natCast_mul_eq_zero_iff_castHom_pow_eq_zero` and
`ZMod.castHom_pow_eq_of_natCast_mul_eq`).
-/

public section

namespace ZMod

/-- For `N = m * k` with `m ≠ 0`, an element of `ZMod N` is killed by `m` exactly when it is the
class of an integer multiple of `k`. -/
theorem natCast_mul_eq_zero_iff_exists_eq_mul {m k N : ℕ} (h : m * k = N) (hm : m ≠ 0)
    {x : ZMod N} : (m : ZMod N) * x = 0 ↔ ∃ t : ℤ, x = ((k * t : ℤ) : ZMod N) := by
  rw [natCast_mul_eq_zero_iff k h hm, exact_mulCastHom_castHom k h x, Set.mem_range,
    intCast_surjective.exists]
  exact exists_congr fun t ↦ by
    rw [mulCastHom_intCast, Int.cast_mul, Int.cast_natCast, mul_comm, eq_comm]

/-- For `N = m * k` with `N ≠ 0`, the representative of an element of `ZMod N` is divisible by `k`
exactly when the element is killed by `m`. -/
theorem dvd_val_iff_natCast_mul_eq_zero {m k N : ℕ} [NeZero N] (h : m * k = N) (x : ZMod N) :
    k ∣ x.val ↔ (m : ZMod N) * x = 0 := by
  have hm : m ≠ 0 := left_ne_zero_of_mul (h ▸ NeZero.ne N)
  rw [natCast_mul_eq_zero_iff k h hm, castHom_apply, cast_eq_val, natCast_eq_zero_iff]

/-- An element of `ZMod (p ^ 2)` reduces to `0` modulo `p` exactly when it is killed by `p`. -/
theorem cast_eq_zero_iff_natCast_mul_eq_zero {p : ℕ} [NeZero p] {u : ZMod (p ^ 2)} :
    (ZMod.cast u : ZMod p) = 0 ↔ (p : ZMod (p ^ 2)) * u = 0 := by
  rw [natCast_mul_eq_zero_iff p (sq p).symm (NeZero.ne p), castHom_apply]

/-- An element of `ZMod (p ^ (n + 1))` is killed by `p` exactly when it is the reduction of a
multiple of `p ^ n`. -/
theorem zsmul_eq_zero_iff_exists_eq_pow_mul {p n : ℕ} [NeZero p] {x : ZMod (p ^ (n + 1))} :
    (p : ℤ) • x = 0 ↔ ∃ t : ℤ, x = (((p : ℤ) ^ n * t : ℤ) : ZMod (p ^ (n + 1))) := by
  rw [zsmul_eq_mul, Int.cast_natCast,
    natCast_mul_eq_zero_iff_exists_eq_mul (pow_succ' p n).symm (NeZero.ne p), Nat.cast_pow]

/-- Multiplying by `m * u` with `u` coprime to `N = m * k` kills `x : ZMod N` exactly when `x`
reduces to `0` modulo `k`. -/
theorem natCast_mul_eq_zero_iff_of_coprime {m u k N : ℕ} (h : m * k = N) (hm : m ≠ 0)
    (hu : Nat.Coprime u N) (x : ZMod N) :
    ((m * u : ℕ) : ZMod N) * x = 0 ↔ castHom (h ▸ dvd_mul_left k m) (ZMod k) x = 0 := by
  have hunit : IsUnit (u : ZMod N) := by
    rw [← coe_unitOfCoprime u hu]
    exact Units.isUnit _
  rw [Nat.cast_mul, mul_comm (m : ZMod N) (u : ZMod N), mul_assoc, hunit.mul_right_eq_zero,
    natCast_mul_eq_zero_iff k h hm]

/-- For a prime `p` and `c ≠ 0`, an element of `ZMod (p ^ (n + c.factorization p))` is killed by
`c` if and only if its reduction modulo `p ^ n` vanishes. -/
theorem natCast_mul_eq_zero_iff_castHom_pow_eq_zero {p c n : ℕ} (hp : p.Prime) (hc : c ≠ 0)
    (z : ZMod (p ^ (n + c.factorization p))) :
    (c : ZMod (p ^ (n + c.factorization p))) * z = 0 ↔
      castHom (pow_dvd_pow p (Nat.le_add_right n _)) (ZMod (p ^ n)) z = 0 := by
  let e := c.factorization p
  have hfact : p ^ e * (c / p ^ e) = c := Nat.ordProj_mul_ordCompl_eq_self c p
  have hcop : Nat.Coprime (c / p ^ e) (p ^ (n + e)) :=
    (Nat.coprime_ordCompl hp hc).symm.pow_right (n + e)
  have hpow : p ^ e * p ^ n = p ^ (n + e) := by rw [← pow_add, add_comm]
  have hc' : (c : ZMod (p ^ (n + e))) = ((p ^ e * (c / p ^ e) : ℕ) : ZMod (p ^ (n + e))) :=
    congrArg Nat.cast hfact.symm
  rw [hc', natCast_mul_eq_zero_iff_of_coprime hpow (pow_ne_zero e hp.ne_zero) hcop]

/-- **Prime-power cancellation in `ZMod`.** If `p` is prime, `c ≠ 0`, and `c.factorization p ≤ v`,
then `(c : ZMod (p ^ (n + v))) * x = (c : ZMod (p ^ (n + v))) * y` implies that `x` and `y` have
the same reduction in `ZMod (p ^ n)`. -/
theorem castHom_pow_eq_of_natCast_mul_eq {p c n v : ℕ} (hp : p.Prime) (hc : c ≠ 0)
    (hv : c.factorization p ≤ v) {x y : ZMod (p ^ (n + v))}
    (hxy : (c : ZMod (p ^ (n + v))) * x = (c : ZMod (p ^ (n + v))) * y) :
    castHom (pow_dvd_pow p (Nat.le_add_right n v)) (ZMod (p ^ n)) x =
      castHom (pow_dvd_pow p (Nat.le_add_right n v)) (ZMod (p ^ n)) y := by
  set e := c.factorization p
  have heq : n + v = (n + (v - e)) + e := by omega
  have hsub : (c : ZMod (p ^ (n + v))) * (x - y) = 0 := by rw [mul_sub, sub_eq_zero, hxy]
  let φ : ZMod (p ^ (n + v)) ≃+* ZMod (p ^ ((n + (v - e)) + e)) := ZMod.ringEquivCongr (by rw [heq])
  have hφ : (c : ZMod (p ^ ((n + (v - e)) + e))) * φ (x - y) = 0 := by
    rw [← map_natCast φ c, ← map_mul, hsub, map_zero]
  have hzero : castHom (pow_dvd_pow p (Nat.le_add_right (n + (v - e)) e))
      (ZMod (p ^ (n + (v - e)))) (φ (x - y)) = 0 :=
    (natCast_mul_eq_zero_iff_castHom_pow_eq_zero hp hc (φ (x - y))).1 hφ
  have hcast : castHom (pow_dvd_pow p (Nat.le_add_right n v)) (ZMod (p ^ n)) (x - y) =
      castHom (pow_dvd_pow p (Nat.le_add_right n (v - e))) (ZMod (p ^ n))
        (castHom (pow_dvd_pow p (Nat.le_add_right (n + (v - e)) e))
          (ZMod (p ^ (n + (v - e)))) (φ (x - y))) := by
    have hcomp :
        (castHom (pow_dvd_pow p (Nat.le_add_right n (v - e))) (ZMod (p ^ n))).comp
          ((castHom (pow_dvd_pow p (Nat.le_add_right (n + (v - e)) e))
            (ZMod (p ^ (n + (v - e))))).comp φ.toRingHom) =
          castHom (pow_dvd_pow p (Nat.le_add_right n v)) (ZMod (p ^ n)) :=
      Subsingleton.elim _ _
    exact (RingHom.congr_fun hcomp (x - y)).symm
  rw [← sub_eq_zero, ← map_sub, hcast, hzero, map_zero]

end ZMod

namespace TauCeti

/-- The homomorphism underlying `zmodTorsionByEquiv`: multiplication by `n`, `ZMod.mulCastHom`,
with codomain restricted to the `m`-torsion of `ZMod (m * n)`. -/
private def zmodTorsionByEquivHom (m n : ℕ) :
    ZMod m →+ AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ) :=
  (ZMod.mulCastHom n rfl).codRestrict _ fun x ↦ by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      map_zero]

/-- An element of the `m`-torsion of `ZMod (m * n)` is killed by multiplication by `m`. -/
private theorem natCast_mul_coe_eq_zero {m n : ℕ}
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) : (m : ZMod (m * n)) * y = 0 := by
  rw [← nsmul_eq_mul]
  exact AddSubgroup.torsionBy.nsmul y |> congrArg Subtype.val

/-- Multiplication by `n` is a bijection from `ZMod m` onto the `m`-torsion of `ZMod (m * n)`. -/
private theorem zmodTorsionByEquivHom_bijective (m n : ℕ) [NeZero m] [NeZero n] :
    Function.Bijective (zmodTorsionByEquivHom m n) := by
  refine ⟨fun a b hab ↦ ZMod.mulCastHom_injective n rfl (NeZero.ne n) (congrArg Subtype.val hab),
    fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := (ZMod.exact_mulCastHom_castHom n rfl y.1).1 <|
    (ZMod.natCast_mul_eq_zero_iff n rfl (NeZero.ne m) y.1).1 (natCast_mul_coe_eq_zero y)
  exact ⟨x, Subtype.ext hx⟩

/-- For nonzero `m` and `n`, the subgroup of `ZMod (m * n)` killed by `m` is additively
equivalent to `ZMod m`, by multiplication by `n`. -/
noncomputable def zmodTorsionByEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ZMod m ≃+ AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ) :=
  AddEquiv.ofBijective (zmodTorsionByEquivHom m n) (zmodTorsionByEquivHom_bijective m n)

/-- `zmodTorsionByEquiv` sends a residue to its multiple by `n` in the ambient residue ring. -/
@[simp]
theorem zmodTorsionByEquiv_apply_coe (m n : ℕ) [NeZero m] [NeZero n] (x : ZMod m) :
    (zmodTorsionByEquiv m n x : ZMod (m * n)) = (x.val * n : ℕ) := by
  rw [Nat.cast_mul, ← ZMod.cast_eq_val, ← ZMod.mulCastHom_apply, zmodTorsionByEquiv,
    AddEquiv.ofBijective_apply, zmodTorsionByEquivHom, AddMonoidHom.codRestrict_apply]

/-- The inverse of `zmodTorsionByEquiv` divides the representative by `n`. -/
@[simp]
theorem zmodTorsionByEquiv_symm_apply (m n : ℕ) [NeZero m] [NeZero n]
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) :
    (zmodTorsionByEquiv m n).symm y = ((y.1.val / n : ℕ) : ZMod m) := by
  refine (AddEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
  rw [zmodTorsionByEquiv_apply_coe, ZMod.val_natCast, ← Nat.mul_mod_mul_right, ZMod.natCast_mod,
    Nat.div_mul_cancel ((ZMod.dvd_val_iff_natCast_mul_eq_zero rfl y.1).2
      (natCast_mul_coe_eq_zero y)), ZMod.natCast_zmod_val]

/-- Equality with the image of a chosen residue under `zmodTorsionByEquiv` is characterized in
the ambient residue ring. -/
theorem zmodTorsionByEquiv_apply_eq_iff (m n : ℕ) [NeZero m] [NeZero n] (x : ZMod m)
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) :
    zmodTorsionByEquiv m n x = y ↔ (x.val * n : ℕ) = (y : ZMod (m * n)) := by
  rw [Subtype.ext_iff, zmodTorsionByEquiv_apply_coe]

/-- The inverse picks the unique residue whose multiple by `n` is the given torsion point. -/
theorem zmodTorsionByEquiv_symm_apply_eq_iff (m n : ℕ) [NeZero m] [NeZero n]
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) (x : ZMod m) :
    (zmodTorsionByEquiv m n).symm y = x ↔ (x.val * n : ℕ) = (y : ZMod (m * n)) := by
  rw [AddEquiv.symm_apply_eq, eq_comm, zmodTorsionByEquiv_apply_eq_iff]

end TauCeti

end
