/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod
import TauCeti.GroupTheory.Torsion

/-!
# Finite subgroups of `GL n` inject modulo an odd prime

Let `ℓ` be an odd prime and `R` a commutative ring in which `ℓ` is a non-zero-divisor and which is
`ℓ`-adically separated, such as `ℤ` or `ℤ_[ℓ]`. An invertible matrix over `R` that is congruent
to `1` modulo `ℓ` and is not `1` has infinite order. Equivalently, the kernel of reduction modulo
`ℓ` on `GL n R` is torsion-free, so reduction modulo `ℓ` is injective on every finite subgroup of
`GL n R`. For `R = ℤ` and `ℓ = 3`, every finite subgroup of `GL n ℤ` embeds into `GL n (ZMod 3)`.
This bounds, for instance, the finite image of a Galois group acting on a lattice of rank `n` by
`|GL n (ZMod 3)|`.

The prime `2` is excluded: `-1 ∈ GL 1 ℤ` reduces to `1` modulo `2` and has order `2`
(`Matrix.GeneralLinearGroup.not_isMulTorsionFree_ker_map_intCast_two`).

## Main results

* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`: if `φ : R →+* S` has kernel contained in
  `ℓ R`, the kernel of `GL n R → GL n S` is torsion-free.
* `Matrix.GeneralLinearGroup.injective_domRestrict_map`: under the same hypotheses,
  `GL n R → GL n S` is injective on every finite subgroup.
* `Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map_toZMod`,
  `Matrix.GeneralLinearGroup.injective_domRestrict_map_toZMod`: the first congruence subgroup of
  `GL n ℤ_[ℓ]` is torsion-free, and reduction `GL n ℤ_[ℓ] → GL n (ZMod ℓ)` is injective on every
  finite subgroup.
* `Matrix.GeneralLinearGroup.injective_domRestrict_map_intCast_three`,
  `Matrix.GeneralLinearGroup.natCard_le_natCard_zmod_three`: reduction `GL n ℤ → GL n (ZMod 3)` is
  injective on every finite subgroup, so a finite subgroup of `GL n ℤ` has at most
  `|GL n (ZMod 3)|` elements.

## References

* H. Minkowski, *Zur Theorie der positiven quadratischen Formen*, J. Reine Angew. Math. 101 (1887),
  196–202.
* D. Huybrechts, *Lectures on K3 surfaces*, Cambridge Stud. Adv. Math. 158, Chapter 17, proof of
  Lemma 2.6.
-/

public section

open Polynomial

namespace Matrix.GeneralLinearGroup

section Expansion

variable {A : Type*} [Ring A]

/-- The binomial expansion of `(1 + x) ^ q` to second order, with the remainder divisible by
`x ^ 3`. -/
private theorem exists_one_add_pow_eq (x : A) (q : ℕ) :
    ∃ w : A, (1 + x) ^ q = 1 + q * x + q.choose 2 * x ^ 2 + x ^ 3 * w := by
  obtain ⟨W, hW⟩ : (X : ℤ[X]) ^ 3 ∣
      (X + 1) ^ q - 1 - (q : ℤ[X]) * X - (q.choose 2 : ℤ[X]) * X ^ 2 := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp [coeff_X_add_one_pow, coeff_one, coeff_X, coeff_X_pow]
  refine ⟨aeval x W, ?_⟩
  have h := congrArg (aeval x) hW
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_natCast, aeval_X] at h
  rw [add_comm 1 x, ← sub_eq_zero, ← sub_eq_zero.mpr h]
  abel

end Expansion

section Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The inductive step.** Let `ℓ` be odd, `q = ℓ` or `q` prime to `ℓ`, and `ℓ` a non-zero-divisor
on `A`. If `(1 + ℓ ^ (k + 1) y) ^ q = 1`, then `y` is divisible by `ℓ`. -/
private theorem exists_eq_smul_of_one_add_pow_eq_one {ℓ q k : ℕ} (hodd : Odd ℓ)
    (hqℓ : q = ℓ ∨ q.Coprime ℓ) (hreg : IsSMulRegular A (ℓ : R)) {y : A}
    (h : (1 + (ℓ : R) ^ (k + 1) • y) ^ q = 1) : ∃ z : A, y = (ℓ : R) • z := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq ((ℓ : R) ^ (k + 1) • y) q
  rw [h, eq_comm, add_assoc, add_assoc, add_eq_left] at hw
  set c : R := (ℓ : R)
  -- the expansion of `(1 + c ^ (k + 1) • y) ^ q = 1`, divided by `c ^ (k + 1)`
  have hE : (q : A) * y + c ^ (k + 1) • ((q.choose 2 : A) * y ^ 2) +
      c ^ (2 * k + 2) • (y ^ 3 * w) = 0 := by
    refine hreg.pow (k + 1) ?_
    dsimp only
    rw [smul_zero, ← hw]
    simp only [smul_pow, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, ← pow_add, ← pow_mul,
      add_assoc]
    ring_nf
  have hcz (z : A) : (ℓ : A) * z = c • z := by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rcases hqℓ with rfl | hcop
  · -- for `q = ℓ = 2 m + 1`, the binomial coefficient `q.choose 2 = q m` is divisible by `ℓ`
    obtain ⟨m, hm⟩ := hodd
    have hC : q.choose 2 = q * m := by
      rw [Nat.choose_two_right]
      refine Nat.div_eq_of_eq_mul_left two_pos ?_
      rw [hm, Nat.add_sub_cancel]
      ring
    rw [hcz, hC, Nat.cast_mul, mul_assoc, hcz] at hE
    refine ⟨-(c ^ k • ((m : A) * y ^ 2) + c ^ (2 * k) • (y ^ 3 * w)), sub_eq_zero.mp ?_⟩
    refine hreg ?_
    dsimp only
    rw [smul_zero]
    linear_combination (norm := module) hE
  · -- for `q` prime to `ℓ`, `q y` is divisible by `ℓ`, hence so is `y`
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    refine ⟨u • -(c ^ k • ((q.choose 2 : A) * y ^ 2) + c ^ (2 * k + 1) • (y ^ 3 * w)) + v • y, ?_⟩
    have hy : y = u • ((q : A) * y) + v • ((ℓ : A) * y) := by
      have h1 : ((u * q + v * ℓ : ℤ) : A) = 1 := by rw [huv, Int.cast_one]
      push_cast at h1
      rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, h1, one_mul]
    calc y = u • ((q : A) * y) + v • ((ℓ : A) * y) := hy
      _ = _ := by
        rw [hcz]
        linear_combination (norm := module) u • hE

/-- An element `1 + ℓ y` of prime order `q` in an `ℓ`-torsion-free, `ℓ`-adically separated
`R`-algebra, for `ℓ` an odd prime, has `ℓ y = 0`. -/
private theorem smul_eq_zero_of_one_add_smul_pow_eq_one {ℓ q : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hq : q.Prime) (hreg : IsSMulRegular A (ℓ : R))
    (hsep : ∀ x : A, (∀ k : ℕ, ∃ z : A, x = (ℓ : R) ^ k • z) → x = 0) {y : A}
    (h : (1 + (ℓ : R) • y) ^ q = 1) : (ℓ : R) • y = 0 := by
  have hqℓ : q = ℓ ∨ q.Coprime ℓ := by
    rw [Nat.coprime_primes hq hℓ]
    exact eq_or_ne q ℓ
  -- `ℓ • y` is divisible by every power of `ℓ`
  have hdiv (k : ℕ) : ∃ z : A, (ℓ : R) • y = (ℓ : R) ^ (k + 1) • z := by
    induction k with
    | zero => exact ⟨y, by rw [zero_add, pow_one]⟩
    | succ k ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨z', rfl⟩ := exists_eq_smul_of_one_add_pow_eq_one hodd hqℓ hreg (hz ▸ h)
      exact ⟨z', by rw [hz, smul_smul, ← pow_succ]⟩
  refine hsep _ fun k ↦ ?_
  obtain ⟨z, hz⟩ := hdiv k
  exact ⟨(ℓ : R) • z, by rw [hz, smul_smul, ← pow_succ]⟩

end Algebra

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- **The congruence kernel is torsion-free.** Let `ℓ` be an odd prime and `R` a commutative ring
in which `ℓ` is a non-zero-divisor and which is `ℓ`-adically separated. For a ring hom `φ : R →+* S`
whose kernel lies in `ℓ R`, the kernel of `GL n R → GL n S` is torsion-free: an invertible matrix
congruent to `1` modulo `ker φ` and of finite order is `1`. -/
theorem isMulTorsionFree_ker_map {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {(ℓ : R)}) :
    IsMulTorsionFree (map (n := n) φ).ker := by
  rw [isMulTorsionFree_iff_forall_not_prime_orderOf]
  rintro ⟨g, hg⟩ hq
  rw [Subgroup.orderOf_mk] at hq
  -- the entries of `g - 1` are multiples of `ℓ`
  have hgφ : (g : Matrix n n R).map φ = 1 := by
    simpa [Units.ext_iff] using MonoidHom.mem_ker.mp hg
  have hdvd (i j : n) : ∃ r : R, r * ℓ = (g - 1 : Matrix n n R) i j := by
    refine Ideal.mem_span_singleton'.mp (hφ (RingHom.mem_ker.mpr ?_))
    have h0 : φ.mapMatrix ((g : Matrix n n R) - 1) = 0 := by
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hgφ, sub_self]
    simpa using congrFun (congrFun h0 i) j
  choose Y hY using hdvd
  have hgY : (g : Matrix n n R) = 1 + (ℓ : R) • Matrix.of Y := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_comm, hY,
      Matrix.sub_apply, add_sub_cancel]
  have hpow : (1 + (ℓ : R) • Matrix.of Y) ^ orderOf g = 1 := by
    rw [← hgY, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  -- the matrix `ℓ Y` vanishes, so `g = 1`
  have hsepM (x : Matrix n n R) (hx : ∀ k : ℕ, ∃ z : Matrix n n R, x = (ℓ : R) ^ k • z) :
      x = 0 := by
    ext i j
    refine hsep.haus' _ fun k ↦ ?_
    obtain ⟨z, rfl⟩ := hx k
    rw [SModEq.zero, Matrix.smul_apply]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)
      Submodule.mem_top
  have h0 := smul_eq_zero_of_one_add_smul_pow_eq_one hℓ hodd hq hreg.matrix hsepM hpow
  rw [h0, add_zero, ← Units.val_one, Units.val_inj] at hgY
  rw [hgY, orderOf_one] at hq
  exact Nat.not_prime_one hq

/-- **Reduction is injective on finite subgroups.** Under the hypotheses of
`Matrix.GeneralLinearGroup.isMulTorsionFree_ker_map`, the map `GL n R → GL n S` induced by `φ` is
injective on every finite subgroup of `GL n R`. -/
theorem injective_domRestrict_map {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hreg : IsSMulRegular R (ℓ : R)) (hsep : IsHausdorff (Ideal.span {(ℓ : R)}) R) (φ : R →+* S)
    (hφ : RingHom.ker φ ≤ Ideal.span {(ℓ : R)}) (G : Subgroup (GL n R)) [Finite G] :
    Function.Injective ((map φ).domRestrict G) :=
  have := isMulTorsionFree_ker_map (n := n) hℓ hodd hreg hsep φ hφ
  (map φ).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **The first congruence subgroup of `GL n ℤ_[p]` is torsion-free** for an odd prime `p`: the
kernel of reduction `GL n ℤ_[p] → GL n (ZMod p)` has no nontrivial element of finite order. -/
theorem isMulTorsionFree_ker_map_toZMod (hp : Odd p) :
    IsMulTorsionFree (map (n := n) (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).ker :=
  isMulTorsionFree_ker_map Fact.out hp (IsSMulRegular.of_ne_zero (by exact_mod_cast
    (Fact.out : p.Prime).ne_zero)) (PadicInt.maximalIdeal_eq_span_p (p := p) ▸ inferInstance) _
    (by rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p])

/-- **Finite subgroups of `GL n ℤ_[p]` inject modulo `p`** for an odd prime `p`: reduction
`GL n ℤ_[p] → GL n (ZMod p)` is injective on every finite subgroup. -/
theorem injective_domRestrict_map_toZMod (hp : Odd p) (G : Subgroup (GL n ℤ_[p])) [Finite G] :
    Function.Injective ((map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).domRestrict G) :=
  have := isMulTorsionFree_ker_map_toZMod (n := n) hp
  (map _).injective_domRestrict_of_isMulTorsion isMulTorsion_of_finite

end Padic

section Int

/-- **Finite subgroups of `GL n ℤ` inject modulo `3`**: reduction `GL n ℤ → GL n (ZMod 3)` is
injective on every finite subgroup. -/
theorem injective_domRestrict_map_intCast_three (G : Subgroup (GL n ℤ)) [Finite G] :
    Function.Injective ((map (Int.castRingHom (ZMod 3))).domRestrict G) :=
  injective_domRestrict_map (ℓ := 3) Nat.prime_three (by decide) (.of_ne_zero (by norm_num))
    (.of_isDomain _ (by norm_num [Ideal.span_singleton_eq_top, Int.isUnit_iff])) _
    (ZMod.ker_intCastRingHom 3).le G

/-- A finite subgroup of `GL n ℤ` has at most `|GL n (ZMod 3)|` elements, since it embeds into
`GL n (ZMod 3)` by reduction. -/
theorem natCard_le_natCard_zmod_three {G : Subgroup (GL n ℤ)} [Finite G] :
    Nat.card G ≤ Nat.card (GL n (ZMod 3)) :=
  Nat.card_le_card_of_injective _ (injective_domRestrict_map_intCast_three G)

/-- Oddness is needed: the kernel of `GL n ℤ → GL n (ZMod 2)` contains `-1`, of order `2`, as soon
as `n` is nonempty. -/
theorem not_isMulTorsionFree_ker_map_intCast_two [Nonempty n] :
    ¬IsMulTorsionFree (map (n := n) (Int.castRingHom (ZMod 2))).ker := by
  rw [not_isMulTorsionFree_iff_isOfFinOrder]
  refine ⟨⟨-1, ?_⟩, ?_, isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by ext1; simp⟩⟩
  · rw [MonoidHom.mem_ker]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro h
    have := congrArg (fun g : (map (n := n) (Int.castRingHom (ZMod 2))).ker ↦
      ((g : GL n ℤ) : Matrix n n ℤ) (Classical.arbitrary n) (Classical.arbitrary n)) h
    simp at this

end Int

end Matrix.GeneralLinearGroup
