/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.Lie.Restricted.Basic
public import TauCeti.RingTheory.Derivation.BaseChange
public import TauCeti.RingTheory.Derivation.Localization
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Init
import TauCeti.Algebra.Lie.AdjointAction.Frobenius
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Derivation.Basic

/-!
# The `p`-th power of a derivation and restricted Lie algebra structure

Over a commutative semiring `A` of prime characteristic `p`, the `p`-th iterate `D^[p]` of an
`R`-derivation `D : Derivation R A A` is again a derivation (`Derivation.pPow`), since the general
Leibniz rule expands `D^[p] (a * b)` with binomial coefficients `p.choose k` that vanish modulo `p`
for `0 < k < p` (`Derivation.iterate_leibniz`).

Unlike the base-ring action `c • D` (`c : R`), where `(c • D).pPow p = c ^ p • D.pPow p`
(`Derivation.pPow_smul_base`), the `A`-module action satisfies **Hochschild's formula** (also due to
Deligne; Katz 1970, Proposition 5.3):

`(a • D).pPow p = a ^ p • D.pPow p + ((⇑(a • D))^[p - 1] a) • D` (`Derivation.pPow_smul`).

In particular, whenever `D a = 0`, the correction term vanishes
(`Derivation.pPow_smul_of_apply_eq_zero`). The proof works over arbitrary commutative semirings
(no subtraction is needed) by expanding `(a • D)^[n]` via recursive coefficients, lifting `D` to
`A[X]`, and reading off the constant term of `((C a • D').pPow p) (X ^ m)` for `2 ≤ m < p`, where
`D' = coeffDer D + d/dX`.

When `R` and `A` are commutative rings of characteristic `p`, the `p`-th power equips
`Derivation R A A` with a canonical restricted Lie algebra structure
(`Derivation.instRestrictedLieAlgebra`), and the embedding `Derivation.toEndRestrictedLieHom` into
`Module.End R A` is an injective morphism of restricted Lie algebras.

We also establish compatibility of `Derivation.pPow` with base change (`Derivation.baseChange_pPow`)
and localization (`Derivation.extendOfIsLocalization_pPow`), and construct the dual coordinate
derivations `TauCeti.kaehlerDualDer` associated to a basis of `Ω[A⁄R]` of the form `d(sᵢ)`:
they pairwise commute (`TauCeti.lie_kaehlerDualDer`), determine derivations on the coordinates
(`Derivation.eq_of_apply_eq_of_kaehlerBasis`), and satisfy `(kaehlerDualDer b i).pPow p = 0` in
prime characteristic `p` (`TauCeti.pPow_kaehlerDualDer`).

## Main definitions

* `Derivation.pPow`: the `p`-th power `D^[p]` of a derivation, packaged as a derivation.
* `Derivation.toEndLieHom`: the canonical Lie algebra embedding
  `Derivation R A A →ₗ⁅R⁆ Module.End R A`.
* `Derivation.instRestrictedLieAlgebra`: the restricted Lie algebra structure on `Derivation R A A`.
* `Derivation.toEndRestrictedLieHom`: the restricted Lie algebra embedding
  `Derivation R A A → Module.End R A`.
* `TauCeti.kaehlerDualDer`: the coordinate derivation dual to a basis vector of `Ω[A⁄R]`.

## Main results

* `Derivation.iterate_leibniz`: in prime characteristic `p`, `D^[p]` obeys the Leibniz rule.
* `Derivation.pPow_smul`: Hochschild's formula for `(a • D).pPow p`.
* `Derivation.pPow_smul_of_apply_eq_zero`: `(a • D).pPow p = a ^ p • D.pPow p` when `D a = 0`.
* `Derivation.pPow_smul_base`: `(c • D).pPow p = c ^ p • D.pPow p` for `c : R`.
* `Derivation.baseChange_pPow`: compatibility of `pPow` with `Derivation.baseChange`.
* `Derivation.ad_pPow`: `ad (D.pPow p) = (ad D) ^ p` on derivations.
* `Derivation.pPow_add`: Jacobson's formula for `(D + E).pPow p`.
* `Derivation.extendOfIsLocalization_pPow`: compatibility of `pPow` with
  `Derivation.extendOfIsLocalization`.
* `Derivation.eq_of_apply_eq_of_kaehlerBasis`: derivations agreeing on coordinates of a basis of
  `Ω[A⁄R]` are equal.
* `TauCeti.lie_kaehlerDualDer` and `TauCeti.pPow_kaehlerDualDer`: dual coordinate derivations
  commute and have zero `p`-th power.

## References

* G. Hochschild, *Simple algebras with purely inseparable splitting fields of exponent 1*,
  Trans. Amer. Math. Soc. **79** (1955), 477–489.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: Applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), §5 (5.0, Proposition 5.3).
-/

public section

open scoped Nat

namespace Derivation

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- In prime characteristic `p`, the `p`-th iterate of a derivation satisfies the Leibniz rule:
`D^[p] (a * b) = a * D^[p] b + b * D^[p] a`. -/
theorem iterate_leibniz (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] (a b : A) :
    D^[p] (a * b) = a * D^[p] b + b * D^[p] a := by
  have hp : p.Prime := Fact.out
  rw [D.iterate_apply_mul p a b, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => p.choose i • (D^[i] a * D^[j] b)) p]
  rw [Finset.sum_range_succ, Nat.choose_self, one_smul, Nat.sub_self, Function.iterate_zero_apply,
    mul_comm (D^[p] a) b]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp.pos)]
  · simp [Nat.choose_zero_right, add_comm]
  · intro k hk hk0
    have hkp : k < p := Finset.mem_range.mp hk
    obtain ⟨m, hm⟩ := hp.dvd_choose_self hk0 hkp
    rw [hm, mul_smul, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero A p, zero_smul]

/-- The `p`-th power `D^[p]` of a derivation `D` in prime characteristic `p`, packaged as a
derivation. -/
def pPow (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] : Derivation R A A where
  toLinearMap := D.toLinearMap ^ p
  map_one_eq_zero' := by
    have hp : p.Prime := Fact.out
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
    rw [pow_apply_eq_iterate, coeFn_coe, hp1, Function.iterate_succ_apply, map_one_eq_zero]
    exact (D.toLinearMap ^ (p - 1)).map_zero |> fun h => by
      simpa only [pow_apply_eq_iterate, coeFn_coe] using h
  leibniz' a b := by
    simp only [pow_apply_eq_iterate, coeFn_coe, smul_eq_mul]
    exact D.iterate_leibniz p a b

@[simp]
theorem pPow_apply (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) :
    D.pPow p a = D^[p] a := by
  rw [← coeFn_coe, pPow, pow_apply_eq_iterate, coeFn_coe]

@[simp]
theorem pPow_toLinearMap (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] :
    (D.pPow p).toLinearMap = D.toLinearMap ^ p :=
  (rfl)

@[simp]
theorem pPow_zero (p : ℕ) [Fact p.Prime] [CharP A p] :
    (0 : Derivation R A A).pPow p = 0 := by
  ext a
  rw [pPow_apply, zero_apply]
  have hp : p.Prime := Fact.out
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
  rw [hp1, Function.iterate_succ_apply, zero_apply]
  induction (p - 1) with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, zero_apply]

/-- Scaling by a scalar `c : R` from the base ring is `p`-homogeneous:
`(c • D).pPow p = c ^ p • D.pPow p`. -/
theorem pPow_smul_base (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] (c : R) :
    (c • D).pPow p = c ^ p • D.pPow p := by
  ext a
  rw [pPow_apply, smul_apply, pPow_apply, D.iterate_smul_apply c p a]

section Hochschild

/-- Recursive coefficients `P n k` in the expansion
`((a • D)^[n]) y = ∑ k ∈ Finset.range (n + 1), P n k * D^[k] y`. -/
private def hochschildCoeff (D : Derivation R A A) (a : A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => a * D (hochschildCoeff D a n (k + 1)) + a * hochschildCoeff D a n k

private theorem hochschildCoeff_eq_zero_of_lt (D : Derivation R A A) (a : A) :
    ∀ {n k : ℕ}, n < k → hochschildCoeff D a n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    have h1 : n < k + 1 := Nat.lt_trans (Nat.lt_of_succ_lt_succ h) (Nat.lt_succ_self k)
    have h2 : n < k := Nat.lt_of_succ_lt_succ h
    simp [hochschildCoeff, hochschildCoeff_eq_zero_of_lt D a h1,
      hochschildCoeff_eq_zero_of_lt D a h2]

private theorem hochschildCoeff_self (D : Derivation R A A) (a : A) :
    ∀ n : ℕ, hochschildCoeff D a n n = a ^ n
  | 0 => (pow_zero a).symm
  | n + 1 => by
    simp only [hochschildCoeff, hochschildCoeff_eq_zero_of_lt D a (Nat.lt_succ_self n),
      map_zero, mul_zero, zero_add, hochschildCoeff_self D a n, pow_succ']

private theorem hochschildCoeff_zero_of_pos (D : Derivation R A A) (a : A) {n : ℕ} (hn : 0 < n) :
    hochschildCoeff D a n 0 = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

private theorem map_hochschildCoeff_zero (D : Derivation R A A) (a : A) (n : ℕ) :
    D (hochschildCoeff D a n 0) = 0 := by
  cases n with
  | zero => exact D.map_one_eq_zero
  | succ m => exact map_zero D

private theorem hochschildCoeff_one (D : Derivation R A A) (a : A) :
    ∀ n : ℕ, hochschildCoeff D a (n + 1) 1 = (⇑(a • D))^[n] a
  | 0 => by simp [hochschildCoeff]
  | n + 1 => by
    rw [hochschildCoeff, hochschildCoeff_zero_of_pos D a (Nat.succ_pos n), mul_zero, add_zero,
      hochschildCoeff_one D a n, Function.iterate_succ_apply', smul_apply, smul_eq_mul]

/-- Universal expansion of `(f a • E)^[n] y` along any compatible ring homomorphism `f : A →+* B`
and derivation `E : Derivation R B B` intertwining `D` via `f`. -/
private theorem iterate_smul_eq_sum_hochschildCoeff {B : Type*} [CommSemiring B] [Algebra R B]
    (D : Derivation R A A) (E : Derivation R B B) (f : A →+* B)
    (hf : ∀ x : A, E (f x) = f (D x)) (a : A) :
    ∀ (n : ℕ) (y : B),
      (⇑(f a • E))^[n] y =
        ∑ k ∈ Finset.range (n + 1), f (hochschildCoeff D a n k) * E^[k] y
  | 0, y => by simp [hochschildCoeff]
  | n + 1, y => by
    rw [Function.iterate_succ_apply', iterate_smul_eq_sum_hochschildCoeff D E f hf a n y]
    rw [smul_apply, smul_eq_mul, map_sum, Finset.mul_sum]
    have hstep : ∀ k ∈ Finset.range (n + 1),
        f a * E (f (hochschildCoeff D a n k) * E^[k] y) =
          f (a * D (hochschildCoeff D a n k)) * E^[k] y +
            f (a * hochschildCoeff D a n k) * E^[k + 1] y := by
      intro k _
      rw [E.leibniz, smul_eq_mul, smul_eq_mul, hf, map_mul, map_mul, Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    have hsum1 : ∑ k ∈ Finset.range (n + 1),
          f (a * D (hochschildCoeff D a n k)) * E^[k] y =
        ∑ k ∈ Finset.range (n + 1),
          f (a * D (hochschildCoeff D a n (k + 1))) * E^[k + 1] y := by
      rw [Finset.sum_range_succ' (fun k => f (a * D (hochschildCoeff D a n k)) * E^[k] y) n,
        map_hochschildCoeff_zero, mul_zero, map_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ (fun k =>
        f (a * D (hochschildCoeff D a n (k + 1))) * E^[k + 1] y) n]
      rw [hochschildCoeff_eq_zero_of_lt D a (Nat.lt_succ_self n), map_zero, mul_zero, map_zero,
        zero_mul, add_zero]
    rw [hsum1, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => f (hochschildCoeff D a (n + 1) k) * E^[k] y) (n + 1)]
    rw [hochschildCoeff_zero_of_pos D a (Nat.succ_pos n), map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hochschildCoeff, map_add, add_mul]

/-- Apply a derivation `D` coefficientwise to a polynomial in `A[X]`. -/
private noncomputable def coeffMap (D : Derivation R A A) (g : Polynomial A) : Polynomial A :=
  g.sum fun n c => Polynomial.monomial n (D c)

private theorem coeff_coeffMap (D : Derivation R A A) (g : Polynomial A) (k : ℕ) :
    (coeffMap D g).coeff k = D (g.coeff k) := by
  classical
  simp only [coeffMap, Polynomial.sum_def, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k ∈ g.support
  · rw [Finset.sum_eq_single k
      (fun n _ hnk => Finsupp.single_eq_of_ne hnk.symm) (fun h => absurd hk h),
      Finsupp.single_eq_same]
  · have hg : g.coeff k = 0 := Polynomial.notMem_support_iff.mp hk
    rw [hg, map_zero, Finset.sum_eq_zero]
    intro n hn
    exact Finsupp.single_eq_of_ne (fun h => hk (h ▸ hn))

/-- The derivation on `A[X]` obtained by applying `D` coefficientwise. -/
private noncomputable def coeffDer (D : Derivation R A A) :
    Derivation R (Polynomial A) (Polynomial A) where
  toFun := coeffMap D
  map_add' g h := by
    ext k
    simp only [coeff_coeffMap, Polynomial.coeff_add, map_add]
  map_smul' r g := by
    ext k
    simp only [coeff_coeffMap, RingHom.id_apply]
    rw [Algebra.smul_def (R := R) (A := Polynomial A),
      IsScalarTower.algebraMap_apply R A (Polynomial A), Polynomial.algebraMap_eq,
      Polynomial.coeff_C_mul, Algebra.smul_def (R := R) (A := Polynomial A),
      IsScalarTower.algebraMap_apply R A (Polynomial A), Polynomial.algebraMap_eq,
      Polynomial.coeff_C_mul, coeff_coeffMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  map_one_eq_zero' := by
    ext k
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coeff_coeffMap, Polynomial.coeff_one, Polynomial.coeff_zero]
    split_ifs <;> simp
  leibniz' g h := by
    ext k
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coeff_coeffMap, Polynomial.coeff_mul, map_sum, Polynomial.coeff_add, smul_eq_mul,
      smul_eq_mul, Polynomial.coeff_mul, Polynomial.coeff_mul]
    have hterm : ∀ ij ∈ Finset.antidiagonal k,
        D (g.coeff ij.1 * h.coeff ij.2) =
          g.coeff ij.1 * (coeffMap D h).coeff ij.2 +
            h.coeff ij.2 * (coeffMap D g).coeff ij.1 := by
      intro ij _
      rw [D.leibniz, smul_eq_mul, smul_eq_mul, coeff_coeffMap, coeff_coeffMap]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun ij => ?_) (fun ij _ => rfl)
    simp [Finset.mem_antidiagonal, add_comm]

private theorem coeffDer_apply (D : Derivation R A A) (g : Polynomial A) :
    coeffDer D g = coeffMap D g :=
  rfl

/-- The ordinary derivative `d/dX` on `A[X]`, viewed as an `R`-derivation. -/
private noncomputable def polyDerivativeR : Derivation R (Polynomial A) (Polynomial A) where
  toLinearMap := Polynomial.derivative.restrictScalars R
  map_one_eq_zero' := Polynomial.derivative_one
  leibniz' g h := by
    simp only [LinearMap.restrictScalars_apply, Polynomial.derivative_mul, smul_eq_mul,
      mul_comm h, add_comm]

private theorem polyDerivativeR_apply (g : Polynomial A) :
    polyDerivativeR (R := R) g = Polynomial.derivative g :=
  rfl

/-- The lifted derivation `D' = coeffDer D + d/dX` on `A[X]`. -/
private noncomputable def polyLiftDer (D : Derivation R A A) :
    Derivation R (Polynomial A) (Polynomial A) :=
  coeffDer D + polyDerivativeR

private theorem polyLiftDer_C (D : Derivation R A A) (b : A) :
    polyLiftDer D (Polynomial.C b) = Polynomial.C (D b) := by
  ext k
  rw [polyLiftDer, add_apply, coeffDer_apply, polyDerivativeR_apply, Polynomial.derivative_C,
    add_zero, coeff_coeffMap, Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs <;> simp

private theorem iterate_polyLiftDer_X_pow (D : Derivation R A A) (m : ℕ) :
    ∀ k : ℕ, (⇑(polyLiftDer D))^[k] (Polynomial.X ^ m : Polynomial A) =
      Polynomial.derivative^[k] (Polynomial.X ^ m : Polynomial A)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_polyLiftDer_X_pow D m k,
      Function.iterate_succ_apply']
    have hcoeff : coeffDer D (Polynomial.derivative^[k] (Polynomial.X ^ m : Polynomial A)) = 0 := by
      ext n
      rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, coeffDer_apply, coeff_coeffMap,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_zero]
      split_ifs <;> simp
    rw [polyLiftDer, add_apply, hcoeff, zero_add, polyDerivativeR_apply]

/-- Over a commutative semiring `A` of prime characteristic `p`, `m !` is invertible for `m < p`,
so `x * (m ! : A) = 0` implies `x = 0`. -/
private theorem eq_zero_of_mul_factorial_eq_zero (p : ℕ) [Fact p.Prime] [CharP A p] {m : ℕ}
    (hmp : m < p) {x : A} (hx : x * (m ! : A) = 0) : x = 0 := by
  have hp : p.Prime := Fact.out
  have hcop : (m !).Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, hp.dvd_factorial]
    omega
  let u : ℕ := ((m ! : ZMod p)⁻¹).val
  have hu_mod : u * m ! % p = 1 := by
    have hz : ((u * m ! : ℕ) : ZMod p) = (1 : ZMod p) := by
      simpa only [Nat.cast_mul] using ZMod.val_inv_mul hcop
    have : NeZero p := ⟨hp.ne_zero⟩
    have hval := congrArg ZMod.val hz
    rw [ZMod.val_natCast, ZMod.val_one'' hp.one_lt.ne'] at hval
    exact hval
  have hu_nat : u * m ! = p * (u * m ! / p) + 1 := by
    rw [← hu_mod, Nat.div_add_mod]
  have hu_cast : (u : A) * (m ! : A) = 1 := by
    have hc := congrArg (Nat.cast (R := A)) hu_nat
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero A p, zero_mul,
      zero_add] at hc
    exact hc
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * ((m ! : A) * (u : A)) := by rw [mul_comm (m ! : A), hu_cast]
    _ = (x * (m ! : A)) * (u : A) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hx, zero_mul]

/-- In prime characteristic `p`, all intermediate Hochschild coefficients `P p m` (`2 ≤ m < p`)
vanish, without assuming subtraction in `A`. -/
private theorem hochschildCoeff_prime_eq_zero (D : Derivation R A A) (a : A) (p : ℕ)
    [Fact p.Prime] [CharP A p] {m : ℕ} (hm2 : 2 ≤ m) (hmp : m < p) :
    hochschildCoeff D a p m = 0 := by
  have : CharP (Polynomial A) p :=
    charP_of_injective_ringHom Polynomial.C_injective p
  let E : Derivation R (Polynomial A) (Polynomial A) := (Polynomial.C a • polyLiftDer D).pPow p
  have hlhs : (E (Polynomial.X ^ m : Polynomial A)).coeff 0 = 0 := by
    rw [E.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Polynomial.coeff_natCast_mul]
    have hm1 : m - 1 = (m - 2) + 1 := by omega
    rw [hm1, pow_succ', mul_assoc, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
      mul_zero]
  have hrhs : (E (Polynomial.X ^ m : Polynomial A)).coeff 0 =
      hochschildCoeff D a p m * (m ! : A) := by
    dsimp only [E]
    rw [pPow_apply]
    rw [iterate_smul_eq_sum_hochschildCoeff D (polyLiftDer D) Polynomial.C (polyLiftDer_C D) a p]
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (Nat.lt_succ_of_lt hmp))]
    · rw [iterate_polyLiftDer_X_pow, Polynomial.iterate_derivative_X_pow_eq_C_mul,
        Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, ← Polynomial.C_mul,
        Polynomial.coeff_C_zero]
    · intro k _ hkm
      rw [iterate_polyLiftDer_X_pow, Polynomial.iterate_derivative_X_pow_eq_C_mul,
        ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul]
      rcases lt_or_gt_of_ne hkm with hlt | hgt
      · have hpos : m - k ≠ 0 := by omega
        rw [Polynomial.coeff_X_pow, ite_eq_right_iff.mpr (fun h => absurd h.symm hpos), mul_zero]
      · rw [Nat.descFactorial_of_lt hgt, Nat.cast_zero, mul_zero, zero_mul]
  exact eq_zero_of_mul_factorial_eq_zero p hmp (hrhs.symm.trans hlhs)

/-- **Hochschild's formula** (also due to Deligne; Katz 1970, Proposition 5.3): for an algebra
element `a : A` and a derivation `D : Derivation R A A` in prime characteristic `p`,
`(a • D).pPow p = a ^ p • D.pPow p + ((⇑(a • D))^[p - 1] a) • D`. -/
theorem pPow_smul (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) :
    (a • D).pPow p = a ^ p • D.pPow p + ((⇑(a • D))^[p - 1] a) • D := by
  have hp : p.Prime := Fact.out
  ext b
  rw [pPow_apply, add_apply, smul_apply, smul_apply, pPow_apply, smul_eq_mul, smul_eq_mul]
  have hexp := iterate_smul_eq_sum_hochschildCoeff D D (RingHom.id A) (fun _ => rfl) a p b
  simp only [RingHom.id_apply] at hexp
  rw [hexp, Finset.sum_range_succ, hochschildCoeff_self, add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr hp.one_lt)]
  · have hp1 : (p - 1) + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [Function.iterate_one, ← hp1, hochschildCoeff_one, Nat.add_sub_cancel]
  · intro k hk hk1
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hochschildCoeff_zero_of_pos D a hp.pos, zero_mul]
    · have hk2 : 2 ≤ k := by omega
      rw [hochschildCoeff_prime_eq_zero D a p hk2 (Finset.mem_range.mp hk), zero_mul]

/-- If `D a = 0`, the correction term in Hochschild's formula vanishes and
`(a • D).pPow p = a ^ p • D.pPow p`. -/
theorem pPow_smul_of_apply_eq_zero (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p]
    {a : A} (ha : D a = 0) :
    (a • D).pPow p = a ^ p • D.pPow p := by
  have hp : p.Prime := Fact.out
  have hcorr : (⇑(a • D))^[p - 1] a = 0 := by
    have h1 : p - 1 = (p - 2) + 1 := by
      have := hp.two_le
      omega
    rw [h1, Function.iterate_succ_apply, smul_apply, ha, smul_zero]
    induction (p - 2) with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  rw [D.pPow_smul p a, hcorr, zero_smul, add_zero]

end Hochschild

section BaseChange

open TensorProduct

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- Iterating a base-changed derivation acts on the second tensor factor. -/
theorem baseChange_iterate_tmul (D : Derivation R A A) (n : ℕ) (s : S) (a : A) :
    (D.baseChange S)^[n] (s ⊗ₜ[R] a) = s ⊗ₜ[R] D^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, baseChange_tmul, Function.iterate_succ_apply']

/-- Compatibility of `Derivation.pPow` with base change: `(D.pPow p).baseChange S` equals
`(D.baseChange S).pPow p`. -/
theorem baseChange_pPow (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p]
    [CharP (S ⊗[R] A) p] :
    (D.pPow p).baseChange S = (D.baseChange S).pPow p := by
  refine baseChange_ext fun a => ?_
  rw [baseChange_tmul, pPow_apply, pPow_apply, baseChange_iterate_tmul]

end BaseChange

end CommSemiring

section CommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section EndHom

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R A) in
/-- The canonical Lie algebra embedding `Derivation R A A →ₗ⁅R⁆ Module.End R A` taking a
derivation to its underlying `R`-linear endomorphism. -/
def toEndLieHom : Derivation R A A →ₗ⁅R⁆ Module.End R A where
  toFun D := D.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp]
theorem toEndLieHom_apply (D : Derivation R A A) :
    toEndLieHom R A D = D.toLinearMap :=
  (rfl)

theorem toEndLieHom_injective : Function.Injective (toEndLieHom R A) := by
  intro D E h
  ext a
  exact LinearMap.congr_fun h a

/-- The `p`-th power of a derivation satisfies `ad (D.pPow p) = (ad D) ^ p`. -/
theorem ad_pPow (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] :
    LieAlgebra.ad R (Derivation R A A) (D.pPow p) =
      LieAlgebra.ad R (Derivation R A A) D ^ p := by
  have : CharP (Module.End R A) p :=
    charP_of_injective_ringHom (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
      Algebra.lmul_injective p
  have : ExpChar (Module.End R A) p := ExpChar.prime Fact.out
  refine LinearMap.ext fun E => toEndLieHom_injective ?_
  have had : ∀ n : ℕ,
      ((LieAlgebra.ad R (Derivation R A A) D ^ n) E).toLinearMap =
        (LieAlgebra.ad R (Module.End R A) D.toLinearMap ^ n) E.toLinearMap := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, LieAlgebra.ad_apply,
        LieAlgebra.ad_apply, commutator_coe_linear_map, ih]
  rw [toEndLieHom_apply, toEndLieHom_apply, had p, LieAlgebra.ad_apply,
    commutator_coe_linear_map, pPow_toLinearMap]
  have h := congrArg (fun f : Module.End R (Module.End R A) => f E.toLinearMap)
    (TauCeti.LieAlgebra.ad_pow_expChar_pow (R := R) p D.toLinearMap 1)
  simpa only [pow_one, LieAlgebra.ad_apply] using h

/-- Jacobson's formula for the `p`-th power of a sum of derivations. -/
theorem pPow_add (D E : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] :
    (D + E).pPow p =
      D.pPow p + E.pPow p + FreeLieAlgebra.lift R ![D, E] (TauCeti.jacobsonLie R p) := by
  have : CharP (Module.End R A) p :=
    charP_of_injective_ringHom (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
      Algebra.lmul_injective p
  refine toEndLieHom_injective ?_
  have hjac := TauCeti.add_pow_eq_jacobson R p D.toLinearMap E.toLinearMap
  have hmap := TauCeti.map_lift_jacobsonLie p (toEndLieHom R A) D E
  simp only [toEndLieHom_apply] at hmap
  have hadd (D₁ D₂ : Derivation R A A) :
      (D₁ + D₂).toLinearMap = D₁.toLinearMap + D₂.toLinearMap := rfl
  rw [toEndLieHom_apply, toEndLieHom_apply, pPow_toLinearMap, hadd, hjac, ← hmap, hadd, hadd,
    pPow_toLinearMap, pPow_toLinearMap]

/-- Derivations of a commutative `R`-algebra of prime characteristic `p` form a restricted Lie
algebra with `p`-map `D ↦ D.pPow p`. -/
instance instRestrictedLieAlgebra (p : ℕ) [Fact p.Prime] [CharP A p] :
    TauCeti.RestrictedLieAlgebra R (Derivation R A A) p where
  pMap D := D.pPow p
  pMap_smul c D := D.pPow_smul_base p c
  ad_pMap D := D.ad_pPow p
  pMap_add D E := D.pPow_add E p

@[simp]
theorem pMap_eq_pPow (p : ℕ) [Fact p.Prime] [CharP A p] (D : Derivation R A A) :
    TauCeti.RestrictedLieAlgebra.pMap (R := R) (p := p) D = D.pPow p :=
  (rfl)

variable (R A) in
/-- The canonical embedding `Derivation R A A → Module.End R A` as an injective morphism of
restricted Lie algebras into the associative restricted Lie algebra `ofAssociative`. -/
def toEndRestrictedLieHom (p : ℕ) [Fact p.Prime] [CharP A p] :
    @TauCeti.RestrictedLieHom R p (Derivation R A A) (Module.End R A) _ _ _ _ _ _
      (@TauCeti.RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
        (charP_of_injective_ringHom
          (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
          Algebra.lmul_injective p)) :=
  @TauCeti.RestrictedLieHom.mk R p (Derivation R A A) (Module.End R A) _ _ _ _ _ _
    (@TauCeti.RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
      (charP_of_injective_ringHom
        (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
        Algebra.lmul_injective p))
    (toEndLieHom R A) fun D => by
      have : CharP (Module.End R A) p :=
        charP_of_injective_ringHom
          (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
          Algebra.lmul_injective p
      dsimp only [LieHom.toFun_eq_coe]
      rw [pMap_eq_pPow, toEndLieHom_apply, toEndLieHom_apply, pPow_toLinearMap]
      exact (TauCeti.RestrictedLieAlgebra.ofAssociative_pMap R (Module.End R A) p
        D.toLinearMap).symm

@[simp]
theorem toEndRestrictedLieHom_apply (p : ℕ) [Fact p.Prime] [CharP A p] (D : Derivation R A A) :
    toEndRestrictedLieHom R A p D = D.toLinearMap :=
  (rfl)

theorem toEndRestrictedLieHom_injective (p : ℕ) [Fact p.Prime] [CharP A p] :
    Function.Injective (toEndRestrictedLieHom R A p) :=
  toEndLieHom_injective

end EndHom

section Localization

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower R A T]
  (S : Submonoid A) [IsLocalization S T]

/-- Iterating the localization extension of a derivation commutes with `algebraMap A T`. -/
theorem iterate_extendOfIsLocalization_algebraMap (D : Derivation R A A) (n : ℕ) (a : A) :
    ((((Algebra.linearMap A T).compDer D).extendOfIsLocalization S)^[n]) (algebraMap A T a) =
      algebraMap A T (D^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, extendOfIsLocalization_algebraMap, coe_comp,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      coeFn_coe, Function.iterate_succ_apply']

/-- Compatibility of `Derivation.pPow` with localization: extending `D.pPow p` to a localization
equals taking `pPow p` of the extended derivation. -/
theorem extendOfIsLocalization_pPow (D : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p]
    [CharP T p] :
    ((Algebra.linearMap A T).compDer (D.pPow p)).extendOfIsLocalization S =
      (((Algebra.linearMap A T).compDer D).extendOfIsLocalization S).pPow p := by
  refine Derivation.ext (congrFun (IsLocalization.eq_of_leibniz S
    (fun x y => by simp [leibniz]) (fun x y => by simp [leibniz]) fun a => ?_))
  rw [extendOfIsLocalization_algebraMap, coe_comp, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Algebra.linearMap_apply, coeFn_coe,
    pPow_apply, pPow_apply, iterate_extendOfIsLocalization_algebraMap]

end Localization

section KaehlerUniqueness

/-- Two derivations `A → M` agreeing on elements `s i` whose Kähler differentials `d(s i)` form an
`A`-basis of `Ω[A⁄R]` are equal. -/
theorem eq_of_apply_eq_of_kaehlerBasis {ι M : Type*} [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ i, b i = KaehlerDifferential.D R A (s i))
    {D E : Derivation R A M} (h : ∀ i, D (s i) = E (s i)) : D = E := by
  have hlift : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    refine b.ext fun i => ?_
    rw [hb i, liftKaehlerDifferential_comp_D, liftKaehlerDifferential_comp_D, h i]
  exact (KaehlerDifferential.linearMapEquivDerivation R A).symm.injective hlift

end KaehlerUniqueness

end CommRing

end Derivation

namespace TauCeti

section KaehlerCoordinates

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The `i`-th coordinate derivation dual to a basis `b : Module.Basis ι A Ω[A⁄R]` of Kähler
differentials, sending `a ↦ b.coord i (d a)`. -/
noncomputable def kaehlerDualDer (b : Module.Basis ι A Ω[A⁄R]) (i : ι) : Derivation R A A :=
  (b.coord i).compDer (KaehlerDifferential.D R A)

@[simp]
theorem kaehlerDualDer_apply (b : Module.Basis ι A Ω[A⁄R]) (i : ι) (a : A) :
    kaehlerDualDer b i a = b.coord i (KaehlerDifferential.D R A a) :=
  (rfl)

theorem kaehlerDualDer_apply_self (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) (i : ι) :
    kaehlerDualDer b i (s i) = 1 := by
  rw [kaehlerDualDer_apply, ← hb i, Module.Basis.coord_apply, b.repr_self, Finsupp.single_eq_same]

theorem kaehlerDualDer_apply_ne (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) {i j : ι} (hji : j ≠ i) :
    kaehlerDualDer b i (s j) = 0 := by
  rw [kaehlerDualDer_apply, ← hb j, Module.Basis.coord_apply, b.repr_self,
    Finsupp.single_eq_of_ne hji.symm]

theorem kaehlerDualDer_apply_eq_ite [DecidableEq ι] (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) (i j : ι) :
    kaehlerDualDer b i (s j) = if j = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact kaehlerDualDer_apply_self b hb j
  · exact kaehlerDualDer_apply_ne b hb h

/-- The dual coordinate derivations of a basis `b i = d(s i)` of `Ω[A⁄R]` pairwise commute in the
Lie algebra of derivations (characteristic-free). -/
theorem lie_kaehlerDualDer (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) (i j : ι) :
    ⁅kaehlerDualDer b i, kaehlerDualDer b j⁆ = 0 := by
  refine Derivation.eq_of_apply_eq_of_kaehlerBasis b hb fun k => ?_
  rw [Derivation.commutator_apply, zero_apply]
  have h1 : kaehlerDualDer b i (kaehlerDualDer b j (s k)) = 0 := by
    by_cases h : k = j
    · subst h; rw [kaehlerDualDer_apply_self b hb k, Derivation.map_one_eq_zero]
    · rw [kaehlerDualDer_apply_ne b hb h, map_zero]
  have h2 : kaehlerDualDer b j (kaehlerDualDer b i (s k)) = 0 := by
    by_cases h : k = i
    · subst h; rw [kaehlerDualDer_apply_self b hb k, Derivation.map_one_eq_zero]
    · rw [kaehlerDualDer_apply_ne b hb h, map_zero]
  rw [h1, h2, sub_self]

/-- The linear endomorphisms underlying the dual coordinate derivations pairwise commute. -/
theorem commute_kaehlerDualDer (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) (i j : ι) :
    Commute (kaehlerDualDer b i).toLinearMap (kaehlerDualDer b j).toLinearMap := by
  have h := congrArg (fun D : Derivation R A A => D.toLinearMap) (lie_kaehlerDualDer b hb i j)
  rw [Derivation.commutator_coe_linear_map, Ring.lie_def] at h
  exact sub_eq_zero.mp h

/-- In prime characteristic `p`, every dual coordinate derivation `∂ᵢ` of a basis `b i = d(s i)` of
`Ω[A⁄R]` has zero `p`-th power. -/
theorem pPow_kaehlerDualDer (b : Module.Basis ι A Ω[A⁄R]) {s : ι → A}
    (hb : ∀ j, b j = KaehlerDifferential.D R A (s j)) (p : ℕ) [Fact p.Prime] [CharP A p] (i : ι) :
    (kaehlerDualDer b i).pPow p = 0 := by
  have hp : p.Prime := Fact.out
  refine Derivation.eq_of_apply_eq_of_kaehlerBasis b hb fun k => ?_
  rw [Derivation.pPow_apply, zero_apply]
  have hp2 : p = (p - 2) + 2 := (Nat.sub_add_cancel hp.two_le).symm
  rw [hp2, Function.iterate_add_apply, Function.iterate_succ_apply, Function.iterate_one]
  have hstep : kaehlerDualDer b i (kaehlerDualDer b i (s k)) = 0 := by
    by_cases h : k = i
    · subst h; rw [kaehlerDualDer_apply_self b hb k, Derivation.map_one_eq_zero]
    · rw [kaehlerDualDer_apply_ne b hb h, map_zero]
  rw [hstep]
  induction (p - 2) with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

end KaehlerCoordinates

end TauCeti

section Examples

open Polynomial

-- Witness 1: on `R[X]` in prime characteristic `p`, `(d/dX).pPow p = 0` (reusing
-- `Polynomial.iterate_derivative_eq_zero_of_charP`).
example (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] [CharP R[X] p] :
    (Polynomial.derivative' (R := R)).pPow p = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine Derivation.ext fun f => ?_
  rw [Derivation.pPow_apply, zero_apply, Polynomial.coe_derivative']
  exact Polynomial.iterate_derivative_eq_zero_of_charP hp le_rfl f

-- Witness 2: on `R[X]` in prime characteristic `p`, the Euler derivation `X • d/dX` is toral:
-- `(X • d/dX).pPow p = X • d/dX` (confirming the `+` sign in `Derivation.pPow_smul`).
example (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] [CharP R[X] p] :
    ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)).pPow p =
      (Polynomial.X : R[X]) • Polynomial.derivative' (R := R) := by
  have hprime : p.Prime := Fact.out
  have h0 : (Polynomial.derivative' (R := R)).pPow p = 0 := by
    refine Derivation.ext fun f => ?_
    rw [Derivation.pPow_apply, zero_apply, Polynomial.coe_derivative']
    exact Polynomial.iterate_derivative_eq_zero_of_charP hprime.pos le_rfl f
  have hX : ∀ n : ℕ,
      (⇑((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)))^[n] (Polynomial.X : R[X]) =
        Polynomial.X := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, smul_apply, Polynomial.derivative'_apply,
        Polynomial.derivative_X, smul_eq_mul, mul_one]
  rw [Derivation.pPow_smul, h0, smul_zero, zero_add, hX (p - 1)]

-- Witness 3: independent direct computation on monomials `X ^ k` via Fermat's little theorem
-- `(k : R) ^ p = k`, confirming `(X • d/dX)^[p] (X ^ k) = (X • d/dX) (X ^ k)` without using
-- `pPow_smul`.
example (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] (k : ℕ) :
    (⇑((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)))^[p] ((Polynomial.X : R[X]) ^ k) =
      ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)) ((Polynomial.X : R[X]) ^ k) := by
  have hfermat : ∀ j : ℕ, (j : R) ^ p = (j : R) := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, zero_pow (Fact.out : p.Prime).ne_zero]
    | succ m ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]
  have hiter : ∀ n : ℕ,
      (⇑((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)))^[n]
          ((Polynomial.X : R[X]) ^ k) =
        C ((k : R) ^ n) * (X : R[X]) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, smul_apply, Polynomial.derivative'_apply,
        Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, smul_eq_mul]
      cases k with
      | zero => simp [pow_succ']
      | succ m =>
        rw [Nat.succ_sub_one, pow_succ' ((m + 1 : ℕ) : R), map_mul]
        ring
  rw [hiter p, hfermat k,
    ← Function.iterate_one (⇑((X : R[X]) • derivative' (R := R))), hiter 1, pow_one]

-- Witness 4: characteristic `0` counterexample on `ℚ[X]` showing `(d/dX)^[2]` fails the Leibniz
-- rule without `[CharP A p]`.
example :
    (Polynomial.derivative' (R := ℚ))^[2] ((Polynomial.X : ℚ[X]) * Polynomial.X) ≠
      (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X +
        (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp [Polynomial.coe_derivative', Function.iterate_succ_apply'] at h0

end Examples
