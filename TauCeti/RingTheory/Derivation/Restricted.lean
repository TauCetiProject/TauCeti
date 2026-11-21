/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import TauCeti.Algebra.Lie.Restricted.Basic
public import TauCeti.RingTheory.Derivation.Lie
public import TauCeti.RingTheory.Derivation.PPow
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Init
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Hochschild's formula and the restricted Lie algebra structure on derivations

Over a commutative semiring `A` of prime characteristic `p`, `Derivation.pPow p D` (defined in
`TauCeti.RingTheory.Derivation.PPow`) packages the `p`-th iterate `D^[p]` of an `R`-derivation
`D : Derivation R A A` as a derivation.

Unlike the base-ring action `c • D` (`c : R`), where `(c • D).pPow p = c ^ p • D.pPow p`
(`Derivation.pPow_const_smul`), the `A`-module action satisfies **Hochschild's formula** (also
due to Deligne; Katz 1970, Proposition 5.3):

`(a • D).pPow p = a ^ p • D.pPow p + ((⇑(a • D))^[p - 1] a) • D` (`Derivation.pPow_smul`).

In particular, whenever `D a = 0`, the correction term vanishes
(`Derivation.pPow_smul_of_apply_eq_zero`). The proof works over arbitrary commutative semirings
(no subtraction is needed) by expanding `(a • D)^[n]` via recursive coefficients, lifting `D` to
`A[X]`, and reading off the constant term of `((C a • D').pPow p) (X ^ m)` for `2 ≤ m < p`, where
`D' = coeffDer D + d/dX`.

When `R` is a commutative ring and `A` is a commutative `R`-algebra of prime characteristic `p`,
`Derivation.pPow p` also satisfies Jacobson's additivity formula (`Derivation.pPow_add`), equipping
`Derivation R A A` with a canonical restricted Lie algebra structure
(`Derivation.instRestrictedLieAlgebra`), and the inclusion `Derivation.toEndRestrictedLieHom` into
`Module.End R A` is an injective morphism of restricted Lie algebras extending
`Derivation.toLinearMapLieHom`.

## Main definitions

* `Derivation.instRestrictedLieAlgebra`: the restricted Lie algebra structure on `Derivation R A A`.
* `Derivation.toEndRestrictedLieHom`: the restricted Lie algebra embedding
  `Derivation R A A → Module.End R A`.

## Main results

* `Derivation.pPow_smul`: Hochschild's formula for `(a • D).pPow p`.
* `Derivation.pPow_smul_of_apply_eq_zero`: `(a • D).pPow p = a ^ p • D.pPow p` when `D a = 0`.
* `Derivation.pPow_add`: Jacobson's formula for `(D + E).pPow p`.

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

section Hochschild

/-- The derivation on `A[X]` obtained by applying `D` coefficientwise. -/
private noncomputable def coeffDer (D : Derivation R A A) :
    Derivation R (Polynomial A) (Polynomial A) where
  toFun := AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom
  map_add' := AddMonoidAlgebra.map_add _
  map_smul' r g := by
    ext k
    simp only [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe,
      coeFn_coe, RingHom.id_apply]
    rw [Algebra.smul_def (R := R) (A := Polynomial A),
      IsScalarTower.algebraMap_apply R A (Polynomial A), Polynomial.algebraMap_eq,
      Polynomial.coeff_C_mul, Algebra.smul_def (R := R) (A := Polynomial A),
      IsScalarTower.algebraMap_apply R A (Polynomial A), Polynomial.algebraMap_eq,
      Polynomial.coeff_C_mul, AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply,
      LinearMap.toAddMonoidHom_coe, coeFn_coe, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  map_one_eq_zero' := by
    ext k
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe,
      coeFn_coe, Polynomial.coeff_one, Polynomial.coeff_zero]
    split_ifs <;> simp
  leibniz' g h := by
    ext k
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe,
      coeFn_coe, Polynomial.coeff_mul, map_sum, Polynomial.coeff_add, smul_eq_mul,
      smul_eq_mul, Polynomial.coeff_mul, Polynomial.coeff_mul]
    have hterm : ∀ ij ∈ Finset.antidiagonal k,
        D (g.coeff ij.1 * h.coeff ij.2) =
          g.coeff ij.1 * (AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom h).coeff ij.2 +
            h.coeff ij.2 * (AddMonoidAlgebra.map D.toLinearMap.toAddMonoidHom g).coeff ij.1 := by
      intro ij _
      rw [D.leibniz, smul_eq_mul, smul_eq_mul, AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply,
        AddMonoidAlgebra.coeff_map, Finsupp.mapRange_apply, LinearMap.toAddMonoidHom_coe, coeFn_coe]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun ij => ?_) (fun ij _ => rfl)
    simp [Finset.mem_antidiagonal, add_comm]

private theorem coeff_coeffDer (D : Derivation R A A) (g : Polynomial A) (k : ℕ) :
    (coeffDer D g).coeff k = D (g.coeff k) :=
  rfl

/-- The lifted derivation `D' = coeffDer D + d/dX` on `A[X]`. -/
private noncomputable def polyLiftDer (D : Derivation R A A) :
    Derivation R (Polynomial A) (Polynomial A) :=
  coeffDer D + (Polynomial.derivative' (R := A)).restrictScalars R

private theorem polyLiftDer_C (D : Derivation R A A) (b : A) :
    polyLiftDer D (Polynomial.C b) = Polynomial.C (D b) := by
  ext k
  rw [polyLiftDer, add_apply, Derivation.restrictScalars_apply, Polynomial.derivative'_apply,
    Polynomial.derivative_C, add_zero, coeff_coeffDer, Polynomial.coeff_C, Polynomial.coeff_C]
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
      rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, coeff_coeffDer, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_zero]
      split_ifs <;> simp
    rw [polyLiftDer, add_apply, hcoeff, zero_add, Derivation.restrictScalars_apply,
      Polynomial.derivative'_apply]

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
  have humod : u * m ! ≡ 1 [MOD p] := by
    rw [Nat.ModEq, hu_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hu_cast : (u : A) * (m ! : A) = 1 := by
    simpa [Nat.cast_mul, Nat.cast_one] using CharP.natCast_eq_natCast' A p humod
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

end CommSemiring

section CommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section EndHom

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Jacobson's formula for the `p`-th power of a sum of derivations. -/
theorem pPow_add (D E : Derivation R A A) (p : ℕ) [Fact p.Prime] [CharP A p] :
    (D + E).pPow p =
      D.pPow p + E.pPow p + FreeLieAlgebra.lift R ![D, E] (TauCeti.jacobsonLie R p) := by
  have : CharP (Module.End R A) p :=
    charP_of_injective_ringHom (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
      Algebra.lmul_injective p
  refine toLinearMapLieHom_injective ?_
  have hjac := TauCeti.add_pow_eq_jacobson R p (D : Module.End R A) (E : Module.End R A)
  have hmap := TauCeti.map_lift_jacobsonLie p (toLinearMapLieHom R A) D E
  simp only [toLinearMapLieHom_apply] at hmap
  have hadd (D₁ D₂ : Derivation R A A) :
      ((D₁ + D₂ : Derivation R A A) : Module.End R A) =
        (D₁ : Module.End R A) + (D₂ : Module.End R A) := by
    rw [← toLinearMapLieHom_apply, map_add, toLinearMapLieHom_apply, toLinearMapLieHom_apply]
  rw [toLinearMapLieHom_apply, toLinearMapLieHom_apply, toLinearMap_pPow, hadd, hjac, ← hmap,
    hadd, hadd, toLinearMap_pPow, toLinearMap_pPow]

/-- Derivations of a commutative `R`-algebra of prime characteristic `p` form a restricted Lie
algebra with `p`-map `D ↦ D.pPow p`. -/
instance instRestrictedLieAlgebra (p : ℕ) [Fact p.Prime] [CharP A p] :
    TauCeti.RestrictedLieAlgebra R (Derivation R A A) p where
  prime := Fact.out
  p_nsmul_eq_zero D := by
    ext a
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  pMap D := D.pPow p
  pMap_smul c D := D.pPow_const_smul p c
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
    (toLinearMapLieHom R A) fun D => by
      have : CharP (Module.End R A) p :=
        charP_of_injective_ringHom
          (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
          Algebra.lmul_injective p
      dsimp only [LieHom.toFun_eq_coe]
      rw [pMap_eq_pPow, toLinearMapLieHom_apply, toLinearMapLieHom_apply, toLinearMap_pPow]
      exact (TauCeti.RestrictedLieAlgebra.ofAssociative_pMap R (Module.End R A) p
        (D : Module.End R A)).symm

@[simp]
theorem toEndRestrictedLieHom_apply (p : ℕ) [Fact p.Prime] [CharP A p] (D : Derivation R A A) :
    toEndRestrictedLieHom R A p D = (D : Module.End R A) :=
  toLinearMapLieHom_apply D

theorem toEndRestrictedLieHom_injective (p : ℕ) [Fact p.Prime] [CharP A p] :
    Function.Injective (toEndRestrictedLieHom R A p) :=
  toLinearMapLieHom_injective

end EndHom

end CommRing

end Derivation

section Examples

open Polynomial

-- Witness 1: on `R[X]` in prime characteristic `p`, the Euler derivation `X • d/dX` is toral:
-- `(X • d/dX).pPow p = X • d/dX` (confirming the `+` sign in `Derivation.pPow_smul`).
example (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] [CharP R[X] p] :
    ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)).pPow p =
      (Polynomial.X : R[X]) • Polynomial.derivative' (R := R) := by
  have hX : ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)) Polynomial.X =
      Polynomial.X := by
    simp
  rw [Derivation.pPow_smul, Derivation.pPow_derivative', smul_zero, zero_add,
    Function.iterate_fixed hX]

-- Witness 3: characteristic `0` counterexample on `ℚ[X]` showing `(d/dX)^[2]` fails the Leibniz
-- rule without `[CharP A p]`.
example :
    (Polynomial.derivative' (R := ℚ))^[2] ((Polynomial.X : ℚ[X]) * Polynomial.X) ≠
      (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X +
        (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp [Polynomial.coe_derivative', Function.iterate_succ_apply'] at h0

-- Witness 4: over mixed-characteristic base ring `ℤ`, `RestrictedLieHom.ad` expresses the
-- adjoint representation of `Derivation ℤ (ZMod p)[X] (ZMod p)[X]`.
example (p : ℕ) [Fact p.Prime] (D : Derivation ℤ (ZMod p)[X] (ZMod p)[X]) :
    TauCeti.RestrictedLieHom.ad ℤ (Derivation ℤ (ZMod p)[X] (ZMod p)[X]) p D =
      LieAlgebra.ad ℤ (Derivation ℤ (ZMod p)[X] (ZMod p)[X]) D :=
  TauCeti.RestrictedLieHom.ad_apply _ _ _ D

end Examples
